#!/usr/bin/env python3
"""Report text conflicts between one queued pull request and the rest of the batch queue.

The batch-queue workflow runs this from its trusted checkout. Pull request commits are fetched
as git objects and compared with `git merge-tree`. Nothing from a pull request is checked out
or run, and the only thing written to GitHub is one comment on the pull request being checked.

This finds pull requests that edit the same lines, and pairs of which one deletes a Lean file
that the other starts to import. It cannot tell whether pull requests that pass both checks also
build together.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

# Compared against, in this order: what is being built now, then what is waiting.
LABELS = ("building", "batch queue")
# Branches of this repository that hold a batch. Their pull requests are not compared.
BATCHES = "batch/"
# Hidden in the comment so that a later run edits it instead of adding another.
MARKER = "<!-- batch-queue-conflicts -->"
BOT = "github-actions[bot]"
# Most files a trial merge may have to read. Past this the report only counts shared files.
MERGE_LIMIT = 5000
# Matching a renamed file that was also edited means reading every file the other side added.
# Past this many changed files on the two sides together, only exact renames are followed.
RENAME_LIMIT = 2000
# Most file names listed for one pull request in the report.
LISTED = 10
# Lean modules live under this directory: the module `A.B` is the file `src/A/B.lean`.
SOURCE, LEAN = b"src/", b".lean"
LEAN_PATHSPEC = b":(top,glob)" + SOURCE + b"**/*" + LEAN
# Most changed Lean files whose import lines are read for one pull request.
IMPORT_LIMIT = 5000
# One line of a Lean file's import header, as scripts/quick-check.py reads it.
IMPORT = re.compile(r"(?:public\s+)?(?:meta\s+)?import(?:\s+all)?\s+([\w']+(?:\.[\w']+)*)")


def run(args, *, data=None, ok=(0,)):
    """Run a command and return (exit code, stdout). Any exit code outside `ok` is an error."""
    done = subprocess.run(args, input=data, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if done.returncode not in ok:
        sys.stderr.write(done.stderr.decode("utf-8", "replace"))
        raise RuntimeError(f"{args[0]} failed with exit code {done.returncode}")
    return done.returncode, done.stdout


def git(repo, *args, data=None, ok=(0,), config=()):
    settings = [part for item in config for part in ("-c", item)]
    return run(["git", "-C", str(repo), *settings, *args], data=data, ok=ok)


# ---------------------------------------------------------------------------------------------
# Comparing two commits in a local repository.


class Comparison:
    """How one other pull request relates to the one being checked."""

    def __init__(self, kind, shared=(), conflicts=(), note=""):
        self.kind = kind  # "apart", "clean", "conflict", "too many" or "unknown"
        self.shared = list(shared)  # files both change
        self.conflicts = list(conflicts)  # files git cannot merge
        self.note = note
        # (who deletes, deleted file, importing file): a Lean file that one of the two deletes
        # and the other starts to import. "ours" is the pull request being checked.
        self.stale = []
        self.unread = False  # too many changed files to read one side's import lines


def changed(repo, base, head):
    """Paths that differ between two commits. Reads trees only."""
    _, out = git(repo, "diff", "--name-only", "--no-renames", "-z", base, head)
    return {path for path in out.split(b"\0") if path}


def blob_ids(repo, commit, paths):
    """The blob of each of `paths` that exists at `commit`, as {path: id}. Reads trees only."""
    found = {}
    paths = sorted(paths)
    for start in range(0, len(paths), 200):
        chunk = paths[start:start + 200]
        _, out = git(repo, "--literal-pathspecs", "ls-tree", "-r", "-z", commit, "--", *chunk)
        for entry in out.split(b"\0"):
            meta, _, path = entry.partition(b"\t")
            meta = meta.split()
            if len(meta) == 3 and meta[1] == b"blob":
                found[path] = meta[2]
    return found


def fetch_blobs(repo, commits, paths):
    """Fetch the contents of `paths` at `commits` in one request, for a clone without blobs."""
    wanted = set()
    for commit in commits:
        wanted.update(blob_ids(repo, commit, paths).values())
    fetch_ids(repo, wanted)


def fetch_ids(repo, wanted):
    """Fetch blobs by id in one request."""
    if wanted:
        git(repo, "fetch", "--quiet", "--no-tags", "--no-write-fetch-head", "--recurse-submodules=no",
            "--filter=blob:none", "--stdin", "origin", data=b"\n".join(sorted(wanted)) + b"\n",
            config=("fetch.negotiationAlgorithm=noop",))


def compare(repo, base, ours, theirs, *, ours_fork=None, theirs_fork=None,
            merge_limit=MERGE_LIMIT, rename_limit=RENAME_LIMIT, partial=False):
    """Compare two pull request heads that share the ancestor `base`.

    A fork is the commit where a pull request left the main branch. What a pull request itself
    changes is measured from its fork, so that changes already on main, which one branch has
    and the other has not caught up with, are not counted against either.
    """
    mine = changed(repo, ours_fork or base, ours)
    other = changed(repo, theirs_fork or base, theirs)
    shared = sorted(mine & other)
    if not shared:
        return Comparison("apart")
    # The merge itself starts from `base`, and reads every file that differs on both sides.
    seen_mine, seen_other = changed(repo, base, ours), changed(repo, base, theirs)
    to_merge = seen_mine & seen_other
    if len(shared) > merge_limit or len(to_merge) > merge_limit:
        return Comparison("too many", shared)
    if partial:
        fetch_blobs(repo, (base, ours, theirs), to_merge)
    # git's merge ignores `merge.renames=false` in some versions, but it does honour the limit.
    config = () if len(seen_mine) + len(seen_other) <= rename_limit else ("merge.renameLimit=1",)
    code, out = git(repo, "merge-tree", "--write-tree", "--name-only", "--no-messages", "-z",
                    f"--merge-base={base}", ours, theirs, ok=(0, 1), config=config)
    # The first entry is the tree that was written; the conflicted paths follow. A conflict in
    # a file only one of the two changed is a conflict with main, which GitHub already shows.
    conflicts = sorted({path for path in out.split(b"\0")[1:] if path} & set(shared)) if code else []
    return Comparison("conflict" if conflicts else "clean", shared, conflicts)


# ---------------------------------------------------------------------------------------------
# A Lean file that one pull request deletes and another starts to import. git merges the two
# without conflict, because they change different files, and the result does not build.


def deleted_lean_files(repo, fork, head, seen):
    """Lean files under SOURCE that a pull request deletes."""
    key = ("deleted", fork, head)
    if key not in seen:
        _, out = git(repo, "diff", "--name-only", "--no-renames", "--diff-filter=D", "-z",
                     fork, head, "--", LEAN_PATHSPEC)
        seen[key] = set(out.split(b"\0")[:-1])
    return seen[key]


def import_blobs(repo, fork, head, limit):
    """The before and after blob IDs for changed Lean files, or None past the file limit."""
    _, out = git(repo, "diff", "--raw", "--no-abbrev", "--no-renames", "--diff-filter=AM",
                 "-z", fork, head, "--", LEAN_PATHSPEC)
    # With renames disabled, each raw record is a metadata field and a literal path.
    if out.count(b"\0") > 2 * limit:
        return None
    before, after = {}, {}
    records = iter(out.split(b"\0"))
    for meta, path in zip(records, records):
        old_mode, new_mode, old_id, new_id, _ = meta[1:].split()
        if old_mode not in (b"000000", b"160000"):  # absent or a gitlink
            before[path] = old_id
        if new_mode != b"160000":
            after[path] = new_id
    return before, after


def imports(contents):
    """The files that a Lean file's import header names, as paths under SOURCE.

    Only the header is read. It ends at the first line that is not blank, a comment, `module`,
    `prelude` or an import.
    """
    found, depth = set(), 0
    for raw in contents.decode("utf-8", "replace").split("\n"):
        kept, at = [], 0
        while at < len(raw):
            if raw.startswith("/-", at):
                depth, at = depth + 1, at + 2
            elif depth and raw.startswith("-/", at):
                depth, at = depth - 1, at + 2
            elif depth:
                at += 1
            elif raw.startswith("--", at):
                break
            else:
                kept.append(raw[at])
                at += 1
        line = "".join(kept).strip()
        if not line or line in ("module", "prelude"):
            continue
        match = IMPORT.fullmatch(line)
        if not match:
            break
        found.add(SOURCE + match[1].replace(".", "/").encode() + LEAN)
    return found


def read_blobs(repo, ids):
    """The contents of blobs that are already here, as {id: contents}, from one git process."""
    ids = sorted(set(ids))
    if not ids:
        return {}
    _, out = git(repo, "cat-file", "--batch", data=b"\n".join(ids) + b"\n")
    found, at = {}, 0
    for wanted in ids:
        end = out.index(b"\n", at)
        header = out[at:end].split()
        at = end + 1
        if len(header) == 3:  # "<id> <type> <size>"; a blob that is not here gives "<id> missing"
            size = int(header[2])
            found[wanted] = out[at:at + size]
            at += size + 1
    return found


def added_imports(repo, fork, head, *, limit=IMPORT_LIMIT, seen=None):
    """What a pull request starts to import, as {file it adds or edits: files newly imported}.

    An import that the file already had where the pull request left main is not new. Returns
    None if the pull request adds or edits more than `limit` Lean files. In a clone without
    blobs, `prefetch_imports` fetches what this reads.
    """
    key = ("blobs", fork, head, limit)
    if seen is not None and key in seen:
        # Prefetch already found these IDs. Only the resulting imports need to stay cached.
        blobs = seen.pop(key)
    else:
        blobs = import_blobs(repo, fork, head, limit)
    if blobs is None:
        return None
    before, after = blobs
    contents = read_blobs(repo, [*before.values(), *after.values()])
    found = {}
    for path, blob in after.items():
        new = imports(contents.get(blob, b"")) - imports(contents.get(before.get(path), b""))
        if new:
            found[path] = new
    return found


def compare_imports(repo, result, ours_fork, ours, theirs_fork, theirs, *,
                    seen=None, limit=IMPORT_LIMIT):
    """Record in `result` the Lean files that one side deletes and the other starts to import.

    `seen` keeps what was read for each pull request, so that checking one pull request against
    many others reads its files once. Import lines are only read when the other side deletes
    a Lean file.
    """
    seen = {} if seen is None else seen

    sides = (("ours", (ours_fork, ours), (theirs_fork, theirs)),
             ("theirs", (theirs_fork, theirs), (ours_fork, ours)))
    for who, deleter, importer in sides:
        gone = deleted_lean_files(repo, *deleter, seen)
        if not gone:
            continue
        key = ("imports", *importer, limit)
        if key not in seen:
            seen[key] = added_imports(repo, *importer, limit=limit, seen=seen)
        new = seen[key]
        if new is None:
            result.unread = True
            continue
        result.stale += sorted((who, target, path)
                               for path, targets in new.items() for target in targets & gone)
    return result


def prefetch_imports(repo, ours, others, *, limit=IMPORT_LIMIT):
    """For a clone without blobs: fetch, in one request, every file `compare_imports` will read.

    `ours` and each of `others` are (fork, head) pairs. A pull request's files are read only if
    the other side of some comparison deletes a Lean file, which is known from the trees alone.
    Return the tree results so that the comparisons can reuse them after the fetch.
    """
    seen = {}
    readers = list(others) if deleted_lean_files(repo, *ours, seen) else []
    if any(deleted_lean_files(repo, *pair, seen) for pair in others):
        readers.append(ours)
    wanted = set()
    for fork, head in readers:
        blobs = import_blobs(repo, fork, head, limit)
        seen["blobs", fork, head, limit] = blobs
        if blobs is not None:
            before, after = blobs
            wanted.update(before.values(), after.values())
    fetch_ids(repo, wanted)
    return seen


# ---------------------------------------------------------------------------------------------
# Asking GitHub.


def gh(*args, data=None):
    _, out = run(["gh", "api", *args], data=data)
    return out.decode("utf-8", "replace")


def head_of(repo, number):
    return gh(f"repos/{repo}/pulls/{number}", "--jq", ".head.sha").strip()


def open_pulls(repo):
    """Every open pull request as {number: (head commit, labels, whether it is a batch)}.

    One listing answers for all of them. The workflow's token is allowed 1,000 requests an hour,
    shared with every other workflow, so nothing here asks GitHub about pull requests one by one.
    """
    rows = gh("--paginate", f"repos/{repo}/pulls?state=open&per_page=100", "--jq",
              '.[] | [.number, .head.sha, .head.ref, (.head.repo.full_name // ""), ([.labels[].name] | join("|"))] | @tsv')
    found = {}
    for row in rows.splitlines():
        number, sha, ref, home, labels = (row.split("\t") + [""] * 5)[:5]
        found[int(number)] = (sha, set(labels.split("|")), home == repo and ref.startswith(BATCHES))
    return found


def labelled(pulls, exclude):
    """Pull requests carrying one of LABELS, as {number: label}. The first label wins.

    A batch pull request is left out: what it contains is compared one pull request at a time.
    """
    found = {}
    for label in LABELS:
        for number, (_, labels, batch) in sorted(pulls.items()):
            if label in labels and number != exclude and not batch:
                found.setdefault(number, label)
    return found


def merge_base(work, ours, theirs):
    """The common ancestor of two commits that have been fetched, or None if they have none."""
    code, out = git(work, "merge-base", ours, theirs, ok=(0, 1))
    return out.decode().strip() if code == 0 else None


def survey(repo, number, work):
    """Compare pull request `number` with every other labelled one.

    Returns its head commit, the others as {number: label}, and {number: Comparison}.
    """
    main = gh(f"repos/{repo}", "--jq", ".default_branch").strip()
    pulls = open_pulls(repo)
    head = pulls[number][0] if number in pulls else head_of(repo, number)
    others = labelled(pulls, number)
    results = {}
    if not others:
        return head, others, results
    # One fetch of commits and trees, without file contents, for every pull request involved.
    # The history comes with it, so common ancestors are worked out here and not asked for.
    git(work, "init", "--quiet")
    git(work, "remote", "add", "origin", f"https://github.com/{repo}.git")
    git(work, "fetch", "--quiet", "--filter=blob:none", "--no-tags", "origin",
        f"+refs/heads/{main}:refs/remotes/origin/{main}", head, *sorted({pulls[other][0] for other in others}))
    trunk = f"refs/remotes/origin/{main}"
    fork = merge_base(work, trunk, head)
    forks = {other: merge_base(work, trunk, pulls[other][0]) for other in others}
    seen = {}
    if fork:
        seen = prefetch_imports(work, (fork, head),
                                [(forks[other], pulls[other][0]) for other in others if forks[other]])
    for other in others:
        theirs = pulls[other][0]
        base, theirs_fork = merge_base(work, head, theirs), forks[other]
        if None in (fork, base, theirs_fork):
            results[other] = Comparison("unknown", note="no common ancestor")
            continue
        try:
            results[other] = compare(work, base, head, theirs, ours_fork=fork, theirs_fork=theirs_fork,
                                     partial=True)
            compare_imports(work, results[other], fork, head, theirs_fork, theirs, seen=seen)
        except RuntimeError as error:
            results[other] = Comparison("unknown", note=str(error))
    return head, others, results


# ---------------------------------------------------------------------------------------------
# Writing the report.


def show(path):
    """A file name as inline code. Names come from pull requests, so keep them inert."""
    text = path.decode("utf-8", "replace")
    text = "".join(char if char.isprintable() and char != "`" else "?" for char in text)
    return f"`{text[:200]}`"


def listing(paths):
    names = ", ".join(show(path) for path in paths[:LISTED])
    more = len(paths) - LISTED
    return names + (f" and {more:,} more" if more > 0 else "")


def count(number, noun):
    return f"{number:,} {noun}" if number == 1 else f"{number:,} {noun}s"


def report(number, head, others, results):
    """The comment text, and whether it says anything a maintainer has to act on."""
    def rows(kind):
        return [(other, others[other], results[other])
                for other in sorted(results) if results[other].kind == kind]

    lines = [MARKER]
    if not results:
        lines.append(f"No other pull request is labelled `{LABELS[0]}` or `{LABELS[1]}`, "
                     f"so #{number} was not compared with anything.")
        return "\n".join(lines) + "\n", False
    lines.append(f"#{number} was compared with the {count(len(results), 'other pull request')} "
                 f"labelled `{LABELS[0]}` or `{LABELS[1]}`.")

    conflicts, too_many, unknown = rows("conflict"), rows("too many"), rows("unknown")
    if conflicts:
        lines += ["", "It does not merge cleanly with:", ""]
        lines += [f"- #{other} (`{label}`): {count(len(result.conflicts), 'file')} in conflict: "
                  f"{listing(result.conflicts)}" for other, label, result in conflicts]
    stale = [(other, others[other], results[other]) for other in sorted(results) if results[other].stale]
    if stale:
        lines += ["", "git merges these without conflict, but one deletes a Lean file that the other "
                      "starts to import:", ""]
        for other, label, result in stale:
            said = []
            for who, deleter, importer in (("ours", number, other), ("theirs", other, number)):
                users = {}
                for side, target, path in result.stale:
                    if side == who:
                        users.setdefault(target, []).append(path)
                said += [f"#{deleter} deletes {show(target)}, "
                         f"which #{importer} starts to import in {listing(paths)}"
                         for target, paths in sorted(users.items())]
            more = len(said) - LISTED
            lines.append(f"- #{other} (`{label}`): " + "; ".join(said[:LISTED])
                         + (f"; and {more:,} more" if more > 0 else ""))
    unread = [(other, others[other]) for other in sorted(results) if results[other].unread]
    if unread:
        lines += ["", "Import lines were not read for these, because one side changes more than "
                      f"{IMPORT_LIMIT:,} Lean files:", ""]
        lines += [f"- #{other} (`{label}`)" for other, label in unread]
    if too_many:
        lines += ["", "It shares too many files with these for a trial merge here:", ""]
        lines += [f"- #{other} (`{label}`): {count(len(result.shared), 'file')} changed by both"
                  for other, label, result in too_many]
    if unknown:
        lines += ["", "These could not be compared:", ""]
        lines += [f"- #{other} (`{label}`): {result.note}" for other, label, result in unknown]
    clean = rows("clean")
    if clean:
        lines += ["", "It changes some of the same files as these, and git merges them without conflict:", ""]
        lines += [f"- #{other} (`{label}`): {count(len(result.shared), 'file')}" for other, label, result in clean]
    apart = rows("apart")
    if apart:
        lines += ["", "It has no file in common with " + ", ".join(f"#{other}" for other, _, _ in apart) + "."]
    lines += ["", f"This compares text, and new imports against deleted Lean files, at `{head[:10]}`. "
                  "Pull requests that pass both can still fail to build together."]
    return "\n".join(lines) + "\n", bool(conflicts or stale or unread or too_many or unknown)


def publish(repo, number, body, needed):
    """Post the comment, or bring an earlier one up to date. Stay quiet when there is no news."""
    earlier = gh("--paginate", f"repos/{repo}/issues/{number}/comments?per_page=100", "--jq",
                 f'.[] | select(.user.login == "{BOT}" and (.body | contains("{MARKER}"))) | .id').split()
    payload = json.dumps({"body": body}).encode()
    if earlier:
        gh("-X", "PATCH", f"repos/{repo}/issues/comments/{earlier[-1]}", "--input", "-", data=payload)
        return "updated the earlier comment"
    if needed:
        gh("-X", "POST", f"repos/{repo}/issues/{number}/comments", "--input", "-", data=payload)
        return "posted a comment"
    return "nothing to report, so no comment"


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True, help="owner/name")
    parser.add_argument("--pr", required=True, type=int, help="the pull request to check")
    parser.add_argument("--comment", action="store_true", help="post or update the comment on the pull request")
    parser.add_argument("--summary", type=Path, help="append the report to this file")
    args = parser.parse_args()

    with tempfile.TemporaryDirectory() as work:
        head, others, results = survey(args.repo, args.pr, work)
    body, needed = report(args.pr, head, others, results)
    sys.stdout.write(body)
    if args.summary:
        with args.summary.open("a") as handle:
            handle.write(body)
    if args.comment:
        print(publish(args.repo, args.pr, body, needed))


if __name__ == "__main__":
    main()
