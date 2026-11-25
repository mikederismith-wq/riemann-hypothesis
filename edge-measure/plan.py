"""Freeze the Harris–Taylor root, the two real clients, and the accepted scalar edit."""
import hashlib
import json
from pathlib import Path
import subprocess

NS = "Development.AbelianVarietyTheory.Proofs.DivisorProofs."
J = NS + "ExistsSqZeroLiftRealisingKs"
S = NS + "HarrisTaylorRealiseKodairaSpencerDirectionStatement"
U = NS + "ExistsUniversalTangentHarrisTaylorRepresentingFaStatement"
E = NS + "HarrisTaylorHodgeFiltrationNaturalityStatement"
M = NS + "SmoothOfRelativeDimensionStatement"
R = NS + "HarrisTaylorRhoPartLieDeRhamQuotient"
RETIRE = {NS + "RedPullConstMorVPull", NS + "HarrisTaylorExistsGluedFirstOrderDeformation"}
TOUCHED = {J,S,U,E} | RETIRE
OFFICIAL = "a18a350c3e5aad997766cff2670b292313e46574"
PRODUCTION = "14c585298be9468fb0c37d00fc5de2165f5daca0"
SPLIT = "1bbf7dc51b1f9d23547d2b8c7723e2c61c4b127a"
ACCEPTED = "bcfbf2ad3dfb918abcbc05d093634c11f741c98d"
PREVIOUS = "4a5b4a2d2a5177a2b6cb876425f0cb4cb6b85061"
BLOBS = {"old_j":"aa0bb029399e712ecdb8b6283a9f36973a6a8fc6", "new_j":"ba61301a17772c517ada3ebc7b7b4513a6069b98",
         "old_s":"b1e8d563d1c4f875458d7f8039ba50db01c242c3", "new_s":"3a1bcf43bdc90398b692f78d42464a5dafc53faf",
         "early":"39467cb97a15350b8ba20dcf639f8c3a449755f2", "late":"1c2f3b8956aab6fb5c1c33ce9ab0e4dfded08d67"}
def path(n):return Path("src",*n.split(".")).with_suffix(".lean")
def digest(data):return hashlib.sha256(data).hexdigest()
def blob(data):return hashlib.sha1(f"blob {len(data)}\0".encode()+data).hexdigest()

def tree(repo, project):
    """Hash the exact git tree using only the six source overlays plus untouched B14 entries."""
    replacements={};directory=path(J).parent
    for name in TOUCHED:
        f=project/path(name);replacements[f.name.encode()]=(b'100644 blob '+blob(f.read_bytes()).encode()) if f.is_file() else None
    while True:
        ref=OFFICIAL if directory==Path('.') else OFFICIAL+':'+directory.as_posix()
        raw=subprocess.check_output(['git','-C',str(repo),'ls-tree','-z',ref]);entries={b:a for v in raw.split(b'\0') if v for a,b in [v.split(b'\t',1)]}
        for key,value in replacements.items():
            if value is None:entries.pop(key,None)
            else:entries[key]=value
        payload=b''.join(v+b'\t'+k+b'\0' for k,v in entries.items());oid=subprocess.check_output(['git','-C',str(repo),'mktree','--missing','-z'],input=payload).strip()
        if directory==Path('.'):return oid.decode()
        replacements={directory.name.encode():b'040000 tree '+oid};directory=directory.parent

def closure(g,roots):
    seen=set();todo=list(roots)
    while todo:
        n=todo.pop()
        if n not in seen and n in g:
            seen.add(n);todo.extend(g[n])
    return seen

def rev(g):
    out={n:set() for n in g}
    for n,inputs in g.items():
        for v in inputs:
            if v in out:out[v].add(n)
    return out

def freeze(graphs, official):
    old,new=graphs['old']['post'],graphs['new']['post']
    joint={side:closure(states['post'],[J]) for side,states in graphs.items()}
    only=joint['old']-joint['new']
    if joint['new']-joint['old'] or S not in only or R in only or R not in joint['new']:raise ValueError('unrecognised joint dependency shape')
    clients=[U,M]; roots=set().union(*(closure(g,clients) for states in graphs.values() for g in states.values()))
    hot=closure(rev(official),TOUCHED)
    for states in graphs.values():
        for g in states.values():
            hot|=closure(rev(g),TOUCHED)
    safe=roots-hot;expected={S,J,E,U,M}
    if roots-safe!=expected or set(rev(old)[J])!=set(clients) or set(rev(new)[J])!=set(clients):raise ValueError('unexpected direct programs or affected-source frontier')
    if any(set(official[n]) & hot for n in safe):raise ValueError('unsafe public archive import')
    def mods(xs):return {'count':len(xs),'sha256':digest(('\n'.join(sorted(xs))+'\n').encode())}
    summary={'safe':mods(safe),'old_exclusive':mods(only),'joint_old':len(joint['old']),'joint_new':len(joint['new']),
      'union':len(roots),'clients':clients,'changed_in_union':sorted(expected),'cycles':2,
      'post_client_cones':{k:{n:len(closure(states['post'],[n])) for n in [J,U,M,'Main']} for k,states in graphs.items()}}
    return safe,only,summary
