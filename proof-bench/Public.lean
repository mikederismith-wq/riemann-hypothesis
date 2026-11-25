import Lean

open Lean

/-- Normalize public signatures that now refer to the shared copies from `MonoCount`. -/
def normalizeShared (removed : List String) (expr : Expr) : Expr :=
  expr.replace fun e => match e with
    | .const (.str ns part) levels =>
      if ns == `Formalism.CountingSumsFrames.TO && removed.contains part then
        some (.const (.str `Formalism.CountingSumsFrames part) levels)
      else none
    | _ => none

def main (args : List String) : IO Unit := do
  let [modulesFile, removedFile] := args | throw (IO.userError "expected module and declaration lists")
  let removed := (← IO.FS.readFile removedFile).splitOn "\n"
  for line in (← IO.FS.readFile modulesFile).splitOn "\n" do
    if line.isEmpty then continue
    let path := "/work/project/.lake/build/lib/lean/" ++ line.replace "." "/" ++ ".olean"
    let (data, _) ← readModuleData path
    for decl in data.constants do
      if decl.name.isInternal then continue
      let record := Json.mkObj [
        ("module", toJson line), ("name", toJson decl.name.toString),
        ("universeParameters", toJson (decl.levelParams.map Name.toString)),
        ("typeHash", toJson (toString (hash decl.type))),
        ("canonicalTypeHash", toJson (toString (hash (normalizeShared removed decl.type))))]
      IO.println record.compress
