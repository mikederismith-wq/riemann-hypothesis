import Lean

open Lean

/-- Read the public module object without importing its private proof bodies. -/
def main (args : List String) : IO Unit := do
  let [list] := args | throw (IO.userError "expected a module list")
  for line in (← IO.FS.readFile list).splitOn "\n" do
    if line.isEmpty then continue
    let path := "/work/project/.lake/build/lib/lean/" ++ line.replace "." "/" ++ ".olean"
    let (data, _) ← readModuleData path
    for decl in data.constants do
      if decl.name.isInternal then continue
      let record := Json.mkObj [
        ("module", toJson line), ("name", toJson decl.name.toString),
        ("universeParameters", toJson (decl.levelParams.map Name.toString)),
        ("typeHash", toJson (toString (hash decl.type)))]
      IO.println record.compress
