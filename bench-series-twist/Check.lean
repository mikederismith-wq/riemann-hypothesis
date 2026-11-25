import Lean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNewTwistLamFull
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AllStagesAtMemberOfSpecializations
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerUpStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultiplicityBoundOfLocalComponents
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsAtStart

open Lean Elab Command

private def roots : List String := ["Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumEq", "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNewTwistLamFull", "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AllStagesAtMemberOfSpecializations", "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FinitenessOfHyp", "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerUpStatement", "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Lb2OfThetaTwistStatement", "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultiplicityBoundOfLocalComponents", "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsAtStart"]

private def readParts (path : String) : IO (Array (ModuleData × CompactedRegion)) :=
  readModuleDataParts #[System.FilePath.mk path, System.FilePath.mk (path ++ ".server"),
    System.FilePath.mk (path ++ ".private")]

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut modules : Array Json := #[]
  for mod in roots do
    let oldParts ← readParts ("/work/result/old/" ++ mod ++ ".olean")
    let newParts ← readParts ("/work/result/new/" ++ mod ++ ".olean")
    let some oldPub := oldParts[0]? | throwError "missing old public facet for {mod}"
    let some newPub := newParts[0]? | throwError "missing new public facet for {mod}"
    let old := oldPub.1.constants
    let current := newPub.1.constants
    let oldNames := old.map ConstantInfo.name
    let newNames := current.map ConstantInfo.name
    let mut removed : Array String := #[]
    let mut retained : Array String := #[]
    for decl in old do
      if decl.name.isInternal || decl.name.toString.startsWith "_private." then continue
      if !newNames.contains decl.name then
        throwError "public declaration removed from {mod}: {decl.name}"
      let some candidate := env.find? decl.name | throwError "missing imported declaration {decl.name}"
      unless decl.levelParams.length == candidate.levelParams.length do
        throwError "universe parameter count changed for {decl.name}"
      let original := decl.type.instantiateLevelParams decl.levelParams (candidate.levelParams.map Level.param)
      match Kernel.isDefEq env {} original candidate.type with
      | .ok true => retained := retained.push decl.name.toString
      | _ => throwError "kernel equality failed for the retained type {decl.name}"
    for decl in current do
      unless decl.name.isInternal || decl.name.toString.startsWith "_private." || oldNames.contains decl.name do
        throwError "unexpected new public declaration {decl.name}"
    modules := modules.push <| Json.mkObj [("module", toJson mod), ("removed", toJson removed),
      ("retained_types", toJson retained)]
  IO.FS.writeFile "/work/result/signatures.json" (toJson modules).pretty
