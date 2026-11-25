import Lean
import Formalism.PolynomialDimension.MultinomialDepth.TieOps
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SymmetryFinitenessWindowLevelDimOnAdmissible
import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.LatticeTheoremEps28Valid
import Formalism.PolynomialDimension.MultinomialDepth.MonoCount

open Lean Elab Command

private def sharedRoots : List String := ["C_stable", "Cset", "IsF", "IsL", "Mup", "eq_sum_sl", "ext", "ext_Y", "ext_eq_sum", "ext_glAct", "ext_monomial", "ext_mul", "ext_wh", "frst", "frst_add", "frst_add_ltr", "frst_isF", "frst_of", "frst_of'", "fsj", "glAct_isF", "glAct_isL", "isF_iff", "isF_monomial_frst", "isF_of_polLz", "isL_iff", "isL_monomial_ltr", "killL_of_isL", "ltr", "ltr_add", "ltr_isL", "ltr_of", "ltr_of'", "midAct_eq", "midAct_isF", "midAct_isL", "midAct_mul_F", "monomial_eq_basis", "monomial_split", "mul_ltr_pol", "polynomial_finite_weights", "proj_exists", "psi", "psi_glAct", "psi_id", "psi_mem", "sl_monomial", "sl_mul", "slc", "slc_C", "slc_glAct", "slc_pol", "slc_wh", "slc_ycond", "weight_eq_zero_iff", "weight_first", "weight_wv_zero", "wfir", "wh_first", "whc_comm", "whc_keep", "wlat", "instDecidablePredProdFinFsj"]

private def testedModules : List String := ["Formalism.PolynomialDimension.MultinomialDepth.TieOps", "Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SymmetryFinitenessWindowLevelDimOnAdmissible", "Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.LatticeTheoremEps28Valid"]

/-- Rebind only removed names, including equation lemmas beneath a removed name. -/
private def sharedName (n : Name) : Name :=
  match n with
  | .anonymous => .anonymous
  | .str parent part =>
    if parent == `Formalism.CountingSumsFrames.TO && sharedRoots.contains part then
      .str `Formalism.CountingSumsFrames part
    else .str (sharedName parent) part
  | .num parent i => .num (sharedName parent) i

private def sharedExpr (e : Expr) : Expr :=
  e.replace fun a => match a with
    | .const n us =>
      let fresh := sharedName n
      if fresh == n then none else some (.const fresh us)
    | _ => none

private def kernelEqual (env : Environment) (a b : Expr) (n : Name) (part : String) : CommandElabM Unit :=
  match Kernel.isDefEq env {} a b with
  | .ok true => pure ()
  | .ok false => throwError "kernel equality failed for {n} ({part})"
  | .error _ => throwError "kernel raised an exception comparing {n} ({part})"

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut retained : Array String := #[]
  let mut replaced : Array String := #[]
  let mut values : Array String := #[]
  for mod in testedModules do
    let (oldModule, _) ← readModuleData ("/work/result/legacy/" ++ mod ++ ".olean")
    for decl in oldModule.constants do
      if decl.name.isInternal then continue
      let canonical := sharedName decl.name
      let some candidate := env.find? canonical | throwError "missing destination {canonical} for {decl.name}"
      if decl.levelParams.length != candidate.levelParams.length then
        throwError "universe parameter count changed for {decl.name}"
      let ls := candidate.levelParams.map Level.param
      let legacyType := sharedExpr (decl.type.instantiateLevelParams decl.levelParams ls)
      kernelEqual env legacyType candidate.type decl.name "type"
      if canonical == decl.name then
        retained := retained.push decl.name.toString
      else
        if (env.find? decl.name).isSome then throwError "duplicate {decl.name} survived in the candidate"
        replaced := replaced.push decl.name.toString
        match decl, candidate with
        | .defnInfo oldDef, .defnInfo freshDef =>
          let oldValue := sharedExpr (oldDef.value.instantiateLevelParams decl.levelParams ls)
          kernelEqual env oldValue freshDef.value decl.name "definition value"
          values := values.push decl.name.toString
        | .thmInfo _, .thmInfo _ => pure ()
        | _, _ => throwError "unexpected declaration kinds for {decl.name} and {canonical}"
  let report := Json.mkObj [("surviving_types", toJson retained), ("replaced_types", toJson replaced),
    ("definition_values", toJson values)]
  IO.FS.writeFile "/work/result/legacy-check.json" (report.compress ++ "\n")
  if retained.size != 218 || replaced.size != 75 || values.size != 13 ||
      (values.contains "Formalism.CountingSumsFrames.TO.instDecidablePredProdFinFsj") == false then
    throwError "unexpected checked counts: retained {retained.size}, replaced {replaced.size}, values {values.size}"
