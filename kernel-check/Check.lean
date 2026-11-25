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

private def dataRoots : List String := ["frst", "ltr", "IsF", "IsL", "ext", "slc", "fsj", "wlat", "wfir",
  "Mup", "Cset", "psi", "instDecidablePredProdFinFsj"]

private def isDataRoot : Name → Bool
  | .str parent part => parent == `Formalism.CountingSumsFrames.TO && dataRoots.contains part
  | _ => false

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private abbrev Parts := Array (ModuleData × CompactedRegion)

private def readParts (base : String) : IO Parts :=
  readModuleDataParts #[System.FilePath.mk base, System.FilePath.mk (base ++ ".server"),
    System.FilePath.mk (base ++ ".private")]

private def defBody (parts : Parts) (n : Name) : Option DefinitionVal := Id.run do
  for (m, _) in parts.reverse do
    for c in m.constants do
      if c.name == n then
        if let .defnInfo d := c then return some d
  return none

private def kinds (parts : Parts) (n : Name) : Array String := Id.run do
  let mut out := #[]
  for (m, _) in parts do
    let c := m.constants.find? (fun decl => decl.name == n)
    out := out.push ((c.map kind).getD "absent")
  return out

private def equalityError (env : Environment) (a b : Expr) : String :=
  match Kernel.isDefEq env {} a b with
  | .ok true => ""
  | .ok false => "kernel returned false"
  | .error _ => "kernel raised an exception"

private def propositionError (env : Environment) (t : Expr) : String :=
  match Kernel.check env {} t with
  | .ok s => equalityError env s (.sort .zero)
  | .error _ => "kernel could not type-check the proposition"

/-- The public instance inferred by an ordinary consumer computes the original Nat decision. -/
example (N r j0 : ℕ) :
    (inferInstance : DecidablePred (Formalism.CountingSumsFrames.fsj N r j0)) =
      fun v => Nat.decLt (v.1 : ℕ) j0 := rfl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let provider ← readParts "/work/project/.lake/build/lib/lean/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.olean"
  let mut retained : Array String := #[]
  let mut replaced : Array String := #[]
  let mut values : Array String := #[]
  let mut proofTypes : Array String := #[]
  let mut kindReport : Array Json := #[]
  let mut failures : Array String := #[]
  for mod in testedModules do
    let legacy ← readParts ("/work/result/legacy/" ++ mod ++ ".olean")
    let some pub := legacy[0]? | throwError "missing public facet for {mod}"
    for decl in pub.1.constants do
      if decl.name.isInternal then continue
      let canonical := sharedName decl.name
      let some candidate := env.find? canonical | do
        failures := failures.push s!"missing {canonical} for {decl.name}"
        continue
      if decl.levelParams.length != candidate.levelParams.length then
        failures := failures.push s!"universe parameter count changed for {decl.name}"
        continue
      let levels := candidate.levelParams.map Level.param
      let legacyType := sharedExpr (decl.type.instantiateLevelParams decl.levelParams levels)
      let reason := equalityError env legacyType candidate.type
      if !reason.isEmpty then
        failures := failures.push s!"{decl.name} declaration type: {reason}"
      if canonical == decl.name then
        if reason.isEmpty then retained := retained.push decl.name.toString
        continue
      if (env.find? decl.name).isSome then
        failures := failures.push s!"duplicate {decl.name} survived"
      kindReport := kindReport.push (Json.mkObj [("legacy", toJson decl.name.toString),
        ("provider", toJson canonical.toString), ("legacy_facets", toJson (kinds legacy decl.name)),
        ("provider_facets", toJson (kinds provider canonical)), ("imported_kind", toJson (kind candidate))])
      if reason.isEmpty then replaced := replaced.push decl.name.toString
      if isDataRoot decl.name then
        let some a := defBody legacy decl.name | do
          failures := failures.push s!"no legacy implementation of {decl.name} in the compiled facets"
          continue
        let some b := defBody provider canonical | do
          failures := failures.push s!"no provider implementation of {canonical} in the compiled facets"
          continue
        if a.levelParams.length != b.levelParams.length then
          failures := failures.push s!"implementation universe parameter count changed for {decl.name}"
          continue
        let oldValue := sharedExpr (a.value.instantiateLevelParams a.levelParams (b.levelParams.map Level.param))
        let err := equalityError env oldValue b.value
        if err.isEmpty then values := values.push decl.name.toString
        else failures := failures.push s!"{decl.name} implementation: {err}"
      else
        let oldErr := propositionError env legacyType
        let freshErr := propositionError env candidate.type
        if oldErr.isEmpty && freshErr.isEmpty then proofTypes := proofTypes.push decl.name.toString
        else failures := failures.push s!"{decl.name} expected two propositions: old {oldErr}, new {freshErr}"
  let report := Json.mkObj [("surviving_types", toJson retained), ("replaced_types", toJson replaced),
    ("definition_values", toJson values), ("proof_types", toJson proofTypes), ("failures", toJson failures),
    ("facet_kinds", toJson kindReport)]
  IO.FS.writeFile "/work/result/legacy-check.json" (report.compress ++ "\n")
  if !failures.isEmpty || retained.size != 218 || replaced.size != 75 || values.size != 13 || proofTypes.size != 62 ||
      (values.contains "Formalism.CountingSumsFrames.TO.instDecidablePredProdFinFsj") == false then
    throwError "kernel verification failed. Retained {retained.size}, replaced {replaced.size}, implementations {values.size}, propositions {proofTypes.size}, recorded failures {failures.size}"
