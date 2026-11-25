import Lean
import Formalism.PolynomialDimension.MultinomialDepth.MonoCount

open Lean Elab Command

private def sharedRoots : List String := ["C_stable", "Cset", "IsF", "IsL", "Mup", "eq_sum_sl", "ext", "ext_Y", "ext_eq_sum", "ext_glAct", "ext_monomial", "ext_mul", "ext_wh", "frst", "frst_add", "frst_add_ltr", "frst_isF", "frst_of", "frst_of'", "fsj", "glAct_isF", "glAct_isL", "isF_iff", "isF_monomial_frst", "isF_of_polLz", "isL_iff", "isL_monomial_ltr", "killL_of_isL", "ltr", "ltr_add", "ltr_isL", "ltr_of", "ltr_of'", "midAct_eq", "midAct_isF", "midAct_isL", "midAct_mul_F", "monomial_eq_basis", "monomial_split", "mul_ltr_pol", "polynomial_finite_weights", "proj_exists", "psi", "psi_glAct", "psi_id", "psi_mem", "sl_monomial", "sl_mul", "slc", "slc_C", "slc_glAct", "slc_pol", "slc_wh", "slc_ycond", "weight_eq_zero_iff", "weight_first", "weight_wv_zero", "wfir", "wh_first", "whc_comm", "whc_keep", "wlat", "instDecidablePredProdFinFsj"]

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

private def equalityError (env : Environment) (a b : Expr) : String :=
  match Kernel.isDefEq env {} a b with
  | .ok true => ""
  | .ok false => "kernel returned false"
  | .error _ => "kernel raised an exception"

private def propositionError (env : Environment) (t : Expr) : String :=
  match Kernel.check env {} t with
  | .ok s => equalityError env s (.sort .zero)
  | .error _ => "kernel could not type-check the proposition"

/-- Rebuild the implicit binders and `Eq.refl` of an old compiler-generated equation. -/
private partial def equationWitness : Expr → Option Expr
  | .forallE n ty body bi => (equationWitness body).map fun witness => .lam n ty witness bi
  | .mdata _ t => equationWitness t
  | .app (.app (.app (.const n levels) ty) lhs) _ =>
    if n == ``Eq then some (mkApp2 (.const ``Eq.refl levels) ty lhs) else none
  | _ => none

private def equationError (env : Environment) (t : Expr) : String :=
  match equationWitness t with
  | none => "old type is not a telescope ending in an equality"
  | some witness =>
    match Kernel.check env {} witness with
    | .ok inferred => equalityError env inferred t
    | .error _ => "kernel rejected the closed reflexivity proof"

/-- The public instance inferred by an ordinary consumer computes the original Nat decision. -/
example (N r j0 : ℕ) :
    (inferInstance : DecidablePred (Formalism.CountingSumsFrames.fsj N r j0)) =
      (fun (v : Fin N × Fin r) => Nat.decLt (v.1 : ℕ) j0) := rfl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let (legacy, _) ← readModuleData "/work/result/legacy/TieOps.olean"
  let wanted := [`Formalism.CountingSumsFrames.TO.ext.eq_1, `Formalism.CountingSumsFrames.TO.slc.eq_1]
  let mut equations : Array String := #[]
  let mut failures : Array String := #[]
  for n in wanted do
    let some old := legacy.constants.find? (fun c => c.name == n) | do
      failures := failures.push s!"legacy equation {n} missing"
      continue
    let targetName := sharedName n
    if (env.find? targetName).isSome then
      failures := failures.push s!"named equivalent unexpectedly exists: {targetName}"
    let target := sharedExpr old.type
    let eqErr := equationError env target
    let propErr := propositionError env target
    if eqErr.isEmpty && propErr.isEmpty then equations := equations.push n.toString
    else failures := failures.push s!"{n}: equality {eqErr}, proposition {propErr}"
  let report := Json.mkObj [("equations", toJson equations), ("failures", toJson failures)]
  IO.FS.writeFile "/work/result/legacy-equations.json" (report.compress ++ "\n")
  if equations.size != 2 || !failures.isEmpty then
    throwError "proved {equations.size} genuine legacy equations, failed {failures.size} checks"
