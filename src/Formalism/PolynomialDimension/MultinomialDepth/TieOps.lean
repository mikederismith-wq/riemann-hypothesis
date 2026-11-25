module

public import Formalism.PolynomialDimension.MultinomialDepth.PartnerM
public import Formalism.MahlerMeasure.MahlerMeasureProofs.WeightSpaceDimensionMonotone
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamInt
public import Formalism.MahlerMeasure.StatementT
public import Mathlib.CategoryTheory.Category.Basic
public import Formalism.PolynomialDimension.MultinomialDepth.MonoCount
import Formalism.MahlerMeasure.MahlerMeasureProofs.FreezeBij
import Formalism.MahlerMeasure.MahlerMeasureProofs.FreezeInto
public import Formalism.MahlerMeasure.MahlerMeasureProofs.LieMat
import Formalism.MahlerMeasure.MahlerMeasureProofs.TheoremM
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.CountingSumsFrames.TO

open MvPolynomial Finset

section Ext

variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]

theorem sl_isF (m : σ →₀ ℕ) (x : MvPolynomial σ K) : IsF fs (slc fs m x) := by
  intro m' hm' v hv

  rw [x.as_sum, map_sum] at hm'
  obtain ⟨d, -, hd⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm')
  rw [sl_monomial] at hd
  split_ifs at hd
  · have := support_monomial_subset hd
    rw [Finset.mem_singleton] at this
    subst this
    exact frst_isF fs d v hv
  · simp at hd

end Ext

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM.DimensionMonotonicity Finset

namespace GlX

open Formalism.CountingSumsFrames.GlX

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem Lv_single_nil (v : V) : Lv G v (Finsupp.single [] 1) = v := by
  simp [Lv, act]

theorem Lv_zero (c : List (Fin r × Fin r) →₀ K) : Lv G (0 : V) c = 0 := by
  first
    | simp [Lv, Finsupp.linearCombination_apply]

theorem eqExt_core {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {ι : Type} [Fintype ι] [DecidableEq ι]
    (h g : ι → V) (la : ι → Fin r → ℤ) (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W)
    (hli : LinearIndependent K h) (hsp : W ≤ ⨆ i, G.gS {h i})
    (hg : ∀ i, G.IsHW (la i) (g i)) (hgW : ∀ i, g i ∈ W) :
    ∃ φ : V →ₗ[K] V, ∀ i c, φ (Lv G (h i) c) = Lv G (g i) c := by
  have h0 : ∀ i, h i ≠ 0 := fun i => hli.ne_zero i
  have hk : ∀ i, LinearMap.ker (Lv G (h i)) ≤ LinearMap.ker (Lv G (g i)) := fun i =>
    ker_le G hW hWf (hh i) (hg i) (hhW i) (hgW i) (h0 i)
  obtain ⟨S, hS⟩ := hWf
  have hind := indep_hw G hW hS h la hh hhW hli
  have hRW : ∀ i, G.gS {h i} ≤ W := fun i => G.gS_le (by simpa using hhW i) hW
  obtain ⟨π, hπ1, hπ2, hπ3⟩ := proj_exists (fun i => G.gS {h i}) hind hRW hsp
  have hπr : ∀ i x, π i x ∈ LinearMap.range (Lv G (h i)) := fun i x => by rw [range_Lv]; exact hπ1 i x
  refine ⟨∑ i, tr G (hk i) ∘ₗ (π i).codRestrict (LinearMap.range (Lv G (h i))) (hπr i), fun i c => ?_⟩
  have hmem : Lv G (h i) c ∈ G.gS {h i} := by rw [← range_Lv]; exact LinearMap.mem_range_self _ c
  rw [LinearMap.sum_apply, Finset.sum_eq_single i]
  · rw [LinearMap.comp_apply]
    have e : (π i).codRestrict (LinearMap.range (Lv G (h i))) (hπr i) (Lv G (h i) c) =
        ⟨Lv G (h i) c, LinearMap.mem_range_self _ c⟩ := by
      ext; exact hπ2 i _ hmem
    rw [e, tr_apply]
  · intro j _ hji
    rw [LinearMap.comp_apply]
    have e : (π j).codRestrict (LinearMap.range (Lv G (h j))) (hπr j) (Lv G (h i) c) = 0 := by
      ext; exact hπ3 j i (Ne.symm hji) _ hmem
    rw [e, map_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem eqExt {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {ι : Type} [Fintype ι] [DecidableEq ι]
    (h g : ι → V) (la : ι → Fin r → ℤ) (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W)
    (hli : LinearIndependent K h) (hsp : W ≤ ⨆ i, G.gS {h i})
    (hg : ∀ i, G.IsHW (la i) (g i)) (hgW : ∀ i, g i ∈ W) :
    ∃ φ : V →ₗ[K] V, (∀ i, φ (h i) = g i) ∧ (∀ x ∈ W, ∀ a b, φ (G.E a b x) = G.E a b (φ x)) ∧
      (∀ x ∈ W, φ x ∈ W) ∧ (∀ i, ∀ x ∈ G.gS {h i}, φ x ∈ G.gS {g i}) ∧
      (∀ i, g i ≠ 0 → ∀ x ∈ G.gS {h i}, φ x = 0 → x = 0) ∧
      (∀ i, g i = h i → ∀ x ∈ G.gS {h i}, φ x = x) ∧ (∀ i, g i = 0 → ∀ x ∈ G.gS {h i}, φ x = 0) := by
  obtain ⟨φ, hφ⟩ := eqExt_core G hW hWf h g la hh hhW hli hsp hg hgW
  have hrep : ∀ i, ∀ x ∈ G.gS {h i}, ∃ c, x = Lv G (h i) c := by
    intro i x hx
    rw [← range_Lv] at hx
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, rfl⟩
  have hgS : ∀ i c, Lv G (g i) c ∈ G.gS {g i} := fun i c => by
    rw [← range_Lv]; exact LinearMap.mem_range_self _ c
  refine ⟨φ, fun i => ?_, fun x hx a b => ?_, fun x hx => ?_, fun i x hx => ?_, fun i hgi x hx hx0 => ?_,
    fun i hgi x hx => ?_, fun i hgi x hx => ?_⟩
  · have := hφ i (Finsupp.single [] 1)
    rwa [Lv_single_nil, Lv_single_nil] at this
  · refine Submodule.iSup_induction (fun i => G.gS {h i}) (motive := fun x => φ (G.E a b x) = G.E a b (φ x))
      (hsp hx) (fun j y hy => ?_) (by simp) (fun x y hx hy => by simp only [map_add (f := _), hx, hy])
    obtain ⟨c, rfl⟩ := hrep j y hy
    rw [E_Lv, hφ, hφ, E_Lv]
  · refine Submodule.iSup_induction (fun i => G.gS {h i}) (motive := fun x => φ x ∈ W)
      (hsp hx) (fun j y hy => ?_) (by simp) (fun x y hx hy => by rw [map_add (f := _)]; exact W.add_mem hx hy)
    obtain ⟨c, rfl⟩ := hrep j y hy
    rw [hφ]
    exact (G.gS_le (by simpa using hgW j) hW) (hgS j c)
  · obtain ⟨c, rfl⟩ := hrep i x hx
    rw [hφ]; exact hgS i c
  · obtain ⟨c, rfl⟩ := hrep i x hx
    rw [hφ] at hx0
    exact LinearMap.mem_ker.mp (ker_le G hW hWf (hg i) (hh i) (hgW i) (hhW i) hgi (LinearMap.mem_ker.mpr hx0))
  · obtain ⟨c, rfl⟩ := hrep i x hx
    rw [hφ, hgi]
  · obtain ⟨c, rfl⟩ := hrep i x hx
    rw [hφ, hgi, Lv_zero]

theorem form_zero {W : Submodule K V} (hW : G.Stable W) {ι : Type} (h : ι → V) (la : ι → Fin r → ℤ)
    (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W) (hsp : W ≤ ⨆ i, G.gS {h i})
    (B : V →ₗ[K] V →ₗ[K] K) (hB : ∀ x ∈ W, ∀ y ∈ W, ∀ a b, B (G.E a b x) y = B x (G.E b a y))
    (h0 : ∀ i j, la i = la j → B (h i) (h j) = 0) : ∀ x ∈ W, ∀ y ∈ W, B x y = 0 := by

  have h1 : ∀ i j, B (h i) (h j) = 0 := by
    intro i j
    by_cases hij : la i = la j
    · exact h0 i j hij
    · obtain ⟨c, hc⟩ : ∃ c, la i c ≠ la j c := by
        by_contra hcon; exact hij (funext fun c => by by_contra hc; exact hcon ⟨c, hc⟩)
      have e := hB (h i) (hhW i) (h j) (hhW j) c c
      rw [G.E_diag_of_isWt (hh i).1, G.E_diag_of_isWt (hh j).1, map_smul, map_smul, LinearMap.smul_apply,
        smul_eq_mul, smul_eq_mul] at e
      have e2 : (((la i c : ℤ) : K) - ((la j c : ℤ) : K)) * B (h i) (h j) = 0 := by rw [sub_mul, e, sub_self]
      rcases mul_eq_zero.mp e2 with h3 | h3
      · exfalso; apply hc
        have : ((la i c : ℤ) : K) = ((la j c : ℤ) : K) := sub_eq_zero.mp h3
        exact_mod_cast this
      · exact h3

  have h2 : ∀ i, ∀ y ∈ W, B (h i) y = 0 := by
    intro i y hy
    have hle : ∀ j, G.gS {h j} ≤ W ⊓ LinearMap.ker (B (h i)) := by
      intro j
      refine (G.gS_le_Lw (hh j)).trans (G.Lw_le (h j) ⟨hhW j, LinearMap.mem_ker.mpr (h1 i j)⟩ ?_)
      intro a b hba x hx
      refine ⟨hW a b x hx.1, LinearMap.mem_ker.mpr ?_⟩
      rw [← hB (h i) (hhW i) x hx.1 b a, (hh i).2 b a hba, map_zero, LinearMap.zero_apply]
    exact LinearMap.mem_ker.mp ((iSup_le hle) (hsp hy)).2

  let U : Submodule K V :=
    { carrier := {x | x ∈ W ∧ ∀ y ∈ W, B x y = 0}
      add_mem' := fun {x x'} hx hx' => ⟨W.add_mem hx.1 hx'.1, fun y hy => by
        rw [map_add (f := _), LinearMap.add_apply, hx.2 y hy, hx'.2 y hy, add_zero]⟩
      zero_mem' := ⟨W.zero_mem, fun y _ => by rw [map_zero, LinearMap.zero_apply]⟩
      smul_mem' := fun t x hx => ⟨W.smul_mem t hx.1, fun y hy => by
        rw [map_smul, LinearMap.smul_apply, hx.2 y hy, smul_zero]⟩ }
  have hU : G.Stable U := fun a b x hx => ⟨hW a b x hx.1, fun y hy => by
    rw [hB x hx.1 y hy a b]; exact hx.2 _ (hW b a y hy)⟩
  have hle : ∀ i, G.gS {h i} ≤ U := fun i =>
    G.gS_le (by intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact ⟨hhW i, h2 i⟩) hU
  intro x hx y hy
  exact ((iSup_le hle) (hsp hx)).2 y hy

end GlX

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem isWt_iff (L : Letters N) (j : ℕ) (la : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GA p L j).IsWt la x ↔ x ∈ WtSpC p L j univ la := by
  show weightedHomogeneousComponent (wv L j) la x = x ↔ _
  rw [WtSpC, mem_restrictSupport_iff]
  constructor
  · intro h m hm c _
    have hw : IsWeightedHomogeneous (wv L j) x la := by
      rw [← h]; exact weightedHomogeneousComponent_isWeightedHomogeneous la x
    rw [← weight_wv, hw (mem_support_iff.mp (Finset.mem_coe.mp hm))]
  · intro h
    apply weightedHomogeneousComponent_eq_self
    intro m hm
    funext c
    rw [weight_wv]
    exact h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c (mem_univ c)

theorem isHW_iff (L : Letters N) (j : ℕ) (la : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GA p L j).IsHW la x ↔ x ∈ HWC p L j univ la := by
  unfold GlW.IsHW HWC
  rw [isWt_iff, Submodule.mem_inf]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun c d hcd => h2 c d hcd.2.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a b hab => h2 a b ⟨mem_univ _, mem_univ _, hab⟩⟩

noncomputable def fockB (p : ℕ) [Fact p.Prime] (σ : Type) [Fintype σ] [DecidableEq σ] :
    MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] :=
  LinearMap.mk₂ ℚ_[p] (fun F G => fock p F G)
    (fun F F' G => gammaIntegralityLemmas.fock_add_left F F' G)
    (fun c F G => by rw [gammaIntegralityLemmas.fock_smul_left, smul_eq_mul])
    (fun F G G' => by
      rw [gammaIntegralityLemmas.fock_symm F (G + G'), gammaIntegralityLemmas.fock_add_left, gammaIntegralityLemmas.fock_symm G F, gammaIntegralityLemmas.fock_symm G' F])
    (fun c F G => by rw [gammaIntegralityLemmas.fock_smul_right, smul_eq_mul])

theorem fockB_apply {σ : Type} [Fintype σ] [DecidableEq σ] (F G : MvPolynomial σ ℚ_[p]) :
    fockB p σ F G = fock p F G := rfl

theorem fock_XD {σ : Type} [Fintype σ] [DecidableEq σ] (u v : σ) (x y : MvPolynomial σ ℚ_[p]) :
    fock p (X u * pderiv v x) y = fock p x (X v * pderiv u y) := by
  rw [gammaIntegralityLemmas.fock_X_mul, gammaIntegralityLemmas.fock_symm, ← gammaIntegralityLemmas.fock_X_mul, gammaIntegralityLemmas.fock_symm]

theorem fock_glAct (L : Letters N) (j : ℕ) (c d : Fin r) (x y : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    fock p (glAct p L j c d x) y = fock p x (glAct p L j d c y) := by
  simp only [glAct, LinearMap.sum_apply]
  rw [gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.fock_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← fockB_apply, ← fockB_apply]
  split_ifs with h1 h2
  · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, fockB_apply]
    exact fock_XD _ _ _ _
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
      map_neg, fockB_apply]
    exact congrArg Neg.neg (fock_XD _ _ _ _)
  · simp

theorem wf_add_disj (j0 : ℕ) (a m : Fin N × Fin r →₀ ℕ) (ha : ∀ v, a v ≠ 0 → fsj N r j0 v)
    (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v) :
    gammaIntegralityLemmas.wf (p := p) (a + m) = gammaIntegralityLemmas.wf a * gammaIntegralityLemmas.wf m := by
  unfold gammaIntegralityLemmas.wf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : a v = 0
  · simp [hv]
  · have : m v = 0 := by
      by_contra h
      exact hm v h (ha v hv)
    simp [this]

theorem add_eq_add_iff_disj (j0 : ℕ) (a b m m' : Fin N × Fin r →₀ ℕ) (ha : ∀ v, a v ≠ 0 → fsj N r j0 v)
    (hb : ∀ v, b v ≠ 0 → fsj N r j0 v) (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v)
    (hm' : ∀ v, m' v ≠ 0 → ¬ fsj N r j0 v) : a + m = b + m' ↔ a = b ∧ m = m' := by
  constructor
  · intro h
    have h1 := congrArg (frst (fsj N r j0)) h
    have h2 := congrArg (ltr (fsj N r j0)) h
    rw [frst_add, frst_add, frst_of _ ha, frst_of _ hb, frst_of' _ hm, frst_of' _ hm', add_zero, add_zero] at h1
    rw [ltr_add, ltr_add, ltr_of _ ha, ltr_of _ hb, ltr_of' _ hm, ltr_of' _ hm', zero_add, zero_add] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem fock_mul_monomial_orthogonal (j0 : ℕ) (s t : Finset (Fin N × Fin r →₀ ℕ)) (cg cg' : (Fin N × Fin r →₀ ℕ) → ℚ_[p])
    (hs : ∀ a ∈ s, ∀ v, a v ≠ 0 → fsj N r j0 v) (ht : ∀ b ∈ t, ∀ v, b v ≠ 0 → fsj N r j0 v)
    (m m' : Fin N × Fin r →₀ ℕ) (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v)
    (hm' : ∀ v, m' v ≠ 0 → ¬ fsj N r j0 v) :
    fock p ((∑ a ∈ s, monomial a (cg a)) * monomial m 1) ((∑ b ∈ t, monomial b (cg' b)) * monomial m' 1) =
      if m = m' then fock p (∑ a ∈ s, monomial a (cg a)) (∑ b ∈ t, monomial b (cg' b)) *
        (m.prod fun _ k => (k.factorial : ℚ_[p])) else 0 := by
  rw [Finset.sum_mul, Finset.sum_mul, gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.prod_eq_wf]
  simp only [gammaIntegralityLemmas.fock_sum_right, monomial_mul, mul_one, gammaIntegralityLemmas.fock_monomial]
  by_cases hmm : m = m'
  · rw [if_pos hmm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b hb => ?_
    by_cases hab : a = b
    · rw [if_pos hab, if_pos (by rw [hab, hmm]), wf_add_disj j0 a m (hs a ha) hm]; ring
    · rw [if_neg hab, if_neg (fun h => hab ((add_eq_add_iff_disj j0 a b m m' (hs a ha) (ht b hb) hm hm').mp h).1),
        zero_mul]
  · rw [if_neg hmm]
    refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
    rw [if_neg (fun h => hmm ((add_eq_add_iff_disj j0 a b m m' (hs a ha) (ht b hb) hm hm').mp h).2)]

theorem fock_mul_mono (j0 : ℕ) {g g' : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hg : IsF (fsj N r j0) g)
    (hg' : IsF (fsj N r j0) g') (m m' : Fin N × Fin r →₀ ℕ) (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v)
    (hm' : ∀ v, m' v ≠ 0 → ¬ fsj N r j0 v) :
    fock p (g * monomial m 1) (g' * monomial m' 1) =
      if m = m' then fock p g g' * (m.prod fun _ k => (k.factorial : ℚ_[p])) else 0 := by
  have := fock_mul_monomial_orthogonal j0 g.support g'.support (fun a => AddMonoidAlgebra.coeff g a) (fun b => AddMonoidAlgebra.coeff g' b)
    (fun a ha => hg a ha) (fun b hb => hg' b hb) m m' hm hm'
  rwa [← g.as_sum, ← g'.as_sum] at this

theorem fock_ext_reduce (j0 : ℕ)
    (A φ1 φ2 : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) (c : ℚ_[p])
    (Cs : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hA : ∀ g q, IsL (fsj N r j0) q → A (g * q) = A g * q)
    (hAF : ∀ g, IsF (fsj N r j0) g → IsF (fsj N r j0) (A g))
    (h1 : ∀ x, IsF (fsj N r j0) (φ1 x)) (h2 : ∀ x, IsF (fsj N r j0) (φ2 x))
    (hcore : ∀ g ∈ Cs, ∀ g' ∈ Cs, fock p (A g) (φ1 g') = c * fock p (φ2 g) g')
    (u u' : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hu : ∀ m, slc (fsj N r j0) m u ∈ Cs)
    (hu' : ∀ m, slc (fsj N r j0) m u' ∈ Cs) :
    fock p (A u) (ext (fsj N r j0) φ1 u') = c * fock p (ext (fsj N r j0) φ2 u) u' := by
  classical
  set S : Finset (Fin N × Fin r →₀ ℕ) := (u.support ∪ u'.support).image (ltr (fsj N r j0)) with hS
  have hSu : ∀ m ∈ u.support, ltr (fsj N r j0) m ∈ S := fun m hm =>
    Finset.mem_image_of_mem _ (Finset.mem_union_left _ hm)
  have hSu' : ∀ m ∈ u'.support, ltr (fsj N r j0) m ∈ S := fun m hm =>
    Finset.mem_image_of_mem _ (Finset.mem_union_right _ hm)
  have hSl : ∀ m ∈ S, ∀ v, m v ≠ 0 → ¬ fsj N r j0 v := by
    intro m hm
    obtain ⟨m0, _, rfl⟩ := Finset.mem_image.mp hm
    exact ltr_isL _ m0
  have hSL : ∀ m ∈ S, IsL (fsj N r j0) (monomial m (1 : ℚ_[p])) := by
    intro m hm
    obtain ⟨m0, _, rfl⟩ := Finset.mem_image.mp hm
    exact isL_monomial_ltr _ m0 1
  have hAu : A u = ∑ m ∈ S, A (slc (fsj N r j0) m u) * monomial m 1 := by
    conv_lhs => rw [eq_sum_sl (fsj N r j0) u S hSu]

    rw [map_sum]
    exact Finset.sum_congr rfl fun m hm => hA _ _ (hSL m hm)
  rw [hAu, ext_eq_sum (fsj N r j0) φ1 u' S hSu', ext_eq_sum (fsj N r j0) φ2 u S hSu]
  conv_rhs => rw [eq_sum_sl (fsj N r j0) u' S hSu']
  rw [gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.fock_sum_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [gammaIntegralityLemmas.fock_sum_right, gammaIntegralityLemmas.fock_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' hm' => ?_
  rw [fock_mul_mono j0 (hAF _ (sl_isF _ m u)) (h1 _) m m' (hSl m hm) (hSl m' hm'),
    fock_mul_mono j0 (h2 _) (sl_isF _ m' u') m m' (hSl m hm) (hSl m' hm')]
  split_ifs with h
  · rw [hcore _ (hu m) _ (hu' m')]; ring
  · simp

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

section OpsAux

variable {k σ : Type} [Field k]

theorem tiePhi_mem' {r : ℕ} (w e : Fin r → σ) (o n z : ℕ) :
    (Formalism.GM.tiePhi w e o n z : Module.End k (MvPolynomial σ k)) ∈ FockB.Ops (Set.range w ∪ Set.range e) := by
  unfold Formalism.GM.tiePhi
  refine sum_mem fun j _ => Subalgebra.smul_mem _ ?_ _
  rw [← Module.End.mul_eq_comp]
  refine mul_mem (pow_mem ?_ _) (pow_mem ?_ _)
  · exact FockB.mulLeft_mem (sum_mem fun c _ => mul_mem (FockB.X_mem (Or.inl ⟨c, rfl⟩))
      (FockB.X_mem (Or.inr ⟨c, rfl⟩)))
  · unfold Formalism.GM.tieF
    refine sum_mem fun c _ => ?_
    rw [← Module.End.mul_eq_comp]
    exact mul_mem (FockB.pderiv_mem (Or.inl ⟨c, rfl⟩)) (FockB.pderiv_mem (Or.inr ⟨c, rfl⟩))

theorem ops_mul_free (S : Set σ) {T : Module.End k (MvPolynomial σ k)} (hT : T ∈ FockB.Ops S)
    (q : MvPolynomial σ k) (hq : ∀ m ∈ q.support, ∀ v ∈ S, m v = 0) (g : MvPolynomial σ k) :
    T (g * q) = T g * q := by
  have hc : Commute (LinearMap.mulRight k q : Module.End k (MvPolynomial σ k)) T := by
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hT (fun b hb => ?_)
    obtain ⟨u, hu, rfl | rfl⟩ := hb
    · rw [commute_iff_eq]
      refine LinearMap.ext fun f => ?_
      simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
      ring
    · rw [commute_iff_eq]
      refine LinearMap.ext fun f => ?_
      simp only [Module.End.mul_apply, LinearMap.mulRight_apply, Derivation.coeFn_coe]
      rw [pderiv_mul, ProjS.pderiv_of_free u q (fun m hm => hq m hm u hu), mul_zero, add_zero]
  have := LinearMap.congr_fun hc.eq g
  simp only [Module.End.mul_apply, LinearMap.mulRight_apply] at this
  exact this.symm

theorem ops_keep_pred (S : Set σ) (P : σ → Prop) (hS : ∀ v ∈ S, P v) {T : Module.End k (MvPolynomial σ k)}
    (hT : T ∈ FockB.Ops S) (g : MvPolynomial σ k) (hg : ∀ m ∈ g.support, ∀ v, m v ≠ 0 → P v) :
    ∀ m ∈ (T g).support, ∀ v, m v ≠ 0 → P v := by
  have h1 := ops_keep_supp S {m : σ →₀ ℕ | ∀ v, m v ≠ 0 → P v} (fun m m' h hm v hv => by
    by_cases hvS : v ∈ S
    · exact hS v hvS
    · exact hm v (by rw [h v hvS]; exact hv)) hT g (by
      rw [mem_restrictSupport_iff]
      intro m hm
      exact hg m (Finset.mem_coe.mp hm))
  rw [mem_restrictSupport_iff] at h1
  intro m hm
  exact h1 (Finset.mem_coe.mpr hm)

theorem ext_ops_comm [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs] (S : Set σ) (hS : ∀ v ∈ S, ¬ fs v)
    {T : Module.End k (MvPolynomial σ k)} (hT : T ∈ FockB.Ops S)
    (φ : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (hφ : ∀ x, IsF fs (φ x)) (x : MvPolynomial σ k) :
    ext fs φ (T x) = T (ext fs φ x) := by
  have hfree : ∀ g : MvPolynomial σ k, IsF fs g → ∀ m ∈ g.support, ∀ v ∈ S, m v = 0 := by
    intro g hg m hm v hv
    by_contra h
    exact hS v hv (hg m hm v h)
  induction x using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [monomial_split fs m a]
    have hg := isF_monomial_frst (K := k) fs m a
    have hq := isL_monomial_ltr (K := k) fs m 1
    have hTq : IsL fs (T (monomial (ltr fs m) 1)) := ops_keep_pred S (fun v => ¬ fs v) hS hT _ hq
    have e1 : T (monomial (frst fs m) a * monomial (ltr fs m) 1) = monomial (frst fs m) a * T (monomial (ltr fs m) 1) := by
      rw [mul_comm, ops_mul_free S hT _ (hfree _ hg), mul_comm]
    have e2 : T (φ (monomial (frst fs m) a) * monomial (ltr fs m) 1) =
        φ (monomial (frst fs m) a) * T (monomial (ltr fs m) 1) := by
      rw [mul_comm, ops_mul_free S hT _ (hfree _ (hφ _)), mul_comm]
    rw [ext_mul fs φ hg hq, e1, ext_mul fs φ hg hTq, e2]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tieE_rename {τ : Type} {r : ℕ} (ι : σ → τ) (w e : Fin r → σ) (F : MvPolynomial σ k) :
    Formalism.GM.tieE (fun c => ι (w c)) (fun c => ι (e c)) (rename ι F) = rename ι (Formalism.GM.tieE w e F) := by

  simp only [Formalism.GM.tieE, LinearMap.mulLeft_apply, map_mul, map_sum, rename_X]

theorem tieF_rename {τ : Type} {r : ℕ} (ι : σ → τ) (hι : Function.Injective ι) (w e : Fin r → σ)
    (F : MvPolynomial σ k) :
    Formalism.GM.tieF (fun c => ι (w c)) (fun c => ι (e c)) (rename ι F) = rename ι (Formalism.GM.tieF w e F) := by

  simp only [Formalism.GM.tieF, LinearMap.sum_apply, LinearMap.comp_apply, Derivation.coeFn_coe, map_sum,
  pderiv_rename hι]

theorem tiePhi_rename {τ : Type} {r : ℕ} (ι : σ → τ) (hι : Function.Injective ι) (w e : Fin r → σ) (o n z : ℕ)
    (F : MvPolynomial σ k) :
    Formalism.GM.tiePhi (fun c => ι (w c)) (fun c => ι (e c)) o n z (rename ι F) =
      rename ι (Formalism.GM.tiePhi w e o n z F) := by
  have hE : ∀ (j : ℕ) (G : MvPolynomial σ k),
      ((Formalism.GM.tieE (fun c => ι (w c)) (fun c => ι (e c))) ^ j) (rename ι G) =
        rename ι (((Formalism.GM.tieE w e) ^ j) G) := by
    intro j
    induction j with
    | zero => intro G; simp
    | succ j ih => intro G; rw [pow_succ, Module.End.mul_apply, tieE_rename, ih, pow_succ, Module.End.mul_apply]
  have hF : ∀ (j : ℕ) (G : MvPolynomial σ k),
      ((Formalism.GM.tieF (fun c => ι (w c)) (fun c => ι (e c))) ^ j) (rename ι G) =
        rename ι (((Formalism.GM.tieF w e) ^ j) G) := by
    intro j
    induction j with
    | zero => intro G; simp
    | succ j ih => intro G; rw [pow_succ, Module.End.mul_apply, tieF_rename ι hι, ih, pow_succ, Module.End.mul_apply]

  simp only [Formalism.GM.tiePhi, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, hF, hE]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← AlgHom.toLinearMap_apply (rename ι), map_smul]
  rfl

end OpsAux

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem fock_rename {σ τ : Type} (ι : σ → τ) (hι : Function.Injective ι) (F F' : MvPolynomial σ ℚ_[p]) :
    fock p (rename ι F) (rename ι F') = fock p F F' := by
  classical
  unfold fock
  rw [support_rename_of_injective hι, Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hι h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_rename_mapDomain ι hι, coeff_rename_mapDomain ι hι, Finsupp.prod_mapDomain_index_inj hι]

theorem fock_nondeg {σ : Type} (z : MvPolynomial σ ℚ_[p]) (h : ∀ y, fock p z y = 0) : z = 0 := by
  by_contra hz
  obtain ⟨m, hm⟩ : ∃ m, m ∈ z.support := by
    by_contra hc; push Not at hc
    exact hz (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
  have h1 := Formalism.CountingSumsFrames.fock_monomial z m hm
  rw [h] at h1
  have h2 : (m.prod fun _ k => (k.factorial : ℚ_[p])) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => by exact_mod_cast Nat.factorial_ne_zero _
  exact (mul_ne_zero (mem_support_iff.mp hm) h2) h1.symm

theorem phi_mem' (L : Letters N) (T : TieData) (j : Fin T.t) (h : T.pos j + 1 < N) :
    (T.phi p L j : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
      FockB.Ops {v : Fin N × Fin r | (v.1 : ℕ) = T.pos j ∨ (v.1 : ℕ) = T.pos j + 1} := by
  unfold TieData.phi
  rw [dif_pos h]
  unfold tiePhiAt
  refine FockB.ops_mono ?_ (tiePhi_mem' _ _ _ _ _)
  rintro v (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · left; rfl
  · right; rfl

section Comparison₂

variable (L : Letters N) (T : TieData) (hadm : T.Admissible L) (i : Fin T.t)

include hadm

theorem phi_mul_later (g q : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hq : IsL (fsj N r (T.pos i + 1 + 1)) q) :
    T.phi p L i (g * q) = T.phi p L i g * q := by
  have hK := hK_of_adm L T hadm i
  refine ops_mul_free _ (phi_mem' L T i (by omega)) q (fun m hm v hv => ?_) g
  by_contra h
  have := hq m hm v h
  simp only [fsj] at this
  rcases hv with hv | hv <;> omega

theorem phi_isF (g : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hg : IsF (fsj N r (T.pos i + 1 + 1)) g) :
    IsF (fsj N r (T.pos i + 1 + 1)) (T.phi p L i g) := by
  have hK := hK_of_adm L T hadm i
  refine ops_keep_pred _ (fsj N r (T.pos i + 1 + 1)) (fun v hv => ?_) (phi_mem' L T i (by omega)) g hg
  simp only [fsj]
  rcases hv with hv | hv <;> omega

theorem phi_glAct (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    T.phi p L i (glAct p L (T.pos i + 1 + 1) c d x) = glAct p L (T.pos i + 1 + 1) c d (T.phi p L i x) := by
  classical
  obtain ⟨h, hva, hvb⟩ := hadm.2.1 i
  set a : Fin N := ⟨T.pos i, by omega⟩ with ha
  set b : Fin N := ⟨T.pos i + 1, h⟩ with hb
  have hE : ∀ (c d : Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
      glAct p L (T.pos i + 1 + 1) c d (Formalism.GM.tieE (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) y) =
        Formalism.GM.tieE (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (glAct p L (T.pos i + 1 + 1) c d y) := by
    intro c d y
    simp only [Formalism.GM.tieE, LinearMap.mulLeft_apply]
    rw [Formalism.GM.M.FB.glAct_mul]
    have h0 : glAct p L (T.pos i + 1 + 1) c d (∑ e : Fin r, X (a, e) * X (b, e)) = 0 := by

      rw [map_sum]
      have : ∀ e : Fin r, glAct p L (T.pos i + 1 + 1) c d (X (a, e) * X (b, e)) =
          (if e = c then -(X (a, c) * X (b, d)) else 0) + (if e = d then X (a, c) * X (b, d) else 0) := by
        intro e
        have hXa : glAct p L (T.pos i + 1 + 1) c d (X (a, e)) = if e = d then X (a, c) else 0 := by
          rw [glAct_X_gen, if_pos (show (a : ℕ) < T.pos i + 1 + 1 by show T.pos i < _; omega), hva]; simp
        have hXb : glAct p L (T.pos i + 1 + 1) c d (X (b, e)) = if e = c then -X (b, d) else 0 := by
          rw [glAct_X_gen, if_pos (show (b : ℕ) < T.pos i + 1 + 1 by show T.pos i + 1 < _; omega), hvb]; simp
        rw [Formalism.GM.M.FB.glAct_mul, hXa, hXb]
        split_ifs with h1 h2 h2
        · subst h1; subst h2; ring
        · subst h1; ring
        · subst h2; ring
        · ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    rw [h0, mul_zero, add_zero]
  have hF : ∀ (c d : Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
      glAct p L (T.pos i + 1 + 1) c d (Formalism.GM.tieF (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) y) =
        Formalism.GM.tieF (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (glAct p L (T.pos i + 1 + 1) c d y) := by
    intro c d y
    rw [← sub_eq_zero]
    apply fock_nondeg
    intro u
    rw [gammaIntegralityLemmas.fock_symm, sub_eq_add_neg, gammaIntegralityLemmas.fock_symm, gammaIntegralityLemmas.fock_add_left, ← neg_one_smul ℚ_[p],
      gammaIntegralityLemmas.fock_smul_left, fock_glAct, gammaIntegralityLemmas.fock_symm _ (glAct p L (T.pos i + 1 + 1) d c u),
      ← gammaIntegralityLemmas.fock_E, ← hE, gammaIntegralityLemmas.fock_symm, ← fock_glAct,
      gammaIntegralityLemmas.fock_symm (Formalism.GM.tieF _ _ _) u, ← gammaIntegralityLemmas.fock_E, gammaIntegralityLemmas.fock_symm _ (Formalism.GM.tieE _ _ u)]
    ring
  have cE : Commute (glAct p L (T.pos i + 1 + 1) c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
      (Formalism.GM.tieE (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c))) := by
    rw [commute_iff_eq]; exact LinearMap.ext fun y => hE c d y
  have cF : Commute (glAct p L (T.pos i + 1 + 1) c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
      (Formalism.GM.tieF (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c))) := by
    rw [commute_iff_eq]; exact LinearMap.ext fun y => hF c d y
  have cP : Commute (glAct p L (T.pos i + 1 + 1) c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
      (T.phi p L i) := by
    unfold TieData.phi
    rw [dif_pos h]
    unfold tiePhiAt Formalism.GM.tiePhi
    refine Commute.sum_right _ _ _ fun j _ => Commute.smul_right ?_ _
    rw [← Module.End.mul_eq_comp]
    exact (cE.pow_right j).mul_right (cF.pow_right j)
  exact (LinearMap.congr_fun cP.eq x).symm

theorem phi_ext_comm (j : Fin T.t) (hij : i < j)
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hφ : ∀ x, IsF (fsj N r (T.pos i + 1 + 1)) (φ x)) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ext (fsj N r (T.pos i + 1 + 1)) φ (T.phi p L j x) = T.phi p L j (ext (fsj N r (T.pos i + 1 + 1)) φ x) := by
  have hK := hK_of_adm L T hadm j
  have hlt : T.pos i < T.pos j := hadm.1 hij
  have hne : T.pos j ≠ T.pos i + 1 := by
    intro he
    obtain ⟨h1, -, hb⟩ := hadm.2.1 i
    obtain ⟨h2, ha, -⟩ := hadm.2.1 j
    have : (⟨T.pos j, by omega⟩ : Fin N) = ⟨T.pos i + 1, h1⟩ := Fin.ext he
    rw [this, hb] at ha
    exact Bool.false_ne_true ha
  refine ext_ops_comm (fsj N r (T.pos i + 1 + 1)) _ (fun v hv => ?_) (phi_mem' L T j (by omega)) φ hφ x
  simp only [fsj]
  rcases hv with hv | hv <;> omega

end Comparison₂

section Tie2

variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)

include hadm

theorem fock_Ffull (ρ : Fin r) (n : Fin T.t → ℕ) (f f' : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    fock p (T.Ffull p (LL.setTies T n) i ρ (n i) f) (T.Ffull p (LL.setTies T n) i ρ (n i) f') =
      fock p (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f)
        (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f') := by
  rw [Ffull_eq, Ffull_eq]
  exact fock_rename _ (inclusion_prodMap_injective (hK_of_adm LL T hadm i)) _ _

theorem phi_Ffull (ρ : Fin r) (n : Fin T.t → ℕ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) f) =
      rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2))
        (tiePhiAt p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) (Fin.castSucc (Fin.last (T.pos i)))
          (Fin.last (T.pos i + 1)) (T.z i) (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f)) := by
  have hK := hK_of_adm LL T hadm i
  have h : T.pos i + 1 < N := by omega
  rw [Ffull_eq]
  unfold TieData.phi
  rw [dif_pos h]
  unfold tiePhiAt
  rw [← tiePhi_rename _ (inclusion_prodMap_injective hK)]
  have e1 : ιF N (T.pos i + 1) (Fin.castSucc (Fin.last (T.pos i))) = ⟨T.pos i, by omega⟩ := by
    apply Fin.ext; rw [ιF_val hK]; simp
  have e2 : ιF N (T.pos i + 1) (Fin.last (T.pos i + 1)) = ⟨T.pos i + 1, h⟩ := by
    apply Fin.ext; rw [ιF_val hK]; simp
  have d1 : (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)).deg (Fin.castSucc (Fin.last (T.pos i))) =
      (LL.setTies T n).deg ⟨T.pos i, by omega⟩ := by
    rw [Formalism.GM.FrozenVariableComponents.snoc_deg_castSucc]
    simp [Letters.takeD, (by omega : T.pos i < N)]
  have d2 : (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)).deg (Fin.last (T.pos i + 1)) =
      (LL.setTies T n).deg ⟨T.pos i + 1, h⟩ := by
    rw [Formalism.GM.FrozenVariableComponents.snoc_deg_last, setTies_deg_eta LL T hadm i n h]
  rw [d1, d2]
  simp only [e1, e2]

theorem gam_eq (ρ : Fin r) (n : Fin T.t → ℕ) (f f' : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    tieGam p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (T.z i) (n i) f f' =
      (((((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) + n i + r + T.z i - 1).choose
          (((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i))) : ℕ) : ℚ_[p]) *
        fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) f))
          (T.Ffull p (LL.setTies T n) i ρ (n i) f') /
        ((((n i - ((LL.setTies T n).takeD (T.pos i + 1)).total).factorial *
            ((LL.setTies T n).takeD (T.pos i + 1)).total.factorial : ℕ) : ℚ_[p]) *
          ∏ x, ((((LL.setTies T n).takeD (T.pos i + 1)).deg x).factorial : ℚ_[p])) := by
  rw [phi_Ffull LL T hadm i ρ n f, Ffull_eq, fock_rename _ (inclusion_prodMap_injective (hK_of_adm LL T hadm i))]
  rfl

end Tie2

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

structure IsProjC [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (Pi : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) : Prop where
  comm : ∀ c d x, Pi (glAct p L j0 c d x) = glAct p L j0 c d (Pi x)
  wh : ∀ ν x, x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν →
    Pi x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν
  pol : ∀ L' : Letters N, L'.vec = L.vec → ∀ x ∈ Pol p r L', Pi x ∈ Pol p r L'
  ycond : ∀ x k, Pi x ∈ YCond p L (J k) (Mup J M j0 k)
  fix : ∀ L' : Letters N, L'.vec = L.vec → ∀ x ∈ Pol p r L', (∀ k, x ∈ YCond p L (J k) (Mup J M j0 k)) → Pi x = x
  int : ∀ x ∈ PolZ p r L, ((p : ℚ_[p]) ^ e) • Pi x ∈ IntPol p (Fin N × Fin r)
  mul : ∀ g q, IsL (fsj N r j0) q → Pi (g * q) = Pi g * q

theorem wtsp_iff_wh (L : Letters N) (j : ℕ) (μ : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ WtSpC p L j univ μ ↔ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j) μ := by
  rw [WtSpC, mem_restrictSupport_iff, mem_weightedHomogeneousSubmodule]
  constructor
  · intro h m hm
    funext c
    rw [weight_wv]
    exact h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c (Finset.mem_univ c)
  · intro h m hm c _
    rw [← weight_wv, h (mem_support_iff.mp (Finset.mem_coe.mp hm))]

theorem hwc_keep (L : Letters N) (j : ℕ) (la : Fin r → ℤ)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c d x, Q (glAct p L j c d x) = glAct p L j c d (Q x)) :
    ∀ x ∈ HWC p L j univ la, Q x ∈ HWC p L j univ la := by
  intro x hx
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hx
  refine Submodule.mem_inf.mpr ⟨comm_wtsp L j Q (fun c x => hc c c x) la x h1, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h2 ⊢
  intro c d hcd
  rw [← hc, h2 c d hcd, map_zero]

theorem iso_keep_comm (L : Letters N) (j : ℕ)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c d x, Q (glAct p L j c d x) = glAct p L j c d (Q x)) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p L j univ la, Q x ∈ IsoC p L j univ la :=
  isoC_keep L j la Q hc (hwc_keep L j la Q hc)

theorem iso_keep_glAct (L : Letters N) {j j0 : ℕ} (hj : j ≤ j0) (c d : Fin r) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p L j univ la, glAct p L j0 c d x ∈ IsoC p L j univ la := by
  intro x hx
  rw [glAct_split L hj c d, LinearMap.add_apply]
  exact Submodule.add_mem _ (isoC_glStable L j la c d x hx)
    (iso_keep_comm L j (midAct p L j j0 c d) (fun c' d' y => midAct_comm L j j0 c d c' d' y) la x hx)

theorem iso_keep_mul (L : Letters N) {j j0 : ℕ} (hj : j ≤ j0) {q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hq : IsL (fsj N r j0) q) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p L j univ la, LinearMap.mulRight ℚ_[p] q x ∈ IsoC p L j univ la :=
  iso_keep_comm L j (LinearMap.mulRight ℚ_[p] q) (fun c d x => by
    simp only [LinearMap.mulRight_apply]
    exact (glAct_mul_kill L j c d x (killL_of_isL hj hq)).symm) la

theorem isTypeProj_congr (L L' : Letters N) (h : L'.vec = L.vec) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p L j Cs T P) : IsTypeProj p L' j Cs T P := by
  obtain ⟨v, d⟩ := L
  obtain ⟨v', d'⟩ := L'
  simp only at h
  subst h
  exact hP

theorem ycond_congr [NeZero r] (L L' : Letters N) (h : L'.vec = L.vec) (j : ℕ) (Mt : WithTop ℤ) :
    YCond p (r := r) L' j Mt = YCond p (r := r) L j Mt := by
  obtain ⟨v, d⟩ := L
  obtain ⟨v', d'⟩ := L'
  simp only at h
  subst h
  rfl

theorem lcomp_fixed {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι] (P : ι → V →ₗ[K] V)
    (x : V) (hx : ∀ j, P j x = x) : ∀ l : List ι, lcomp P l x = x
  | [] => rfl
  | a :: l => by rw [lcomp_cons, LinearMap.comp_apply, lcomp_fixed P x hx l, hx a]

theorem lcomp_commQ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι] (P : ι → V →ₗ[K] V)
    (Q : V →ₗ[K] V) (h : ∀ j x, P j (Q x) = Q (P j x)) : ∀ (l : List ι) (x : V), lcomp P l (Q x) = Q (lcomp P l x)
  | [], _ => rfl
  | a :: l, x => by
    rw [lcomp_cons, LinearMap.comp_apply, LinearMap.comp_apply, lcomp_commQ P Q h l x, h a]

theorem projC [NeZero r] (L : Letters N) (ρ : Fin r) (e1 j0 : ℕ) (hj0 : j0 ≤ N) (hHP : HypP p L ρ e1) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    ∃ Pi : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
      IsProjC L j0 (e1 * j0) J M Pi := by
  obtain ⟨hP1, hP2⟩ := hHP
  let Tj : Fin j0 → Set (Fin r → ℤ) := fun j => {la | ∀ k, J k = (j : ℕ) → ((la 0 : ℤ) : WithTop ℤ) ≤ M k}
  have hex : ∀ j : Fin j0, ∃ P, IsTypeProj p L j univ (Tj j) P ∧ (∀ F G, fock p (P F) G = fock p F (P G)) ∧
      ∀ F ∈ PolZ p r L, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r) :=
    fun j => hP1 j (le_trans (le_of_lt j.isLt) hj0) univ (Or.inl rfl) (Tj j)
      (fun la la' h => by rw [show la = la' from funext fun c => h c (mem_univ c)])
  choose P hPt _hPsa hPint using hex
  have hPP : ∀ j x, P j (P j x) = P j x := fun j x => LinearMap.congr_fun (hPt j).1 x
  have hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x) := by
    intro j j' x
    rcases le_total (j : ℕ) (j' : ℕ) with h | h
    · exact LinearMap.congr_fun (hP2 j j' univ univ (Tj j) (Tj j') (P j) (P j') h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j) (hPt j')) x
    · exact (LinearMap.congr_fun (hP2 j' j univ univ (Tj j') (Tj j) (P j') (P j) h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j') (hPt j)) x).symm
  have hPpol : ∀ L' : Letters N, L'.vec = L.vec → ∀ j, ∀ x ∈ Pol p r L', P j x ∈ Pol p r L' := fun L' hL' j =>
    typeProj_pol L' j (Tj j) (P j) (isTypeProj_congr L L' hL' j univ (Tj j) (P j) (hPt j))
  have hgl : ∀ c d x, lcomp P (List.finRange j0) (glAct p L j0 c d x) =
      glAct p L j0 c d (lcomp P (List.finRange j0) x) := fun c d x =>
    lcomp_commQ P (glAct p L j0 c d) (fun j y => typeProj_comm L j (Tj j) (P j) (hPt j) (glAct p L j0 c d)
      (fun la => iso_keep_glAct L (le_of_lt j.isLt) c d la) y) _ x
  refine ⟨lcomp P (List.finRange j0), hgl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ν x hx
    rw [← wtsp_iff_wh] at hx ⊢
    exact comm_wtsp L j0 _ (fun c y => hgl c c y) ν x hx
  · intro L' hL' x hx
    exact lcomp_keep P (Pol p r L' : Set _) _ (fun j _ u hu => hPpol L' hL' j u hu) x hx
  · intro x k
    by_cases hk : J k < j0
    · rw [Mup, if_pos hk]
      have hfix : P ⟨J k, hk⟩ (lcomp P (List.finRange j0) x) = lcomp P (List.finRange j0) x :=
        lcomp_fix P hPP hcomm _ ⟨J k, hk⟩ (List.mem_finRange _) x
      have h1 : lcomp P (List.finRange j0) x ∈ LinearMap.range (P ⟨J k, hk⟩) := ⟨_, hfix⟩
      rw [(hPt ⟨J k, hk⟩).2.1] at h1
      exact (iSup₂_le fun la hla => isoC_le_ycond L (J k) la (M k) (hla k rfl)) h1
    · rw [Mup, if_neg hk, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top
  · intro L' hL' x hxP hxY
    refine lcomp_fixed P x (fun j => ?_) _
    have hPt' := isTypeProj_congr L L' hL' j univ (Tj j) (P j) (hPt j)
    set S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
      Pol p r L' ⊓ ⨅ (k : Fin q) (_ : J k = (j : ℕ)), YCond p (r := r) L' j (M k) with hSdef
    have hmemS : ∀ x, x ∈ S ↔ x ∈ Pol p r L' ∧ ∀ k, J k = (j : ℕ) → x ∈ YCond p (r := r) L' j (M k) := by
      intro x; simp only [hSdef, Submodule.mem_inf, Submodule.mem_iInf]
    have hfix := proj_fix L' j (Tj j) (P j) hPt' S inf_le_left
      (fun c d x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨Formalism.CountingSumsFrames.glAct_pol L' j c d x hx.1, fun k hk => ycond_glStable L' j (M k) c d x (hx.2 k hk)⟩)
      (fun x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨hPpol L' hL' j x hx.1, fun k hk => typeProj_ycond L' j (Tj j) (P j) hPt' (M k) x (hx.2 k hk)⟩)
      (fun h hh hh0 μ hμ => by
        rw [hmemS] at hh
        intro k hk
        have h1 := ycond_le_supp L' j (M k) (hh.2 k hk)
        obtain ⟨m, hm⟩ : ∃ m, m ∈ h.support := by
          by_contra hc; push Not at hc
          exact hh0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
        rw [mem_restrictSupport_iff] at h1
        have h2 := h1 (Finset.mem_coe.mpr hm)
        have h3 := (Submodule.mem_inf.mp hμ).1
        rw [WtSpC, mem_restrictSupport_iff] at h3
        have h4 := h3 (Finset.mem_coe.mpr hm) 0 (Finset.mem_univ _)
        simp only [Set.mem_ofPred_eq] at h2
        rw [h4] at h2
        exact h2)
    apply hfix
    rw [hmemS]
    refine ⟨hxP, fun k hk => ?_⟩
    have := hxY k
    rw [Mup, if_pos (by rw [hk]; exact j.isLt), hk] at this
    rw [ycond_congr L L' hL']
    exact this
  · intro x hx
    have := lcomp_int L e1 P (hPpol L rfl) hPint (List.finRange j0) x hx
    rw [List.length_finRange] at this
    exact (Submodule.mem_inf.mp this).2
  · intro g q hq
    have := lcomp_commQ P (LinearMap.mulRight ℚ_[p] q) (fun j y => typeProj_comm L j (Tj j) (P j) (hPt j)
      (LinearMap.mulRight ℚ_[p] q) (fun la => iso_keep_mul L (le_of_lt j.isLt) hq la) y) (List.finRange j0) g
    simpa only [LinearMap.mulRight_apply] using this

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

section Leib

variable {σ : Type} (A : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
  (hA : ∀ a b, A (a * b) = a * A b + b * A a)

include hA

theorem pow_mul_killed {u' : MvPolynomial σ ℚ_[p]} (hu' : A u' = 0) (k : ℕ) :
    ∀ f, (A ^ k) (f * u') = (A ^ k) f * u' := by
  induction k with
  | zero => intro f; simp
  | succ k ih =>
    intro f
    rw [pow_succ A k, Module.End.mul_apply, Module.End.mul_apply, hA, hu', mul_zero, zero_add, mul_comm u', ih]

theorem pow_succ_mul_gen {u u' : MvPolynomial σ ℚ_[p]} (hu : A u = u') (hu' : A u' = 0) (k : ℕ) :
    ∀ f, (A ^ (k + 1)) (f * u) = (A ^ (k + 1)) f * u + ((k + 1 : ℕ) : ℚ_[p]) • ((A ^ k) f * u') := by
  induction k with
  | zero =>
    intro f
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, hA, hu, Nat.cast_one, one_smul]
    ring
  | succ k ih =>
    intro f
    have e1 : (A ^ (k + 1 + 1)) (f * u) = (A ^ (k + 1)) (A (f * u)) := by
      rw [pow_succ A (k + 1), Module.End.mul_apply]
    have e2 : (A ^ (k + 1 + 1)) f = (A ^ (k + 1)) (A f) := by
      rw [pow_succ A (k + 1), Module.End.mul_apply]
    have e3 : (A ^ (k + 1)) f = (A ^ k) (A f) := by
      rw [pow_succ A k, Module.End.mul_apply]
    rw [e1, e2, hA, hu, map_add (f := _), pow_mul_killed A hA hu' (k + 1), mul_comm u, ih, ← e3,
      Nat.cast_succ (k + 1), add_smul, one_smul]
    abel

end Leib

theorem glAct_C' (L : Letters N) (j : ℕ) (c d : Fin r) (a : ℚ_[p]) :
    glAct p L j c d (C a) = 0 := by
  rw [Formalism.GM.FrozenVariableComponents.glAct_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs <;> simp

theorem glAct_X_int (L : Letters N) (j : ℕ) (c d : Fin r) (v : Fin N × Fin r) :
    glAct p L j c d (X v) ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨i, a⟩ := v
  rw [glAct_X_gen]
  split_ifs
  · exact FrozenVariableLemmas.intPol_X p _
  · exact Submodule.zero_mem _
  · exact Submodule.neg_mem _ (FrozenVariableLemmas.intPol_X p _)
  · exact Submodule.zero_mem _
  · exact Submodule.zero_mem _

theorem glAct_glAct_X (L : Letters N) (j : ℕ) (c d : Fin r) (hcd : c ≠ d) (v : Fin N × Fin r) :
    glAct p L j c d (glAct p L j c d (X v)) = 0 := by
  obtain ⟨i, a⟩ := v
  rw [glAct_X_gen]
  split_ifs with h1 h2 h3 h3
  · rw [glAct_X_gen, if_pos h1, if_pos h2, if_neg hcd]
  · exact map_zero _
  · rw [map_neg, glAct_X_gen, if_pos h1, if_neg h2, if_neg (Ne.symm hcd), neg_zero]
  · exact map_zero _
  · exact map_zero _

theorem divpow_int (L : Letters N) (j : ℕ) (c d : Fin r) (hcd : c ≠ d) (k : ℕ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ IntPol p (Fin N × Fin r)) :
    (((k.factorial : ℚ_[p]))⁻¹) • ((glAct p L j c d) ^ k) x ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨x₀, rfl⟩ := (FrozenVariableLemmas.intPol_iff p x).mp hx
  clear hx
  induction x₀ using MvPolynomial.induction_on generalizing k with
  | C a =>
    rw [map_C]
    cases k with
    | zero => simpa using (FrozenVariableLemmas.intPol_iff p _).mpr ⟨C a, map_C _ _⟩
    | succ k =>
      rw [pow_succ, Module.End.mul_apply, glAct_C', map_zero, smul_zero]
      exact Submodule.zero_mem _
  | add f g hf hg =>
    rw [map_add (f := _), map_add (f := _), smul_add]
    exact Submodule.add_mem _ (hf k) (hg k)
  | mul_X f v hf =>
    rw [map_mul, map_X]
    cases k with
    | zero =>
      have := hf 0
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, Module.End.one_apply, one_smul] at this ⊢
      exact FrozenVariableLemmas.intPol_mul p this (FrozenVariableLemmas.intPol_X p v)
    | succ k =>
      rw [pow_succ_mul_gen (glAct p L j c d) (fun a b => Formalism.GM.M.FB.glAct_mul L j c d a b) rfl
        (glAct_glAct_X L j c d hcd v) k, smul_add, smul_smul]
      have e : (((k + 1).factorial : ℚ_[p]))⁻¹ * ((k + 1 : ℕ) : ℚ_[p]) = ((k.factorial : ℚ_[p]))⁻¹ := by
        have h1 : ((k + 1 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        have h2 : ((k.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
        rw [Nat.factorial_succ, Nat.cast_mul]
        field_simp
      rw [e, ← smul_mul_assoc, ← smul_mul_assoc]
      exact Submodule.add_mem _ (FrozenVariableLemmas.intPol_mul p (hf (k + 1)) (FrozenVariableLemmas.intPol_X p v))
        (FrozenVariableLemmas.intPol_mul p (hf k) (glAct_X_int L j c d v))

theorem comm_pow (L : Letters N) (j0 : ℕ)
    (Tm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hcomm : ∀ c d x, Tm (glAct p L j0 c d x) = glAct p L j0 c d (Tm x)) (c d : Fin r) (k : ℕ) :
    ∀ x, Tm (((glAct p L j0 c d) ^ k) x) = ((glAct p L j0 c d) ^ k) (Tm x) := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, hcomm, ih]

theorem int_main (L : Letters N) (ρ : Fin r) (e1 j0 : ℕ) (hj0 : j0 ≤ N) (hHP : HypP p L ρ e1) (hHW : HypW p (r := r) L e1)
    (Tm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) (K0 : ℕ)
    (hcomm : ∀ c d x, Tm (glAct p L j0 c d x) = glAct p L j0 c d (Tm x))
    (hhw : ∀ la : Fin r → ℤ, ∀ h ∈ HWC p L j0 univ la ⊓ Pol p r L, h ∈ IntPol p (Fin N × Fin r) →
      ((p : ℚ_[p]) ^ K0) • Tm h ∈ IntPol p (Fin N × Fin r)) :
    ∀ y ∈ PolZ p r L, ((p : ℚ_[p]) ^ (K0 + 2 * e1)) • Tm y ∈ IntPol p (Fin N × Fin r) := by
  classical
  obtain ⟨hP1, -⟩ := hHP
  have hsat : ∀ T : Set (Fin r → ℤ), CsSaturated (univ : Finset (Fin r)) T := fun T la la' h => by
    rw [show la = la' from funext fun c => h c (mem_univ c)]

  have htop : (⨆ la : Fin r → ℤ, IsoC p L j0 univ la) = ⊤ := by
    obtain ⟨P0, ⟨hPP, hran, hker⟩, -, -⟩ := hP1 j0 hj0 univ (Or.inl rfl) Set.univ (hsat _)
    have hk : LinearMap.ker P0 = ⊥ := by
      rw [hker]; simp
    have hid : ∀ x, P0 x = x := by
      intro x
      have : P0 x - x ∈ LinearMap.ker P0 := by
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero]; exact LinearMap.congr_fun hPP x
      rw [hk, Submodule.mem_bot, sub_eq_zero] at this
      exact this
    have hr : LinearMap.range P0 = ⊤ := by
      rw [eq_top_iff]; intro x _; exact ⟨x, hid x⟩
    rw [← hr, hran]; simp
  have hex : ∀ la : Fin r → ℤ, ∃ P, IsTypeProj p L j0 univ {la} P ∧
      ∀ F ∈ PolZ p r L, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r) := fun la => by
    obtain ⟨P, h1, -, h3⟩ := hP1 j0 hj0 univ (Or.inl rfl) {la} (hsat _)
    exact ⟨P, h1, h3⟩
  choose P hPt hPint using hex

  set S : Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    (IntPol p (Fin N × Fin r)).comap ((((p : ℚ_[p]) ^ K0) • Tm).restrictScalars ℤ_[p]) with hS
  have hmemS : ∀ x, x ∈ S ↔ ((p : ℚ_[p]) ^ K0) • Tm x ∈ IntPol p (Fin N × Fin r) := fun x => Iff.rfl
  have hWeyl : ∀ la : Fin r → ℤ, ∀ h, (h ∈ HWC p L j0 univ la ⊓ Pol p r L ∧ h ∈ IntPol p (Fin N × Fin r)) →
      WeylLat p L j0 h ≤ S := by
    intro la h hh
    refine sInf_le ⟨(hmemS h).mpr (hhw la h hh.1 hh.2), ?_⟩
    intro c d hcd k x hx
    rw [hmemS] at hx ⊢
    rw [map_smul, comm_pow L j0 Tm hcomm c d k x, smul_comm, ← map_smul]
    exact divpow_int L j0 c d hcd k _ hx
  intro y hy
  have hyP : y ∈ Pol p r L := (Submodule.mem_inf.mp hy).1
  have hyT : y ∈ ⨆ la : Fin r → ℤ, IsoC p L j0 univ la := by rw [htop]; exact Submodule.mem_top
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hyT
  have hPfix : ∀ la, ∀ x ∈ IsoC p L j0 univ la, P la x = x := by
    intro la x hx
    have : x ∈ LinearMap.range (P la) := by
      rw [(hPt la).2.1]
      exact (le_iSup₂ (f := fun la' (_ : la' ∈ ({la} : Set (Fin r → ℤ))) => IsoC p L j0 univ la') la rfl) hx
    obtain ⟨z, rfl⟩ := this
    exact LinearMap.congr_fun (hPt la).1 z
  have hPkill : ∀ la mu, mu ≠ la → ∀ x ∈ IsoC p L j0 univ mu, P la x = 0 := by
    intro la mu hne x hx
    have : x ∈ LinearMap.ker (P la) := by
      rw [(hPt la).2.2]
      exact (le_iSup₂ (f := fun la' (_ : la' ∉ ({la} : Set (Fin r → ℤ))) => IsoC p L j0 univ la') mu hne) hx
    exact this
  have hPy : ∀ la, P la y = f la := by
    intro la

    rw [← hsum, Finsupp.sum, map_sum]
    rw [Finset.sum_eq_single la]
    · exact hPfix la _ (hf la)
    · intro mu _ hne; exact hPkill la mu hne _ (hf mu)
    · intro hla
      rw [Finsupp.notMem_support_iff.mp hla, map_zero]
  have hterm : ∀ la, ((p : ℚ_[p]) ^ (K0 + 2 * e1)) • Tm (P la y) ∈ IntPol p (Fin N × Fin r) := by
    intro la
    have h1 : ((p : ℚ_[p]) ^ e1) • P la y ∈ IntPol p (Fin N × Fin r) := hPint la y hy
    have h2 : ((p : ℚ_[p]) ^ e1) • P la y ∈ IsoC p L j0 univ la ⊓ Pol p r L :=
      Submodule.smul_mem _ _ (Submodule.mem_inf.mpr ⟨by rw [hPy]; exact hf la,
        typeProj_pol L j0 {la} (P la) (hPt la) y hyP⟩)
    have h3 := hHW j0 hj0 la _ h2 h1
    have h4 : ((p : ℚ_[p]) ^ e1) • ((p : ℚ_[p]) ^ e1) • P la y ∈ S :=
      (iSup₂_le fun h hh => hWeyl la h hh) h3
    rw [hmemS, map_smul, map_smul, smul_smul, smul_smul] at h4
    have e : (p : ℚ_[p]) ^ (K0 + 2 * e1) = (p : ℚ_[p]) ^ K0 * (p : ℚ_[p]) ^ e1 * (p : ℚ_[p]) ^ e1 := by
      rw [pow_add, two_mul, pow_add, mul_assoc]
    rw [e]; exact h4
  have hy2 : y = ∑ la ∈ f.support, P la y := by
    conv_lhs => rw [← hsum, Finsupp.sum]
    exact Finset.sum_congr rfl fun la _ => (hPy la).symm

  rw [hy2, map_sum, Finset.smul_sum]
  exact Submodule.sum_mem _ fun la _ => hterm la

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.GM.TM MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def FfL (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero N] (L : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r)
    (n : ℕ) : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] where
  toFun := T.Ffull p L i ρ n
  map_add' := by
    intro f g
    simp only [TieData.Ffull, freeze, map_add (f := _), mul_add]
  map_smul' := by
    intro c f
    simp only [TieData.Ffull, freeze, map_smul, mul_smul_comm, RingHom.id_apply]

theorem FfL_apply [NeZero N] (L : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) : FfL p L T i ρ n f = T.Ffull p L i ρ n f := rfl

theorem wtsp_iff {M : ℕ} (L : Letters M) (j : ℕ) (la : Fin r → ℤ) (x : MvPolynomial (Fin M × Fin r) ℚ_[p]) :
    x ∈ WtSpC p L j univ la ↔ IsWeightedHomogeneous (wv L j) x la := by
  rw [WtSpC, mem_restrictSupport_iff]
  constructor
  · intro h m hm
    funext c
    rw [weight_wv]
    exact h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c (mem_univ c)
  · intro h m hm c _
    rw [← weight_wv, h (mem_support_iff.mp (Finset.mem_coe.mp hm))]

theorem intPol_rename {σ τ : Type} (e : σ → τ) {y : MvPolynomial σ ℚ_[p]} (hy : y ∈ IntPol p σ) :
    rename e y ∈ IntPol p τ := by
  obtain ⟨P, rfl⟩ := LinearMap.mem_range.mp hy
  refine LinearMap.mem_range.mpr ⟨rename e P, ?_⟩
  simp only [AlgHom.toLinearMap_apply, mapAlgHom_apply, map_rename]

section Comparison₂

variable [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (ρ : Fin r)
  (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ) (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i)

include hadm hS

theorem Ffull_int (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : f ∈ PolZ p r ((LL.setTies T n).takeD (T.pos i + 1))) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨hP, hI⟩ := Submodule.mem_inf.mp hf
  have h1 := (Formalism.GM.extendMapsTo p (T.pos i + 1) r _ ρ (n i) hS f hP).2.2 hI
  rw [Ffull_eq]
  exact intPol_rename _ h1

theorem Ffull_C (w : Fin r → ℤ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ∈ Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr := by
  have hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)) :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1).1
  refine Submodule.mem_inf.mpr ⟨Ffull_pol LL T hadm i ρ n f hP hS, (Submodule.mem_iInf _).mpr fun k => ?_⟩
  by_cases hk : T.J k < T.pos i + 1 + 1
  · rw [Mup, if_pos hk]
    exact Ffull_ycond LL T hadm i ρ n w f hf hS k (by omega)
  · rw [Mup, if_neg hk, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top

theorem Ffull_inj (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)))
    (h0 : T.Ffull p (LL.setTies T n) i ρ (n i) f = 0) : f = 0 := by
  have hK := hK_of_adm LL T hadm i
  rw [Ffull_eq] at h0
  have h1 : freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f = 0 := by
    apply rename_injective _ (inclusion_prodMap_injective (r := r) hK)
    rw [h0, map_zero]
  exact (Formalism.GM.extendBijOn p (T.pos i + 1) r ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) hS).1 f hP 0
    (Submodule.zero_mem _) (by rw [h1, freeze_zero])

omit hS in
theorem deg_compat (a : Fin (T.pos i + 1 + 1)) :
    (LL.setTies T n).deg (ιF N (T.pos i + 1) a) = (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)).deg a := by
  have hK := hK_of_adm LL T hadm i
  induction a using Fin.lastCases with
  | last =>
    rw [Formalism.GM.M.FB.snoc_deg_last]
    have : ιF N (T.pos i + 1) (Fin.last (T.pos i + 1)) = ⟨T.pos i + 1, by omega⟩ := by
      apply Fin.ext; rw [ιF_val hK]; simp
    rw [this]; exact setTies_deg_eta LL T hadm i n _
  | cast a =>
    rw [Formalism.GM.M.FB.snoc_deg_castSucc]
    have : ιF N (T.pos i + 1) (Fin.castSucc a) = ⟨a, by omega⟩ := by
      apply Fin.ext; rw [ιF_val hK]; simp
    rw [this]
    simp [Letters.takeD, (by omega : (a : ℕ) < N)]


omit hS in
theorem ycond_pull (J : ℕ) (M : WithTop ℤ) (F : MvPolynomial (Fin (T.pos i + 1 + 1) × Fin r) ℚ_[p])
    (h : rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) F ∈ YCond p LL J M) :
    F ∈ YCond p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) J M := by
  classical
  have hK := hK_of_adm LL T hadm i
  have hι := inclusion_prodMap_injective (N := N) (r := r) hK
  set S : Submodule ℚ_[p] (MvPolynomial (Fin (T.pos i + 1 + 1) × Fin r) ℚ_[p]) := (YCond p LL J M).comap
    (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2))).toLinearMap with hSd
  have hle : S ≤ YCond p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) J M := by
    refine le_sSup ⟨?_, ?_⟩
    · intro G hG
      rw [mem_restrictSupport_iff]
      intro m hm
      have h1 := Formalism.CountingSumsFrames.ycond_le_supp LL J M (Submodule.mem_comap.mp hG)
      rw [mem_restrictSupport_iff] at h1
      have h2 : Finsupp.mapDomain (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) m ∈
          (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) G).support := by
        rw [support_rename_of_injective hι]; exact Finset.mem_image_of_mem _ hm
      have h3 : ((wt LL J 0 (Finsupp.mapDomain (fun x : Fin (T.pos i + 1 + 1) × Fin r =>
          (ιF N (T.pos i + 1) x.1, x.2)) m) : ℤ) : WithTop ℤ) ≤ M := h1 (Finset.mem_coe.mpr h2)
      rw [← weight_wv, weight_mapDomain, wv_compat LL T hadm i n (n i), weight_wv] at h3
      exact h3
    · intro c d G hG
      rw [hSd, Submodule.mem_comap, AlgHom.toLinearMap_apply,
        glAct_rename (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) LL (ιF N (T.pos i + 1)) (ιF_val hK)
          (fun a => vec_compat LL T hadm i n (n i) a) J c d G]
      exact Formalism.CountingSumsFrames.ycond_glStable LL J M c d _ (Submodule.mem_comap.mp hG)
  exact hle (Submodule.mem_comap.mpr h)

include hρ

theorem hw_is_Ffull (μ : Fin r → ℤ) (v : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hv : v ∈ Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr)
    (hw : (GA p (LL.setTies T n) (T.pos i + 1 + 1)).IsHW μ v) (hint : v ∈ IntPol p (Fin N × Fin r)) :
    ∃ f ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1),
      v = T.Ffull p (LL.setTies T n) i ρ (n i) f := by
  classical
  have hK := hK_of_adm LL T hadm i
  set LLK := (LL.setTies T n).takeD (T.pos i + 1) with hLLK
  let ι : Fin (T.pos i + 1 + 1) × Fin r → Fin N × Fin r := fun x => (ιF N (T.pos i + 1) x.1, x.2)
  have hι : Function.Injective ι := inclusion_prodMap_injective (r := r) hK
  obtain ⟨hvP, hvY⟩ := Submodule.mem_inf.mp hv
  have hvF := isF_of_polLz _ _ hvP
  obtain ⟨F, hF⟩ : ∃ F, rename ι F = v := by
    apply exists_rename_eq_of_vars_subset_range v ι hι
    intro x hx
    rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support] at hx
    obtain ⟨m, hm, hxm⟩ := hx
    have hlt : (x.1 : ℕ) < T.pos i + 1 + 1 := hvF m hm x (Finsupp.mem_support_iff.mp hxm)
    exact ⟨(⟨x.1, hlt⟩, x.2), Prod.ext (Fin.ext (ιF_val hK _)) rfl⟩
  have hsupp : ∀ m ∈ F.support, Finsupp.mapDomain ι m ∈ v.support := by
    intro m hm; rw [← hF, support_rename_of_injective hι]; exact Finset.mem_image_of_mem _ hm
  have hFP : F ∈ Pol p r (LLK.snoc (n i)) := by
    rw [Pol, mem_restrictSupport_iff]
    intro m hm a
    have h1 : MultiDeg (Lz (LL.setTies T n) (T.pos i + 1 + 1)) (Finsupp.mapDomain ι m) :=
      ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hvP) (Finset.mem_coe.mpr (hsupp m hm))
    have h2 := h1 (ιF N (T.pos i + 1) a)
    have h3 : ∀ c, Finsupp.mapDomain ι m (ιF N (T.pos i + 1) a, c) = m (a, c) :=
      fun c => Finsupp.mapDomain_apply_of_injective hι m (a, c)
    simp only [h3] at h2
    rw [h2]
    simp only [Lz]
    rw [if_pos (by rw [ιF_val hK]; exact a.isLt), deg_compat LL T hadm i n]
  have hFI : F ∈ IntPol p (Fin (T.pos i + 1 + 1) × Fin r) := mem_intPol_of_norm _ fun m => by
    have := Formalism.CountingSumsFrames.intPol_norm v hint (Finsupp.mapDomain ι m)
    rwa [← hF, coeff_rename_mapDomain ι hι] at this
  have hgl : ∀ J c d, rename ι (glAct p (LLK.snoc (n i)) J c d F) = glAct p LL J c d v := by
    intro J c d
    rw [← hF]
    exact glAct_rename (LLK.snoc (n i)) LL (ιF N (T.pos i + 1)) (ιF_val hK)
      (fun a => vec_compat LL T hadm i n (n i) a) J c d F
  have hraise : ∀ a b, a < b → glAct p (LLK.snoc (n i)) (T.pos i + 1 + 1) a b F = 0 := by
    intro a b hab
    apply rename_injective ι hι
    rw [hgl, map_zero]
    exact hw.2 a b hab
  have hinv : IsFrozenInv p LLK ρ (n i) F := fun c hc => hraise c ρ (Fin.lt_def.mpr (by
    have := c.isLt
    have : (c : ℕ) ≠ ρ := fun h => hc (Fin.ext h)
    omega))
  obtain ⟨f, hfZ, hfF⟩ := (Formalism.GM.extendBijOn p (T.pos i + 1) r LLK ρ (n i) hS).2 F
    (Submodule.mem_inf.mpr ⟨hFP, hFI⟩) hinv
  have hfP : f ∈ Pol p r LLK := (Submodule.mem_inf.mp hfZ).1
  let J' : Fin T.q → ℕ := fun k => min (T.J k) (T.pos i + 1)
  have hFY : freeze p LLK ρ (n i) f ∈ Y p (LLK.snoc (n i)) J' (T.thrUpTo i) := by
    rw [hfF]
    refine Submodule.mem_inf.mpr ⟨hFP, (Submodule.mem_iInf _).mpr fun k => ?_⟩
    by_cases hk : T.J k ≤ T.pos i + 1
    · have e1 : J' k = T.J k := min_eq_left hk
      have e2 : T.thrUpTo i k = T.thr k := by simp [TieData.thrUpTo, hk]
      rw [e1, e2]
      apply ycond_pull LL T hadm i n
      have h1 := (Submodule.mem_iInf _).mp hvY k
      rw [Mup, if_pos (by omega)] at h1
      rw [← hF] at h1
      exact h1
    · have ht : T.thrUpTo i k = ⊤ := by simp [TieData.thrUpTo, hk]
      rw [ht, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top
  have hfY' := (Formalism.GM.extendWeightBounded p (T.pos i + 1) r LLK ρ (n i) J' (T.thrUpTo i) hS
    (fun k => min_le_right _ _) f hfP).mpr hFY
  have hfY : f ∈ Y p LLK T.J (T.thrUpTo i) := by
    refine Submodule.mem_inf.mpr ⟨hfP, (Submodule.mem_iInf _).mpr fun k => ?_⟩
    have h1 := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hfY').2 k
    by_cases hk : T.J k ≤ T.pos i + 1
    · simpa [J', min_eq_left hk] using h1
    · have ht : T.thrUpTo i k = ⊤ := by simp [TieData.thrUpTo, hk]
      rw [ht, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top

  set w : Fin r → ℤ := μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1 with hwd
  have hvW : IsWeightedHomogeneous (wv LL (T.pos i + 1 + 1)) v μ := by
    have h1 := weightedHomogeneousComponent_isWeightedHomogeneous (R := ℚ_[p]) (w := wv LL (T.pos i + 1 + 1)) μ v
    have h2 : weightedHomogeneousComponent (wv LL (T.pos i + 1 + 1)) μ v = v := hw.1
    rwa [h2] at h1
  have hFw : IsWeightedHomogeneous (wv (LLK.snoc (n i)) (T.pos i + 1 + 1)) F μ := by
    intro m hm
    have h1 := hvW (mem_support_iff.mp (hsupp m (mem_support_iff.mpr hm)))
    rwa [weight_mapDomain, wv_compat LL T hadm i n (n i)] at h1
  have hcP : ∀ w', weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w' f ∈ Pol p r LLK := by
    intro w'
    rw [pol_iff] at hfP ⊢
    exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
      (whc_keep _ _ w' _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hfP))
  have hcW : ∀ w', IsWeightedHomogeneous (wv (LLK.snoc (n i)) (T.pos i + 1 + 1))
      (freeze p LLK ρ (n i) (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w' f))
      (w' - ((n i : ℕ) : ℤ) • Pi.single ρ 1) := fun w' =>
    freeze_wh LLK ρ (n i) hS w' _ (hcP w')
      ((wtsp_iff LLK (T.pos i + 1) w' _).mpr (weightedHomogeneousComponent_isWeightedHomogeneous w' f))
  have hcomp : f = weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w f := by
    obtain ⟨S, hS0⟩ := (GA p LLK (T.pos i + 1)).dec f
    have hS' : ∀ μ' ∉ S, weightedHomogeneousComponent (wv LLK (T.pos i + 1)) μ' f = 0 := hS0
    have hsum : ∑ μ' ∈ S, weightedHomogeneousComponent (wv LLK (T.pos i + 1)) μ' f = f :=
      (GA p LLK (T.pos i + 1)).sum_comp f S hS0
    have hfr : freeze p LLK ρ (n i) f =
        ∑ w' ∈ S, freeze p LLK ρ (n i) (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w' f) := by
      conv_lhs => rw [← hsum]

      simp only [freeze, map_sum, Finset.mul_sum]
    have h5 : F = freeze p LLK ρ (n i) (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w f) := by
      have h6 : weightedHomogeneousComponent (wv (LLK.snoc (n i)) (T.pos i + 1 + 1)) μ F = F := by
        rw [weightedHomogeneousComponent_of_mem hFw, if_pos rfl]

      rw [← h6, ← hfF, hfr, map_sum]
      simp only [weightedHomogeneousComponent_of_mem (hcW _)]
      have hiff : ∀ w', μ = w' - ((n i : ℕ) : ℤ) • Pi.single ρ 1 ↔ w' = w := by
        intro w'; rw [hwd]; constructor
        · intro h; rw [h]; abel
        · intro h; rw [h]; abel
      simp only [hiff]
      rw [Finset.sum_ite_eq' S w]
      split_ifs with hwS
      · rfl
      · rw [hS' w hwS, freeze_zero]
    exact (Formalism.GM.extendBijOn p (T.pos i + 1) r LLK ρ (n i) hS).1 f hfP _ (hcP w) (by rw [hfF, ← h5])
  have hfW : f ∈ WtSpC p LLK (T.pos i + 1) univ w := by
    rw [wtsp_iff, hcomp]
    exact weightedHomogeneousComponent_isWeightedHomogeneous w f
  have hfH : f ∈ HWC p LLK (T.pos i + 1) (univ.erase ρ) w := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [WtSpC, mem_restrictSupport_iff] at hfW ⊢
      intro m hm c _
      exact hfW hm c (mem_univ c)
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
      intro a b hab
      have ha : a ≠ ρ := (Finset.mem_erase.mp hab.1).1
      have hb : b ≠ ρ := (Finset.mem_erase.mp hab.2.1).1
      have h1 := glAct_freeze_gen LLK (n i) ρ a b ha hb f
      rw [hfF, hraise a b hab.2.2] at h1
      exact (Formalism.GM.extendBijOn p (T.pos i + 1) r LLK ρ (n i) hS).1 _
        (Formalism.GM.DimensionMonotonicity.glAct_pol LLK LLK (T.pos i + 1) a b hfP) 0 (Submodule.zero_mem _) (by rw [← h1, freeze_zero])
  refine ⟨f, Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hfY, hfH⟩, hfW⟩,
    (Submodule.mem_inf.mp hfZ).2⟩, ?_⟩
  rw [Ffull_eq, hfF]
  exact hF.symm

omit hρ

theorem Ffull_indep (Ω : Finset (Fin r → ℤ)) (nb : (Fin r → ℤ) → ℕ)
    (f : ∀ w, Fin (nb w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : ∀ w a, f w a ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w)
    (hli : ∀ w, LinearIndependent ℚ_[p] (f w)) :
    LinearIndependent ℚ_[p] (fun x : (Σ w : Ω, Fin (nb w.1)) => T.Ffull p (LL.setTies T n) i ρ (n i) (f x.1.1 x.2)) := by
  classical
  set LLK := (LL.setTies T n).takeD (T.pos i + 1) with hLLK
  have hPf : ∀ w a, f w a ∈ Pol p r LLK := fun w a =>
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp (hf w a)).1).1).1
  rw [Fintype.linearIndependent_iff]
  intro c hc x0
  have h1 : T.Ffull p (LL.setTies T n) i ρ (n i) (∑ x : (Σ w : Ω, Fin (nb w.1)), c x • f x.1.1 x.2) = 0 := by

    rw [← FfL_apply, map_sum, ← hc]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, FfL_apply]
  have hsumP : (∑ x : (Σ w : Ω, Fin (nb w.1)), c x • f x.1.1 x.2) ∈ Pol p r LLK :=
    Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hPf _ _)
  have h2 := Ffull_inj LL T hadm i ρ n hS _ hsumP h1
  have h3 := congrArg (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) x0.1.1) h2

  rw [map_sum, map_zero, Fintype.sum_sigma] at h3
  have h4 : ∀ (w : Ω) (a : Fin (nb w.1)),
      weightedHomogeneousComponent (wv LLK (T.pos i + 1)) x0.1.1 (c ⟨w, a⟩ • f w.1 a) =
        if x0.1 = w then c ⟨w, a⟩ • f w.1 a else 0 := by
    intro w a
    have hW : IsWeightedHomogeneous (wv LLK (T.pos i + 1)) (f w.1 a) w.1 :=
      (wtsp_iff LLK (T.pos i + 1) w.1 _).mp (Submodule.mem_inf.mp (hf w.1 a)).2
    rw [map_smul, weightedHomogeneousComponent_of_mem hW]
    by_cases h : x0.1 = w
    · rw [if_pos h, if_pos (congrArg Subtype.val h)]
    · rw [if_neg h, if_neg (fun h' => h (Subtype.ext h')), smul_zero]
  simp only [h4] at h3
  rw [Finset.sum_eq_single x0.1 (fun w _ hw => by simp [Ne.symm hw]) (fun h => absurd (Finset.mem_univ _) h)] at h3
  simp only [if_true] at h3
  have := Fintype.linearIndependent_iff.mp (hli x0.1.1) (fun a => c ⟨x0.1, a⟩) h3 x0.2
  simpa using this

omit hadm hS

theorem mmw_finite :
    {w : Fin r → ℤ | MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥}.Finite := by
  classical
  refine ((pol_finite (r := r) ((LL.setTies T n).takeD (T.pos i + 1))).image
    (fun m => fun c => wt ((LL.setTies T n).takeD (T.pos i + 1)) (T.pos i + 1) c m)).subset ?_
  intro w hw
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw
  have hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)) :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1).1
  have hW := (Submodule.mem_inf.mp hf).2
  obtain ⟨m, hm⟩ : ∃ m, m ∈ f.support := by
    by_contra hc; push Not at hc
    exact hf0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
  rw [Pol, mem_restrictSupport_iff] at hP
  rw [WtSpC, mem_restrictSupport_iff] at hW
  exact ⟨m, hP (Finset.mem_coe.mpr hm), funext fun c => hW (Finset.mem_coe.mpr hm) c (mem_univ c)⟩

end Comparison₂

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

structure IsEqC [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) : Prop where
  comm : ∀ x ∈ Cset p L j0 J M, ∀ a b, φ (glAct p L j0 a b x) = glAct p L j0 a b (φ x)
  mem : ∀ x ∈ Cset p L j0 J M, φ x ∈ Cset p L j0 J M

noncomputable def inOp (L : Letters N) (j0 : ℕ)
    (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  φ ∘ₗ Pi ∘ₗ psi p L j0

noncomputable def bigOp (L : Letters N) (j0 : ℕ)
    (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  ext (fsj N r j0) (inOp L j0 Pi φ)

section Gen

variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]

theorem slc_ext (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (hφ : ∀ x, IsF fs (φ x)) (m : σ →₀ ℕ)
    (x : MvPolynomial σ K) : slc fs m (ext fs φ x) = φ (slc fs m x) := by
  classical
  induction x using MvPolynomial.induction_on' with
  | monomial m' a =>
    rw [ext_monomial, map_smul, sl_mul fs m (hφ _) (isL_monomial_ltr fs m' 1), sl_monomial, coeff_monomial]
    split_ifs with h
    · rw [one_smul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
    · rw [zero_smul, smul_zero, map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end Gen

theorem slc_int (j0 : ℕ) (m : Fin N × Fin r →₀ ℕ) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ IntPol p (Fin N × Fin r)) : slc (fsj N r j0) m x ∈ IntPol p (Fin N × Fin r) := by
  classical

  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m' _ => ?_
  rw [sl_monomial]
  split_ifs
  · refine TM.mem_intPol_of_norm _ fun k => ?_
    rw [coeff_monomial]
    split_ifs
    · exact intPol_norm x hx m'
    · simp
  · exact Submodule.zero_mem _

theorem int_of_mul_monomial {σ : Type} (g : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ)
    (h : g * monomial m 1 ∈ IntPol p σ) : g ∈ IntPol p σ := by
  refine TM.mem_intPol_of_norm _ fun k => ?_
  have := intPol_norm _ h (k + m)
  rwa [coeff_mul_monomial, mul_one] at this

theorem int_monomial_one {σ : Type} (m : σ →₀ ℕ) : (monomial m 1 : MvPolynomial σ ℚ_[p]) ∈ IntPol p σ := by
  unfold Formalism.GM.M.IntPol
  exact LinearMap.mem_range.mpr ⟨monomial m 1, by simp [MvPolynomial.mapAlgHom_apply, MvPolynomial.map_monomial]⟩

theorem isWt_iff_wh (L : Letters N) (j : ℕ) (ν : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GA p L j).IsWt ν x ↔ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j) ν := by
  constructor
  · intro h
    have h' : weightedHomogeneousComponent (wv L j) ν x = x := h
    rw [← h']
    exact weightedHomogeneousComponent_mem _ _ _
  · intro h
    show weightedHomogeneousComponent (wv L j) ν x = x
    rw [weightedHomogeneousComponent_of_mem h, if_pos rfl]

section

variable [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
  (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi) (hφ : IsEqC L j0 J M φ)

include hPi

theorem piPsi_mem (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : Pi (psi p L j0 x) ∈ Cset p L j0 J M :=
  Submodule.mem_inf.mpr ⟨hPi.pol (Lz L j0) rfl _ (psi_mem L j0 x), (Submodule.mem_iInf _).mpr fun k => hPi.ycond _ k⟩

theorem inOp_C (g : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hg : g ∈ Cset p L j0 J M) : inOp L j0 Pi φ g = φ g := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hg
  simp only [inOp, LinearMap.comp_apply]
  rw [psi_id L j0 h1, hPi.fix (Lz L j0) rfl g h1 (fun k => (Submodule.mem_iInf _).mp h2 k)]

include hφ

theorem inOp_mem (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : inOp L j0 Pi φ x ∈ Cset p L j0 J M := by
  exact hφ.mem _ (piPsi_mem L j0 e J M Pi hPi x)

theorem inOp_isF (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : IsF (fsj N r j0) (inOp L j0 Pi φ x) := by
  exact isF_of_polLz L j0 (Submodule.mem_inf.mp (inOp_mem L j0 e J M Pi φ hPi hφ x)).1

theorem inOp_glAct (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    inOp L j0 Pi φ (glAct p L j0 c d x) = glAct p L j0 c d (inOp L j0 Pi φ x) := by
  simp only [inOp, LinearMap.comp_apply]
  rw [psi_glAct, hPi.comm, hφ.comm _ (piPsi_mem L j0 e J M Pi hPi x)]

theorem eqC_wh (ν : Fin r → ℤ) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hy : y ∈ Cset p L j0 J M)
    (hw : y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν) :
    φ y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν := by
  rw [← isWt_iff_wh] at hw ⊢
  refine GlX.isWt_of_eig (GA p L j0) fun c => ?_
  have h1 : glAct p L j0 c c y = ((ν c : ℤ) : ℚ_[p]) • y := (GA p L j0).E_diag_of_isWt hw c
  show glAct p L j0 c c (φ y) = _
  rw [← hφ.comm y hy, h1, map_smul]

theorem inOp_wh (ν : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν) :
    inOp L j0 Pi φ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν := by
  simp only [inOp, LinearMap.comp_apply]
  exact eqC_wh L j0 e J M Pi φ hPi hφ ν _ (piPsi_mem L j0 e J M Pi hPi x) (hPi.wh ν _ (whc_keep _ _ _ _ hx))

theorem bigOp_glAct (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    bigOp L j0 Pi φ (glAct p L j0 c d x) = glAct p L j0 c d (bigOp L j0 Pi φ x) := by
  exact ext_glAct L le_rfl _ (inOp_glAct L j0 e J M Pi φ hPi hφ) (inOp_isF L j0 e J M Pi φ hPi hφ) c d x

theorem bigOp_Y : ∀ y ∈ Y p L J M, bigOp L j0 Pi φ y ∈ Y p L J M := by
  exact ext_Y L j0 J M _ (inOp_glAct L j0 e J M Pi φ hPi hφ) (inOp_wh L j0 e J M Pi φ hPi hφ)
    (fun x => (Submodule.mem_inf.mp (inOp_mem L j0 e J M Pi φ hPi hφ x)).1)
    (fun x _ => inOp_mem L j0 e J M Pi φ hPi hφ x)

theorem bigOp_slc (m : Fin N × Fin r →₀ ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    slc (fsj N r j0) m (bigOp L j0 Pi φ x) = inOp L j0 Pi φ (slc (fsj N r j0) m x) := by
  exact slc_ext _ _ (inOp_isF L j0 e J M Pi φ hPi hφ) m x

theorem bigOp_span (VF : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hVF : ∀ g ∈ Cset p L j0 J M, φ g ∈ VF) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    bigOp L j0 Pi φ x ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ VF,
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q} := by
  classical
  rw [bigOp, ext_eq_sum (fsj N r j0) _ x (x.support.image (ltr (fsj N r j0)))
    (fun m hm => Finset.mem_image_of_mem _ hm)]
  refine Submodule.sum_mem _ fun m hm => Submodule.subset_span ?_
  obtain ⟨m', _, rfl⟩ := Finset.mem_image.mp hm
  refine ⟨_, hVF _ (piPsi_mem L j0 e J M Pi hPi (slc (fsj N r j0) (ltr (fsj N r j0) m') x)), _, ?_, rfl⟩
  rw [mem_supported, vars_monomial one_ne_zero]
  intro v hv
  have := ltr_isL (fsj N r j0) m' v (Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hv))
  simp only [fsj, not_lt] at this
  exact this

theorem bigOp_int
    (hint : ∀ μ v, v ∈ Cset p L j0 J M → (GA p L j0).IsHW μ v → v ∈ IntPol p (Fin N × Fin r) →
      φ v ∈ IntPol p (Fin N × Fin r))
    (la : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ HWC p L j0 univ la ⊓ Pol p r L)
    (hxi : x ∈ IntPol p (Fin N × Fin r)) :
    ((p : ℚ_[p]) ^ e) • bigOp L j0 Pi φ x ∈ IntPol p (Fin N × Fin r) := by
  classical
  obtain ⟨hxH, hxP⟩ := Submodule.mem_inf.mp hx
  obtain ⟨hxW, hxE⟩ := (isHW_iff L j0 la x).mpr hxH
  rw [bigOp, ext_eq_sum (fsj N r j0) _ x (x.support.image (ltr (fsj N r j0)))
    (fun m hm => Finset.mem_image_of_mem _ hm), Finset.smul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hm
  set s := slc (fsj N r j0) (ltr (fsj N r j0) m') x with hs
  have hsP : s ∈ Pol p r (Lz L j0) := slc_pol L j0 _ hxP
  have hsI : s ∈ IntPol p (Fin N × Fin r) := slc_int j0 _ hxi
  have hmd : MultiDeg L m' := ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hxP) hm'
  have hsm : s * monomial (ltr (fsj N r j0) m') 1 ∈ PolZ p r L :=
    Submodule.mem_inf.mpr ⟨mul_ltr_pol L j0 hsP hmd, FrozenVariableLemmas.intPol_mul p hsI (int_monomial_one _)⟩
  have h1 := hPi.int _ hsm
  rw [hPi.mul _ _ (isL_monomial_ltr (fsj N r j0) m' 1), ← smul_mul_assoc] at h1
  have hvI : ((p : ℚ_[p]) ^ e) • Pi s ∈ IntPol p (Fin N × Fin r) := int_of_mul_monomial _ _ h1
  have hPs : Pi s ∈ Cset p L j0 J M := by
    have := piPsi_mem L j0 e J M Pi hPi s
    rwa [psi_id L j0 hsP] at this
  have hvC : ((p : ℚ_[p]) ^ e) • Pi s ∈ Cset p L j0 J M := Submodule.smul_mem _ _ hPs
  have hsW : s ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) la :=
    slc_wh L le_rfl _ ((isWt_iff_wh L j0 la x).mp hxW)
  have hvH : (GA p L j0).IsHW la (((p : ℚ_[p]) ^ e) • Pi s) := by
    refine ⟨(isWt_iff_wh L j0 la _).mpr (Submodule.smul_mem _ _ (hPi.wh la _ hsW)), fun a b hab => ?_⟩
    show glAct p L j0 a b _ = 0
    have h0 : glAct p L j0 a b x = 0 := hxE a b hab
    rw [map_smul, ← hPi.comm, hs, ← slc_glAct L le_rfl a b, h0, map_zero, map_zero, smul_zero]
  have h2 := hint la _ hvC hvH hvI
  rw [map_smul] at h2
  have e3 : inOp L j0 Pi φ s = φ (Pi s) := by
    simp only [inOp, LinearMap.comp_apply]; rw [psi_id L j0 hsP]
  rw [e3, ← smul_mul_assoc]
  exact FrozenVariableLemmas.intPol_mul p h2 (int_monomial_one _)

end

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def YYs [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (v : MvPolynomial (Fin N × Fin r) ℚ_[p]) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  Y p L J M ⊓ Submodule.span ℚ_[p] {x | ∃ g ∈ (GA p L j0).gS {v},
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q}

theorem eq_of_slc {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
    (x y : MvPolynomial σ K) (hxy : ∀ m, slc fs m x = slc fs m y) : x = y := by
  classical
  have hx := eq_sum_sl fs x ((x.support ∪ y.support).image (ltr fs))
    (fun m hm => Finset.mem_image_of_mem _ (Finset.mem_union_left _ hm))
  have hy := eq_sum_sl fs y ((x.support ∪ y.support).image (ltr fs))
    (fun m hm => Finset.mem_image_of_mem _ (Finset.mem_union_right _ hm))
  exact hx.trans ((Finset.sum_congr rfl fun m _ => by rw [hxy m]).trans hy.symm)

theorem finrank_biSup_le {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] (Yv : Submodule K V)
    [FiniteDimensional K Yv] (A : ι → Submodule K V) (hA : ∀ i, A i ≤ Yv) (s : Finset ι) :
    Module.finrank K (⨆ i ∈ s, A i : Submodule K V) ≤ ∑ i ∈ s, Module.finrank K (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (⨆ i ∈ (∅ : Finset ι), A i : Submodule K V) = ⊥ := by simp
    rw [this]; simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.sum_insert ha]
    have : FiniteDimensional K (A a) := Submodule.finiteDimensional_of_le (hA a)
    have : FiniteDimensional K (⨆ i ∈ s, A i : Submodule K V) :=
      Submodule.finiteDimensional_of_le (iSup₂_le fun i _ => hA i)
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

theorem isHW_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r) (μ : Fin r → ℤ) :
    G.IsHW μ 0 := by
  unfold Formalism.GM.DimensionMonotonicity.GlW.IsHW Formalism.GM.DimensionMonotonicity.GlW.IsWt
  exact ⟨map_zero _, fun a b _ => map_zero _⟩

theorem C_finW [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    (GA p (r := r) L j0).FinW (Cset p L j0 J M) := by
  obtain ⟨S, hS⟩ := polynomial_finite_weights (p := p) (r := r) L j0
  exact ⟨S, fun x hx => hS x (Submodule.mem_inf.mp hx).1⟩

theorem Y_fd [NeZero r] (L : Letters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    FiniteDimensional ℚ_[p] (Y p (r := r) L J M) := by
  have := pol_fd (p := p) (r := r) L
  exact Submodule.finiteDimensional_of_le (inf_le_left : Y p (r := r) L J M ≤ Pol p r L)

theorem slc_span (L : Letters N) (j0 : ℕ) (VF : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hVF : VF ≤ Pol p r (Lz L j0)) {z : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hz : z ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ VF,
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q})
    (m : Fin N × Fin r →₀ ℕ) : slc (fsj N r j0) m z ∈ VF := by
  classical
  obtain ⟨s, a, hs, ha, rfl⟩ := rep_span VF j0 hz

  rw [map_sum]
  refine Submodule.sum_mem _ fun b hb => ?_
  have hL : IsL (fsj N r j0) (monomial b (1 : ℚ_[p])) := by
    intro m' hm' v hv hfs
    have : m' = b := Finset.mem_singleton.mp (support_monomial_subset hm')
    subst this
    exact hv (hs m' hb v hfs)
  rw [sl_mul (fsj N r j0) m (isF_of_polLz L j0 (hVF (ha b))) hL]
  exact VF.smul_mem _ (ha b)

section

variable [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
  (Pi : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi)
  {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
  (hh : ∀ i, (GA p L j0).IsHW (la i) (h i)) (hhC : ∀ i, h i ∈ Cset p L j0 J M)
  (hli : LinearIndependent ℚ_[p] h) (hsp : Cset p (r := r) L j0 J M ≤ ⨆ i, (GA p L j0).gS {h i})

include hPi hh hhC hli hsp

theorem count_le (bad : ι → Prop) [DecidablePred bad]
    (ϖ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hϖ : IsEqC L j0 J M ϖ) (hgood : ∀ i, ¬ bad i → ∀ x ∈ (GA p L j0).gS {h i}, ϖ x = x)
    (hbad : ∀ i, bad i → ∀ x ∈ (GA p L j0).gS {h i}, ϖ x = 0) :
    Module.finrank ℚ_[p] (Y p (r := r) L J M) -
      Module.finrank ℚ_[p] ((Y p L J M ⊓ LinearMap.ker (bigOp L j0 Pi ϖ - LinearMap.id) :
        Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))) ≤
      ∑ i ∈ univ.filter bad, Module.finrank ℚ_[p] (YYs L j0 J M (h i)) := by
  classical
  have hex : ∀ i : ι, ∃ φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
      IsEqC L j0 J M φ ∧ (∀ x ∈ (GA p (r := r) L j0).gS {h i}, φ x = x) ∧
        (∀ k, k ≠ i → ∀ x ∈ (GA p (r := r) L j0).gS {h k}, φ x = 0) := by
    intro i
    obtain ⟨φ, -, hφE, hφC, -, -, hφ1, hφ0⟩ := GlX.eqExt (GA p (r := r) L j0) (C_stable L j0 J M)
      (C_finW L j0 J M) h (fun k => if k = i then h k else 0) la hh hhC hli hsp
      (fun k => by
        by_cases hk : k = i
        · simpa [hk] using hh i
        · simpa [hk] using isHW_zero (GA p (r := r) L j0) (la k))
      (fun k => by
        by_cases hk : k = i
        · simpa [hk] using hhC i
        · simp [hk])
    exact ⟨φ, ⟨hφE, hφC⟩, hφ1 i (by simp), fun k hk => hφ0 k (by simp [hk])⟩
  choose π hπEq hπ1 hπ0 using hex

  have hπVF : ∀ i, ∀ g ∈ Cset p L j0 J M, π i g ∈ (GA p (r := r) L j0).gS {h i} := by
    intro i g hg
    refine Submodule.iSup_induction _ (motive := fun x => π i x ∈ (GA p (r := r) L j0).gS {h i}) (hsp hg) ?_
      (by simp) (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)
    intro k x hx
    by_cases hk : k = i
    · subst hk; rw [hπ1 k x hx]; exact hx
    · rw [hπ0 i k hk x hx]; exact zero_mem _

  have hdec : ∀ g ∈ Cset p L j0 J M, g - ϖ g = ∑ i ∈ univ.filter bad, π i g := by
    intro g hg
    refine Submodule.iSup_induction _ (motive := fun x => x - ϖ x = ∑ i ∈ univ.filter bad, π i x) (hsp hg) ?_
      (by simp) (fun x y hx hy => by
        simp only [map_add (f := _), Finset.sum_add_distrib, ← hx, ← hy]; abel)
    intro k x hx
    by_cases hk : bad k
    · rw [hbad k hk x hx, sub_zero, Finset.sum_eq_single k (fun i _ hik => hπ0 i k (Ne.symm hik) x hx)
        (fun hk' => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩) hk'), hπ1 k x hx]
    · rw [hgood k hk x hx, sub_self]
      refine (Finset.sum_eq_zero fun i hi => hπ0 i k ?_ x hx).symm
      rintro rfl
      exact hk (Finset.mem_filter.mp hi).2

  have hdecY : ∀ y ∈ Y p L J M, y - bigOp L j0 Pi ϖ y = ∑ i ∈ univ.filter bad, bigOp L j0 Pi (π i) y := by
    intro y hy
    apply eq_of_slc (fsj N r j0)
    intro m
    have hc := slc_C L j0 J M hy m

    rw [map_sub, map_sum, bigOp_slc L j0 e J M Pi ϖ hPi hϖ m y, inOp_C L j0 e J M Pi ϖ hPi _ hc, hdec _ hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bigOp_slc L j0 e J M Pi (π i) hPi (hπEq i) m y, inOp_C L j0 e J M Pi (π i) hPi _ hc]
  have hfd := Y_fd (p := p) (r := r) L J M
  set Z : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := ⨆ i ∈ univ.filter bad, YYs L j0 J M (h i) with hZ
  have hZY : Z ≤ Y p L J M := iSup₂_le fun i _ => inf_le_left
  have hZfd : FiniteDimensional ℚ_[p] Z := Submodule.finiteDimensional_of_le hZY
  set f : Y p (r := r) L J M →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
    (bigOp L j0 Pi ϖ - LinearMap.id) ∘ₗ (Y p (r := r) L J M).subtype with hf
  have hran : LinearMap.range f ≤ Z := by
    rintro _ ⟨y, rfl⟩
    have h1 : f y = -(∑ i ∈ univ.filter bad, bigOp L j0 Pi (π i) y.1) := by
      rw [← hdecY y.1 y.2]; simp [hf]
    rw [h1]
    refine Z.neg_mem (Submodule.sum_mem _ fun i hi => ?_)
    refine (le_iSup₂ (f := fun i (_ : i ∈ univ.filter bad) => YYs L j0 J M (h i)) i hi) ?_
    exact Submodule.mem_inf.mpr ⟨bigOp_Y L j0 e J M Pi (π i) hPi (hπEq i) y.1 y.2,
      bigOp_span L j0 e J M Pi (π i) hPi (hπEq i) _ (hπVF i) y.1⟩
  have hker : Module.finrank ℚ_[p] (LinearMap.ker f) =
      Module.finrank ℚ_[p] ((Y p L J M ⊓ LinearMap.ker (bigOp L j0 Pi ϖ - LinearMap.id) :
        Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))) := by
    rw [hf, LinearMap.ker_comp, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have h1 : Module.finrank ℚ_[p] (LinearMap.range f) ≤ Module.finrank ℚ_[p] Z := Submodule.finrank_mono hran
  have h2 : Module.finrank ℚ_[p] Z ≤ ∑ i ∈ univ.filter bad, Module.finrank ℚ_[p] (YYs L j0 J M (h i)) :=
    finrank_biSup_le (Y p (r := r) L J M) (fun i => YYs L j0 J M (h i)) (fun i => inf_le_left) (univ.filter bad)
  rw [← hker]
  omega

theorem transport_le (i0 : ι) (v : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hv : (GA p L j0).IsHW (la i0) v)
    (hvC : v ∈ Cset p L j0 J M) (hv0 : v ≠ 0) :
    Module.finrank ℚ_[p] (YYs L j0 J M (h i0)) ≤ Module.finrank ℚ_[p] (YYs L j0 J M v) := by
  classical
  obtain ⟨φ, -, hφE, hφC, hφg, hφinj, -, hφ0⟩ := GlX.eqExt (GA p (r := r) L j0) (C_stable L j0 J M)
    (C_finW L j0 J M) h (fun k => if k = i0 then v else 0) la hh hhC hli hsp
    (fun k => by
      by_cases hk : k = i0
      · subst hk; simpa using hv
      · simpa [hk] using isHW_zero (GA p (r := r) L j0) (la k))
    (fun k => by
      by_cases hk : k = i0
      · simpa [hk] using hvC
      · simp [hk])
  have hEq : IsEqC L j0 J M φ := ⟨hφE, hφC⟩
  have hVF : ∀ g ∈ Cset p L j0 J M, φ g ∈ (GA p (r := r) L j0).gS {v} := by
    intro g hg
    refine Submodule.iSup_induction _ (motive := fun x => φ x ∈ (GA p (r := r) L j0).gS {v}) (hsp hg) ?_
      (by simp) (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)
    intro k x hx
    by_cases hk : k = i0
    · subst hk
      have := hφg k x hx
      simpa using this
    · rw [hφ0 k (by simp [hk]) x hx]; exact zero_mem _
  have hgSC : (GA p (r := r) L j0).gS {h i0} ≤ Cset p L j0 J M :=
    (GA p (r := r) L j0).gS_le (by simpa using hhC i0) (C_stable L j0 J M)
  have hmap : ∀ z ∈ YYs L j0 J M (h i0), bigOp L j0 Pi φ z ∈ YYs L j0 J M v := fun z hz =>
    Submodule.mem_inf.mpr ⟨bigOp_Y L j0 e J M Pi φ hPi hEq z (Submodule.mem_inf.mp hz).1,
      bigOp_span L j0 e J M Pi φ hPi hEq _ hVF z⟩
  have hinj : ∀ z ∈ YYs L j0 J M (h i0), bigOp L j0 Pi φ z = 0 → z = 0 := by
    intro z hz h0
    apply eq_of_slc (fsj N r j0)
    intro m
    have h1 : slc (fsj N r j0) m z ∈ (GA p (r := r) L j0).gS {h i0} :=
      slc_span L j0 _ (hgSC.trans inf_le_left) (Submodule.mem_inf.mp hz).2 m
    have h2 := bigOp_slc L j0 e J M Pi φ hPi hEq m z
    rw [h0, map_zero, inOp_C L j0 e J M Pi φ hPi _ (hgSC h1)] at h2
    rw [map_zero]
    exact hφinj i0 (by simpa using hv0) _ h1 h2.symm
  have hfd := Y_fd (p := p) (r := r) L J M
  have : FiniteDimensional ℚ_[p] (YYs L j0 J M v) :=
    Submodule.finiteDimensional_of_le (inf_le_left : YYs L j0 J M v ≤ Y p L J M)
  refine LinearMap.finrank_le_finrank_of_injective (f := (bigOp L j0 Pi φ).restrict hmap) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  apply Subtype.ext
  apply hinj z.1 z.2
  exact congrArg Subtype.val hz

end

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime]

theorem int_smul_mem {σ : Type} (S : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (c : ℚ_[p]) (hc : ‖c‖ ≤ 1)
    (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ S) : c • x ∈ S := by
  have h := S.smul_mem (⟨c, hc⟩ : ℤ_[p]) hx
  first
    | exact h

theorem smith_bases {σ : Type} (nb : ℕ) (f : Fin nb → MvPolynomial σ ℚ_[p])
    (Lat : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (hli : LinearIndependent ℤ_[p] f) (hsp : Submodule.span ℤ_[p] (Set.range f) = Lat)
    (B : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p])
    (U V : Matrix (Fin nb) (Fin nb) ℚ_[p]) (dg : Fin nb → ℚ_[p])
    (hU : ∀ x y, ‖U x y‖ ≤ 1) (hV : ∀ x y, ‖V x y‖ ≤ 1) (hUd : ‖U.det‖ = 1) (hVd : ‖V.det‖ = 1)
    (hfac : (Matrix.of fun x y => B (f x) (f y)) = U * Matrix.diagonal dg * V) :
    ∃ f' f'' : Fin nb → MvPolynomial σ ℚ_[p], (∀ a, f' a ∈ Lat) ∧ (∀ a, f'' a ∈ Lat) ∧
      LinearIndependent ℚ_[p] f' ∧ Lat ≤ Submodule.span ℤ_[p] (Set.range f') ∧
      ∀ a b, B (f' a) (f'' b) = if a = b then dg a else 0 := by
  classical
  have hUu : IsUnit U.det := by
    rw [isUnit_iff_ne_zero]; intro h; rw [h, norm_zero] at hUd; exact zero_ne_one hUd
  have hVu : IsUnit V.det := by
    rw [isUnit_iff_ne_zero]; intro h; rw [h, norm_zero] at hVd; exact zero_ne_one hVd
  have hUi := fun x y => DetBound.norm_inv_entry_le U hU hUd x y
  have hVi := fun x y => DetBound.norm_inv_entry_le V hV hVd x y
  have hliQ : LinearIndependent ℚ_[p] f := (LinearIndependent.iff_fractionRing ℤ_[p] ℚ_[p]).mp hli
  have hfL : ∀ x, f x ∈ Lat := fun x => hsp ▸ Submodule.subset_span ⟨x, rfl⟩
  have hback : ∀ x, f x = ∑ a, U x a • ∑ y, U⁻¹ a y • f y := by
    intro x
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have : ∀ y, ∑ a, U x a * U⁻¹ a y = (1 : Matrix (Fin nb) (Fin nb) ℚ_[p]) x y := by
      intro y
      rw [← Matrix.mul_nonsing_inv U hUu, Matrix.mul_apply]
    simp only [this, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨fun a => ∑ x, U⁻¹ a x • f x, fun b => ∑ y, V⁻¹ y b • f y, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun a => Lat.sum_mem fun x _ => int_smul_mem Lat _ (hUi a x) _ (hfL x)
  · exact fun b => Lat.sum_mem fun y _ => int_smul_mem Lat _ (hVi y b) _ (hfL y)
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Finset.smul_sum, smul_smul] at hg
    rw [Finset.sum_comm] at hg
    simp only [← Finset.sum_smul] at hg
    have h0 := Fintype.linearIndependent_iff.mp hliQ _ hg
    have h1 : Matrix.vecMul g U⁻¹ = 0 := by
      funext x
      simpa [Matrix.vecMul, dotProduct] using h0 x
    have h2 : Matrix.vecMul (Matrix.vecMul g U⁻¹) U = g := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul U hUu, Matrix.vecMul_one]
    intro a
    rw [← h2, h1, Matrix.zero_vecMul]; rfl
  · rw [← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hback x]
    exact Submodule.sum_mem _ fun a _ => int_smul_mem _ _ (hU x a) _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro a b
    have e : B (∑ x, U⁻¹ a x • f x) (∑ y, V⁻¹ y b • f y) =
        (U⁻¹ * (Matrix.of fun x y => B (f x) (f y)) * V⁻¹) a b := by

      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [e, hfac]
    have : U⁻¹ * (U * Matrix.diagonal dg * V) * V⁻¹ = Matrix.diagonal dg := by
      rw [Matrix.mul_assoc U, ← Matrix.mul_assoc U⁻¹, Matrix.nonsing_inv_mul U hUu, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv V hVu, Matrix.mul_one]
    rw [this, Matrix.diagonal_apply]

theorem good_norm (E : ℝ) (hE : 0 ≤ E) (d : ℚ_[p]) (hd : ¬ ‖d‖ < (p : ℝ) ^ (-E)) :
    ‖(p : ℚ_[p]) ^ ⌊E⌋₊ / d‖ ≤ 1 ∧ d ≠ 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hd0 : d ≠ 0 := by
    intro h
    apply hd
    rw [h, norm_zero]
    exact Real.rpow_pos_of_pos hp0 _
  refine ⟨?_, hd0⟩
  rw [not_lt, Padic.norm_eq_zpow_neg_valuation hd0, ← Real.rpow_intCast, Real.rpow_le_rpow_left_iff hp1] at hd
  have hk : ((d.valuation : ℤ) : ℝ) ≤ E := by push_cast at hd; linarith
  have hk' : d.valuation ≤ (⌊E⌋₊ : ℤ) := by
    by_cases h0 : d.valuation ≤ 0
    · exact h0.trans (Int.natCast_nonneg _)
    · push Not at h0
      have h1 : ((d.valuation.toNat : ℕ) : ℝ) ≤ E := by
        have : ((d.valuation.toNat : ℕ) : ℤ) = d.valuation := Int.toNat_of_nonneg h0.le
        calc ((d.valuation.toNat : ℕ) : ℝ) = (((d.valuation.toNat : ℕ) : ℤ) : ℝ) := by push_cast; rfl
          _ = ((d.valuation : ℤ) : ℝ) := by rw [this]
          _ ≤ E := hk
      have h2 := Nat.le_floor h1
      omega
  rw [norm_div, norm_pow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hd0, div_le_one (zpow_pos hp0 _),
    inv_pow, ← zpow_natCast, ← zpow_neg]
  exact zpow_le_zpow_right₀ hp1.le (by omega)

alias S_eq_total := _root_.Formalism.GM.TM.takeD_total_eq

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem smul_int {σ : Type} {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) {x : MvPolynomial σ ℚ_[p]} (hx : x ∈ IntPol p σ) :
    c • x ∈ IntPol p σ := int_smul_mem (IntPol p σ) c hc x hx

theorem Cset_thrUpTo [NeZero r] (L : Letters N) (T : TieData) (i : Fin T.t) :
    Cset p (r := r) L (T.pos i + 1 + 1) T.J (T.thrUpTo i) = Cset p L (T.pos i + 1 + 1) T.J T.thr := by
  unfold Cset
  congr 1
  refine iInf_congr fun k => ?_
  unfold Mup TieData.thrUpTo
  by_cases h : T.J k < T.pos i + 1 + 1
  · rw [if_pos h, if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg h]

theorem YYsp_eq [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r) (n : Fin T.t → ℕ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    T.YYsp p LL i ρ n f =
      YYs (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr (T.Ffull p (LL.setTies T n) i ρ (n i) f) := by
  unfold TieData.YYsp YYs
  rw [gSpan_eq]
  rfl

theorem isHW_smul (L : Letters N) (j : ℕ) (la : Fin r → ℤ) (c : ℚ_[p]) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : (GA p L j).IsHW la x) : (GA p L j).IsHW la (c • x) := by
  rw [isHW_iff] at hx ⊢
  exact Submodule.smul_mem _ _ hx

theorem isHW_zero' (L : Letters N) (j : ℕ) (la : Fin r → ℤ) :
    (GA p L j).IsHW la (0 : MvPolynomial (Fin N × Fin r) ℚ_[p]) := by
  rw [isHW_iff]
  exact Submodule.zero_mem _

theorem tie_core [NeZero r] (L : Letters N) (T : TieData) (hadm : T.Admissible L) (i : Fin T.t) (ρ : Fin r) (e1 : ℕ)
    (hK : T.pos i + 1 + 1 ≤ N) (hHP : HypP p L ρ e1) (hHW : HypW p (r := r) L e1) (E : ℝ) (hE : 0 ≤ E)
    {ι : Type} [Fintype ι] [DecidableEq ι] (h' h'' : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
    (hh : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (h' x))
    (hhC : ∀ x, h' x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr)
    (hli : LinearIndependent ℚ_[p] h')
    (hspZ : ∀ μ v, v ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr → (GA p L (T.pos i + 1 + 1)).IsHW μ v →
      v ∈ IntPol p (Fin N × Fin r) → v ∈ Submodule.span ℤ_[p] (Set.range h'))
    (hh2 : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (h'' x))
    (hh2C : ∀ x, h'' x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr)
    (hh2i : ∀ x, h'' x ∈ IntPol p (Fin N × Fin r))
    (d : ι → ℚ_[p]) (cst : ℚ_[p])
    (hdiag : ∀ x y, la x = la y → cst * fock p (T.phi p L i (h' x)) (h'' y) = if x = y then d x else 0)
    (hG0 : ∀ x y, ‖cst * fock p (h' x) (h' y)‖ ≤ 1)
    (vv : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (hvv : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (vv x))
    (hvvC : ∀ x, vv x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr) (hvv0 : ∀ x, vv x ≠ 0) :
    ∃ Tm πm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ y ∈ Y p (r := r) L T.J T.thr, Tm y ∈ Y p (r := r) L T.J T.thr) ∧
      (∀ y ∈ YZ p (r := r) L T.J T.thr,
        ((p : ℚ_[p]) ^ (e1 * (T.pos i + 1 + 1) + 2 * e1)) • Tm y ∈ IntPol p (Fin N × Fin r)) ∧
      (∀ u ∈ Y p (r := r) L T.J (T.thrUpTo i), ∀ u' ∈ Y p (r := r) L T.J T.thr,
        fockN p L (T.phi p L i u) (Tm u') = (p : ℚ_[p]) ^ ⌊E⌋₊ * fockN p L (πm u) u') ∧
      (∀ j : Fin T.t, i < j → ∀ u, πm (T.phi p L j u) = T.phi p L j (πm u)) ∧
      Module.finrank ℚ_[p] (Y p (r := r) L T.J T.thr) -
        Module.finrank ℚ_[p] ((Y p (r := r) L T.J T.thr ⊓ LinearMap.ker (πm - LinearMap.id) :
          Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))) ≤
        ∑ x ∈ univ.filter (fun x => ‖d x‖ < (p : ℝ) ^ (-E)),
          Module.finrank ℚ_[p] (YYs L (T.pos i + 1 + 1) T.J T.thr (vv x)) := by
  classical
  obtain ⟨Pi, hPi⟩ := projC L ρ e1 (T.pos i + 1 + 1) hK hHP T.J T.thr
  have hCst := C_stable (p := p) (r := r) L (T.pos i + 1 + 1) T.J T.thr
  have hCf : (GA p L (T.pos i + 1 + 1)).FinW (Cset p (r := r) L (T.pos i + 1 + 1) T.J T.thr) := by
    obtain ⟨S, hS⟩ := polynomial_finite_weights (p := p) (r := r) L (T.pos i + 1 + 1)
    exact ⟨S, fun x hx => hS x (Submodule.mem_inf.mp hx).1⟩
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hspQ : ∀ μ v, v ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr → (GA p L (T.pos i + 1 + 1)).IsHW μ v →
      v ∈ Submodule.span ℚ_[p] (Set.range h') := by
    intro μ v hv hw
    obtain ⟨k, hk⟩ := _root_.Formalism.GM.TM.exists_pow_smul_intPol v
    have h1 := hspZ μ (((p : ℚ_[p]) ^ k) • v) (Submodule.smul_mem _ _ hv) (isHW_smul L _ μ _ hw) hk
    have h2 : ((p : ℚ_[p]) ^ k) • v ∈ Submodule.span ℚ_[p] (Set.range h') :=
      Submodule.span_le_restrictScalars ℤ_[p] ℚ_[p] _ h1
    exact (Submodule.smul_mem_iff _ (pow_ne_zero _ hp0)).mp h2
  have hsp : Cset p (r := r) L (T.pos i + 1 + 1) T.J T.thr ≤ ⨆ x, (GA p L (T.pos i + 1 + 1)).gS {h' x} := by
    obtain ⟨S, hS⟩ := hCf
    exact GlX.span_hw (GA p L (T.pos i + 1 + 1)) hCst hS h' la hh hhC (fun x => hli.ne_zero x) hspQ
  set c : ℚ_[p] := (p : ℚ_[p]) ^ ⌊E⌋₊ with hc
  let gϖ : ι → MvPolynomial (Fin N × Fin r) ℚ_[p] := fun x => if ‖d x‖ < (p : ℝ) ^ (-E) then 0 else h' x
  let tc : ι → ι → ℚ_[p] := fun z y =>
    if la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E) then (c / d z) * (cst * fock p (h' z) (h' y)) else 0
  let gτ : ι → MvPolynomial (Fin N × Fin r) ℚ_[p] := fun y => ∑ z, tc z y • h'' z
  have hgϖ : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (gϖ x) := by
    intro x
    by_cases hx : ‖d x‖ < (p : ℝ) ^ (-E)
    · simp only [gϖ, if_pos hx]; exact isHW_zero' L _ _
    · simp only [gϖ, if_neg hx]; exact hh x
  have hgϖC : ∀ x, gϖ x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr := by
    intro x
    by_cases hx : ‖d x‖ < (p : ℝ) ^ (-E)
    · simp only [gϖ, if_pos hx]; exact Submodule.zero_mem _
    · simp only [gϖ, if_neg hx]; exact hhC x
  have hgτ : ∀ y, (GA p L (T.pos i + 1 + 1)).IsHW (la y) (gτ y) := by
    intro y
    rw [isHW_iff]
    refine Submodule.sum_mem _ fun z _ => ?_
    by_cases hz : la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E)
    · refine Submodule.smul_mem _ _ ?_
      rw [← isHW_iff, ← hz.1]; exact hh2 z
    · simp only [tc, if_neg hz, zero_smul]; exact Submodule.zero_mem _
  have hgτC : ∀ y, gτ y ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr :=
    fun y => Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _ (hh2C z)
  have htc : ∀ z y, ‖tc z y‖ ≤ 1 := by
    intro z y
    by_cases hz : la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E)
    · simp only [tc, if_pos hz, norm_mul]
      exact mul_le_one₀ (good_norm E hE (d z) hz.2).1 (by positivity) (by rw [← norm_mul]; exact hG0 z y)
    · simp only [tc, if_neg hz, norm_zero]; exact zero_le_one
  have hgτi : ∀ y, gτ y ∈ IntPol p (Fin N × Fin r) :=
    fun y => Submodule.sum_mem _ fun z _ => smul_int (htc z y) (hh2i z)
  obtain ⟨ϖ, hϖ1, hϖ2, hϖ3, -, -, hϖ6, hϖ7⟩ :=
    GlX.eqExt (GA p L (T.pos i + 1 + 1)) hCst hCf h' gϖ la hh hhC hli hsp hgϖ hgϖC
  obtain ⟨τ, hτ1, hτ2, hτ3, -, -, -, -⟩ :=
    GlX.eqExt (GA p L (T.pos i + 1 + 1)) hCst hCf h' gτ la hh hhC hli hsp hgτ hgτC
  have hEϖ : IsEqC L (T.pos i + 1 + 1) T.J T.thr ϖ := ⟨hϖ2, hϖ3⟩
  have hEτ : IsEqC L (T.pos i + 1 + 1) T.J T.thr τ := ⟨hτ2, hτ3⟩
  refine ⟨bigOp L (T.pos i + 1 + 1) Pi τ, bigOp L (T.pos i + 1 + 1) Pi ϖ,
    bigOp_Y L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ, ?_, ?_, ?_, ?_⟩
  ·
    intro y hy
    have hint : ∀ μ v, v ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr → (GA p L (T.pos i + 1 + 1)).IsHW μ v →
        v ∈ IntPol p (Fin N × Fin r) → τ v ∈ IntPol p (Fin N × Fin r) := by
      intro μ v hv hw hvi
      have h1 := hspZ μ v hv hw hvi
      refine Submodule.span_induction (p := fun v _ => τ v ∈ IntPol p (Fin N × Fin r)) ?_ ?_ ?_ ?_ h1
      · rintro _ ⟨x, rfl⟩
        rw [hτ1]; exact hgτi x
      · rw [map_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb
        rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
      · intro a b _ hb
        rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hb
    exact int_main L ρ e1 (T.pos i + 1 + 1) hK hHP hHW (bigOp L (T.pos i + 1 + 1) Pi τ) (e1 * (T.pos i + 1 + 1))
      (bigOp_glAct L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ)
      (fun la0 x hx hxi => bigOp_int L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ hint la0 x hx hxi)
      y (Submodule.mem_inf.mp hy).2
  ·
    intro u hu u' hu'
    have hcore : ∀ g ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr, ∀ g' ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr,
        fock p (T.phi p L i g) (inOp L (T.pos i + 1 + 1) Pi τ g') =
          c * fock p (inOp L (T.pos i + 1 + 1) Pi ϖ g) g' := by
      intro g hg g' hg'
      rw [inOp_C L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi g' hg', inOp_C L (T.pos i + 1 + 1) _ T.J T.thr Pi ϖ hPi g hg]
      let B : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] :=
        (fockB p (Fin N × Fin r)).compl₁₂ (T.phi p L i) τ - c • (fockB p (Fin N × Fin r)).compl₁₂ ϖ LinearMap.id
      have hBa : ∀ x y, B x y = fock p (T.phi p L i x) (τ y) - c * fock p (ϖ x) y := by
        intro x y
        simp [B, fockB_apply]
      have hBz := GlX.form_zero (GA p L (T.pos i + 1 + 1)) hCst h' la hh hhC hsp B ?_ ?_ g hg g' hg'
      · rw [hBa] at hBz; exact sub_eq_zero.mp hBz
      · intro x hx y hy a b
        rw [hBa, hBa]
        change fock p (T.phi p L i (glAct p L (T.pos i + 1 + 1) a b x)) (τ y) -
          c * fock p (ϖ (glAct p L (T.pos i + 1 + 1) a b x)) y =
          fock p (T.phi p L i x) (τ (glAct p L (T.pos i + 1 + 1) b a y)) -
          c * fock p (ϖ x) (glAct p L (T.pos i + 1 + 1) b a y)
        rw [phi_glAct L T hadm i a b x, fock_glAct, hEτ.comm y hy b a, hEϖ.comm x hx a b, fock_glAct]
      · intro x y hxy
        rw [hBa, hτ1, hϖ1]
        have hterm : ∀ z, tc z y * fock p (T.phi p L i (h' x)) (h'' z) =
            if z = x then (if ‖d x‖ < (p : ℝ) ^ (-E) then 0 else c * fock p (h' x) (h' y)) else 0 := by
          intro z
          by_cases hz : la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E)
          · have h1 := hdiag x z (hxy.trans hz.1.symm)
            simp only [tc, if_pos hz]
            have h2 : c / d z * (cst * fock p (h' z) (h' y)) * fock p (T.phi p L i (h' x)) (h'' z) =
                c / d z * fock p (h' z) (h' y) * (cst * fock p (T.phi p L i (h' x)) (h'' z)) := by ring
            rw [h2, h1]
            by_cases hzx : z = x
            · subst hzx
              rw [if_pos rfl, if_pos rfl, if_neg hz.2]
              have hd0 := (good_norm E hE (d z) hz.2).2
              field_simp
            · rw [if_neg (Ne.symm hzx), if_neg hzx, mul_zero]
          · simp only [tc, if_neg hz, zero_mul]
            by_cases hzx : z = x
            · subst hzx
              rw [if_pos rfl]
              have : ‖d z‖ < (p : ℝ) ^ (-E) := by
                by_contra h; exact hz ⟨hxy, h⟩
              rw [if_pos this]
            · rw [if_neg hzx]
        have hsum : fock p (T.phi p L i (h' x)) (gτ y) =
            if ‖d x‖ < (p : ℝ) ^ (-E) then 0 else c * fock p (h' x) (h' y) := by
          simp only [gτ]
          rw [gammaIntegralityLemmas.fock_sum_right]
          simp only [gammaIntegralityLemmas.fock_smul_right, hterm]
          rw [Finset.sum_ite_eq']
          simp
        rw [hsum]
        by_cases hx : ‖d x‖ < (p : ℝ) ^ (-E)
        · simp only [gϖ, if_pos hx]
          rw [gammaIntegralityLemmas.fock_zero_left]; ring
        · simp only [gϖ, if_neg hx]
          ring
    have key := fock_ext_reduce (T.pos i + 1 + 1) (T.phi p L i) (inOp L (T.pos i + 1 + 1) Pi τ)
      (inOp L (T.pos i + 1 + 1) Pi ϖ) c (Cset p L (T.pos i + 1 + 1) T.J T.thr)
      (phi_mul_later L T hadm i) (phi_isF L T hadm i)
      (inOp_isF L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ) (inOp_isF L (T.pos i + 1 + 1) _ T.J T.thr Pi ϖ hPi hEϖ)
      hcore u u'
      (fun m => by rw [← Cset_thrUpTo]; exact slc_C L (T.pos i + 1 + 1) T.J (T.thrUpTo i) hu m)
      (fun m => slc_C L (T.pos i + 1 + 1) T.J T.thr hu' m)
    unfold fockN
    change fock p (T.phi p L i u) (ext (fsj N r (T.pos i + 1 + 1)) (inOp L (T.pos i + 1 + 1) Pi τ) u') / _ =
      c * (fock p (ext (fsj N r (T.pos i + 1 + 1)) (inOp L (T.pos i + 1 + 1) Pi ϖ) u) u' / _)
    rw [key, mul_div_assoc]
  · intro j hij u
    exact phi_ext_comm L T hadm i j hij _ (inOp_isF L (T.pos i + 1 + 1) _ T.J T.thr Pi ϖ hPi hEϖ) u
  · exact (count_le L (T.pos i + 1 + 1) _ T.J T.thr Pi hPi h' la hh hhC hli hsp
      (fun x => ‖d x‖ < (p : ℝ) ^ (-E)) ϖ hEϖ
      (fun x hx => hϖ6 x (by simp only [gϖ, if_neg hx]))
      (fun x hx => hϖ7 x (by simp only [gϖ, if_pos hx]))).trans
      (Finset.sum_le_sum fun x _ => transport_le L (T.pos i + 1 + 1) _ T.J T.thr Pi hPi h' la hh hhC hli hsp x (vv x)
        (hvv x) (hvvC x) (hvv0 x))

theorem mmwZ_mmw [NeZero r] {K : ℕ} (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) {g : MvPolynomial (Fin K × Fin r) ℚ_[p]} (hg : g ∈ MMwZ p LLw J M ρ w) :
    g ∈ MMw p LLw J M ρ w := (Submodule.mem_inf.mp hg).1

theorem mmwZ_polZ [NeZero r] {K : ℕ} (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) {g : MvPolynomial (Fin K × Fin r) ℚ_[p]} (hg : g ∈ MMwZ p LLw J M ρ w) :
    g ∈ PolZ p r LLw :=
  Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp
    (Submodule.mem_inf.mp hg).1).1).1).1, (Submodule.mem_inf.mp hg).2⟩

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames

end Formalism.CountingSumsFrames
