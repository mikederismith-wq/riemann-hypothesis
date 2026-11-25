module

meta import Lean.Elab.Command
meta import Lean.Util.FoldConsts
meta import Lean.Util.CollectAxioms
public import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystalOfDualAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationHasComplement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationOrderStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroLiftRealisingKs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilLagrangianOfLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftOrderActionHodgeSummand
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsPolarisationBundleLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieMultiplicitySquareZeroLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftLieOfHodgeSummandLieStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPrimeToPLevelLiftSquareZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRealiseKodairaSpencerDirectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBCTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceLeHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFilHtObject
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClsDiag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumProjSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
public import Mathlib.Tactic.Linter.Style
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

theorem fil_iff_red_glueFil_scalar_api_probe : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl o₀.A).Corr e y) := by
  intro p _ D R _ b N _ k _ t o₀ β _ φ _ d f _ y
  constructor
  · intro hy
    obtain ⟨e, he, hc⟩ := exists_mem_glueFil o₀.A o₀.ab f hy
    refine ⟨e, he, corr_of_fst o₀.A o₀.ab e y fun c => ?_⟩
    rw [hc c]
    simp
  · rintro ⟨e, ⟨x, hx, z, hz, he⟩, hcorr⟩
    have hxy : y = x := LinearMap.ext fun c => by
      have h1 := hcorr ((GlobalTheory.FODef.constMorV k (Fin d → k) o₀.A).pull c)
      rw [red_pull_constMorV_pull, he c] at h1
      simpa using h1
    exact hxy ▸ hx

end GlobalTheory.HTGlue

namespace GlobalTheory.HTGlue

theorem push_mem_glueFil_scalar_api_probe : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ (c : D.O), ∀ e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (c)) (e)) ∈ (GlobalTheory.HTGlue.glueFil o₀.A f)) := by
  intro p _ D R _ b N _ k _ t o₀ β _ φ _ d f hf c e he
  haveI := o₀.act.hom c
  obtain ⟨x, hx, z, hz, hxz⟩ := he
  let g : HdR o₀.A →ₗ[k] HdR o₀.A := GlobalTheory.HTCount.crysAct o₀ c
  have hg : ∀ h, g h = push (dp0 k) (𝟙 _) (o₀.act.act c) h := fun _ ↦ rfl
  refine ⟨g x, push_mem_Fil _ hx, fun j ↦ g (z j) - (f j (g x) - g (f j x)),
    fun j ↦ sub_mem (push_mem_Fil _ (hz j)) ((hf j).1 c x hx), fun q ↦ ?_⟩
  rw [push_apply, primPull_constMorV_pull, hxz]
  congr 2
  funext j
  rw [← push_apply, ← hg]
  simp only [map_add (f := _), LinearMap.add_apply, LinearMap.sub_apply]
  abel

end GlobalTheory.HTGlue

namespace GlobalTheory.HTGlueIsoPol

open GlobalTheory.AbDual

theorem glueFil_isotropic_scalar_api_probe : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ Φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[(TrivSqZeroExt k (Fin d → k))] Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[(TrivSqZeroExt k (Fin d → k))] (TrivSqZeroExt k (Fin d → k)), GlobalTheory.AbDual.IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A o₀.A o₀.P Φ → ∀ x ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), ∀ y ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), Φ x y = 0) := by
  intro p _ D R _ b N hNp k _ t o₀ β hβ φ hφ d f hf Φ hΦ X hX Y hY
  have h2 := GlobalTheory.FODef.sqZero k (Fin d → k)
  have hA := o₀.ab
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k o₀.A hA
  obtain ⟨A, _, i, hi, hAC, hgC⟩ := GlobalTheory.abelianScheme_constLift (TrivSqZeroExt k (Fin d → k)) k
    (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom (algebraMap k (TrivSqZeroExt k (Fin d → k)))
    (by ext; simp [TrivSqZeroExt.algebraMap_eq_inl]) o₀.A g hA hg
  have ADR := GlobalTheory.abelianDeRham
  have ADC := GlobalTheory.abelianDualCrystal_of_dualAbelianScheme GlobalTheory.dualAbelianScheme
  have CS := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 (isDPNilpotent_squareZero h2)
    (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl hAC hgC hAC hgC hi hi
  have m := GlobalTheory.FODef.constMorV k (Fin d → k) o₀.A
  have hBC : m.IsBC := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) o₀.A hA _ m
  have hP := o₀.isLB
  have e0 : LBIso (o₀.P.pull (𝟙 _)) o₀.P := by
    first
      | exact LBIso.chartPull (chartPullPull o₀.P (𝟙 _)) (chartPullId o₀.P) (PolBaseChange.lbIso_refl hP)
  obtain ⟨Ψ, hΨ, hΨc⟩ := hφ.pull hP m m (h := 𝟙 _) (by simp) (by simp) hP e0
  obtain rfl := hΦ.unique CS hP hΨ

  have key : ∀ u v : HdR o₀.A, Φ (hBC.bcMap u) (hBC.bcMap v) = algebraMap k _ (φ u v) := fun u v ↦
    hΨc u _ v _ ((hBC.corr_iff (h := u)).2 rfl) ((hBC.corr_iff (h := v)).2 rfl)

  have dec : ∀ Z ∈ GlobalTheory.HTGlue.glueFil o₀.A f, ∃ x ∈ Fil o₀.A, ∃ z : Fin d → HdR o₀.A, (∀ j, z j ∈ Fil o₀.A) ∧
      Z = hBC.bcMap x + ∑ j, (TrivSqZeroExt.inr (Pi.single j 1) : TrivSqZeroExt k (Fin d → k)) •
        hBC.bcMap (f j x + z j) := by
    rintro Z ⟨x, hx, z, hz, hZ⟩
    refine ⟨x, hx, z, hz, ext_of_isBC hBC fun c ↦ ?_⟩
    rw [hZ c, tsze_coords, crys_add_apply]
    refine (congrArg₂ (· + ·) (bcMap_pull hBC x c) ?_).symm
    exact (crys_sum_apply _ _ _).trans (Finset.sum_congr rfl fun j _ ↦
      (crys_smul_apply _ _ _).trans (congrArg _ (bcMap_pull hBC _ c)))
  have iso := (GlobalTheory.HTLagr.fil_lagrangian p D R b N k t o₀ φ ⟨g, hg⟩ hφ).1
  refine (dec X hX).elim fun x hx' ↦ (dec Y hY).elim fun y hy' ↦ ?_
  refine hx'.2.elim fun z hz' ↦ hy'.2.elim fun w hw' ↦ ?_
  refine (congrArg₂ (fun a b ↦ Φ a b) hz'.2 hw'.2).trans ?_
  refine glue_pairing_eq_zero hBC.bcMap Φ φ key (iso x hx'.1 y hy'.1) fun j ↦ ?_
  simp only [map_add (f := _), LinearMap.add_apply, iso _ (hz'.1 j) _ hy'.1, iso _ hx'.1 _ (hw'.1 j), add_zero]
  exact (hf j).2.2 x hx'.1 y hy'.1

end GlobalTheory.HTGlueIsoPol

namespace GlobalTheory.HTGlueLie

open GlobalTheory.HTCount

theorem glueFil_lie_scalar_api_probe : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - algebraMap k (TrivSqZeroExt k (Fin d → k)) (β b.ρ) • e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f) → ∃ w : Fin D.a → Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - algebraMap k (TrivSqZeroExt k (Fin d → k)) (β (b.t i c)) • w i ∈ (GlobalTheory.HTGlue.glueFil o₀.A f)) ∧ e - ∑ i, w i ∈ (GlobalTheory.HTGlue.glueFil o₀.A f)) := by
  intro p _ D R _ b N _ k _ t o₀ β hs φ _ d f hf e he
  have hT : ∀ (x : D.O) (π : TrivSqZeroExt k (Fin d → k) →ₗ[k] k) (u : CrysC k d o₀.A),
      crd o₀.A π ((haveI := o₀.act.hom x; push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k)))
        (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act x)) u) =
        crysAct o₀ x (crd o₀.A π u) := fun x π u => by
    haveI := o₀.act.hom x
    exact crd_push o₀.A π _ u
  have hZ := lieZ_le_fil o₀ β hs
  have hfZ : ∀ j, ∀ x ∈ lieZ o₀ β, f j x ∈ Fil o₀.A := fun j => (hf j).2.1
  have hδ := root_sub_ne_zero b β
  have hex : ∃ e' : CrysC k d o₀.A, e' = algebraMap k (TrivSqZeroExt k (Fin d → k))
      (β b.ρ - ((D.tr : k) - β b.ρ))⁻¹ •
      ((haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k)))
        (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω))) e -
        algebraMap k (TrivSqZeroExt k (Fin d → k)) ((D.tr : k) - β b.ρ) • e) := ⟨_, rfl⟩
  obtain ⟨e', he'⟩ := hex
  have hrho : ∀ π, crd o₀.A π e' ∈ rhoPart o₀ β := fun π => by
    rw [he', crd_smul, map_sub, hT, crd_smul]
    exact smul_mem_rhoPart o₀ β _ _
  choose r lam c hc using fun i => exists_combo (fun j => β.comp (b.t j)) (injective_chars b β)
    (fun j => if i = j then (1 : k) else 0)
  have hc' : ∀ i j, ∑ l, lam i l * β (b.t j (c i l)) = if i = j then 1 else 0 := hc
  refine ⟨fun i => ∑ l, algebraMap k (TrivSqZeroExt k (Fin d → k)) (lam i l) •
    (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O (c i l)); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k)))
        (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O (c i l)))) e',
    fun i c₀ => ?_, ?_⟩
  · refine mem_glueFil_of_crd_mem o₀.A f _ hZ hfZ _ fun π => ?_
    have H := mul_sub_mem_lieZ o₀ β (lam i) (c i) i (hc' i) (hrho π) c₀
    convert H using 1

    simp only [map_sub, map_sum, hT, crd_smul]
  · have hk : algebraMap k (TrivSqZeroExt k (Fin d → k)) (β b.ρ - ((D.tr : k) - β b.ρ))⁻¹ *
        (algebraMap k (TrivSqZeroExt k (Fin d → k)) (β b.ρ) -
          algebraMap k (TrivSqZeroExt k (Fin d → k)) ((D.tr : k) - β b.ρ)) = 1 := by
      rw [← map_sub, ← map_mul, inv_mul_cancel₀ hδ, map_one]
    refine sub_mem_trans _ (sub_mem_of_inv _ hk he' he) ?_
    refine mem_glueFil_of_crd_mem o₀.A f _ hZ hfZ _ fun π => ?_
    have H := one_sub_mem_lieZ o₀ β lam c hc' (hrho π)
    convert H using 1

    simp only [map_sub, map_sum, hT, crd_smul]

end GlobalTheory.HTGlueLie

theorem GlobalTheory.UPel.HT.exists_sqZero_lift_realising_ks_scalar_api_probe : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → ∃ (o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t)) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)), ∀ x ∈ Fil o₀.A, GlobalTheory.FODef.IsFilLiftV m.cart x (LinearMap.pi fun j => f j x) := by
  intro p _ D R _ b N hNp k _ t o₀ β ht φ hφ d f hf
  haveI := GlobalTheory.HTGlue.isArtinianRing_tsze k d
  have hsurj : Function.Surjective (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, by simp⟩
  have htR : spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t =
      spMap ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp β) := by
    rw [ht]; exact (GlobalTheory.Cris.spMap_comp _ _).symm
  have ht₀ : t = spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫
      (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t) := by
    rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp]
    have : (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp (algebraMap k (TrivSqZeroExt k (Fin d → k))) = RingHom.id k := by
      ext a; simp
    rw [this]
    simp [spMap]
  obtain ⟨M₀, hM⟩ := Submodule.exists_isCompl (Fil o₀.A)
  have h2 := _root_.GlobalTheory.HTGlue.fil_iff_red_glueFil_scalar_api_probe p D R b N hNp k t o₀ β ht φ hφ d f hf
  have h3 := _root_.GlobalTheory.HTGlue.push_mem_glueFil_scalar_api_probe p D R b N hNp k t o₀ β ht φ hφ d f hf
  have h4 := _root_.GlobalTheory.HTGlueIsoPol.glueFil_isotropic_scalar_api_probe p D R b N hNp k t o₀ β ht φ hφ d f hf
  have h5 := _root_.GlobalTheory.HTGlueLie.glueFil_lie_scalar_api_probe p D R b N hNp k t o₀ β ht φ hφ d f hf
  have key := _root_.GlobalTheory.UPel.HT.exists_sqZero_lift_of_fil p D R b N hNp (TrivSqZeroExt k (Fin d → k)) k
    (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom hsurj (GlobalTheory.FODef.sqZero k (Fin d → k))
    ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp β) (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t) t htR ht₀ o₀ (GlobalTheory.HTGlue.glueFil o₀.A f)
  obtain ⟨o, m, hm⟩ := key ⟨_, GlobalTheory.HTGlue.isCompl_glueFil o₀.A o₀.ab f M₀ hM⟩ h2 h3 h4 h5
  refine ⟨o, m, fun x hx => ?_⟩
  obtain ⟨e, he, hce⟩ := GlobalTheory.HTGlue.exists_mem_glueFil o₀.A o₀.ab f hx
  unfold GlobalTheory.FODef.IsFilLiftV
  refine ⟨e, ?_, hce⟩
  rw [hm]; exact he

namespace GlobalTheory.UPel.HT

open GlobalTheory.UPel.HT.MapComp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem MapComp.cancel_fac_scalar_api_probe {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    {outer : S₁ ⟶ S₃} (houter : f ≫ g = outer)
    (m : ObjMap o₁ o₃ outer) (m₂ : ObjMap o₂ o₃ g) : ∃ mc : ObjMap o₁ o₂ f, mc.φ ≫ m₂.φ = m.φ := by
  subst outer
  have w : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by rw [m.cart.1.w, Category.assoc]
  set φ := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) w
  have hφ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
  have hφ' : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
  have n : IsGrpPullback o₁.A o₃.A (f ≫ g) (φ ≫ m₂.φ) := by rw [hφ]; exact m.cart
  obtain ⟨φ₂, sq⟩ := exists_isSquare hφ'
  have e : m.φ₂ = φ₂ ≫ m₂.φ₂ := isSquare_unique m.sq (hφ ▸ isSquare_comp sq m₂.sq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (o₂.act.act c).left := by
    intro c
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₂.act, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = f ≫ (o₂.eta y).left := by
    intro y
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₂.eta]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ f = f ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  exact ⟨{ φ := φ
           φ₂ := φ₂
           cart := m₂.cart.cancel n hφ'
           sq := sq
           act := hact
           pol := LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
             (LBIso.symm (lbIso_pull_comp m₂.pol φ₂ e))
           eta := heta }, hφ⟩

end GlobalTheory.UPel.HT

namespace GlobalTheory.HTUniv.Nat

open GlobalTheory.CechPic GlobalTheory.UPel.HT

theorem of_comm_scalar_api_probe : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∀ (d : ℕ) (s : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)) (c : (Fin d → k) →ₗ[k] k) (s' : Sp (DualNumber k) ⟶ Sp R) (o' : GlobalTheory.UPel.HT.Obj b N s') (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (n : GlobalTheory.UPel.HT.ObjMap o' o (spMap (TrivSqZeroExt.map c).toRingHom)) (hrig : m'.φ ≫ n.φ = m.φ) (x : HdR o₀.A) (y : primDR o₀.A →ₗ[k] (Fin d → k)), GlobalTheory.FODef.IsFilLiftV m.cart x y → IsFilLift m'.cart x (c ∘ₗ y) := by
  intro p _ D R _ b N k _ t o₀ d s o m c s' o' m' n hrig x y hxy
  obtain ⟨dd, hdd, edd⟩ := hxy
  let σ : TrivSqZeroExt k (Fin d → k) →+* DualNumber k := (TrivSqZeroExt.map c).toRingHom
  have hz : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap σ =
      spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom := by
    rw [← Cris.spMap_comp]
    congr 1
    ext a <;> simp [σ]

  have hdp : (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))).IsDPMorphism (epsDP k) σ := by
    unfold epsDP
    refine isDPMorphism_sqDP _ _ σ fun a ha => ?_
    have ha' : a.fst = 0 := ha
    change (σ a).fst = 0
    simp [σ, ha']
  have M : GrpMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
      o₀.A (epsDP k) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A σ (𝟙 _) (Over.Hom.left (𝟙 o₀.A)) :=
    GrpMor.of_hom hdp hz.symm (𝟙 o₀.A)
  have hBC : (constMor o₀.A).IsBC := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k k o₀.A o₀.ab _ (constMor o₀.A)
  have hBCV : (GlobalTheory.FODef.constMorV k (Fin d → k) o₀.A).IsBC :=
    GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) o₀.A o₀.ab _ _
  let d' : Crys (epsDP k) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A :=
    hBC.bcMap x + (TrivSqZeroExt.inr (1 : k) : DualNumber k) • hBC.bcMap (c ∘ₗ y)
  have ed' : ∀ q, d' ((constMor o₀.A).pull q) = TrivSqZeroExt.inl (x q) + TrivSqZeroExt.inr (c (y q)) := by
    intro q
    have e1 := (hBC.corr_iff (h := x)).2 rfl q
    have e2 := (hBC.corr_iff (h := c ∘ₗ y)).2 rfl q
    simp only [d', LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, e1, e2]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hMc : M.Corr dd d' := corr_of_isBC hBCV M fun q => by
    rw [GrpMor.pull_pull (GlobalTheory.FODef.constMorV k (Fin d → k) o₀.A) M (constMor o₀.A) (fun _ => by
      ext <;> simp [σ, TrivSqZeroExt.algebraMap_eq_inl]) (by simp) q, ed', edd q]
    ext <;> simp [σ]
  have Nm : GrpMor (dp0 _) (𝟙 _) o.A (dp0 _) (𝟙 _) o'.A σ (spMap σ) n.φ :=
    GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) n.cart
  have hNc := crysToDR_corr (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) m.cart m'.cart M Nm
    (by rw [hrig]; simp) hMc
  refine ⟨d', ?_, fun q => ?_⟩
  · letI : Algebra (TrivSqZeroExt k (Fin d → k)) (DualNumber k) := σ.toAlgebra
    obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim (TrivSqZeroExt k (Fin d → k)) o.A o.ab
    have hF := (GlobalTheory.abelianDeRham.2.2.1 _ o.A g o.ab hg (DualNumber k) o'.A n.φ n.cart).2
    exact mem_Fil_of_corr (hφ := n.cart) hF hNc hdd
  · rw [ed']
    rfl

end GlobalTheory.HTUniv.Nat

theorem GlobalTheory.UPel.HT.realise_singleton_scalar_api_probe : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ f : HdR o₀.A →ₗ[k] HdR o₀.A, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) f → ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f x) := by
  intro p _ D R _ b N hNp k _ t o₀ β ht φ hφ f hf
  obtain ⟨o, m, hm⟩ := GlobalTheory.UPel.HT.exists_sqZero_lift_realising_ks_scalar_api_probe
    p D R b N hNp k t o₀ β ht φ hφ 1 (fun _ => f) (fun _ => hf)
  let c : (Fin 1 → k) →ₗ[k] k := LinearMap.proj 0
  let σ := (TrivSqZeroExt.map c).toRingHom
  let τ := spMap σ
  let s := spMap (algebraMap k (TrivSqZeroExt k (Fin 1 → k))) ≫ t
  have hbase' : σ.comp (algebraMap k (TrivSqZeroExt k (Fin 1 → k))) = algebraMap k (DualNumber k) := by
    exact RingHom.ext (fun a => (TrivSqZeroExt.map c).commutes a)
  have hbase : τ ≫ s = spMap (algebraMap k (DualNumber k)) ≫ t := by
    dsimp only [τ, s]
    rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp, hbase']
  obtain ⟨oc, ⟨nc⟩⟩ :=
    GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N _ _ s τ o
  have hfst : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ τ =
      spMap (TrivSqZeroExt.fstHom k k (Fin 1 → k)).toRingHom := by
    dsimp only [τ, σ]
    rw [← GlobalTheory.Cris.spMap_comp]
    congr 1
    ext a
    simp
  obtain ⟨mc, hc⟩ := GlobalTheory.UPel.HT.MapComp.cancel_fac_scalar_api_probe
    (f := spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (g := τ) hfst m nc
  rw [← hbase]
  refine ⟨oc, mc, fun x hx => ?_⟩
  have e : c ∘ₗ (LinearMap.pi fun _ : Fin 1 => f x) = f x := by
    ext q
    rfl
  have h := GlobalTheory.HTUniv.Nat.of_comm_scalar_api_probe p D R b N k t o₀ 1 s o m c
    _ oc mc nc hc x _ (hm x hx)
  simpa only [e] using h

theorem GlobalTheory.HTRealise.realise_core_scalar_api_probe (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (hN : N.Coprime p) (k : Type) [Field k] (β : R →+* k)
    (s : Sp k ⟶ Sp R) (hs : s = spMap β) (o₀ : GlobalTheory.UPel.HT.Obj b N s)
    (φ : LinearMap.BilinForm k (HdR o₀.A)) (hφ : GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ)
    (f : HdR o₀.A →ₗ[k] HdR o₀.A)
    (hf : IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) f)
    (tR : R →+* DualNumber k) (htR : tR = (algebraMap k (DualNumber k)).comp β)
    (hs' : s = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap tR) :
    ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap tR))
      (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)),
      ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f x) := by
  have e : spMap (algebraMap k (DualNumber k)) ≫ s = spMap tR := by
    rw [hs, htR, ← GlobalTheory.Cris.spMap_comp]
  simpa only [e] using (GlobalTheory.UPel.HT.realise_singleton_scalar_api_probe p D R b N hN k s o₀ β hs φ hφ f hf)

end

open Lean in
run_cmd Elab.Command.liftTermElabM do
  let env := (← getEnv).setExporting false
  let target : Name := `GlobalTheory.HTRealise.realise_core_scalar_api_probe
  let original : Name := `GlobalTheory.HTRealise.realise_core
  let some newDecl := env.find? target | throwError "missing unrestricted witness"
  let some oldDecl := env.find? original | throwError "missing pinned signature"
  unless (← Meta.isDefEq oldDecl.type newDecl.type) do
    throwError "the new public theorem differs from the type on main"
  let prescribed : List Name := [
    `GlobalTheory.HTGlue.fil_iff_red_glueFil_scalar_api_probe,
    `GlobalTheory.HTGlue.push_mem_glueFil_scalar_api_probe,
    `GlobalTheory.HTGlueIsoPol.glueFil_isotropic_scalar_api_probe,
    `GlobalTheory.HTGlueLie.glueFil_lie_scalar_api_probe,
    `GlobalTheory.UPel.HT.exists_sqZero_lift_realising_ks_scalar_api_probe,
    `GlobalTheory.UPel.HT.MapComp.cancel_fac_scalar_api_probe,
    `GlobalTheory.HTUniv.Nat.of_comm_scalar_api_probe,
    `GlobalTheory.UPel.HT.realise_singleton_scalar_api_probe, target]
  let forbiddenNames : List String := [
    "GlobalTheory.HTRealise.realise_core", "GlobalTheory.HTRealise.lift_with_filtration",
    "GlobalTheory.HTRealise.isFilLift_of_graphFil", "GlobalTheory.UPel.HT.realise_isKS",
    "GlobalTheory.HTUniv.Nat.main", "GlobalTheory.HTUniv.Nat.phi_eq",
    "GlobalTheory.UPel.HT.exists_sqZero_lift_realising_ks", "sorryAx"]
  let mut pending : List Name := [target]
  let mut visited : List Name := []
  for _ in [0:4096] do
    let nm :: rest := pending | break
    pending := rest
    if visited.contains nm then continue
    visited := nm :: visited
    let some info := env.find? nm | throwError "missing local proof {nm}"
    let some value := info.value? (allowOpaque := true) | throwError "no body for local proof {nm}"
    let deps := value.getUsedConstants.toList
    logInfo m!"SCALAR_DIRECT {nm} {repr (deps.map Name.toString)}"
    for dep in deps do
      let depText := dep.toString
      if forbiddenNames.any (fun blocked => depText == blocked || depText.endsWith ("." ++ blocked)) then
        throwError "{nm} cites {dep}"
      if (env.getModuleIdxFor? dep).isNone && !(visited.contains dep) then
        pending := dep :: pending
  unless pending.isEmpty && prescribed.all visited.contains do
    throwError "incomplete traversal of local proof dependencies: {repr visited}"
  let axs ← collectAxioms target
  let kernelAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]
  unless axs.toList.all kernelAxioms.contains do
    throwError "unapproved axiom: {repr axs}"
  logInfo m!"SCALAR_AUDIT_OK type_defeq=true local_bodies={visited.length} axioms={repr axs}"
