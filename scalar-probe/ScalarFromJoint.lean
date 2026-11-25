module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFaStatement

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

example : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ f : HdR o₀.A →ₗ[k] HdR o₀.A, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) f → ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f x) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ β ht φ hφ f hf
  obtain ⟨o, m, hm⟩ := GlobalTheory.UPel.HT.exists_sqZero_lift_realising_ks
    p D R b N hN hNp k t o₀ β ht φ hφ 1 (fun _ => f) (fun _ => hf)
  let c : (Fin 1 → k) →ₗ[k] k := LinearMap.proj 0
  let σ := (TrivSqZeroExt.map c).toRingHom
  let τ := spMap σ
  let s := spMap (algebraMap k (TrivSqZeroExt k (Fin 1 → k))) ≫ t
  have hbase' : σ.comp (algebraMap k (TrivSqZeroExt k (Fin 1 → k))) = algebraMap k (DualNumber k) := by
    ext a
    simp [σ, TrivSqZeroExt.algebraMap_eq_inl]
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
  obtain ⟨mc⟩ := (GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o₀ oc o
    (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) τ).2 (by rw [hfst]; exact ⟨m⟩) ⟨nc⟩
  rw [← hbase]
  refine ⟨oc, mc, fun x hx => ?_⟩
  have e : c ∘ₗ (LinearMap.pi fun _ : Fin 1 => f x) = f x := by
    ext q
    rfl
  have h := GlobalTheory.HTUniv.Nat.main p D R b N hN hNp k t o₀ 1 s o m c
    _ oc mc nc x _ (hm x hx)
  simpa only [e] using h
