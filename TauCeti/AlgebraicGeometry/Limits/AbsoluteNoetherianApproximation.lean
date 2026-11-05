/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Limits.ModelExtension

/-!
# Absolute Noetherian approximation

Every quasi-compact quasi-separated scheme is the limit of a cofiltered diagram, with affine
transition maps, of quasi-compact quasi-separated schemes of finite presentation over `ℤ`
(Stacks, Proposition 32.5.4 (01ZA)). The proof is by induction on the number of affine opens
covering the scheme: the affine case is
`TauCeti.AlgebraicGeometry.Scheme.exists_isLimit_finitePresentation_of_isAffine`, and the
induction step is
`TauCeti.AlgebraicGeometry.Scheme.exists_isLimit_finitePresentation_of_sup_eq_top`.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.exists_isLimit_finitePresentation`: absolute Noetherian
  approximation.
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

/-- `X` is the limit of a cofiltered diagram, with affine transition maps, of quasi-compact
quasi-separated schemes of finite presentation over `ℤ`. -/
private def IsApproximable (X : Scheme.{u}) : Prop :=
  ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I) (D : I ⥤ Scheme.{u})
    (π : (Functor.const I).obj X ⟶ D), Nonempty (IsLimit (Cone.mk X π)) ∧
    (∀ ⦃i j : I⦄ (f : i ⟶ j), IsAffineHom (D.map f)) ∧
    ∀ i, CompactSpace (D.obj i) ∧ QuasiSeparatedSpace (D.obj i) ∧
      LocallyOfFinitePresentation (terminal.from (D.obj i))

private lemma IsApproximable.of_iso {X X' : Scheme.{u}} (e : X' ≅ X) (h : IsApproximable X) :
    IsApproximable X' := by
  obtain ⟨I, hI, hI', D, π, ⟨hπ⟩, h₁, h₂⟩ := h
  exact ⟨I, hI, hI', D, ((Cone.mk X π).extend e.hom).π,
    ⟨hπ.ofIsoLimit ((Cone.mk X π).extendIso e.symm)⟩, h₁, h₂⟩

private lemma IsApproximable.of_isAffine (X : Scheme.{u}) [IsAffine X] : IsApproximable X := by
  obtain ⟨I, hI, hI', D, π, hπ, h₁, h₂⟩ := Scheme.exists_isLimit_finitePresentation_of_isAffine X
  refine ⟨I, hI, hI', D, π, hπ, h₁, fun i ↦ ?_⟩
  have := (h₂ i).1
  exact ⟨inferInstance, inferInstance, (h₂ i).2⟩

private lemma IsApproximable.of_sup_eq_top {Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] {U W : Y.Opens} (hUW : U ⊔ W = ⊤) (hW : IsAffineOpen W)
    (h : IsApproximable U.toScheme) : IsApproximable Y := by
  obtain ⟨I, _, _, D, π, ⟨hπ⟩, h₁, h₂⟩ := h
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f) := fun f ↦ h₁ f
  have (i : I) : CompactSpace (D.obj i) := (h₂ i).1
  have (i : I) : QuasiSeparatedSpace (D.obj i) := (h₂ i).2.1
  have (i : I) : LocallyOfFinitePresentation (terminal.from (D.obj i)) := (h₂ i).2.2
  exact exists_isLimit_finitePresentation_of_sup_eq_top hUW hW D π hπ

/-- **Absolute Noetherian approximation.** Every quasi-compact quasi-separated scheme is the limit
of a cofiltered diagram, with affine transition maps, of quasi-compact quasi-separated schemes of
finite presentation over `ℤ`. Stacks, Proposition 32.5.4 (01ZA). -/
theorem exists_isLimit_finitePresentation (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I) (D : I ⥤ Scheme.{u})
      (π : (Functor.const I).obj X ⟶ D), Nonempty (IsLimit (Cone.mk X π)) ∧
      (∀ ⦃i j : I⦄ (f : i ⟶ j), IsAffineHom (D.map f)) ∧
      ∀ i, CompactSpace (D.obj i) ∧ QuasiSeparatedSpace (D.obj i) ∧
        LocallyOfFinitePresentation (terminal.from (D.obj i)) := by
  classical
  suffices h : ∀ s : Finset X.affineOpens, IsApproximable (⨆ w ∈ s, (w : X.Opens)).toScheme by
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun w : X.affineOpens ↦ (w : Set X))
      (fun w ↦ w.1.isOpen) fun x _ ↦ by
        obtain ⟨w, hw, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
        exact Set.mem_iUnion.mpr ⟨⟨w, hw⟩, hx⟩
    have hs : ⨆ w ∈ t, (w : X.Opens) = ⊤ := by
      refine eq_top_iff.mpr fun x _ ↦ ?_
      obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨w, TopologicalSpace.Opens.mem_iSup.mpr ⟨hw, hxw⟩⟩
    exact (h t).of_iso (X.topIso.symm ≪≫ X.isoOfEq hs.symm)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    have : IsAffine (⊥ : X.Opens).toScheme := isAffineOpen_bot X
    exact (IsApproximable.of_isAffine _).of_iso (X.isoOfEq (V := ⊥) (by simp))
  | insert w s _ ih =>
    let O := ⨆ w ∈ s, (w : X.Opens)
    have hO : IsCompact (O : Set X) := by
      simpa [O, TopologicalSpace.Opens.coe_iSup] using
        s.isCompact_biUnion fun w _ ↦ w.2.isCompact
    have : CompactSpace (w.1 ⊔ O).toScheme :=
      isCompact_iff_compactSpace.mp (w.2.isCompact.union hO)
    have : QuasiSeparatedSpace (w.1 ⊔ O).toScheme :=
      (w.1 ⊔ O).ι.isOpenEmbedding.quasiSeparatedSpace
    have hUW : (w.1 ⊔ O).ι ⁻¹ᵁ O ⊔ (w.1 ⊔ O).ι ⁻¹ᵁ w.1 = ⊤ := by
      rw [← Scheme.Hom.preimage_sup, sup_comm, Scheme.Opens.ι_preimage_self]
    have hW : IsAffineOpen ((w.1 ⊔ O).ι ⁻¹ᵁ w.1) :=
      w.2.preimage_of_isOpenImmersion _ (by rw [Scheme.Opens.opensRange_ι]; exact le_sup_left)
    have h := IsApproximable.of_sup_eq_top hUW hW (ih.of_iso ((w.1 ⊔ O).ι.isoImage _ ≪≫
      X.isoOfEq (((w.1 ⊔ O).functor_map_eq_inf O).trans (inf_eq_left.mpr le_sup_right))))
    exact h.of_iso (X.isoOfEq (Finset.iSup_insert w s _))

end TauCeti.AlgebraicGeometry.Scheme
