/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import TauCeti.Algebra.Category.Ring.FGSubringPair

/-!
# The fibre products of a cofiltered system of models of an open

Let `V` be an open of a scheme `X`, the limit of a cofiltered diagram `D` of quasi-compact
quasi-separated schemes with affine transition maps, through `π : V ⟶ D`. The fibre products
`P j = Γ(X, ⊤) ×_{Γ(X, V)} Γ(D j, ⊤)` (Mathlib's `CommRingCat.pullbackCone`) form a system of
rings `fiberProductSystem π : Iᵒᵖ ⥤ CommRingCat` with a cocone to `Γ(X, ⊤)` by the first
projections. Every global section of `X` comes from some `P j`, and an element of `P j` with first
component zero vanishes in some later `P j'`; so `Γ(X, ⊤)` is the colimit of the finitely
generated subrings of the `P j` (`TauCeti.CommRingCat.FGSubringPair`).

For `X = Spec R` affine this is the ring-theoretic half of the extension step in the proof of
Stacks, Proposition 32.5.4 (01ZA): with
`TauCeti.AlgebraicGeometry.Scheme.exists_finset_isPullback_toSpecΓ_comp_SpecMap` making each
`D j` an open of `Spec C` with preimage `V`, the affine schemes `Spec C` form a cofiltered system
of models of `X` near `V` with limit `Spec R`.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.fiberProductSystem`: the system of fibre products.
* `TauCeti.AlgebraicGeometry.Scheme.fiberProductCocone`: its cocone to `Γ(X, ⊤)`.
* `TauCeti.AlgebraicGeometry.Scheme.isColimitFiberProductCocone`: `Γ(X, ⊤)` is the colimit of
  the finitely generated subrings of the fibre products.
* `TauCeti.AlgebraicGeometry.Scheme.isLimitSpecFiberProductCocone`: `Spec Γ(X, ⊤)` is the
  cofiltered limit of their spectra.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {X : Scheme.{u}} {V : X.Opens}
  (π : (Functor.const I).obj V.toScheme ⟶ D)

/-- The fibre product `Γ(X, ⊤) ×_{Γ(X, V)} Γ(D j, ⊤)` of the restriction and of `π_j^*`. -/
abbrev fiberProductCone (j : I) :
    PullbackCone (X.presheaf.map (homOfLE (le_top (a := V))).op)
      ((π.app j).appTop ≫ V.topIso.hom) :=
  CommRingCat.pullbackCone _ _

lemma fiberProductCone_condition {j j' : I} (f : j' ⟶ j) :
    (fiberProductCone π j).fst ≫ X.presheaf.map (homOfLE le_top).op =
      ((fiberProductCone π j).snd ≫ (D.map f).appTop) ≫ (π.app j').appTop ≫ V.topIso.hom := by
  rw [(fiberProductCone π j).condition, Category.assoc, ← Category.assoc (D.map f).appTop,
    ← Scheme.Hom.comp_appTop, ← π.naturality f]
  simp

/-- The map `P j ⟶ P j'` of fibre products along a morphism `j' ⟶ j`. -/
noncomputable def fiberProductMap {j j' : I} (f : j' ⟶ j) :
    (fiberProductCone π j).pt ⟶ (fiberProductCone π j').pt :=
  PullbackCone.IsLimit.lift (CommRingCat.pullbackConeIsLimit _ _)
    (fiberProductCone π j).fst ((fiberProductCone π j).snd ≫ (D.map f).appTop)
    (fiberProductCone_condition π f)

@[reassoc (attr := simp)]
lemma fiberProductMap_fst {j j' : I} (f : j' ⟶ j) :
    fiberProductMap π f ≫ (fiberProductCone π j').fst = (fiberProductCone π j).fst :=
  PullbackCone.IsLimit.lift_fst _ _ _ _

@[reassoc (attr := simp)]
lemma fiberProductMap_snd {j j' : I} (f : j' ⟶ j) :
    fiberProductMap π f ≫ (fiberProductCone π j').snd =
      (fiberProductCone π j).snd ≫ (D.map f).appTop :=
  PullbackCone.IsLimit.lift_snd _ _ _ _

/-- The system of fibre products `Γ(X, ⊤) ×_{Γ(X, V)} Γ(D j, ⊤)`. -/
@[simps]
noncomputable def fiberProductSystem : Iᵒᵖ ⥤ CommRingCat.{u} where
  obj j := (fiberProductCone π j.unop).pt
  map f := fiberProductMap π f.unop
  map_id j := by
    refine PullbackCone.IsLimit.hom_ext (CommRingCat.pullbackConeIsLimit _ _) ?_ ?_
    · simp
    · simp
  map_comp f g := by
    refine PullbackCone.IsLimit.hom_ext (CommRingCat.pullbackConeIsLimit _ _) ?_ ?_
    · simp
    · simp

/-- The second projection `Γ(X, ⊤) ×_{Γ(X, V)} Γ(D j, ⊤) ⟶ Γ(D j, ⊤)`, as a morphism out of
`(fiberProductSystem π).obj (op j)`. -/
noncomputable abbrev fiberProductSnd (j : I) : (fiberProductSystem π).obj (op j) ⟶ Γ(D.obj j, ⊤) :=
  (fiberProductCone π j).snd

@[reassoc (attr := simp)]
lemma fiberProductSystem_map_fiberProductSnd {j j' : I} (f : j' ⟶ j) :
    (fiberProductSystem π).map f.op ≫ fiberProductSnd π j' =
      fiberProductSnd π j ≫ (D.map f).appTop :=
  fiberProductMap_snd π f

/-- The cocone on the fibre products to `Γ(X, ⊤)` by the first projections. -/
@[simps pt]
noncomputable def fiberProductCocone : Cocone (fiberProductSystem π) where
  pt := Γ(X, ⊤)
  ι.app j := (fiberProductCone π j.unop).fst
  ι.naturality _ _ f := (fiberProductMap_fst π f.unop).trans (Category.comp_id _).symm

@[simp]
lemma fiberProductCocone_ι_app (j : Iᵒᵖ) :
    (fiberProductCocone π).ι.app j = (fiberProductCone π j.unop).fst :=
  rfl

/-- Let `V` be an open of `X`, the limit of a cofiltered diagram of quasi-compact quasi-separated
schemes `D j` with affine transition maps. Then, for finite subsets `s j` of the fibre products
`P j = Γ(X, ⊤) ×_{Γ(X, V)} Γ(D j, ⊤)`, `Γ(X, ⊤)` is the colimit of the finitely generated subrings
of the `P j` containing `s j`. Part of the proof of Stacks, Proposition 32.5.4 (01ZA). -/
noncomputable def isColimitFiberProductCocone [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (hc : IsLimit (Cone.mk _ π))
    (s : ∀ j, Finset ((fiberProductSystem π).obj (op j))) :
    IsColimit (TauCeti.CommRingCat.FGSubringPair.cocone (s := s) (fiberProductCocone π)) := by
  refine TauCeti.CommRingCat.FGSubringPair.isColimitCocone _ (fun r ↦ ?_) fun j y hy ↦ ?_
  · obtain ⟨j, t, ht⟩ := exists_appTop_π_eq_of_isLimit D _ hc
      (V.topIso.inv (X.presheaf.map (homOfLE le_top).op r))
    refine ⟨j, ⟨(r, t), ?_⟩, rfl⟩
    change X.presheaf.map (homOfLE le_top).op r = V.topIso.hom ((π.app j).appTop t)
    rw [← ht]
    exact (Iso.inv_hom_id_apply _ _).symm
  · have h₁ : ((π.app j).appTop ≫ V.topIso.hom) y.1.2 = 0 := by
      have hy' : X.presheaf.map (homOfLE le_top).op y.1.1 =
          ((π.app j).appTop ≫ V.topIso.hom) y.1.2 := y.2
      rw [← hy', show y.1.1 = 0 from hy, map_zero]
    have h₂ : (π.app j).appTop y.1.2 = 0 := by
      rw [CommRingCat.comp_apply] at h₁
      have := congr(V.topIso.inv $h₁)
      rwa [Iso.hom_inv_id_apply, map_zero] at this
    obtain ⟨j', f, hf⟩ := exists_appTop_map_eq_zero_of_isLimit D _ hc _ h₂
    refine ⟨j', f, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change (fiberProductMap π f ≫ (fiberProductCone π j').fst) y = 0
      rw [fiberProductMap_fst]
      exact hy
    · change (fiberProductMap π f ≫ (fiberProductCone π j').snd) y = 0
      rw [fiberProductMap_snd]
      exact hf

/-- In the situation of `isColimitFiberProductCocone`, `Spec Γ(X, ⊤)` is the cofiltered limit of
the spectra of the finitely generated subrings of the fibre products containing `s j`. -/
noncomputable def isLimitSpecFiberProductCocone [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (hc : IsLimit (Cone.mk _ π))
    (s : ∀ j, Finset ((fiberProductSystem π).obj (op j))) :
    IsLimit (Scheme.Spec.mapCone (coneRightOpOfCocone
      (TauCeti.CommRingCat.FGSubringPair.cocone (s := s) (fiberProductCocone π)))) :=
  have : PreservesLimits Scheme.Spec.{u} := ΓSpec.adjunction.rightAdjoint_preservesLimits
  isLimitOfPreserves Scheme.Spec
    (isLimitConeRightOpOfCocone _ (isColimitFiberProductCocone π hc s))

end TauCeti.AlgebraicGeometry.Scheme
