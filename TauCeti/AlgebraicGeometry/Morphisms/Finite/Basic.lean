/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Sections of finite morphisms

For a finite morphism `f : X ⟶ Spec R`, the global sections `Γ(X, ⊤)` form a finite
`R`-module. `AlgebraicGeometry.Scheme.Hom.moduleFinite_appTop` states this for an existing
`R`-algebra structure compatible with the map of global sections. It transports Mathlib's
`Scheme.Hom.finite_appTop` across the canonical isomorphism `R ≅ Γ(Spec R, ⊤)`.

This finiteness is used to compute the rank of a finite morphism over a field as the dimension
of its global sections.

If `g : Y ⟶ S` is moreover flat and locally of finite presentation (finite locally free), its
sections `Γ(Y, g⁻¹ U)` over an affine open `U` of `S` form a projective `Γ(S, U)`-module
(`AlgebraicGeometry.Scheme.Hom.projective_app`).

A morphism whose restriction over an open `V` is finite has, around every point of `V`, an affine
open `U` with affine preimage and `Γ(Y, U) → Γ(X, f⁻¹ U)` finite
(`AlgebraicGeometry.Scheme.Hom.exists_isAffineOpen_finite_app_of_isFinite_morphismRestrict`).

Finite, flat and locally finitely presented morphisms each respect isomorphisms
(`TauCeti.isFinite_respectsIso`, `TauCeti.flat_respectsIso` and
`TauCeti.locallyOfFinitePresentation_respectsIso`).
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- A finite morphism to the spectrum of a commutative ring has module-finite global sections,
for any `R`-algebra structure on `Γ(X, ⊤)` given by the map of global sections. -/
theorem Scheme.Hom.moduleFinite_appTop {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsFinite f] [Algebra R Γ(X, ⊤)]
    (hf : algebraMap R Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom) :
    Module.Finite R Γ(X, ⊤) := by
  rw [← RingHom.finite_algebraMap, hf, CommRingCat.hom_comp]
  exact f.finite_appTop.comp (RingHom.Finite.of_surjective _
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective)

/-- The sections of a finite, flat, locally finitely presented morphism `g : Y ⟶ S` over an affine
open `U` of `S` form a projective module over `Γ(S, U)`. -/
theorem Scheme.Hom.projective_app {Y S : Scheme.{u}} (g : Y ⟶ S) [IsFinite g] [Flat g]
    [LocallyOfFinitePresentation g] (U : S.affineOpens) :
    letI := (g.app U).hom.toAlgebra
    Module.Projective Γ(S, U) Γ(Y, g ⁻¹ᵁ U) := by
  have hflat := HasRingHomProperty.appLE @Flat g inferInstance U ⟨_, U.2.preimage g⟩ le_rfl
  have hfp := HasRingHomProperty.appLE @LocallyOfFinitePresentation g inferInstance U
    ⟨_, U.2.preimage g⟩ le_rfl
  rw [Scheme.Hom.appLE_eq_app] at hflat hfp
  have hfin := g.finite_app U U.2
  algebraize [(g.app U).hom]
  have := Module.FinitePresentation.of_finite_of_finitePresentation (R := Γ(S, U))
    (S := Γ(Y, g ⁻¹ᵁ U))
  exact Module.Flat.projective_of_finitePresentation

/-- **A finite restriction is finite over an affine neighbourhood.** If `f ∣_ V` is finite and
`y ∈ V`, then `y` has an affine open neighbourhood `U ⊆ V` whose preimage is affine, with
`Γ(Y, U) → Γ(X, f⁻¹ U)` finite. -/
theorem Scheme.Hom.exists_isAffineOpen_finite_app_of_isFinite_morphismRestrict {X Y : Scheme.{u}}
    (f : X ⟶ Y) {V : Y.Opens} [IsFinite (f ∣_ V)] {y : Y} (hy : y ∈ V) :
    ∃ U : Y.Opens, U ≤ V ∧ IsAffineOpen U ∧ IsAffineOpen (f ⁻¹ᵁ U) ∧ (f.app U).hom.Finite ∧
      y ∈ U := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    (V : Scheme).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ⟨y, hy⟩) isOpen_univ
  have hW' := (IsAffineHom.isAffine_preimage (f := f ∣_ V) W hW).image_of_isOpenImmersion
    (f ⁻¹ᵁ V).ι
  rw [image_morphismRestrict_preimage] at hW'
  have hfin := (f ∣_ V).finite_app W hW
  rw [morphismRestrict_app'] at hfin
  refine ⟨V.ι ''ᵁ W, V.ι_image_le W, hW.image_of_isOpenImmersion _, hW', ?_,
    V.ι.apply_mem_image_iff.mpr hyW⟩
  rw [← f.appLE_eq_app]
  exact (f.appLE_congr _ rfl (image_morphismRestrict_preimage f V W) fun φ ↦ φ.hom.Finite).mp hfin

end AlgebraicGeometry

namespace TauCeti

open AlgebraicGeometry

universe u

/-- Finite morphisms of schemes respect isomorphisms. -/
instance isFinite_respectsIso :
    MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) ↦ inferInstance)

/-- Flat morphisms of schemes respect isomorphisms. -/
instance flat_respectsIso :
    MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) ↦ inferInstance)

/-- Morphisms of schemes locally of finite presentation respect isomorphisms. -/
instance locallyOfFinitePresentation_respectsIso :
    MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) ↦ inferInstance)

end TauCeti
