/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Normalization
public import TauCeti.AlgebraicGeometry.IdealSheaf.Conductor
public import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
public import TauCeti.RingTheory.Japanese

/-!
# Finiteness of the relative normalization

Let `f : X ⟶ Y` be quasi-compact and quasi-separated. Over an affine open `U` of `Y`, the
normalization of `Y` in `X` is the spectrum of the integral closure of `Γ(Y, U)` in
`Γ(X, f ⁻¹ᵁ U)`. Since the normalization is an affine morphism, it is finite over `Y` exactly when
each of these integral closures is a finite `Γ(Y, U)`-module.

For an integral scheme `Y` and a finite extension `L` of its function field `k(Y)`, consider the
normalization of `Y` in `Spec L`, along `Spec L ⟶ Spec k(Y) ⟶ Y`. Over a nonempty affine open `U`,
the sections of `Spec L` are `L`, and `k(Y)` is the fraction field of `Γ(Y, U)`. So this
normalization is finite when the rings `Γ(Y, U)` are Japanese; for instance when they are Nagata,
as a Nagata domain is Japanese. For `L = k(Y)` itself, the normalization of `Y` in its function
field is finite exactly when the rings `Γ(Y, U)` are N-1. This supplies the finiteness hypothesis
of resolution of curves by normalization
(`TauCeti.AlgebraicGeometry.isRegular_normalization_of_field`) for curves whose affine opens have
Japanese rings.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isFinite_fromNormalization_iff`: the normalization of `Y` in `X` is
  finite over `Y` if and only if, over every affine open `U` of `Y`, the integral closure of
  `Γ(Y, U)` in `Γ(X, f ⁻¹ᵁ U)` is a finite `Γ(Y, U)`-module.
* `AlgebraicGeometry.Scheme.Hom.isFinite_fromNormalization_of_iSup_eq_top`: it suffices to check
  this over the members of an affine open cover of `Y`.
* `AlgebraicGeometry.Scheme.Hom.normalizationObjAlgEquiv`: over an affine open `U`, the sections
  of the normalization are the integral closure, as a `Γ(Y, U)`-algebra.
* `AlgebraicGeometry.Scheme.Hom.conductor_fromNormalization_ideal`: over an affine open, the
  conductor of a finite normalization is that of the integral closure.
* `TauCeti.AlgebraicGeometry.isFinite_fromNormalization_fromSpecStalk_genericPoint_iff`: the
  normalization of an integral scheme in its function field is finite if and only if the ring of
  sections of every nonempty affine open is N-1.
* `TauCeti.AlgebraicGeometry.isFinite_fromNormalization_of_isJapanese`: if the ring of sections of
  every nonempty affine open of an integral scheme `Y` is Japanese, the normalization of `Y` in a
  finite extension of its function field is finite over `Y` (Stacks, Lemma 29.54.14 (0AVK), with
  the hypothesis on every affine open).

## References

* [Stacks Project, Lemma 29.54.14](https://stacks.math.columbia.edu/tag/0AVK).
* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H), for the relative
  normalization over affine opens.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- Over an affine open `U` of `Y`, the map on sections of the normalization of `Y` in `X` is
finite if and only if the integral closure of `Γ(Y, U)` in `Γ(X, f ⁻¹ᵁ U)` is a finite
`Γ(Y, U)`-module. -/
theorem finite_fromNormalization_app_iff {U : Y.Opens} (hU : IsAffineOpen U) :
    (f.fromNormalization.app U).hom.Finite ↔
      letI := (f.app U).hom.toAlgebra
      Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
  let := (f.app U).hom.toAlgebra
  -- Over an affine open `U`, the map on sections is the algebra map to the integral closure,
  -- followed by the isomorphism `normalizationObjIso`.
  rw [fromNormalization_app _ hU, CommRingCat.hom_comp,
    RingHom.finite_respectsIso.cancel_right_isIso, CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap

/-- The normalization of `Y` in `X`, along `f`, is finite over `Y` if and only if, over every affine
open `U` of `Y`, the integral closure of `Γ(Y, U)` in `Γ(X, f ⁻¹ᵁ U)` is a finite
`Γ(Y, U)`-module. -/
theorem isFinite_fromNormalization_iff :
    IsFinite f.fromNormalization ↔ ∀ U : Y.Opens, IsAffineOpen U →
      letI := (f.app U).hom.toAlgebra
      Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
  refine ⟨fun _ U hU ↦ (f.finite_fromNormalization_app_iff hU).mp
    (f.fromNormalization.finite_app U hU), fun h ↦ ?_⟩
  exact { finite_app U hU := (f.finite_fromNormalization_app_iff hU).mpr (h U hU) }

/-- **Finiteness of the normalization is local on the target.** If `Y` is covered by affine opens
`Uᵢ` over which the integral closure of `Γ(Y, Uᵢ)` in `Γ(X, f ⁻¹ᵁ Uᵢ)` is a finite
`Γ(Y, Uᵢ)`-module, then the normalization of `Y` in `X` is finite over `Y`. -/
theorem isFinite_fromNormalization_of_iSup_eq_top {ι : Type*} (U : ι → Y.affineOpens)
    (hU : ⨆ i, (U i : Y.Opens) = ⊤)
    (h : ∀ i, letI := (f.app (U i)).hom.toAlgebra
      Module.Finite Γ(Y, U i) (integralClosure Γ(Y, U i) Γ(X, f ⁻¹ᵁ U i))) :
    IsFinite f.fromNormalization := by
  -- The affine property of finite morphisms has to be named for instance search to find it.
  observe hP : HasAffineProperty @IsFinite.{u}
    (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom)
  have : IsZariskiLocalAtTarget @IsFinite.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hP
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite) (fun i ↦ (U i).1) hU fun i ↦ ?_
  have : IsAffine (U i).1.toScheme := (U i).2
  rw [@HasAffineProperty.iff_of_isAffine _ _ hP]
  refine ⟨(U i).2.preimage _, ?_⟩
  -- Over `U i`, the restriction is the map on sections over `U i`, up to an isomorphism.
  rw [morphismRestrict_appTop]
  have hi : (U i).1.ι ''ᵁ ⊤ = U i := Scheme.Opens.ι_image_top _
  have hUi : IsAffineOpen ((U i).1.ι ''ᵁ ⊤) := by
    rw [hi]
    exact (U i).2
  refine RingHom.Finite.comp (.of_surjective _ (asIso _).commRingCatIsoToRingEquiv.surjective)
    ((f.finite_fromNormalization_app_iff hUi).mpr ?_)
  convert h i using 0
  rw [hi]

/-- Over an affine open `U` of `Y`, the sections of the normalization of `Y` in `X` are the
integral closure of `Γ(Y, U)` in `Γ(X, f ⁻¹ᵁ U)`, as a `Γ(Y, U)`-algebra. -/
noncomputable def normalizationObjAlgEquiv (U : Y.affineOpens) :
    letI := (f.app U).hom.toAlgebra
    letI := (f.fromNormalization.app U).hom.toAlgebra
    Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) ≃ₐ[Γ(Y, U)]
      integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
  letI := (f.app U).hom.toAlgebra
  letI := (f.fromNormalization.app U).hom.toAlgebra
  { (f.normalizationObjIso U.2).commRingCatIsoToRingEquiv with
    commutes' c := by
      change (f.fromNormalization.app U ≫ (f.normalizationObjIso U.2).hom) c = _
      rw [f.fromNormalization_app_assoc U.2, Iso.inv_hom_id, Category.comp_id]
      rfl }

/-- `normalizationObjAlgEquiv` is Mathlib's `normalizationObjIso`. -/
theorem normalizationObjAlgEquiv_apply (U : Y.affineOpens)
    (x : Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U)) :
    f.normalizationObjAlgEquiv U x = (f.normalizationObjIso U.2).hom x :=
  (rfl)

/-- Over an affine open `U` of `Y`, the conductor of a finite normalization of `Y` in `X` is the
conductor of the integral closure of `Γ(Y, U)` in `Γ(X, f ⁻¹ᵁ U)`. -/
theorem conductor_fromNormalization_ideal [IsFinite f.fromNormalization] (U : Y.affineOpens) :
    f.fromNormalization.conductor.ideal U =
      letI := (f.app U).hom.toAlgebra
      TauCeti.Algebra.conductor Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) :=
  letI := (f.app U).hom.toAlgebra
  letI := (f.fromNormalization.app U).hom.toAlgebra
  (f.fromNormalization.conductor_ideal U).trans
    (TauCeti.Algebra.conductor_congr (f.normalizationObjAlgEquiv U))

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

variable {Y : Scheme.{u}} [IsIntegral Y]

/-- **Finite normalization and N-1 rings.** The normalization of an integral scheme `Y` in its
function field, along `Spec k(Y) ⟶ Y`, is finite over `Y` if and only if the ring of sections of
every nonempty affine open of `Y` is N-1: over such an open `U` the normalization is the spectrum
of the integral closure of `Γ(Y, U)` in its fraction field `k(Y)`. -/
theorem isFinite_fromNormalization_fromSpecStalk_genericPoint_iff :
    IsFinite (Y.fromSpecStalk (genericPoint Y)).fromNormalization ↔
      ∀ U : Y.Opens, IsAffineOpen U → Nonempty U → Ring.IsN1 Γ(Y, U) := by
  set f := Y.fromSpecStalk (genericPoint Y)
  rw [f.isFinite_fromNormalization_iff]
  refine forall₂_congr fun U hU ↦ ?_
  let := (f.app U).hom.toAlgebra
  by_cases hη : genericPoint Y ∈ U
  · have : Nonempty U := ⟨⟨_, hη⟩⟩
    have := Scheme.isFractionRing_app_fromSpecStalk_genericPoint hU
    exact ⟨fun _ _ ↦ .of_finite_integralClosure Γ(Spec Y.functionField, f ⁻¹ᵁ U),
      fun h ↦ (h ‹_›).finite_integralClosure _⟩
  · -- Over an open missing the generic point, the sections of `Spec k(Y)` are the zero ring.
    have := Scheme.subsingleton_preimage_of_genericPoint_notMem f hη
    refine ⟨fun _ hU ↦ (hη ?_).elim, fun _ ↦ inferInstance⟩
    obtain ⟨⟨y, hy⟩⟩ := hU
    exact (genericPoint_specializes y).mem_open U.isOpen hy

variable (L : Type u) [Field L] [Algebra Y.functionField L]

/-- **Finite normalization in a finite extension of the function field.** Let `Y` be an integral
scheme such that the ring of sections of every nonempty affine open is Japanese, for instance
Nagata. Then for every finite extension `L` of the function field `k(Y)`, the normalization of `Y`
in `Spec L`, along `Spec L ⟶ Spec k(Y) ⟶ Y`, is finite over `Y`. Stacks, Lemma 29.54.14 (0AVK),
with the hypothesis imposed on every nonempty affine open. -/
@[stacks 0AVK "The Japanese hypothesis is imposed on every nonempty affine open."]
theorem isFinite_fromNormalization_of_isJapanese
    (hY : ∀ U : Y.Opens, IsAffineOpen U → ∀ [Nonempty U], Ring.IsJapanese Γ(Y, U))
    [FiniteDimensional Y.functionField L] :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField L)) ≫
      Y.fromSpecStalk (genericPoint Y)).fromNormalization := by
  set f := Spec.map (CommRingCat.ofHom (algebraMap Y.functionField L)) ≫
    Y.fromSpecStalk (genericPoint Y)
  refine f.isFinite_fromNormalization_iff.mpr fun U hU ↦ ?_
  let := (f.app U).hom.toAlgebra
  by_cases hη : genericPoint Y ∈ U
  · have : Nonempty U := ⟨⟨_, hη⟩⟩
    -- Over `U`, the integral closure is that of `Γ(Y, U)` in `L`, which is finite as
    -- `Γ(Y, U)` is a Japanese domain with fraction field `k(Y)`.
    let : Algebra Γ(Y, U) L :=
      ((algebraMap Y.functionField L).comp (algebraMap Γ(Y, U) Y.functionField)).toAlgebra
    have : IsScalarTower Γ(Y, U) Y.functionField L := .of_algebraMap_eq' rfl
    have := functionField_isFractionRing_of_isAffineOpen Y U hU
    have := hY U hU
    have := Ring.IsJapanese.finite_integralClosure (R := Γ(Y, U)) Y.functionField L
    exact .equiv (Scheme.algEquivAppPreimageSpecExtension L).mapIntegralClosure.toLinearEquiv
  · -- Over an open missing the generic point, the sections of `Spec L` are the zero ring.
    have := Scheme.subsingleton_preimage_of_genericPoint_notMem f hη
    infer_instance

end TauCeti.AlgebraicGeometry
