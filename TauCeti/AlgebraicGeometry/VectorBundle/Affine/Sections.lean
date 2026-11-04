/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.Modules.Sections
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic

/-!
# Sections of a finite locally free sheaf over an affine open

Let `E` be a finite locally free sheaf on a scheme `X` and let `U` be an affine open of `X`. The
sections `Γ(E, U)` form a finitely generated projective `Γ(X, U)`-module: they are the global
sections of the restriction of `E` to the affine chart `Spec Γ(X, U) ⟶ X`, which is again finite
locally free (`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finite_projective_moduleSpecΓ`).

If `X` is flat over a commutative ring `R`, then `Γ(X, U)` is flat over `R`, hence so is
`Γ(E, U)`. This is the flatness of the coefficients on the members of an affine cover required by
cohomology and base change (`TauCeti.AlgebraicGeometry.Cohomology.CohomologyAndBaseChange`).

## Main results

* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finite_projective_sections`: `Γ(E, U)` is a
  finitely generated projective `Γ(X, U)`-module for `U` affine.
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.flat_sectionsBase`: if `X` is flat over `R`,
  then `Γ(E, U)` is a flat `R`-module for `U` affine.

## References

* [The Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
-/

public section

open CategoryTheory Opposite _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

universe u

variable {X : Scheme.{u}} (E : FiniteLocallyFreeSheaf X) {U : X.Opens}

/-- The sections of a finite locally free sheaf over an affine open `U` form a finitely generated
projective `Γ(X, U)`-module. -/
theorem finite_projective_sections (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ(E.obj, U) ∧ Module.Projective Γ(X, U) Γ(E.obj, U) := by
  obtain ⟨h₁, h₂⟩ := finite_projective_moduleSpecΓ
    ((FiniteLocallyFreeSheaf.pullback hU.fromSpec).obj E)
  rw [pullback_obj_obj] at h₁ h₂
  -- Sections over `U` are global sections of the restriction to `Spec Γ(X, U)`, which is the
  -- pullback along the open immersion `hU.fromSpec`.
  let e : Γ(E.obj, U) ≃ₗ[Γ(X, U)]
      moduleSpecΓFunctor.obj ((Scheme.Modules.pullback hU.fromSpec).obj E.obj) :=
    (E.obj.fromSpecSectionsEquiv hU).trans (moduleSpecΓFunctor.mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app E.obj)).toLinearEquiv
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))]

open Scheme.Modules in
/-- If `X` is flat over `R`, then the sections of a finite locally free sheaf over an affine open
`U` form a flat `R`-module, for the action of `R` through `Scheme.baseRingToStructurePresheaf`. -/
theorem flat_sectionsBase [Flat (X ↘ Spec (.of R))] (hU : IsAffineOpen U) :
    Module.Flat R (((sectionsBasePresheafFunctor R).obj E.obj).obj (op U)) := by
  let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  let : Module R Γ(E.obj, U) := sectionsBaseModule R E.obj U
  have : IsScalarTower R Γ(X, U) Γ(E.obj, U) := .of_algebraMap_smul fun _ _ ↦ rfl
  -- The base ring maps to `Γ(X, U)` through `R ≅ Γ(Spec R, ⊤)` and `appLE`, which is flat.
  have : Module.Flat R Γ(X, U) := by
    change ((X.baseRingToStructurePresheaf R).app (op U)).hom.Flat
    rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE]
    exact .comp (.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv))
      ((X ↘ Spec (.of R)).flat_appLE (isAffineOpen_top _) hU le_top)
  have := (E.finite_projective_sections hU).2
  exact Module.Flat.trans R Γ(X, U) Γ(E.obj, U)

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
