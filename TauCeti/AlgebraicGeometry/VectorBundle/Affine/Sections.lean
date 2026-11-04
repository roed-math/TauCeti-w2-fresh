/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.Modules.Sections
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover

/-!
# Sections of a finite locally free sheaf over an affine open

Let `E` be a finite locally free sheaf on a scheme `X` and let `U` be an affine open of `X`. The
sections `Γ(E, U)` form a finitely generated projective `Γ(X, U)`-module: they are the global
sections of the restriction of `E` to the affine chart `Spec Γ(X, U) ⟶ X`, which is again finite
locally free (`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finite_projective_moduleSpecΓ`).

If `X` is flat over a commutative ring `R`, then `Γ(X, U)` is flat over `R`, hence so is
`Γ(E, U)`. This is the flatness of the coefficients on the members of an affine cover required by
cohomology and base change (`TauCeti.AlgebraicGeometry.Cohomology.CohomologyAndBaseChange`).

Conversely, a quasi-coherent sheaf whose sections over the members of an affine open cover are
finitely generated projective is finite locally free: on `Spec Γ(X, U)` it is the sheaf associated
with its sections over `U`
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_finite_projective_sections`).

## Main results

* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finite_projective_sections`: `Γ(E, U)` is a
  finitely generated projective `Γ(X, U)`-module for `U` affine.
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rank_fromSpec_apply`: the rank at a point of
  `U` is the rank of `Γ(E, U)` at the corresponding prime.
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.flat_sectionsBase`: if `X` is flat over `R`,
  then `Γ(E, U)` is a flat `R`-module for `U` affine.
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_finite_projective_sections`: a
  quasi-coherent sheaf with finitely generated projective sections over the members of an affine
  open cover is finite locally free.

## References

* [The Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
-/

public section

open CategoryTheory Opposite _root_.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

variable {X : Scheme.{u}} (E : FiniteLocallyFreeSheaf X) {U : X.Opens}

/-- The sections of an `𝒪_X`-module `M` over an affine open `U` are the global sections of its
pullback to `Spec Γ(X, U)`, as `Γ(X, U)`-modules. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.Modules.sectionsLinearEquivModuleSpecΓ
    (M : X.Modules) (hU : IsAffineOpen U) :
    Γ(M, U) ≃ₗ[Γ(X, U)] moduleSpecΓFunctor.obj ((Scheme.Modules.pullback hU.fromSpec).obj M) :=
  -- the pullback along the open immersion `hU.fromSpec` is the restriction
  (M.fromSpecSectionsEquiv hU).trans (moduleSpecΓFunctor.mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app M)).toLinearEquiv

/-- The sections of a finite locally free sheaf over an affine open `U` form a finitely generated
projective `Γ(X, U)`-module. -/
theorem finite_projective_sections (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ(E.obj, U) ∧ Module.Projective Γ(X, U) Γ(E.obj, U) := by
  obtain ⟨h₁, h₂⟩ := finite_projective_moduleSpecΓ
    ((FiniteLocallyFreeSheaf.pullback hU.fromSpec).obj E)
  rw [pullback_obj_obj] at h₁ h₂
  let e := E.obj.sectionsLinearEquivModuleSpecΓ hU
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

/-- The rank of a finite locally free sheaf at a point of an affine open `U` is the rank of its
sections over `U` at the corresponding prime of `Γ(X, U)`. -/
theorem rank_fromSpec_apply (hU : IsAffineOpen U) (y : Spec Γ(X, U)) :
    E.rank (hU.fromSpec y) = Module.rankAtStalk Γ(E.obj, U) y := by
  rw [← rank_pullback_apply, rank_apply_eq_rankAtStalk, pullback_obj_obj]
  exact congrFun (Module.rankAtStalk_eq_of_equiv (E.obj.sectionsLinearEquivModuleSpecΓ hU)).symm y

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

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]

/-- A quasi-coherent sheaf whose sections over an affine open `U` form a finitely generated
projective `Γ(X, U)`-module is finite locally free on `Spec Γ(X, U)`: there it is the sheaf
associated with these sections. -/
theorem isFiniteLocallyFree_pullback_fromSpec {U : X.Opens} (hU : IsAffineOpen U)
    [Module.Finite Γ(X, U) Γ(M, U)] [Module.Projective Γ(X, U) Γ(M, U)] :
    isFiniteLocallyFree (Spec Γ(X, U)) ((pullback hU.fromSpec).obj M) := by
  have : ((pullback hU.fromSpec).obj M).IsQuasicoherent := isQuasicoherent_pullback _ M
  -- The global sections on `Spec Γ(X, U)` are the sections of `M` over `U`.
  let e := M.sectionsLinearEquivModuleSpecΓ hU
  have := Module.Finite.equiv e
  have := Module.Projective.of_equiv' e
  exact (isFiniteLocallyFree _).prop_of_iso (asIso (fromTildeΓ _))
    ((isFiniteLocallyFree_tilde_iff _).mpr ⟨‹_›, ‹_›⟩)

/-- **Finite local freeness from sections over an affine cover.** A quasi-coherent sheaf whose
sections over each member `U i` of a cover of `X` by affine opens form a finitely generated
projective `Γ(X, U i)`-module is finite locally free. -/
theorem isFiniteLocallyFree_of_finite_projective_sections {ι : Type u} {U : ι → X.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) (hcov : iSup U = ⊤)
    [∀ i, Module.Finite Γ(X, U i) Γ(M, U i)] [∀ i, Module.Projective Γ(X, U i) Γ(M, U i)] :
    isFiniteLocallyFree X M := by
  refine (isFiniteLocallyFree_iff_forall_pullback (Cover.mkOfCovers ι (fun i ↦ Spec Γ(X, U i))
    (fun i ↦ (hU i).fromSpec) (fun x ↦ ?_) fun _ ↦ inferInstance) M).mpr
    fun (i : ι) ↦ ?_
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
    obtain ⟨y, hy⟩ : x ∈ Set.range (hU i).fromSpec := by rwa [(hU i).range_fromSpec]
    exact ⟨i, y, hy⟩
  · exact isFiniteLocallyFree_pullback_fromSpec M (hU i)

end AlgebraicGeometry.Scheme.Modules
