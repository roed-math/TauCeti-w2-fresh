/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.PullbackSections
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange

/-!
# Affine base change of the sections of a pulled-back graded algebra

Let `g : X ⟶ Y` be a morphism of schemes, `A = ⨁ₙ Aₙ` a graded quasicoherent algebra on `Y`, and
`U` an affine open of `Y`, `V` an affine open of `X` with `V ≤ g⁻¹ U`. Pulling back sections
(`GradedQuasicoherentAlgebra.pullbackGradedSections`) exhibits the graded ring of sections of
`g^* A` over `V` as the base change

`⨁ n, Γ(g^* Aₙ, V) = Γ(X, V) ⊗[Γ(Y, U)] ⨁ n, Γ(Aₙ, U)`

(`GradedQuasicoherentAlgebra.isBaseChange_pullbackGradedSections`), degree by degree by the affine
base change of quasicoherent sections `Scheme.Hom.isBaseChange_pullbackSectionsLE`. Consequently
the chart `Proj (⨁ n, Γ(g^* Aₙ, V))` of the relative `Proj` of `g^* A` is the base change of the
chart `Proj (⨁ n, Γ(Aₙ, U))` of the relative `Proj` of `A` along `Spec Γ(X, V) ⟶ Spec Γ(Y, U)`
(`GradedQuasicoherentAlgebra.isPullback_proj_pullbackGradedSections`). These cartesian squares
are the charts of the base change of the relative `Proj`.

## Main declarations

* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.isBaseChange_pullbackGradedSections`:
  the graded sections of `g^* A` over `V` are the base change of those of `A` over `U`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.isPullback_proj_pullbackGradedSections`:
  the corresponding square of projective spectra is cartesian.

## References

* [The Stacks Project, Lemma 27.16.10](https://stacks.math.columbia.edu/tag/01O3)
-/

public section

open CategoryTheory DirectSum
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (A : GradedQuasicoherentAlgebra Y) {U : Y.Opens}
  {V : X.Opens} (hV : V ≤ g ⁻¹ᵁ U)

/-- The `Γ(Y, U)`-algebra structure on the sections `⨁ n, Γ(g^* Aₙ, V)` of `g^* A` over an open
`V ≤ g⁻¹ U`, through the map of functions `g.appLE U V hV : Γ(Y, U) → Γ(X, V)`. -/
abbrev algebraPullbackGradedSections :
    Algebra Γ(Y, U) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) :=
  ((algebraMap Γ(X, V) (⨁ n, Γ(((pullback g).obj A).obj.X n, V))).comp
    (g.appLE U V hV).hom).toAlgebra

/-- Pullback of sections is a homomorphism of `Γ(Y, U)`-algebras. -/
theorem pullbackGradedSectionsGradedHom_algebraMap (r : Γ(Y, U)) :
    let := A.algebraPullbackGradedSections g hV
    A.pullbackGradedSectionsGradedHom g hV (algebraMap Γ(Y, U) (⨁ n, Γ(A.obj.X n, U)) r) =
      algebraMap Γ(Y, U) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) r := by
  intro
  rw [pullbackGradedSectionsGradedHom_apply, pullbackGradedSections_algebraMap,
    RingHom.algebraMap_toAlgebra, RingHom.comp_apply]

/-- The algebra structures of `⨁ n, Γ(g^* Aₙ, V)` over `Γ(Y, U)` and `Γ(X, V)` form a scalar
tower over `g.appLE U V hV`. -/
theorem isScalarTower_pullbackGradedSections :
    let := (g.appLE U V hV).hom.toAlgebra
    let := A.algebraPullbackGradedSections g hV
    IsScalarTower Γ(Y, U) Γ(X, V) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) := by
  intro _ _
  -- `algebraPullbackGradedSections` is defined by this composite of algebra maps
  exact .of_algebraMap_eq' rfl

/-- Pulling back sections of a quasicoherent module `M` and transporting them along an equation
`g^* M = N` is a base change. -/
private lemma isBaseChange_eqToHom_app_pullbackSectionsLE (M : Y.Modules) [M.IsQuasicoherent]
    {N : X.Modules} (h : (Scheme.Modules.pullback g).obj M = N) (hU : IsAffineOpen U)
    (hV' : IsAffineOpen V) :
    letI := (g.appLE U V hV).hom.toAlgebra
    ∀ [Module Γ(Y, U) Γ(N, V)] [IsScalarTower Γ(Y, U) Γ(X, V) Γ(N, V)]
      (f : Γ(M, U) →ₗ[Γ(Y, U)] Γ(N, V)),
      (∀ s, f s = (eqToHom h).app V (g.pullbackSectionsLE M U V hV s)) →
        IsBaseChange Γ(X, V) f := by
  subst h
  intro _ _ f hf
  exact g.isBaseChange_pullbackSectionsLE M hV hU hV' f hf

/-- **Affine base change of graded sections.** For affine opens `U` of `Y` and `V ≤ g⁻¹ U` of `X`,
pulling back sections exhibits `⨁ n, Γ(g^* Aₙ, V)` as the base change
`Γ(X, V) ⊗[Γ(Y, U)] ⨁ n, Γ(Aₙ, U)` along `g.appLE U V hV`. -/
theorem isBaseChange_pullbackGradedSections (hU : IsAffineOpen U) (hV' : IsAffineOpen V) :
    let := (g.appLE U V hV).hom.toAlgebra
    let := A.algebraPullbackGradedSections g hV
    have := A.isScalarTower_pullbackGradedSections g hV
    IsBaseChange Γ(X, V)
      (AlgHom.mk (R := Γ(Y, U)) (A.pullbackGradedSectionsGradedHom g hV).toRingHom
        (A.pullbackGradedSectionsGradedHom_algebraMap g hV)).toLinearMap := by
  intro _ _ _
  obtain ⟨e, he⟩ : ∃ e : Γ(X, V) ⊗[Γ(Y, U)] (⨁ n, Γ(A.obj.X n, U)) ≃ₗ[Γ(X, V)]
      ⨁ n, Γ(((pullback g).obj A).obj.X n, V),
        ∀ x, e (1 ⊗ₜ x) = A.pullbackGradedSections g hV x := by
    -- degree by degree, through the `Γ(Y, U)`-module structures along `g.appLE U V hV`
    let (n : ℕ) : Module Γ(Y, U) Γ(((pullback g).obj A).obj.X n, V) :=
      Module.compHom _ (algebraMap Γ(Y, U) Γ(X, V))
    have (n : ℕ) : IsScalarTower Γ(Y, U) Γ(X, V) Γ(((pullback g).obj A).obj.X n, V) :=
      IsScalarTower.of_compHom _ _ _
    let ε (n : ℕ) : Γ(A.obj.X n, U) →ₗ[Γ(Y, U)] Γ(((pullback g).obj A).obj.X n, V) :=
      { toFun := A.pullbackComponentSections g hV n
        map_add' := map_add _
        map_smul' r s := (A.pullbackComponentSections g hV n).map_smulₛₗ r s }
    have hε := IsBaseChange.directSum fun n ↦
      isBaseChange_eqToHom_app_pullbackSectionsLE g hV (A.obj.X n)
        (pullback_obj_obj_X g A n).symm hU hV' (ε n)
        (A.pullbackComponentSections_apply g hV n)
    have h (x : ⨁ n, Γ(A.obj.X n, U)) : DirectSum.lmap ε x = A.pullbackGradedSections g hV x := by
      induction x using DirectSum.induction_on with
      | zero => rw [map_zero, map_zero]
      | of n x => rw [DirectSum.lmap_of, pullbackGradedSections_of]; rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    exact ⟨hε.equiv, fun x ↦ (hε.equiv_tmul 1 x).trans ((one_smul _ _).trans (h x))⟩
  exact IsBaseChange.of_equiv e fun x ↦
    (he x).trans (A.pullbackGradedSectionsGradedHom_apply g hV x).symm

/-- For affine opens `U` of `Y` and `V ≤ g⁻¹ U` of `X`, the irrelevant ideal of the sections of
`g^* A` over `V` is contained in the ideal generated by the pullback of the irrelevant ideal of the
sections of `A` over `U`, so that `Proj.map` gives
`Proj (⨁ n, Γ(g^* Aₙ, V)) ⟶ Proj (⨁ n, Γ(Aₙ, U))`. -/
theorem irrelevant_le_map_pullbackGradedSectionsGradedHom (hU : IsAffineOpen U)
    (hV' : IsAffineOpen V) :
    HomogeneousIdeal.irrelevant (((pullback g).obj A).obj.gradedSectionsGrading V) ≤
      (HomogeneousIdeal.irrelevant (A.obj.gradedSectionsGrading U)).map
        (A.pullbackGradedSectionsGradedHom g hV) := by
  let := (g.appLE U V hV).hom.toAlgebra
  let := A.algebraPullbackGradedSections g hV
  have := A.isScalarTower_pullbackGradedSections g hV
  exact HomogeneousIdeal.irrelevant_le_map_of_isBaseChange _ _ _
    (A.isBaseChange_pullbackGradedSections g hV hU hV')

/-- **The charts of the relative `Proj` of a pulled-back graded algebra.** For affine opens `U` of
`Y` and `V ≤ g⁻¹ U` of `X`, the square

`Proj (⨁ n, Γ(g^* Aₙ, V)) ⟶ Proj (⨁ n, Γ(Aₙ, U))`, `Spec Γ(X, V) ⟶ Spec Γ(Y, U)`

formed by pullback of sections and the coefficient projections is cartesian. -/
theorem isPullback_proj_pullbackGradedSections (hU : IsAffineOpen U) (hV' : IsAffineOpen V) :
    IsPullback (Proj.map (A.pullbackGradedSectionsGradedHom g hV)
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV hU hV'))
      (Proj.toSpecCoeff (((pullback g).obj A).obj.gradedSectionsGrading V))
      (Proj.toSpecCoeff (A.obj.gradedSectionsGrading U)) (Spec.map (g.appLE U V hV)) := by
  let := (g.appLE U V hV).hom.toAlgebra
  let := A.algebraPullbackGradedSections g hV
  have := A.isScalarTower_pullbackGradedSections g hV
  exact Proj.isPullback_map_of_isBaseChange _ _ _
    (A.isBaseChange_pullbackGradedSections g hV hU hV')

end GradedQuasicoherentAlgebra

end

end TauCeti.AlgebraicGeometry
