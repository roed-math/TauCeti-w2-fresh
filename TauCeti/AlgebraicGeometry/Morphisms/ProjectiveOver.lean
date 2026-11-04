/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation
public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Affine
public import TauCeti.AlgebraicGeometry.Morphisms.Projective
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

/-!
# Projective schemes over a ring are projective morphisms

A scheme `X` over `Spec R` is projective over `R` in the sense of
`AlgebraicGeometry.Scheme.IsProjectiveOver` if it is a closed subscheme over `R` of
`Proj (Sym_R M)` for a finite `R`-module `M`. This file shows that then `X ⟶ Spec R` is a
projective morphism (`TauCeti.AlgebraicGeometry.IsProjective`).

The identification `M ≅ Γ(M~, Spec R)`, semilinear over `R ≅ Γ(Spec R, Spec R)`, induces an
isomorphism `Proj (Sym Γ(M~, Spec R)) ≅ Proj (Sym_R M)` over `Spec R`
(`TauCeti.AlgebraicGeometry.projSymmetricAlgebraTildeIso`). The left side is the projective bundle
`ℙ(M~)` (`TauCeti.AlgebraicGeometry.relativeProjGradedSymmetricAlgebraIso`), which is projective
over `Spec R` because `M~` is of finite type.

## Main results

* `TauCeti.AlgebraicGeometry.projSymmetricAlgebraTildeIso`: `Proj (Sym Γ(M~, Spec R))` is
  `Proj (Sym_R M)`, over `Spec R` (`projSymmetricAlgebraTildeIso_hom_projToSpec`);
* `AlgebraicGeometry.Scheme.IsProjectiveOver.isProjective`: a scheme projective over `R` is
  projective over `Spec R`.
-/

public section

open CategoryTheory Opposite AlgebraicGeometry TauCeti.SymmetricAlgebra

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- The inverse of the identification `M ≅ Γ(M~, Spec R)` (`tildeToOpenₛₗ M ⊤`), semilinear over
`Γ(Spec R, Spec R) ≅ R`. -/
def tildeToOpenTopInvₛₗ :
    PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (op ⊤) →ₛₗ[
      (Scheme.ΓSpecIso R).hom.hom] M where
  toFun n := inv (tilde.toOpen M ⊤) n
  map_add' := (inv (tilde.toOpen M ⊤)).hom.map_add
  map_smul' s n := by
    obtain ⟨m, rfl⟩ := (ConcreteCategory.bijective_of_isIso (tilde.toOpen M ⊤)).2 n
    obtain ⟨r, rfl⟩ : ∃ r, (Scheme.ΓSpecIso R).inv.hom r = s :=
      ⟨(Scheme.ΓSpecIso R).hom.hom s, by simp⟩
    -- The scalar action of `Γ(Spec R, ⊤)` through `R → Γ(Spec R, ⊤)` is the `R`-module structure
    -- of the global sections in which `tilde.toOpen` is linear.
    change inv (tilde.toOpen M ⊤) (r • tilde.toOpen M ⊤ m) = _
    rw [← (tilde.toOpen M ⊤).hom.map_smul r m]
    simp

@[simp]
theorem tildeToOpenTopInvₛₗ_apply
    (n : PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (op ⊤)) :
    tildeToOpenTopInvₛₗ M n = inv (tilde.toOpen M ⊤) n :=
  (rfl)

/-- The map `Sym_R M → Sym Γ(M~, Spec R)` induced by `M ≅ Γ(M~, Spec R)`, as a graded ring
homomorphism. -/
def symmetricAlgebraTildeGradedHom :
    homogeneousSubmodule R M →+*ᵍ homogeneousSubmodule Γ(Spec R, ⊤)
      (PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (op ⊤)) where
  toRingHom := _root_.SymmetricAlgebra.mapₛₗ (tildeToOpenₛₗ M ⊤)
  map_mem := mapₛₗ_mem_homogeneousSubmodule _

/-- The inverse of `symmetricAlgebraTildeGradedHom`, as a graded ring homomorphism. -/
def symmetricAlgebraTildeGradedHomInv :
    homogeneousSubmodule Γ(Spec R, ⊤)
      (PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (op ⊤)) →+*ᵍ
      homogeneousSubmodule R M where
  toRingHom := _root_.SymmetricAlgebra.mapₛₗ (tildeToOpenTopInvₛₗ M)
  map_mem := mapₛₗ_mem_homogeneousSubmodule _

/-- The projective spectrum of the symmetric algebra of the global sections of `M~` is the
projective spectrum `Proj (Sym_R M)`. -/
def projSymmetricAlgebraTildeIso :
    Proj (homogeneousSubmodule Γ(Spec R, ⊤)
      (PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (op ⊤))) ≅
      Proj (homogeneousSubmodule R M) :=
  Proj.mapIso (symmetricAlgebraTildeGradedHom M) (symmetricAlgebraTildeGradedHomInv M)
    (fun x ↦ by
      have h := _root_.SymmetricAlgebra.mapₛₗ_comp_mapₛₗ (tildeToOpenTopInvₛₗ M)
        (tildeToOpenₛₗ M ⊤) LinearMap.id (fun s ↦ by simp) fun n ↦ by
          rw [tildeToOpenₛₗ_apply, tildeToOpenTopInvₛₗ_apply, LinearMap.id_apply]
          exact ConcreteCategory.congr_hom (IsIso.inv_hom_id (tilde.toOpen M ⊤)) n
      rw [_root_.SymmetricAlgebra.mapₛₗ_eq_id (fun _ ↦ rfl) (fun _ ↦ rfl)] at h
      exact RingHom.congr_fun h x)
    (fun x ↦ by
      have h := _root_.SymmetricAlgebra.mapₛₗ_comp_mapₛₗ (tildeToOpenₛₗ M ⊤)
        (tildeToOpenTopInvₛₗ M) LinearMap.id (fun s ↦ by simp) fun m ↦ by
          rw [tildeToOpenₛₗ_apply, LinearMap.id_apply]
          exact ConcreteCategory.congr_hom (IsIso.hom_inv_id (tilde.toOpen M ⊤)) m
      rw [_root_.SymmetricAlgebra.mapₛₗ_eq_id (fun _ ↦ rfl) (fun _ ↦ rfl)] at h
      exact RingHom.congr_fun h x)

/-- `projSymmetricAlgebraTildeIso` lies over `Spec Γ(Spec R, Spec R) ≅ Spec R`. -/
theorem projSymmetricAlgebraTildeIso_hom_projToSpec :
    (projSymmetricAlgebraTildeIso M).hom ≫ projToSpec R M =
      Proj.toSpecCoeff (homogeneousSubmodule Γ(Spec R, ⊤)
        (PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (op ⊤))) ≫
        Spec.map (Scheme.ΓSpecIso R).inv := by
  -- `Proj.mapIso` is not exposed, so its forward map is unfolded with `Proj.mapIso_hom`.
  have e : (projSymmetricAlgebraTildeIso M).hom =
      Proj.map (symmetricAlgebraTildeGradedHom M) _ :=
    Proj.mapIso_hom _ _ _ _
  rw [e, projToSpec_def, Proj.map_toSpecZero_assoc, Proj.toSpecCoeff_def, Category.assoc]
  congr 1
  simp only [← Spec.map_comp]
  congr 1
  ext r
  exact _root_.SymmetricAlgebra.mapₛₗ_algebraMap (tildeToOpenₛₗ M ⊤) r

end

/-- **A projective scheme over a ring is projective over its spectrum**: if `X` is a closed
subscheme over `R` of `Proj (Sym_R M)` for a finite `R`-module `M`
(`AlgebraicGeometry.Scheme.IsProjectiveOver`), then `X ⟶ Spec R` is projective. Through
`projSymmetricAlgebraTildeIso` and `relativeProjGradedSymmetricAlgebraIso`, `Proj (Sym_R M)` is the
projective bundle of `M~`, which is of finite type. -/
instance _root_.AlgebraicGeometry.Scheme.IsProjectiveOver.isProjective {R : Type u} [CommRing R]
    {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R] :
    IsProjective (X ↘ Spec (.of R)) := by
  obtain ⟨M, _, _, _, g, hg, hgR⟩ :=
    Scheme.IsProjectiveOver.exists_isClosedImmersion (R := R) (X := X)
  -- `ModuleCat` needs an additive group, and a module over a ring is one.
  let := Module.addCommMonoidToAddCommGroup R (M := M)
  let F : QuasicoherentSheaf (Spec (.of R)) := ⟨tilde (ModuleCat.of R M), inferInstance⟩
  have := isProjective_toSpecCoeff_comp_fromSpec F
  have key : projToSpec R M =
      (projSymmetricAlgebraTildeIso (ModuleCat.of (CommRingCat.of R) M)).inv ≫
        Proj.toSpecCoeff (homogeneousSubmodule Γ(Spec (.of R), ⊤)
          (PresheafOfModulesOfCommRing.obj (R := (Spec (.of R)).presheaf) F.obj.val (op ⊤))) ≫
          (isAffineOpen_top _).fromSpec := by
    rw [Iso.eq_inv_comp, projSymmetricAlgebraTildeIso_hom_projToSpec,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  rw [← comp_over g (Spec (.of R)), over_eq_projToSpec, key, ← Category.assoc]
  infer_instance

end TauCeti.AlgebraicGeometry
