/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftSheaf.Derivation

/-!
# The sheaf of derivations into the ideal of a thickening as a sheaf of modules

For `f : X ⟶ S`, `i : T ⟶ T'` and `a : T ⟶ X`, the derivations over an open `W` of `T'`
(`liftDerivationSubgroup f i a W`) form a module over `Γ(T', W)`: a section `t` acts on a
derivation `D` by `(t • D) U V x = t|_V * D U V x`. This makes the sheaf of derivations
`liftDerivationSheaf f i a` the underlying abelian sheaf of a sheaf of `𝒪_{T'}`-modules,
`liftDerivationModule f i a`.

## Main definitions

* `TauCeti.AlgebraicGeometry.liftDerivationModule f i a`: the sheaf of derivations of `a⁻¹ 𝒪_X`
  over `𝒪_S` into the ideal of `i`, as a sheaf of `𝒪_{T'}`-modules.

## Main results

* `TauCeti.AlgebraicGeometry.liftDerivationModule_toSheaf`: its underlying sheaf of abelian groups
  is `liftDerivationSheaf f i a`.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace TauCeti.AlgebraicGeometry

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) (i : T ⟶ T') (a : T ⟶ X)

variable {f i a} in
/-- A derivation over `W` multiplied by a section of `𝒪_{T'}` over `W` is a derivation. -/
theorem IsLiftDerivation.mul_left {W : T'.Opens}
    {D : ∀ p : LiftDerivationIndex i a W, Γ(X, p.1.1) →+ Γ(T', p.1.2)}
    (hD : IsLiftDerivation f i a D) (t : Γ(T', W)) :
    IsLiftDerivation f i a fun p ↦ AddMonoidHom.mk'
      (fun x ↦ T'.presheaf.map (homOfLE p.2.1).op t * D p x) fun x y ↦ by
        rw [map_add, mul_add] where
  map_apply p V' hV x := by
    simp only [AddMonoidHom.mk'_apply]
    rw [_root_.map_mul, hD.map_apply, ← CommRingCat.comp_apply, ← Functor.map_comp]
    -- Both sides restrict `t` along morphisms `V' ⟶ W` of the poset of opens, which are equal.
    rfl
  apply_map p U' hU e x := by
    simp only [AddMonoidHom.mk'_apply, hD.apply_map p U' hU e x]
  app_apply p x := by
    simp only [AddMonoidHom.mk'_apply]
    rw [_root_.map_mul, hD.app_apply, mul_zero]
  apply_appLE p O e s := by
    simp only [AddMonoidHom.mk'_apply, hD.apply_appLE, mul_zero]
  map_mul p x y z w hz hw := by
    simp only [AddMonoidHom.mk'_apply, hD.map_mul p x y z w hz hw]
    ring

/-- A section `t` of `𝒪_{T'}` over `W` acts on the derivations over `W` by
`(t • D) U V x = t|_V * D U V x`. -/
noncomputable instance (W : T'.Opens) : SMul Γ(T', W) (liftDerivationSubgroup f i a W) where
  smul t D := ⟨_, mem_liftDerivationSubgroup.2 ((isLiftDerivation_coe D).mul_left t)⟩

@[simp]
theorem liftDerivationSubgroup.smul_apply {W : T'.Opens} (t : Γ(T', W))
    (D : liftDerivationSubgroup f i a W) (p : LiftDerivationIndex i a W) (x : Γ(X, p.1.1)) :
    (t • D).1 p x = T'.presheaf.map (homOfLE p.2.1).op t * D.1 p x :=
  (rfl)

/-- The derivations over `W` form a module over `Γ(T', W)`. -/
noncomputable instance (W : T'.Opens) : Module Γ(T', W) (liftDerivationSubgroup f i a W) where
  one_smul D := liftDerivationSubgroup.ext fun p x ↦ by simp
  mul_smul s t D := liftDerivationSubgroup.ext fun p x ↦ by simp [mul_assoc]
  smul_zero t := liftDerivationSubgroup.ext fun p x ↦ by simp
  smul_add t D E := liftDerivationSubgroup.ext fun p x ↦ by simp [mul_add]
  add_smul s t D := liftDerivationSubgroup.ext fun p x ↦ by simp [add_mul]
  zero_smul D := liftDerivationSubgroup.ext fun p x ↦ by simp

/-- Restriction of derivations is semilinear over the restriction of sections of `𝒪_{T'}`. -/
theorem liftDerivationSubgroupRestrict_smul {W W' : T'.Opens} (e : W' ≤ W) (t : Γ(T', W))
    (D : liftDerivationSubgroup f i a W) :
    liftDerivationSubgroupRestrict f i a e (t • D) =
      T'.presheaf.map (homOfLE e).op t • liftDerivationSubgroupRestrict f i a e D :=
  liftDerivationSubgroup.ext fun q x ↦ by
    simp only [liftDerivationSubgroupRestrict_apply, liftDerivationSubgroup.smul_apply]
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    -- Both sides restrict `t` along morphisms `V ⟶ W` of the poset of opens, which are equal.
    rfl

/-- The sheaf of derivations of `a⁻¹ 𝒪_X` over `𝒪_S` into the ideal of `i`, as a sheaf of
`𝒪_{T'}`-modules: a section `t` of `𝒪_{T'}` over `W` acts by `(t • D) U V x = t|_V * D U V x`. -/
noncomputable def liftDerivationModule : T'.Modules where
  val :=
    letI (W : T'.Opensᵒᵖ) :
        Module (T'.ringCatSheaf.obj.obj W) ((liftDerivationPresheaf f i a).obj W) :=
      inferInstanceAs (Module Γ(T', W.unop) (liftDerivationSubgroup f i a W.unop))
    .ofPresheaf (liftDerivationPresheaf f i a) fun _ _ e t D ↦
      liftDerivationSubgroupRestrict_smul f i a e.unop.le t D
  isSheaf := liftDerivationPresheaf_isSheaf f i a

/-- The underlying sheaf of abelian groups of `liftDerivationModule f i a` is the sheaf of
derivations `liftDerivationSheaf f i a`. -/
theorem liftDerivationModule_toSheaf :
    (SheafOfModules.toSheaf T'.ringCatSheaf).obj (liftDerivationModule f i a) =
      liftDerivationSheaf f i a :=
  (rfl)

end TauCeti.AlgebraicGeometry
