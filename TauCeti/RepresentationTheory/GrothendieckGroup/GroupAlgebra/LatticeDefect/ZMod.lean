/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Basic
public import TauCeti.RepresentationTheory.RestrictScalars

/-!
# Reduction classes of `ZMod n`-representations

A representation `ρ` of `G` over `ZMod n` is in particular a representation on an abelian group,
`ρ.restrictScalarsInt`. Its reduction `ZMod n ⊗_ℤ W` is `W` again: the scalar multiplication
`r ⊗ w ↦ r • w` is a `G`-equivariant isomorphism
(`Representation.baseChangeRestrictScalarsIntEquiv`), because every element of `ZMod n` is the
image of an integer. Hence the reduction class of `ρ.restrictScalarsInt` in `G₀(ZMod n[G])` is
the class of `ρ` itself (`TauCeti.reductionK0_restrictScalarsInt`).

This is how the reduction classes computed for groups such as `Lˣ ⧸ (Lˣ)^ℓ`, which are naturally
`ZMod ℓ`-modules, are compared with the classes of the corresponding `ZMod ℓ`-representations.
-/

public section

open TensorProduct
open scoped MonoidAlgebra

variable {n : ℕ} {G : Type} [Monoid G] {W : Type} [AddCommGroup W] [Module (ZMod n) W]

namespace Representation

/-- **The reduction of a `ZMod n`-module is itself**: `r ⊗ w ↦ r • w` is a `G`-equivariant
`ZMod n`-linear isomorphism `ZMod n ⊗_ℤ W ≃ W` for every representation `ρ` of `G` over
`ZMod n`. -/
noncomputable def baseChangeRestrictScalarsIntEquiv (ρ : Representation (ZMod n) G W) :
    (Representation.baseChange (ZMod n) ρ.restrictScalarsInt).Equiv ρ := by
  let f : ZMod n ⊗[ℤ] W →+ W :=
    (TensorProduct.lift (LinearMap.mk₂ ℤ (fun (r : ZMod n) (w : W) ↦ r • w) add_smul
      (fun c r w ↦ smul_assoc c r w) smul_add (fun c r w ↦ smul_comm r c w))).toAddMonoidHom
  -- `f` is `TensorProduct.lift` of the bilinear scalar multiplication, so it computes on pure
  -- tensors by definition; the `change` steps below only unfold `e` and `eL` to `f`.
  have hf (r : ZMod n) (w : W) : f (r ⊗ₜ w) = r • w := rfl
  have hmk (r : ZMod n) (w : W) : (1 : ZMod n) ⊗ₜ[ℤ] (r • w) = r ⊗ₜ w := by
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective r
    rw [Int.cast_smul_eq_zsmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', zsmul_eq_mul,
      mul_one]
  let e : ZMod n ⊗[ℤ] W ≃+ W :=
    { f with
      invFun := fun w ↦ (1 : ZMod n) ⊗ₜ w
      left_inv := fun x ↦ by
        induction x using TensorProduct.inductionOn with
        | tmul r w =>
            change (1 : ZMod n) ⊗ₜ[ℤ] f (r ⊗ₜ w) = r ⊗ₜ w
            rw [hf, hmk]
        | add x y hx hy =>
            change (1 : ZMod n) ⊗ₜ[ℤ] f (x + y) = x + y
            rw [map_add, TensorProduct.tmul_add]
            exact congrArg₂ (· + ·) hx hy
      right_inv := fun w ↦ by
        change f ((1 : ZMod n) ⊗ₜ w) = w
        rw [hf, one_smul] }
  let eL : ZMod n ⊗[ℤ] W ≃ₗ[ZMod n] W :=
    { AddMonoidHom.toZModLinearMap n e.toAddMonoidHom with
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv }
  refine .mk eL fun g ↦ LinearMap.ext fun x ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Representation.baseChange_apply]
  -- The underlying function of `eL` is `f`, by construction.
  change f ((ρ.restrictScalarsInt g).baseChange (ZMod n) x) = ρ g (f x)
  induction x using TensorProduct.inductionOn with
  | tmul r w =>
      rw [LinearMap.baseChange_tmul, hf, hf, Representation.restrictScalarsInt_apply, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Representation

namespace TauCeti

/-- **The reduction class of a `ZMod n`-representation is its class.** In `G₀(ZMod n[G])`,
the class of `ZMod n ⊗_ℤ W` is the class of the `ZMod n[G]`-module of `ρ`. -/
theorem reductionK0_restrictScalarsInt [Module.Finite (ZMod n) W]
    (ρ : Representation (ZMod n) G W) :
    haveI : Module.Finite (ZMod n) (ZMod n ⊗[ℤ] W) :=
      Module.Finite.equiv (ρ.baseChangeRestrictScalarsIntEquiv).toLinearEquiv.symm
    haveI : Module.Finite (ZMod n)[G] ρ.asModule :=
      Module.Finite.of_restrictScalars_finite (ZMod n) (ZMod n)[G] _
    reductionK0 (ZMod n) ρ.restrictScalarsInt =
      ExactK0.of (FGModuleCat.of (ZMod n)[G] ρ.asModule) := by
  have : Module.Finite (ZMod n) (ZMod n ⊗[ℤ] W) :=
    Module.Finite.equiv (ρ.baseChangeRestrictScalarsIntEquiv).toLinearEquiv.symm
  have : Module.Finite (ZMod n)[G] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite (ZMod n) (ZMod n)[G] _
  rw [reductionK0_def]
  exact ExactK0.of_congr
    (Representation.asModuleLinearEquivOfEquiv (ρ.baseChangeRestrictScalarsIntEquiv)
      ).toFGModuleCatIso

end TauCeti
