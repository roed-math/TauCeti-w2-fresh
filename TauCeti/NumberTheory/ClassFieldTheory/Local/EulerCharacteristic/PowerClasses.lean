/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Lookahead.EulerCharacteristicMixed.Stubs
public import TauCeti.RepresentationTheory.QuotSMulTop
public import TauCeti.RepresentationTheory.RestrictScalars

/-!
# Power classes as reductions of the multiplicative group

The unit calculation used in the local Euler characteristic is phrased in terms of the additive
reduction `Lˣ / nLˣ`, while Kummer theory is phrased in terms of the multiplicative quotient
`Lˣ / (Lˣ)ⁿ`. This file identifies the two quotients and checks that the identification respects
the natural Galois actions. It is the bridge through which the power-class Grothendieck-group
calculation enters equivariant Kummer theory.

## Main results

* `TauCeti.quotSMulTopPowerClassEquiv`: the additive equivalence between reduction modulo `n` and
  the group of `n`th power classes.
* `TauCeti.quotSMulTopUnitsPowerClassRepresentationEquiv`: the equivalence respects the action of
  `Gal(L/K)`.
-/

public noncomputable section

open scoped Pointwise

namespace TauCeti

/-- In the additive group of a commutative group, the subgroup of integer multiples by `n` is the
additive form of the subgroup of `n`th powers. -/
theorem zsmulTop_toAddSubgroup_eq_powerSubgroup {G : Type*} [CommGroup G] (n : ℕ) :
    ((n : ℤ) • (⊤ : Submodule ℤ (Additive G))).toAddSubgroup =
      (powerSubgroup G n).toAddSubgroup := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_top, true_and, Additive.mem_toAddSubgroup, mem_powerSubgroup_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.toMul, by simp [natCast_zsmul]⟩
  · rintro ⟨y, hy⟩
    exact ⟨Additive.ofMul y, by simpa [natCast_zsmul] using congrArg Additive.ofMul hy⟩

/-- Reduction modulo `n` of a commutative group, written additively, is its group of `n`th power
classes. -/
def quotSMulTopPowerClassEquiv {G : Type*} [CommGroup G] (n : ℕ) :
    QuotSMulTop (n : ℤ) (Additive G) ≃+ Additive (powerClassQuotient G n) := by
  let f : Additive G →+ Additive (powerClassQuotient G n) :=
    MonoidHom.toAdditive (powerClassHom G n)
  have hker : ((n : ℤ) • (⊤ : Submodule ℤ (Additive G))).toAddSubgroup = f.ker := by
    rw [zsmulTop_toAddSubgroup_eq_powerSubgroup]
    ext x
    change x.toMul ∈ powerSubgroup G n ↔ powerClassHom G n x.toMul = 1
    rw [← MonoidHom.mem_ker, ker_powerClassHom]
  exact (QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f (powerClassHom_surjective G n))

/-- The reduction/power-class equivalence sends the class of `x` to its power class. -/
@[simp]
theorem quotSMulTopPowerClassEquiv_mk {G : Type*} [CommGroup G] (n : ℕ) (x : Additive G) :
    quotSMulTopPowerClassEquiv n (Submodule.Quotient.mk x) =
      Additive.ofMul (powerClassHom G n x.toMul) := by
  unfold quotSMulTopPowerClassEquiv
  rfl

/-- The natural identification of additive reduction with power classes is equivariant for the
action of `Gal(L/K)`. -/
def quotSMulTopUnitsPowerClassRepresentationEquiv
    {K L : Type*} [Field K] [Field L] [Algebra K L] (n : ℕ) :
    ((Representation.ofDistribMulAction ℤ Gal(L/K) (Additive Lˣ)).quotSMulTop
      (n : ℤ)).Equiv
        (powerClassRepresentation (K := K) (L := L) n).restrictScalarsInt where
  toLinearEquiv := (quotSMulTopPowerClassEquiv n).toIntLinearEquiv
  isIntertwining' tau := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Representation.quotSMulTop_apply_mk, Representation.restrictScalarsInt_apply,
      powerClassRepresentation_apply]
    change Additive.toMul (quotSMulTopPowerClassEquiv n
        (Submodule.Quotient.mk
          ((Representation.ofDistribMulAction ℤ Gal(L/K) (Additive Lˣ)) tau x))) =
      Additive.toMul (MonoidHom.toAdditive (powerClassMap n (Units.map (tau : L →* L)))
        (quotSMulTopPowerClassEquiv n (Submodule.Quotient.mk x)))
    rw [quotSMulTopPowerClassEquiv_mk, quotSMulTopPowerClassEquiv_mk]
    simp

end TauCeti
