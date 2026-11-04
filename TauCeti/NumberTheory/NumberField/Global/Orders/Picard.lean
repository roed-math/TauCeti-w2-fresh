/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.ProperIdeal
public import TauCeti.RingTheory.ClassGroup.Basic

/-!
# Invertible ideals and the Picard group of an order

For an order in a number field, the invertible fractional ideals are precisely the units of its
fractional-ideal monoid. Every such ideal is proper, although a proper ideal need not be invertible.
The wide Picard group is their quotient by nonzero principal ideals. Mathlib's `ClassGroup` already
forms this quotient for every domain, so the Picard group of an order uses that carrier rather than
constructing a second quotient.

## References

* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

public section
noncomputable section

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The wide Picard group of an order: invertible fractional ideals modulo principal ideals.
`ClassGroup` already implements this quotient for every integral domain. -/
abbrev Pic (O : NumberFieldOrder K) := ClassGroup O.toSubalgebra

namespace NumberFieldOrder

/-- The wide Picard class of an invertible fractional ideal. -/
abbrev mkPic (O : NumberFieldOrder K) : O.invertibleProperFractionalIdeals →* Pic O :=
  ClassGroup.mk K

/-- Every wide Picard class has an invertible fractional-ideal representative. -/
theorem mkPic_surjective (O : NumberFieldOrder K) : Function.Surjective O.mkPic :=
  fun c => ClassGroup.induction (K := K) (P := fun c => ∃ I, O.mkPic I = c)
    (fun I => ⟨I, rfl⟩) c

open FractionalIdeal in
/-- **Every wide Picard class contains an integral ideal**: a representative that is an ideal of
the order, obtained by clearing the denominator of any representative. -/
theorem exists_mkPic_eq_coeIdeal (O : NumberFieldOrder K) (a : Pic O) :
    ∃ (u : O.invertibleProperFractionalIdeals) (𝔞 : Ideal O.toSubalgebra),
      (u : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) = 𝔞 ∧ O.mkPic u = a := by
  obtain ⟨I, rfl⟩ := O.mkPic_surjective a
  set I' : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K := I.val
  set d : K := algebraMap O.toSubalgebra K I'.den
  have hd : d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I'.den.2
  set x : Kˣ := Units.mk0 d hd
  refine ⟨toPrincipalIdeal O.toSubalgebra K x * I, I'.num, ?_, ?_⟩
  · rw [Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0, den_mul_self_eq_num']
  · rw [map_mul, mul_eq_right, ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal,
      coe_spanSingleton]
    exact ⟨⟨_, rfl⟩⟩

end NumberFieldOrder

end TauCeti.GlobalNumberFields
