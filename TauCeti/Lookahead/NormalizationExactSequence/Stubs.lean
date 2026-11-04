/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Ideal.AffineBlowup
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

set_option warningAsError false

/-!
# Lookahead stubs for `node-branch-splitting`

These are lookahead stubs of the declarations of the StableReduction list item
`node-branch-splitting` consumed by the lookahead proof of `normalization-exact-sequence`. They
restate, with `sorry` proofs, the forms of open pull request #23800 (the roadmap's
`Suggested.lean` pins no declaration for this item), which adds them to
`TauCeti/RingTheory/Node/ExceptionalFiber.lean`. When that pull request lands, this file is
replaced by the landed declarations.
-/

public section

noncomputable section

open IsLocalRing TensorProduct TauCeti.Localization

namespace TauCeti

variable {A : Type*} [CommRing A] {x y a b : A}
  (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away x S]

/-- In the chart `A[𝔪/x]`, the relation `a x² + b x y + y² = 0` becomes the monic quadratic
relation `w² + b w + a = 0` for `w = y/x`. -/
theorem divBy_sq_add_mul_add_eq_zero (hrel : a * x ^ 2 + b * x * y + y ^ 2 = 0) :
    (divBy y x : S) ^ 2 + algebraMap A S b * divBy y x + algebraMap A S a = 0 := by
  sorry

variable {S} {I : Ideal A}

/-- **The chart of the blowup is spanned by `1` and `y/x`.** If `I = (x, y)` and
`a x² + b x y + y² = 0`, the affine blowup algebra `A[I/x]` is the `A`-submodule of the localization
spanned by `1` and `y/x`. -/
theorem toSubmodule_affineBlowup_eq_span (hI : I = Ideal.span {x, y})
    (hrel : a * x ^ 2 + b * x * y + y ^ 2 = 0) :
    Subalgebra.toSubmodule (I.affineBlowup x S) = Submodule.span A {1, divBy y x} := by
  sorry

/-- **The chart of the blowup is finite.** If `I = (x, y)` and `a x² + b x y + y² = 0`, the affine
blowup algebra `A[I/x]` is a finite `A`-module. -/
theorem finite_affineBlowup (hI : I = Ideal.span {x, y})
    (hrel : a * x ^ 2 + b * x * y + y ^ 2 = 0) :
    Module.Finite A (I.affineBlowup x S) := by
  sorry

variable [IsLocalRing A]

/-- **The exceptional fibre of blowing up a node is étale.** Let `𝔪 = (x, y)` with
`a x² + b x y + y² = 0`. If the discriminant `b² - 4a` is a unit, the fibre `κ ⊗[A] A[𝔪/x]` of the
chart `A[𝔪/x]` of the blowup at the closed point is étale over the residue field `κ`: it is a
quotient of the étale algebra `κ[W] ⧸ (W² + b W + a)`. -/
theorem etale_tensor_affineBlowup (hm : maximalIdeal A = Ideal.span {x, y})
    (hrel : a * x ^ 2 + b * x * y + y ^ 2 = 0) (hd : IsUnit (discrim a b 1)) :
    Algebra.Etale (ResidueField A) (ResidueField A ⊗[A] (maximalIdeal A).affineBlowup x S) := by
  sorry

end TauCeti
