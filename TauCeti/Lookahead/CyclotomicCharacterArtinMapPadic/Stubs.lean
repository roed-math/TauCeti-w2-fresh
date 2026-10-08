/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.RingTheory.Norm.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.Basic

set_option warningAsError false

/-!
# Lookahead stubs for `cyclotomic-symbol-norm-fixes`

These are lookahead stubs for the supplier `cyclotomic-symbol-norm-fixes` (ClassFieldTheory,
Layer 7, the cyclotomic normalization, step 2), stated against `main`'s API under the name the
supplier will have on Tau Ceti. They are to be replaced by the landed declarations.
-/

public section

namespace TauCeti

/-- **The explicit symbol at `p` kills local norms.** Let `M` be a finite extension of `ℚ_p` inside
`ℚ_p(μ_m)`. For `y ∈ Mˣ`, every `σ ∈ G_{ℚ_p}` acting on `μ_m` through
`cyclotomicSymbol m p (N_{M/ℚ_p} y)` fixes `M`. -/
theorem cyclotomicSymbol_norm_fixes (p : ℕ) [Fact p.Prime] (m : ℕ) [NeZero m]
    (M : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) [FiniteDimensional ℚ_[p] M]
    (hM : M ≤ IntermediateField.adjoin ℚ_[p] {z : AlgebraicClosure ℚ_[p] | z ^ m = 1})
    (y : Mˣ) (σ : Field.absoluteGaloisGroup ℚ_[p])
    (hσ : ∀ z : AlgebraicClosure ℚ_[p], z ^ m = 1 →
      σ.toRingEquiv z =
        z ^ ((cyclotomicSymbol m p (Units.map (Algebra.norm ℚ_[p] : M →* ℚ_[p]) y) :
          ZMod m).val))
    (x : M) :
    σ.toRingEquiv (x : AlgebraicClosure ℚ_[p]) = x :=
  sorry

end TauCeti
