/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.Uniformization

set_option warningAsError false

/-!
# Lookahead stubs for `weierstrass-uniformization`

These are lookahead stubs for the supplier `weierstrass-uniformization`
(ImaginaryQuadraticClassNumber, H3.1), in the form stated by its open pull request #22646
(`TauCeti/Analysis/SpecialFunctions/Elliptic/AdditionTheorem.lean`). They are to be replaced by the
landed declarations: the group law of the Weierstrass point map, the point map as a homomorphism
`ℂ →+ E(ℂ)`, and its kernel.
-/

public noncomputable section

namespace PeriodPair

variable (L : PeriodPair)

/-- **The addition law.** The point map `z ↦ (℘(z), ℘'(z) / 2)` (sending `Λ` to the point at
infinity) is additive: `P(z + w) = P(z) + P(w)` in the group of points of the Weierstrass curve. -/
@[simp]
theorem weierstrassPoint_add (z w : ℂ) :
    L.weierstrassPoint (z + w) = L.weierstrassPoint z + L.weierstrassPoint w := by
  sorry

/-- The point map `z ↦ (℘(z), ℘'(z) / 2)` as a group homomorphism from `ℂ` to the points of the
Weierstrass curve of `L`. -/
def weierstrassPointHom : ℂ →+ L.weierstrassCurve.toAffine.Point :=
  sorry

@[simp]
lemma weierstrassPointHom_apply (z : ℂ) : L.weierstrassPointHom z = L.weierstrassPoint z := by
  sorry

/-- The kernel of the point map is the period lattice. -/
lemma ker_weierstrassPointHom : L.weierstrassPointHom.ker = L.lattice.toAddSubgroup := by
  sorry

end PeriodPair
