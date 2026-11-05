/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.AdditionTheorem

set_option warningAsError false

/-!
# Lookahead stubs for `weierstrass-uniformization`

These are lookahead stubs for the supplier `weierstrass-uniformization`
(ImaginaryQuadraticClassNumber, H3.1), in the form stated by its open pull request #28061
(`PeriodPair.weierstrassCurve_j_eq_of_lattice_eq_smul` in
`TauCeti/Analysis/SpecialFunctions/Elliptic/Uniformization.lean` and
`PeriodPair.weierstrassCurve_j_eq_iff` and
`WeierstrassCurve.exists_variableChange_smul_weierstrassCurve_periodPair_eq` in
`TauCeti/Analysis/SpecialFunctions/Elliptic/LatticeClassification.lean`). They are to be replaced
by the landed declarations: homothetic lattices have the same `j`-invariant, the `j`-invariant
classifies lattices up to homothety, and every elliptic curve over `ℂ` comes from a lattice.
-/

public noncomputable section

namespace PeriodPair

variable {L L' : PeriodPair} {c : ℂˣ}

/-- Homothetic lattices have the same `j`-invariant. -/
lemma weierstrassCurve_j_eq_of_lattice_eq_smul (h : L'.lattice = (c • L).lattice) :
    L'.weierstrassCurve.j = L.weierstrassCurve.j := by
  sorry

/-- **The `j`-invariant classifies lattices up to homothety**: `E_Λ` and `E_{Λ'}` have the same
`j`-invariant exactly when `Λ' = c Λ` for some `c ∈ ℂˣ`. -/
theorem weierstrassCurve_j_eq_iff :
    L.weierstrassCurve.j = L'.weierstrassCurve.j ↔ ∃ c : ℂˣ, L'.lattice = (c • L).lattice := by
  sorry

end PeriodPair

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℂ) [E.IsElliptic]

/-- **Every elliptic curve over `ℂ` comes from a lattice**: it is a change of variables of the
Weierstrass curve `y² = x³ - (g₂ / 4) x - g₃ / 4` of `ℤ τ + ℤ` for some `τ ∈ ℍ`, namely any `τ`
with `j(τ) = j(E)`. -/
theorem exists_variableChange_smul_weierstrassCurve_periodPair_eq :
    ∃ (τ : UpperHalfPlane) (C : VariableChange ℂ), C • τ.periodPair.weierstrassCurve = E := by
  sorry

end WeierstrassCurve
