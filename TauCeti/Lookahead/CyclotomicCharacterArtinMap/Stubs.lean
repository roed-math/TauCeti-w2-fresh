/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
public import TauCeti.NumberTheory.LocalField.Padic

set_option warningAsError false

/-!
# Lookahead stubs for the cyclotomic normalization over the p-adics

This module records the statement supplied by the roadmap item
`cyclotomic-character-artin-map-padic`. It is a temporary lookahead interface and is to be
replaced by the landed declaration.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

/-- Lookahead stub for the cyclotomic normalization of the local Artin map over `ℚ_p`. -/
theorem cyclotomicCharacter_artinMap_padic (p : ℕ) [Fact p.Prime]
    [IsNonarchimedeanLocalField ℚ_[p]] (u : ℤ_[p]ˣ)
    (σ : Field.absoluteGaloisGroup ℚ_[p])
    (_hσ : (QuotientGroup.mk σ : Field.absoluteGaloisGroupAbelianization ℚ_[p])
      = artinMap ℚ_[p] (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u)) :
    cyclotomicCharacter (AlgebraicClosure ℚ_[p]) p σ.toRingEquiv = u⁻¹ := by
  sorry

end TauCeti.ClassFieldTheory
