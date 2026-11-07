/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.Hecke.CharacterField
public import TauCeti.NumberTheory.ModularForms.Newforms.Hecke.Rational

set_option warningAsError false

/-!
# Lookahead stubs for `newspace-hecke-algebra-over-character-field`

These are lookahead stubs for the supplier `newspace-hecke-algebra-over-character-field`
(ModularForms, Layer 8G, the semisimple Hecke-algebra correspondence), to be replaced by the
landed declarations. The algebras, the newform characters and their conjugates have landed on
`main`; what remains is the theorem that the characters of the newspace Hecke algebra after
`⊗ ℂ` are exactly the normalized newforms of the space, stated here over `ℚ(χ)` and over `ℚ`
after summing the character orbit.
-/

public section

open HeckeRing.GL2

namespace TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- In weight at least two, every `ℚ(χ)`-algebra character of the Hecke algebra of
`S_k(N, χ)ⁿᵉʷ` over `ℚ(χ)` is the character of a newform of nebentypus `χ`. -/
theorem exists_heckeTCuspNewCharFieldCharacter_eq {χ : (ZMod N)ˣ →* ℂˣ} (hk : 2 ≤ k)
    (φ : heckeTCuspNewCharFieldAlgebra k χ →ₐ[CharacterField χ] ℂ) :
    ∃ g, heckeTCuspNewCharFieldCharacter g = φ :=
  sorry

/-- In weight at least two, every complex-valued character of the rational newspace Hecke
algebra, which sums the newspaces of all nebentypus characters, is the character of a newform. -/
theorem Newform.exists_heckeTDiamondCuspNewRationalCharacter_eq (hk : 2 ≤ k)
    (φ : heckeTDiamondCuspNewRationalAlgebra N k →ₐ[ℚ] ℂ) :
    ∃ g : Newform N k, Newform.heckeTDiamondCuspNewRationalCharacter g = φ :=
  sorry

end TauCeti
