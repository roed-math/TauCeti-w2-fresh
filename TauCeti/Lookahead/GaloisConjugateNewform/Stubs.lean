/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.Hecke.Full

set_option warningAsError false

/-!
# Lookahead stubs for `newspace-hecke-algebra-over-character-field`

These are lookahead stubs for the supplier `newspace-hecke-algebra-over-character-field`
(ModularForms, Layer 8G, the semisimple Hecke-algebra correspondence), to be replaced by the
landed declarations. The supplier's remaining theorem is that the characters of the finite
Hecke algebra of the newspace over `ℚ`, after `⊗ ℂ`, are exactly the normalized newforms of the
space. It is stated here for the rational algebra generated on the newspace by `T_p` at every
prime `p` and the diamond operators.
-/

public section

open HeckeRing.GL2

namespace TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- In weight at least two, every complex-valued character of the rational Hecke algebra
generated on the newspace by every `T_p` and the diamond operators is the character of a
newform. -/
theorem Newform.exists_heckeTDiamondCuspNewFullRationalCharacter_eq (hk : 2 ≤ k)
    (φ : heckeTDiamondCuspNewFullRationalAlgebra N k →ₐ[ℚ] ℂ) :
    ∃ g : Newform N k, Newform.heckeTDiamondCuspNewFullRationalCharacter g = φ :=
  sorry

end TauCeti
