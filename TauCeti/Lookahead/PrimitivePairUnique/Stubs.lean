/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.StrongMultiplicityOne.Basic

set_option warningAsError false

/-!
# Lookahead stubs for `cross-level-strong-multiplicity-one`

These are lookahead stubs for the supplier `cross-level-strong-multiplicity-one` (ModularForms,
Layer 5): cross-level strong multiplicity one for newforms, with no hypothesis on the nebentypus.
They are to be replaced by the landed declarations.
-/

public section

namespace HeckeRing.GL2

/-- **Strong multiplicity one across levels, for newforms** (Miyake, Theorem 4.6.19). Two
newforms `f`, `g` of the same weight and of levels `N`, `M` whose eigenvalues agree at every
prime `p ∤ N M` outside a finite set `S` satisfy `N = M`, have the same nebentypus, and are the
same function. Nothing is assumed about the nebentypes. -/
theorem Newform.level_eq_and_χ_comp_unitsMap_eq_and_coe_eq_of_forall_notMem_prime_eigenvalue_eq
    {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ} (f : Newform N k) (g : Newform M k) {S : Finset ℕ}
    (h : ∀ (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N) (hpM : p.Coprime M), p ∉ S →
      f.eigenvalue ⟨p, hp.pos⟩ hpN = g.eigenvalue ⟨p, hp.pos⟩ hpM) :
    N = M ∧ f.χ.comp (ZMod.unitsMap (Nat.dvd_lcm_left N M)) =
      g.χ.comp (ZMod.unitsMap (Nat.dvd_lcm_right N M)) ∧ ⇑f.toCuspForm = ⇑g.toCuspForm :=
  sorry

end HeckeRing.GL2
