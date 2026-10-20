/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IntermediateField.Basic
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff

/-!
# Root counts of coefficient vectors in intermediate fields

A monic polynomial of degree `n` over a field `K` is its coefficient vector `a : Fin n → K`,
through `TauCeti.Polynomial.monicOfCoeff`. For an intermediate field `L` of `E / K`, the root
count `L.rootCount a` is the number of roots of that polynomial in `L`, counted with
multiplicity. Serre's mass formula integrates these root counts over coefficient space.

## Main declarations

* `IntermediateField.rootCount`: the number of roots of `monicOfCoeff a` in `L`.
* `IntermediateField.rootCount_def`: its unfolding as the cardinality of a root multiset.
-/

public section
noncomputable section

open Polynomial TauCeti.Polynomial

namespace IntermediateField

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- The root count of a coefficient vector `a : Fin n → K` in an intermediate field `L` of `E / K`:
the number of roots in `L`, counted with multiplicity, of the monic polynomial
`X ^ n + ∑ i, a i * X ^ i` whose lower coefficients are `a`. -/
def rootCount (L : IntermediateField K E) {n : ℕ} (a : Fin n → K) : ℕ :=
  ((monicOfCoeff a).aroots L).card

/-- The root count is the cardinality of the root multiset of `monicOfCoeff a` in `L`. -/
@[simp]
theorem rootCount_def (L : IntermediateField K E) {n : ℕ} (a : Fin n → K) :
    L.rootCount a = ((monicOfCoeff a).aroots L).card := by
  rw [rootCount]

end IntermediateField
