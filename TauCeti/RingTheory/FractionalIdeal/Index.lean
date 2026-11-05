/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.FractionalIdeal.Operations
import TauCeti.RingTheory.FractionalIdeal.CoprimeRepresentative

/-!
# The index of `𝔞 J` in an invertible fractional ideal `J`

Let `R` be a domain with fraction field `K`, let `J` be an invertible fractional ideal of `R` and
let `𝔞` be an ideal of `R` contained in only finitely many maximal ideals, for instance an ideal
with finite quotient ring (`Ideal.finite_setOfPred_isMaximal_and_le`). Then the index of `𝔞 J` in
`J` is the index of `𝔞` in `R`: `[J : 𝔞 J] = [R : 𝔞]`
(`FractionalIdeal.relIndex_coeIdeal_mul_eq_index`).

No Dedekind hypothesis is made: the motivating case is a non-maximal order of a number field, where
`[R : 𝔞]` is the norm of `𝔞` and the result says that multiplication by an invertible ideal `J`
does not change it, `[J : 𝔞 J] = N(𝔞)`.

The proof replaces `J` by a multiple `a J = I` which is an integral ideal coprime to `𝔞`
(`FractionalIdeal.exists_coeIdeal_eq_spanSingleton_mul_and_sup_eq_top`); multiplication by `a`
does not change the index. Then `𝔞 I = 𝔞 ⊓ I`, and `I / (𝔞 ⊓ I) ≃ (𝔞 ⊔ I) / 𝔞 = R / 𝔞` by the
second isomorphism theorem.

## Main results

* `FractionalIdeal.relIndex_coeIdeal_mul_eq_index`: `[J : 𝔞 J] = [R : 𝔞]` for invertible `J`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Lemma 7.14 and Corollary 7.17 (orders in quadratic
  fields).
-/

open scoped nonZeroDivisors

public section

namespace FractionalIdeal

section CommRing

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]

/-- The additive group of an integral ideal, as a fractional ideal, is the image of the ideal in
`K`. -/
lemma toAddSubgroup_coeIdeal (I : Ideal R) :
    ((I : FractionalIdeal R⁰ K) : Submodule R K).toAddSubgroup =
      I.toAddSubgroup.map (algebraMap R K).toAddMonoidHom := by
  ext x
  simp [eq_comm]

variable [IsFractionRing R K]

/-- Multiplying a fractional ideal by `a` is the image of its additive group under `x ↦ a x`. -/
lemma toAddSubgroup_spanSingleton_mul (a : K) (M : FractionalIdeal R⁰ K) :
    ((spanSingleton R⁰ a * M : FractionalIdeal R⁰ K) : Submodule R K).toAddSubgroup =
      (M : Submodule R K).toAddSubgroup.map (AddMonoidHom.mulLeft a) := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, mem_coe, mem_singleton_mul, AddSubgroup.mem_map,
    AddMonoidHom.coe_mulLeft]
  exact ⟨fun ⟨y, hy, e⟩ ↦ ⟨y, hy, e.symm⟩, fun ⟨y, hy, e⟩ ↦ ⟨y, hy, e.symm⟩⟩

end CommRing

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The index of `𝔞 J` in `J`.** If `J` is an invertible fractional ideal of a domain `R` and
`𝔞` is an ideal of `R` contained in only finitely many maximal ideals, then `[J : 𝔞 J] = [R : 𝔞]`.
-/
theorem relIndex_coeIdeal_mul_eq_index (J : (FractionalIdeal R⁰ K)ˣ) {𝔞 : Ideal R}
    (h𝔞 : {P : Ideal R | P.IsMaximal ∧ 𝔞 ≤ P}.Finite) :
    ((𝔞 * J : FractionalIdeal R⁰ K) : Submodule R K).toAddSubgroup.relIndex
        ((J : FractionalIdeal R⁰ K) : Submodule R K).toAddSubgroup =
      𝔞.toAddSubgroup.index := by
  obtain ⟨a, ha, I, hI, hI𝔞⟩ := exists_coeIdeal_eq_spanSingleton_mul_and_sup_eq_top J h𝔞
  -- Multiplying by `a ≠ 0` does not change the index and turns `J` into the integral ideal `I`
  -- coprime to `𝔞`, and `𝔞 J` into `𝔞 I`.
  have hinj : Function.Injective (AddMonoidHom.mulLeft a) := mul_right_injective₀ ha
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj,
    ← toAddSubgroup_spanSingleton_mul, ← toAddSubgroup_spanSingleton_mul, mul_left_comm, ← hI,
    ← coeIdeal_mul, toAddSubgroup_coeIdeal, toAddSubgroup_coeIdeal,
    AddSubgroup.relIndex_map_map_of_injective _ _ (IsFractionRing.injective R K)]
  -- Coprimality gives `𝔞 I = 𝔞 ⊓ I`, and `I / (𝔞 ⊓ I) ≃ (𝔞 ⊔ I) / 𝔞 = R / 𝔞`.
  have hinf : (𝔞 * I).toAddSubgroup = 𝔞.toAddSubgroup ⊓ I.toAddSubgroup := by
    rw [Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.mpr (by rwa [sup_comm]))]
    ext
    simp
  rw [hinf, AddSubgroup.inf_relIndex_right, ← AddSubgroup.relIndex_sup_right,
    ← Submodule.sup_toAddSubgroup, hI𝔞, Submodule.top_toAddSubgroup,
    AddSubgroup.relIndex_top_right]

end FractionalIdeal
