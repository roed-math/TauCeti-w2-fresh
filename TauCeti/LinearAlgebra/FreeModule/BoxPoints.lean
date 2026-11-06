/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Points of a rank-one subgroup of `ℤ^m` in a box

A subgroup `H ≤ ℤ^m` of rank at most one is contained in `ℤ h` for a single vector `h`. A nonzero
multiple `k h` with all coordinates of absolute value at most `R` has `|k| ≤ R`, since some
coordinate of `h` has absolute value at least one. So `H` has at most `2R + 1` points in the box
`‖s‖∞ ≤ R`.

By rank-nullity, a `ℤ`-linear map `φ` out of `ℤ^m` whose image has rank at least `m - 1` has a
kernel of rank at most one. For `φ s = ∏ α_j ^ s_j` into the multiplicative group of a field,
viewed additively, the rank of the image is the multiplicative rank of `α₁, …, α_m`. So when the
`α_j` generate a group of rank at least `m - 1`, at most `2R + 1` exponent vectors in the box
`‖s‖∞ ≤ R` satisfy `∏ α_j ^ s_j = 1`. This is the count by which the multiplicative rank enters
the subgroup obstruction of Waldschmidt's rank argument (W00 §9.2.3, Proposition 9.16).

## Main results

* `Submodule.ncard_setOf_mem_abs_le_le_of_finrank_le_one`: a rank-at-most-one subgroup of `ℤ^m`
  has at most `2R + 1` points in the box `‖s‖∞ ≤ R`.
* `LinearMap.finrank_ker_le_one`: a map out of `ℤ^m` with image of rank at least `m - 1` has
  kernel of rank at most one.
* `LinearMap.ncard_setOf_apply_eq_zero_abs_le_le`: such a map vanishes at most at `2R + 1`
  points of the box `‖s‖∞ ≤ R`.
-/

public section

open Module Set

namespace Submodule

/-- A subgroup of `ℤ^m` of rank at most one has at most `2R + 1` points whose coordinates all
have absolute value at most `R`. -/
theorem ncard_setOf_mem_abs_le_le_of_finrank_le_one {m : ℕ} {H : Submodule ℤ (Fin m → ℤ)}
    (hH : finrank ℤ H ≤ 1) (R : ℕ) :
    {s : Fin m → ℤ | s ∈ H ∧ ∀ i, |s i| ≤ R}.ncard ≤ 2 * R + 1 := by
  obtain ⟨h, hh⟩ := finrank_le_one_iff.mp hH
  have hsub : {s : Fin m → ℤ | s ∈ H ∧ ∀ i, |s i| ≤ R} ⊆
      (fun k : ℤ ↦ k • (h : Fin m → ℤ)) '' Icc (-(R : ℤ)) R := by
    rintro s ⟨hs, hbox⟩
    obtain ⟨k, hk⟩ := hh ⟨s, hs⟩
    have hks : k • (h : Fin m → ℤ) = s := congrArg Subtype.val hk
    by_cases h0 : (h : Fin m → ℤ) = 0
    · exact ⟨0, by simp, by simp [← hks, h0]⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h0
    refine ⟨k, abs_le.mp ?_, hks⟩
    have := hbox i
    rw [← hks, Pi.smul_apply, smul_eq_mul, abs_mul] at this
    nlinarith [Int.one_le_abs hi, abs_nonneg k]
  calc _ ≤ ((fun k : ℤ ↦ k • (h : Fin m → ℤ)) '' Icc (-(R : ℤ)) R).ncard :=
        ncard_le_ncard hsub ((finite_Icc _ _).image _)
    _ ≤ (Icc (-(R : ℤ)) R).ncard := ncard_image_le (finite_Icc _ _)
    _ = 2 * R + 1 := by
        rw [ncard_eq_toFinset_card', toFinset_Icc, Int.card_Icc]
        omega

end Submodule

namespace LinearMap

variable {m : ℕ} {M : Type*} [AddCommGroup M]

/-- **Rank-nullity over `ℤ`.** A `ℤ`-linear map out of `ℤ^m` whose image has rank at least
`m - 1` has a kernel of rank at most one. -/
theorem finrank_ker_le_one (φ : (Fin m → ℤ) →ₗ[ℤ] M) (hφ : m ≤ finrank ℤ (range φ) + 1) :
    finrank ℤ (ker φ) ≤ 1 := by
  have h := (ker φ).finrank_quotient_add_finrank
  rw [φ.quotKerEquivRange.finrank_eq, finrank_fin_fun] at h
  omega

/-- A `ℤ`-linear map out of `ℤ^m` whose image has rank at least `m - 1` vanishes at no more than
`2R + 1` points whose coordinates all have absolute value at most `R`. -/
theorem ncard_setOf_apply_eq_zero_abs_le_le (φ : (Fin m → ℤ) →ₗ[ℤ] M)
    (hφ : m ≤ finrank ℤ (range φ) + 1) (R : ℕ) :
    {s : Fin m → ℤ | φ s = 0 ∧ ∀ i, |s i| ≤ R}.ncard ≤ 2 * R + 1 :=
  Submodule.ncard_setOf_mem_abs_le_le_of_finrank_le_one (φ.finrank_ker_le_one hφ) R

end LinearMap
