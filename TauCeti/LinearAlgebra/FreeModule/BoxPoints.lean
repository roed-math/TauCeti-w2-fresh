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
public import TauCeti.Combinatorics.Additive.ImageCard

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

Two points of a finite set `S ⊆ ℤ^m` with the same image under `s ↦ ∏ α_j ^ s_j` differ by a
vector of the kernel. So if the differences of `S` lie in the box `‖s‖∞ ≤ R`, each fibre of this
map on `S`, and more generally of any homomorphism `g` whose kernel lies in that kernel, has at
most `2R + 1` points, and `#S ≤ (2R + 1) · #g(S)`.

## Main results

* `Submodule.ncard_setOf_mem_abs_le_le_of_finrank_le_one`: a rank-at-most-one subgroup of `ℤ^m`
  has at most `2R + 1` points in the box `‖s‖∞ ≤ R`.
* `LinearMap.finrank_ker_le_one`: a map out of `ℤ^m` with image of rank at least `m - 1` has
  kernel of rank at most one.
* `LinearMap.ncard_setOf_apply_eq_zero_abs_le_le`: such a map vanishes at most at `2R + 1`
  points of the box `‖s‖∞ ≤ R`.
* `LinearMap.ncard_le_mul_ncard_image_of_ker_le`: a finite `S ⊆ ℤ^m` whose differences lie in
  the box `‖s‖∞ ≤ R` has at most `(2R + 1) · #g(S)` elements, for every homomorphism `g` whose
  kernel lies in the kernel of such a map.
-/

public section

open Module Set
open scoped Pointwise

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

/-- Let `φ` be a `ℤ`-linear map out of `ℤ^m` whose image has rank at least `m - 1`, and let `g` be
an additive homomorphism whose kernel lies in the kernel of `φ`. A finite set `S ⊆ ℤ^m` whose
differences all have coordinates of absolute value at most `R` meets each fibre of `g` in at most
`2R + 1` points, so it has at most `(2R + 1) · #g(S)` elements. -/
theorem ncard_le_mul_ncard_image_of_ker_le {C : Type*} [AddGroup C] (φ : (Fin m → ℤ) →ₗ[ℤ] M)
    (hφ : m ≤ finrank ℤ (range φ) + 1) (g : (Fin m → ℤ) →+ C) (hg : ∀ s, g s = 0 → φ s = 0)
    {S : Set (Fin m → ℤ)} (hS : S.Finite) {R : ℕ}
    (hR : ∀ s ∈ S, ∀ t ∈ S, ∀ i, |s i - t i| ≤ R) :
    S.ncard ≤ (g '' S).ncard * (2 * R + 1) := by
  have hbox : {s : Fin m → ℤ | φ s = 0 ∧ ∀ i, |s i| ≤ R}.Finite :=
    (Finite.pi (t := fun _ : Fin m ↦ Icc (-(R : ℤ)) R) fun _ ↦ finite_Icc _ _).subset
      fun s hs i _ ↦ abs_le.mp (hs.2 i)
  have hsub : (AddMonoidHom.id _ '' ((S - S) ∩ g.ker)) ⊆
      {s : Fin m → ℤ | φ s = 0 ∧ ∀ i, |s i| ≤ R} := by
    rintro _ ⟨_, ⟨⟨s, hs, t, ht, rfl⟩, hker⟩, rfl⟩
    exact ⟨hg _ hker, hR s hs t ht⟩
  calc S.ncard = (AddMonoidHom.id _ '' S).ncard := by simp
    _ ≤ (g '' S).ncard * (AddMonoidHom.id _ '' ((S - S) ∩ g.ker)).ncard :=
        (AddMonoidHom.id _).ncard_image_le_mul_ncard_image_sub_inter_ker g hS
    _ ≤ (g '' S).ncard * (2 * R + 1) :=
        Nat.mul_le_mul_left _ ((ncard_le_ncard hsub hbox).trans
          (φ.ncard_setOf_apply_eq_zero_abs_le_le hφ R))

end LinearMap
