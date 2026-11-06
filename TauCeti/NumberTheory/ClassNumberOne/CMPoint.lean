/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# The CM point of an imaginary quadratic discriminant and its multiplication matrices

For a negative discriminant `D ≡ 0, 1 (mod 4)` the CM point `τ_D` in the upper half-plane is
`i √|D| / 2` if `D ≡ 0 (mod 4)` and `(3 + i √|D|) / 2` if `D ≡ 1 (mod 4)`
(`TauCeti.cmTau`). It is a root of the monic integral polynomial `X² + B X + C` with
`B = 0` or `B = -3` (`TauCeti.cmTauLinearCoeff`, `TauCeti.cmTauConstCoeff`,
`TauCeti.cmTau_sq_add`), whose discriminant `B² - 4C` is `D`
(`TauCeti.cmTauLinearCoeff_sq_sub_four_mul_cmTauConstCoeff`), so `ℤ[τ_D]` is the order of
discriminant `D`.

Multiplication by `t + s τ` on the basis `(τ, 1)` of `ℤ[τ]` has the matrix
`[[t - B s, -C s], [s, t]]` (`TauCeti.cmMulMatrix`): the column `(τ, 1)` is an eigenvector with
eigenvalue `t + s τ` (`TauCeti.cmMulMatrix_mulVec`). These matrices multiply as the elements
`t + s τ` do (`TauCeti.cmMulMatrix_mul`), their determinant is the norm form
`t² - B s t + C s²` (`TauCeti.det_cmMulMatrix`), and reduction to any commutative ring commutes
with their formation (`TauCeti.map_cmMulMatrix`). They are the matrices through which the
reciprocity law of complex multiplication acts on values of modular functions of level `N` at
`τ_D`.

Since `4 (t² - B s t + C s²) = (2t - B s)² - D s²`, the units `t + s τ` of `ℤ[τ]`, the solutions
of `t² - B s t + C s² = 1`, are only `±1` once `D < -4`
(`TauCeti.cmNormForm_eq_one_iff_of_lt_neg_four`), while `D = -4` has the four units
`±1, ±τ` (`TauCeti.cmNormForm_eq_one_iff_neg_four`) and `D = -3` has six
(`TauCeti.cmNormForm_eq_one_iff_neg_three`). These are the exceptional kernels of the
reciprocity action at `D = -3, -4`, which are larger than `{±1}`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §11 and §12.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §3.
-/

public noncomputable section

open Complex
open scoped UpperHalfPlane

namespace TauCeti

/-- The linear coefficient `B` of the monic polynomial `X² + B X + C` of the CM point `τ_D`:
`0` if `D ≡ 0 (mod 4)` and `-3` otherwise. -/
@[expose] def cmTauLinearCoeff (D : ℤ) : ℤ := if D % 4 = 0 then 0 else -3

/-- The constant coefficient `C` of the monic polynomial `X² + B X + C` of the CM point `τ_D`:
`-D / 4` if `D ≡ 0 (mod 4)` and `(9 - D) / 4` otherwise. -/
@[expose] def cmTauConstCoeff (D : ℤ) : ℤ := if D % 4 = 0 then -D / 4 else (9 - D) / 4

/-- The discriminant of `X² + B X + C` is `D`. -/
theorem cmTauLinearCoeff_sq_sub_four_mul_cmTauConstCoeff {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) :
    cmTauLinearCoeff D ^ 2 - 4 * cmTauConstCoeff D = D := by
  unfold cmTauLinearCoeff cmTauConstCoeff
  split_ifs <;> omega

/-- The complex number `i √|D| / 2` if `D ≡ 0 (mod 4)` and `(3 + i √|D|) / 2` otherwise,
the underlying number of the CM point `TauCeti.cmTau`. -/
def cmTauCoe (D : ℤ) : ℂ :=
  if D % 4 = 0 then I * √|(D : ℝ)| / 2 else (3 + I * √|(D : ℝ)|) / 2

/-- The imaginary part of `TauCeti.cmTauCoe D` is `√|D| / 2`. -/
theorem im_cmTauCoe (D : ℤ) : (cmTauCoe D).im = √|(D : ℝ)| / 2 := by
  unfold cmTauCoe
  split_ifs <;> simp

/-- **The CM point `τ_D`** of a negative discriminant `D`: `i √|D| / 2` if `D ≡ 0 (mod 4)` and
`(3 + i √|D|) / 2` if `D ≡ 1 (mod 4)`. -/
def cmTau (D : ℤ) (hD : D < 0) : ℍ :=
  ⟨cmTauCoe D, by
    rw [im_cmTauCoe]
    have : (0 : ℝ) < |(D : ℝ)| := abs_pos.mpr (by exact_mod_cast hD.ne)
    positivity⟩

/-- The underlying complex number of `τ_D`. -/
theorem coe_cmTau {D : ℤ} (hD : D < 0) : (cmTau D hD : ℂ) = cmTauCoe D := (rfl)

/-- The imaginary part of `τ_D` is `√|D| / 2`. -/
theorem im_cmTau {D : ℤ} (hD : D < 0) : (cmTau D hD).im = √|(D : ℝ)| / 2 :=
  im_cmTauCoe D

/-- **`τ_D` is a root of `X² + B X + C`.** -/
theorem cmTau_sq_add {D : ℤ} (hD : D < 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    (cmTau D hD : ℂ) ^ 2 + cmTauLinearCoeff D * (cmTau D hD : ℂ) + cmTauConstCoeff D = 0 := by
  have hr : ((√|(D : ℝ)| : ℝ) : ℂ) ^ 2 = -(D : ℂ) := by
    rw [← ofReal_pow, Real.sq_sqrt (abs_nonneg _), abs_of_neg (by exact_mod_cast hD)]
    push_cast
    ring
  rw [coe_cmTau]
  unfold cmTauCoe cmTauLinearCoeff cmTauConstCoeff
  split_ifs with h
  · obtain ⟨k, rfl⟩ : (4 : ℤ) ∣ D := Int.dvd_of_emod_eq_zero h
    rw [show -(4 * k) / 4 = -k by omega]
    push_cast at hr ⊢
    linear_combination (((√|(4 * k : ℝ)| : ℝ) : ℂ) ^ 2 / 4) * I_sq - (1 / 4) * hr
  · obtain ⟨k, rfl⟩ : ∃ k, D = 4 * k + 1 := ⟨D / 4, by omega⟩
    rw [show (9 - (4 * k + 1)) / 4 = 2 - k by omega]
    push_cast at hr ⊢
    linear_combination (((√|(4 * k + 1 : ℝ)| : ℝ) : ℂ) ^ 2 / 4) * I_sq - (1 / 4) * hr

section Matrix

variable {R : Type*} [CommRing R]

/-- **The multiplication matrix** `[[t - B s, -C s], [s, t]]`: the matrix of multiplication by
`t + s τ` on the basis `(τ, 1)`, for `τ` a root of `X² + B X + C`. -/
@[expose] def cmMulMatrix (B C s t : R) : Matrix (Fin 2) (Fin 2) R :=
  !![t - B * s, -C * s; s, t]

/-- **The column `(τ, 1)` is an eigenvector** of the multiplication matrix of `t + s τ`, with
eigenvalue `t + s τ`. -/
theorem cmMulMatrix_mulVec {B C x : R} (hx : x ^ 2 + B * x + C = 0) (s t : R) :
    (cmMulMatrix B C s t).mulVec ![x, 1] = (t + s * x) • ![x, 1] := by
  ext i
  fin_cases i
  · simp [cmMulMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination (-s) * hx
  · simp [cmMulMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- **The determinant of a multiplication matrix is the norm** `t² - B s t + C s²` of
`t + s τ`. -/
theorem det_cmMulMatrix (B C s t : R) :
    (cmMulMatrix B C s t).det = t ^ 2 - B * s * t + C * s ^ 2 := by
  rw [cmMulMatrix, Matrix.det_fin_two_of]
  ring

/-- **The multiplication matrices multiply as the elements do**: with `τ² = -B τ - C`,
`(t + s τ)(t' + s' τ) = (t t' - C s s') + (t s' + s t' - B s s') τ`. -/
theorem cmMulMatrix_mul (B C s t s' t' : R) :
    cmMulMatrix B C s t * cmMulMatrix B C s' t' =
      cmMulMatrix B C (t * s' + s * t' - B * s * s') (t * t' - C * s * s') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cmMulMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The multiplication matrix of `1` is the identity. -/
theorem cmMulMatrix_zero_one (B C : R) : cmMulMatrix B C 0 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cmMulMatrix]

/-- The multiplication matrix of `-(t + s τ)` is the negative of that of `t + s τ`. -/
theorem cmMulMatrix_neg (B C s t : R) : cmMulMatrix B C (-s) (-t) = -cmMulMatrix B C s t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cmMulMatrix]
  ring

/-- Forming multiplication matrices commutes with ring homomorphisms, in particular with reduction
modulo `N`. -/
theorem map_cmMulMatrix {S : Type*} [CommRing S] (f : R →+* S) (B C s t : R) :
    (cmMulMatrix B C s t).map f = cmMulMatrix (f B) (f C) (f s) (f t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cmMulMatrix]

/-- Four times the norm form is `(2t - B s)² + (4C - B²) s²`. -/
theorem four_mul_cmNormForm (B C s t : R) :
    4 * (t ^ 2 - B * s * t + C * s ^ 2) = (2 * t - B * s) ^ 2 + (4 * C - B ^ 2) * s ^ 2 := by
  ring

end Matrix

section Units

/-- **Units of `ℤ[τ_D]` away from `D = -3, -4`**: if `B² - 4C < -4`, the only solutions of
`t² - B s t + C s² = 1` are `(s, t) = (0, ±1)`. -/
theorem cmNormForm_eq_one_iff_of_lt_neg_four {B C : ℤ} (hD : B ^ 2 - 4 * C < -4) (s t : ℤ) :
    t ^ 2 - B * s * t + C * s ^ 2 = 1 ↔ s = 0 ∧ (t = 1 ∨ t = -1) := by
  constructor
  · intro h
    have h4 := four_mul_cmNormForm B C s t
    rw [h] at h4
    have hs : s = 0 := by
      by_contra hs
      have : 1 ≤ s ^ 2 := by
        have := sq_nonneg s
        have : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
        omega
      nlinarith [sq_nonneg (2 * t - B * s)]
    subst hs
    have : (t - 1) * (t + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact ⟨rfl, Or.inl (by linarith)⟩
    · exact ⟨rfl, Or.inr (by linarith)⟩
  · rintro ⟨rfl, rfl | rfl⟩ <;> ring

/-- **The four units of `ℤ[i]`**: for `D = -4` (`B = 0`, `C = 1`) the solutions of
`t² + s² = 1` are `(s, t) = (0, ±1), (±1, 0)`. -/
theorem cmNormForm_eq_one_iff_neg_four (s t : ℤ) :
    t ^ 2 - cmTauLinearCoeff (-4) * s * t + cmTauConstCoeff (-4) * s ^ 2 = 1 ↔
      (s = 0 ∧ (t = 1 ∨ t = -1)) ∨ (t = 0 ∧ (s = 1 ∨ s = -1)) := by
  simp only [cmTauLinearCoeff, cmTauConstCoeff]
  norm_num
  constructor
  · intro h
    have hs : s ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
    have ht : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
    have hs' : -1 ≤ s ∧ s ≤ 1 := ⟨by nlinarith, by nlinarith⟩
    have ht' : -1 ≤ t ∧ t ≤ 1 := ⟨by nlinarith, by nlinarith⟩
    obtain ⟨hs1, hs2⟩ := hs'
    obtain ⟨ht1, ht2⟩ := ht'
    interval_cases s <;> interval_cases t <;> simp_all
  · rintro (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩) <;> norm_num

/-- **The six units of `ℤ[ζ₃]`**: for `D = -3` (`B = -3`, `C = 3`) the solutions of
`t² + 3 s t + 3 s² = 1` are `(s, t) = (0, ±1), (1, -1), (1, -2), (-1, 1), (-1, 2)`. -/
theorem cmNormForm_eq_one_iff_neg_three (s t : ℤ) :
    t ^ 2 - cmTauLinearCoeff (-3) * s * t + cmTauConstCoeff (-3) * s ^ 2 = 1 ↔
      (s = 0 ∧ (t = 1 ∨ t = -1)) ∨ (s = 1 ∧ (t = -1 ∨ t = -2)) ∨
        (s = -1 ∧ (t = 1 ∨ t = 2)) := by
  simp only [cmTauLinearCoeff, cmTauConstCoeff]
  norm_num
  constructor
  · intro h
    have h4 : (2 * t + 3 * s) ^ 2 + 3 * s ^ 2 = 4 := by linear_combination 4 * h
    have hs : -1 ≤ s ∧ s ≤ 1 := ⟨by nlinarith [sq_nonneg (2 * t + 3 * s)],
      by nlinarith [sq_nonneg (2 * t + 3 * s)]⟩
    have ht : -2 ≤ 2 * t + 3 * s ∧ 2 * t + 3 * s ≤ 2 :=
      ⟨by nlinarith [sq_nonneg s], by nlinarith [sq_nonneg s]⟩
    obtain ⟨hs1, hs2⟩ := hs
    have ht1 : -3 ≤ t := by omega
    have ht2 : t ≤ 3 := by omega
    interval_cases s <;> interval_cases t <;> simp_all
  · rintro (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩) <;> norm_num

end Units

end TauCeti
