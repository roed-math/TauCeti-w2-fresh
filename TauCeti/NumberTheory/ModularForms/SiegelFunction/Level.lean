/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Basic

/-!
# Siegel functions under the translations of `Γ(N)`

The translation `T^N = [[1, N], [0, 1]]` lies in the principal congruence subgroup `Γ(N)`. This
file computes the exact root of unity by which a Siegel function `g_r` with `N r₁ ∈ ℤ` changes
under `τ ↦ τ + N`, the first of the explicit `Γ(N)` transformation phases of Kubert–Lang.

## Main results

* `TauCeti.ModularForm.siegelFunction_apply_add_natCast`:
  `g_r(τ + n) = e^{π i n / 6} g_{(r₁, n r₁ + r₂)}(τ)`, the transformation under `T^n`.
* `TauCeti.ModularForm.siegelFunction_apply_add_natCast_of_mul_eq`: if `N r₁ = a ∈ ℤ`, then
  `g_r(τ + N) = e^{π i N / 6} (-1)^a e^{π i a r₁} g_r(τ)`.
* `TauCeti.ModularForm.siegelFunction_pow_apply_add_natCast_of_mul_eq`: if `N r₁ ∈ ℤ`, then
  `g_r^{12N / gcd(6, N)}` is invariant under `τ ↦ τ + N`.

## References

* D. S. Kubert, S. Lang, *Modular Units*, Grundlehren der mathematischen Wissenschaften 244,
  Chapter 2, §1 (K 1–K 3) and Chapter 3, §5.
-/

public section

open Complex Real

namespace TauCeti.ModularForm

/-- **The translation `τ ↦ τ + n`**: `g_r(τ + n) = e^{π i n / 6} g_{r Tⁿ}(τ)`, where
`r Tⁿ = (r₁, n r₁ + r₂)` is the row vector `r` multiplied on the right by
`Tⁿ = [[1, n], [0, 1]]`. -/
theorem siegelFunction_apply_add_natCast (r : Fin 2 → ℝ) (n : ℕ) (τ : ℂ) :
    siegelFunction r (τ + n) = cexp (π * I * n / 6) * siegelFunction ![r 0, n * r 0 + r 1] τ := by
  induction n generalizing τ with
  | zero =>
    have hr : ![r 0, (0 : ℕ) * r 0 + r 1] = r := by
      ext i; fin_cases i <;> simp
    rw [hr]
    simp
  | succ n ih =>
    have hτ : τ + ((n + 1 : ℕ) : ℂ) = τ + 1 + n := by push_cast; ring
    have hr : ![r 0, r 0 + (n * r 0 + r 1)] = ![r 0, ((n + 1 : ℕ) : ℝ) * r 0 + r 1] := by
      congr 2
      push_cast
      ring
    rw [hτ, ih, siegelFunction_apply_add_one]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hr,
      ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring

/-- **The translation `T^N` of `Γ(N)`.** If `N r₁ = a` is an integer, then `τ ↦ τ + N` multiplies
`g_r` by the root of unity `e^{π i N / 6} (-1)^a e^{π i a r₁}`. -/
theorem siegelFunction_apply_add_natCast_of_mul_eq (r : Fin 2 → ℝ) {N : ℕ} {a : ℤ}
    (ha : N * r 0 = a) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction r (τ + N) =
      cexp (π * I * N / 6) * (-1) ^ a * cexp (π * I * a * r 0) * siegelFunction r τ := by
  have hr : ![r 0, N * r 0 + r 1] = r + fun i ↦ ((![0, a] : Fin 2 → ℤ) i : ℝ) := by
    ext i; fin_cases i <;> simp [ha, add_comm]
  rw [siegelFunction_apply_add_natCast, hr, siegelFunction_add_intCast _ _ hτ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_zero,
    zero_mul, zero_add, zero_sub]
  have he : cexp (-(π * I * -((a : ℝ) * r 0 : ℂ))) = cexp (π * I * a * r 0) := by
    congr 1
    push_cast
    ring
  push_cast at he ⊢
  rw [he]
  ring

/-- **The power `12N / gcd(6, N)` under `T^N`.** If `N r₁` is an integer, then
`g_r^{12N / gcd(6, N)}` is invariant under the translation `τ ↦ τ + N` of `Γ(N)`. -/
theorem siegelFunction_pow_apply_add_natCast_of_mul_eq (r : Fin 2 → ℝ) {N : ℕ} {a : ℤ}
    (ha : N * r 0 = a) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction r (τ + N) ^ (12 * N / Nat.gcd 6 N) =
      siegelFunction r τ ^ (12 * N / Nat.gcd 6 N) := by
  set g := Nat.gcd 6 N
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (by norm_num)
  obtain ⟨k, hk⟩ : g ∣ N := Nat.gcd_dvd_right 6 N
  obtain ⟨l, hl⟩ : g ∣ 6 := Nat.gcd_dvd_left 6 N
  have hm : 12 * N / g = 12 * k := by
    rw [hk, mul_left_comm, Nat.mul_div_cancel_left _ hg]
  have hneg : (-1 : ℂ) ^ a = cexp (a * (π * I)) := by
    rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have hk' : (N : ℂ) = g * k := by exact_mod_cast hk
  have hl' : (6 : ℂ) = g * l := by exact_mod_cast hl
  have ha' : (N : ℂ) * (r 0 : ℂ) = a := by exact_mod_cast ha
  have key : (6 * k * a * r 0 : ℂ) = l * a ^ 2 := by
    linear_combination (k * a * r 0 : ℂ) * hl' - (l * a * r 0 : ℂ) * hk' + (l * a : ℂ) * ha'
  rw [siegelFunction_apply_add_natCast_of_mul_eq r ha hτ, hm, mul_pow, hneg, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_nat_mul]
  convert one_mul _
  rw [Complex.exp_eq_one_iff]
  refine ⟨k * N + 6 * k * a + l * a ^ 2, ?_⟩
  push_cast
  linear_combination (2 * π * I) * key

end TauCeti.ModularForm
