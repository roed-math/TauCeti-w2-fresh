/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Product
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# Siegel functions under `Γ(N)`

The upper and lower translations `T^N = [[1, N], [0, 1]]` and `L^N = [[1, 0], [N, 1]]` lie in the
principal congruence subgroup `Γ(N)`. This file computes the exact roots of unity by which a Siegel
function `g_r` changes under `τ ↦ τ + N` (when `N r₁ ∈ ℤ`) and under `τ ↦ τ / (N τ + 1)` (when
`N r₂ ∈ ℤ`), the first of the explicit `Γ(N)` transformation phases of Kubert–Lang, and deduces
that `g_r^{12N / gcd(6, N)}` is invariant under both. For finite products `∏ g_r^{m(r)}` it proves
the corresponding half of the Kubert–Lang congruence criterion: if `12 ∣ ∑ m(r)` and
`gcd(2, N) N ∣ ∑ m(r) (N r₁)²` (resp. `∑ m(r) (N r₂)²`), the product is invariant under `T^N`
(resp. `L^N`).

For a general `γ = 1 + N [[u, w], [v, z]] ∈ Γ(N)` the `SL₂(ℤ)` law contributes a twelfth root of
unity depending only on `γ`, and `r γ - r ∈ ℤ²` contributes an explicit `2N`-th root of unity. This
gives the invariance of `g_r^{12N / gcd(6, N)}` under all of `Γ(N)`, and the full Kubert–Lang
congruence criterion: the quadratic conditions on `(N r₁)²`, `(N r₂)²` and `(N r₁)(N r₂)` make
`∏ g_r^{m(r)}` invariant under `Γ(N)`.

## Main results

* `TauCeti.ModularForm.siegelFunction_apply_add_natCast`:
  `g_r(τ + n) = e^{π i n / 6} g_{(r₁, n r₁ + r₂)}(τ)`, the transformation under `T^n`.
* `TauCeti.ModularForm.siegelFunction_apply_add_natCast_of_mul_eq`: if `N r₁ = a ∈ ℤ`, then
  `g_r(τ + N) = e^{π i N / 6} (-1)^a e^{π i a r₁} g_r(τ)`.
* `TauCeti.ModularForm.siegelFunction_pow_apply_add_natCast_of_mul_eq`: if `N r₁ ∈ ℤ`, then
  `g_r^{12N / gcd(6, N)}` is invariant under `τ ↦ τ + N`.
* `TauCeti.ModularForm.siegelFunction_apply_div_natCast_mul_add_one`:
  `g_r(τ / (n τ + 1)) = e^{-π i n / 6} g_{(r₁ + n r₂, r₂)}(τ)`, the transformation under `Lⁿ`.
* `TauCeti.ModularForm.siegelFunction_apply_div_natCast_mul_add_one_of_mul_eq`: if `N r₂ = b ∈ ℤ`,
  then `g_r(τ / (N τ + 1)) = e^{-π i N / 6} (-1)^b e^{-π i b r₂} g_r(τ)`.
* `TauCeti.ModularForm.siegelFunction_pow_apply_div_natCast_mul_add_one_of_mul_eq`: if `N r₂ ∈ ℤ`,
  then `g_r^{12N / gcd(6, N)}` is invariant under `τ ↦ τ / (N τ + 1)`.
* `TauCeti.ModularForm.siegelProduct_apply_add_natCast_of_dvd`,
  `TauCeti.ModularForm.siegelProduct_apply_div_natCast_mul_add_one_of_dvd`: the congruence
  criterion for a Siegel product `∏ g_r^{m(r)}` to be invariant under `T^N` and under `L^N`.
* `TauCeti.ModularForm.siegelFunction_pow_smul_of_mem_Gamma`: if `N r ∈ ℤ²`, then
  `g_r^{12N / gcd(6, N)}` is invariant under `Γ(N)`.
* `TauCeti.ModularForm.siegelProduct_smul_of_mem_Gamma`: the Kubert–Lang congruence criterion
  for `∏ g_r^{m(r)}` to be invariant under `Γ(N)`.

## References

* D. S. Kubert, S. Lang, *Modular Units*, Grundlehren der mathematischen Wissenschaften 244,
  Chapter 2, §1 (K 1–K 3) and Chapter 3, §5.
-/

public section

open Complex Real
open scoped MatrixGroups UpperHalfPlane

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

/-- The phase `e^{π i N / 6} (-1)^a e^{π i a x}` of the `Γ(N)` translations, for `N x = a ∈ ℤ`, is
a root of unity of order dividing `12N / gcd(6, N)`. -/
private theorem translationPhase_pow_eq_one {N : ℕ} {x : ℝ} {a : ℤ} (ha : N * x = a) :
    (cexp (π * I * N / 6) * (-1) ^ a * cexp (π * I * a * x)) ^ (12 * N / Nat.gcd 6 N) = 1 := by
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
  have ha' : (N : ℂ) * (x : ℂ) = a := by exact_mod_cast ha
  have key : (6 * k * a * x : ℂ) = l * a ^ 2 := by
    linear_combination (k * a * x : ℂ) * hl' - (l * a * x : ℂ) * hk' + (l * a : ℂ) * ha'
  rw [hm, hneg, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_nat_mul,
    Complex.exp_eq_one_iff]
  refine ⟨k * N + 6 * k * a + l * a ^ 2, ?_⟩
  push_cast
  linear_combination (2 * π * I) * key

/-- **The power `12N / gcd(6, N)` under `T^N`.** If `N r₁` is an integer, then
`g_r^{12N / gcd(6, N)}` is invariant under the translation `τ ↦ τ + N` of `Γ(N)`. -/
theorem siegelFunction_pow_apply_add_natCast_of_mul_eq (r : Fin 2 → ℝ) {N : ℕ} {a : ℤ}
    (ha : N * r 0 = a) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction r (τ + N) ^ (12 * N / Nat.gcd 6 N) =
      siegelFunction r τ ^ (12 * N / Nat.gcd 6 N) := by
  rw [siegelFunction_apply_add_natCast_of_mul_eq r ha hτ, mul_pow,
    translationPhase_pow_eq_one ha, one_mul]

/-- The product over a finite exponent family `m` of the translation phases
`e^{π i N / 6} (-1)^{a_r} e^{π i a_r x_r}`, for `N x_r = a_r ∈ ℤ`, is `1` under the congruence
conditions of Kubert–Lang: `12 ∣ ∑ m(r)` and `gcd(2, N) N ∣ ∑ m(r) a_r²`. -/
private theorem prod_translationPhase_zpow_eq_one {N : ℕ} (hN : N ≠ 0) {m : (Fin 2 → ℝ) →₀ ℤ}
    (x : (Fin 2 → ℝ) → ℝ) (a : (Fin 2 → ℝ) → ℤ) (ha : ∀ r ∈ m.support, N * x r = a r)
    (h12 : (12 : ℤ) ∣ m.sum fun _ k ↦ k)
    (hsq : (Nat.gcd 2 N * N : ℤ) ∣ m.sum fun r k ↦ k * a r ^ 2) :
    ∏ r ∈ m.support, (cexp (π * I * N / 6) * (-1) ^ a r * cexp (π * I * a r * x r)) ^ m r = 1 := by
  obtain ⟨s, hs⟩ := h12
  obtain ⟨t, ht⟩ := hsq
  simp only [Finsupp.sum] at hs ht
  -- `∑ m(r) a_r ≡ ∑ m(r) a_r² = gcd(2, N) N t (mod 2)`, and `gcd(2, N) t (N + 1)` is even.
  obtain ⟨u, hu⟩ : (2 : ℤ) ∣ (∑ r ∈ m.support, m r * a r) + Nat.gcd 2 N * t := by
    have h₁ : (2 : ℤ) ∣ (∑ r ∈ m.support, m r * a r ^ 2) - ∑ r ∈ m.support, m r * a r := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.dvd_sum fun r _ ↦ ?_
      rw [show m r * a r ^ 2 - m r * a r = m r * (a r * (a r - 1)) by ring]
      exact (Int.even_mul_pred_self (a r)).two_dvd.mul_left _
    have h₂ : (2 : ℤ) ∣ Nat.gcd 2 N * t * (N + 1) := by
      rcases Nat.even_or_odd N with he | ho
      · rw [Nat.gcd_eq_left he.two_dvd]
        exact ((dvd_refl _).mul_right _).mul_right _
      · exact (by exact_mod_cast ho.add_one.two_dvd : (2 : ℤ) ∣ N + 1).mul_left _
    rw [ht] at h₁
    convert dvd_sub h₂ h₁ using 1
    ring
  have hQ : ∑ r ∈ m.support, (m r : ℂ) * a r * x r = Nat.gcd 2 N * t := by
    refine mul_left_cancel₀ (Nat.cast_ne_zero.mpr hN) ?_
    have hsum : ∑ r ∈ m.support, (N : ℂ) * ((m r : ℂ) * a r * x r) =
        ((∑ r ∈ m.support, m r * a r ^ 2 : ℤ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun r hr ↦ ?_
      have h : (N : ℂ) * (x r : ℂ) = a r := by exact_mod_cast ha r hr
      linear_combination (m r * a r : ℂ) * h
    rw [Finset.mul_sum, hsum, ht]
    push_cast
    ring
  have hphase : ∀ r : Fin 2 → ℝ,
      (cexp (π * I * N / 6) * (-1) ^ a r * cexp (π * I * a r * x r)) ^ m r =
        cexp (m r * (π * I * N / 6 + a r * (π * I) + π * I * a r * x r)) := fun r ↦ by
    rw [Complex.exp_int_mul, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul (π * I),
      Complex.exp_pi_mul_I]
  have hexp : ∑ r ∈ m.support, (m r : ℂ) * (π * I * N / 6 + a r * (π * I) + π * I * a r * x r) =
      π * I * N / 6 * ∑ r ∈ m.support, (m r : ℂ) + π * I * ∑ r ∈ m.support, (m r : ℂ) * a r +
        π * I * ∑ r ∈ m.support, (m r : ℂ) * a r * x r := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ ↦ by ring
  have hs' : ∑ r ∈ m.support, (m r : ℂ) = 12 * s := by exact_mod_cast hs
  have hu' : ∑ r ∈ m.support, (m r : ℂ) * a r + Nat.gcd 2 N * t = 2 * u := by exact_mod_cast hu
  simp_rw [hphase]
  rw [← Complex.exp_sum, Complex.exp_eq_one_iff, hexp, hs', hQ]
  refine ⟨N * s + u, ?_⟩
  push_cast
  linear_combination (π * I) * hu'

/-- **The congruence criterion under `T^N`.** Let `m` be a finite exponent family supported on
vectors `r` with `N r₁ = a_r ∈ ℤ`. If `12 ∣ ∑ m(r)` and `gcd(2, N) N ∣ ∑ m(r) a_r²`, then the Siegel
product `∏ g_r^{m(r)}` is invariant under the translation `τ ↦ τ + N` of `Γ(N)`. -/
theorem siegelProduct_apply_add_natCast_of_dvd {N : ℕ} {m : (Fin 2 → ℝ) →₀ ℤ}
    (a : (Fin 2 → ℝ) → ℤ) (ha : ∀ r ∈ m.support, N * r 0 = a r)
    (h12 : (12 : ℤ) ∣ m.sum fun _ k ↦ k)
    (hsq : (Nat.gcd 2 N * N : ℤ) ∣ m.sum fun r k ↦ k * a r ^ 2) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelProduct m (τ + N) = siegelProduct m τ := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  rw [siegelProduct_def, siegelProduct_def, Finsupp.prod, Finsupp.prod,
    Finset.prod_congr rfl fun r hr ↦ by
      rw [siegelFunction_apply_add_natCast_of_mul_eq r (ha r hr) hτ, mul_zpow],
    Finset.prod_mul_distrib, prod_translationPhase_zpow_eq_one hN (fun r ↦ r 0) a ha h12 hsq,
    one_mul]

/-- **The lower translation `τ ↦ τ / (n τ + 1)`**:
`g_r(τ / (n τ + 1)) = e^{-π i n / 6} g_{r Lⁿ}(τ)`, where `r Lⁿ = (r₁ + n r₂, r₂)` is the row
vector `r` multiplied on the right by `Lⁿ = [[1, 0], [n, 1]] = S T⁻ⁿ S⁻¹`. -/
theorem siegelFunction_apply_div_natCast_mul_add_one (r : Fin 2 → ℝ) (n : ℕ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    siegelFunction r (τ / (n * τ + 1)) =
      cexp (-(π * I * n / 6)) * siegelFunction ![r 0 + n * r 1, r 1] τ := by
  have hτ₀ : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  have hσ := im_neg_one_div_pos hτ
  set w := -1 / τ - n with hw_def
  have hw : 0 < w.im := by simpa [hw_def] using hσ
  have hw₀ : w ≠ 0 := fun h ↦ by simp [h] at hw
  have hden : (n : ℂ) * τ + 1 = -τ * w := by
    rw [hw_def]; field_simp; ring
  have hτw : τ / (n * τ + 1) = -1 / w := by
    rw [hden]; field_simp
  have h₁ := siegelFunction_apply_add_natCast ![r 1, -r 0 - n * r 1] n w
  have hs : ![(![r 1, -r 0 - n * r 1] : Fin 2 → ℝ) 0,
      n * (![r 1, -r 0 - n * r 1] : Fin 2 → ℝ) 0 + (![r 1, -r 0 - n * r 1] : Fin 2 → ℝ) 1] =
      ![r 1, -r 0] := by
    ext i; fin_cases i <;> simp
  rw [hs, show w + n = -1 / τ by rw [hw_def]; ring] at h₁
  have h₂ := siegelFunction_apply_neg_one_div ![r 1, -r 0 - n * r 1] hτ
  have hv : ![(![r 1, -r 0 - n * r 1] : Fin 2 → ℝ) 1, -(![r 1, -r 0 - n * r 1] : Fin 2 → ℝ) 0] =
      -![r 0 + n * r 1, r 1] := by
    ext i; fin_cases i <;> simp; ring
  rw [hv, siegelFunction_neg _ hτ] at h₂
  have hE : cexp (-(π * I * n / 6)) * cexp (π * I * n / 6) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  rw [hτw, siegelFunction_apply_neg_one_div r hw]
  linear_combination (I * siegelFunction ![r 1, -r 0] w) * hE +
    (I * cexp (-(π * I * n / 6))) * (h₂.symm.trans h₁) +
    -(cexp (-(π * I * n / 6)) * siegelFunction ![r 0 + n * r 1, r 1] τ) * I_sq

/-- **The lower translation `L^N` of `Γ(N)`.** If `N r₂ = b` is an integer, then
`τ ↦ τ / (N τ + 1)` multiplies `g_r` by the root of unity `e^{-π i N / 6} (-1)^b e^{-π i b r₂}`. -/
theorem siegelFunction_apply_div_natCast_mul_add_one_of_mul_eq (r : Fin 2 → ℝ) {N : ℕ} {b : ℤ}
    (hb : N * r 1 = b) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction r (τ / (N * τ + 1)) =
      cexp (-(π * I * N / 6)) * (-1) ^ b * cexp (-(π * I * b * r 1)) * siegelFunction r τ := by
  have hr : ![r 0 + N * r 1, r 1] = r + fun i ↦ ((![b, 0] : Fin 2 → ℤ) i : ℝ) := by
    ext i; fin_cases i <;> simp [hb]
  rw [siegelFunction_apply_div_natCast_mul_add_one r N hτ, hr, siegelFunction_add_intCast _ _ hτ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_zero,
    mul_zero, zero_add, add_zero, zero_mul, sub_zero, mul_assoc]

/-- **The power `12N / gcd(6, N)` under `L^N`.** If `N r₂` is an integer, then
`g_r^{12N / gcd(6, N)}` is invariant under the lower translation `τ ↦ τ / (N τ + 1)` of `Γ(N)`. -/
theorem siegelFunction_pow_apply_div_natCast_mul_add_one_of_mul_eq (r : Fin 2 → ℝ) {N : ℕ}
    {b : ℤ} (hb : N * r 1 = b) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction r (τ / (N * τ + 1)) ^ (12 * N / Nat.gcd 6 N) =
      siegelFunction r τ ^ (12 * N / Nat.gcd 6 N) := by
  have hinv : cexp (-(π * I * N / 6)) * (-1) ^ b * cexp (-(π * I * b * r 1)) =
      (cexp (π * I * N / 6) * (-1) ^ b * cexp (π * I * b * r 1))⁻¹ := by
    rw [mul_inv, mul_inv, ← Complex.exp_neg, ← Complex.exp_neg, ← inv_zpow, inv_neg, inv_one]
  rw [siegelFunction_apply_div_natCast_mul_add_one_of_mul_eq r hb hτ, hinv, mul_pow, inv_pow,
    translationPhase_pow_eq_one hb, inv_one, one_mul]

/-- **The congruence criterion under `L^N`.** Let `m` be a finite exponent family supported on
vectors `r` with `N r₂ = b_r ∈ ℤ`. If `12 ∣ ∑ m(r)` and `gcd(2, N) N ∣ ∑ m(r) b_r²`, then the Siegel
product `∏ g_r^{m(r)}` is invariant under the lower translation `τ ↦ τ / (N τ + 1)` of `Γ(N)`. -/
theorem siegelProduct_apply_div_natCast_mul_add_one_of_dvd {N : ℕ} {m : (Fin 2 → ℝ) →₀ ℤ}
    (b : (Fin 2 → ℝ) → ℤ) (hb : ∀ r ∈ m.support, N * r 1 = b r)
    (h12 : (12 : ℤ) ∣ m.sum fun _ k ↦ k)
    (hsq : (Nat.gcd 2 N * N : ℤ) ∣ m.sum fun r k ↦ k * b r ^ 2) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelProduct m (τ / (N * τ + 1)) = siegelProduct m τ := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  have hinv : ∀ r : Fin 2 → ℝ,
      cexp (-(π * I * N / 6)) * (-1) ^ b r * cexp (-(π * I * b r * r 1)) =
        (cexp (π * I * N / 6) * (-1) ^ b r * cexp (π * I * b r * r 1))⁻¹ := fun r ↦ by
    rw [mul_inv, mul_inv, ← Complex.exp_neg, ← Complex.exp_neg, ← inv_zpow, inv_neg, inv_one]
  rw [siegelProduct_def, siegelProduct_def, Finsupp.prod, Finsupp.prod,
    Finset.prod_congr rfl fun r hr ↦ by
      rw [siegelFunction_apply_div_natCast_mul_add_one_of_mul_eq r (hb r hr) hτ, hinv, mul_zpow,
        inv_zpow],
    Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    prod_translationPhase_zpow_eq_one hN (fun r ↦ r 1) b hb h12 hsq, inv_one, one_mul]

/-- The phase `(-1)^n e^{-π i x}` of an integral translation of `r ∈ N⁻¹ℤ²`, where `N x ∈ ℤ`,
is a root of unity of order dividing `12N / gcd(6, N)`. -/
private theorem integralTranslationPhase_pow_eq_one {N : ℕ} {x : ℂ} {c : ℤ} (hc : N * x = c)
    (n : ℤ) : ((-1) ^ n * cexp (-(π * I * x))) ^ (12 * N / Nat.gcd 6 N) = 1 := by
  set g := Nat.gcd 6 N
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (by norm_num)
  obtain ⟨k, hk⟩ : g ∣ N := Nat.gcd_dvd_right 6 N
  obtain ⟨l, hl⟩ : g ∣ 6 := Nat.gcd_dvd_left 6 N
  have hm : 12 * N / g = 12 * k := by
    rw [hk, mul_left_comm, Nat.mul_div_cancel_left _ hg]
  have hneg : (-1 : ℂ) ^ n = cexp (n * (π * I)) := by
    rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have hk' : (N : ℂ) = g * k := by exact_mod_cast hk
  have hl' : (6 : ℂ) = g * l := by exact_mod_cast hl
  have key : (6 * k * x : ℂ) = l * c := by
    linear_combination (k * x : ℂ) * hl' - (l * x : ℂ) * hk' + (l : ℂ) * hc
  rw [hm, hneg, ← Complex.exp_add, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨6 * k * n - l * c, ?_⟩
  push_cast
  linear_combination (-2 * π * I) * key

/-- **The exact phase on `Γ(N)`.** For `γ ∈ Γ(N)`, write `γ = 1 + N [[u, w], [v, z]]`. There is a
twelfth root of unity `ε`, depending only on `γ`, such that for every `r` with `N r = (a, b) ∈ ℤ²`,
`g_r(γ τ) = ε (-1)^{s₁ s₂ + s₁ + s₂} e^{-π i (s₁ r₂ - s₂ r₁)} g_r(τ)`, where
`(s₁, s₂) = (a u + b v, a w + b z) = r γ - r`. -/
private theorem exists_siegelFunction_smul_eq_of_mem_Gamma {N : ℕ} (hN : N ≠ 0) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    ∃ ε : ℂ, ε ^ 12 = 1 ∧ ∃ u v w z : ℤ, u + z + N * (u * z - v * w) = 0 ∧
      ∀ (r : Fin 2 → ℝ) (a b : ℤ), N * r 0 = a → N * r 1 = b → ∀ τ : ℍ,
        siegelFunction r ↑(γ • τ) = ε * ((-1) ^ ((a * u + b * v) * (a * w + b * z) +
          (a * u + b * v) + (a * w + b * z)) * cexp (-(π * I * (((a * u + b * v : ℤ) : ℂ) * r 1 -
            ((a * w + b * z : ℤ) : ℂ) * r 0)))) * siegelFunction r τ := by
  obtain ⟨ε, hε, hγε⟩ := exists_siegelFunction_smul_eq_mul γ
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  obtain ⟨h00, h01, h10, h11⟩ := hγ
  obtain ⟨u, hu⟩ : (N : ℤ) ∣ γ 0 0 - 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (by simpa using h00.symm)
  obtain ⟨w, hw⟩ : (N : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h01
  obtain ⟨v, hv⟩ : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h10
  obtain ⟨z, hz⟩ : (N : ℤ) ∣ γ 1 1 - 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (by simpa using h11.symm)
  have hdet : u + z + N * (u * z - v * w) = 0 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    refine mul_left_cancel₀ (Int.natCast_ne_zero.mpr hN) ?_
    linear_combination h - (γ 1 1 : ℤ) * hu - (1 + N * u) * hz + (γ 1 0 : ℤ) * hw + N * w * hv
  refine ⟨ε, hε, u, v, w, z, hdet, fun r a b ha hb τ ↦ ?_⟩
  have hu' : ((γ 0 0 : ℤ) : ℝ) = 1 + N * u := by
    rw [show (γ 0 0 : ℤ) = 1 + (γ 0 0 - 1) by ring, hu]; push_cast; ring
  have hz' : ((γ 1 1 : ℤ) : ℝ) = 1 + N * z := by
    rw [show (γ 1 1 : ℤ) = 1 + (γ 1 1 - 1) by ring, hz]; push_cast; ring
  have hw' : ((γ 0 1 : ℤ) : ℝ) = N * w := by rw [hw]; push_cast; ring
  have hv' : ((γ 1 0 : ℤ) : ℝ) = N * v := by rw [hv]; push_cast; ring
  have hrγ : Matrix.vecMul r ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) =
      r + fun i ↦ ((![a * u + b * v, a * w + b * z] : Fin 2 → ℤ) i : ℝ) := by
    ext i
    fin_cases i <;>
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hu', hz', hw', hv', ← ha, ← hb] <;> ring
  rw [hγε, hrγ, siegelFunction_add_intCast _ _ τ.im_pos]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_assoc]

/-- **The power `12N / gcd(6, N)` under `Γ(N)`.** If `N r ∈ ℤ²`, then `g_r^{12N / gcd(6, N)}` is
invariant under the whole principal congruence subgroup `Γ(N)`: the `SL₂(ℤ)` law contributes a
twelfth root of unity, and `r γ - r ∈ ℤ²` contributes a `2N`-th root of unity. -/
theorem siegelFunction_pow_smul_of_mem_Gamma (r : Fin 2 → ℝ) {N : ℕ} {a b : ℤ}
    (ha : N * r 0 = a) (hb : N * r 1 = b) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) :
    siegelFunction r ↑(γ • τ) ^ (12 * N / Nat.gcd 6 N) =
      siegelFunction r τ ^ (12 * N / Nat.gcd 6 N) := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  obtain ⟨ε, hε, u, v, w, z, -, hγε⟩ := exists_siegelFunction_smul_eq_of_mem_Gamma hN hγ
  have hc : (N : ℂ) * (((a * u + b * v : ℤ) : ℂ) * r 1 - ((a * w + b * z : ℤ) : ℂ) * r 0) =
      ((a * u + b * v) * b - (a * w + b * z) * a : ℤ) := by
    have h0 : (N : ℂ) * (r 0 : ℂ) = a := by exact_mod_cast ha
    have h1 : (N : ℂ) * (r 1 : ℂ) = b := by exact_mod_cast hb
    push_cast
    linear_combination ((a : ℂ) * u + b * v) * h1 - ((a : ℂ) * w + b * z) * h0
  have hε' : ε ^ (12 * N / Nat.gcd 6 N) = 1 := by
    obtain ⟨k, hk⟩ : 12 ∣ 12 * N / Nat.gcd 6 N := Nat.dvd_div_of_mul_dvd <| by
      rw [mul_comm]; exact Nat.mul_dvd_mul_left 12 (Nat.gcd_dvd_right 6 N)
    rw [hk, pow_mul, hε, one_pow]
  rw [hγε r a b ha hb τ, mul_pow, mul_pow, hε', one_mul,
    integralTranslationPhase_pow_eq_one hc, one_mul]

/-- The product over a finite exponent family `m` of the phases of `g_r` under `γ ∈ Γ(N)` coming
from `r γ - r ∈ ℤ²` is `1` under the Kubert–Lang quadratic congruence conditions. -/
private theorem prod_congruencePhase_zpow_eq_one {N : ℕ} (hN : N ≠ 0) {u v w z : ℤ}
    (hdet : u + z + N * (u * z - v * w) = 0) {m : (Fin 2 → ℝ) →₀ ℤ}
    (a b : (Fin 2 → ℝ) → ℤ) (ha : ∀ r ∈ m.support, N * r 0 = a r)
    (hb : ∀ r ∈ m.support, N * r 1 = b r)
    (haa : (Nat.gcd 2 N * N : ℤ) ∣ m.sum fun r k ↦ k * a r ^ 2)
    (hbb : (Nat.gcd 2 N * N : ℤ) ∣ m.sum fun r k ↦ k * b r ^ 2)
    (hab : (N : ℤ) ∣ m.sum fun r k ↦ k * (a r * b r)) :
    ∏ r ∈ m.support, ((-1) ^ ((a r * u + b r * v) * (a r * w + b r * z) + (a r * u + b r * v) +
      (a r * w + b r * z)) * cexp (-(π * I * (((a r * u + b r * v : ℤ) : ℂ) * r 1 -
        ((a r * w + b r * z : ℤ) : ℂ) * r 0)))) ^ m r = 1 := by
  set g : ℤ := ((Nat.gcd 2 N : ℕ) : ℤ) with hg_def
  obtain ⟨α, hα⟩ := haa
  obtain ⟨β, hβ⟩ := hbb
  obtain ⟨κ, hκ⟩ := hab
  simp only [Finsupp.sum] at hα hβ hκ
  set s₀ : (Fin 2 → ℝ) → ℤ := fun r ↦ a r * u + b r * v with hs₀
  set s₁ : (Fin 2 → ℝ) → ℤ := fun r ↦ a r * w + b r * z with hs₁
  set n : (Fin 2 → ℝ) → ℤ := fun r ↦ s₀ r * s₁ r + s₀ r + s₁ r with hn
  -- `x ≡ x² (mod 2)` turns `∑ m(r) n_r` into a quadratic form in the sums of `hα`, `hβ`, `hκ`.
  have hD : (2 : ℤ) ∣ (∑ r ∈ m.support, m r * n r) -
      ((∑ r ∈ m.support, m r * a r ^ 2) * (u * w + u ^ 2 + w ^ 2) +
        (∑ r ∈ m.support, m r * b r ^ 2) * (v * z + v ^ 2 + z ^ 2) +
        (∑ r ∈ m.support, m r * (a r * b r)) * (u * z + v * w + 2 * u * v + 2 * w * z)) := by
    have h₀ : (2 : ℤ) ∣ ∑ r ∈ m.support, m r * (s₀ r * (s₀ r - 1)) :=
      Finset.dvd_sum fun r _ ↦ (Int.even_mul_pred_self (s₀ r)).two_dvd.mul_left _
    have h₁ : (2 : ℤ) ∣ ∑ r ∈ m.support, m r * (s₁ r * (s₁ r - 1)) :=
      Finset.dvd_sum fun r _ ↦ (Int.even_mul_pred_self (s₁ r)).two_dvd.mul_left _
    convert (dvd_add h₀ h₁).neg_right using 1
    simp only [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun r _ ↦ by simp only [hn, hs₀, hs₁]; ring
  rw [hα, hβ, hκ] at hD
  have hE : (2 : ℤ) ∣ g * N * α * (u * w + u ^ 2 + w ^ 2) + g * N * β * (v * z + v ^ 2 + z ^ 2) +
      N * κ * (u * z + v * w + 2 * u * v + 2 * w * z) - ((u - z) * κ + g * (v * β - w * α)) := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 ?_
    have hdet' := congrArg (Int.cast : ℤ → ZMod 2) hdet
    push_cast at hdet' ⊢
    rcases Nat.even_or_odd N with he | ho
    · have hN2 : (N : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff_even).2 he
      have hg2 : (g : ZMod 2) = 0 := by
        rw [hg_def, Nat.gcd_eq_left he.two_dvd]; rfl
      rw [hN2] at hdet' ⊢
      rw [hg2]
      generalize (u : ZMod 2) = u' at hdet' ⊢
      generalize (v : ZMod 2) = v' at hdet' ⊢
      generalize (w : ZMod 2) = w' at hdet' ⊢
      generalize (z : ZMod 2) = z' at hdet' ⊢
      generalize (α : ZMod 2) = α'
      generalize (β : ZMod 2) = β'
      generalize (κ : ZMod 2) = κ'
      revert u' v' w' z' α' β' κ'
      decide
    · have hN2 : (N : ZMod 2) = 1 := (ZMod.natCast_eq_one_iff_odd).2 ho
      have hg2 : (g : ZMod 2) = 1 := by
        rw [hg_def, Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.2 ho)]; rfl
      rw [hN2] at hdet' ⊢
      rw [hg2]
      generalize (u : ZMod 2) = u' at hdet' ⊢
      generalize (v : ZMod 2) = v' at hdet' ⊢
      generalize (w : ZMod 2) = w' at hdet' ⊢
      generalize (z : ZMod 2) = z' at hdet' ⊢
      generalize (α : ZMod 2) = α'
      generalize (β : ZMod 2) = β'
      generalize (κ : ZMod 2) = κ'
      revert u' v' w' z' α' β' κ'
      decide
  obtain ⟨K, hK⟩ := dvd_add hD hE
  have hQ : ∑ r ∈ m.support, (m r : ℂ) * ((s₀ r : ℂ) * r 1 - s₁ r * r 0) =
      (u - z) * κ + g * (v * β - w * α) := by
    refine mul_left_cancel₀ (Nat.cast_ne_zero.mpr hN) ?_
    have hsum : ∑ r ∈ m.support, (N : ℂ) * ((m r : ℂ) * ((s₀ r : ℂ) * r 1 - s₁ r * r 0)) =
        (u - z) * ((∑ r ∈ m.support, m r * (a r * b r) : ℤ) : ℂ) +
          v * ((∑ r ∈ m.support, m r * b r ^ 2 : ℤ) : ℂ) -
          w * ((∑ r ∈ m.support, m r * a r ^ 2 : ℤ) : ℂ) := by
      push_cast
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r hr ↦ ?_
      have h0 : (N : ℂ) * (r 0 : ℂ) = a r := by exact_mod_cast ha r hr
      have h1 : (N : ℂ) * (r 1 : ℂ) = b r := by exact_mod_cast hb r hr
      simp only [hs₀, hs₁]
      push_cast
      linear_combination (m r * (a r * u + b r * v) : ℂ) * h1 -
        (m r * (a r * w + b r * z) : ℂ) * h0
    rw [Finset.mul_sum, hsum, hα, hβ, hκ]
    push_cast
    ring
  have hphase : ∀ r : Fin 2 → ℝ, ((-1) ^ n r * cexp (-(π * I * ((s₀ r : ℂ) * r 1 - s₁ r * r 0))))
      ^ m r = cexp (m r * (n r * (π * I) - π * I * ((s₀ r : ℂ) * r 1 - s₁ r * r 0))) := fun r ↦ by
    rw [Complex.exp_int_mul, Complex.exp_sub, Complex.exp_neg, div_eq_mul_inv,
      Complex.exp_int_mul (π * I), Complex.exp_pi_mul_I]
  have hexp : ∑ r ∈ m.support,
      (m r : ℂ) * (n r * (π * I) - π * I * ((s₀ r : ℂ) * r 1 - s₁ r * r 0)) =
      π * I * ((∑ r ∈ m.support, m r * n r : ℤ) : ℂ) -
        π * I * ∑ r ∈ m.support, (m r : ℂ) * ((s₀ r : ℂ) * r 1 - s₁ r * r 0) := by
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ ↦ by ring
  have hK' := congrArg (Int.cast : ℤ → ℂ) hK
  push_cast at hK'
  change ∏ r ∈ m.support, ((-1) ^ n r * cexp (-(π * I * ((s₀ r : ℂ) * r 1 - s₁ r * r 0))))
    ^ m r = 1
  simp_rw [hphase]
  rw [← Complex.exp_sum, Complex.exp_eq_one_iff, hexp, hQ]
  refine ⟨K, ?_⟩
  push_cast
  linear_combination (π * I) * hK'


/-- **The Kubert–Lang congruence criterion on `Γ(N)`.** Let `m` be a finite exponent family
supported on vectors `r` with `N r = (a_r, b_r) ∈ ℤ²`. If `12 ∣ ∑ m(r)`,
`gcd(2, N) N ∣ ∑ m(r) a_r²`, `gcd(2, N) N ∣ ∑ m(r) b_r²` and `N ∣ ∑ m(r) a_r b_r`, then the Siegel
product `∏ g_r^{m(r)}` is invariant under the whole principal congruence subgroup `Γ(N)`. -/
theorem siegelProduct_smul_of_mem_Gamma {N : ℕ} {m : (Fin 2 → ℝ) →₀ ℤ}
    (a b : (Fin 2 → ℝ) → ℤ) (ha : ∀ r ∈ m.support, N * r 0 = a r)
    (hb : ∀ r ∈ m.support, N * r 1 = b r) (h12 : (12 : ℤ) ∣ m.sum fun _ k ↦ k)
    (haa : (Nat.gcd 2 N * N : ℤ) ∣ m.sum fun r k ↦ k * a r ^ 2)
    (hbb : (Nat.gcd 2 N * N : ℤ) ∣ m.sum fun r k ↦ k * b r ^ 2)
    (hab : (N : ℤ) ∣ m.sum fun r k ↦ k * (a r * b r)) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) :
    siegelProduct m ↑(γ • τ) = siegelProduct m τ := by
  rcases eq_or_ne N 0 with rfl | hN
  · rw [CongruenceSubgroup.Gamma_zero_bot, Subgroup.mem_bot] at hγ
    rw [hγ, one_smul]
  obtain ⟨ε, hε, u, v, w, z, hdet, hγε⟩ := exists_siegelFunction_smul_eq_of_mem_Gamma hN hγ
  have hε₀ : ε ≠ 0 := by rintro rfl; norm_num at hε
  have hprod : ∀ s : Finset (Fin 2 → ℝ), ∏ r ∈ s, ε ^ m r = ε ^ ∑ r ∈ s, m r := fun s ↦ by
    induction s using Finset.cons_induction with
    | empty => simp
    | cons x s hx ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hε₀]
  obtain ⟨t, ht⟩ := h12
  simp only [Finsupp.sum] at ht
  rw [siegelProduct_def, siegelProduct_def, Finsupp.prod, Finsupp.prod,
    Finset.prod_congr rfl fun r hr ↦ by
      rw [hγε r (a r) (b r) (ha r hr) (hb r hr) τ, mul_zpow, mul_zpow],
    Finset.prod_mul_distrib, Finset.prod_mul_distrib, hprod, ht, zpow_mul,
    show (12 : ℤ) = ((12 : ℕ) : ℤ) from rfl, zpow_natCast, hε, one_zpow, one_mul,
    prod_congruencePhase_zpow_eq_one hN hdet a b ha hb haa hbb hab, one_mul]

end TauCeti.ModularForm
