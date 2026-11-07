/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Product
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# Siegel functions under the translations of `Γ(N)`

The upper and lower translations `T^N = [[1, N], [0, 1]]` and `L^N = [[1, 0], [N, 1]]` lie in the
principal congruence subgroup `Γ(N)`. This file computes the exact roots of unity by which a Siegel
function `g_r` changes under `τ ↦ τ + N` (when `N r₁ ∈ ℤ`) and under `τ ↦ τ / (N τ + 1)` (when
`N r₂ ∈ ℤ`), the first of the explicit `Γ(N)` transformation phases of Kubert–Lang, and deduces
that `g_r^{12N / gcd(6, N)}` is invariant under both. For finite products `∏ g_r^{m(r)}` it proves
the corresponding half of the Kubert–Lang congruence criterion: if `12 ∣ ∑ m(r)` and
`gcd(2, N) N ∣ ∑ m(r) (N r₁)²` (resp. `∑ m(r) (N r₂)²`), the product is invariant under `T^N`
(resp. `L^N`).

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

end TauCeti.ModularForm
