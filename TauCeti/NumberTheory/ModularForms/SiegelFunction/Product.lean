/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Transform
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Finite products of Siegel functions

For a finitely supported family of integer exponents `m : ℝ² →₀ ℤ`, the *Siegel product*
`∏_r g_r^{m(r)}` (`TauCeti.ModularForm.siegelProduct`) is the function whose modularity for `Γ(N)`
is governed by congruence conditions on `m`. This file supplies the exponent-family API: the
product of the zero family is `1`, a single exponent gives a power of one Siegel function, adding
exponent families multiplies the products and negating a family inverts its product. When no
`r` in the support of `m` is integral the product is holomorphic and has no zeros on the upper
half-plane. Finally, `SL₂(ℤ)` acts on Siegel products through its right action on the indices:
`∏ g_r^{m(r)}(γ τ) = ε^{Σ m(r)} ∏ g_{r γ}^{m(r)}(τ)` with the twelfth root of unity `ε = ε(γ)`
of `TauCeti.ModularForm.exists_siegelFunction_smul_eq_mul`. In particular the product is invariant
under `SL₂(ℤ)` up to the index permutation as soon as `12 ∣ Σ m(r)`.

## Main definitions

* `TauCeti.ModularForm.siegelProduct`: `τ ↦ ∏_r g_r(τ)^{m(r)}` for `m : ℝ² →₀ ℤ`.

## Main results

* `TauCeti.ModularForm.siegelProduct_add`, `TauCeti.ModularForm.siegelProduct_neg`: the product
  is multiplicative in the exponent family.
* `TauCeti.ModularForm.differentiableOn_siegelProduct`,
  `TauCeti.ModularForm.siegelProduct_ne_zero`: away from integral indices, a Siegel product is
  holomorphic and nonvanishing on the upper half-plane.
* `TauCeti.ModularForm.exists_siegelProduct_smul_eq_mul`: the transformation under `SL₂(ℤ)`.

## References

* D. S. Kubert, S. Lang, *Modular Units*, Grundlehren der mathematischen Wissenschaften 244,
  Chapter 3, §5.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §2.
-/

public section

open Complex Matrix
open UpperHalfPlane hiding I
open scoped Manifold MatrixGroups

namespace TauCeti.ModularForm

/-- **The Siegel product** `∏_r g_r(τ)^{m(r)}` of a finitely supported family `m : ℝ² →₀ ℤ` of
integer exponents. -/
noncomputable def siegelProduct (m : (Fin 2 → ℝ) →₀ ℤ) (τ : ℂ) : ℂ :=
  m.prod fun r k ↦ siegelFunction r τ ^ k

/-- The defining product of a Siegel product. -/
theorem siegelProduct_def (m : (Fin 2 → ℝ) →₀ ℤ) (τ : ℂ) :
    siegelProduct m τ = m.prod fun r k ↦ siegelFunction r τ ^ k :=
  (rfl)

/-- The Siegel product of the zero exponent family is `1`. -/
@[simp]
theorem siegelProduct_zero (τ : ℂ) : siegelProduct 0 τ = 1 :=
  Finsupp.prod_zero_index

/-- The Siegel product of a single exponent `k` at `r` is `g_r^k`. -/
@[simp]
theorem siegelProduct_single (r : Fin 2 → ℝ) (k : ℤ) (τ : ℂ) :
    siegelProduct (Finsupp.single r k) τ = siegelFunction r τ ^ k :=
  Finsupp.prod_single_index (zpow_zero _)

/-- Negating the exponent family inverts the Siegel product. -/
@[simp]
theorem siegelProduct_neg (m : (Fin 2 → ℝ) →₀ ℤ) (τ : ℂ) :
    siegelProduct (-m) τ = (siegelProduct m τ)⁻¹ := by
  rw [siegelProduct_def, siegelProduct_def, Finsupp.prod_neg_index fun _ ↦ zpow_zero _]
  simp only [_root_.zpow_neg, Finsupp.prod, Finset.prod_inv_distrib]

/-- **A Siegel product has no zeros** on the upper half-plane when no index in the support of the
exponent family is integral. -/
theorem siegelProduct_ne_zero {m : (Fin 2 → ℝ) →₀ ℤ}
    (hm : ∀ r ∈ m.support, ∀ s : Fin 2 → ℤ, r ≠ fun i ↦ (s i : ℝ)) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelProduct m τ ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun r hr ↦ zpow_ne_zero _ (siegelFunction_ne_zero (hm r hr) hτ)

/-- **Siegel products are multiplicative in the exponent family**, on the upper half-plane and
away from integral indices. -/
theorem siegelProduct_add {m m' : (Fin 2 → ℝ) →₀ ℤ}
    (hm : ∀ r ∈ m.support ∪ m'.support, ∀ s : Fin 2 → ℤ, r ≠ fun i ↦ (s i : ℝ)) {τ : ℂ}
    (hτ : 0 < τ.im) : siegelProduct (m + m') τ = siegelProduct m τ * siegelProduct m' τ :=
  Finsupp.prod_add_index (fun _ _ ↦ zpow_zero _)
    fun r hr _ _ ↦ zpow_add₀ (siegelFunction_ne_zero (hm r hr) hτ) _ _

/-- **A Siegel product is holomorphic** on the upper half-plane when no index in the support of
the exponent family is integral. -/
theorem differentiableOn_siegelProduct {m : (Fin 2 → ℝ) →₀ ℤ}
    (hm : ∀ r ∈ m.support, ∀ s : Fin 2 → ℤ, r ≠ fun i ↦ (s i : ℝ)) :
    DifferentiableOn ℂ (siegelProduct m) upperHalfPlaneSet := by
  simp only [funext (siegelProduct_def m), Finsupp.prod]
  exact DifferentiableOn.fun_finsetProd fun r hr ↦
    (differentiableOn_siegelFunction r).zpow
      (Or.inl fun τ hτ ↦ siegelFunction_ne_zero (hm r hr) hτ)

/-- A Siegel product is holomorphic as a function on `ℍ` when no index in the support of the
exponent family is integral. -/
theorem mdifferentiable_siegelProduct {m : (Fin 2 → ℝ) →₀ ℤ}
    (hm : ∀ r ∈ m.support, ∀ s : Fin 2 → ℤ, r ≠ fun i ↦ (s i : ℝ)) :
    MDiff fun τ : ℍ ↦ siegelProduct m τ := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  exact (differentiableOn_siegelProduct hm).congr fun z hz ↦ by
    simp [Function.comp_apply, ofComplex_apply_of_im_pos hz]

/-- **The transformation of Siegel products under `SL₂(ℤ)`.** For every `γ ∈ SL₂(ℤ)` there is a
twelfth root of unity `ε` such that `∏ g_r^{m(r)}(γ τ) = ε^{Σ m(r)} ∏ g_{r γ}^{m(r)}(τ)` for every
exponent family `m` and every `τ` in the upper half-plane, where the indices of the second product
are moved by the right action `r ↦ r γ`. -/
theorem exists_siegelProduct_smul_eq_mul (γ : SL(2, ℤ)) :
    ∃ ε : ℂ, ε ^ 12 = 1 ∧ ∀ (m : (Fin 2 → ℝ) →₀ ℤ) (τ : ℍ),
      siegelProduct m ↑(γ • τ) = ε ^ (m.sum fun _ k ↦ k) * siegelProduct
        (m.mapDomain fun r ↦ r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ := by
  obtain ⟨ε, hε, h⟩ := exists_siegelFunction_smul_eq_mul γ
  have hε₀ : ε ≠ 0 := by rintro rfl; simp at hε
  refine ⟨ε, hε, fun m τ ↦ ?_⟩
  have hinj : Function.Injective fun r : Fin 2 → ℝ ↦
      r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) :=
    Function.LeftInverse.injective (g := fun r ↦
        r ᵥ* (↑γ⁻¹ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ))
      fun r ↦ by simpa using SpecialLinearGroup.vecMul_map_inv_vecMul_map (Int.castRingHom ℝ) r γ⁻¹
  have hsum : ∀ s : Finset (Fin 2 → ℝ), ε ^ (∑ r ∈ s, m r) = ∏ r ∈ s, ε ^ m r := fun s ↦ by
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ hε₀, ih]
  rw [siegelProduct_def, siegelProduct_def, Finsupp.prod_mapDomain_index_inj hinj,
    Finsupp.sum, hsum, Finsupp.prod, Finsupp.prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun r _ ↦ by rw [h, mul_zpow]

/-- **Siegel products with exponent sum divisible by `12` are permuted by `SL₂(ℤ)`**:
`∏ g_r^{m(r)}(γ τ) = ∏ g_{r γ}^{m(r)}(τ)` when `12 ∣ Σ m(r)`. -/
theorem siegelProduct_smul_of_dvd_sum (γ : SL(2, ℤ)) {m : (Fin 2 → ℝ) →₀ ℤ}
    (hm : (12 : ℤ) ∣ m.sum fun _ k ↦ k) (τ : ℍ) :
    siegelProduct m ↑(γ • τ) = siegelProduct
      (m.mapDomain fun r ↦ r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ := by
  obtain ⟨ε, hε, h⟩ := exists_siegelProduct_smul_eq_mul γ
  obtain ⟨k, hk⟩ := hm
  rw [h, hk, _root_.zpow_mul, zpow_ofNat, hε, _root_.one_zpow, one_mul]

end TauCeti.ModularForm
