/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Chart.Basic
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic

/-!
# The overlap of the charts `D₊(Y)` and `D₊(Z)` of a projective Weierstrass cubic

Let `W'` be a Weierstrass curve over a commutative ring `R`, with homogeneous coordinate ring
`A = R[X, Y, Z] ⧸ (W'(X, Y, Z))`. The degree-zero parts `A_(Y)`, `A_(Z)` and `A_(YZ)` of its
localizations are the rings of functions of the standard affine charts `D₊(Y)`, `D₊(Z)` and of
their overlap `D₊(YZ)`. This file describes `A_(YZ)` in terms of the affine coordinates of the
two charts.

On the overlap, `Z / Y` and `Y / Z` are inverse to each other
(`WeierstrassCurve.Projective.awayMapOverlapY_mul_awayMapOverlapZ`), and `A_(YZ)` is the
localization of `A_(Z)` away from `y = Y / Z`
(`WeierstrassCurve.Projective.isLocalization_awayMapOverlapZ`). On the chart `D₊(Z)`, the
Weierstrass equation `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` in `x = X / Z` and `y` is monic of
degree three in `x`, so every function on `D₊(Z)` is `P₀(y) + x P₁(y) + x² P₂(y)`
(`WeierstrassCurve.Projective.exists_eq_chartRing_two`). Hence every function on the overlap is
`(Z / Y)ᵏ (P₀(y) + x P₁(y) + x² P₂(y))` (`WeierstrassCurve.Projective.exists_eq_overlap`). This
is the input for the finiteness of the first cohomology of the projective model
(`WeierstrassCurve.finite_cohomology_one`).

## Main results

* `WeierstrassCurve.Projective.exists_eq_chartRing_two`: the chart ring of `D₊(Z)` is spanned by
  `1`, `x` and `x²` over `R[y]`.
* `WeierstrassCurve.Projective.awayMapOverlapY_mul_awayMapOverlapZ`: `(Z / Y) (Y / Z) = 1` on the
  overlap.
* `WeierstrassCurve.Projective.isLocalization_awayMapOverlapZ`: `A_(YZ) = A_(Z)[(Y / Z)⁻¹]`.
* `WeierstrassCurve.Projective.exists_eq_overlap`: every function on the overlap is
  `(Z / Y)ᵏ (P₀(y) + x P₁(y) + x² P₂(y))`.
-/

public section

open MvPolynomial HomogeneousLocalization

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] (W' : Projective R)

/-- Every element of the chart ring of `D₊(Z)` is `P₀(y) + x P₁(y) + x² P₂(y)`. -/
theorem exists_eq_chartRing_two (c : W'.ChartRing 2) :
    ∃ P₀ P₁ P₂ : Polynomial R, c = Polynomial.aeval (W'.chartPoint 2 1) P₀ +
      W'.chartPoint 2 0 * Polynomial.aeval (W'.chartPoint 2 1) P₁ +
        W'.chartPoint 2 0 ^ 2 * Polynomial.aeval (W'.chartPoint 2 1) P₂ := by
  set x := W'.chartPoint 2 0
  set y := W'.chartPoint 2 1
  have h := (equation_iff _).mp (W'.equation_chartPoint 2)
  rw [chartPoint_self, show W'.baseChange (W'.ChartRing 2) = W'.map (algebraMap R _) from rfl] at h
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at h
  -- `x³` reduces to lower powers of `x` with coefficients polynomial in `y`
  have hx3 : x ^ 3 = Polynomial.aeval y (Polynomial.X ^ 2 + Polynomial.C W'.a₃ * Polynomial.X -
      Polynomial.C W'.a₆) + x * Polynomial.aeval y (Polynomial.C W'.a₁ * Polynomial.X -
        Polynomial.C W'.a₄) + x ^ 2 * Polynomial.aeval y (-Polynomial.C W'.a₂) := by
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C]
    linear_combination -h
  -- the elements of this form are closed under multiplication by `x`, by `y` and by constants
  let S : Set (W'.ChartRing 2) := {c | ∃ P₀ P₁ P₂ : Polynomial R, c = Polynomial.aeval y P₀ +
      x * Polynomial.aeval y P₁ + x ^ 2 * Polynomial.aeval y P₂}
  have hadd {a b} (ha : a ∈ S) (hb : b ∈ S) : a + b ∈ S := by
    obtain ⟨P₀, P₁, P₂, rfl⟩ := ha
    obtain ⟨Q₀, Q₁, Q₂, rfl⟩ := hb
    exact ⟨P₀ + Q₀, P₁ + Q₁, P₂ + Q₂, by simp only [map_add]; ring⟩
  have hmulx {a} (ha : a ∈ S) : a * x ∈ S := by
    obtain ⟨P₀, P₁, P₂, rfl⟩ := ha
    refine ⟨(Polynomial.X ^ 2 + Polynomial.C W'.a₃ * Polynomial.X - Polynomial.C W'.a₆) * P₂,
      P₀ + (Polynomial.C W'.a₁ * Polynomial.X - Polynomial.C W'.a₄) * P₂,
      P₁ + -Polynomial.C W'.a₂ * P₂, ?_⟩
    simp only [map_add, map_mul] at hx3 ⊢
    linear_combination (Polynomial.aeval y P₂) * hx3
  have hmuly {a} (ha : a ∈ S) : a * y ∈ S := by
    obtain ⟨P₀, P₁, P₂, rfl⟩ := ha
    exact ⟨P₀ * Polynomial.X, P₁ * Polynomial.X, P₂ * Polynomial.X, by
      simp only [map_mul, Polynomial.aeval_X]; ring⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨Polynomial.C a, 0, 0, by simp [Polynomial.aeval_C]; rfl⟩
  | add p q hp hq => rw [map_add]; exact hadd hp hq
  | mul_X p j hp =>
    rw [map_mul]
    match j with
    | 0 => rw [← chartPoint_apply]; exact hmulx hp
    | 1 => rw [← chartPoint_apply]; exact hmuly hp
    | 2 =>
      have : (Ideal.Quotient.mk _ (X 2) : W'.ChartRing 2) = 1 := W'.chartRing_mk_X_self 2
      rw [this, mul_one]
      exact hp

/-- Restriction from the chart `D₊(Y)` to the overlap `D₊(YZ)`. -/
noncomputable abbrev awayMapOverlapY :
    Away W'.grading (W'.coord 1) →+* Away W'.grading (W'.coord 1 * W'.coord 2) :=
  awayMap W'.grading (W'.coord_mem_grading 2) rfl

/-- Restriction from the chart `D₊(Z)` to the overlap `D₊(YZ)`. -/
noncomputable abbrev awayMapOverlapZ :
    Away W'.grading (W'.coord 2) →+* Away W'.grading (W'.coord 1 * W'.coord 2) :=
  awayMap W'.grading (W'.coord_mem_grading 1) (mul_comm _ _)

/-- The fraction `Xⱼ / Xᵢ` on the chart `D₊(Xᵢ)`. -/
noncomputable abbrev awayCoord (i j : Fin 3) : Away W'.grading (W'.coord i) :=
  Away.mk W'.grading (W'.coord_mem_grading i) 1 (W'.coord j) (by simpa using W'.coord_mem_grading j)

/-- On the overlap `D₊(YZ)`, the functions `Z / Y` and `Y / Z` are inverse to each other. -/
theorem awayMapOverlapY_mul_awayMapOverlapZ :
    W'.awayMapOverlapY (W'.awayCoord 1 2) * W'.awayMapOverlapZ (W'.awayCoord 2 1) = 1 := by
  simp only [awayMap_mk]
  ext
  simp only [val_mul, Away.val_mk, val_one, Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

/-- The overlap ring is the localization of the chart ring of `D₊(Z)` away from `Y / Z`. -/
theorem isLocalization_awayMapOverlapZ :
    letI := W'.awayMapOverlapZ.toAlgebra
    IsLocalization.Away (W'.awayCoord 2 1) (Away W'.grading (W'.coord 1 * W'.coord 2)) := by
  have h := Away.isLocalization_mul (W'.coord_mem_grading 2) (W'.coord_mem_grading 1)
    (mul_comm _ _) one_ne_zero
  convert h using 2
  ext
  simp [Away.val_mk]

/-- The chart ring of `D₊(Z)` maps to the overlap ring `A_(YZ)`, as an `R`-algebra. -/
private noncomputable def chartRingTwoToOverlap :
    W'.ChartRing 2 →ₐ[R] Away W'.grading (W'.coord 1 * W'.coord 2) where
  toRingHom := W'.awayMapOverlapZ.comp (W'.awayEquivChartRing 2).symm.toRingHom
  commutes' r :=
    (congrArg W'.awayMapOverlapZ
      (RingHom.congr_fun (W'.awayEquivChartRing_symm_comp_algebraMap 2) r)).trans
      (awayMap_algebraMap (W'.coord_mem_grading 1) (mul_comm _ _) r)

/-- **Every function on the overlap `D₊(YZ)` is `(Z/Y)ᵏ (P₀(y) + x P₁(y) + x² P₂(y))`**, where
`x = X / Z` and `y = Y / Z`. -/
theorem exists_eq_overlap (b : Away W'.grading (W'.coord 1 * W'.coord 2)) :
    ∃ (k : ℕ) (P₀ P₁ P₂ : Polynomial R), b = W'.awayMapOverlapY (W'.awayCoord 1 2) ^ k *
      (Polynomial.aeval (W'.awayMapOverlapZ (W'.awayCoord 2 1)) P₀ +
        W'.awayMapOverlapZ (W'.awayCoord 2 0) *
          Polynomial.aeval (W'.awayMapOverlapZ (W'.awayCoord 2 1)) P₁ +
        W'.awayMapOverlapZ (W'.awayCoord 2 0) ^ 2 *
          Polynomial.aeval (W'.awayMapOverlapZ (W'.awayCoord 2 1)) P₂) := by
  let := W'.awayMapOverlapZ.toAlgebra
  have := W'.isLocalization_awayMapOverlapZ
  obtain ⟨⟨a, _, k, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers (W'.awayCoord 2 1)) b
  have h' : b * W'.awayMapOverlapZ (W'.awayCoord 2 1) ^ k = W'.awayMapOverlapZ a := by
    simpa [RingHom.algebraMap_toAlgebra] using h
  obtain ⟨P₀, P₁, P₂, hc⟩ := W'.exists_eq_chartRing_two (W'.awayEquivChartRing 2 a)
  have ha : W'.awayMapOverlapZ a = W'.chartRingTwoToOverlap (W'.awayEquivChartRing 2 a) := by
    simp [chartRingTwoToOverlap]
  have hx (j : Fin 3) : W'.chartRingTwoToOverlap (W'.chartPoint 2 j) =
      W'.awayMapOverlapZ (W'.awayCoord 2 j) := by
    simp [chartRingTwoToOverlap, chartPoint_apply]
  rw [hc, map_add, map_add, map_mul, map_mul, map_pow, ← Polynomial.aeval_algHom_apply,
    ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply, hx, hx] at ha
  refine ⟨k, P₀, P₁, P₂, ?_⟩
  rw [← ha, ← h']
  have hb : b = b * (W'.awayMapOverlapY (W'.awayCoord 1 2) *
      W'.awayMapOverlapZ (W'.awayCoord 2 1)) ^ k := by
    rw [awayMapOverlapY_mul_awayMapOverlapZ, one_pow, mul_one]
  nth_rw 1 [hb]
  ring

end WeierstrassCurve.Projective
