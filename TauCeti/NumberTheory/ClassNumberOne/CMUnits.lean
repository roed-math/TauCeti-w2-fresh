/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassNumberOne.CMPoint
public import TauCeti.NumberTheory.QuadraticOrder.Field
public import TauCeti.NumberTheory.QuadraticOrder.NormOne
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination

/-!
# Units of the quadratic order as CM multiplication matrices

Let `D < 0` be a discriminant and `O = ℤ[(D + √D)/2]` the quadratic order of discriminant `D`
(`TauCeti.QuadraticOrder.toSubalgebra D hD`). Its generator `ω = (D + √D)/2` differs from the
CM point `τ_D` by the integer `(B + D)/2` (`TauCeti.cmTauShift`), where `X² + B X + C` is the
monic polynomial of `τ_D`. Writing an element of `O` as `t + s τ_D`, it acts on the basis
`(τ_D, 1)` by the multiplication matrix `[[t - B s, -C s], [s, t]]` (`TauCeti.cmMulMatrix`). This
is a ring homomorphism `O → M₂(ℤ)` (`TauCeti.cmMulMatrixHom`), so reduction modulo `N` gives a
group homomorphism `Oˣ → GL(2, ℤ/Nℤ)` (`TauCeti.cmUnitsToGL`).

Its image is the image of the actual units of `O` among the multiplication matrices of level `N`.
For `N ≥ 3` the units inject (`TauCeti.cmUnitsToGL_injective`), so the image has order `6` for
`D = -3`, `4` for `D = -4` and `2` otherwise (`TauCeti.card_range_cmUnitsToGL`): at `D = -3, -4`
it is strictly larger than `{±1}`. At `N = 2` the unit `-1` already becomes trivial
(`TauCeti.cmUnitsToGL_two_neg_one`).

For a fundamental discriminant the order is the ring of integers of `K = ℚ(√D)`
(`TauCeti.ringOfIntegersEquivToSubalgebra`), so the same statements hold for the actual units of
`O_K` (`TauCeti.cmRingOfIntegersUnitsToGL`, `TauCeti.card_range_cmRingOfIntegersUnitsToGL`).

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §11.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §3.
-/

public noncomputable section

open QuadraticAlgebra

namespace TauCeti

/-- The integer `(B + D)/2` by which the generator `(D + √D)/2` of the quadratic order of
discriminant `D` exceeds the CM point `τ_D`. -/
@[expose] def cmTauShift (D : ℤ) : ℤ := (cmTauLinearCoeff D + D) / 2

/-- Twice the shift is `B + D`. -/
theorem two_mul_cmTauShift {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) :
    2 * cmTauShift D = cmTauLinearCoeff D + D := by
  unfold cmTauShift cmTauLinearCoeff
  split_ifs <;> omega

variable (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)

/-- The multiplication matrix of the generator `(D + √D)/2 = τ_D + (B + D)/2` satisfies the
defining relation `ω² = (D - D²)/4 + D ω` of the integral quadratic model. -/
theorem cmMulMatrix_shift_mul_self (hD : D % 4 = 0 ∨ D % 4 = 1) :
    cmMulMatrix (cmTauLinearCoeff D) (cmTauConstCoeff D) 1 (cmTauShift D) *
        cmMulMatrix (cmTauLinearCoeff D) (cmTauConstCoeff D) 1 (cmTauShift D) =
      ((D - D ^ 2) / 4) • 1 +
        D • cmMulMatrix (cmTauLinearCoeff D) (cmTauConstCoeff D) 1 (cmTauShift D) := by
  have hdisc := cmTauLinearCoeff_sq_sub_four_mul_cmTauConstCoeff hD
  have hh := two_mul_cmTauShift hD
  have ha := QuadraticOrder.parameter_discr D hD
  rw [QuadraticAlgebra.discr_def] at ha
  set B := cmTauLinearCoeff D
  set C := cmTauConstCoeff D
  set h := cmTauShift D
  set a := (D - D ^ 2) / 4
  have h00 : 4 * ((h - B) * (h - B) - C - (a + D * (h - B))) = 0 := by
    linear_combination (2 * h - 3 * B - D) * hh - ha + hdisc
  have h11 : 4 * (h * h - C - (a + D * h)) = 0 := by
    linear_combination (2 * h + B - D) * hh + hdisc - ha
  have h01 : C * (2 * h) = C * (B + D) := by rw [hh]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cmMulMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.intCast_apply] <;>
    linarith

/-- **The regular representation of the quadratic order** on the basis `(τ_D, 1)`: the element
`t + s τ_D` goes to its multiplication matrix `[[t - B s, -C s], [s, t]]`. -/
def cmMulMatrixHom : QuadraticOrder.toSubalgebra D hD →ₐ[ℤ] Matrix (Fin 2) (Fin 2) ℤ :=
  (QuadraticAlgebra.lift ⟨_, cmMulMatrix_shift_mul_self D hD⟩).comp
    (QuadraticOrder.equivToSubalgebra D hD).symm.toAlgHom

/-- The element `m + n (D + √D)/2 = (m + n (B + D)/2) + n τ_D` of the order goes to the
multiplication matrix with `s = n` and `t = m + n (B + D)/2`. -/
theorem cmMulMatrixHom_equivToSubalgebra (z : QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D) :
    cmMulMatrixHom D hD (QuadraticOrder.equivToSubalgebra D hD z) =
      cmMulMatrix (cmTauLinearCoeff D) (cmTauConstCoeff D) z.im (z.re + z.im * cmTauShift D) := by
  simp only [cmMulMatrixHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply, QuadraticAlgebra.lift_apply_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cmMulMatrix, Matrix.intCast_apply] <;> ring

/-- The regular representation is injective: the entries `s` and `t` recover the element. -/
theorem cmMulMatrixHom_injective : Function.Injective (cmMulMatrixHom D hD) := by
  intro x y hxy
  obtain ⟨z, rfl⟩ := (QuadraticOrder.equivToSubalgebra D hD).surjective x
  obtain ⟨w, rfl⟩ := (QuadraticOrder.equivToSubalgebra D hD).surjective y
  rw [cmMulMatrixHom_equivToSubalgebra, cmMulMatrixHom_equivToSubalgebra] at hxy
  have hs := congrFun (congrFun hxy 1) 0
  have ht := congrFun (congrFun hxy 1) 1
  simp only [cmMulMatrix, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at hs ht
  congr 1
  ext
  · rw [hs] at ht
    linarith
  · exact hs

/-- The determinant of the multiplication matrix is the norm form `t² - B s t + C s²`, which is
`1` on units when `D < 0`. -/
theorem det_cmMulMatrixHom_unit (hneg : D < 0) (u : (QuadraticOrder.toSubalgebra D hD)ˣ) :
    (cmMulMatrixHom D hD u).det = 1 := by
  have hunit : IsUnit (cmMulMatrixHom D hD u) := u.isUnit.map _
  rw [Matrix.isUnit_iff_isUnit_det, Int.isUnit_iff] at hunit
  obtain ⟨z, hz⟩ := (QuadraticOrder.equivToSubalgebra D hD).surjective u
  rw [← hz, cmMulMatrixHom_equivToSubalgebra, det_cmMulMatrix] at hunit ⊢
  have h4 := four_mul_cmNormForm (cmTauLinearCoeff D) (cmTauConstCoeff D) z.im
    (z.re + z.im * cmTauShift D)
  have hdisc := cmTauLinearCoeff_sq_sub_four_mul_cmTauConstCoeff hD
  rcases hunit with h | h
  · exact h
  · rw [h] at h4
    nlinarith [sq_nonneg (2 * (z.re + z.im * cmTauShift D) - cmTauLinearCoeff D * z.im),
      sq_nonneg z.im]

variable (N : ℕ)

/-- **The units of the quadratic order as multiplication matrices of level `N`**: a unit
`t + s τ_D` goes to `[[t - B s, -C s], [s, t]]` reduced modulo `N`. -/
def cmUnitsToGL : (QuadraticOrder.toSubalgebra D hD)ˣ →* GL (Fin 2) (ZMod N) :=
  Units.map ((Int.castRingHom (ZMod N)).mapMatrix.comp (cmMulMatrixHom D hD).toRingHom :
    QuadraticOrder.toSubalgebra D hD →* Matrix (Fin 2) (Fin 2) (ZMod N))

/-- The level-`N` matrix of a unit is the reduction of its integral multiplication matrix. -/
theorem coe_cmUnitsToGL (u : (QuadraticOrder.toSubalgebra D hD)ˣ) :
    (cmUnitsToGL D hD N u : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      (cmMulMatrixHom D hD u).map (Int.castRingHom (ZMod N)) := (rfl)

/-- A solution of the norm-form equation `t² - B s t + C s² = 1` with `B² - 4C ≤ -3` and
`(s, t) ≡ (0, 1) (mod N)` for some `N ≥ 3` is `(0, 1)`. -/
theorem eq_zero_one_of_cmNormForm_eq_one {B C s t : ℤ} (hBC : B ^ 2 - 4 * C ≤ -3)
    (h : t ^ 2 - B * s * t + C * s ^ 2 = 1) {N : ℕ} (hN : 3 ≤ N) (hs : (N : ℤ) ∣ s)
    (ht : (N : ℤ) ∣ t - 1) : s = 0 ∧ t = 1 := by
  have h4 := four_mul_cmNormForm B C s t
  rw [h] at h4
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * t - B * s), sq_nonneg s]
  have hN' : (3 : ℤ) ≤ N := by exact_mod_cast hN
  have hs0 : s = 0 := by
    obtain ⟨k, rfl⟩ := hs
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · have : 1 ≤ k ^ 2 := by
        have := sq_nonneg k
        have : k ^ 2 ≠ 0 := pow_ne_zero 2 hk
        omega
      have h9 : (9 : ℤ) ≤ (N : ℤ) ^ 2 * k ^ 2 := by nlinarith
      rw [mul_pow] at hs2
      exact absurd hs2 (by linarith)
  subst hs0
  refine ⟨rfl, ?_⟩
  have ht2 : (t - 1) * (t + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp ht2 with h1 | h1
  · linarith
  · obtain ⟨k, hk⟩ := ht
    have : (N : ℤ) * k = -2 := by linarith
    rcases eq_or_ne k 0 with rfl | hk0
    · simp at this
    · have : (3 : ℤ) ≤ |(N : ℤ) * k| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
        nlinarith [Int.one_le_abs hk0]
      rw [‹(N : ℤ) * k = -2›] at this
      norm_num at this

/-- **The units inject into the level-`N` multiplication matrices for `N ≥ 3`**, so the kernel
of reduction is trivial even at `D = -3, -4`. -/
theorem cmUnitsToGL_injective (hneg : D < 0) {N : ℕ} (hN : 3 ≤ N) :
    Function.Injective (cmUnitsToGL D hD N) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have hdet := det_cmMulMatrixHom_unit D hD hneg u
  have hmat := congrArg (fun g : GL (Fin 2) (ZMod N) => (g : Matrix (Fin 2) (Fin 2) (ZMod N)))
    hu
  simp only [coe_cmUnitsToGL, Units.val_one] at hmat
  obtain ⟨z, hz⟩ := (QuadraticOrder.equivToSubalgebra D hD).surjective u
  rw [← hz, cmMulMatrixHom_equivToSubalgebra] at hmat hdet
  rw [det_cmMulMatrix] at hdet
  have hs := congrFun (congrFun hmat 1) 0
  have ht := congrFun (congrFun hmat 1) 1
  simp only [cmMulMatrix, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
    Matrix.one_apply_eq, eq_intCast] at hs ht
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hs
  rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff_dvd_sub] at ht
  have hdisc := cmTauLinearCoeff_sq_sub_four_mul_cmTauConstCoeff hD
  obtain ⟨hs0, ht1⟩ := eq_zero_one_of_cmNormForm_eq_one (by omega) hdet hN hs
    (by rw [← dvd_neg, neg_sub]; exact ht)
  apply Units.ext
  rw [← hz, Units.val_one, ← map_one (QuadraticOrder.equivToSubalgebra D hD)]
  congr 1
  rw [hs0, zero_mul, add_zero] at ht1
  ext
  · simpa using ht1
  · simpa using hs0

/-- **The image of the units among the level-`N` multiplication matrices** has order `6` for
`D = -3`, `4` for `D = -4` and `2` otherwise, once `N ≥ 3`. -/
theorem card_range_cmUnitsToGL (hneg : D < 0) {N : ℕ} (hN : 3 ≤ N) :
    Nat.card (cmUnitsToGL D hD N).range = if D = -3 then 6 else if D = -4 then 4 else 2 := by
  rw [← QuadraticOrder.card_units_of_neg D hD hneg]
  exact Nat.card_congr (MonoidHom.ofInjective (cmUnitsToGL_injective D hD hneg hN)).toEquiv.symm

/-- At level `2` the unit `-1` becomes trivial. -/
theorem cmUnitsToGL_two_neg_one : cmUnitsToGL D hD 2 (-1) = 1 := by
  apply Units.ext
  rw [coe_cmUnitsToGL, Units.val_neg, Units.val_one, Units.val_one, map_neg, map_one]
  ext i j
  fin_cases i <;> fin_cases j <;> decide


section RingOfIntegers

open scoped NumberField

variable [Fact (¬ IsSquare D)]

/-- For a fundamental discriminant `D`, the ring of integers of `ℚ(√D)` is the order
`ℤ[(D + √D)/2]`. -/
def ringOfIntegersEquivToSubalgebra (hfund : Int.IsFundamentalDiscr D) :
    𝓞 (QuadraticAlgebra ℚ (D : ℚ) 0) ≃ₐ[ℤ] QuadraticOrder.toSubalgebra D hD :=
  (Subalgebra.equivOfEq _ _
    ((QuadraticOrder.toSubalgebra_eq_integralClosure_iff D hD).mpr hfund)).symm

/-- **The actual units of `O_K` as multiplication matrices of level `N`**, for `K = ℚ(√D)` with
fundamental discriminant `D`. -/
def cmRingOfIntegersUnitsToGL (hfund : Int.IsFundamentalDiscr D) (N : ℕ) :
    (𝓞 (QuadraticAlgebra ℚ (D : ℚ) 0))ˣ →* GL (Fin 2) (ZMod N) :=
  (cmUnitsToGL D hD N).comp (Units.map (ringOfIntegersEquivToSubalgebra D hD hfund :
    𝓞 (QuadraticAlgebra ℚ (D : ℚ) 0) →* QuadraticOrder.toSubalgebra D hD))

/-- For `N ≥ 3` the actual units of `O_K` inject into the level-`N` multiplication matrices. -/
theorem cmRingOfIntegersUnitsToGL_injective (hfund : Int.IsFundamentalDiscr D) (hneg : D < 0)
    {N : ℕ} (hN : 3 ≤ N) : Function.Injective (cmRingOfIntegersUnitsToGL D hD hfund N) :=
  (cmUnitsToGL_injective D hD hneg hN).comp
    (Units.map_injective (ringOfIntegersEquivToSubalgebra D hD hfund).injective)

/-- **The image of the actual units of `O_K`** among the level-`N` multiplication matrices has
order `|O_Kˣ|` for `N ≥ 3`: six for `D = -3`, four for `D = -4` and two otherwise. -/
theorem card_range_cmRingOfIntegersUnitsToGL (hfund : Int.IsFundamentalDiscr D) (hneg : D < 0)
    {N : ℕ} (hN : 3 ≤ N) :
    Nat.card (cmRingOfIntegersUnitsToGL D hD hfund N).range =
      Nat.card (𝓞 (QuadraticAlgebra ℚ (D : ℚ) 0))ˣ :=
  Nat.card_congr (MonoidHom.ofInjective
    (cmRingOfIntegersUnitsToGL_injective D hD hfund hneg hN)).toEquiv.symm

end RingOfIntegers

end TauCeti
