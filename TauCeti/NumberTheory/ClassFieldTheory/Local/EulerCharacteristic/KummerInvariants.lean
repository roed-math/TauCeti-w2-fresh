/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import TauCeti.Lookahead.EulerCharacteristicMixed.Stubs
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.PowerClasses
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.TensorInvariants

/-!
# The first cohomology of a finite Galois layer through equivariant Kummer theory

Let `L/K` be a finite Galois extension of nonarchimedean local fields, embedded in `Kˢ` by `σ`,
let `G = Gal(L/K)`, and let `ℓ` be a prime invertible in `K` such that `σ(L)` contains the `ℓ`th
roots of unity `μ_ℓ`. Equivariant Kummer theory identifies the conjugation representation of `G`
on `H¹(Gal(Kˢ/σ(L)), 𝔽_ℓ)` with `μ_ℓ^∨ ⊗ Lˣ ⧸ (Lˣ)^ℓ`. This file computes, for every
finite-dimensional representation `A` of `G` over `𝔽_ℓ` with `ℓ ∤ #G`,

`dim (H¹ ⊗ A)ᴳ = dim (μ_ℓ^∨ ⊗ A)ᴳ + dim Aᴳ + [ℓ = p] [K : ℚ_p] dim A`.

The ingredients are:

* `σ` identifies the `ℓ`-torsion `μ_ℓ(L)` of `Lˣ` with `μ_ℓ(Kˢ)` as representations of `G`
  (`TauCeti.torsionByUnitsEquivKummerCoeff`): every `ℓ`th root of unity of `Kˢ` is fixed by the
  subgroup fixing `σ(L)`, hence lies in `σ(L)` by infinite Galois theory;
* the class of `Lˣ ⧸ (Lˣ)^ℓ` in `G₀(𝔽_ℓ[G])` is `1 + [μ_ℓ] + [ℓ = p] [K : ℚ_p] [𝔽_ℓ[G]]`
  (`TauCeti.exactK0_powerClassRepresentation_of_isUnit`,
  `TauCeti.exactK0_powerClassRepresentation_eq_add_finrank_smul`);
* the tensor-invariant count `TauCeti.finrankTensorInvariantsK0_dual_mul_one_add_add` for the
  line `μ_ℓ`.

This is the arithmetic heart of the cyclic prime-to-`ℓ` case of Tate's local Euler characteristic
formula: `dim H¹(K, A) = dim (H¹(L, 𝔽_ℓ) ⊗ A)ᴳ`, `dim H²(K, A) = dim (μ_ℓ^∨ ⊗ A)ᴳ` and
`dim H⁰(K, A) = dim Aᴳ`.

## Main results

* `TauCeti.torsionByUnitsEquivKummerCoeff`: `μ_ℓ(L) ≃ μ_ℓ(Kˢ)` as representations of `G`.
* `TauCeti.finrank_invariants_kummerH1FiniteRepresentation_tprod_of_isUnit`: the count away from
  the residue characteristic.
* `TauCeti.finrank_invariants_kummerH1FiniteRepresentation_tprod_of_finitePadicExtension`: the
  count at the residue characteristic `ℓ = p`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, proof of Theorem 2.8.
-/

public noncomputable section

open CategoryTheory MonoidalCategory TauCeti.ContCohomology Module ValuativeRel
open scoped MonoidAlgebra

namespace TauCeti

/-! ### The roots of unity of `L` -/

section RootsOfUnity

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]
  (sigma : L →ₐ[K] SeparableClosure K) (n : ℕ)

/-- An `n`-torsion element of `Lˣ`, written additively, read as an `n`th root of unity of `Kˢ`
through the embedding `σ`. -/
private def torsionByUnitsToKummerCoeff :
    Submodule.torsionBy ℤ (Additive Lˣ) (n : ℤ) →+ KummerCoeff K n where
  toFun x := Additive.ofMul ⟨Units.map (sigma : L →* SeparableClosure K) x.1.toMul, by
    have hx := congrArg Additive.toMul ((Submodule.mem_torsionBy_iff _ _).1 x.2)
    rw [natCast_zsmul, toMul_nsmul, toMul_zero] at hx
    rw [mem_rootsOfUnity, ← map_pow, hx, map_one]⟩
  map_zero' := by
    apply Additive.toMul.injective
    ext
    simp
  map_add' x y := by
    apply Additive.toMul.injective
    ext
    simp

private theorem coe_torsionByUnitsToKummerCoeff_apply
    (x : Submodule.torsionBy ℤ (Additive Lˣ) (n : ℤ)) :
    (((torsionByUnitsToKummerCoeff sigma n x).toMul : (SeparableClosure K)ˣ) :
      SeparableClosure K) = sigma (x.1.toMul : L) :=
  rfl

private theorem bijective_torsionByUnitsToKummerCoeff
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K n, g • xi = xi) :
    Function.Bijective (torsionByUnitsToKummerCoeff sigma n) := by
  refine ⟨fun x y h ↦ ?_, fun xi ↦ ?_⟩
  · have h' := congrArg (fun z : KummerCoeff K n ↦ ((z.toMul : (SeparableClosure K)ˣ) :
      SeparableClosure K)) h
    simp only [coe_torsionByUnitsToKummerCoeff_apply] at h'
    exact Subtype.ext (Additive.toMul.injective (Units.ext (sigma.injective h')))
  · set ζ : SeparableClosure K := ((xi.toMul : (SeparableClosure K)ˣ) : SeparableClosure K)
    have hfix : ζ ∈ IntermediateField.fixedField sigma.fieldRange.fixingSubgroup := by
      rintro ⟨g, hg⟩
      have h := congrArg (fun z : KummerCoeff K n ↦ ((z.toMul : (SeparableClosure K)ˣ) :
        SeparableClosure K)) (hN g hg xi)
      simpa [AlgEquiv.smul_units_def] using h
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hfix
    obtain ⟨y, hy⟩ := hfix
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact xi.toMul.1.ne_zero (by simp [ζ, ← hy])
    have hyn : Units.mk0 y hy0 ^ n = 1 := by
      apply Units.ext
      apply sigma.injective
      have := congrArg (fun u : (SeparableClosure K)ˣ ↦ (u : SeparableClosure K))
        ((mem_rootsOfUnity n _).1 xi.toMul.2)
      simpa [ζ, ← hy] using this
    refine ⟨⟨Additive.ofMul (Units.mk0 y hy0), (Submodule.mem_torsionBy_iff _ _).2 ?_⟩, ?_⟩
    · apply Additive.toMul.injective
      simpa [natCast_zsmul] using hyn
    · apply Additive.toMul.injective
      exact Subtype.ext (Units.ext hy)

variable [Normal K L] (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
  ∀ xi : KummerCoeff K n, g • xi = xi)

/-- **The roots of unity of `L` are those of `Kˢ`.** If the subgroup of `G_K` fixing `σ(L)`
fixes the `n`th roots of unity of `Kˢ`, then `σ` identifies the `n`-torsion `μ_n(L)` of `Lˣ`
with `μ_n(Kˢ)`, as representations of `Gal(L/K)`: an `n`th root of unity fixed by that subgroup
lies in `σ(L)` by infinite Galois theory (`InfiniteGalois.fixedField_fixingSubgroup`). -/
def torsionByUnitsEquivKummerCoeff :
    ((Representation.ofDistribMulAction ℤ Gal(L/K) (Additive Lˣ)).torsionBy n).Equiv
      (kummerCoeffFiniteRepresentation sigma n hN).restrictScalarsInt := by
  refine .mk (AddEquiv.ofBijective _ (bijective_torsionByUnitsToKummerCoeff sigma n hN)
    ).toIntLinearEquiv fun tau ↦ LinearMap.ext fun x ↦ ?_
  obtain ⟨g, rfl⟩ := sigma.restrictNormalHom_surjective tau
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv,
    AddEquiv.ofBijective_apply, Representation.restrictScalarsInt_apply]
  rw [kummerCoeffFiniteRepresentation_restrictNormalHom]
  apply Additive.toMul.injective
  ext
  simp [coe_torsionByUnitsToKummerCoeff_apply, AlgEquiv.smul_units_def]

end RootsOfUnity

/-! ### The invariant count -/

section Count

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {L : Type} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [IsGalois K L] (sigma : L →ₐ[K] SeparableClosure K) {ℓ : ℕ} [Fact ℓ.Prime]
  (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
    ∀ xi : KummerCoeff K ℓ, g • xi = xi)
  [NeZero (Nat.card Gal(L/K) : ZMod ℓ)]

/-- The absolute Galois group acts trivially on the constant coefficient module. -/
local instance : DistribMulAction (AbsoluteGaloisGroup K) (ZMod ℓ) :=
  trivialZModAction ℓ (AbsoluteGaloisGroup K)

local instance : ContinuousSMul (AbsoluteGaloisGroup K) (ZMod ℓ) :=
  ⟨continuous_snd⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The roots-of-unity representation is a line. -/
private theorem finrank_kummerCoeff (hℓ : IsUnit (ℓ : K)) :
    finrank (ZMod ℓ) (KummerCoeff K ℓ) = 1 := by
  have hp : ℓ.Prime := Fact.out
  apply Nat.pow_right_injective hp.two_le
  dsimp only
  conv_rhs => rw [pow_one, ← natCard_kummerCoeff hℓ]
  rw [Module.natCard_eq_pow_finrank (K := ZMod ℓ), Nat.card_zmod]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension K L] in
/-- **The finite-layer count from the class of the power classes.** If the power-class
representation has class `1 + [μ_ℓ(L)] + c [𝔽_ℓ[G]]`, then
`dim (H¹ ⊗ A)ᴳ = dim (μ_ℓ^∨ ⊗ A)ᴳ + dim Aᴳ + c dim A`. -/
private theorem finrank_invariants_kummerH1FiniteRepresentation_tprod_of_exactK0
    (hℓ : IsUnit (ℓ : K)) (c : ℕ)
    (hPC :
      haveI : NeZero (ℓ : L) := ⟨by
        rw [← map_natCast (algebraMap K L)]
        exact (map_ne_zero _).2 hℓ.ne_zero⟩
      haveI : Module.Finite (ZMod ℓ)[Gal(L/K)]
          (powerClassRepresentation (K := K) (L := L) ℓ).asModule :=
        Module.Finite.of_restrictScalars_finite (ZMod ℓ) (ZMod ℓ)[Gal(L/K)] _
      ExactK0.of (FGModuleCat.of (ZMod ℓ)[Gal(L/K)]
          (powerClassRepresentation (K := K) (L := L) ℓ).asModule) =
        1 + reductionK0 (ZMod ℓ)
            ((Representation.ofDistribMulAction ℤ (L ≃ₐ[K] L) (Additive Lˣ)).torsionBy ℓ) +
          c • permK0 (ZMod ℓ) (L ≃ₐ[K] L) (L ≃ₐ[K] L))
    (A : FDRep (ZMod ℓ) Gal(L/K)) :
    (finrank (ZMod ℓ) (Representation.invariants
        (V := TensorProduct (ZMod ℓ) (H1 sigma.fieldRange.fixingSubgroup (ZMod ℓ)) A)
        ((kummerH1FiniteRepresentation sigma ℓ).tprod A.ρ)) : ℤ) =
      finrank (ZMod ℓ) (Representation.invariants
          (V := TensorProduct (ZMod ℓ) (Module.Dual (ZMod ℓ) (KummerCoeff K ℓ)) A)
          ((kummerCoeffFiniteRepresentation sigma ℓ hN).dual.tprod A.ρ)) +
        finrank (ZMod ℓ) (Representation.invariants A.ρ) + c * finrank (ZMod ℓ) A := by
  have : NeZero (ℓ : L) := ⟨by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero _).2 hℓ.ne_zero⟩
  have : Module.Finite (ZMod ℓ)[Gal(L/K)]
      (powerClassRepresentation (K := K) (L := L) ℓ).asModule :=
    Module.Finite.of_restrictScalars_finite (ZMod ℓ) (ZMod ℓ)[Gal(L/K)] _
  let e := kummerH1FiniteRepresentationEquiv sigma ℓ hℓ hN
  have : Module.Finite (ZMod ℓ) (H1 sigma.fieldRange.fixingSubgroup (ZMod ℓ)) :=
    Module.Finite.equiv e.toLinearEquiv.symm
  let μ : FDRep (ZMod ℓ) Gal(L/K) := FDRep.of (kummerCoeffFiniteRepresentation sigma ℓ hN)
  let P : FDRep (ZMod ℓ) Gal(L/K) := FDRep.of (powerClassRepresentation (K := K) (L := L) ℓ)
  let H : FDRep (ZMod ℓ) Gal(L/K) := FDRep.of (kummerH1FiniteRepresentation sigma ℓ)
  have hμ : finrank (ZMod ℓ) μ = 1 := finrank_kummerCoeff hℓ
  have hP : fdRepK0RingEquiv (ZMod ℓ) Gal(L/K) (ExactK0.of P) =
      1 + fdRepK0RingEquiv (ZMod ℓ) Gal(L/K) (ExactK0.of μ) +
        c • permK0 (ZMod ℓ) (L ≃ₐ[K] L) (L ≃ₐ[K] L) := by
    rw [fdRepK0RingEquiv_of, fdRepK0RingEquiv_of]
    refine hPC.trans ?_
    rw [reductionK0_congr (ZMod ℓ) (torsionByUnitsEquivKummerCoeff sigma ℓ hN),
      reductionK0_restrictScalarsInt]
    -- `μ` is `FDRep.of` of the roots-of-unity representation, whose representation is that one.
    rfl
  have hH : fdRepK0RingEquiv (ZMod ℓ) Gal(L/K) (ExactK0.of H) =
      fdRepK0RingEquiv (ZMod ℓ) Gal(L/K) (ExactK0.of (FDRep.of (Representation.dual μ.ρ))) *
        fdRepK0RingEquiv (ZMod ℓ) Gal(L/K) (ExactK0.of P) := by
    have : Module.Finite (ZMod ℓ)[Gal(L/K)] (Representation.asModule H.ρ) :=
      Module.Finite.of_restrictScalars_finite (ZMod ℓ) (ZMod ℓ)[Gal(L/K)] _
    have : Module.Finite (ZMod ℓ)[Gal(L/K)]
        (Representation.asModule (FDRep.of (Representation.dual μ.ρ) ⊗ P).ρ) :=
      Module.Finite.of_restrictScalars_finite (ZMod ℓ) (ZMod ℓ)[Gal(L/K)] _
    rw [← map_mul, ExactK0.of_mul_of, fdRepK0RingEquiv_of, fdRepK0RingEquiv_of]
    exact ExactK0.of_congr (Representation.asModuleLinearEquivOfEquiv e).toFGModuleCatIso
  have hcount := finrankTensorInvariantsK0_dual_mul_one_add_add μ A hμ c
  rw [← hP, ← hH, fdRepK0RingEquiv_of, finrankTensorInvariantsK0_of] at hcount
  exact hcount

/-- **The first cohomology of a finite Galois layer, away from the residue characteristic.** If `ℓ`
is a unit of `𝒪[L]` and `σ(L)` contains the `ℓ`th roots of unity, then for every
finite-dimensional representation `A` of `G = Gal(L/K)` over `𝔽_ℓ` with `ℓ ∤ #G`,
`dim (H¹(Gal(Kˢ/σ(L)), 𝔽_ℓ) ⊗ A)ᴳ = dim (μ_ℓ^∨ ⊗ A)ᴳ + dim Aᴳ`. -/
theorem finrank_invariants_kummerH1FiniteRepresentation_tprod_of_isUnit
    (hℓ : IsUnit (ℓ : 𝒪[L])) (A : FDRep (ZMod ℓ) Gal(L/K)) :
    finrank (ZMod ℓ) (Representation.invariants
        (V := TensorProduct (ZMod ℓ) (H1 sigma.fieldRange.fixingSubgroup (ZMod ℓ)) A)
        ((kummerH1FiniteRepresentation sigma ℓ).tprod A.ρ)) =
      finrank (ZMod ℓ) (Representation.invariants
          (V := TensorProduct (ZMod ℓ) (Module.Dual (ZMod ℓ) (KummerCoeff K ℓ)) A)
          ((kummerCoeffFiniteRepresentation sigma ℓ hN).dual.tprod A.ρ)) +
        finrank (ZMod ℓ) (Representation.invariants A.ρ) := by
  have hℓK : IsUnit (ℓ : K) := by
    refine Ne.isUnit fun h ↦ natCast_ne_zero_of_isUnit hℓ ?_
    rw [← map_natCast (algebraMap K L), h, map_zero]
  have hPC := exactK0_powerClassRepresentation_of_isUnit K L ℓ hℓ
  rw [← add_zero (1 + _), ← zero_smul ℕ (permK0 (ZMod ℓ) (L ≃ₐ[K] L) (L ≃ₐ[K] L))] at hPC
  have h := finrank_invariants_kummerH1FiniteRepresentation_tprod_of_exactK0 sigma hN hℓK 0 hPC A
  omega

/-- **The first cohomology of a finite Galois layer, at the residue characteristic.** If `K` and `L`
are finite extensions of `ℚ_p` and `σ(L)` contains the `p`th roots of unity, then for every
finite-dimensional representation `A` of `G = Gal(L/K)` over `𝔽_p` with `p ∤ #G`,
`dim (H¹(Gal(Kˢ/σ(L)), 𝔽_p) ⊗ A)ᴳ = dim (μ_p^∨ ⊗ A)ᴳ + dim Aᴳ + [K : ℚ_p] dim A`. -/
theorem finrank_invariants_kummerH1FiniteRepresentation_tprod_of_finitePadicExtension
    [FinitePadicExtension K ℓ] [FinitePadicExtension L ℓ] (A : FDRep (ZMod ℓ) Gal(L/K)) :
    finrank (ZMod ℓ) (Representation.invariants
        (V := TensorProduct (ZMod ℓ) (H1 sigma.fieldRange.fixingSubgroup (ZMod ℓ)) A)
        ((kummerH1FiniteRepresentation sigma ℓ).tprod A.ρ)) =
      finrank (ZMod ℓ) (Representation.invariants
          (V := TensorProduct (ZMod ℓ) (Module.Dual (ZMod ℓ) (KummerCoeff K ℓ)) A)
          ((kummerCoeffFiniteRepresentation sigma ℓ hN).dual.tprod A.ρ)) +
        finrank (ZMod ℓ) (Representation.invariants A.ρ) +
          finrank ℚ_[ℓ] K * finrank (ZMod ℓ) A := by
  have : CharZero K := FinitePadicExtension.charZero K ℓ
  have hℓK : IsUnit (ℓ : K) := (Nat.cast_ne_zero.2 (NeZero.ne ℓ)).isUnit
  have h := finrank_invariants_kummerH1FiniteRepresentation_tprod_of_exactK0 sigma hN hℓK
    (finrank ℚ_[ℓ] K) (exactK0_powerClassRepresentation_eq_add_finrank_smul K L ℓ) A
  omega

end Count

end TauCeti
