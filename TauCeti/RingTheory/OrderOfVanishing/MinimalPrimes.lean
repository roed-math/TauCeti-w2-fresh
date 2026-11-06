/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import TauCeti.RingTheory.Length
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Support

/-!
# The order of vanishing as a sum over minimal primes

Let `A` be a Noetherian ring of Krull dimension at most one and `a` a non-zero-divisor of `A`.
The order of vanishing `Ring.ord A a = length (A ⧸ aA)` splits over the minimal primes `𝔮` of `A`:
each contributes the order of `a` on the integral quotient `A ⧸ 𝔮`, counted with the multiplicity
`length_{A_𝔮} (A_𝔮)` of `A` at `𝔮` (Stacks, Section 42.3; Fulton, Appendix A.3).

The proof is the prime-filtration argument of Stacks, Section 42.3, for the length index
`e(M, a) = length (M ⧸ aM) - length (ker a)` of a finite module `M`. It is additive in short exact
sequences (`TauCeti.length_ker_add_length_quotient_range_eq_of_exact`, from the snake lemma), so by
Mathlib's `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime` it suffices to compute it on
`A ⧸ 𝔭` for a prime `𝔭`. A minimal `𝔭` does not contain `a`, and `e(A ⧸ 𝔭, a)` is the order of `a`
in `A ⧸ 𝔭`. Any other `𝔭` is maximal, as `A` has dimension at most one
(`Ring.krullDimLE_one_iff`), so `A ⧸ 𝔭` has finite length and `e(A ⧸ 𝔭, a) = 0`. Since `e` takes
values in `ℕ∞` here, it is stated without subtraction, as
`length (ker a) + ∑ᶠ 𝔮, length (M_𝔮) * ord_{A ⧸ 𝔮} (a) = length (M ⧸ aM)`.

## Main results

* `TauCeti.subsingleton_localizedModule_quotient`: `(A ⧸ 𝔭)_𝔮 = 0` unless `𝔭 ≤ 𝔮`.
* `TauCeti.length_ker_lsmul_ne_top`: multiplication by a non-zero-divisor on a finite module has a
  kernel of finite length.
* `TauCeti.length_ker_lsmul_add_finsum_eq`: the formula for the length index of a finite module.
* `TauCeti.Ring.ord_eq_finsum_minimalPrimes`: the order of vanishing of a non-zero-divisor as a sum
  over the minimal primes.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors

variable {A : Type*} [CommRing A]

/-- The localization of `A ⧸ 𝔭` at a prime `𝔮` vanishes unless `𝔭 ≤ 𝔮`. -/
theorem subsingleton_localizedModule_quotient {𝔭 : Ideal A} {𝔮 : PrimeSpectrum A}
    (h : ¬𝔭 ≤ 𝔮.asIdeal) : Subsingleton (LocalizedModule 𝔮.asIdeal.primeCompl (A ⧸ 𝔭)) := by
  rw [← Module.notMem_support_iff, Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
  exact h

variable [IsNoetherianRing A] [Ring.KrullDimLE 1 A] {a : A}

/-- In a Noetherian ring of dimension at most one, multiplication by a non-zero-divisor on a finite
module has a kernel of finite length: the kernel is a finite module killed by it. -/
theorem length_ker_lsmul_ne_top (ha : a ∈ A⁰) (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Finite A M] : Module.length A (LinearMap.ker (LinearMap.lsmul A M a)) ≠ ⊤ :=
  Module.length_ne_top_iff.mpr <| isFiniteLength_of_nonZeroDivisor_mem_annihilator
    (Module.mem_annihilator.mpr fun x => Subtype.ext x.2) ha

/-- **The length index of a finite module over its minimal primes** (Stacks, Section 42.3). Let
`A` be a Noetherian ring of dimension at most one, `a` a non-zero-divisor and `M` a finite
`A`-module. Then `length (M ⧸ aM) - length (ker a) = ∑ 𝔮, length_{A_𝔮} (M_𝔮) * ord_{A ⧸ 𝔮} (a)`,
the sum running over the minimal primes `𝔮` of `A`; it is stated here without subtraction. -/
theorem length_ker_lsmul_add_finsum_eq (ha : a ∈ A⁰) (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    Module.length A (LinearMap.ker (LinearMap.lsmul A M a)) +
        ∑ᶠ 𝔮 : {𝔮 : PrimeSpectrum A // 𝔮.asIdeal ∈ minimalPrimes A},
          Module.length (Localization.AtPrime 𝔮.1.asIdeal)
              (LocalizedModule 𝔮.1.asIdeal.primeCompl M) *
            Ring.ord (A ⧸ 𝔮.1.asIdeal) (Ideal.Quotient.mk _ a) =
      Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M a)) := by
  have : Finite (minimalPrimes A) := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
  have : Finite {𝔮 : PrimeSpectrum A // 𝔮.asIdeal ∈ minimalPrimes A} :=
    Finite.of_injective (fun 𝔮 => (⟨𝔮.1.asIdeal, 𝔮.2⟩ : minimalPrimes A))
      fun _ _ h => Subtype.ext (PrimeSpectrum.ext (congrArg Subtype.val h))
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A inferInstance
    (motive := fun N _ _ _ => Module.length A (LinearMap.ker (LinearMap.lsmul A N a)) +
        ∑ᶠ 𝔮 : {𝔮 : PrimeSpectrum A // 𝔮.asIdeal ∈ minimalPrimes A},
          Module.length (Localization.AtPrime 𝔮.1.asIdeal)
              (LocalizedModule 𝔮.1.asIdeal.primeCompl N) *
            Ring.ord (A ⧸ 𝔮.1.asIdeal) (Ideal.Quotient.mk _ a) =
      Module.length A (N ⧸ LinearMap.range (LinearMap.lsmul A N a))) ?_ ?_ ?_
  · intro N _ _ _ _
    have (𝔮 : PrimeSpectrum A) : Subsingleton (LocalizedModule 𝔮.asIdeal.primeCompl N) := by
      rw [← Module.notMem_support_iff, Module.support_eq_empty]
      exact Set.notMem_empty _
    simp [Module.length_eq_zero]
  · intro N _ _ _ 𝔭 e
    -- Transport the three quantities along `e : N ≃ A ⧸ 𝔭`.
    have hker : (LinearMap.ker (LinearMap.lsmul A N a)).map e.toLinearMap
        = LinearMap.ker (LinearMap.lsmul A (A ⧸ 𝔭.asIdeal) a) := by
      ext x
      simp only [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.lsmul_apply]
      rw [← map_smul, e.symm.map_eq_zero_iff]
    have hloc (𝔮 : PrimeSpectrum A) :
        Module.length (Localization.AtPrime 𝔮.asIdeal) (LocalizedModule 𝔮.asIdeal.primeCompl N)
          = Module.length (Localization.AtPrime 𝔮.asIdeal)
              (LocalizedModule 𝔮.asIdeal.primeCompl (A ⧸ 𝔭.asIdeal)) :=
      (LinearEquiv.ofBijective (LocalizedModule.map 𝔮.asIdeal.primeCompl e.toLinearMap)
        ⟨LocalizedModule.map_injective _ _ e.injective,
          LocalizedModule.map_surjective _ _ e.surjective⟩).length_eq
    rw [(LinearEquiv.ofSubmodules e _ _ hker).length_eq, length_quotient_lsmul_congr e]
    simp_rw [hloc]
    -- A summand vanishes unless `𝔭 ≤ 𝔮`, which for a minimal `𝔮` forces `𝔮 = 𝔭`.
    have hterm (𝔮 : {𝔮 : PrimeSpectrum A // 𝔮.asIdeal ∈ minimalPrimes A}) (h𝔮 : 𝔮.1 ≠ 𝔭) :
        Module.length (Localization.AtPrime 𝔮.1.asIdeal)
          (LocalizedModule 𝔮.1.asIdeal.primeCompl (A ⧸ 𝔭.asIdeal)) = 0 := by
      have : ¬𝔭.asIdeal ≤ 𝔮.1.asIdeal := fun hle => h𝔮 (PrimeSpectrum.ext
        (le_antisymm (𝔮.2.2 ⟨𝔭.2, bot_le⟩ hle) hle))
      have := subsingleton_localizedModule_quotient this
      exact Module.length_eq_zero
    by_cases h𝔭 : 𝔭.asIdeal ∈ minimalPrimes A
    · have ha𝔭 : a ∉ 𝔭.asIdeal := fun h =>
        Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes h𝔭) h ha
      have hker0 : LinearMap.ker (LinearMap.lsmul A (A ⧸ 𝔭.asIdeal) a) = ⊥ := by
        refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
        rw [LinearMap.mem_ker, LinearMap.lsmul_apply, Algebra.smul_def,
          Ideal.Quotient.algebraMap_eq, mul_eq_zero] at hx
        exact hx.resolve_left (Ideal.Quotient.eq_zero_iff_mem.not.mpr ha𝔭)
      rw [hker0, Module.length_bot, zero_add, length_quotient_lsmul_quotient_eq_ord,
        finsum_eq_single _ ⟨𝔭, h𝔭⟩ fun 𝔮 h𝔮 => by
          rw [hterm 𝔮 fun h => h𝔮 (Subtype.ext h), zero_mul]]
      rw [Ideal.length_localizedModule_quotient_eq_one, one_mul]
    · have : 𝔭.asIdeal.IsMaximal :=
        (Ring.krullDimLE_one_iff.mp inferInstance 𝔭.asIdeal inferInstance).resolve_left h𝔭
      have : IsSimpleModule A (A ⧸ 𝔭.asIdeal) := isSimpleModule_iff_isCoatom.mpr this.out
      have hfin : Module.length A (A ⧸ 𝔭.asIdeal) ≠ ⊤ := by
        rw [Module.length_eq_one_iff.mpr this]
        exact ENat.one_ne_top
      rw [length_ker_eq_length_quotient_range _ hfin]
      have : ∀ 𝔮 : {𝔮 : PrimeSpectrum A // 𝔮.asIdeal ∈ minimalPrimes A},
          Module.length (Localization.AtPrime 𝔮.1.asIdeal)
            (LocalizedModule 𝔮.1.asIdeal.primeCompl (A ⧸ 𝔭.asIdeal)) = 0 :=
        fun 𝔮 => hterm 𝔮 fun h => h𝔭 (h ▸ 𝔮.2)
      simp [this]
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg ih₁ ih₃
    have hsnake := length_ker_add_length_quotient_range_eq_of_exact hf hfg hg
      (φN := LinearMap.lsmul A N₁ a) (φM := LinearMap.lsmul A N₂ a)
      (φP := LinearMap.lsmul A N₃ a) (LinearMap.ext fun x => map_smul f a x)
      (LinearMap.ext fun x => map_smul g a x)
    have hloc (𝔮 : PrimeSpectrum A) :
        Module.length (Localization.AtPrime 𝔮.asIdeal) (LocalizedModule 𝔮.asIdeal.primeCompl N₂)
          = Module.length (Localization.AtPrime 𝔮.asIdeal)
              (LocalizedModule 𝔮.asIdeal.primeCompl N₁) +
            Module.length (Localization.AtPrime 𝔮.asIdeal)
              (LocalizedModule 𝔮.asIdeal.primeCompl N₃) :=
      Module.length_eq_add_of_exact (LocalizedModule.map 𝔮.asIdeal.primeCompl f)
        (LocalizedModule.map 𝔮.asIdeal.primeCompl g) (LocalizedModule.map_injective _ _ hf)
        (LocalizedModule.map_surjective _ _ hg) (LocalizedModule.map_exact _ _ _ hfg)
    simp_rw [hloc, add_mul]
    rw [finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
    set S₁ := ∑ᶠ 𝔮 : {𝔮 : PrimeSpectrum A // 𝔮.asIdeal ∈ minimalPrimes A},
      Module.length (Localization.AtPrime 𝔮.1.asIdeal)
          (LocalizedModule 𝔮.1.asIdeal.primeCompl N₁) *
        Ring.ord (A ⧸ 𝔮.1.asIdeal) (Ideal.Quotient.mk _ a)
    set S₃ := ∑ᶠ 𝔮 : {𝔮 : PrimeSpectrum A // 𝔮.asIdeal ∈ minimalPrimes A},
      Module.length (Localization.AtPrime 𝔮.1.asIdeal)
          (LocalizedModule 𝔮.1.asIdeal.primeCompl N₃) *
        Ring.ord (A ⧸ 𝔮.1.asIdeal) (Ideal.Quotient.mk _ a)
    set K₁ := Module.length A (LinearMap.ker (LinearMap.lsmul A N₁ a))
    set K₃ := Module.length A (LinearMap.ker (LinearMap.lsmul A N₃ a))
    have hK : K₁ + K₃ ≠ ⊤ :=
      WithTop.add_ne_top.mpr ⟨length_ker_lsmul_ne_top ha N₁, length_ker_lsmul_ne_top ha N₃⟩
    have key : Module.length A (LinearMap.ker (LinearMap.lsmul A N₂ a)) + (S₁ + S₃) + (K₁ + K₃) =
        Module.length A (N₂ ⧸ LinearMap.range (LinearMap.lsmul A N₂ a)) + (K₁ + K₃) := by
      calc _ = Module.length A (LinearMap.ker (LinearMap.lsmul A N₂ a)) + (K₁ + S₁) +
              (K₃ + S₃) := by ac_rfl
        _ = K₁ + K₃ + Module.length A (N₂ ⧸ LinearMap.range (LinearMap.lsmul A N₂ a)) := by
            rw [ih₁, ih₃]; exact hsnake
        _ = _ := add_comm _ _
    exact WithTop.add_right_cancel hK key

namespace Ring

/-- **The order of vanishing over the minimal primes** (Stacks, Section 42.3; Fulton,
Appendix A.3). For a non-zero-divisor `a` of a Noetherian ring `A` of dimension at most one,
`ord_A (a) = ∑ 𝔮, length_{A_𝔮} (A_𝔮) * ord_{A ⧸ 𝔮} (a)`, the sum running over the minimal primes
`𝔮` of `A`. This is `TauCeti.length_ker_lsmul_add_finsum_eq` for `M = A`, on which `a` acts
injectively. -/
theorem ord_eq_finsum_minimalPrimes (ha : a ∈ A⁰) :
    _root_.Ring.ord A a =
      ∑ᶠ 𝔮 : {𝔮 : PrimeSpectrum A // 𝔮.asIdeal ∈ minimalPrimes A},
        Module.length (Localization.AtPrime 𝔮.1.asIdeal) (Localization.AtPrime 𝔮.1.asIdeal) *
          _root_.Ring.ord (A ⧸ 𝔮.1.asIdeal) (Ideal.Quotient.mk _ a) := by
  have h := length_ker_lsmul_add_finsum_eq ha A
  have hker : LinearMap.ker (LinearMap.lsmul A A a) = ⊥ :=
    (Submodule.eq_bot_iff _).mpr fun x hx => by
      rw [LinearMap.mem_ker, LinearMap.lsmul_apply, smul_eq_mul] at hx
      exact (mem_nonZeroDivisors_iff_right.mp ha) x (by rw [mul_comm]; exact hx)
  have hspan : LinearMap.range (LinearMap.lsmul A A a) = Ideal.span {a} := by
    ext y
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply, smul_eq_mul, Ideal.mem_span_singleton']
    exact ⟨fun ⟨c, hc⟩ => ⟨c, by rw [← hc, mul_comm]⟩, fun ⟨c, hc⟩ => ⟨c, by rw [← hc, mul_comm]⟩⟩
  have hloc (𝔮 : PrimeSpectrum A) :
      Module.length (Localization.AtPrime 𝔮.asIdeal) (LocalizedModule 𝔮.asIdeal.primeCompl A)
        = Module.length (Localization.AtPrime 𝔮.asIdeal) (Localization.AtPrime 𝔮.asIdeal) := by
    have := IsLocalization.linearMap_compatibleSMul 𝔮.asIdeal.primeCompl
      (Localization.AtPrime 𝔮.asIdeal)
    exact ((IsLocalizedModule.linearEquiv 𝔮.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap 𝔮.asIdeal.primeCompl A)
      (Algebra.linearMap A (Localization.AtPrime 𝔮.asIdeal))).restrictScalars
        (Localization.AtPrime 𝔮.asIdeal)).length_eq
  rw [hker, Module.length_bot, zero_add, hspan] at h
  simp_rw [hloc] at h
  exact h.symm

end Ring

end TauCeti
