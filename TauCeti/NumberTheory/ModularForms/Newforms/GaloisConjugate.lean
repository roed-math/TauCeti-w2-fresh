/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Lookahead.GaloisConjugateNewform.Stubs
public import TauCeti.NumberTheory.ModularForms.Newforms.Fields
import TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.Primes

/-!
# The Galois conjugate of a newform

For a newform `f` of weight `k ≥ 2` and an embedding `σ : K_f → ℂ` of its coefficient field
`K_f = ℚ(aₙ(f) : n)`, the Galois conjugate `f^σ` is the unique normalized newform with the
conjugated eigensystem. It is *not* obtained by applying `σ` to the `q`-expansion termwise: `σ`
need not be continuous, so it does not act on analytic objects. Instead, the character of `f`
on the rational Hecke algebra generated on the newspace by every `T_p` and the diamond operators
takes values in `K_f`, its composite with `σ` is another character of that algebra, and every
character of the algebra is the character of a newform; strong multiplicity one makes that
newform unique.

The conjugate has nebentypus `σ ∘ χ_f` and prime coefficients `σ(a_p(f))` at every prime `p`,
so by the Hecke recurrences at good primes, the geometric coefficients at the primes dividing
the level and multiplicativity, `aₙ(f^σ) = σ(aₙ(f))` at every positive index `n`.

## Main definitions

* `TauCeti.Newform.heckeTDiamondCuspNewFullRationalCoefficientCharacter f`: the character of `f`
  on the full rational newspace Hecke algebra, valued in `K_f`.
* `TauCeti.Newform.galoisConj hk f σ`: the Galois conjugate `f^σ`.

## Main results

* `TauCeti.Newform.heckeTDiamondCuspNewFullRationalCharacter_galoisConj`: the character of `f^σ`
  is the conjugate by `σ` of the character of `f`.
* `TauCeti.Newform.eq_galoisConj_iff`: `f^σ` is the unique newform with nebentypus `σ ∘ χ_f` and
  good Hecke eigenvalues `σ(a_p(f))`.
* `TauCeti.Newform.χ_galoisConj`: `χ_{f^σ} = σ ∘ χ_f`.
* `TauCeti.Newform.qExpansion_coeff_galoisConj`: `aₙ(f^σ) = σ(aₙ(f))` at every positive index.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  §6.5, for the Galois conjugates of newforms.
-/

public noncomputable section

open UpperHalfPlane HeckeRing.GL2

namespace TauCeti

namespace Newform

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The good Hecke eigenvalues of a newform are its Fourier coefficients. -/
private theorem eigenvalue_eq_qExpansion_coeff (f : Newform N k) {p : ℕ} (hp : p.Prime)
    (hpN : Nat.Coprime p N) :
    f.eigenvalue ⟨p, hp.pos⟩ hpN = (qExpansion 1 f.toCuspForm).coeff p :=
  (f.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue f.isNorm ⟨p, hp.pos⟩ hpN).symm

/-- Every value of the character of a newform on the full rational newspace Hecke algebra lies
in its coefficient field. -/
theorem heckeTDiamondCuspNewFullRationalCharacter_mem_CoefficientField (f : Newform N k)
    (T : heckeTDiamondCuspNewFullRationalAlgebra N k) :
    heckeTDiamondCuspNewFullRationalCharacter f T ∈ CoefficientField f := by
  let P := ((CoefficientField f).toSubalgebra.comap
    (heckeTDiamondCuspNewFullRationalCharacter f)).map
      (heckeTDiamondCuspNewFullRationalAlgebra N k).val
  suffices h : heckeTDiamondCuspNewFullRationalAlgebra N k ≤ P by
    obtain ⟨S, hS, hST⟩ := h T.2
    rwa [Subtype.ext hST] at hS
  refine (heckeTDiamondCuspNewFullRationalAlgebra_le_iff N k P).mpr
    ⟨fun p hp ↦ ?_, fun u ↦ ?_⟩
  · refine ⟨⟨_, heckeTCuspNatNewEnd_mem_heckeTDiamondCuspNewFullRationalAlgebra N k hp⟩, ?_,
      rfl⟩
    change heckeTDiamondCuspNewFullRationalCharacter f _ ∈ CoefficientField f
    rw [heckeTDiamondCuspNewFullRationalCharacter_apply_heckeTCuspNatNewEnd]
    exact coeff_mem_CoefficientField f ⟨p, hp.pos⟩
  · refine ⟨⟨_, diamondOpCuspNewEnd_mem_heckeTDiamondCuspNewFullRationalAlgebra N k u⟩, ?_, rfl⟩
    change heckeTDiamondCuspNewFullRationalCharacter f _ ∈ CoefficientField f
    rw [heckeTDiamondCuspNewFullRationalCharacter_apply_diamondOpCuspNewEnd]
    exact char_mem_CoefficientField f u

/-- The character of a newform on the full rational newspace Hecke algebra, valued in its
coefficient field. -/
def heckeTDiamondCuspNewFullRationalCoefficientCharacter (f : Newform N k) :
    heckeTDiamondCuspNewFullRationalAlgebra N k →ₐ[ℚ] CoefficientField f :=
  (heckeTDiamondCuspNewFullRationalCharacter f).codRestrict (CoefficientField f).toSubalgebra
    (heckeTDiamondCuspNewFullRationalCharacter_mem_CoefficientField f)

@[simp]
theorem coe_heckeTDiamondCuspNewFullRationalCoefficientCharacter_apply (f : Newform N k)
    (T : heckeTDiamondCuspNewFullRationalAlgebra N k) :
    (heckeTDiamondCuspNewFullRationalCoefficientCharacter f T : ℂ) =
      heckeTDiamondCuspNewFullRationalCharacter f T :=
  (rfl)

/-- The **Galois conjugate** `f^σ` of a newform `f` of weight at least two by an embedding `σ`
of its coefficient field: the newform whose character on the full rational newspace Hecke
algebra is the conjugate by `σ` of that of `f`. It exists since every character of that algebra
is the character of a newform, and it is unique by strong multiplicity one. -/
def galoisConj (hk : 2 ≤ k) (f : Newform N k) (σ : CoefficientField f →ₐ[ℚ] ℂ) : Newform N k :=
  (exists_heckeTDiamondCuspNewFullRationalCharacter_eq hk
    (σ.comp (heckeTDiamondCuspNewFullRationalCoefficientCharacter f))).choose

variable (hk : 2 ≤ k) (f : Newform N k) (σ : CoefficientField f →ₐ[ℚ] ℂ)

/-- The character of `f^σ` on the full rational newspace Hecke algebra is the conjugate by `σ`
of the character of `f`. -/
theorem heckeTDiamondCuspNewFullRationalCharacter_galoisConj :
    heckeTDiamondCuspNewFullRationalCharacter (galoisConj hk f σ) =
      σ.comp (heckeTDiamondCuspNewFullRationalCoefficientCharacter f) :=
  (exists_heckeTDiamondCuspNewFullRationalCharacter_eq hk _).choose_spec

/-- **The nebentypus of the Galois conjugate**: `χ_{f^σ} = σ ∘ χ_f`. -/
@[simp]
theorem χ_galoisConj (u : (ZMod N)ˣ) :
    ((galoisConj hk f σ).χ u : ℂ) = σ ⟨f.χ u, char_mem_CoefficientField f u⟩ := by
  have h := DFunLike.congr_fun (heckeTDiamondCuspNewFullRationalCharacter_galoisConj hk f σ)
    ⟨_, diamondOpCuspNewEnd_mem_heckeTDiamondCuspNewFullRationalAlgebra N k u⟩
  rw [heckeTDiamondCuspNewFullRationalCharacter_apply_diamondOpCuspNewEnd] at h
  rw [h, AlgHom.comp_apply]
  congr 1
  exact Subtype.ext (heckeTDiamondCuspNewFullRationalCharacter_apply_diamondOpCuspNewEnd f u)

/-- **The prime Fourier coefficients of the Galois conjugate**: `a_p(f^σ) = σ(a_p(f))` at every
prime `p`, the primes dividing the level included. -/
theorem qExpansion_coeff_galoisConj_prime {p : ℕ} (hp : p.Prime) :
    (qExpansion 1 (galoisConj hk f σ).toCuspForm).coeff p =
      σ ⟨(qExpansion 1 f.toCuspForm).coeff p, coeff_mem_CoefficientField f ⟨p, hp.pos⟩⟩ := by
  have h := DFunLike.congr_fun (heckeTDiamondCuspNewFullRationalCharacter_galoisConj hk f σ)
    ⟨_, heckeTCuspNatNewEnd_mem_heckeTDiamondCuspNewFullRationalAlgebra N k hp⟩
  rw [heckeTDiamondCuspNewFullRationalCharacter_apply_heckeTCuspNatNewEnd] at h
  rw [h, AlgHom.comp_apply]
  congr 1
  exact Subtype.ext (heckeTDiamondCuspNewFullRationalCharacter_apply_heckeTCuspNatNewEnd f hp)

/-- The good Hecke eigenvalues of the Galois conjugate are the conjugates of those of `f`. -/
theorem eigenvalue_galoisConj {p : ℕ} (hp : p.Prime) (hpN : Nat.Coprime p N) :
    (galoisConj hk f σ).eigenvalue ⟨p, hp.pos⟩ hpN =
      σ ⟨(qExpansion 1 f.toCuspForm).coeff p, coeff_mem_CoefficientField f ⟨p, hp.pos⟩⟩ := by
  rw [eigenvalue_eq_qExpansion_coeff _ hp hpN, qExpansion_coeff_galoisConj_prime hk f σ hp]

/-- The induction behind `qExpansion_coeff_galoisConj`, over the prime powers and coprime
products of indices, stated for any element of `K_f` lifting `aₙ(f)` so that the membership
proofs do not get in the way. -/
private theorem qExpansion_coeff_galoisConj_aux (n : ℕ) (hn₀ : 0 < n) (x : CoefficientField f)
    (hx : (x : ℂ) = (qExpansion 1 f.toCuspForm).coeff n) :
    (qExpansion 1 (galoisConj hk f σ).toCuspForm).coeff n = σ x := by
  have h₁ : ∀ x : CoefficientField f, (x : ℂ) = (qExpansion 1 f.toCuspForm).coeff 1 →
      (qExpansion 1 (galoisConj hk f σ).toCuspForm).coeff 1 = σ x := fun x hx ↦ by
    rw [(galoisConj hk f σ).isNorm, show x = 1 from Subtype.ext (hx.trans f.isNorm), map_one]
  induction n using Nat.recOnPosPrimePosCoprime generalizing x with
  | zero => exact absurd hn₀ (lt_irrefl 0)
  | one => exact h₁ x hx
  | prime_pow p r hp hr =>
    clear hn₀ hr
    by_cases hpN : Nat.Coprime p N
    · induction r using Nat.twoStepInduction generalizing x with
      | zero => exact h₁ x (by simpa using hx)
      | one =>
        rw [pow_one] at hx ⊢
        rw [qExpansion_coeff_galoisConj_prime hk f σ hp]
        exact congrArg σ (Subtype.ext hx.symm)
      | more r ih₀ ih₁ =>
        set u := ZMod.unitOfCoprime p hpN
        let a (m : ℕ) : CoefficientField f :=
          ⟨_, coeff_mem_CoefficientField f ⟨p ^ m, pow_pos hp.pos m⟩⟩
        let ap : CoefficientField f := ⟨_, coeff_mem_CoefficientField f ⟨p, hp.pos⟩⟩
        have hrec :=
          (galoisConj hk f σ).toEigenformAwayFromLevel.qExpansion_coeff_prime_pow_add_two
            (galoisConj hk f σ).isNorm (p := ⟨p, hp.pos⟩) hp hpN r
        have hrecf := f.toEigenformAwayFromLevel.qExpansion_coeff_prime_pow_add_two f.isNorm
          (p := ⟨p, hp.pos⟩) hp hpN r
        have hx' : x = ap * a (r + 1) -
            ⟨f.χ u, char_mem_CoefficientField f u⟩ * (p : CoefficientField f) ^ (k - 1) * a r :=
          Subtype.ext (hx.trans hrecf)
        simp only [PNat.mk_coe] at hrec
        rw [hrec, ih₀ (a r) rfl, ih₁ (a (r + 1)) rfl, qExpansion_coeff_galoisConj_prime hk f σ hp,
          hx', map_sub, map_mul, map_mul, map_mul, map_zpow₀, map_natCast]
        exact congrArg₂ (· - ·) rfl
          (congrArg₂ (· * ·) (congrArg₂ (· * ·) (χ_galoisConj hk f σ u) rfl) rfl)
    · -- at a prime dividing the level the coefficients along the powers of `p` are geometric
      have hdvd : p ∣ N := (Nat.Prime.dvd_iff_not_coprime hp).mpr hpN
      rw [HeckeRing.GL2.Newform.qExpansion_coeff_prime_pow_of_mem_badPrimes _
          ((galoisConj hk f σ).mem_badPrimes_iff_dvd.mpr ⟨hp, hdvd⟩),
        qExpansion_coeff_galoisConj_prime hk f σ hp, ← map_pow]
      refine congrArg σ (Subtype.ext ?_)
      rw [SubmonoidClass.coe_pow, hx,
        f.qExpansion_coeff_prime_pow_of_mem_badPrimes (f.mem_badPrimes_iff_dvd.mpr ⟨hp, hdvd⟩)]
  | coprime a b ha hb hab iha ihb =>
    have hrec := (galoisConj hk f σ).toEigenform.qExpansion_coeff_mul
      (galoisConj hk f σ).toEigenform_qExpansion_coeff_one hab
    have hrecf := f.toEigenform.qExpansion_coeff_mul f.toEigenform_qExpansion_coeff_one hab
    simp only [HeckeRing.GL2.Newform.toEigenform_toCuspForm] at hrec hrecf
    let xa : CoefficientField f := ⟨_, coeff_mem_CoefficientField f ⟨a, by omega⟩⟩
    let xb : CoefficientField f := ⟨_, coeff_mem_CoefficientField f ⟨b, by omega⟩⟩
    rw [hrec, iha (by omega) xa rfl, ihb (by omega) xb rfl, ← map_mul]
    exact congrArg σ (Subtype.ext (hx.trans hrecf).symm)

/-- **The Fourier coefficients of the Galois conjugate**: `aₙ(f^σ) = σ(aₙ(f))` at every positive
index `n`. -/
theorem qExpansion_coeff_galoisConj (n : ℕ+) :
    (qExpansion 1 (galoisConj hk f σ).toCuspForm).coeff n =
      σ ⟨(qExpansion 1 f.toCuspForm).coeff n, coeff_mem_CoefficientField f n⟩ :=
  qExpansion_coeff_galoisConj_aux hk f σ n n.pos _ rfl

/-- **Uniqueness of the Galois conjugate**: `f^σ` is the only newform with nebentypus `σ ∘ χ_f`
and good Hecke eigenvalues `σ(a_p(f))`. -/
theorem eq_galoisConj_iff (g : Newform N k) :
    g = galoisConj hk f σ ↔
      (∀ u, (g.χ u : ℂ) = σ ⟨f.χ u, char_mem_CoefficientField f u⟩) ∧
        ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N), g.eigenvalue ⟨p, hp.pos⟩ hpN =
          σ ⟨(qExpansion 1 f.toCuspForm).coeff p, coeff_mem_CoefficientField f ⟨p, hp.pos⟩⟩ := by
  refine ⟨?_, fun ⟨hχ, ha⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨χ_galoisConj hk f σ, fun p hp hpN ↦ eigenvalue_galoisConj hk f σ hp hpN⟩
  · refine Newform.eq_of_forall_prime_eigenvalue_eq ?_ fun p hp hpN ↦ ?_
    · ext u
      rw [hχ, χ_galoisConj]
    · rw [ha p hp hpN, eigenvalue_galoisConj hk f σ hp hpN]

end Newform

end TauCeti
