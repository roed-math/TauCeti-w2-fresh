/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Lookahead.GaloisConjugateNewform.Stubs

/-!
# The Galois conjugate of a newform

For a newform `f` of weight `k ≥ 2` and an embedding `σ : K_f → ℂ` of its coefficient field
`K_f = ℚ(aₙ(f) : n)`, the Galois conjugate `f^σ` is the unique newform whose good Hecke
eigensystem is the conjugate of that of `f`. It is *not* obtained by applying `σ` to the
`q`-expansion termwise: `σ` need not be continuous, so it does not act on analytic objects.
Instead, the character of `f` on the rational newspace Hecke algebra takes values in `K_f`,
its composite with `σ` is another character of that algebra, and every character of the algebra
is the character of a newform; strong multiplicity one makes that newform unique.

The conjugate has nebentypus `σ ∘ χ_f` and good Hecke eigenvalues `σ(a_p(f))`, so by the Hecke
recurrences `aₙ(f^σ) = σ(aₙ(f))` at every positive index `n` coprime to the level. When `σ` fixes
the character field `ℚ(χ_f)`, the conjugate is also the newform realizing the conjugate character
of the Hecke algebra of `S_k(N, χ_f)ⁿᵉʷ` over `ℚ(χ_f)`, which contains every `Tₙ`, so then
`aₙ(f^σ) = σ(aₙ(f))` at every positive index `n`.

## Main definitions

* `TauCeti.Newform.heckeTDiamondCuspNewRationalCoefficientCharacter f`: the character of `f` on
  the rational newspace Hecke algebra, valued in `K_f`.
* `TauCeti.Newform.galoisConj hk f σ`: the Galois conjugate `f^σ`.

## Main results

* `TauCeti.Newform.heckeTDiamondCuspNewRationalCharacter_galoisConj`: the character of `f^σ` is
  the conjugate by `σ` of the character of `f`.
* `TauCeti.Newform.eq_galoisConj_iff`: `f^σ` is the unique newform with nebentypus `σ ∘ χ_f` and
  good Hecke eigenvalues `σ(a_p(f))`.
* `TauCeti.Newform.χ_galoisConj`: `χ_{f^σ} = σ ∘ χ_f`.
* `TauCeti.Newform.qExpansion_coeff_galoisConj_prime`: `a_p(f^σ) = σ(a_p(f))` at good primes.
* `TauCeti.Newform.qExpansion_coeff_galoisConj_of_coprime`: `aₙ(f^σ) = σ(aₙ(f))` at every
  positive index coprime to the level.
* `TauCeti.Newform.qExpansion_coeff_galoisConj_of_forall_char`: `aₙ(f^σ) = σ(aₙ(f))` at every
  positive index, for `σ` fixing `ℚ(χ_f)`.

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

/-- Every value of the character of a newform on the rational newspace Hecke algebra lies in
its coefficient field. -/
theorem heckeTDiamondCuspNewRationalCharacter_mem_CoefficientField (f : Newform N k)
    (T : heckeTDiamondCuspNewRationalAlgebra N k) :
    heckeTDiamondCuspNewRationalCharacter f T ∈ CoefficientField f := by
  let P := ((CoefficientField f).toSubalgebra.comap
    (heckeTDiamondCuspNewRationalCharacter f)).map (heckeTDiamondCuspNewRationalAlgebra N k).val
  suffices h : heckeTDiamondCuspNewRationalAlgebra N k ≤ P by
    obtain ⟨S, hS, hST⟩ := h T.2
    rwa [Subtype.ext hST] at hS
  rw [heckeTDiamondCuspNewRationalAlgebra_def]
  refine Algebra.adjoin_le ((heckeTDiamondCuspNewIntegralAlgebra_le_iff N k
    (P.restrictScalars ℤ)).mpr ⟨fun p hp hpN ↦ ?_, fun u ↦ ?_⟩)
  · refine ⟨⟨_, heckeTCuspNewEnd_mem_heckeTDiamondCuspNewRationalAlgebra N k hp hpN⟩, ?_, rfl⟩
    change heckeTDiamondCuspNewRationalCharacter f _ ∈ CoefficientField f
    rw [heckeTDiamondCuspNewRationalCharacter_apply_heckeTCuspNewEnd f hp hpN,
      eigenvalue_eq_qExpansion_coeff f hp hpN]
    exact coeff_mem_CoefficientField f ⟨p, hp.pos⟩
  · refine ⟨⟨_, diamondOpCuspNewEnd_mem_heckeTDiamondCuspNewRationalAlgebra N k u⟩, ?_, rfl⟩
    change heckeTDiamondCuspNewRationalCharacter f _ ∈ CoefficientField f
    rw [heckeTDiamondCuspNewRationalCharacter_apply_diamondOpCuspNewEnd]
    exact char_mem_CoefficientField f u

/-- The character of a newform on the rational newspace Hecke algebra, valued in its
coefficient field. -/
def heckeTDiamondCuspNewRationalCoefficientCharacter (f : Newform N k) :
    heckeTDiamondCuspNewRationalAlgebra N k →ₐ[ℚ] CoefficientField f :=
  (heckeTDiamondCuspNewRationalCharacter f).codRestrict (CoefficientField f).toSubalgebra
    (heckeTDiamondCuspNewRationalCharacter_mem_CoefficientField f)

@[simp]
theorem coe_heckeTDiamondCuspNewRationalCoefficientCharacter_apply (f : Newform N k)
    (T : heckeTDiamondCuspNewRationalAlgebra N k) :
    (heckeTDiamondCuspNewRationalCoefficientCharacter f T : ℂ) =
      heckeTDiamondCuspNewRationalCharacter f T :=
  (rfl)

/-- The **Galois conjugate** `f^σ` of a newform `f` of weight at least two by an embedding `σ`
of its coefficient field: the newform whose character on the rational newspace Hecke algebra is
the conjugate by `σ` of that of `f`. It exists since every character of that algebra is the
character of a newform, and it is unique by strong multiplicity one. -/
def galoisConj (hk : 2 ≤ k) (f : Newform N k) (σ : CoefficientField f →ₐ[ℚ] ℂ) : Newform N k :=
  (exists_heckeTDiamondCuspNewRationalCharacter_eq hk
    (σ.comp (heckeTDiamondCuspNewRationalCoefficientCharacter f))).choose

variable (hk : 2 ≤ k) (f : Newform N k) (σ : CoefficientField f →ₐ[ℚ] ℂ)

/-- The character of `f^σ` on the rational newspace Hecke algebra is the conjugate by `σ` of the
character of `f`. -/
theorem heckeTDiamondCuspNewRationalCharacter_galoisConj :
    heckeTDiamondCuspNewRationalCharacter (galoisConj hk f σ) =
      σ.comp (heckeTDiamondCuspNewRationalCoefficientCharacter f) :=
  (exists_heckeTDiamondCuspNewRationalCharacter_eq hk _).choose_spec

/-- **The nebentypus of the Galois conjugate**: `χ_{f^σ} = σ ∘ χ_f`. -/
@[simp]
theorem χ_galoisConj (u : (ZMod N)ˣ) :
    ((galoisConj hk f σ).χ u : ℂ) = σ ⟨f.χ u, char_mem_CoefficientField f u⟩ := by
  have h := DFunLike.congr_fun (heckeTDiamondCuspNewRationalCharacter_galoisConj hk f σ)
    ⟨_, diamondOpCuspNewEnd_mem_heckeTDiamondCuspNewRationalAlgebra N k u⟩
  rw [heckeTDiamondCuspNewRationalCharacter_apply_diamondOpCuspNewEnd] at h
  rw [h, AlgHom.comp_apply]
  congr 1
  exact Subtype.ext (heckeTDiamondCuspNewRationalCharacter_apply_diamondOpCuspNewEnd f u)

/-- The good Hecke eigenvalues of the Galois conjugate are the conjugates of those of `f`. -/
theorem eigenvalue_galoisConj {p : ℕ} (hp : p.Prime) (hpN : Nat.Coprime p N) :
    (galoisConj hk f σ).eigenvalue ⟨p, hp.pos⟩ hpN =
      σ ⟨(qExpansion 1 f.toCuspForm).coeff p, coeff_mem_CoefficientField f ⟨p, hp.pos⟩⟩ := by
  have h := DFunLike.congr_fun (heckeTDiamondCuspNewRationalCharacter_galoisConj hk f σ)
    ⟨_, heckeTCuspNewEnd_mem_heckeTDiamondCuspNewRationalAlgebra N k hp hpN⟩
  rw [heckeTDiamondCuspNewRationalCharacter_apply_heckeTCuspNewEnd] at h
  rw [h, AlgHom.comp_apply]
  congr 1
  exact Subtype.ext ((heckeTDiamondCuspNewRationalCharacter_apply_heckeTCuspNewEnd f hp hpN).trans
    (eigenvalue_eq_qExpansion_coeff f hp hpN))

/-- **The good Fourier coefficients of the Galois conjugate**: `a_p(f^σ) = σ(a_p(f))` at every
prime `p` not dividing the level. -/
theorem qExpansion_coeff_galoisConj_prime {p : ℕ} (hp : p.Prime) (hpN : Nat.Coprime p N) :
    (qExpansion 1 (galoisConj hk f σ).toCuspForm).coeff p =
      σ ⟨(qExpansion 1 f.toCuspForm).coeff p, coeff_mem_CoefficientField f ⟨p, hp.pos⟩⟩ := by
  rw [← eigenvalue_eq_qExpansion_coeff _ hp hpN, eigenvalue_galoisConj hk f σ hp hpN]

/-- The induction behind `qExpansion_coeff_galoisConj_of_coprime`, over the prime powers and
coprime products of good indices, stated for any element of `K_f` lifting `aₙ(f)` so that the
membership proofs do not get in the way. -/
private theorem qExpansion_coeff_galoisConj_of_coprime_aux (n : ℕ) (hn₀ : 0 < n)
    (hn : Nat.Coprime n N) (x : CoefficientField f)
    (hx : (x : ℂ) = (qExpansion 1 f.toCuspForm).coeff n) :
    (qExpansion 1 (galoisConj hk f σ).toCuspForm).coeff n = σ x := by
  have h₁ : ∀ x : CoefficientField f, (x : ℂ) = (qExpansion 1 f.toCuspForm).coeff 1 →
      (qExpansion 1 (galoisConj hk f σ).toCuspForm).coeff 1 = σ x := fun x hx ↦ by
    rw [(galoisConj hk f σ).isNorm, show x = 1 from Subtype.ext (hx.trans f.isNorm), map_one]
  induction n using Nat.recOnPosPrimePosCoprime generalizing x with
  | zero => exact absurd hn₀ (lt_irrefl 0)
  | one => exact h₁ x hx
  | prime_pow p r hp hr =>
    have hpN : Nat.Coprime p N := Nat.Coprime.coprime_dvd_left (dvd_pow_self p hr.ne') hn
    clear hn₀ hn hr
    induction r using Nat.twoStepInduction generalizing x with
    | zero => exact h₁ x (by simpa using hx)
    | one =>
      rw [pow_one] at hx ⊢
      rw [qExpansion_coeff_galoisConj_prime hk f σ hp hpN]
      exact congrArg σ (Subtype.ext hx.symm)
    | more r ih₀ ih₁ =>
      set u := ZMod.unitOfCoprime p hpN
      let a (m : ℕ) : CoefficientField f :=
        ⟨_, coeff_mem_CoefficientField f ⟨p ^ m, pow_pos hp.pos m⟩⟩
      let ap : CoefficientField f := ⟨_, coeff_mem_CoefficientField f ⟨p, hp.pos⟩⟩
      have hrec := (galoisConj hk f σ).toEigenformAwayFromLevel.qExpansion_coeff_prime_pow_add_two
        (galoisConj hk f σ).isNorm (p := ⟨p, hp.pos⟩) hp hpN r
      have hrecf := f.toEigenformAwayFromLevel.qExpansion_coeff_prime_pow_add_two f.isNorm
        (p := ⟨p, hp.pos⟩) hp hpN r
      have hx' : x = ap * a (r + 1) -
          ⟨f.χ u, char_mem_CoefficientField f u⟩ * (p : CoefficientField f) ^ (k - 1) * a r :=
        Subtype.ext (hx.trans hrecf)
      simp only [PNat.mk_coe] at hrec
      rw [hrec, ih₀ (a r) rfl, ih₁ (a (r + 1)) rfl, qExpansion_coeff_galoisConj_prime hk f σ hp hpN,
        hx', map_sub, map_mul, map_mul, map_mul, map_zpow₀, map_natCast]
      exact congrArg₂ (· - ·) rfl
        (congrArg₂ (· * ·) (congrArg₂ (· * ·) (χ_galoisConj hk f σ u) rfl) rfl)
  | coprime a b ha hb hab iha ihb =>
    have haN := Nat.Coprime.coprime_mul_right hn
    have hbN := Nat.Coprime.coprime_mul_left hn
    have hrec := (galoisConj hk f σ).toEigenformAwayFromLevel.qExpansion_coeff_mul
      (galoisConj hk f σ).isNorm (m := ⟨a, by omega⟩) (n := ⟨b, by omega⟩) hab haN hbN
    have hrecf := f.toEigenformAwayFromLevel.qExpansion_coeff_mul f.isNorm
      (m := ⟨a, by omega⟩) (n := ⟨b, by omega⟩) hab haN hbN
    let xa : CoefficientField f := ⟨_, coeff_mem_CoefficientField f ⟨a, by omega⟩⟩
    let xb : CoefficientField f := ⟨_, coeff_mem_CoefficientField f ⟨b, by omega⟩⟩
    simp only [PNat.mk_coe] at hrec
    rw [hrec, iha (by omega) haN xa rfl, ihb (by omega) hbN xb rfl, ← map_mul]
    exact congrArg σ (Subtype.ext (hx.trans hrecf).symm)

/-- **The good Fourier coefficients of the Galois conjugate**: `aₙ(f^σ) = σ(aₙ(f))` at every
positive index `n` coprime to the level. -/
theorem qExpansion_coeff_galoisConj_of_coprime (n : ℕ+) (hn : Nat.Coprime (n : ℕ) N) :
    (qExpansion 1 (galoisConj hk f σ).toCuspForm).coeff n =
      σ ⟨(qExpansion 1 f.toCuspForm).coeff n, coeff_mem_CoefficientField f n⟩ :=
  qExpansion_coeff_galoisConj_of_coprime_aux hk f σ n n.pos hn _ rfl

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

/-- An embedding of the coefficient field fixing the nebentypus values fixes the character
field `ℚ(χ_f)`, so it is an embedding over `ℚ(χ_f)`. -/
private def extendScalarsAlgHom
    (hσ : ∀ u, σ ⟨f.χ u, char_mem_CoefficientField f u⟩ = f.χ u) :
    IntermediateField.extendScalars (CharacterField_le_CoefficientField_of_χ_eq f rfl)
      →ₐ[CharacterField f.χ] ℂ where
  toFun x := σ ⟨x, x.2⟩
  map_one' := σ.map_one
  map_mul' x y := σ.map_mul ⟨x, x.2⟩ ⟨y, y.2⟩
  map_zero' := σ.map_zero
  map_add' x y := σ.map_add ⟨x, x.2⟩ ⟨y, y.2⟩
  commutes' c := by
    have h : σ.comp (IntermediateField.inclusion (CharacterField_le_CoefficientField f)) =
        (CharacterField f.χ).val :=
      IntermediateField.algHom_ext_of_eq_adjoin ℚ (CharacterField_def f.χ) <| by
        rintro _ ⟨u, rfl⟩
        exact hσ u
    exact DFunLike.congr_fun h c

/-- **The Fourier coefficients of the Galois conjugate by an embedding fixing `ℚ(χ_f)`**:
`aₙ(f^σ) = σ(aₙ(f))` at every positive index `n`, the indices sharing a factor with the level
included. -/
theorem qExpansion_coeff_galoisConj_of_forall_char
    (hσ : ∀ u, σ ⟨f.χ u, char_mem_CoefficientField f u⟩ = f.χ u) (n : ℕ+) :
    (qExpansion 1 (galoisConj hk f σ).toCuspForm).coeff n =
      σ ⟨(qExpansion 1 f.toCuspForm).coeff n, coeff_mem_CoefficientField f n⟩ := by
  obtain ⟨g, hg⟩ := exists_heckeTCuspNewCharFieldCharacter_eq hk
    (conjHeckeTCuspNewCharFieldCharacter ⟨f, rfl⟩ (extendScalarsAlgHom f σ hσ))
  have hcoeff : ∀ m : ℕ+, (qExpansion 1 g.1.toCuspForm).coeff m =
      σ ⟨(qExpansion 1 f.toCuspForm).coeff m, coeff_mem_CoefficientField f m⟩ := fun m ↦ by
    rw [← heckeTCuspNewCharFieldCharacter_apply_heckeTCuspNewCharEnd, hg,
      conjHeckeTCuspNewCharFieldCharacter_apply_heckeTCuspNewCharEnd]
    rfl
  have hgσ : g.1 = galoisConj hk f σ := by
    refine (eq_galoisConj_iff hk f σ g.1).mpr ⟨fun u ↦ ?_, fun p hp hpN ↦ ?_⟩
    · rw [g.2, hσ]
    · rw [eigenvalue_eq_qExpansion_coeff _ hp hpN]
      exact hcoeff ⟨p, hp.pos⟩
  rw [← hgσ, hcoeff]

end Newform

end TauCeti
