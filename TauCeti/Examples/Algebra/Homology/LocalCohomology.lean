/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import TauCeti.Algebra.Homology.LocalCohomology.DegreeZero

/-!
# Examples of degree-zero local cohomology

This file computes degree zero of Mathlib's colimit-of-`Ext` local cohomology in two examples,
using `TauCeti.Supports.isZero_localCohomology_zero_iff`.

* For a discrete valuation ring `R` with maximal ideal `m`, `H⁰_m(R) = 0`: every power of `m`
  contains a nonzero element, which is a non-zero-divisor in the domain `R`.
* Let `A = k[x₀, x₁, …]/(x_j^{j+2})` and `I = (x₀, x₁, …)`. Every generator of `I` is nilpotent,
  so `V(I)` is all of `Spec A`, but `I^n ≠ 0` for every `n`: given a nonzero class `a` and `n`, a
  variable `x_N` with `n ≤ N` that does not occur in a representative of `a` gives a nonzero
  product `x_N^n a` with `x_N^n ∈ I^n`. Hence the native `H⁰_I(A)` vanishes, and `A` is not
  Noetherian, since the nilradical of a Noetherian ring is nilpotent. Geometrically, the
  sections of `𝒪` on `Spec A` supported in `V(I) = Spec A` are all of `A ≠ 0`, so this is the
  example showing that the colimit-of-`Ext` functor does not compute cohomology with supports
  without a Noetherian hypothesis.

## Main declarations

* `TauCeti.Supports.isZero_localCohomology_zero_self_of_ne_bot`: `H⁰_I(A) = 0` for a domain `A`
  and `I ≠ 0`, and `TauCeti.Supports.isZero_localCohomology_zero_maximalIdeal` for a discrete
  valuation ring.
* `TauCeti.Supports.NilIdealExample.CoordRing k`: the ring `k[x₀, x₁, …]/(x_j^{j+2})`, and
  `TauCeti.Supports.NilIdealExample.ideal k`: its ideal `(x₀, x₁, …)`.
* `TauCeti.Supports.NilIdealExample.zeroLocus_ideal`: `V(I) = Spec A`.
* `TauCeti.Supports.NilIdealExample.not_isNoetherianRing`: `A` is not Noetherian.
* `TauCeti.Supports.NilIdealExample.isZero_localCohomology_zero`: `H⁰_I(A) = 0`.
-/

public section

universe u

open CategoryTheory Limits MvPolynomial

namespace TauCeti.Supports

/-- Degree zero of the local cohomology of a domain at a nonzero ideal vanishes. -/
theorem isZero_localCohomology_zero_self_of_ne_bot {A : Type u} [CommRing A] [IsDomain A]
    {I : Ideal A} (hI : I ≠ ⊥) : IsZero ((localCohomology I 0).obj (ModuleCat.of A A)) := by
  refine isZero_localCohomology_zero_of_isSMulRegular I _ fun n => ?_
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (pow_ne_zero n hI)
  exact ⟨a, ha, fun x y h => mul_left_cancel₀ ha0 h⟩

/-- Degree zero of the local cohomology of a discrete valuation ring at its maximal ideal
vanishes. -/
theorem isZero_localCohomology_zero_maximalIdeal (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] :
    IsZero ((localCohomology (IsLocalRing.maximalIdeal R) 0).obj (ModuleCat.of R R)) :=
  isZero_localCohomology_zero_self_of_ne_bot (IsDiscreteValuationRing.not_a_field R)

namespace NilIdealExample

variable (k : Type u) [CommRing k]

/-- The ideal `(x_j^{j+2})` of `k[x₀, x₁, …]`. -/
noncomputable def relations : Ideal (MvPolynomial ℕ k) :=
  Ideal.span (Set.range fun j : ℕ => X j ^ (j + 2))

/-- The ring `k[x₀, x₁, …]/(x_j^{j+2})`. -/
abbrev CoordRing : Type u :=
  MvPolynomial ℕ k ⧸ relations k

/-- The ideal `(x₀, x₁, …)` of `k[x₀, x₁, …]/(x_j^{j+2})`. -/
noncomputable def ideal : Ideal (CoordRing k) :=
  Ideal.span (Set.range fun j : ℕ => Ideal.Quotient.mk (relations k) (X j))

variable {k}

/-- A polynomial lies in `(x_j^{j+2})` exactly when each of its monomials is divisible by some
`x_j^{j+2}`. -/
theorem mem_relations_iff {p : MvPolynomial ℕ k} :
    p ∈ relations k ↔ ∀ d ∈ p.support, ∃ j : ℕ, j + 2 ≤ d j := by
  have h : (Set.range fun j : ℕ => (X j : MvPolynomial ℕ k) ^ (j + 2)) =
      (fun s => monomial s (1 : k)) '' Set.range fun j : ℕ => Finsupp.single j (j + 2) := by
    rw [← Set.range_comp]
    simp [Function.comp_def, X_pow_eq_monomial]
  rw [relations, h, mem_ideal_span_monomial_image]
  simp only [Set.exists_range_iff, Finsupp.single_le_iff]

/-- Multiplying a polynomial outside `(x_j^{j+2})` by `x_N^n`, for a variable `x_N` with `n ≤ N`
that does not occur in it, stays outside `(x_j^{j+2})`. -/
theorem exists_X_pow_mul_notMem_relations {p : MvPolynomial ℕ k} (hp : p ∉ relations k)
    (n : ℕ) : ∃ N : ℕ, X N ^ n * p ∉ relations k := by
  classical
  obtain ⟨d, hd, hdj⟩ : ∃ d ∈ p.support, ∀ j : ℕ, d j < j + 2 := by
    simpa [mem_relations_iff] using hp
  obtain ⟨N, hN⟩ := Infinite.exists_notMem_finset (p.vars ∪ Finset.range n)
  rw [Finset.mem_union, Finset.mem_range, not_or, not_lt] at hN
  have hdN : d N = 0 := by
    by_contra h
    exact hN.1 ((mem_vars_iff_mem_support N).2 ⟨d, hd, Finsupp.mem_support_iff.2 h⟩)
  refine ⟨N, fun h => ?_⟩
  have hmem : Finsupp.single N n + d ∈ (X N ^ n * p).support := by
    rw [mem_support_iff, X_pow_eq_monomial, coeff_monomial_mul, one_mul]
    exact mem_support_iff.1 hd
  obtain ⟨j, hj⟩ := mem_relations_iff.1 h _ hmem
  rw [Finsupp.add_apply, Finsupp.single_apply] at hj
  split_ifs at hj with hjN
  · subst hjN
    omega
  · exact absurd hj (by simpa using hdj j)

/-- `1` does not lie in `(x_j^{j+2})`. -/
theorem one_notMem_relations [Nontrivial k] : (1 : MvPolynomial ℕ k) ∉ relations k := by
  intro h
  obtain ⟨j, hj⟩ := mem_relations_iff.1 h 0 (by simp)
  simp at hj

instance [Nontrivial k] : Nontrivial (CoordRing k) :=
  Ideal.Quotient.nontrivial_iff.2 fun h => one_notMem_relations ((Ideal.eq_top_iff_one _).1 h)

/-- Every nonzero element of `k[x₀, x₁, …]/(x_j^{j+2})` has a nonzero product with an element of
`I^n`. -/
theorem exists_mem_pow_mul_ne_zero {a : CoordRing k} (ha : a ≠ 0) (n : ℕ) :
    ∃ b ∈ ideal k ^ n, b * a ≠ 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨N, hN⟩ := exists_X_pow_mul_notMem_relations
    (fun h => ha (Ideal.Quotient.eq_zero_iff_mem.2 h)) n
  refine ⟨Ideal.Quotient.mk _ (X N) ^ n,
    Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self N)) n, ?_⟩
  rwa [← map_pow, ← map_mul, Ne, Ideal.Quotient.eq_zero_iff_mem]

/-- The ideal `(x₀, x₁, …)` consists of nilpotent elements. -/
theorem ideal_le_nilradical : ideal k ≤ nilradical (CoordRing k) := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨j, rfl⟩
  refine mem_nilradical.2 ⟨j + 2, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_range_self j)

/-- `V(x₀, x₁, …)` is all of `Spec A`. -/
theorem zeroLocus_ideal : PrimeSpectrum.zeroLocus (ideal k : Set (CoordRing k)) = Set.univ :=
  (PrimeSpectrum.zeroLocus_eq_univ_iff _).2 (ideal_le_nilradical (k := k))

/-- `k[x₀, x₁, …]/(x_j^{j+2})` is not Noetherian: its nilradical contains `(x₀, x₁, …)`, no power
of which vanishes. -/
theorem not_isNoetherianRing [Nontrivial k] : ¬IsNoetherianRing (CoordRing k) := by
  intro _
  obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical (CoordRing k)
  obtain ⟨b, hb, hb0⟩ := exists_mem_pow_mul_ne_zero (one_ne_zero (α := CoordRing k)) n
  have : b ∈ nilradical (CoordRing k) ^ n := Ideal.pow_right_mono ideal_le_nilradical n hb
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  exact hb0 (by rw [this, zero_mul])

/-- The native degree-zero local cohomology `H⁰_I(A)` of `A = k[x₀, x₁, …]/(x_j^{j+2})` at
`I = (x₀, x₁, …)` vanishes, although `V(I) = Spec A`. -/
theorem isZero_localCohomology_zero :
    IsZero ((localCohomology (ideal k) 0).obj (ModuleCat.of (CoordRing k) (CoordRing k))) := by
  refine (isZero_localCohomology_zero_iff _ _).2 fun a ⟨n, hn⟩ => ?_
  by_contra ha
  obtain ⟨b, hb, hba⟩ := exists_mem_pow_mul_ne_zero ha n
  exact hba (hn b hb)

end NilIdealExample

end TauCeti.Supports
