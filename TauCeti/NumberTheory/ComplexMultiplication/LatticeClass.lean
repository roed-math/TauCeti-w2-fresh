/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ComplexMultiplication.IdealLattice
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Ideal classes and lattices with complex multiplication

Let `K` be an imaginary quadratic field, oriented by a non-real embedding `σ : K →+* ℂ`, and let `O`
be an order of `K`. By `TauCeti.GlobalNumberFields.NumberFieldOrder.exists_periodPair_lattice_eq`,
every nonzero fractional ideal `I` of `O` gives a lattice `σ(I)`, whose multiplier ring is `σ(O)`
when `I` is proper. This file proves that this is a bijection between the ideal classes of proper
fractional ideals and the homothety classes of lattices with multiplier ring `σ(O)`:

* two nonzero fractional ideals have the same class exactly when their lattices are homothetic
  (`mk_eq_mk_iff_exists_lattice_eq_smul`): a homothety `c σ(I) = σ(J)` has `c = σ(x)` for some
  `x ∈ Kˣ`, and then `J = x I`;
* every lattice whose multiplier ring is `σ(O)` is homothetic to `σ(I)` for a proper fractional
  ideal `I` (`exists_isProper_lattice_smul_eq`): rescale it to `ℤ + ℤ τ`; a non-real multiplier
  `σ(x) = a + b τ` with `x ∈ O` shows `τ = σ(t)` with `t = (x - a) / b ∈ K`, and `ℤ + ℤ t` is
  stable under `O`, so it is the fractional ideal `O + O t`.

This is the oriented ideal-lattice dictionary at the level of homothety classes. By
`PeriodPair.weierstrassCurve_smul` homothetic lattices give isomorphic Weierstrass curves.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.exists_eq_spanSingleton_mul_of_lattice_eq_smul`:
  homothetic ideal lattices come from homothetic ideals.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.mk_eq_mk_iff_exists_lattice_eq_smul`: the ideal
  class is the homothety class of the lattice.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.exists_isProper_lattice_smul_eq`: every lattice
  with multiplier ring `σ(O)` is homothetic to the lattice of a proper ideal.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, 2nd ed., Wiley, 2013, §10.C.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Graduate Texts in
  Mathematics 151, Springer, 1994, §II.1.
-/

public section

open NumberField FractionalIdeal

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K} {σ : K →+* ℂ}

/-- Membership in a lattice `σ(I)`. -/
private lemma mem_lattice_iff_of_coe_eq {L : PeriodPair}
    {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} (hL : (L.lattice : Set ℂ) = σ '' I)
    (z : ℂ) : z ∈ L.lattice ↔ ∃ y ∈ I, σ y = z := by
  rw [← SetLike.mem_coe, hL]
  rfl

/-- **Homothetic ideal lattices come from homothetic ideals.** If the lattices `σ(I)` and `σ(J)`
of two fractional ideals satisfy `σ(J) = c σ(I)` with `I ≠ 0`, then `J = x I` for an `x ∈ Kˣ` with
`σ(x) = c`. -/
theorem exists_eq_spanSingleton_mul_of_lattice_eq_smul
    {I J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} (hI : I ≠ 0) {L L' : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' I) (hL' : (L'.lattice : Set ℂ) = σ '' J) (c : ℂˣ)
    (h : L'.lattice = (c • L).lattice) :
    ∃ x : Kˣ, σ x = c ∧ spanSingleton (nonZeroDivisors O.toSubalgebra) (x : K) * I = J := by
  have hJ : ∀ z, (∃ y ∈ J, σ y = z) ↔ ∃ w, (∃ y ∈ I, σ y = w) ∧ (c : ℂ) * w = z := fun z ↦ by
    rw [← mem_lattice_iff_of_coe_eq hL', h, PeriodPair.mem_lattice_smul_iff]
    simp only [mem_lattice_iff_of_coe_eq hL]
  obtain ⟨y₀, hy₀, hy₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (coeToSubmodule_ne_bot.mpr hI)
  obtain ⟨y₁, -, e⟩ := (hJ _).mpr ⟨_, ⟨y₀, hy₀, rfl⟩, rfl⟩
  have hσy₀ : σ y₀ ≠ 0 := (map_ne_zero σ).mpr hy₀ne
  have hx : σ (y₁ / y₀) = c := by rw [map_div₀, e, mul_div_cancel_right₀ _ hσy₀]
  have hx0 : y₁ / y₀ ≠ 0 := fun h0 ↦ c.ne_zero (by rw [← hx, h0, map_zero])
  refine ⟨Units.mk0 _ hx0, hx, FractionalIdeal.ext fun z ↦ ?_⟩
  rw [mem_singleton_mul, Units.val_mk0]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z', hz', e'⟩ := (hJ _).mpr ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rwa [σ.injective (e'.trans (by rw [map_mul, hx]) : σ z' = σ (y₁ / y₀ * y))] at hz'
  · intro hz
    obtain ⟨_, ⟨y, hy, rfl⟩, e'⟩ := (hJ _).mp ⟨z, hz, rfl⟩
    exact ⟨y, hy, σ.injective (by rw [← e', map_mul, hx])⟩

/-- **The ideal class is the homothety class of the lattice.** Two nonzero fractional ideals have
the same class exactly when their lattices are homothetic. -/
theorem mk_eq_mk_iff_exists_lattice_eq_smul {I J : O.nonzeroFractionalIdeals} {L L' : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K))
    (hL' : (L'.lattice : Set ℂ) = σ '' (J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)) :
    IdealClassMonoid.mk O I = IdealClassMonoid.mk O J ↔ ∃ c : ℂˣ, L'.lattice = (c • L).lattice := by
  rw [IdealClassMonoid.mk_eq_mk_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨Units.map σ.toMonoidHom x, SetLike.coe_injective ?_⟩
    rw [hL', lattice_smul_eq_image_spanSingleton_mul hL x, hx]
  · rintro ⟨c, hc⟩
    obtain ⟨x, -, hx⟩ :=
      exists_eq_spanSingleton_mul_of_lattice_eq_smul (nonZeroDivisors.ne_zero I.2) hL hL' c hc
    exact ⟨x, hx⟩

/-- An order of a quadratic field contains an irrational element. -/
private lemma exists_mem_notMem_span_one (hK : Module.finrank ℚ K = 2) (O : NumberFieldOrder K) :
    ∃ x ∈ O.toSubalgebra, x ∉ Submodule.span ℚ {(1 : K)} := by
  by_contra! h
  have hle : (⊤ : Submodule ℚ K) ≤ Submodule.span ℚ {1} := by
    rw [← O.spans]
    exact Submodule.span_le.mpr h
  have := Submodule.finrank_mono hle
  rw [finrank_top, hK, finrank_span_singleton one_ne_zero] at this
  omega

/-- Together with `1`, an irrational element spans a quadratic field over `ℚ`. -/
private lemma span_one_pair_eq_top (hK : Module.finrank ℚ K = 2) {x : K}
    (hx : x ∉ Submodule.span ℚ {(1 : K)}) : Submodule.span ℚ {1, x} = ⊤ := by
  have hlt : Submodule.span ℚ {(1 : K)} < Submodule.span ℚ {1, x} :=
    lt_of_le_of_ne (Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))) fun h ↦
      hx (h ▸ Submodule.subset_span (by simp))
  have h₁ := Submodule.finrank_lt_finrank_of_lt hlt
  have h₂ := Submodule.finrank_le (Submodule.span ℚ {1, x})
  rw [finrank_span_singleton one_ne_zero] at h₁
  exact Submodule.eq_top_of_finrank_eq (by omega)

/-- **Every lattice with complex multiplication by `O` comes from a proper ideal.** If the
multiplier ring of `L` is `σ(O)`, then a rescaling of the lattice of `L` is `σ(I)` for a proper
fractional ideal `I` of `O`. -/
theorem exists_isProper_lattice_smul_eq (hK : Module.finrank ℚ K = 2)
    (hσ : ¬ ComplexEmbedding.IsReal σ) {L : PeriodPair}
    (hL : L.multiplierRing = O.toSubalgebra.toSubring.map σ) :
    ∃ I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K, O.IsProperFractionalIdeal I ∧
      ∃ c : ℂˣ, ((c • L).lattice : Set ℂ) = σ '' I := by
  -- An irrational element `x` of `O` has a non-real image.
  obtain ⟨x, hxO, hx⟩ := exists_mem_notMem_span_one hK O
  have hind := LinearIndependent.pair_iff.mp
    (linearIndependent_real_of_span_rat_eq_top hσ (span_one_pair_eq_top hK hx))
  have him : (σ x).im ≠ 0 := fun him ↦ by
    have hre : ((σ x).re : ℂ) = σ x := Complex.ext (by simp) (by simp [him])
    have := (hind (σ x).re (-1) (by
      rw [map_one, Complex.real_smul, Complex.real_smul, mul_one, hre]
      push_cast
      ring)).2
    norm_num at this
  -- Rescale `L` to the lattice `ℤ + ℤ τ`.
  set c := Units.mk0 L.ω₁⁻¹ (inv_ne_zero L.ω₁_ne_zero)
  set L' := c • L
  have hω₁ : L'.ω₁ = 1 := by simp [L', c, L.ω₁_ne_zero]
  have hL'R : L'.multiplierRing = O.toSubalgebra.toSubring.map σ := by
    rw [PeriodPair.multiplierRing_smul, hL]
  have hmulR : ∀ o ∈ O.toSubalgebra, ∀ z ∈ L'.lattice, σ o * z ∈ L'.lattice := fun o ho ↦ by
    rw [← PeriodPair.mem_multiplierRing, hL'R]
    exact ⟨o, ho, rfl⟩
  -- `σ x = a + b τ`, with `b ≠ 0` because `σ x` is not real.
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp (hmulR x hxO _ L'.ω₁_mem_lattice)
  simp only [hω₁, mul_one] at hab
  have hb : (b : ℂ) ≠ 0 := fun hb ↦ him (by rw [← hab, hb]; simp)
  set t : K := (x - a) / b
  have ht : σ t = L'.ω₂ := by
    simp only [t, map_div₀, map_sub, map_intCast]
    rw [← hab]
    field_simp
    ring
  -- The fractional ideal `O + O t`.
  set I := spanSingleton (nonZeroDivisors O.toSubalgebra) (1 : K) ⊔ spanSingleton _ t
  have hmemI : ∀ z, z ∈ I ↔ ∃ o₁ ∈ O.toSubalgebra, ∃ o₂ ∈ O.toSubalgebra, o₁ + o₂ * t = z := by
    intro z
    rw [← mem_coe, coe_sup, Submodule.mem_sup]
    simp only [mem_coe, mem_spanSingleton, Algebra.smul_def, mul_one, Subtype.exists]
    constructor
    · rintro ⟨_, ⟨o₁, ho₁, rfl⟩, _, ⟨o₂, ho₂, rfl⟩, rfl⟩
      exact ⟨o₁, ho₁, o₂, ho₂, rfl⟩
    · rintro ⟨o₁, ho₁, o₂, ho₂, rfl⟩
      exact ⟨_, ⟨o₁, ho₁, rfl⟩, _, ⟨o₂, ho₂, rfl⟩, rfl⟩
  have hlat : (L'.lattice : Set ℂ) = σ '' I := by
    ext w
    simp only [SetLike.mem_coe, Set.mem_image, hmemI]
    constructor
    · intro hw
      obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hw
      refine ⟨m + n * t, ⟨m, intCast_mem _ m, n, intCast_mem _ n, rfl⟩, ?_⟩
      rw [map_add, map_mul, map_intCast, map_intCast, ht, hω₁, mul_one]
    · rintro ⟨_, ⟨o₁, ho₁, o₂, ho₂, rfl⟩, rfl⟩
      rw [map_add, map_mul, ht]
      refine add_mem ?_ (hmulR o₂ ho₂ _ L'.ω₂_mem_lattice)
      simpa [hω₁] using hmulR o₁ ho₁ _ L'.ω₁_mem_lattice
  have hI : I ≠ 0 := fun h0 ↦ one_ne_zero ((mem_zero_iff _).mp
    (h0 ▸ (hmemI 1).mpr ⟨1, one_mem _, 0, zero_mem _, by simp⟩))
  refine ⟨I, ?_, c, hlat⟩
  rw [isProperFractionalIdeal_def]
  have hmap := (multiplierRing_eq_map hI hlat).symm.trans hL'R
  rw [← Subring.comap_map_eq_self_of_injective σ.injective (O.multiplierRing I), hmap,
    Subring.comap_map_eq_self_of_injective σ.injective]

end NumberFieldOrder

end TauCeti.GlobalNumberFields
