/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.Endomorphism
public import TauCeti.Lookahead.CmLatticeDictionary.Stubs
public import TauCeti.NumberTheory.NumberField.Global.Orders.IdealClassMonoid
public import TauCeti.NumberTheory.NumberField.Global.Orders.Lattice
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

/-!
# Fractional ideals of imaginary quadratic orders as period lattices

Let `K` be a quadratic number field with a complex embedding `σ : K →+* ℂ` that is not real, so `K`
is imaginary quadratic and `σ` is one of its two complex embeddings (the choice of `σ` is the
orientation). Let `O` be an order of `K` and `I` a nonzero fractional ideal of `O`. A `ℤ`-basis
`v₀, v₁` of `I` is a `ℚ`-basis of `K`, and `σ v₀, σ v₁` are linearly independent over `ℝ`: otherwise
every `σ x = p σ v₀ + q σ v₁` would lie on one real line through `0` together with `σ 1 = 1`,
making `σ` real. So `σ(I)` is the lattice of a period pair (`exists_periodPair_lattice_eq`), and
`I` has a complex elliptic curve `E_I = ℂ / σ(I)`.

This file proves the endomorphism-order comparison for these lattices:

* the multiplier ring `{α ∈ ℂ | α σ(I) ⊆ σ(I)}` of the lattice is the image under `σ` of the
  multiplier ring `{x ∈ K | x I ⊆ I}` of the ideal (`multiplierRing_eq_map`);
* for a proper ideal, it is the image of `O`, so `O` is the ring of analytic endomorphisms of
  `E_I(ℂ)`, acting faithfully (`multiplierRingEquiv`, `orderEndRingHom_injective`).

Homothetic ideals give homothetic lattices, hence isomorphic curves. So the `j`-invariant of
`E_I` depends only on the ideal class of `I` in the ideal class monoid of `O`
(`IdealClassMonoid.jInvariant`), and it is a value of the modular `j`-function
(`IdealClassMonoid.exists_jInvariant_eq_j`).

## Main definitions

* `TauCeti.GlobalNumberFields.NumberFieldOrder.multiplierRingEquiv`: for a proper ideal `I`, the
  order is isomorphic to the multiplier ring of the lattice `σ(I)`, by `σ`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.orderEndRingHom`: the resulting action of `O` on
  the points `E_I(ℂ)`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.jInvariant`: the `j`-invariant of the curve of a
  nonzero fractional ideal.
* `TauCeti.GlobalNumberFields.IdealClassMonoid.jInvariant`: its descent to ideal classes.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.linearIndependent_real_of_span_rat_eq_top`: a
  `ℚ`-basis of `K` maps to an `ℝ`-basis of `ℂ` under a non-real embedding.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.exists_periodPair_lattice_eq`: `σ(I)` is the
  lattice of a period pair.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.multiplierRing_eq_map`: the multiplier ring of
  `σ(I)` is `σ` of the multiplier ring of `I`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.multiplierRing_eq_map_of_isProper`: for a proper
  ideal it is `σ(O)`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.orderEndRingHom_injective`: `O` acts faithfully.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.jInvariant_eq_of_homothetyCon`: homothetic ideals
  have the same `j`-invariant.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Graduate Texts in
  Mathematics 151, Springer, 1994, §II.1.
* D. A. Cox, *Primes of the Form x² + ny²*, 2nd ed., Wiley, 2013, §10.
-/

public noncomputable section

open NumberField ComplexConjugate FractionalIdeal

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K]

/-- **A `ℚ`-basis of `K` gives an `ℝ`-basis of `ℂ`.** If `σ` is not real and `v₀, v₁` span `K`
over `ℚ`, then `σ v₀` and `σ v₁` are linearly independent over `ℝ`. -/
theorem linearIndependent_real_of_span_rat_eq_top {σ : K →+* ℂ}
    (hσ : ¬ ComplexEmbedding.IsReal σ) {v₀ v₁ : K} (hv : Submodule.span ℚ {v₀, v₁} = ⊤) :
    LinearIndependent ℝ ![σ v₀, σ v₁] := by
  have hcoord : ∀ x : K, ∃ p q : ℚ, (p : ℂ) * σ v₀ + q * σ v₁ = σ x := by
    intro x
    obtain ⟨p, q, h⟩ := Submodule.mem_span_pair.mp (hv ▸ Submodule.mem_top : x ∈ _)
    refine ⟨p, q, ?_⟩
    rw [← h, Rat.smul_def, Rat.smul_def, map_add, map_mul, map_mul, map_ratCast, map_ratCast]
  refine LinearIndependent.pair_iff.mpr fun s t hst ↦ by_contra fun hne ↦ hσ ?_
  have hre : s * (σ v₀).re + t * (σ v₁).re = 0 := by simpa using congrArg Complex.re hst
  have him : s * (σ v₀).im + t * (σ v₁).im = 0 := by simpa using congrArg Complex.im hst
  -- The real determinant of `σ v₀, σ v₁` vanishes.
  have hD : (σ v₀).re * (σ v₁).im - (σ v₁).re * (σ v₀).im = 0 := by
    rcases not_and_or.mp hne with hs | ht
    · refine (mul_eq_zero.mp ?_).resolve_left hs
      linear_combination (σ v₁).im * hre - (σ v₁).re * him
    · refine (mul_eq_zero.mp ?_).resolve_left ht
      linear_combination -(σ v₀).im * hre + (σ v₀).re * him
  -- Hence every `σ x` lies on the real line through `σ 1 = 1`.
  obtain ⟨p₁, q₁, h₁⟩ := hcoord 1
  rw [map_one] at h₁
  have h₁re := congrArg Complex.re h₁
  have h₁im := congrArg Complex.im h₁
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re,
    Complex.ratCast_im, zero_mul, sub_zero, add_zero, Complex.one_re, Complex.one_im] at h₁re h₁im
  refine ComplexEmbedding.isReal_iff.mpr (RingHom.ext fun x ↦ ?_)
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_eq_iff_im]
  obtain ⟨p, q, hx⟩ := hcoord x
  rw [← hx]
  simp only [Complex.add_im, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im, zero_mul,
    add_zero]
  linear_combination -((p : ℝ) * (σ v₀).im + q * (σ v₁).im) * h₁re +
    ((p : ℝ) * (σ v₀).re + q * (σ v₁).re) * h₁im + ((q : ℝ) * p₁ - p * q₁) * hD

variable {O : NumberFieldOrder K} {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K}

/-- **The lattice of a fractional ideal.** If `K` is quadratic and `σ` is not real, the image of a
nonzero fractional ideal `I` of an order is the lattice of a period pair. -/
theorem exists_periodPair_lattice_eq (hK : Module.finrank ℚ K = 2) {σ : K →+* ℂ}
    (hσ : ¬ ComplexEmbedding.IsReal σ) (hI : I ≠ 0) :
    ∃ L : PeriodPair, (L.lattice : Set ℂ) = σ '' I := by
  obtain ⟨b, hb⟩ := O.exists_basis_restrictScalars_eq_span hI
  set b' := b.reindex (finCongr hK)
  have hrange : Set.range b = {b' 0, b' 1} := by
    rw [← b.range_reindex (finCongr hK)]
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two]
    exact ⟨fun h ↦ h.imp Eq.symm Eq.symm, fun h ↦ h.imp Eq.symm Eq.symm⟩
  have hspan : Submodule.span ℚ {b' 0, b' 1} = ⊤ := by
    rw [← hrange]
    exact b.span_eq
  refine ⟨⟨σ (b' 0), σ (b' 1), linearIndependent_real_of_span_rat_eq_top hσ hspan⟩, ?_⟩
  have hI' : (I : Set K) = Submodule.span ℤ {b' 0, b' 1} := by
    rw [← hrange, ← hb, Submodule.coe_restrictScalars, coeToSet_coeToSubmodule]
  rw [hI', PeriodPair.lattice]
  change _ = σ.toAddMonoidHom.toIntLinearMap '' _
  rw [← Submodule.map_coe, Submodule.map_span, Set.image_pair]
  rfl

/-- **The endomorphism-order comparison.** If the lattice of `L` is `σ(I)`, its multiplier ring is
the image under `σ` of the multiplier ring of `I`. -/
theorem multiplierRing_eq_map {σ : K →+* ℂ} (hI : I ≠ 0) {L : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' I) :
    L.multiplierRing = (O.multiplierRing I).map σ := by
  have hmem : ∀ z, z ∈ L.lattice ↔ ∃ y ∈ I, σ y = z := fun z ↦ by
    rw [← SetLike.mem_coe, hL]
    rfl
  obtain ⟨y₀, hy₀, hy₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (coeToSubmodule_ne_bot.mpr hI)
  have hσy₀ : σ y₀ ≠ 0 := (map_ne_zero σ).mpr hy₀ne
  ext α
  rw [PeriodPair.mem_multiplierRing, Subring.mem_map]
  constructor
  · intro h
    obtain ⟨y₁, -, e⟩ := (hmem _).mp (h _ ((hmem _).mpr ⟨y₀, hy₀, rfl⟩))
    have hα : σ (y₁ / y₀) = α := by rw [map_div₀, e, mul_div_cancel_right₀ _ hσy₀]
    refine ⟨y₁ / y₀, (O.mem_multiplierRing_iff I _).mpr fun y hy ↦ ?_, hα⟩
    obtain ⟨y', hy', e'⟩ := (hmem _).mp (h _ ((hmem _).mpr ⟨y, hy, rfl⟩))
    rwa [σ.injective (e'.trans (by rw [map_mul, hα]) : σ y' = σ (y₁ / y₀ * y))] at hy'
  · rintro ⟨x, hx, rfl⟩ z hz
    obtain ⟨y, hy, rfl⟩ := (hmem _).mp hz
    exact (hmem _).mpr ⟨x * y, (O.mem_multiplierRing_iff I x).mp hx y hy, map_mul σ x y⟩

/-- For a proper fractional ideal `I`, the multiplier ring of the lattice `σ(I)` is `σ(O)`. -/
theorem multiplierRing_eq_map_of_isProper {σ : K →+* ℂ} (hI : O.IsProperFractionalIdeal I)
    {L : PeriodPair} (hL : (L.lattice : Set ℂ) = σ '' I) :
    L.multiplierRing = O.toSubalgebra.toSubring.map σ := by
  rw [multiplierRing_eq_map hI.ne_zero hL, (O.isProperFractionalIdeal_def I).mp hI]

/-- For a proper fractional ideal `I`, the order is isomorphic by `σ` to the multiplier ring of the
lattice `σ(I)`. -/
def multiplierRingEquiv {σ : K →+* ℂ} (hI : O.IsProperFractionalIdeal I) {L : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' I) : O.toSubalgebra.toSubring ≃+* L.multiplierRing :=
  (O.toSubalgebra.toSubring.equivMapOfInjective σ σ.injective).trans
    (RingEquiv.subringCongr (multiplierRing_eq_map_of_isProper hI hL).symm)

/-- `multiplierRingEquiv` is `σ`. -/
@[simp]
lemma coe_multiplierRingEquiv {σ : K →+* ℂ} (hI : O.IsProperFractionalIdeal I) {L : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' I) (x : O.toSubalgebra.toSubring) :
    (multiplierRingEquiv hI hL x : ℂ) = σ x :=
  (rfl)

/-- The action of the order on the points `E_I(ℂ)` of the curve of a proper ideal `I`: `x ∈ O`
acts by the scalar map of `σ x`. -/
def orderEndRingHom {σ : K →+* ℂ} (hI : O.IsProperFractionalIdeal I) {L : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' I) :
    O.toSubalgebra.toSubring →+* AddMonoid.End L.weierstrassCurve.toAffine.Point :=
  L.endRingHom.comp (multiplierRingEquiv hI hL).toRingHom

/-- An element `x` of the order acts on the curve of `I` by `P(z) ↦ P(σ(x) z)`. -/
@[simp]
lemma orderEndRingHom_weierstrassPoint {σ : K →+* ℂ} (hI : O.IsProperFractionalIdeal I)
    {L : PeriodPair} (hL : (L.lattice : Set ℂ) = σ '' I) (x : O.toSubalgebra.toSubring)
    (z : ℂ) :
    orderEndRingHom hI hL x (L.weierstrassPoint z) = L.weierstrassPoint (σ x * z) := by
  simp [orderEndRingHom]

/-- **The order acts faithfully** on the points of the curve of a proper ideal, and by
`multiplierRingEquiv` every analytic endomorphism `PeriodPair.endRingHom` comes from it. -/
theorem orderEndRingHom_injective {σ : K →+* ℂ} (hI : O.IsProperFractionalIdeal I)
    {L : PeriodPair} (hL : (L.lattice : Set ℂ) = σ '' I) :
    Function.Injective (orderEndRingHom hI hL) :=
  L.endRingHom_injective.comp (multiplierRingEquiv hI hL).injective

/-! ### The `j`-invariant of an ideal class -/

/-- If the lattice of `L` is `σ(I)` and `J = x I`, then the lattice of `σ(x) • L` is `σ(J)`. -/
lemma lattice_smul_eq_image_spanSingleton_mul {σ : K →+* ℂ} {L : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' I) (x : Kˣ) :
    (((Units.map σ.toMonoidHom x) • L).lattice : Set ℂ) =
      σ '' (spanSingleton (nonZeroDivisors O.toSubalgebra) (x : K) * I : FractionalIdeal _ K) := by
  have hmem : ∀ z, z ∈ L.lattice ↔ ∃ y ∈ I, σ y = z := fun z ↦ by
    rw [← SetLike.mem_coe, hL]
    rfl
  ext z
  simp only [SetLike.mem_coe, PeriodPair.lattice_smul, Submodule.mem_map, LinearMap.mulLeft_apply,
    Set.mem_image, mem_singleton_mul, hmem]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x * y, ⟨y, hy, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨σ y, ⟨y, hy, rfl⟩, by simp⟩

variable (O) in
/-- The `j`-invariant of the curve `ℂ / σ(I)` of a nonzero fractional ideal `I`. -/
def jInvariant (hK : Module.finrank ℚ K = 2) {σ : K →+* ℂ} (hσ : ¬ ComplexEmbedding.IsReal σ)
    (I : O.nonzeroFractionalIdeals) : ℂ :=
  (exists_periodPair_lattice_eq hK hσ (nonZeroDivisors.ne_zero I.2)).choose.weierstrassCurve.j

/-- The `j`-invariant of `I` is that of any period pair with lattice `σ(I)`. -/
lemma jInvariant_eq (hK : Module.finrank ℚ K = 2) {σ : K →+* ℂ}
    (hσ : ¬ ComplexEmbedding.IsReal σ) (I : O.nonzeroFractionalIdeals) {L : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)) :
    O.jInvariant hK hσ I = L.weierstrassCurve.j := by
  refine PeriodPair.weierstrassCurve_j_eq_of_lattice_eq_smul (c := 1) ?_
  rw [one_smul]
  exact SetLike.coe_injective
    ((exists_periodPair_lattice_eq hK hσ (nonZeroDivisors.ne_zero I.2)).choose_spec.trans hL.symm)

/-- Homothetic fractional ideals have the same `j`-invariant. -/
theorem jInvariant_eq_of_homothetyCon (hK : Module.finrank ℚ K = 2) {σ : K →+* ℂ}
    (hσ : ¬ ComplexEmbedding.IsReal σ) {I J : O.nonzeroFractionalIdeals}
    (h : O.homothetyCon I J) : O.jInvariant hK hσ I = O.jInvariant hK hσ J := by
  obtain ⟨x, hx⟩ := (O.homothetyCon_iff).mp h
  obtain ⟨L, hL⟩ := exists_periodPair_lattice_eq hK hσ (nonZeroDivisors.ne_zero I.2)
  have hL' := lattice_smul_eq_image_spanSingleton_mul hL x
  rw [hx] at hL'
  rw [jInvariant_eq hK hσ I hL, jInvariant_eq hK hσ J hL',
    PeriodPair.weierstrassCurve_j_eq_of_lattice_eq_smul rfl]

end NumberFieldOrder

namespace IdealClassMonoid

variable {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K}

/-- The `j`-invariant of an ideal class of an order of an imaginary quadratic field, for the
orientation given by a non-real embedding `σ`: the `j`-invariant of the curve `ℂ / σ(I)` of any
representative `I` (`IdealClassMonoid.jInvariant_mk`). -/
def jInvariant (hK : Module.finrank ℚ K = 2) {σ : K →+* ℂ} (hσ : ¬ ComplexEmbedding.IsReal σ)
    (c : IdealClassMonoid O) : ℂ :=
  O.jInvariant hK hσ (Function.surjInv (mk_surjective O) c)

/-- The `j`-invariant of the class of `I` is the `j`-invariant of `I`. -/
@[simp]
theorem jInvariant_mk (hK : Module.finrank ℚ K = 2) {σ : K →+* ℂ}
    (hσ : ¬ ComplexEmbedding.IsReal σ) (I : O.nonzeroFractionalIdeals) :
    (mk O I).jInvariant hK hσ = O.jInvariant hK hσ I :=
  NumberFieldOrder.jInvariant_eq_of_homothetyCon hK hσ
    ((O.homothetyCon_iff).mpr ((mk_eq_mk_iff O).mp (Function.surjInv_eq (mk_surjective O) _)))

/-- The `j`-invariant of an ideal class is a value of the modular `j`-function: it is `j(τ)` for a
point `τ` of the upper half-plane with `σ(I)` homothetic to `ℤ τ + ℤ`. -/
theorem exists_jInvariant_eq_j (hK : Module.finrank ℚ K = 2) {σ : K →+* ℂ}
    (hσ : ¬ ComplexEmbedding.IsReal σ) (c : IdealClassMonoid O) :
    ∃ τ : UpperHalfPlane, c.jInvariant hK hσ = TauCeti.ModularForm.j τ := by
  obtain ⟨I, rfl⟩ := mk_surjective O c
  obtain ⟨L, hL⟩ := NumberFieldOrder.exists_periodPair_lattice_eq hK hσ
    (nonZeroDivisors.ne_zero I.2)
  obtain ⟨u, τ, hτ⟩ := L.exists_lattice_eq_smul_periodPair
  refine ⟨τ, ?_⟩
  rw [jInvariant_mk, NumberFieldOrder.jInvariant_eq hK hσ I hL,
    PeriodPair.weierstrassCurve_j_eq_of_lattice_eq_smul hτ,
    UpperHalfPlane.weierstrassCurve_j_periodPair]

end IdealClassMonoid

end TauCeti.GlobalNumberFields
