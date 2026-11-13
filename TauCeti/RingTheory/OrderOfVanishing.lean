/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.RingTheory.Localization.Ideal
import TauCeti.Algebra.Module.Equiv.Length
import TauCeti.RingTheory.Ideal.Quotient.Semilocal
import TauCeti.RingTheory.Length

/-!
# Invariance, vanishing and localization of the order of vanishing

For a Noetherian domain `R` of Krull dimension at most one with fraction field `K`, Mathlib's
`Ring.ordFrac R : K →*₀ ℤᵐ⁰` extends the order of vanishing `Ring.ord R x = length (R ⧸ (x))` to the
fraction field. This file records that the order of vanishing is transported by ring isomorphisms,
that it turns finite products of non-zero-divisors into sums, and that the order of a nonzero
element of `R` is trivial exactly when that element is a unit: `R ⧸ (x)` is the zero ring exactly
when `(x)` is the unit ideal. Mathlib has the forward direction, `Ring.ordFrac_of_isUnit`; the
converse is what reads "`f` has order zero at a codimension-one point" as "`f` is a unit at that
point".

It also expresses the length of `B ⧸ bB`, for `B` integral over a local ring `A`, as a sum of
local orders of `b` at the maximal ideals of `B` weighted by residue degrees (Fulton, *Intersection
Theory*, Appendix A.3). Here `(B ⧸ bB)_q` is identified with `B_m ⧸ b B_m` through Mathlib's
localization of a quotient, and the orders are moved to any localization of `B` at `m`.

## Main results

* `TauCeti.Ring.ord_ringEquiv`, `TauCeti.Ring.ordMonoidWithZeroHom_ringEquiv` and
  `TauCeti.Ring.ordFrac_map_of_ringEquiv`: the order of vanishing is invariant under ring
  isomorphisms, also as a homomorphism to `ℤᵐ⁰` and on fraction fields;
* `TauCeti.Ring.ord_eq_zero_iff`: `Ring.ord R x = 0` exactly when `x` is a unit;
* `TauCeti.Ring.ord_prod`: the order of a finite product of non-zero-divisors is the sum of the
  orders;
* `TauCeti.Ring.isUnit_iff_ordFrac_one`: `x` is a unit exactly when `Ring.ordFrac R x = 1`; this
  extends Mathlib's `Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing` to Noetherian domains
  of dimension at most one;
* `TauCeti.length_localization_quotient_span_singleton`: the localization `(R ⧸ bR)_q` has length
  `ord_{R_m} b` over itself, where `m` is the prime of `R` under `q`;
* `TauCeti.support_ord_subset`: the local order of `b` vanishes at the maximal ideals not
  containing `b`;
* `TauCeti.length_quotient_span_singleton_eq_finsum_ord`: for `B` integral over a local ring `A`
  with `B ⧸ bB` Artinian, `length_A (B ⧸ bB) = Σ_m ord_{B_m}(b) [κ(B_m) : κ(A)]` over the maximal
  ideals `m` of `B` (Fulton, *Intersection Theory*, Appendix A.3);
* `TauCeti.ordFrac_algebraMap_eq_ofAdd_ord`: the order of `b : B` in any localization `R` of `B`
  at a prime `p` with fraction field `L` is its order in `B_p`.
-/

public section

namespace TauCeti

namespace Ring

open scoped nonZeroDivisors

section RingEquiv

section Ring

variable {R R' : Type*} [Ring R] [Ring R']

/-- The order of vanishing is invariant under ring isomorphisms: `σ : R ≃+* R'` induces a
`σ`-semilinear isomorphism `R ⧸ (x) ≃ R' ⧸ (σ x)`, so both quotients have the same length. -/
@[simp]
theorem ord_ringEquiv (σ : R ≃+* R') (x : R) : Ring.ord R' (σ x) = Ring.ord R x := by
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.symm (σ : R →+* R') σ.symm
  exact ((Submodule.Quotient.equiv (Ideal.span {x}) (Ideal.span {σ x}) σ.toSemilinearEquiv
    (by simp [← Ideal.submodule_span_eq, Submodule.map_span])).toLinearMap.length_eq_of_bijective
    (LinearEquiv.bijective _)).symm

end Ring

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- The order of vanishing, as a homomorphism to `ℤᵐ⁰`, is invariant under ring isomorphisms. -/
@[simp]
theorem ordMonoidWithZeroHom_ringEquiv [Nontrivial R] [Nontrivial R'] (σ : R ≃+* R') (x : R) :
    Ring.ordMonoidWithZeroHom R' (σ x) = Ring.ordMonoidWithZeroHom R x := by
  have hmem : σ x ∈ R'⁰ ↔ x ∈ R⁰ := by
    rw [← MulEquivClass.map_nonZeroDivisors σ, Submonoid.mem_map_iff_mem σ.injective]
  by_cases hx : x ∈ R⁰ <;> simp [Ring.ordMonoidWithZeroHom_eq_ord, hx, hmem]

variable [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [IsDomain R'] [IsNoetherianRing R'] [Ring.KrullDimLE 1 R']
  {K K' : Type*} [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K']
  [IsFractionRing R' K']

/-- The order of vanishing on fraction fields is invariant under ring isomorphisms: if
`σ : R ≃+* R'` and `τ : K →+* K'` are compatible with the inclusions into the fraction fields, then
`ordFrac R' (τ k) = ordFrac R k`. -/
theorem ordFrac_map_of_ringEquiv (σ : R ≃+* R') (τ : K →+* K')
    (h : ∀ a, τ (algebraMap R K a) = algebraMap R' K' (σ a)) (k : K) :
    Ring.ordFrac R' (τ k) = Ring.ordFrac R k := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) k
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  simp [h, Ring.ordFrac_eq_ord, ha, nonZeroDivisors.ne_zero hb]

end RingEquiv

variable {R : Type*} [CommRing R]

/-- The order of vanishing of a ring element is zero exactly when the element is a unit: the
quotient `R ⧸ (x)` is trivial exactly when `(x)` is the unit ideal. -/
theorem ord_eq_zero_iff (x : R) : Ring.ord R x = 0 ↔ IsUnit x := by
  rw [Ring.ord, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff,
    Ideal.span_singleton_eq_top]

/-- The order of vanishing of a finite product of non-zero-divisors is the sum of their orders. -/
theorem ord_prod {ι : Type*} {s : Finset ι} {d : ι → R} (hd : ∀ i ∈ s, d i ∈ R⁰) :
    Ring.ord R (∏ i ∈ s, d i) = ∑ i ∈ s, Ring.ord R (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Ring.ord_mul' R (hd a (Finset.mem_insert_self a s)),
      ih fun i hi ↦ hd i (Finset.mem_insert_of_mem hi)]

variable [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- In a Noetherian domain of dimension at most one, an element is a unit exactly when its order
of vanishing in the fraction field is trivial. This extends Mathlib's
`Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing` from discrete valuation rings to
Noetherian domains of dimension at most one, such as the local rings at the codimension-one points
of a locally Noetherian integral scheme. -/
theorem isUnit_iff_ordFrac_one {x : R} : IsUnit x ↔ Ring.ordFrac R (algebraMap R K x) = 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hnz : x ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hx
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hnz)
  rw [Ring.ordFrac_eq_ord R hx, Ring.ordMonoidWithZeroHom_eq_coe R hnz hn.symm, ← ord_eq_zero_iff,
    ← hn]
  simp [← WithZero.coe_one]

end Ring

/-- The localization `(R ⧸ bR)_q` has length `ord_{R_m} b` over itself, where `m` is the prime
of `R` under `q`. -/
theorem length_localization_quotient_span_singleton {R : Type*} [CommRing R] (b : R)
    (q : Ideal (R ⧸ Ideal.span {b})) [q.IsPrime] :
    Module.length (Localization.AtPrime q) (Localization.AtPrime q) =
      Ring.ord (Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {b}))))
        (algebraMap R _ b) := by
  set Rm := Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {b})))
  -- `(R ⧸ bR)_q` is the quotient of `R_m` by the extension of `bR`.
  have : IsLocalization q.primeCompl (Rm ⧸ (Ideal.span {b}).map (algebraMap R Rm)) := by
    rw [← q.map_primeCompl_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    exact (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {b})
      (q.comap (Ideal.Quotient.mk (Ideal.span {b}))).primeCompl)
      (Rm ⧸ (Ideal.span {b}).map (algebraMap R Rm)))
  rw [(IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
      (Rm ⧸ (Ideal.span {b}).map (algebraMap R Rm))).toRingEquiv.length_self_eq,
    ← Module.length_eq_of_surjective (S := Rm) Ideal.Quotient.mk_surjective, Ideal.map_span,
    Set.image_singleton, Ring.ord]

/-- The local order of `b` vanishes outside the maximal ideals containing `b`. -/
theorem support_ord_subset {B : Type*} [CommRing B] (b : B) :
    Function.support (fun m : MaximalSpectrum B ↦
      Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b)) ⊆
      {m | b ∈ m.asIdeal} := by
  intro m hm
  by_contra hbm
  exact hm (Ring.ord_of_isUnit ((IsLocalization.AtPrime.isUnit_to_map_iff _ _ b).2 hbm))

/-- **The length of `B ⧸ bB` as a sum of local orders** (Fulton, *Intersection Theory*,
Appendix A.3). Let `B` be integral over a local ring `A`, and let `b : B` with `B ⧸ bB` Artinian
(for instance `b ≠ 0`, when `B` is a domain finite over a Noetherian domain `A` of dimension at
most one). Then `length_A (B ⧸ bB) = Σ_m ord_{B_m}(b) [κ(B_m) : κ(A)]`, the sum over the maximal
ideals `m` of `B` (only those containing `b` contribute), with the residue degree
`[κ(B_m) : κ(A)]` read as the `A`-length of `κ(B_m)`. -/
theorem length_quotient_span_singleton_eq_finsum_ord {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (b : B)
    [IsArtinianRing (B ⧸ Ideal.span {b})] :
    Module.length A (B ⧸ Ideal.span {b}) =
      ∑ᶠ m : MaximalSpectrum B, Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b) *
        Module.length A (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal)) := by
  set G : MaximalSpectrum B → ℕ∞ := fun m ↦
    Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b) *
      Module.length A (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal))
  -- The maximal ideals of `B ⧸ bB` are those of `B` containing `b`.
  let c : MaximalSpectrum (B ⧸ Ideal.span {b}) → MaximalSpectrum B := fun q ↦
    ⟨q.asIdeal.comap (Ideal.Quotient.mk _),
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
  have hc : Function.Injective c := fun q q' h ↦ MaximalSpectrum.ext
    (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      (congrArg MaximalSpectrum.asIdeal h))
  have hsupp : Function.support G ⊆ Set.range c := by
    intro m hm
    have hbm : b ∈ m.asIdeal := support_ord_subset b (Function.support_mul_subset_left _ _ hm)
    obtain ⟨q, hq⟩ := exists_maximalSpectrum_comap_mk_eq ((Ideal.span_singleton_le_iff_mem _).2 hbm)
    exact ⟨q, MaximalSpectrum.ext hq⟩
  have hG : ∑ᶠ m, G m = ∑ᶠ q, G (c q) := by
    rw [← finsum_mem_range hc, finsum_mem_def, Set.indicator_eq_self.2 hsupp]
  rw [length_eq_finsum_localization_mul_residueField, hG]
  refine finsum_congr fun q ↦ ?_
  rw [length_localization_quotient_span_singleton, Ideal.length_residueField_localization_quotient]

/-- For nonzero `b : B`, its order in a localization `R` of `B` at a prime `p`, computed on the
fraction field `L`, is its order in `B_p`. Here `R` is a Noetherian domain of Krull dimension at
most one. -/
theorem ordFrac_algebraMap_eq_ofAdd_ord {B L : Type*} [CommRing B] [Field L] [Algebra B L]
    [FaithfulSMul B L] (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Algebra B R] (p : Ideal B) [p.IsPrime] [IsLocalization.AtPrime R p]
    [Algebra R L] [IsScalarTower B R L] [IsFractionRing R L] {b : B} (hb : b ≠ 0) :
    Ring.ordFrac R (algebraMap B L b) = Multiplicative.ofAdd
      ((Ring.ord (Localization.AtPrime p) (algebraMap B _ b)).toNat : ℤ) := by
  let e : Localization.AtPrime p ≃ₐ[B] R := IsLocalization.algEquiv p.primeCompl _ _
  have hy : algebraMap B R b ≠ 0 := fun h ↦ (FaithfulSMul.algebraMap_eq_zero_iff B L).not.2 hb <| by
    rw [IsScalarTower.algebraMap_apply B R L, h, map_zero]
  have hy' := mem_nonZeroDivisors_of_ne_zero hy
  have he : Ring.ord R (algebraMap B R b) =
      Ring.ord (Localization.AtPrime p) (algebraMap B _ b) := by
    rw [← e.commutes]
    exact Ring.ord_ringEquiv e.toRingEquiv _
  have hn : Ring.ord R (algebraMap B R b) =
      ((Ring.ord (Localization.AtPrime p) (algebraMap B _ b)).toNat : ℕ∞) := by
    rw [← he, ENat.natCast_toNat (Ring.ord_ne_top hy')]
  rw [IsScalarTower.algebraMap_apply B R L, Ring.ordFrac_eq_ord R hy,
    Ring.ordMonoidWithZeroHom_eq_coe R hy' hn]

end TauCeti
