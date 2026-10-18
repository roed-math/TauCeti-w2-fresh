/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import TauCeti.RingTheory.HahnSeries.Valuation
public import TauCeti.RingTheory.LaurentSeries.Convergence
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Basic

/-!
# The valuation and topology of the Puiseux field

The Puiseux field `TauCeti.puiseuxField K` is a subfield of the rational-exponent Hahn series field
`HahnSeries ℚ K`, so it inherits the order valuation. This file restricts Mathlib's additive
valuation `HahnSeries.addVal ℚ K` and the multiplicative valuation `HahnSeries.valuation ℚ K` to
it, and equips it with the resulting valuation topology through a `Valued` instance. A nonzero
Puiseux series of order `q` has valuation `exp (-q)`, matching Mathlib's normalization on
`K⸨X⸩`, for which `X` has valuation `exp (-1)`.

On the level-`n` image `K⸨t ^ (1 / n)⸩` the order is the integer order of the Laurent series
scaled by `1 / n`. Consequently every level embedding `K⸨X⸩ → puiseuxField K`, with the
Laurent-series valuation topology on its source, is a topological embedding: a homeomorphism onto
its image.

The Puiseux field is not complete. The partial sums of `∑_{j ≥ 1} t ^ (j + 1 / (j + 1))` form a
Cauchy sequence of Puiseux series, but a limit would have every `j + 1 / (j + 1)` in its support,
and these exponents have no common denominator.

## Main definitions

* `TauCeti.puiseuxField.addVal K`: the additive valuation `x ↦ x.orderTop` in `WithTop ℚ`.
* `TauCeti.puiseuxField.valuation K`: the multiplicative valuation in `ℚᵐ⁰`.
* `TauCeti.puiseuxField.valued`: the `Valued` instance defining the valuation topology.

## Main results

* `TauCeti.puiseuxField.addVal_levelEmbedding`: the order of a level-`n` element is the order of
  the Laurent series divided by `n`.
* `TauCeti.puiseuxField.addVal_single` and `TauCeti.puiseuxField.valuation_single`: the additive
  and multiplicative valuations of a nonzero Puiseux monomial.
* `TauCeti.puiseuxField.tendsto_iff_addVal_sub`: convergence in the valuation topology means that
  the order of the difference eventually exceeds every rational bound.
* `TauCeti.puiseuxField.isEmbedding_levelEmbedding`: the level embeddings are homeomorphisms onto
  their images.
* `TauCeti.puiseuxField.cauchySeq_sum_single` and
  `TauCeti.puiseuxField.not_tendsto_sum_single`: the partial sums of
  `∑_{j ≥ 1} t ^ (j + 1 / (j + 1))` are Cauchy but do not converge.
* `TauCeti.puiseuxField.not_completeSpace`: the Puiseux field is not complete.
-/

public section

open Filter HahnSeries LaurentSeries Topology WithZero
open scoped LaurentSeries Topology WithZero

namespace TauCeti

namespace puiseuxField

variable {K : Type*} [Field K]

section Valuation

variable (K) in
/-- The additive valuation on the Puiseux field: the order `x.orderTop` of the underlying
rational-exponent Hahn series, with `ord 0 = ⊤`. -/
noncomputable def addVal : AddValuation (puiseuxField K) (WithTop ℚ) :=
  (HahnSeries.addVal ℚ K).comap (puiseuxField K).val.toRingHom

/-- The additive valuation of a Puiseux series is the order of its underlying Hahn series. -/
@[simp]
theorem addVal_apply (x : puiseuxField K) :
    addVal K x = (x : HahnSeries ℚ K).orderTop :=
  HahnSeries.addVal_apply

/-- The order of a level-`n` Puiseux series is the integer order of the Laurent series scaled by
`1 / n`. -/
theorem addVal_levelEmbedding (n : ℕ+) (f : K⸨X⸩) :
    addVal K (levelEmbedding K n f) = f.orderTop.map fun k : ℤ ↦ (k : ℚ) / n := by
  rw [addVal_apply, coe_levelEmbedding, orderTop_ramifiedEmbedding]

/-- A level-`n` Puiseux series has order at least `q` exactly when the Laurent series has order at
least `⌈q n⌉`. -/
theorem le_addVal_levelEmbedding_iff {n : ℕ+} {f : K⸨X⸩} {q : ℚ} :
    (q : WithTop ℚ) ≤ addVal K (levelEmbedding K n f) ↔
      ((⌈q * n⌉ : ℤ) : WithTop ℤ) ≤ f.orderTop := by
  rw [addVal_levelEmbedding]
  cases f.orderTop with
  | top => simp
  | coe k =>
    rw [WithTop.map_coe, WithTop.coe_le_coe, WithTop.coe_le_coe, Int.ceil_le,
      le_div_iff₀ (by positivity)]

variable (K) in
/-- The multiplicative valuation on the Puiseux field, sending a nonzero series of order `q` to
`exp (-q)` and `0` to `0`. -/
noncomputable def valuation : Valuation (puiseuxField K) ℚᵐ⁰ :=
  (HahnSeries.valuation ℚ K).comap (puiseuxField K).val.toRingHom

/-- The valuation of a Puiseux series is the valuation of its underlying Hahn series. -/
@[simp]
theorem valuation_apply (x : puiseuxField K) :
    valuation K x = HahnSeries.valuation ℚ K x :=
  Valuation.comap_apply _ _ _

/-- A nonzero Puiseux series has valuation `exp (-ord x)`. -/
theorem valuation_of_ne_zero {x : puiseuxField K} (hx : x ≠ 0) :
    valuation K x = exp (-(x : HahnSeries ℚ K).order) :=
  HahnSeries.valuation_of_ne_zero (by simpa using hx)

/-- The additive valuation of the nonzero Puiseux monomial `a t ^ q` is `q`. -/
theorem addVal_single (q : ℚ) {a : K} (ha : a ≠ 0) :
    addVal K (monomial K q a) = q := by
  rw [addVal_apply, coe_monomial]
  exact orderTop_single ha

/-- The multiplicative valuation of the nonzero Puiseux monomial `a t ^ q` is `exp (-q)`. -/
theorem valuation_single (q : ℚ) {a : K} (ha : a ≠ 0) :
    valuation K (monomial K q a) = exp (-q) := by
  rw [valuation_apply, coe_monomial, HahnSeries.valuation_single q ha]

/-- A Puiseux series has valuation at most `exp (-q)` exactly when its order is at least `q`. -/
theorem valuation_le_exp_neg_iff {x : puiseuxField K} {q : ℚ} :
    valuation K x ≤ exp (-q) ↔ (q : WithTop ℚ) ≤ addVal K x := by
  rw [valuation_apply, addVal_apply, HahnSeries.valuation_le_exp_neg_iff]

/-- A Puiseux series has valuation below `exp (-q)` exactly when its order is above `q`. -/
theorem valuation_lt_exp_neg_iff {x : puiseuxField K} {q : ℚ} :
    valuation K x < exp (-q) ↔ (q : WithTop ℚ) < addVal K x := by
  rw [valuation_apply, addVal_apply, HahnSeries.valuation_lt_exp_neg_iff]

/-- The valuation of a nonzero level-`n` Puiseux series is `exp (-(ord f / n))`, where `ord f` is
the integer order of the Laurent series. -/
theorem valuation_levelEmbedding {n : ℕ+} {f : K⸨X⸩} (hf : f ≠ 0) :
    valuation K (levelEmbedding K n f) = exp (-((f.order : ℚ) / n)) := by
  have hn : ramifiedEmbedding K n f ≠ 0 := (map_ne_zero _).mpr hf
  have h : ((ramifiedEmbedding K n f).order : WithTop ℚ) = ((f.order : ℚ) / n : ℚ) := by
    rw [order_eq_orderTop_of_ne_zero hn, orderTop_ramifiedEmbedding,
      ← order_eq_orderTop_of_ne_zero hf, WithTop.map_coe]
  rw [valuation_of_ne_zero ((map_ne_zero _).mpr hf), coe_levelEmbedding, WithTop.coe_inj.mp h]

end Valuation

section Topology

/-- The Puiseux field carries the valuation topology of `TauCeti.puiseuxField.valuation`. -/
noncomputable instance valued : Valued (puiseuxField K) ℚᵐ⁰ :=
  Valued.mk' (valuation K)

/-- The valuation of the `Valued` instance on the Puiseux field is
`TauCeti.puiseuxField.valuation`. -/
theorem valued_v : (Valued.v : Valuation (puiseuxField K) ℚᵐ⁰) = valuation K :=
  (rfl)

/-- A family of Puiseux series converges to `g` in the valuation topology exactly when the order
of the difference with `g` eventually exceeds every rational bound. -/
theorem tendsto_iff_addVal_sub {ι : Type*} {l : Filter ι} (f : ι → puiseuxField K)
    (g : puiseuxField K) :
    Tendsto f l (𝓝 g) ↔ ∀ q : ℚ, ∀ᶠ i in l, (q : WithTop ℚ) ≤ addVal K (f i - g) := by
  rw [← tendsto_sub_nhds_zero_iff, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  simp only [true_implies, Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, valued_v]
  constructor
  · intro h q
    -- the ball of radius `exp (-q)` is the set of series of order above `q`
    let y : puiseuxField K := monomial K q 1
    have hy : y ≠ 0 := by
      rw [ne_eq, ← Subtype.coe_inj]
      simp [y]
    filter_upwards [h (Units.mk0 ((valuation K).restrict y) (by simp [hy]))] with i hi
    rw [Units.val_mk0, ← Valuation.restrict_lt_iff_lt_embedding, Valuation.restrict_lt_iff,
      valuation_single q one_ne_zero,
      valuation_lt_exp_neg_iff] at hi
    exact hi.le
  · intro h γ
    have hγ := MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
    filter_upwards [h (1 - log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1))] with i hi
    rw [← valuation_le_exp_neg_iff] at hi
    refine hi.trans_lt ?_
    rw [← exp_log hγ, exp_lt_exp, exp_log hγ]
    linarith

/-- **Level embeddings are homeomorphisms onto their images.** For the valuation topologies on
`K⸨X⸩` and on the Puiseux field, the level-`n` embedding `X ↦ t ^ (1 / n)` is a topological
embedding. -/
theorem isEmbedding_levelEmbedding (n : ℕ+) : IsEmbedding (levelEmbedding K n) := by
  refine ⟨IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr (le_antisymm ?_ ?_),
    (levelEmbedding K n).toRingHom.injective⟩
  · -- continuity at `0`: order at least `⌈q n⌉` upstairs gives order at least `q` downstairs
    rw [← tendsto_iff_comap]
    refine (tendsto_iff_addVal_sub _ _).mpr fun q ↦ ?_
    filter_upwards [(tendsto_laurentSeries_iff_orderTop_sub id 0).mp tendsto_id ⌈q * n⌉]
      with f hf
    rwa [sub_zero, le_addVal_levelEmbedding_iff, ← sub_zero f]
  · -- order at least `D / n` downstairs gives order at least `D` upstairs
    rw [← tendsto_id', tendsto_laurentSeries_iff_orderTop_sub]
    intro D
    filter_upwards [(tendsto_iff_addVal_sub _ 0).mp (tendsto_comap (f := levelEmbedding K n))
      ((D : ℚ) / n)] with f hf
    rwa [sub_zero, le_addVal_levelEmbedding_iff, div_mul_cancel₀ _ (by positivity),
      Int.ceil_intCast, ← sub_zero f] at hf

end Topology

section NotComplete

private noncomputable def partialSums (N : ℕ) : puiseuxField K :=
  ∑ j ∈ Finset.Ico 1 N, monomial K ((j : ℚ) + 1 / (j + 1)) 1

private theorem coeff_partialSums (N : ℕ) (q : ℚ) :
    ((partialSums (K := K) N : puiseuxField K) : HahnSeries ℚ K).coeff q =
      ∑ j ∈ Finset.Ico 1 N,
        (HahnSeries.single ((j : ℚ) + 1 / (j + 1)) 1 : HahnSeries ℚ K).coeff q := by
  rw [partialSums, AddSubmonoidClass.coe_finsetSum, coeff_sum]
  simp only [coe_monomial]

/-- **The partial sums of `∑_{j ≥ 1} t ^ (j + 1 / (j + 1))` are Cauchy** in the valuation
topology of the Puiseux field: the terms of index at least `N` have order above `N`. -/
theorem cauchySeq_sum_single :
    CauchySeq fun N : ℕ ↦ ∑ j ∈ Finset.Ico 1 N,
      monomial K ((j : ℚ) + 1 / (j + 1)) 1 := by
  change CauchySeq (partialSums (K := K))
  let s := partialSums (K := K)
  -- the tail from index `N ≥ 1` has order at least `N`
  have htail : ∀ N m : ℕ, 1 ≤ N → N ≤ m → ((N : ℚ) : WithTop ℚ) ≤ addVal K (s m - s N) := by
    intro N m h₁ h₂
    simp only [s, partialSums]
    rw [← Finset.sum_Ico_consecutive _ h₁ h₂, add_sub_cancel_left]
    refine AddValuation.map_le_sum _ fun j hj ↦ ?_
    rw [addVal_single _ one_ne_zero, WithTop.coe_le_coe]
    have : (N : ℚ) ≤ j := by exact_mod_cast (Finset.mem_Ico.mp hj).1
    linarith [show (0 : ℚ) ≤ 1 / (j + 1) by positivity]
  rw [CauchySeq, IsUniformAddGroup.cauchy_map_iff_tendsto]
  refine ⟨atTop_neBot, (tendsto_iff_addVal_sub _ 0).mpr fun q ↦ ?_⟩
  set N := ⌈q⌉₊ + 1
  filter_upwards [prod_mem_prod (eventually_ge_atTop N) (eventually_ge_atTop N)]
  rintro ⟨m, k⟩ ⟨hm, hk⟩
  have hq : (q : WithTop ℚ) ≤ ((N : ℚ) : WithTop ℚ) := by
    rw [WithTop.coe_le_coe]
    exact (Nat.le_ceil q).trans (by simp [N])
  rw [sub_zero, show s m - s k = (s m - s N) - (s k - s N) by abel]
  exact hq.trans (AddValuation.map_le_sub _ (htail N m (by simp [N]) hm)
    (htail N k (by simp [N]) hk))

/-- **The partial sums of `∑_{j ≥ 1} t ^ (j + 1 / (j + 1))` do not converge** in the Puiseux
field: a limit would have coefficient `1` at every exponent `j + 1 / (j + 1)`, and these exponents
have no common denominator. -/
theorem not_tendsto_sum_single (x : puiseuxField K) :
    ¬ Tendsto (fun N : ℕ ↦ ∑ j ∈ Finset.Ico 1 N,
      monomial K ((j : ℚ) + 1 / (j + 1)) 1)
        atTop (𝓝 x) := by
  change ¬ Tendsto (partialSums (K := K)) atTop (𝓝 x)
  intro h
  obtain ⟨n, hn⟩ := mem_puiseuxField_iff_exists_den_dvd.mp x.2
  set e : ℚ := (n : ℚ) + 1 / (n + 1)
  refine not_den_exponent_dvd n (hn e ?_)
  -- far enough along, the partial sum agrees with `x` beyond the exponent `e`
  obtain ⟨N, hN, hnN⟩ :=
    ((tendsto_iff_addVal_sub _ x).mp h (e + 1) |>.and (eventually_gt_atTop (n : ℕ))).exists
  rw [addVal_apply] at hN
  have hcoeff := coeff_eq_zero_of_lt_orderTop ((WithTop.coe_lt_coe.mpr (lt_add_one e)).trans_le hN)
  simp only [AddSubgroupClass.coe_sub, coeff_sub, sub_eq_zero] at hcoeff
  rw [coeff_partialSums] at hcoeff
  simp only [coeff_single, strictMono_exponent.injective.eq_iff, e] at hcoeff
  rw [mem_support, ← hcoeff, Finset.sum_ite_eq]
  simp [hnN]

/-- **The Puiseux field is not complete** for its valuation topology. -/
theorem not_completeSpace : ¬ CompleteSpace (puiseuxField K) := fun _ ↦
  let ⟨x, hx⟩ := cauchySeq_tendsto_of_complete (cauchySeq_sum_single (K := K))
  not_tendsto_sum_single x hx

end NotComplete

end puiseuxField

end TauCeti
