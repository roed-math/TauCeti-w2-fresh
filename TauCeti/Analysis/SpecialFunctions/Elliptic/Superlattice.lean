/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.ScalarMap

/-!
# `℘` of a superlattice

Let `Λ ⊆ Λ'` be period lattices. Then `Λ'` is the union of the finitely many cosets `t + Λ` with
`t` running over representatives of `Λ' / Λ`, and splitting the absolutely convergent series of
`℘_{Λ'}` along these cosets gives **Vélu's formulas**

`℘_{Λ'}(z) = ∑_{t ∈ Λ' / Λ} (℘_Λ(z - t) - ℘_Λ(t))`, `℘'_{Λ'}(z) = ∑_{t ∈ Λ' / Λ} ℘'_Λ(z - t)`

(`PeriodPair.hasSum_weierstrassP_of_le`, `PeriodPair.hasSum_derivWeierstrassP_of_le`). The term
of the trivial coset is `℘_Λ(z)`, since `℘_Λ` vanishes on `Λ`. By the addition theorem each
`℘_Λ(z - t)` with `t ∉ Λ` is a rational function of `℘_Λ(z)` and `℘'_Λ(z)`
(`PeriodPair.weierstrassP_sub_eq`, `PeriodPair.derivWeierstrassP_sub_eq`), so `℘_{Λ'}` and
`℘'_{Λ'}` are rational functions of `℘_Λ` and `℘'_Λ` off `Λ'`
(`PeriodPair.hasSum_weierstrassP_sub_weierstrassP_of_le`,
`PeriodPair.hasSum_derivWeierstrassP_sub_derivWeierstrassP_of_le`).

This describes the scalar maps of `PeriodPair.scalarPointHom` by `℘` and `℘'`: for `α Λ ⊆ Λ'`
the lattice `Λ` lies in `α⁻¹ Λ'`, and `℘_{Λ'}(α z) = α⁻² ℘_{α⁻¹ Λ'}(z)`
(`PeriodPair.hasSum_weierstrassP_mul`, `PeriodPair.hasSum_derivWeierstrassP_mul`).

The addition theorem applies to `℘_Λ(z - t)` because `℘_Λ` takes the same value at `z` and `w`
only when `z ≡ ± w` modulo `Λ` (`PeriodPair.sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq`).

## Main results

* `PeriodPair.finite_quotient_of_le`: `Λ' / Λ` is finite.
* `PeriodPair.hasSum_weierstrassP_of_le`, `PeriodPair.hasSum_derivWeierstrassP_of_le`: Vélu's
  formulas for `℘_{Λ'}` and `℘'_{Λ'}` as sums over `Λ' / Λ`.
* `PeriodPair.hasSum_weierstrassP_mul`, `PeriodPair.hasSum_derivWeierstrassP_mul`: for
  `α Λ ⊆ Λ'`, `℘_{Λ'}(α z)` and `℘'_{Λ'}(α z)` as finite sums of translates of `℘_Λ` and `℘'_Λ`.
* `PeriodPair.sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq`: `℘(z) = ℘(w)` off the
  lattice forces `z ≡ ± w`.
* `PeriodPair.weierstrassP_sub_eq`, `PeriodPair.derivWeierstrassP_sub_eq`: `℘_Λ(z - t)` and
  `℘'_Λ(z - t)` as rational functions of `℘_Λ(z)` and `℘'_Λ(z)`.
* `PeriodPair.hasSum_weierstrassP_sub_weierstrassP_of_le`,
  `PeriodPair.hasSum_derivWeierstrassP_sub_derivWeierstrassP_of_le`: the rational description of
  `℘_{Λ'}` and `℘'_{Λ'}` in terms of `℘_Λ` and `℘'_Λ`.

## References

* J. Vélu, *Isogénies entre courbes elliptiques*, C. R. Acad. Sci. Paris Sér. A–B 273 (1971).
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §VI.4 and Exercise 6.6.
-/

public noncomputable section

namespace PeriodPair

variable {L L' : PeriodPair}

/-- A sublattice of a period lattice has finite index. -/
lemma finite_quotient_of_le (h : L.lattice ≤ L'.lattice) :
    Finite (L'.lattice.toAddSubgroup ⧸
      L.lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup) := by
  have h₁ := relIndex_lattice_smul_ne_zero (L := L) (L' := L') 1 (fun z hz ↦ by simpa using h hz)
  rw [one_smul] at h₁
  have : (L.lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup).FiniteIndex := ⟨h₁⟩
  infer_instance

/-- Splitting a series over `Λ'` along the cosets of `Λ`: the sum over the coset of `t` is the sum
over `Λ` of the translate by `t`. -/
private lemma hasSum_fiberwise (h : L.lattice ≤ L'.lattice) {f : ℂ → ℂ} {a : ℂ}
    (hf : HasSum (fun l : L'.lattice ↦ f l) a)
    {g : (L'.lattice.toAddSubgroup ⧸
      L.lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup) → ℂ}
    (hg : ∀ c, HasSum (fun l : L.lattice ↦ f ((c.out : ℂ) + l)) (g c)) :
    HasSum g a := by
  let q : L'.lattice → L'.lattice.toAddSubgroup ⧸
      L.lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup :=
    fun m ↦ QuotientAddGroup.mk (⟨m, m.2⟩ : L'.lattice.toAddSubgroup)
  refine (hf.tsum_fiberwise q).congr_fun fun c ↦ ?_
  -- The coset of `c` is `c.out + Λ`.
  have hmem : ∀ l : L.lattice, (c.out : ℂ) + l ∈ L'.lattice := fun l ↦ add_mem c.out.2 (h l.2)
  let e : L.lattice ≃ q ⁻¹' {c} :=
    { toFun l := ⟨⟨_, hmem l⟩, by
        rw [Set.mem_preimage, Set.mem_singleton_iff]
        conv_rhs => rw [← c.out_eq']
        rw [eq_comm, QuotientAddGroup.eq]
        simp [AddSubgroup.mem_addSubgroupOf]⟩
      invFun m := ⟨(m : ℂ) - c.out, by
        have hm : q m = c := Set.mem_singleton_iff.mp (Set.mem_preimage.mp m.2)
        conv at hm => rhs; rw [← c.out_eq']
        rw [QuotientAddGroup.eq] at hm
        have hm' : (c.out : ℂ) - m ∈ L.lattice := by
          simpa [AddSubgroup.mem_addSubgroupOf, neg_add_eq_sub] using hm
        simpa using neg_mem hm'⟩
      left_inv l := by simp
      right_inv m := by ext; simp }
  rw [← e.tsum_eq]
  exact ((hg c).tsum_eq).symm

/-- **Vélu's formula for `℘`.** If `Λ ⊆ Λ'`, then
`℘_{Λ'}(z) = ∑_{t ∈ Λ' / Λ} (℘_Λ(z - t) - ℘_Λ(t))`, the sum running over representatives `t`
of the finitely many classes of `Λ' / Λ`. -/
theorem hasSum_weierstrassP_of_le (h : L.lattice ≤ L'.lattice) (z : ℂ) :
    HasSum (fun c : L'.lattice.toAddSubgroup ⧸
        L.lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup ↦
      ℘[L] (z - c.out) - ℘[L] c.out) (℘[L'] z) := by
  refine hasSum_fiberwise h (f := fun m ↦ 1 / (z - m) ^ 2 - 1 / m ^ 2)
    (L'.hasSum_weierstrassP z) fun c ↦ ?_
  have h₁ := (L.hasSum_weierstrassP (z - c.out)).sub (L.hasSum_weierstrassP (-c.out))
  rw [weierstrassP_neg] at h₁
  refine h₁.congr_fun fun l ↦ ?_
  rw [show (-(c.out : ℂ) - l) ^ 2 = ((c.out : ℂ) + l) ^ 2 by ring]
  ring

/-- **Vélu's formula for `℘'`.** If `Λ ⊆ Λ'`, then `℘'_{Λ'}(z) = ∑_{t ∈ Λ' / Λ} ℘'_Λ(z - t)`. -/
theorem hasSum_derivWeierstrassP_of_le (h : L.lattice ≤ L'.lattice) (z : ℂ) :
    HasSum (fun c : L'.lattice.toAddSubgroup ⧸
        L.lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup ↦
      ℘'[L] (z - c.out)) (℘'[L'] z) := by
  refine hasSum_fiberwise h (f := fun m ↦ -2 / (z - m) ^ 3)
    (L'.hasSum_derivWeierstrassP z) fun c ↦ ?_
  refine (L.hasSum_derivWeierstrassP (z - c.out)).congr_fun fun l ↦ ?_
  ring_nf

/-- A scalar map `α Λ ⊆ Λ'` makes `Λ` a sublattice of `α⁻¹ Λ'`. -/
lemma lattice_le_lattice_inv_smul (c : ℂˣ) (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice) :
    L.lattice ≤ (c⁻¹ • L').lattice := fun x hx ↦ by
  simpa using (mul_mem_lattice_smul_iff (L := L') (c := c⁻¹)).mpr (h x hx)

/-- **Vélu's formula for a scalar map.** If `α Λ ⊆ Λ'`, then
`℘_{Λ'}(α z) = α⁻² ∑_{t ∈ α⁻¹ Λ' / Λ} (℘_Λ(z - t) - ℘_Λ(t))`. -/
theorem hasSum_weierstrassP_mul (c : ℂˣ) (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice)
    (z : ℂ) :
    HasSum (fun t : (c⁻¹ • L').lattice.toAddSubgroup ⧸
        L.lattice.toAddSubgroup.addSubgroupOf (c⁻¹ • L').lattice.toAddSubgroup ↦
      (℘[L] (z - t.out) - ℘[L] t.out) / (c : ℂ) ^ 2) (℘[L'] (c * z)) := by
  have := (hasSum_weierstrassP_of_le (lattice_le_lattice_inv_smul c h) z).div_const ((c : ℂ) ^ 2)
  rwa [← weierstrassP_smul, smul_inv_smul] at this

/-- **Vélu's formula for `℘'` and a scalar map.** If `α Λ ⊆ Λ'`, then
`℘'_{Λ'}(α z) = α⁻³ ∑_{t ∈ α⁻¹ Λ' / Λ} ℘'_Λ(z - t)`. -/
theorem hasSum_derivWeierstrassP_mul (c : ℂˣ) (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice)
    (z : ℂ) :
    HasSum (fun t : (c⁻¹ • L').lattice.toAddSubgroup ⧸
        L.lattice.toAddSubgroup.addSubgroupOf (c⁻¹ • L').lattice.toAddSubgroup ↦
      ℘'[L] (z - t.out) / (c : ℂ) ^ 3) (℘'[L'] (c * z)) := by
  have := (hasSum_derivWeierstrassP_of_le (lattice_le_lattice_inv_smul c h) z).div_const
    ((c : ℂ) ^ 3)
  rwa [← derivWeierstrassP_smul, smul_inv_smul] at this

variable {z w : ℂ}

/-- `℘` takes the same value at `z, w ∉ Λ` only when `z ≡ w` or `z ≡ -w` modulo `Λ`. -/
theorem sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (h : ℘[L] z = ℘[L] w) : z - w ∈ L.lattice ∨ z + w ∈ L.lattice := by
  have hsq : ℘'[L] z ^ 2 = ℘'[L] w ^ 2 := by
    rw [L.derivWeierstrassP_sq z hz, L.derivWeierstrassP_sq w hw, h]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h' | h'
  · left
    rw [← weierstrassPoint_eq_zero_iff, ← weierstrassPointHom_apply, map_sub,
      weierstrassPointHom_apply, weierstrassPointHom_apply, sub_eq_zero,
      L.weierstrassPoint_of_notMem hz, L.weierstrassPoint_of_notMem hw]
    simp [h, h']
  · right
    rw [← weierstrassPoint_eq_zero_iff, weierstrassPoint_add, ← neg_neg (L.weierstrassPoint w),
      ← weierstrassPoint_neg, ← sub_eq_add_neg, sub_eq_zero, L.weierstrassPoint_of_notMem hz,
      L.weierstrassPoint_of_notMem (by simpa using hw)]
    simp [h, h', weierstrassP_neg, derivWeierstrassP_neg]

/-- **`℘(z - w)` as a rational function of `℘(z)` and `℘'(z)`.** If `z, w ∉ Λ` and `z ± w ∉ Λ`,
then `℘(z - w) = ((℘'(z) + ℘'(w)) / (℘(z) - ℘(w)))² / 4 - ℘(z) - ℘(w)`. -/
theorem weierstrassP_sub_eq (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z - w ∉ L.lattice) (hzw' : z + w ∉ L.lattice) :
    ℘[L] (z - w) =
      ((℘'[L] z + ℘'[L] w) / (℘[L] z - ℘[L] w)) ^ 2 / 4 - ℘[L] z - ℘[L] w := by
  have hne : ℘[L] z ≠ ℘[L] (-w) := by
    rw [weierstrassP_neg]
    exact fun h ↦ (sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq hz hw h).elim hzw hzw'
  rw [sub_eq_add_neg, L.weierstrassP_add hz (by simpa using hw) hne, weierstrassP_neg,
    derivWeierstrassP_neg, sub_neg_eq_add]

/-- **`℘'(z - w)` in terms of `℘(z)`, `℘'(z)` and `℘(z - w)`.** If `z, w ∉ Λ` and `z ± w ∉ Λ`, then
`℘'(z - w) = -m (℘(z - w) - ℘(z)) - ℘'(z)` with `m = (℘'(z) + ℘'(w)) / (℘(z) - ℘(w))`. -/
theorem derivWeierstrassP_sub_eq (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z - w ∉ L.lattice) (hzw' : z + w ∉ L.lattice) :
    ℘'[L] (z - w) =
      -((℘'[L] z + ℘'[L] w) / (℘[L] z - ℘[L] w)) * (℘[L] (z - w) - ℘[L] z) - ℘'[L] z := by
  have hne : ℘[L] z ≠ ℘[L] (-w) := by
    rw [weierstrassP_neg]
    exact fun h ↦ (sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq hz hw h).elim hzw hzw'
  rw [sub_eq_add_neg, L.derivWeierstrassP_add hz (by simpa using hw) hne, weierstrassP_neg,
    derivWeierstrassP_neg, sub_neg_eq_add]

/-- The representative of a class of `Λ' / Λ` lies in `Λ` exactly for the trivial class. -/
private lemma out_mem_lattice_iff
    (c : L'.lattice.toAddSubgroup ⧸
      L.lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup) :
    (c.out : ℂ) ∈ L.lattice ↔ c = 0 := by
  conv_rhs => rw [← QuotientAddGroup.out_eq' c]
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]

/-- If `z ∉ Λ'` and `t ∈ Λ' \ Λ`, the addition theorem applies to `z` and `t` in `Λ`. -/
private lemma notMem_of_notMem_of_le (h : L.lattice ≤ L'.lattice) (hz : z ∉ L'.lattice)
    (hw : w ∈ L'.lattice) : z ∉ L.lattice ∧ z - w ∉ L.lattice ∧ z + w ∉ L.lattice :=
  ⟨fun h' ↦ hz (h h'), fun h' ↦ hz (by simpa using add_mem (h h') hw),
    fun h' ↦ hz (by simpa using sub_mem (h h') hw)⟩

/-- **`℘_{Λ'}` as a rational function of `℘_Λ` and `℘'_Λ`.** If `Λ ⊆ Λ'` and `z ∉ Λ'`, then
`℘_{Λ'}(z) - ℘_Λ(z)` is the sum over the nontrivial classes `t` of `Λ' / Λ` of
`((℘'_Λ(z) + ℘'_Λ(t)) / (℘_Λ(z) - ℘_Λ(t)))² / 4 - ℘_Λ(z) - 2 ℘_Λ(t)`. -/
theorem hasSum_weierstrassP_sub_weierstrassP_of_le (h : L.lattice ≤ L'.lattice)
    (hz : z ∉ L'.lattice) :
    HasSum (fun c : {c : L'.lattice.toAddSubgroup ⧸
        L.lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup // c ≠ 0} ↦
      ((℘'[L] z + ℘'[L] c.1.out) / (℘[L] z - ℘[L] c.1.out)) ^ 2 / 4 - ℘[L] z - 2 * ℘[L] c.1.out)
      (℘[L'] z - ℘[L] z) := by
  classical
  have h₀ := (out_mem_lattice_iff (L := L) (L' := L') 0).mpr rfl
  have hsum := hasSum_ite_sub_hasSum (hasSum_weierstrassP_of_le h z) 0
  rw [L.weierstrassP_sub_coe z ⟨_, h₀⟩, L.weierstrassP_coe ⟨_, h₀⟩, sub_zero] at hsum
  refine hasSum_subtype_iff_indicator (s := {c | c ≠ 0}) (f := fun (c : L'.lattice.toAddSubgroup ⧸
      L.lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup) ↦
    ((℘'[L] z + ℘'[L] c.out) / (℘[L] z - ℘[L] c.out)) ^ 2 / 4 - ℘[L] z - 2 * ℘[L] c.out)
    |>.mpr (hsum.congr_fun fun c ↦ ?_)
  by_cases hc : c = 0
  · simp [hc]
  obtain ⟨hz', hzt, hzt'⟩ := notMem_of_notMem_of_le h hz c.out.2
  simp only [hc, ↓reduceIte]
  rw [Set.indicator_of_mem (show c ∈ {c | c ≠ 0} from hc),
    weierstrassP_sub_eq hz' (mt (out_mem_lattice_iff c).mp hc) hzt hzt']
  ring

/-- **`℘'_{Λ'}` in terms of `℘_Λ` and `℘'_Λ`.** If `Λ ⊆ Λ'` and `z ∉ Λ'`, then
`℘'_{Λ'}(z) - ℘'_Λ(z)` is the sum over the nontrivial classes `t` of `Λ' / Λ` of
`-m (m² / 4 - 2 ℘_Λ(z) - ℘_Λ(t)) - ℘'_Λ(z)` with `m = (℘'_Λ(z) + ℘'_Λ(t)) / (℘_Λ(z) - ℘_Λ(t))`.
-/
theorem hasSum_derivWeierstrassP_sub_derivWeierstrassP_of_le (h : L.lattice ≤ L'.lattice)
    (hz : z ∉ L'.lattice) :
    HasSum (fun c : {c : L'.lattice.toAddSubgroup ⧸
        L.lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup // c ≠ 0} ↦
      -((℘'[L] z + ℘'[L] c.1.out) / (℘[L] z - ℘[L] c.1.out)) *
        (((℘'[L] z + ℘'[L] c.1.out) / (℘[L] z - ℘[L] c.1.out)) ^ 2 / 4 - 2 * ℘[L] z -
          ℘[L] c.1.out) - ℘'[L] z)
      (℘'[L'] z - ℘'[L] z) := by
  classical
  have h₀ := (out_mem_lattice_iff (L := L) (L' := L') 0).mpr rfl
  have hsum := hasSum_ite_sub_hasSum (hasSum_derivWeierstrassP_of_le h z) 0
  rw [L.derivWeierstrassP_sub_coe z ⟨_, h₀⟩] at hsum
  refine hasSum_subtype_iff_indicator (s := {c | c ≠ 0}) (f := fun (c : L'.lattice.toAddSubgroup ⧸
      L.lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup) ↦
    -((℘'[L] z + ℘'[L] c.out) / (℘[L] z - ℘[L] c.out)) *
      (((℘'[L] z + ℘'[L] c.out) / (℘[L] z - ℘[L] c.out)) ^ 2 / 4 - 2 * ℘[L] z - ℘[L] c.out) -
        ℘'[L] z) |>.mpr (hsum.congr_fun fun c ↦ ?_)
  by_cases hc : c = 0
  · simp [hc]
  obtain ⟨hz', hzt, hzt'⟩ := notMem_of_notMem_of_le h hz c.out.2
  have ht := mt (out_mem_lattice_iff c).mp hc
  simp only [hc, ↓reduceIte]
  rw [Set.indicator_of_mem (show c ∈ {c | c ≠ 0} from hc), derivWeierstrassP_sub_eq hz' ht hzt hzt',
    weierstrassP_sub_eq hz' ht hzt hzt']
  ring

end PeriodPair
