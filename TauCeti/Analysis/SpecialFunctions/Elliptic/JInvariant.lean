/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.Uniformization
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The `j`-invariant classifies lattices up to homothety

Two lattices with the same invariants `g₂` and `g₃` are equal
(`PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq`), and two lattices whose Weierstrass curves have the
same `j`-invariant are homothetic (`PeriodPair.weierstrassCurve_j_eq_iff`).

For the first statement write `℘ = f + 1 / z²` and `℘' = d - 2 / z³` near `0`, with `f` and `d`
holomorphic at `0` (`PeriodPair.weierstrassPExcept` and `PeriodPair.derivWeierstrassPExcept`).
Multiplying the differential equation `℘'² = 4 ℘³ - g₂ ℘ - g₃` by `z⁶` gives a polynomial relation
between `z`, `f` and `d`. For two lattices with the same `g₂` and `g₃`, with functions `f₁, d₁` and
`f₂, d₂`, subtracting the two relations shows that `s = f₁ - f₂`, whose derivative is `d₁ - d₂`,
satisfies near `0`

  `z s'(z) (z³ (d₁(z) + d₂(z)) - 4) = s(z) Q(z)`,  with `Q` holomorphic and `Q(0) = 12`.

If `s` did not vanish near `0`, write `s(z) = z^m g(z)` with `g(0) ≠ 0`; comparing the
coefficients of `z^m` gives `-4 m = 12`, which is impossible. So the two `℘`-functions agree near
`0`, hence on the connected complement of the union of both lattices. Since `℘` has a double pole
at each point of its own lattice, each lattice is contained in the other.

For the second statement, equal `j`-invariants `1728 g₂³ / (g₂³ - 27 g₃²)` give a `μ ≠ 0` with
`g₂' = μ⁴ g₂` and `g₃' = μ⁶ g₃`; then the lattice `μ⁻¹ Λ` has the invariants of `Λ'`, so it is
`Λ'`.

## Main results

* `PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq`: a lattice is determined by `g₂` and `g₃`.
* `PeriodPair.weierstrassCurve_eq_iff`: two lattices have the same Weierstrass curve if and only
  if they are equal.
* `PeriodPair.exists_lattice_eq_smul_of_weierstrassCurve_j_eq`: lattices with the same
  `j`-invariant are homothetic.
* `PeriodPair.weierstrassCurve_j_eq_iff`: two lattices have the same `j`-invariant if and only if
  they are homothetic.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §VI.3 and §VI.5.
-/

public section

open Filter Topology Set

namespace PeriodPair

/-- Multiplying the differential equation of `℘` by `z⁶`: near `0`, with
`℘ = ℘₀ + 1 / z²` and `℘' = ℘₀' - 2 / z³`, it reads
`(z³ ℘₀' - 2)² = 4 (z² ℘₀ + 1)³ - g₂ z⁴ (z² ℘₀ + 1) - g₃ z⁶`. -/
private lemma derivWeierstrassPExcept_zero_relation (L : PeriodPair) {z : ℂ} (hz : z ≠ 0)
    (hzL : z ∉ L.lattice) :
    (z ^ 3 * L.derivWeierstrassPExcept 0 z - 2) ^ 2 =
      4 * (z ^ 2 * L.weierstrassPExcept 0 z + 1) ^ 3 -
        L.g₂ * z ^ 4 * (z ^ 2 * L.weierstrassPExcept 0 z + 1) - L.g₃ * z ^ 6 := by
  have h₁ : z ^ 3 * L.derivWeierstrassPExcept 0 z - 2 = z ^ 3 * L.derivWeierstrassP z := by
    rw [← ZeroMemClass.coe_zero L.lattice, L.derivWeierstrassPExcept_def]
    simp only [ZeroMemClass.coe_zero, sub_zero]
    field_simp
    ring
  have h₂ : z ^ 2 * L.weierstrassPExcept 0 z + 1 = z ^ 2 * L.weierstrassP z := by
    rw [← ZeroMemClass.coe_zero L.lattice, L.weierstrassPExcept_def]
    simp only [ZeroMemClass.coe_zero, sub_zero]
    field_simp
    ring
  rw [h₁, h₂]
  linear_combination z ^ 6 * L.derivWeierstrassP_sq z hzL

/-- **Near `0` the `℘`-function is determined by `g₂` and `g₃`.** If two lattices have the same
invariants `g₂` and `g₃`, the holomorphic parts `℘ - 1 / z²` of their `℘`-functions agree near
`0`. -/
theorem weierstrassPExcept_zero_eventuallyEq {L L' : PeriodPair} (h₂ : L.g₂ = L'.g₂)
    (h₃ : L.g₃ = L'.g₃) : L.weierstrassPExcept 0 =ᶠ[𝓝 0] L'.weierstrassPExcept 0 := by
  set f₁ := L.weierstrassPExcept 0
  set f₂ := L'.weierstrassPExcept 0
  set d₁ := L.derivWeierstrassPExcept 0
  set d₂ := L'.derivWeierstrassPExcept 0
  have hf₁ : AnalyticAt ℂ f₁ 0 := L.analyticAt_weierstrassPExcept 0
  have hf₂ : AnalyticAt ℂ f₂ 0 := L'.analyticAt_weierstrassPExcept 0
  have hd₁ : AnalyticAt ℂ d₁ 0 := L.analyticAt_derivWeierstrassPExcept 0
  have hd₂ : AnalyticAt ℂ d₂ 0 := L'.analyticAt_derivWeierstrassPExcept 0
  by_contra hne
  have hs : AnalyticAt ℂ (fun z ↦ f₁ z - f₂ z) 0 := hf₁.sub hf₂
  obtain ⟨m, g, hg, hg0, hsg⟩ := hs.exists_eventuallyEq_pow_smul_ne_zero_iff.mpr fun h ↦
    hne (h.mono fun z hz ↦ sub_eq_zero.mp hz)
  simp only [sub_zero, smul_eq_mul] at hsg
  set Q : ℂ → ℂ := fun z ↦ 4 * ((z ^ 2 * f₁ z + 1) ^ 2 + (z ^ 2 * f₁ z + 1) * (z ^ 2 * f₂ z + 1) +
    (z ^ 2 * f₂ z + 1) ^ 2) - L.g₂ * z ^ 4
  set B : ℂ → ℂ := fun z ↦
    (m * g z + z * deriv g z) * (z ^ 3 * (d₁ z + d₂ z) - 4) - g z * Q z
  -- The relation `z^m B(z) = 0` holds near `0`, away from `0`.
  have hB : ∀ᶠ z in 𝓝[≠] 0, B z = 0 := by
    have hnhds : ∀ᶠ z in 𝓝 (0 : ℂ), z ∉ (L.lattice \ {0} : Set ℂ) ∧
        z ∉ (L'.lattice \ {0} : Set ℂ) ∧
        (fun w ↦ f₁ w - f₂ w) =ᶠ[𝓝 z] (fun w ↦ w ^ m * g w) ∧ AnalyticAt ℂ g z ∧
        AnalyticAt ℂ f₁ z ∧ AnalyticAt ℂ f₂ z := by
      filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0,
        L'.compl_lattice_sdiff_singleton_mem_nhds 0, hsg.eventually_nhds,
        hg.eventually_analyticAt, hf₁.eventually_analyticAt, hf₂.eventually_analyticAt]
        with z h₁ h₂ h₃ h₄ h₅ h₆
      exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
    filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin]
      with z ⟨hzL, hzL', hzs, hgz, hf₁z, hf₂z⟩ (hz : z ≠ 0)
    have hzL₀ : z ∉ L.lattice := fun h ↦ hzL ⟨h, hz⟩
    have hzL₀' : z ∉ L'.lattice := fun h ↦ hzL' ⟨h, hz⟩
    -- The derivative of `s = f₁ - f₂`, computed in two ways.
    have hderiv : d₁ z - d₂ z = m * z ^ (m - 1) * g z + z ^ m * deriv g z := by
      have e₁ : deriv (fun w ↦ f₁ w - f₂ w) z = d₁ z - d₂ z := by
        rw [deriv_fun_sub hf₁z.differentiableAt hf₂z.differentiableAt,
          L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hzL,
          L'.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hzL']
      rw [← e₁, hzs.deriv_eq]
      exact ((hasDerivAt_pow m z).mul hgz.differentiableAt.hasDerivAt).deriv
    have hzm : z * (m * z ^ (m - 1)) = m * z ^ m := by
      rcases m with _ | m
      · simp
      · simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
        ring
    have hrel := (derivWeierstrassPExcept_zero_relation L hz hzL₀)
    have hrel' := (derivWeierstrassPExcept_zero_relation L' hz hzL₀')
    rw [← h₂, ← h₃] at hrel'
    have hsz : f₁ z - f₂ z = z ^ m * g z := hzs.eq_of_nhds
    -- `z² (z (d₁ - d₂) (z³ (d₁ + d₂) - 4) - (f₁ - f₂) Q) = 0` by the two relations.
    have key : z * (d₁ z - d₂ z) * (z ^ 3 * (d₁ z + d₂ z) - 4) = (f₁ z - f₂ z) * Q z :=
      mul_left_cancel₀ (pow_ne_zero 2 hz) (by simp only [Q]; linear_combination hrel - hrel')
    rw [hderiv, hsz] at key
    have : z ^ m * B z = 0 := by
      simp only [B]
      linear_combination key - (g z * (z ^ 3 * (d₁ z + d₂ z) - 4)) * hzm
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero m hz)
  -- Hence `B(0) = -(4 m + 12) g(0)` vanishes, so `g(0) = 0`.
  have hBc : ContinuousAt B 0 := by
    have := hg.continuousAt
    have := hg.deriv.continuousAt
    have := hf₁.continuousAt
    have := hf₂.continuousAt
    have := hd₁.continuousAt
    have := hd₂.continuousAt
    simp only [B, Q]
    fun_prop
  have hB0 : B 0 = 0 := tendsto_nhds_unique (hBc.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' (hB.mono fun z hz ↦ hz.symm))
  have hf₁0 : f₁ 0 = 0 := by simp [f₁]
  have hf₂0 : f₂ 0 = 0 := by simp [f₂]
  simp only [B, Q, hf₁0, hf₂0] at hB0
  have : ((4 * m + 12 : ℕ) : ℂ) * g 0 = 0 := by push_cast; linear_combination -hB0
  exact hg0 ((mul_eq_zero.mp this).resolve_left (by norm_cast))

/-- **A lattice is determined by its invariants `g₂` and `g₃`.** -/
theorem lattice_eq_of_g₂_eq_of_g₃_eq {L L' : PeriodPair} (h₂ : L.g₂ = L'.g₂)
    (h₃ : L.g₃ = L'.g₃) : L.lattice = L'.lattice := by
  suffices key : ∀ {L L' : PeriodPair}, L.g₂ = L'.g₂ → L.g₃ = L'.g₃ → L.lattice ≤ L'.lattice from
    le_antisymm (key h₂ h₃) (key h₂.symm h₃.symm)
  intro L L' h₂ h₃ l hl
  by_contra hl'
  have hl0 : l ≠ 0 := by rintro rfl; exact hl' (zero_mem _)
  -- The holomorphic parts of the two `℘`-functions agree off both lattices.
  set U : Set ℂ := ((L.lattice ∪ L'.lattice : Set ℂ) \ {0})ᶜ
  have hU : IsPreconnected U :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) (Set.Countable.mono sdiff_le
      (Set.Countable.union (countable_of_Lindelof_of_discrete (X := L.lattice))
        (countable_of_Lindelof_of_discrete (X := L'.lattice))))).2
  have hU₁ : U ⊆ (L.lattice \ {0} : Set ℂ)ᶜ :=
    compl_subset_compl.mpr (sdiff_subset_sdiff subset_union_left le_rfl)
  have hU₂ : U ⊆ (L'.lattice \ {0} : Set ℂ)ᶜ :=
    compl_subset_compl.mpr (sdiff_subset_sdiff subset_union_right le_rfl)
  have heq : EqOn (L.weierstrassPExcept 0) (L'.weierstrassPExcept 0) U :=
    ((L.analyticOnNhd_weierstrassPExcept 0).mono hU₁).eqOn_of_preconnected_of_eventuallyEq
      ((L'.analyticOnNhd_weierstrassPExcept 0).mono hU₂) hU (by simp [U])
      (weierstrassPExcept_zero_eventuallyEq h₂ h₃)
  -- So near `l`, the `℘`-function of `L` agrees with a function continuous at `l`; but it has a
  -- pole at `l`.
  have hP (z : ℂ) : L.weierstrassP z = L.weierstrassPExcept 0 z + 1 / z ^ 2 := by
    rw [← ZeroMemClass.coe_zero L.lattice, L.weierstrassPExcept_def]
    simp
  have hev : L.weierstrassP =ᶠ[𝓝[≠] l] fun z ↦ L'.weierstrassPExcept 0 z + 1 / z ^ 2 := by
    filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds l),
      nhdsWithin_le_nhds (L'.isClosed_lattice.isOpen_compl.mem_nhds hl'), self_mem_nhdsWithin]
      with z h₁ (h₂ : z ∉ L'.lattice) (h₃ : z ≠ l)
    rw [hP, heq fun ⟨h, _⟩ ↦ h.elim (fun h ↦ h₁ ⟨h, h₃⟩) h₂]
  have hcont : ContinuousAt (fun z ↦ L'.weierstrassPExcept 0 z + 1 / z ^ 2) l := by
    have := (L'.analyticOnNhd_weierstrassPExcept 0 l (by simp [hl'])).continuousAt
    fun_prop (disch := simp [hl0])
  have := (tendsto_nhds_iff_meromorphicOrderAt_nonneg (L.meromorphic_weierstrassP l)).mp
    ⟨_, (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm⟩
  rw [L.order_weierstrassP l hl] at this
  exact absurd this (by decide)

/-- **The Weierstrass curve of a lattice determines the lattice.** -/
theorem weierstrassCurve_eq_iff {L L' : PeriodPair} :
    L.weierstrassCurve = L'.weierstrassCurve ↔ L.lattice = L'.lattice :=
  ⟨fun h ↦ lattice_eq_of_g₂_eq_of_g₃_eq (by simpa using congrArg WeierstrassCurve.a₄ h)
    (by simpa using congrArg WeierstrassCurve.a₆ h), weierstrassCurve_eq_of_lattice_eq⟩

/-- Equal `j`-invariants give a rescaling `g₂' = μ⁴ g₂`, `g₃' = μ⁶ g₃`. -/
private lemma exists_g₂_eq_mul_of_weierstrassCurve_j_eq {L L' : PeriodPair}
    (h : L.weierstrassCurve.j = L'.weierstrassCurve.j) :
    ∃ μ : ℂ, μ ≠ 0 ∧ L'.g₂ = L.g₂ * μ ^ 4 ∧ L'.g₃ = L.g₃ * μ ^ 6 := by
  have hΔ := L.weierstrassCurve_Δ_ne_zero
  have hΔ' := L'.weierstrassCurve_Δ_ne_zero
  rw [weierstrassCurve_Δ] at hΔ hΔ'
  rw [weierstrassCurve_j, weierstrassCurve_j, div_eq_div_iff hΔ hΔ'] at h
  have hrel : L.g₂ ^ 3 * L'.g₃ ^ 2 = L'.g₂ ^ 3 * L.g₃ ^ 2 := by linear_combination -h / 46656
  by_cases h₂ : L.g₂ = 0
  · have h₃ : L.g₃ ≠ 0 := by rintro h₃; simp [h₂, h₃] at hΔ
    have h₂' : L'.g₂ = 0 := by simpa [h₂, h₃] using hrel.symm
    have h₃' : L'.g₃ ≠ 0 := by rintro h₃'; simp [h₂', h₃'] at hΔ'
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (L'.g₃ / L.g₃) (by norm_num : 0 < 6)
    refine ⟨μ, fun h0 ↦ div_ne_zero h₃' h₃ ?_, by simp [h₂, h₂'], by rw [hμ]; field⟩
    rw [← hμ, h0, zero_pow (by norm_num)]
  by_cases h₃ : L.g₃ = 0
  · have h₃' : L'.g₃ = 0 := by simpa [h₂, h₃] using hrel
    have h₂' : L'.g₂ ≠ 0 := by rintro h₂'; simp [h₂', h₃'] at hΔ'
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (L'.g₂ / L.g₂) (by norm_num : 0 < 4)
    refine ⟨μ, fun h0 ↦ div_ne_zero h₂' h₂ ?_, by rw [hμ]; field, by simp [h₃, h₃']⟩
    rw [← hμ, h0, zero_pow (by norm_num)]
  have h₂' : L'.g₂ ≠ 0 := by
    rintro h₂'
    have : L'.g₃ = 0 := by simpa [h₂, h₂'] using hrel
    simp [h₂', this] at hΔ'
  have h₃' : L'.g₃ ≠ 0 := by
    rintro h₃'
    simp [h₃', h₂', h₃] at hrel
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (L'.g₃ * L.g₂ / (L.g₃ * L'.g₂))
    (by norm_num : 0 < 2)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact div_ne_zero (mul_ne_zero h₃' h₂) (mul_ne_zero h₃ h₂') (by rw [← hμ, zero_pow two_ne_zero])
  refine ⟨μ, hμ0, ?_, ?_⟩
  · rw [show μ ^ 4 = (μ ^ 2) ^ 2 by ring, hμ]
    field_simp
    linear_combination -hrel
  · rw [show μ ^ 6 = (μ ^ 2) ^ 3 by ring, hμ]
    field_simp
    linear_combination -hrel

/-- **Lattices with the same `j`-invariant are homothetic.** -/
theorem exists_lattice_eq_smul_of_weierstrassCurve_j_eq {L L' : PeriodPair}
    (h : L.weierstrassCurve.j = L'.weierstrassCurve.j) :
    ∃ c : ℂˣ, L'.lattice = (c • L).lattice := by
  obtain ⟨μ, hμ, h₂, h₃⟩ := exists_g₂_eq_mul_of_weierstrassCurve_j_eq h
  refine ⟨(Units.mk0 μ hμ)⁻¹, lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_⟩
  · simp [g₂_smul, h₂]
  · simp [g₃_smul, h₃]

/-- **The `j`-invariant classifies lattices up to homothety.** -/
theorem weierstrassCurve_j_eq_iff {L L' : PeriodPair} :
    L.weierstrassCurve.j = L'.weierstrassCurve.j ↔ ∃ c : ℂˣ, L'.lattice = (c • L).lattice :=
  ⟨exists_lattice_eq_smul_of_weierstrassCurve_j_eq, fun ⟨c, hc⟩ ↦
    (weierstrassCurve_j_eq_of_lattice_eq_smul c hc).symm⟩

end PeriodPair
