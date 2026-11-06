/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Splitting smooth Čech cocycles with a partition of unity

Let `U : ι → Set M` be an open cover of a Hausdorff σ-compact finite-dimensional real manifold
and let `ξ i j` be functions which are `C^n` on `U i ∩ U j` and satisfy the cocycle relation
`ξ i j + ξ j k = ξ i k` on `U i ∩ U j ∩ U k`. Then there are functions `g i`, `C^n` on `U i`,
with `ξ i j = g j - g i` on `U i ∩ U j`
(`TauCeti.exists_contMDiffOn_eq_sub_of_cocycle`): for a smooth partition of unity `ρ`
subordinate to `U`, take `g i = ∑ᶠ k, ρ k • ξ k i`. Being a convex combination, this splitting
is bounded by any common bound of the `ξ k i`.

This is the explicit form of the vanishing of degree one Čech cohomology of sheaves of smooth
functions, used to split a holomorphic cocycle on a Riemann surface into smooth functions before
solving the `\bar∂`-equation (Forster, *Lectures on Riemann Surfaces*, 14.7).

## References

* O. Forster, *Lectures on Riemann Surfaces*, §14.
-/

public section

open Set Function

open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞}

namespace SmoothPartitionOfUnity

variable {s : Set M} {ρ : SmoothPartitionOfUnity ι I M s} {U : ι → Set M}

/-- For a partition of unity `ρ` subordinate to `U` and a family `ξ i j` of functions that are
`C^n` on `U i ∩ U j`, the function `∑ᶠ k, ρ k • ξ k i` is `C^n` on `U i`. -/
theorem contMDiffOn_finsum_smul_of_isSubordinate (hρ : ρ.IsSubordinate U)
    (hUo : ∀ i, IsOpen (U i)) {ξ : ι → ι → M → F}
    (hξ : ∀ i j, ContMDiffOn I 𝓘(ℝ, F) n (ξ i j) (U i ∩ U j)) (i : ι) :
    ContMDiffOn I 𝓘(ℝ, F) n (fun x ↦ ∑ᶠ k, ρ k x • ξ k i x) (U i) := fun _ hx ↦
  (ρ.contMDiffAt_finsum fun k hk ↦ (hξ k i).contMDiffAt
    (((hUo k).inter (hUo i)).mem_nhds ⟨hρ k hk, hx⟩)).contMDiffWithinAt

/-- For a partition of unity `ρ` of `s` subordinate to `U` and a family `ξ i j` satisfying the
cocycle relation `ξ k i + ξ i j = ξ k j` on triple intersections, the functions
`g i = ∑ᶠ k, ρ k • ξ k i` satisfy `ξ i j = g j - g i` on `s ∩ U i ∩ U j`. -/
theorem eq_finsum_smul_sub_finsum_smul_of_isSubordinate (hρ : ρ.IsSubordinate U)
    {ξ : ι → ι → M → F}
    (hcocycle : ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, ξ i j x + ξ j k x = ξ i k x) {i j : ι} {x : M}
    (hxs : x ∈ s) (hx : x ∈ U i ∩ U j) :
    ξ i j x = (∑ᶠ k, ρ k x • ξ k j x) - ∑ᶠ k, ρ k x • ξ k i x := by
  have hfin : (support fun k ↦ ρ k x).Finite := ρ.locallyFinite.point_finite x
  have hfin' (l : ι) : (support fun k ↦ ρ k x • ξ k l x).Finite :=
    hfin.subset fun k hk ↦ left_ne_zero_of_smul hk
  rw [← finsum_sub_distrib (hfin' j) (hfin' i)]
  have hterm : ∀ k, ρ k x • ξ k j x - ρ k x • ξ k i x = ρ k x • ξ i j x := fun k ↦ by
    by_cases hk : ρ k x = 0
    · simp [hk]
    · have hxk : x ∈ U k := hρ k (subset_tsupport _ hk)
      rw [← smul_sub, ← hcocycle k i j x ⟨⟨hxk, hx.1⟩, hx.2⟩, add_sub_cancel_left]
  simp_rw [hterm, ← finsum_smul, ρ.sum_eq_one hxs, one_smul]

/-- For a partition of unity `ρ` of `s` subordinate to `U`, if `‖ξ k i‖ ≤ C` on every
`U k ∩ U i`, then `‖∑ᶠ k, ρ k • ξ k i‖ ≤ C` on `s ∩ U i`. -/
theorem norm_finsum_smul_le_of_isSubordinate (hρ : ρ.IsSubordinate U) {ξ : ι → ι → M → F}
    {i : ι} {C : ℝ} (hC : ∀ k, ∀ x ∈ U k ∩ U i, ‖ξ k i x‖ ≤ C) {x : M} (hxs : x ∈ s)
    (hx : x ∈ U i) : ‖∑ᶠ k, ρ k x • ξ k i x‖ ≤ C :=
  mem_closedBall_zero_iff.1 <| ρ.finsum_smul_mem_convex hxs
    (fun k hk ↦ mem_closedBall_zero_iff.2 (hC k x ⟨hρ k (subset_tsupport _ hk), hx⟩))
    (convex_closedBall 0 C)

end SmoothPartitionOfUnity

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

/-- **Smooth Čech `1`-cocycles split.** On a Hausdorff σ-compact finite-dimensional real manifold,
if `U` is an open cover and `ξ i j` is `C^n` on `U i ∩ U j` with `ξ i j + ξ j k = ξ i k` on
`U i ∩ U j ∩ U k`, then there are functions `g i`, `C^n` on `U i`, with `ξ i j = g j - g i` on
`U i ∩ U j`. Moreover `‖g i‖ ≤ C` on `U i` whenever `‖ξ k i‖ ≤ C` on every `U k ∩ U i`. -/
theorem exists_contMDiffOn_eq_sub_of_cocycle {U : ι → Set M} (hUo : ∀ i, IsOpen (U i))
    (hU : ⋃ i, U i = univ) {ξ : ι → ι → M → F}
    (hξ : ∀ i j, ContMDiffOn I 𝓘(ℝ, F) n (ξ i j) (U i ∩ U j))
    (hcocycle : ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, ξ i j x + ξ j k x = ξ i k x) :
    ∃ g : ι → M → F, (∀ i, ContMDiffOn I 𝓘(ℝ, F) n (g i) (U i)) ∧
      (∀ i j, ∀ x ∈ U i ∩ U j, ξ i j x = g j x - g i x) ∧
      ∀ i C, (∀ k, ∀ x ∈ U k ∩ U i, ‖ξ k i x‖ ≤ C) → ∀ x ∈ U i, ‖g i x‖ ≤ C := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ U hUo hU.ge
  exact ⟨fun i x ↦ ∑ᶠ k, ρ k x • ξ k i x,
    SmoothPartitionOfUnity.contMDiffOn_finsum_smul_of_isSubordinate hρ hUo hξ,
    fun i j x hx ↦
      SmoothPartitionOfUnity.eq_finsum_smul_sub_finsum_smul_of_isSubordinate hρ hcocycle
        (mem_univ x) hx,
    fun _ _ hC x hx ↦
      SmoothPartitionOfUnity.norm_finsum_smul_le_of_isSubordinate hρ hC (mem_univ x) hx⟩

end TauCeti
