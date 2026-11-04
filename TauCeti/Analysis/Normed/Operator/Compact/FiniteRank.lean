/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.FiniteRange
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Basic

/-!
# Compact operators and operators of finite rank

A continuous linear map `T : E →L[𝕜] F` with finite-dimensional range is compact whenever
`F` is a topological vector space over a locally compact nontrivially normed field. It factors
through its range, which is locally compact. No norm or compatibility between the topology and
module structure on `E` is needed.

In particular, operator-norm limits of finite-rank maps into a Banach space are compact, by
`isCompactOperator_of_tendsto`.

Conversely, a compact operator `K` between seminormed spaces is approximately of finite rank in a
relative sense: for every `ε > 0`, each `K x` lies within `ε * ‖x‖` of a fixed finite-dimensional
subspace, at a point of norm `O(‖x‖)`. The subspace is spanned by a finite net of the image of the
unit ball. This is the form in which compactness enters perturbation arguments such as Schwartz's
theorem on compact perturbations of surjections.

Finiteness of the rank is spelled with Mathlib's `LinearMap.HasFiniteRange`.

## Main declarations

* `LinearMap.HasFiniteRange.isCompactOperator`: over a locally compact nontrivially normed field, a
  continuous linear map of finite rank is a compact operator.
* `IsCompactOperator.exists_finiteDimensional_dist_le`: a compact operator is approximately of
  finite rank, with relative error as small as desired.

## Mathlib sources

Scalar completeness and finite-dimensional local compactness come from
`IsLeftUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace` and
`LocallyCompactSpace.of_finiteDimensional_of_complete`, respectively. Compactness of maps into
the range is provided by `isCompactOperator_of_locallyCompactSpace_dom`.
-/

public section

section FiniteRange

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜 F]

/-- Over a locally compact nontrivially normed field, a continuous linear map into a topological
vector space with finite-dimensional range is a compact operator. -/
theorem LinearMap.HasFiniteRange.isCompactOperator {T : E →L[𝕜] F}
    (hT : (T : E →ₗ[𝕜] F).HasFiniteRange) : IsCompactOperator T := by
  have : CompleteSpace 𝕜 :=
    IsLeftUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace 𝕜
  have : FiniteDimensional 𝕜 T.range := .of_fg hT
  have : LocallyCompactSpace T.range :=
    .of_finiteDimensional_of_complete 𝕜 _
  simpa only [← ContinuousLinearMap.coe_comp, ContinuousLinearMap.subtypeL_comp_codRestrict] using
    (isCompactOperator_of_locallyCompactSpace_dom T.rangeRestrict).clm_comp T.range.subtypeL

end FiniteRange

section FiniteRankApproximation

open Metric Set

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A compact operator is approximately of finite rank: for every `ε > 0` there are a
finite-dimensional subspace `B` and a constant `M` such that each `K x` lies within `ε * ‖x‖` of
a point of `B` of norm at most `M * ‖x‖`. -/
theorem IsCompactOperator.exists_finiteDimensional_dist_le {K : E →L[𝕜] F}
    (hK : IsCompactOperator K) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : Submodule 𝕜 F, FiniteDimensional 𝕜 B ∧ ∃ M, ∀ x, ∃ b ∈ B,
      dist (K x) b ≤ ε * ‖x‖ ∧ ‖b‖ ≤ M * ‖x‖ := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hc0 : 0 < ‖c‖ := one_pos.trans hc
  -- `B` is spanned by a finite `ε / ‖c‖`-net `t` of the image of the unit ball.
  obtain ⟨t, htK, ht, hnet⟩ := finite_approx_of_totallyBounded
    (hK.totallyBounded_image_closedBall 1) (ε / ‖c‖) (by positivity)
  refine ⟨Submodule.span 𝕜 t, FiniteDimensional.span_of_finite 𝕜 ht, ‖c‖ * ‖K‖, fun x ↦ ?_⟩
  by_cases hx : ‖x‖ = 0
  · refine ⟨0, zero_mem _, ?_, by simp [hx]⟩
    rw [dist_zero_right, hx, mul_zero]
    exact (K.le_opNorm x).trans (by simp [hx])
  -- Rescale `x` into the unit ball, approximate its image there, and scale back.
  obtain ⟨d, hd0, hdx, -, hdinv⟩ := rescale_to_shell_semi_normed hc one_pos hx
  have hdinv' : ‖d‖⁻¹ ≤ ‖c‖ * ‖x‖ := by simpa using hdinv
  obtain ⟨b, hbt, hb⟩ : ∃ b ∈ t, dist (K (d • x)) b < ε / ‖c‖ := by
    have := hnet ⟨d • x, mem_closedBall_zero_iff.2 hdx.le, rfl⟩
    simp only [mem_iUnion₂, mem_ball, exists_prop] at this
    exact this
  refine ⟨d⁻¹ • b, Submodule.smul_mem _ _ (Submodule.subset_span hbt), ?_, ?_⟩
  · have hsub : K x - d⁻¹ • b = d⁻¹ • (K (d • x) - b) := by
      rw [map_smul, smul_sub, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [dist_eq_norm, hsub, norm_smul, norm_inv, ← dist_eq_norm]
    calc ‖d‖⁻¹ * dist (K (d • x)) b ≤ (‖c‖ * ‖x‖) * (ε / ‖c‖) :=
          mul_le_mul hdinv' hb.le dist_nonneg (by positivity)
      _ = ε * ‖x‖ := by field_simp
  · have hbK : ‖b‖ ≤ ‖K‖ := by
      obtain ⟨z, hz, rfl⟩ := htK hbt
      exact (K.le_opNorm z).trans
        (mul_le_of_le_one_right (norm_nonneg _) (mem_closedBall_zero_iff.1 hz))
    rw [norm_smul, norm_inv]
    calc ‖d‖⁻¹ * ‖b‖ ≤ (‖c‖ * ‖x‖) * ‖K‖ :=
          mul_le_mul hdinv' hbK (norm_nonneg _) (by positivity)
      _ = ‖c‖ * ‖K‖ * ‖x‖ := by ring

end FiniteRankApproximation

end
