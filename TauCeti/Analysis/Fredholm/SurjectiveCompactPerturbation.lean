/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Fredholm.ClosedRange
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Normed.Operator.Compact.FiniteRank

/-!
# Compact perturbations of surjective operators

Let `T : E → F` be a surjective continuous linear map between Banach spaces and `K : E → F` a
compact operator. Then the range of `T + K` has finite codimension, and is therefore closed.
This is **Schwartz's theorem**, the functional-analytic core of the Cartan–Serre finiteness
theorem for the cohomology of coherent analytic sheaves on compact complex spaces, and of the
proof of `dim H¹(X, 𝒪) < ∞` for compact Riemann surfaces.

Unlike the compact-perturbation theorem for Fredholm operators
(`ContinuousLinearMap.IsFredholm.add_of_isCompactOperator`), no condition is put on the kernel of
`T`: in the cohomological application the kernel of `T` is infinite dimensional, and the kernel
of `T` need not be complemented.

## The argument

The proof is the iteration in Forster's proof of the finiteness of `H¹(X, 𝒪)`. The open mapping
theorem lifts every `y` to some `x` with `T x = y` and `‖x‖ ≤ C * ‖y‖`. As `K` is compact, it
is approximately of finite rank (`IsCompactOperator.exists_finiteDimensional_dist_le`): there is
a finite-dimensional subspace `B` such that `K x` lies within `‖y‖ / 2` of a point of `B` of norm
`O(‖y‖)`. So `y` lies within `‖y‖ / 2` of the image of a point of controlled norm under
`(x, b) ↦ (T + K) x + b` on `E × B`. Iterating
(`ContinuousLinearMap.exists_preimage_norm_le_of_approx`), this map is surjective, so `B`
spans the cokernel of `T + K`.

## Main results

* `ContinuousLinearMap.finiteDimensional_quotient_range_add_of_surjective`: the cokernel of a
  compact perturbation of a surjective operator is finite dimensional.
* `ContinuousLinearMap.isClosed_range_add_of_surjective`: its range is closed.
* `ContinuousLinearMap.finiteDimensional_quotient_range_of_surjective_coprod`: if
  `(g, e) ↦ r g + δ e` is surjective and `r` is compact, the cokernel of `δ` is finite
  dimensional. This is the form used for Čech cohomology, with `δ` the coboundary and `r` a
  restriction of cocycles to a relatively compact refinement.
* `ContinuousLinearMap.isClosed_range_of_surjective_coprod`: the range of `δ` is then closed.

## References

* L. Schwartz, *Homomorphismes et applications complètement continues*, C. R. Acad. Sci. Paris
  237 (1953), 1355–1357.
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer,
  1981, §14 (Lemma 14.8 and Theorem 14.9).
* H. Grauert, R. Remmert, *Coherent Analytic Sheaves*, Springer, 1984, Chapter 6, §1.
-/

public section

open Function Metric Module Set

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

/-- **Schwartz's theorem.** A compact perturbation of a surjective continuous linear map between
Banach spaces has finite-dimensional cokernel. -/
theorem finiteDimensional_quotient_range_add_of_surjective {T K : E →L[𝕜] F}
    (hT : Surjective T) (hK : IsCompactOperator K) :
    FiniteDimensional 𝕜 (F ⧸ LinearMap.range ((T + K : E →L[𝕜] F) : E →ₗ[𝕜] F)) := by
  -- Lifts of norm at most `C` times the norm, and approximations of `K` with relative error
  -- `1 / (2 * C)` from a finite-dimensional subspace `B`.
  obtain ⟨C, hC0, hC⟩ := T.exists_preimage_norm_le hT
  obtain ⟨B, hB, M, hM⟩ := hK.exists_finiteDimensional_dist_le (ε := (2 * C)⁻¹) (by positivity)
  have : CompleteSpace B := FiniteDimensional.complete 𝕜 B
  -- Every `y` is within `‖y‖ / 2` of the image of a point of norm `O(‖y‖)` under
  -- `S (x, b) = (T + K) x + b`.
  set S : (E × B) →L[𝕜] F := (T + K).coprod B.subtypeL with hS
  have happrox : ∀ y, ∃ p, dist (S p) y ≤ 1 / 2 * ‖y‖ ∧ ‖p‖ ≤ (C * (1 + |M|)) * ‖y‖ := by
    intro y
    obtain ⟨x, rfl, hx⟩ := hC y
    obtain ⟨b, hbB, hb, hbM⟩ := hM x
    refine ⟨(x, -⟨b, hbB⟩), ?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
    · rw [dist_eq_norm, show S (x, -⟨b, hbB⟩) - T x = K x - b by simp [hS]; abel,
        ← dist_eq_norm]
      calc dist (K x) b ≤ (2 * C)⁻¹ * (C * ‖T x‖) := hb.trans (by gcongr)
        _ = 1 / 2 * ‖T x‖ := by field_simp
    · calc ‖x‖ ≤ C * ‖T x‖ := hx
        _ ≤ C * (1 + |M|) * ‖T x‖ := by
          rw [mul_right_comm]
          exact le_mul_of_one_le_right (by positivity) (by simp)
    · calc ‖-(⟨b, hbB⟩ : B)‖ = ‖b‖ := by simp
        _ ≤ |M| * ‖x‖ := hbM.trans (by gcongr; exact le_abs_self M)
        _ ≤ |M| * (C * ‖T x‖) := by gcongr
        _ ≤ C * (1 + |M|) * ‖T x‖ := by nlinarith [abs_nonneg M, norm_nonneg (T x)]
  -- Hence `S` is onto, so `B` maps onto the cokernel of `T + K`.
  refine FiniteDimensional.of_surjective
    ((LinearMap.range ((T + K : E →L[𝕜] F) : E →ₗ[𝕜] F)).mkQ ∘ₗ B.subtype) fun q ↦ ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨⟨x, b⟩, hxb, -⟩ := S.exists_preimage_norm_le_of_approx happrox y
  refine ⟨b, (Submodule.Quotient.eq _).2 ⟨-x, ?_⟩⟩
  rw [← hxb]
  simp [hS]
  abel

/-- A compact perturbation of a surjective continuous linear map between Banach spaces has
closed range. -/
theorem isClosed_range_add_of_surjective {T K : E →L[𝕜] F} (hT : Surjective T)
    (hK : IsCompactOperator K) :
    IsClosed (LinearMap.range ((T + K : E →L[𝕜] F) : E →ₗ[𝕜] F) : Set F) := by
  have := finiteDimensional_quotient_range_add_of_surjective hT hK
  exact (T + K).isClosed_range_of_finite_coker

/-- If every `y` is of the form `r g + δ e` with `r` compact, then the cokernel of `δ` is
finite dimensional. In the application to Čech cohomology, `δ` is the coboundary of cochains,
`r` restricts cocycles to a relatively compact refinement, and surjectivity says that every
cocycle on the refinement is cohomologous to a restricted one. -/
theorem finiteDimensional_quotient_range_of_surjective_coprod {r : G →L[𝕜] F}
    {δ : E →L[𝕜] F} (hr : IsCompactOperator r) (h : Surjective (r.coprod δ)) :
    FiniteDimensional 𝕜 (F ⧸ LinearMap.range (δ : E →ₗ[𝕜] F)) := by
  have hK : IsCompactOperator (-(r.comp (fst 𝕜 G E))) :=
    (hr.comp_clm (fst 𝕜 G E)).neg
  have hrange : LinearMap.range ((r.coprod δ + -(r.comp (fst 𝕜 G E)) : G × E →L[𝕜] F) :
      G × E →ₗ[𝕜] F) = LinearMap.range (δ : E →ₗ[𝕜] F) := by
    have heq : ((r.coprod δ + -(r.comp (fst 𝕜 G E)) : G × E →L[𝕜] F) : G × E →ₗ[𝕜] F) =
        (δ : E →ₗ[𝕜] F) ∘ₗ LinearMap.snd 𝕜 G E := by
      ext p <;> simp
    rw [heq, LinearMap.range_comp_of_range_eq_top _ (Submodule.range_snd ..)]
  have := finiteDimensional_quotient_range_add_of_surjective h hK
  exact (Submodule.quotEquivOfEq _ _ hrange).finiteDimensional

/-- If every `y` is of the form `r g + δ e` with `r` compact, then the range of `δ` is
closed. -/
theorem isClosed_range_of_surjective_coprod {r : G →L[𝕜] F} {δ : E →L[𝕜] F}
    (hr : IsCompactOperator r) (h : Surjective (r.coprod δ)) :
    IsClosed (LinearMap.range (δ : E →ₗ[𝕜] F) : Set F) := by
  have := finiteDimensional_quotient_range_of_surjective_coprod hr h
  exact δ.isClosed_range_of_finite_coker

end ContinuousLinearMap
