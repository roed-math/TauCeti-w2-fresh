/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Basic

/-!
# Dimension of the simplices of a smooth triangulation

An immersion of a closed simplex into a manifold modelled on a finite-dimensional space `E` has
a derivative that is injective on the directions of the simplex, a space of dimension one less
than the number of vertices. Hence the simplex has at most `finrank ℝ E + 1` vertices, and every
face of a smooth triangulation of such a manifold has at most `finrank ℝ E + 1` vertices. This
bounds the dimension of the CW structure of the triangulation.

## Main results

* `TauCeti.IsSimplexImmersion.card_le`: an immersed simplex has at most `finrank ℝ E + 1`
  vertices.
* `TauCeti.IsSmoothTriangulation.card_le`: the faces of a smooth triangulation have at most
  `finrank ℝ E + 1` vertices.
-/

public section

open Module AbstractSimplicialComplex TauCeti.SetLike
open scoped Manifold

namespace TauCeti

variable {ι : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}

/-- A nonempty simplex immersed in a manifold modelled on `E` has at most `finrank ℝ E + 1`
vertices: its derivative is injective on the directions of the simplex. -/
theorem IsSimplexImmersion.card_le {σ : Finset ι} (hσ : σ.Nonempty)
    {g : StandardSimplex σ → M} (h : IsSimplexImmersion I n g) :
    σ.card ≤ finrank ℝ E + 1 := by
  obtain ⟨F, -, -, hF⟩ := isSimplexImmersion_iff.mp h
  have : Nonempty σ := hσ.to_subtype
  obtain ⟨t⟩ : Nonempty (Convexity.StdSimplex ℝ σ) := inferInstance
  obtain ⟨F', -, hinj⟩ := hF t
  let S : (σ → ℝ) →ₗ[ℝ] ℝ := ∑ a, LinearMap.proj a
  have hS (v : σ → ℝ) : S v = ∑ a, v a := by simp [S]
  have hV : Function.Injective ((F' : (σ → ℝ) →ₗ[ℝ] E).domRestrict (LinearMap.ker S)) := by
    rw [← LinearMap.ker_eq_bot]
    refine LinearMap.ker_eq_bot'.mpr fun v hv => Subtype.ext ?_
    rw [LinearMap.domRestrict_apply] at hv
    exact hinj v.1 ((hS v.1).symm.trans (LinearMap.mem_ker.mp v.2)) hv
  have h₁ := LinearMap.finrank_le_finrank_of_injective hV
  have h₂ := LinearMap.finrank_range_add_finrank_ker S
  have h₃ : finrank ℝ (LinearMap.range S) ≤ 1 :=
    (Submodule.finrank_le _).trans (finrank_self ℝ).le
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h₂
  omega

/-- Every face of a smooth triangulation of a manifold modelled on `E` has at most
`finrank ℝ E + 1` vertices. -/
theorem IsSmoothTriangulation.card_le {K : AbstractSimplicialComplex ι}
    {f : Realization K ≃ₜ M} (h : IsSmoothTriangulation I n f) {σ : Finset ι} (hσ : σ ∈ K) :
    σ.card ≤ finrank ℝ E + 1 :=
  (isSmoothTriangulation_iff.mp h ⟨σ, hσ⟩).card_le (K.isRelLowerSet_faces.prop_of_mem hσ)

end TauCeti
