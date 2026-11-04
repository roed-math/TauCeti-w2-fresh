/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.SmoothTriangulation.Basic

set_option warningAsError false

/-!
# Lookahead stubs for `smooth-implies-pl`

These are lookahead stubs for the GeometricTopology supplier `smooth-implies-pl` (the
smoothing-and-triangulation comparison, item 1: every smooth manifold has a smooth triangulation,
Munkres, *Elementary Differential Topology*, Theorem 10.6). They are to be replaced by the landed
declarations. Only the existence statements consumed by `compact-manifold-finite-cw-type` are
stated: a boundaryless manifold has a `Cⁿ` triangulation, and a manifold modelled on the closed
half-space has one in which the manifold boundary is the polyhedron of a subcomplex.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

/-- **Whitehead's triangulation theorem** (Munkres, Theorem 10.6, boundaryless case): every
Hausdorff second-countable `Cⁿ` manifold without boundary, `1 ≤ n`, has a `Cⁿ` triangulation. -/
theorem exists_isSmoothTriangulation [I.Boundaryless] [T2Space M] [SecondCountableTopology M]
    {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M] :
    ∃ (ι : Type u) (K : AbstractSimplicialComplex ι)
      (f : AbstractSimplicialComplex.Realization K ≃ₜ M), IsSmoothTriangulation I n f := by
  sorry

/-- **Whitehead's triangulation theorem with boundary** (Munkres, Theorem 10.6, bounded case):
every Hausdorff second-countable `Cⁿ` manifold modelled on the closed half-space, `1 ≤ n`, has a
`Cⁿ` triangulation in which the manifold boundary is the polyhedron of a subcomplex. -/
theorem exists_isSmoothTriangulation_boundary {d : ℕ} [NeZero d] {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace d) M] [T2Space M]
    [SecondCountableTopology M] {n : ℕ∞} (hn : 1 ≤ n) [IsManifold (𝓡∂ d) n M] :
    ∃ (ι : Type u) (K : AbstractSimplicialComplex ι)
      (f : AbstractSimplicialComplex.Realization K ≃ₜ M) (L : PreAbstractSimplicialComplex ι),
      IsSmoothTriangulation (𝓡∂ d) n f ∧
        ∀ x, f x ∈ (𝓡∂ d).boundary M ↔ x.1.support ∈ L := by
  sorry

end TauCeti
