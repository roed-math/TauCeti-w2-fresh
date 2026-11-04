/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Lookahead.CompactManifoldFiniteCwType.Stubs
public import TauCeti.Geometry.Manifold.SmoothTriangulation.Dimension
public import TauCeti.Topology.Triangulable.FiniteCWType
public import TauCeti.Topology.Triangulable.LocallyFiniteCWType

/-!
# Smooth manifolds have countable locally finite CW type

Every finite-dimensional Hausdorff second-countable smooth manifold, with the Euclidean model or
with the half-space model and possibly nonempty boundary, is homeomorphic to a countable, locally
finite, finite-dimensional CW complex; a compact one to a finite CW complex. Hence it has
countable locally finite CW type, and finite CW type when compact.

The proof consumes Whitehead's theorem that a smooth manifold has a smooth triangulation
(`TauCeti.exists_isSmoothTriangulation`, `TauCeti.exists_isSmoothTriangulation_boundary`) through
its realization homeomorphism `f : |K| ≃ₜ M`, and then argues purely topologically:

* a manifold is locally compact and σ-compact, so the triangulating complex is locally finite
  and has countably many vertices, and finitely many when the manifold is compact
  (`AbstractSimplicialComplex.exists_cwComplex_of_triangulation`,
  `TauCeti.IsTriangulable.finiteCWType`);
* the immersion condition on simplices bounds their dimension by that of the manifold
  (`TauCeti.IsSmoothTriangulation.card_le`);
* the simplicial CW structure `AbstractSimplicialComplex.realizationCWComplex` is then countable,
  locally finite and finite-dimensional, and finite in the compact case.

The boundary of a manifold with boundary is the polyhedron of a subcomplex, which gives the
boundary-pair forms: `(M, ∂M)` is homeomorphic to a CW pair. Finitely many prescribed points,
for instance interior marked points outside the boundary subcomplex, are made into `0`-cells
by sliding each to the barycenter of its open simplex and subdividing
(`AbstractSimplicialComplex.exists_barycentricSubdivision_homeomorph_vertex`); this keeps the
boundary a subcomplex.

## Main results

* `TauCeti.exists_cwComplex_of_isManifold` and
  `TauCeti.exists_cwComplex_boundary_of_isManifold_euclideanHalfSpace`: the CW models of a
  boundaryless manifold and of a manifold with boundary, the latter as a CW pair `(M, ∂M)`.
* `TauCeti.countableLocallyFiniteCWType_of_isManifold`,
  `TauCeti.countableLocallyFiniteCWType_of_isManifold_euclideanHalfSpace`: countable locally
  finite CW type.
* `TauCeti.finiteCWType_of_isManifold`, `TauCeti.finiteCWType_of_isManifold_euclideanHalfSpace`:
  compact manifolds have finite CW type.

## References

* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Theorem 10.6.
* A. Hatcher, *Algebraic Topology*, Chapter 0 and Appendix A.
-/

public section

noncomputable section

open Set Module Topology Topology.RelCWComplex AbstractSimplicialComplex TauCeti.SetLike
open scoped Manifold ContDiff

namespace TauCeti

universe u

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SecondCountableTopology M]

/-- **Smooth manifolds are countable locally finite CW complexes.** A Hausdorff
second-countable smooth manifold without boundary, modelled on a finite-dimensional space `E`, is
homeomorphic to a CW complex with countably many cells, a locally finite family of closed cells
and no cells above dimension `finrank ℝ E`, which is finite when the manifold is compact; any
finite set of points can be taken to be `0`-cells. -/
theorem exists_cwComplex_of_isManifold [I.Boundaryless] [IsManifold I ∞ M] (S : Finset M) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (C : Set Y) (_ : CWComplex C)
      (e : M ≃ₜ C),
      (∀ n, Countable (cell C n)) ∧ LocallyFinite (fun c : Σ n, cell C n => closedCell c.1 c.2) ∧
      (∀ n, finrank ℝ E < n → IsEmpty (cell C n)) ∧ (CompactSpace M → RelCWComplex.Finite C) ∧
      ∀ p ∈ S, ∃ c : cell C 0, openCell 0 c = {(e p : Y)} := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨ι, K, f, hf⟩ := exists_isSmoothTriangulation (I := I) (M := M) (n := ⊤) le_top
  obtain ⟨Y, _, _, C, _, -, e, hcount, hfin, hdim, hC, -, hS⟩ :=
    K.exists_cwComplex_of_triangulation f univ K.toPreAbstractSimplicialComplex
      (fun x => iff_of_true (mem_univ _) (K.support_mem x)) S
  exact ⟨Y, _, ‹_›, C, ‹_›, e, hcount, hfin, hdim _ fun σ hσ => hf.card_le hσ, hC, hS⟩

/-- A Hausdorff second-countable smooth manifold without boundary, modelled on a
finite-dimensional space, has countable locally finite CW type. -/
theorem countableLocallyFiniteCWType_of_isManifold [I.Boundaryless] [IsManifold I ∞ M] :
    CountableLocallyFiniteCWType M :=
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  have ⟨ι, K, f, _⟩ := exists_isSmoothTriangulation (I := I) (M := M) (n := ⊤) le_top
  IsTriangulable.countableLocallyFiniteCWType ((isTriangulable_iff M).mpr ⟨ι, K, ⟨f⟩⟩)

/-- **A compact smooth manifold has finite CW type.** A compact Hausdorff second-countable
smooth manifold without boundary, modelled on a finite-dimensional space, is homotopy equivalent,
indeed homeomorphic, to a finite CW complex. -/
theorem finiteCWType_of_isManifold [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] :
    FiniteCWType M :=
  have ⟨ι, K, f, _⟩ := exists_isSmoothTriangulation (I := I) (M := M) (n := ⊤) le_top
  IsTriangulable.finiteCWType.{u, u} ((isTriangulable_iff M).mpr ⟨ι, K, ⟨f⟩⟩)

end Manifold

section HalfSpace

variable {d : ℕ} [NeZero d] {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace d) M] [T2Space M] [SecondCountableTopology M]
  [IsManifold (𝓡∂ d) ∞ M]

/-- **Smooth manifolds with boundary are countable locally finite CW pairs.** A Hausdorff
second-countable smooth `d`-manifold with boundary, modelled on the closed half-space, is
homeomorphic to a CW complex with countably many cells, a locally finite family of closed cells
and no cells above dimension `d`, which is finite when the manifold is compact, by a
homeomorphism carrying the manifold boundary onto a subcomplex. Any finite set of points, in
particular finitely many interior marked points outside the boundary subcomplex, can be taken
to be `0`-cells. -/
theorem exists_cwComplex_boundary_of_isManifold_euclideanHalfSpace (S : Finset M) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (C : Set Y) (_ : CWComplex C)
      (A : RelCWComplex.Subcomplex C) (e : M ≃ₜ C),
      (∀ n, Countable (cell C n)) ∧ LocallyFinite (fun c : Σ n, cell C n => closedCell c.1 c.2) ∧
      (∀ n, d < n → IsEmpty (cell C n)) ∧ (CompactSpace M → RelCWComplex.Finite C) ∧
      (∀ x, x ∈ (𝓡∂ d).boundary M ↔ (e x : Y) ∈ A) ∧
      ∀ p ∈ S, ∃ c : cell C 0, openCell 0 c = {(e p : Y)} := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (𝓡∂ d)
  obtain ⟨ι, K, f, L, hf, hL⟩ := exists_isSmoothTriangulation_boundary (d := d) (M := M)
    (n := ⊤) le_top
  obtain ⟨Y, _, _, C, _, A, e, hcount, hfin, hdim, hC, hA, hS⟩ :=
    K.exists_cwComplex_of_triangulation f _ L hL S
  exact ⟨Y, _, ‹_›, C, ‹_›, A, e, hcount, hfin,
    hdim _ fun σ hσ => (hf.card_le hσ).trans_eq (by rw [finrank_euclideanSpace_fin]), hC, hA, hS⟩

variable (d) in
include d in
/-- A Hausdorff second-countable smooth manifold with boundary, modelled on the closed
half-space, has countable locally finite CW type. -/
theorem countableLocallyFiniteCWType_of_isManifold_euclideanHalfSpace :
    CountableLocallyFiniteCWType M :=
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (𝓡∂ d)
  have ⟨ι, K, f, _⟩ := exists_isSmoothTriangulation_boundary (d := d) (M := M) (n := ⊤) le_top
  IsTriangulable.countableLocallyFiniteCWType ((isTriangulable_iff M).mpr ⟨ι, K, ⟨f⟩⟩)

variable (d) in
include d in
/-- **A compact smooth manifold with boundary has finite CW type.** -/
theorem finiteCWType_of_isManifold_euclideanHalfSpace [CompactSpace M] : FiniteCWType M :=
  have ⟨ι, K, f, _⟩ := exists_isSmoothTriangulation_boundary (d := d) (M := M) (n := ⊤) le_top
  IsTriangulable.finiteCWType.{u, u} ((isTriangulable_iff M).mpr ⟨ι, K, ⟨f⟩⟩)

end HalfSpace

end TauCeti
