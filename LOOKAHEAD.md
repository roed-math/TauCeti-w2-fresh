<!--tauceti-lookahead:v1 {"area":"AlgebraicTopology","slug":"compact-manifold-finite-cw-type","main":"7ed979dc2eacd36a3962e1fdf3b481323fb3fb8b","status":"complete","suppliers":["smooth-implies-pl"],"splits":[{"n":1,"after":[],"title":"feat: local finiteness and countability of simplicial realizations and their CW structures"},{"n":2,"after":[],"title":"feat: make prescribed points of a simplicial realization vertices"},{"n":3,"after":[1,2],"title":"feat: countable locally finite CW type of triangulated spaces"},{"n":4,"after":[1,2,3],"title":"feat: smooth manifolds have countable locally finite CW type"}]}-->

# Lookahead: `compact-manifold-finite-cw-type` (AlgebraicTopology, Stage 8, item 7)

Target (operator list): every finite-dimensional Hausdorff second-countable smooth manifold with
the Euclidean or half-space model, with or without boundary, has countable locally finite CW type,
by consuming GeometricTopology's smoothing-and-triangulation comparison item 1 and its realization
homeomorphism; the compact case has finite CW type; include the boundary-pair forms and finitely
many prescribed interior marked points outside the relative boundary locus.

Status: **complete** against the stubs below. Built on `main` at
`7ed979dc2eacd36a3962e1fdf3b481323fb3fb8b`. `lake build` is green and `lookahead-check` passes;
`sorry` occurs only in `TauCeti/Lookahead/CompactManifoldFiniteCwType/Stubs.lean`.

The README's further sentence in item 7 ("as a reusable corollary, a simply connected integral
homology `n`-sphere is homotopy equivalent to `S^n`") is not part of this operator-list target and
needs Stage 8 items 3–5 (Hurewicz, Whitehead), which are not on `main`; it is not attempted here.

## Exported theorems and the pinned form

`AlgebraicTopology/Suggested.lean` pins

```lean
structure FiniteCWTypeModel (M : Type u) [TopologicalSpace M] where
  X : Type u
  topology : TopologicalSpace X
  hausdorff : letI := topology; T2Space X
  cw : letI := topology; CWComplex (Set.univ : Set X)
  finite : letI := topology; letI := cw; CWComplex.Finite (Set.univ : Set X)
  homotopyEquiv : letI := topology; M ≃ₕ X

noncomputable def compactManifoldFiniteCWType (n : ℕ)
    (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M] :
    FiniteCWTypeModel M
```

Since that file was written, `main` gained `TauCeti.FiniteCWType` (`Topology/CWComplex/Classical/
FiniteCWType.lean`: a Hausdorff finite CW model in the same universe and a homotopy equivalence,
with `FiniteCWType.exists_homotopyEquiv_univ` recovering a model of the pinned `CWComplex univ`
shape) and its Euler characteristic `TauCeti.eulerChar` with model independence. Introducing
`FiniteCWTypeModel` would duplicate that API (reuse rubric), so the compact case is stated as
`TauCeti.finiteCWType_of_isManifold I : FiniteCWType M` (general boundaryless model on a
finite-dimensional space; `I := 𝓡 n` is the pinned case) and
`TauCeti.finiteCWType_of_isManifold_euclideanHalfSpace d`. FuchsianOrbifolds 5.1 then applies
`TauCeti.eulerChar` directly.

The full target is:

* `TauCeti.exists_cwComplex_of_isManifold I S` — a boundaryless manifold is homeomorphic to a CW
  complex with countably many cells, a locally finite family of closed cells, no cells above
  dimension `finrank ℝ E`, finite when `M` is compact, with every point of the finite set `S` a
  `0`-cell.
* `TauCeti.exists_cwComplex_boundary_of_isManifold_euclideanHalfSpace S` — the boundary-pair form:
  the same for a `𝓡∂ d` manifold, the homeomorphism carrying `(𝓡∂ d).boundary M` onto a CW
  subcomplex; `S` may be any finite set, in particular interior marked points outside the boundary
  subcomplex (the hypothesis "outside the boundary" is not needed).
* `TauCeti.countableLocallyFiniteCWType_of_isManifold I`,
  `TauCeti.countableLocallyFiniteCWType_of_isManifold_euclideanHalfSpace d` — countable locally
  finite CW type (new class `TauCeti.CountableLocallyFiniteCWType`).
* `TauCeti.finiteCWType_of_isManifold I`, `TauCeti.finiteCWType_of_isManifold_euclideanHalfSpace d`
  — compact manifolds have finite CW type.

## Stubbed declarations (supplier `smooth-implies-pl`)

Both live in `TauCeti/Lookahead/CompactManifoldFiniteCwType/Stubs.lean` and are used only by
`TauCeti/Geometry/Manifold/CWType.lean`.

**Source.** `GeometricTopology/Suggested.lean` pins **no** signature for this supplier (the file
says "no compiled targets yet"; it contains no declaration for the smoothing-and-triangulation
comparison). The open PR #27085 is a partial of the supplier: its diff adds only chart-local
inputs (`TauCeti.IsSimplexImmersion.comp_of_contMDiffOn`, `IsSimplexImmersion.extChartAt_comp`,
`TauCeti.isSimplexImmersion_extChartAt_comp_iff`,
`ModelWithCorners.IsInteriorPoint.exists_isSimplexImmersion_isClosedEmbedding_range_mem_nhds`) and
does not state the final existence theorem. The stubs are therefore stated from the GeometricTopology
README ("The smoothing-and-triangulation comparison", item 1, "Smooth implies PL": every smooth
manifold has a smooth triangulation, Whitehead), from the roadmap's Munkres extract
(`references/munkres-smoothing-triangulations.md`, Theorem 10.6), and from the predicate the
supplier already landed on `main`, `TauCeti.IsSmoothTriangulation I n f`
(`Geometry/Manifold/SmoothTriangulation/Basic.lean`, which states in its docstring that every
smooth manifold, with or without boundary, has one, Munkres 10.6).

Suggested.lean signature (verbatim): *none pinned*.

Stub 1 (Munkres 10.6, boundaryless case):

```lean
theorem exists_isSmoothTriangulation [I.Boundaryless] [T2Space M] [SecondCountableTopology M]
    {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M] :
    ∃ (ι : Type u) (K : AbstractSimplicialComplex ι)
      (f : AbstractSimplicialComplex.Realization K ≃ₜ M), IsSmoothTriangulation I n f
```

(with `E` finite-dimensional, `I : ModelWithCorners ℝ E H`, `M : Type u`).

Stub 2 (Munkres 10.6, bounded case):

```lean
theorem exists_isSmoothTriangulation_boundary {d : ℕ} [NeZero d] {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace d) M] [T2Space M]
    [SecondCountableTopology M] {n : ℕ∞} (hn : 1 ≤ n) [IsManifold (𝓡∂ d) n M] :
    ∃ (ι : Type u) (K : AbstractSimplicialComplex ι)
      (f : AbstractSimplicialComplex.Realization K ≃ₜ M) (L : PreAbstractSimplicialComplex ι),
      IsSmoothTriangulation (𝓡∂ d) n f ∧
        ∀ x, f x ∈ (𝓡∂ d).boundary M ↔ x.1.support ∈ L
```

Differences from the source statements, with reasons:

* Munkres' bounded case says that any `Cʳ` triangulation of `∂M` extends to one of `M`; the stub
  states only the consequence the target consumes, that `∂M` is the polyhedron of a subcomplex
  `L` (Mathlib has no manifold structure on `I.boundary M` to state the extension against).
* Class `1 ≤ n` with `n : ℕ∞` (so `n ≠ ω`), matching Munkres' `1 ≤ r ≤ ∞`.
* The vertex type lives in the universe of `M`; Munkres' complexes live in `ℝ^N`, so they are
  countable and can be relabelled into any universe.
* The boundaryless case is stated for every boundaryless model on a finite-dimensional space; the
  bounded case only for the half-space model `𝓡∂ d`, which is what the target needs (Euclidean or
  half-space model).
* Uniqueness (Munkres 10.5) is not stubbed: the target does not consume it.

When the supplier lands, replace `TauCeti.Lookahead.CompactManifoldFiniteCwType.Stubs` in the
import list of `TauCeti/Geometry/Manifold/CWType.lean` by the supplier's module, adapt the two
call sites `exists_isSmoothTriangulation (I := I) (M := M) (n := ⊤) le_top` and
`exists_isSmoothTriangulation_boundary (d := d) (M := M) (n := ⊤) le_top` to the landed names and
hypotheses, and delete `TauCeti/Lookahead/`. Only `IsSmoothTriangulation.card_le` (split 4) uses
the smoothness of the triangulation; everything else is topological.

## Split plan

All splits carry `Roadmap: AlgebraicTopology` (Stage 8 item 7).

1. **feat: local finiteness and countability of simplicial realizations and their CW structures**
   (after: none; ~256 lines).
   * `TauCeti/AlgebraicTopology/SimplicialComplex/Realization/Compact.lean` (edit):
     `AbstractSimplicialComplex.countable_of_sigmaCompactSpace`.
   * `TauCeti/AlgebraicTopology/SimplicialComplex/Realization/LocallyFinite.lean` (edit):
     `exists_mem_support_eq_of_mem_nhds_vertex`, `finite_closedStar_faces_of_isCompact`,
     `finite_closedStar_faces_of_weaklyLocallyCompactSpace` (converse of the existing
     `locallyCompactSpace_realization_of_finite_vertex_stars`).
   * `TauCeti/AlgebraicTopology/SimplicialComplex/Realization/CWComplex/LocallyFinite.lean` (new):
     `locallyFinite_closedCell_realizationCWComplex`, `countable_cell_realizationCWComplex`,
     `isEmpty_cell_realizationCWComplex`, `finiteDimensional_realizationCWComplex`,
     `realizationSubcomplex`, `coe_realizationSubcomplex`.
2. **feat: make prescribed points of a simplicial realization vertices** (after: none; ~300 lines).
   * `TauCeti/AlgebraicTopology/SimplicialComplex/Realization/Shift.lean` (new):
     `shiftHomeomorph`, `shiftHomeomorph_symm`, `shiftHomeomorph_apply_self`,
     `support_shiftHomeomorph` (private helpers `shiftCoeff`, `shiftVal`, `shift`).
   * `TauCeti/AlgebraicTopology/SimplicialComplex/Subdivision/MarkedVertex.lean` (new):
     `support_faceBarycenter`, `exists_barycentricSubdivision_homeomorph_vertex`.
3. **feat: countable locally finite CW type of triangulated spaces** (after: 1, 2; ~244 lines).
   * `TauCeti/Topology/CWComplex/Classical/LocallyFiniteCWType.lean` (new): class
     `CountableLocallyFiniteCWType`, `CountableLocallyFiniteCWType.toCWType`,
     `CountableLocallyFiniteCWType.of_cwComplex`,
     `ContinuousMap.HomotopyEquiv.countableLocallyFiniteCWType(_iff)`,
     `Homeomorph.countableLocallyFiniteCWType`, `FiniteCWType.toCountableLocallyFiniteCWType`.
   * `TauCeti/Topology/Triangulable/LocallyFiniteCWType.lean` (new):
     `AbstractSimplicialComplex.exists_triangulation_mem_range_vertex`,
     `AbstractSimplicialComplex.exists_cwComplex_of_triangulation`,
     `TauCeti.IsTriangulable.countableLocallyFiniteCWType`.
4. **feat: smooth manifolds have countable locally finite CW type** (after: 1, 2, 3, and the
   supplier `smooth-implies-pl` on `main`; ~227 lines). The only split completing the target.
   * `TauCeti/Geometry/Manifold/SmoothTriangulation/Dimension.lean` (new):
     `IsSimplexImmersion.card_le`, `IsSmoothTriangulation.card_le`.
   * `TauCeti/Geometry/Manifold/CWType.lean` (new): `exists_cwComplex_of_isManifold`,
     `countableLocallyFiniteCWType_of_isManifold`, `finiteCWType_of_isManifold`,
     `exists_cwComplex_boundary_of_isManifold_euclideanHalfSpace`,
     `countableLocallyFiniteCWType_of_isManifold_euclideanHalfSpace`,
     `finiteCWType_of_isManifold_euclideanHalfSpace`.

Splits 1 and 2 are independent and can be opened together; split 3 needs both; split 4 needs all
three and the supplier.
