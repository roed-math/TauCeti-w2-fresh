/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Neighborhood
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Shift

/-!
# Making a prescribed point a vertex

Every point `y` of a weak realization becomes a vertex after one barycentric subdivision, up to
a homeomorphism that changes nothing else of combinatorial significance. Slide the barycenter of
the open simplex containing `y` onto `y` (`AbstractSimplicialComplex.shiftHomeomorph`), and
compose with the subdivision homeomorphism. The resulting homeomorphism from the subdivided
realization sends the face-vertex of the carrier of `y` to `y`, sends the face-vertex of each
singleton `{v}` to the old vertex `v`, and carries the polyhedron of the subdivided subcomplex of
every precomplex `P` onto the polyhedron of `P`, because the slide preserves supports.

Iterating this over a finite set of points of a triangulated space gives a triangulation in
which all of them are vertices, compatible with any prescribed subcomplex such as the boundary of
a triangulated manifold.

## Main results

* `AbstractSimplicialComplex.exists_barycentricSubdivision_homeomorph_vertex`: one prescribed
  point becomes a vertex of the barycentric subdivision.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2
  (subdivisions and the homogeneity of polyhedra).
-/

public section

noncomputable section

open Set TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} (K : AbstractSimplicialComplex ι)

attribute [local instance] Classical.decEq

/-- The barycenter of a face is supported exactly on that face. -/
theorem support_faceBarycenter (σ : Face K) : (faceBarycenter K σ).support = σ.1 := by
  ext w
  have hpos : (0 : ℝ) < (σ.1.card : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr (K.isRelLowerSet_faces.prop_of_mem σ.2)))
  by_cases hw : w ∈ σ.1 <;> simp [Finsupp.mem_support_iff, faceBarycenter_apply, hw, hpos.ne']

/-- **One prescribed point becomes a vertex.** For every point `y` of the realization of `K`
there is a homeomorphism `e` from the realization of the barycentric subdivision of `K` onto the
realization of `K` that sends some face-vertex to `y`, sends the face-vertex `{v}` to the vertex
`v` for every `v`, and carries the subdivided subcomplex of every precomplex `P` onto the
polyhedron of `P`. -/
theorem exists_barycentricSubdivision_homeomorph_vertex (y : Realization K) :
    ∃ e : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex) ≃ₜ Realization K,
      (∃ σ, e (vertex _ σ) = y) ∧
      (∀ v : ι, e (vertex _ ⟨{v}, K.singleton_mem v⟩) = vertex K v) ∧
      ∀ (P : PreAbstractSimplicialComplex ι) x,
        (e x).1.support ∈ P ↔ x.1.support ∈ K.subdivisionSubcomplex P := by
  let s := barycentricSubdivisionRealizationHomeomorph K
  have hs (σ : Face K) : (s (vertex _ σ)).1.support = σ.1 := by
    rw [barycentricSubdivisionRealizationHomeomorph_apply,
      barycentricSubdivisionRealizationMap_vertex, support_faceBarycenter]
  let σ := carrier K y
  have hσ : (s (vertex _ σ)).1.support = y.1.support := by rw [hs, carrier_val]
  refine ⟨s.trans (shiftHomeomorph _ y hσ), ⟨σ, ?_⟩, fun v => ?_, fun P x => ?_⟩
  · rw [Homeomorph.trans_apply, shiftHomeomorph_apply_self]
  · apply Realization.eq_vertex_of_support_eq
    rw [Homeomorph.trans_apply, support_shiftHomeomorph, hs]
  · rw [Homeomorph.trans_apply, support_shiftHomeomorph,
      barycentricSubdivisionRealizationHomeomorph_apply,
      support_barycentricSubdivisionRealizationMap_mem_iff]
    exact (Set.ext_iff.mp (K.setOf_support_mem_subdivisionSubcomplex P) x).symm

end AbstractSimplicialComplex
