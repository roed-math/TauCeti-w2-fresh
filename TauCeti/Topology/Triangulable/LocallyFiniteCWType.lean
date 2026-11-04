/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Triangulable.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.LocallyFinite
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.LocallyFinite
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.EulerCharacteristic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.MarkedVertex
public import TauCeti.Topology.CWComplex.Classical.LocallyFiniteCWType

/-!
# Countable locally finite CW type of locally compact triangulated spaces

A locally compact second-countable space `X` triangulated by a complex `K` is homeomorphic to a
countable locally finite CW complex. Local compactness makes the vertex stars of `K` finite and
σ-compactness makes its vertex set countable, so the simplicial CW structure
`AbstractSimplicialComplex.realizationCWComplex` has these properties; when `X` is compact it is
finite. The triangulation may first be refined so that finitely many prescribed points are
vertices (`AbstractSimplicialComplex.exists_barycentricSubdivision_homeomorph_vertex`), keeping
any prescribed subcomplex, such as the boundary of a triangulated manifold, a subcomplex, and
keeping every bound on the dimension of the simplices.

This is the topological half of the passage from a smooth triangulation of a manifold to its CW
models; the smooth half is in `TauCeti.Geometry.Manifold.CWType`.

## Main results

* `AbstractSimplicialComplex.exists_triangulation_mem_range_vertex`: finitely many prescribed
  points become vertices of a triangulation, compatibly with a subcomplex.
* `AbstractSimplicialComplex.exists_cwComplex_of_triangulation`: a locally compact
  second-countable triangulated space is homeomorphic to a countable locally finite CW complex,
  with a prescribed subcomplex and prescribed `0`-cells, finite in the compact case.
* `TauCeti.IsTriangulable.countableLocallyFiniteCWType`: a locally compact second-countable
  triangulable space has countable locally finite CW type.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 and Appendix A.
-/

public section

noncomputable section

open Set Topology Topology.RelCWComplex AbstractSimplicialComplex TauCeti.SetLike

namespace TauCeti

universe u

section Triangulation

variable {X : Type u} [TopologicalSpace X]

/-- **Prescribed vertices.** A triangulation `f : |K| ≃ₜ X` in which a set `B` is the polyhedron
of a precomplex `L` can be refined so that every point of a finite set `S` is a vertex, keeping
`B` the polyhedron of a precomplex and every bound on the number of vertices of the faces. -/
theorem _root_.AbstractSimplicialComplex.exists_triangulation_mem_range_vertex {ι : Type u}
    (K : AbstractSimplicialComplex ι)
    (f : Realization K ≃ₜ X) (B : Set X) (L : PreAbstractSimplicialComplex ι)
    (hL : ∀ x, f x ∈ B ↔ x.1.support ∈ L) (S : Finset X) :
    ∃ (κ : Type u) (K' : AbstractSimplicialComplex κ) (f' : Realization K' ≃ₜ X)
      (L' : PreAbstractSimplicialComplex κ), (∀ x, f' x ∈ B ↔ x.1.support ∈ L') ∧
        (∀ D : ℕ, (∀ σ ∈ K, σ.card ≤ D) → ∀ σ ∈ K', σ.card ≤ D) ∧
        ∀ p ∈ S, p ∈ range (f' ∘ vertex K') := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨ι, K, f, L, hL, fun _ hD => hD, by simp⟩
  | insert p S _ ih =>
    obtain ⟨κ, K', f', L', hL', hD', hS⟩ := ih
    obtain ⟨e, ⟨σ, hσ⟩, hv, he⟩ :=
      K'.exists_barycentricSubdivision_homeomorph_vertex (f'.symm p)
    refine ⟨_, _, e.trans f', K'.subdivisionSubcomplex L', fun x => ?_,
      fun D hD ρ hρ => ?_, ?_⟩
    · rw [Homeomorph.trans_apply, hL', he]
    · exact TauCeti.PreAbstractSimplicialComplex.card_le_of_mem_barycentricSubdivision
        (fun τ hτ => hD' D hD τ hτ) hρ
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact ⟨σ, by simp [hσ]⟩
      · obtain ⟨v, rfl⟩ := hS q hq
        exact ⟨⟨{v}, K'.singleton_mem v⟩, by simp [hv]⟩

variable [LocallyCompactSpace X] [SecondCountableTopology X]

/-- **Triangulated spaces are countable locally finite CW complexes.** A locally compact
second-countable space `X` triangulated by a complex `K`, in which a set `B` is the polyhedron of
a precomplex, is homeomorphic to a CW complex with countably many cells and a locally finite
family of closed cells, which is finite when `X` is compact and has no cells above dimension `d`
when the faces of `K` have at most `d + 1` vertices; `B` corresponds to a subcomplex, and every
point of a prescribed finite set `S` to a `0`-cell. -/
theorem _root_.AbstractSimplicialComplex.exists_cwComplex_of_triangulation {ι : Type u}
    (K : AbstractSimplicialComplex ι)
    (f : Realization K ≃ₜ X) (B : Set X) (L : PreAbstractSimplicialComplex ι)
    (hL : ∀ x, f x ∈ B ↔ x.1.support ∈ L) (S : Finset X) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (C : Set Y) (_ : CWComplex C)
      (A : RelCWComplex.Subcomplex C) (e : X ≃ₜ C),
      (∀ n, Countable (cell C n)) ∧ LocallyFinite (fun c : Σ n, cell C n => closedCell c.1 c.2) ∧
      (∀ d : ℕ, (∀ σ ∈ K, σ.card ≤ d + 1) → ∀ n, d < n → IsEmpty (cell C n)) ∧
      (CompactSpace X → RelCWComplex.Finite C) ∧
      (∀ x, x ∈ B ↔ (e x : Y) ∈ A) ∧ ∀ p ∈ S, ∃ c : cell C 0, openCell 0 c = {(e p : Y)} := by
  obtain ⟨κ, K', f', L', hL', hd', hS⟩ := K.exists_triangulation_mem_range_vertex f B L hL S
  have : LocallyCompactSpace (Realization K') := f'.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (Realization K') :=
    f'.isEmbedding.isInducing.secondCountableTopology
  have : Countable κ := K'.countable_of_sigmaCompactSpace
  let : LinearOrder κ := IsWellOrder.linearOrder WellOrderingRel
  let := realizationCWComplex K'
  let e : X ≃ₜ (univ : Set (Realization K')) := f'.symm.trans (Homeomorph.Set.univ _).symm
  have he (x : X) : (e x : Realization K') = f'.symm x := rfl
  refine ⟨Realization K', _, inferInstance, univ, realizationCWComplex K',
    realizationSubcomplex K' L', e, K'.countable_cell_realizationCWComplex,
    K'.locallyFinite_closedCell_realizationCWComplex
      (K'.finite_closedStar_faces_of_weaklyLocallyCompactSpace),
    fun d hd n hn => K'.isEmpty_cell_realizationCWComplex (hd' _ hd) hn, fun hX => ?_,
    fun x => ?_,
    fun p hp => ?_⟩
  · have : CompactSpace (Realization K') := f'.symm.compactSpace
    have : Finite κ := (compactSpace_realization_iff_finite K').mp this
    exact K'.finite_realizationCWComplex
  · rw [← SetLike.mem_coe, coe_realizationSubcomplex, he]
    change x ∈ B ↔ (f'.symm x).1.support ∈ L'
    rw [← hL', Homeomorph.apply_symm_apply]
  · obtain ⟨v, rfl⟩ := hS p hp
    refine ⟨(realizationCellEquiv K' 0).symm (RealizationCell.vertex K' v), ?_⟩
    rw [openCell_realizationCellEquiv_symm, he, Function.comp_apply,
      Homeomorph.symm_apply_apply]
    ext y
    simp only [RealizationCell.vertex_val, mem_ofPred_eq, mem_singleton_iff]
    exact ⟨Realization.eq_vertex_of_support_eq K' y, fun h => h ▸ support_vertex K' v⟩

/-- A locally compact second-countable triangulable space has countable locally finite CW
type. -/
theorem IsTriangulable.countableLocallyFiniteCWType (h : IsTriangulable.{u} X) :
    CountableLocallyFiniteCWType X := by
  obtain ⟨ι, K, ⟨f⟩⟩ := (isTriangulable_iff X).mp h
  obtain ⟨Y, _, _, C, _, -, e, hcount, hfin, -⟩ := K.exists_cwComplex_of_triangulation f univ
    K.toPreAbstractSimplicialComplex (fun x => iff_of_true (mem_univ _) (K.support_mem x)) ∅
  have := CountableLocallyFiniteCWType.of_cwComplex C hcount hfin
  exact e.countableLocallyFiniteCWType

end Triangulation

end TauCeti
