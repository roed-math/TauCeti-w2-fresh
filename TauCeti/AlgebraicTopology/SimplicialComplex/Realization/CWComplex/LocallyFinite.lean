/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic
public import Mathlib.Topology.CWComplex.Classical.Finite

/-!
# Locally finite simplicial CW complexes and their subcomplexes

The CW structure `AbstractSimplicialComplex.realizationCWComplex K` on a weak realization has
one closed cell for each face of `K`. When every vertex has a finite closed star, the open star
of a vertex is a neighbourhood meeting only the finitely many closed cells of faces containing
that vertex, so the family of closed cells is locally finite. A countable vertex type gives
countably many cells, and a bound on the size of the faces bounds the dimension of the cells.

Every precomplex `L` determines the CW subcomplex of points whose support is a face of `L`:
its cells are the faces of `K` lying in `L`. This is the cellular form of a subcomplex of a
triangulation, such as the boundary of a triangulated manifold.

## Main results

* `AbstractSimplicialComplex.locallyFinite_closedCell_realizationCWComplex`: finite vertex stars
  make the closed cells a locally finite family.
* `AbstractSimplicialComplex.countable_cell_realizationCWComplex`: countably many vertices give
  countably many cells.
* `AbstractSimplicialComplex.isEmpty_cell_realizationCWComplex` and
  `AbstractSimplicialComplex.finiteDimensional_realizationCWComplex`: bounded faces give a
  finite-dimensional CW complex.
* `AbstractSimplicialComplex.realizationSubcomplex`: the CW subcomplex of a precomplex.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 and Appendix A (simplicial and locally finite
  CW complexes).
-/

public section

noncomputable section

open Set Topology Topology.RelCWComplex TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} [LinearOrder ι] (K : AbstractSimplicialComplex ι)

/-- If every vertex has a finite closed star, the closed cells of the simplicial CW structure
form a locally finite family: the open star of a vertex meets only the closed cells of the
faces containing it. -/
theorem locallyFinite_closedCell_realizationCWComplex
    (hfin : ∀ v : ι,
      (PreAbstractSimplicialComplex.closedStar K.toPreAbstractSimplicialComplex {v}).faces.Finite) :
    letI := realizationCWComplex K
    LocallyFinite fun c : Σ n, cell (univ : Set (Realization K)) n => closedCell c.1 c.2 := by
  let := realizationCWComplex K
  intro x
  obtain ⟨v, hv⟩ := K.exists_mem_openStarRealization x
  refine ⟨K.openStarRealization v, (K.isOpen_openStarRealization v).mem_nhds hv, ?_⟩
  let φ : (Σ n, cell (univ : Set (Realization K)) n) → Finset ι := fun c =>
    (realizationCellEquiv K c.1 c.2).1.1
  have hφ : Function.Injective φ := by
    rintro ⟨n, c⟩ ⟨m, d⟩ h
    have hc := (realizationCellEquiv K n c).2
    have hd := (realizationCellEquiv K m d).2
    change (realizationCellEquiv K n c).1.1 = (realizationCellEquiv K m d).1.1 at h
    obtain rfl : n = m := by rw [h] at hc; omega
    obtain rfl : c = d := (realizationCellEquiv K n).injective (Subtype.ext (Subtype.ext h))
    rfl
  refine Finite.of_finite_image ((hfin v).subset ?_) hφ.injOn
  rintro _ ⟨c, ⟨y, hyc, hyv⟩, rfl⟩
  have hyc' : y ∈ closedCell c.1 c.2 := hyc
  rw [← (realizationCellEquiv K c.1).symm_apply_apply c.2,
    closedCell_realizationCellEquiv_symm] at hyc'
  have hvφ : v ∈ φ c := hyc' ((K.mem_openStarRealization_iff_mem_support).mp hyv)
  refine PreAbstractSimplicialComplex.mem_closedStar.mpr
    ⟨(realizationCellEquiv K c.1 c.2).1.2, ?_⟩
  rw [Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr hvφ)]
  exact (realizationCellEquiv K c.1 c.2).1.2

/-- A complex on a countable vertex type has countably many cells in each dimension. -/
theorem countable_cell_realizationCWComplex [Countable ι] (n : ℕ) :
    letI := realizationCWComplex K
    Countable (cell (univ : Set (Realization K)) n) :=
  letI := realizationCWComplex K
  Countable.of_equiv _ (realizationCellEquiv K n).symm

/-- A complex whose faces have at most `d + 1` vertices has no cells above dimension `d`. -/
theorem isEmpty_cell_realizationCWComplex {d : ℕ} (hd : ∀ σ ∈ K, σ.card ≤ d + 1) {n : ℕ}
    (hn : d < n) :
    letI := realizationCWComplex K
    IsEmpty (cell (univ : Set (Realization K)) n) := by
  let := realizationCWComplex K
  refine ⟨fun c => ?_⟩
  have := hd _ (realizationCellEquiv K n c).1.2
  rw [(realizationCellEquiv K n c).2] at this
  omega

/-- A complex whose faces have at most `d + 1` vertices has a finite-dimensional CW structure. -/
theorem finiteDimensional_realizationCWComplex {d : ℕ} (hd : ∀ σ ∈ K, σ.card ≤ d + 1) :
    letI := realizationCWComplex K
    RelCWComplex.FiniteDimensional (univ : Set (Realization K)) :=
  letI := realizationCWComplex K
  ⟨Filter.eventually_atTop.2 ⟨d + 1, fun _ hn => K.isEmpty_cell_realizationCWComplex hd hn⟩⟩

variable (L : PreAbstractSimplicialComplex ι)

/-- The CW subcomplex of the simplicial CW structure determined by a precomplex `L`: the points
whose support is a face of `L`, with the cells of the faces of `K` lying in `L`. -/
def realizationSubcomplex :
    letI := realizationCWComplex K
    RelCWComplex.Subcomplex (univ : Set (Realization K)) :=
  letI := realizationCWComplex K
  CWComplex.Subcomplex.mk' _ {x | x.1.support ∈ L}
    (fun n => {c | (realizationCellEquiv K n c).1.1 ∈ L})
    (fun n c => by
      rw [← (realizationCellEquiv K n).symm_apply_apply c.1,
        closedCell_realizationCellEquiv_symm]
      intro x hx
      exact (L.isRelLowerSet_faces c.2).2 hx
        (K.isRelLowerSet_faces.prop_of_mem (K.support_mem x)))
    (by
      ext x
      simp only [mem_iUnion, mem_ofPred_eq]
      constructor
      · rintro ⟨n, c, hx⟩
        rw [← (realizationCellEquiv K n).symm_apply_apply c.1,
          openCell_realizationCellEquiv_symm] at hx
        rw [hx]
        exact c.2
      · intro hx
        have hne := K.isRelLowerSet_faces.prop_of_mem (K.support_mem x)
        let n := x.1.support.card - 1
        have hcard : x.1.support.card = n + 1 :=
          (Nat.sub_add_cancel (Finset.card_pos.mpr hne)).symm
        let c : RealizationCell K n := ⟨⟨x.1.support, K.support_mem x⟩, hcard⟩
        refine ⟨n, ⟨(realizationCellEquiv K n).symm c, ?_⟩, ?_⟩
        · change (realizationCellEquiv K n ((realizationCellEquiv K n).symm c)).1.1 ∈ L
          rw [Equiv.apply_symm_apply]
          exact hx
        · rw [openCell_realizationCellEquiv_symm]
          rfl)

/-- The carrier of `realizationSubcomplex K L` is the set of points supported on faces of `L`. -/
@[simp]
theorem coe_realizationSubcomplex :
    letI := realizationCWComplex K
    ((realizationSubcomplex K L : RelCWComplex.Subcomplex (univ : Set (Realization K))) :
      Set (Realization K)) = {x | x.1.support ∈ L} := by
  unfold realizationSubcomplex
  rfl

end AbstractSimplicialComplex
