/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.FiniteCWType

/-!
# Spaces of countable locally finite CW type

A topological space has *countable locally finite CW type*
(`TauCeti.CountableLocallyFiniteCWType`) if it is homotopy equivalent to a classical CW complex,
in a Hausdorff ambient space of the same universe, with countably many cells in each dimension
and whose closed cells form a locally finite family. This is the CW type of a noncompact
manifold: its triangulations are countable and locally finite, but not finite.

The property is inherited along homotopy equivalences and homeomorphisms, and every space of
finite CW type has it.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 and Appendix A (locally finite CW complexes).
-/

public section

open Topology Topology.RelCWComplex Set

universe w

namespace TauCeti

/-- A topological space has **countable locally finite CW type** if it is homotopy equivalent to
a CW complex `C`, a subspace of a Hausdorff space in the same universe, with countably many cells
in each dimension and a locally finite family of closed cells. -/
class CountableLocallyFiniteCWType (X : Type w) [TopologicalSpace X] : Prop where
  /-- A countable locally finite CW complex homotopy equivalent to the space. -/
  exists_homotopyEquiv : ∃ (Y : Type w) (_ : TopologicalSpace Y) (_ : T2Space Y) (C : Set Y)
    (_ : CWComplex C), (∀ n, Countable (cell C n)) ∧
      LocallyFinite (fun c : Σ n, cell C n => closedCell c.1 c.2) ∧
      Nonempty (ContinuousMap.HomotopyEquiv X C)

/-- A space of countable locally finite CW type has CW type. -/
instance CountableLocallyFiniteCWType.toCWType (X : Type w) [TopologicalSpace X]
    [h : CountableLocallyFiniteCWType X] : CWType X := by
  obtain ⟨Y, _, _, C, _, -, -, e⟩ := h.exists_homotopyEquiv
  exact ⟨⟨Y, _, ‹_›, C, ‹_›, e⟩⟩

/-- A CW complex with countably many cells and a locally finite family of closed cells has
countable locally finite CW type. -/
theorem CountableLocallyFiniteCWType.of_cwComplex {Y : Type w} [TopologicalSpace Y] [T2Space Y]
    (C : Set Y) [CWComplex C] (hcount : ∀ n, Countable (cell C n))
    (hfin : LocallyFinite (fun c : Σ n, cell C n => closedCell c.1 c.2)) :
    CountableLocallyFiniteCWType C :=
  ⟨⟨Y, _, ‹_›, C, ‹_›, hcount, hfin, ⟨.refl C⟩⟩⟩

/-- A space homotopy equivalent to a space of countable locally finite CW type has countable
locally finite CW type. -/
theorem _root_.ContinuousMap.HomotopyEquiv.countableLocallyFiniteCWType {X Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [h : CountableLocallyFiniteCWType Y]
    (e : ContinuousMap.HomotopyEquiv X Y) : CountableLocallyFiniteCWType X := by
  obtain ⟨Z, _, _, C, _, hcount, hfin, ⟨e'⟩⟩ := h.exists_homotopyEquiv
  exact ⟨⟨Z, _, ‹_›, C, ‹_›, hcount, hfin, ⟨e.trans e'⟩⟩⟩

/-- A space homeomorphic to a space of countable locally finite CW type has countable locally
finite CW type. -/
theorem _root_.Homeomorph.countableLocallyFiniteCWType {X Y : Type w} [TopologicalSpace X]
    [TopologicalSpace Y] [CountableLocallyFiniteCWType Y] (e : X ≃ₜ Y) :
    CountableLocallyFiniteCWType X :=
  e.toHomotopyEquiv.countableLocallyFiniteCWType

/-- Two homotopy equivalent spaces either both have countable locally finite CW type or both do
not. -/
theorem _root_.ContinuousMap.HomotopyEquiv.countableLocallyFiniteCWType_iff {X Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) :
    CountableLocallyFiniteCWType X ↔ CountableLocallyFiniteCWType Y :=
  ⟨fun _ ↦ e.symm.countableLocallyFiniteCWType, fun _ ↦ e.countableLocallyFiniteCWType⟩

/-- A space of finite CW type has countable locally finite CW type: a finite family of closed
cells is locally finite. -/
instance FiniteCWType.toCountableLocallyFiniteCWType (X : Type w) [TopologicalSpace X]
    [h : FiniteCWType X] : CountableLocallyFiniteCWType X := by
  obtain ⟨Y, _, _, C, _, _, e⟩ := h.exists_homotopyEquiv
  have hcell : ∀ n, _root_.Finite (cell C n) := RelCWComplex.FiniteType.finite_cell
  have : _root_.Finite (Σ n, cell C n) := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (RelCWComplex.FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅))
    let f : (Σ n : Fin N, cell C n) → Σ n, cell C n := fun c => ⟨c.1, c.2⟩
    refine Finite.of_surjective f fun ⟨n, c⟩ => ?_
    have hn : n < N := by
      by_contra hn
      exact (hN n (not_lt.mp hn)).false c
    exact ⟨⟨⟨n, hn⟩, c⟩, rfl⟩
  exact ⟨⟨Y, _, ‹_›, C, ‹_›, fun n => (hcell n).to_countable, locallyFinite_of_finite _, e⟩⟩

end TauCeti
