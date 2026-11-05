/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import TauCeti.AlgebraicGeometry.Chow.Basic

set_option warningAsError false

/-!
# Lookahead stubs for `chow-group`

These are lookahead stubs for the supplier slug `chow-group` (SchemeAndStackFoundations §5.1,
in flight as Tau Ceti PR #27340), to be replaced by the landed declarations. Each is stated under
the name and namespace it has in that pull request:

* `TauCeti.height_eq_topologicalKrullDim_closure_singleton`
  (`TauCeti/Topology/KrullDimension/Basic.lean`);
* `TauCeti.Ring.ord_ringEquiv` (`TauCeti/RingTheory/OrderOfVanishing.lean`);
* `TauCeti.AlgebraicGeometry.coheight_add_height_eq_topologicalKrullDim`
  (`TauCeti/AlgebraicGeometry/Scheme/LocalDimension.lean`);
* `TauCeti.AlgebraicGeometry.Chow.RatEquivFamily.component_def`
  (`TauCeti/AlgebraicGeometry/Chow/Basic.lean`).
-/

public section

open AlgebraicGeometry Order Topology

namespace TauCeti

attribute [local instance] specializationPreorder in
/-- On a quasi-sober T₀ topological space, the height of a point for the specialization preorder
(`x ≤ y ↔ y ⤳ x`) is the Krull dimension of its closure. -/
theorem height_eq_topologicalKrullDim_closure_singleton {α : Type*} [TopologicalSpace α]
    [QuasiSober α] [T0Space α] (x : α) :
    (height x : WithBot ℕ∞) = topologicalKrullDim (closure ({x} : Set α)) := by
  sorry

namespace Ring

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- The order of vanishing is invariant under ring isomorphisms. -/
@[simp]
theorem ord_ringEquiv (σ : R ≃+* R') (x : R) : Ring.ord R' (σ x) = Ring.ord R x := by
  sorry

end Ring

namespace AlgebraicGeometry

universe u

section DimensionFormula

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]

include k in
/-- **Dimension formula.** On an irreducible scheme `X` locally of finite type over a field, the
codimension and the dimension of the closure of any point add up to the dimension of `X`:
`coheight x + height x = dim X`, where `height x = dim {x}⁻` for the specialization order. -/
theorem coheight_add_height_eq_topologicalKrullDim [IrreducibleSpace X] (x : X) :
    (Order.coheight x : WithBot ℕ∞) + Order.height x = topologicalKrullDim X := by
  sorry

end DimensionFormula

namespace Chow.RatEquivFamily

variable {X : Scheme.{u}} {n : ℤ} [IsLocallyNoetherian X] (F : RatEquivFamily X n)

/-- The `j`-th summand is the pushforward `(i j)_* div (r j)`. -/
lemma component_def (j : F.ι) :
    F.component j = AlgebraicCycle.map (F.i j) height height (AlgebraicCycle.div (F.r j)) := by
  sorry

end Chow.RatEquivFamily

end AlgebraicGeometry

end TauCeti
