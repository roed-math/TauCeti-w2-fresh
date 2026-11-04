/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.KrullDimension
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober

set_option warningAsError false

/-!
# Lookahead stubs for `chow-group`

These are lookahead stubs for the supplier slug `chow-group` (SchemeAndStackFoundations §5.1,
in flight as Tau Ceti PR #27340), to be replaced by the landed declarations. Each is stated under
the name, namespace and file placement it has in that pull request
(`TauCeti/Topology/KrullDimension/Basic.lean`).
-/

public section

open Order Topology

namespace TauCeti

attribute [local instance] specializationPreorder in
/-- On a quasi-sober T₀ topological space, the height of a point for the specialization preorder
(`x ≤ y ↔ y ⤳ x`) is the Krull dimension of its closure. -/
theorem height_eq_topologicalKrullDim_closure_singleton {α : Type*} [TopologicalSpace α]
    [QuasiSober α] [T0Space α] (x : α) :
    (height x : WithBot ℕ∞) = topologicalKrullDim (closure ({x} : Set α)) := by
  sorry

end TauCeti
