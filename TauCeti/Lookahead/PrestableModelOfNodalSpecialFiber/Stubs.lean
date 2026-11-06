/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import TauCeti.AlgebraicGeometry.Curves.Node.Relative

set_option warningAsError false

/-!
# Lookahead stubs for `nodal-local-normal-form`

These are lookahead stubs for the supplier `nodal-local-normal-form` (StableReduction, Layer 1),
to be replaced by the landed declarations. Only the clause consumed by
`prestable-model-of-nodal-special-fiber` is stated: nodality is local on the source for the
étale topology.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- **Nodality is étale local on the source.** If a family of étale morphisms `e i : U i ⟶ X`
covers `X` and every composite `e i ≫ f` is at worst nodal of relative dimension one, then so
is `f`. -/
theorem AtWorstNodalOfRelativeDimensionOne.of_etale_cover {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} {U : ι → Scheme.{u}} (e : ∀ i, U i ⟶ X) [∀ i, Etale (e i)]
    (he : ∀ x : X, ∃ i, x ∈ Set.range (e i))
    (h : ∀ i, AtWorstNodalOfRelativeDimensionOne (e i ≫ f)) :
    AtWorstNodalOfRelativeDimensionOne f := by
  sorry

end TauCeti.AlgebraicGeometry
