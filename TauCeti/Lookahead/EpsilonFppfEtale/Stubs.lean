/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale

set_option warningAsError false

/-!
# Lookahead stubs for `epsilon-fppf-etale`

These are lookahead stubs for the supplier `is-nisnevich-covering` (open PR #28094, module
`TauCeti.AlgebraicGeometry.Sites.Nisnevich.Basic`), to be replaced by the landed declarations.
Only what the comparison morphisms consume is stated: the small Nisnevich topology on `X.Etale`
and its comparison with the small étale topology. The proofs use only the stated API, never the
body of `smallNisnevichTopology`.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.Scheme

/-- Stub: the small Nisnevich site of a scheme `X`, on the category `X.Etale` of schemes étale
over `X`. -/
noncomputable def smallNisnevichTopology (X : Scheme.{u}) : GrothendieckTopology X.Etale :=
  sorry

/-- Stub: the small Nisnevich topology is coarser than the small étale topology. -/
theorem smallNisnevichTopology_le_smallEtaleTopology (X : Scheme.{u}) :
    smallNisnevichTopology X ≤ X.smallEtaleTopology := by
  sorry

end TauCeti.AlgebraicGeometry.Scheme
