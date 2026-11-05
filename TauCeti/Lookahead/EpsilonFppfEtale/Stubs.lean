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
Only what the comparison morphisms consume is stated: Nisnevich coverings, their stability under
base change and the fact that Zariski coverings are Nisnevich coverings, the small Nisnevich
topology on `X.Etale`, its description by Nisnevich coverings and its comparison with the small
étale topology. The proofs
use only the stated API, never the bodies of `IsNisnevichCovering` or `smallNisnevichTopology`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- Stub: a family `{pᵢ : Xᵢ ⟶ S}` of morphisms of schemes is a Nisnevich covering if every `pᵢ`
is étale and every point of `S` has a preimage at which `pᵢ` induces an isomorphism of residue
fields. -/
def IsNisnevichCovering {ι : Type*} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S) : Prop :=
  sorry

/-- Stub: Nisnevich coverings are stable under base change: if `{pᵢ : Xᵢ ⟶ S}` is a Nisnevich
covering and each `Pᵢ` is the fibre product of `Xᵢ` and `Y` over `S`, then `{Pᵢ ⟶ Y}` is a
Nisnevich covering. -/
theorem IsNisnevichCovering.of_isPullback {ι : Type*} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (hf : IsNisnevichCovering f) {Y : Scheme.{u}} (g : Y ⟶ S)
    {P : ι → Scheme.{u}} (p₁ : ∀ i, P i ⟶ Y) (p₂ : ∀ i, P i ⟶ X i)
    (h : ∀ i, IsPullback (p₁ i) (p₂ i) g (f i)) : IsNisnevichCovering p₁ := by
  sorry

/-- Stub: Zariski coverings are Nisnevich coverings. -/
theorem isNisnevichCovering_of_zariski {ι : Type*} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (hf : Presieve.ofArrows X f ∈ AlgebraicGeometry.Scheme.zariskiPrecoverage S) :
    IsNisnevichCovering f := by
  sorry

end TauCeti.AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

open TauCeti.AlgebraicGeometry.Scheme

/-- Stub: the small Nisnevich site of a scheme `X`, on the category `X.Etale` of schemes étale
over `X`. -/
noncomputable def smallNisnevichTopology (X : Scheme.{u}) : GrothendieckTopology X.Etale :=
  sorry

/-- Stub: a family of morphisms in `X.Etale` generates a covering sieve of the small Nisnevich
site exactly when the underlying morphisms of schemes form a Nisnevich covering. -/
theorem ofArrows_mem_smallNisnevichTopology_iff {X : Scheme.{u}} {W : X.Etale} {ι : Type*}
    {Z : ι → X.Etale} (f : ∀ i, Z i ⟶ W) :
    Sieve.ofArrows Z f ∈ X.smallNisnevichTopology W ↔
      IsNisnevichCovering (fun i ↦ (f i).left) := by
  sorry

/-- Stub: the small Nisnevich topology is coarser than the small étale topology. -/
theorem smallNisnevichTopology_le_smallEtaleTopology (X : Scheme.{u}) :
    X.smallNisnevichTopology ≤ X.smallEtaleTopology := by
  sorry

end AlgebraicGeometry.Scheme
