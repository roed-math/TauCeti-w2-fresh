/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Relative

set_option warningAsError false

/-!
# Lookahead stubs for `gamma-zero-naive`

These are lookahead stubs for the supplier `finite-quotient` (ModularCurves, Layer 0C, item 3:
the constant-group case of SGA 3, Exposé V, Théorème 4.1), to be replaced by the landed
declarations. The statement is the one of the supplier's open pull request.

The supplier `universal-subgroup` (ModularCurves, Layer 0G) is not stubbed: its open PR states the
universal subgroup only over an affine base `Spec R`, and the identification of the naive
`[Γ₀(N)]` carrier with the cyclic locus of the subgroup parameter space of `E[N]/S` needs the
relative Grassmannian over a non-affine base, which neither the PR nor `Suggested.lean` pins.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u v

namespace CategoryTheory.CommMon

variable {X : Scheme.{u}} {A : CommMon X.Modules} {G : Type v} [Group G] [Finite G]
  [A.X.IsQuasicoherent] {ρ : G →* Aut A}

/-- **The torsor square of a free relative quotient.** For a free action, the identity and the
action of `g` on the component of `g` exhibit `∐_g Spec_X(A)` as the kernel pair
`Spec_X(A) ×_{Spec_X(A)/G} Spec_X(A)` of the quotient projection. -/
theorem isPullback_invariantSubalgebraPresheaf_relativeSpecπ_of_free
    (hG : ∀ (U : X.affineOpens) (g : G), g ≠ 1 →
      Ideal.span (Set.range fun x : Γ(A.X, U) ↦ sectionsAlgHom (ρ g).asIso.hom U x - x) = ⊤) :
    IsPullback (Sigma.desc fun _ : G ↦ 𝟙 A.relativeSpec)
      (Sigma.desc fun g : G ↦ relativeSpecMap (ρ g).asIso.hom)
      (invariantSubalgebraPresheaf ρ).relativeSpecπ
      (invariantSubalgebraPresheaf ρ).relativeSpecπ :=
  sorry

end CategoryTheory.CommMon
