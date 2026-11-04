/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Quotient

set_option warningAsError false

/-!
# Lookahead stubs for `gamma-zero-naive`

These are lookahead stubs for the supplier `finite-quotient` (ModularCurves, Layer 0C, item 3:
the constant-group case of SGA 3, Exposé V, Théorème 4.1), to be replaced by the landed
declarations.

The supplier `universal-subgroup` (ModularCurves, Layer 0G) is not stubbed: its open PR states the
universal subgroup only over an affine base `Spec R`, and the identification of the naive
`[Γ₀(N)]` carrier with the cyclic locus of the subgroup parameter space of `E[N]/S` needs the
relative Grassmannian over a non-affine base, which neither the PR nor `Suggested.lean` pins.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u v

namespace TauCeti.FiniteEtaleScheme

variable {S : Scheme.{u}} {G : Type v} [Group G] [Finite G]
  (F : SingleObj G ⥤ FiniteEtaleScheme S)

/-- **Free finite-group quotients are torsors** (SGA 3, Exposé V, Théorème 4.1, constant-group
case; Layer 0C item 3). If a finite group `G` acts on a finite étale `S`-scheme `Y` without fixed
points with values in fields, then `Y ×_{Y/G} Y` is the disjoint union of `|G|` copies of `Y`,
the copy of `g` mapping to `(y, g y)`: the quotient map `Y ⟶ Y / G` is a `G`-torsor. -/
theorem isPullback_quotientπ_of_free
    (hfree : ∀ (K : Type u) [Field K]
      (x : Spec (CommRingCat.of K) ⟶ (F.obj (SingleObj.star G)).obj.left) (g : G),
      x ≫ (F.map (X := SingleObj.star G) (Y := SingleObj.star G) g).hom.left = x → g = 1) :
    IsPullback (Sigma.desc fun _ : G ↦ 𝟙 (F.obj (SingleObj.star G)).obj.left)
      (Sigma.desc fun g : G ↦ (F.map (X := SingleObj.star G) (Y := SingleObj.star G) g).hom.left)
      (quotientπ F).hom.left (quotientπ F).hom.left :=
  sorry

end TauCeti.FiniteEtaleScheme
