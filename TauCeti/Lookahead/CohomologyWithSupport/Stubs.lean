/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Basic

set_option warningAsError false

/-!
# Lookahead stubs for `cohomology-with-support`

These are lookahead stubs for the supplier slugs `sheaf-h-pullback` (open PR #22647) and
`qcoh-higher-direct-image-vanishing` (open PR #22975), restated under the names and with the
statements those pull requests give them. They are to be replaced by the landed declarations.
-/

@[expose] public section

open CategoryTheory Abelian Limits AddCommGrpCat

universe w w₁ w₂ u

namespace CategoryTheory.Sheaf.H

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {D : Type*} [Category* D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{w₁} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w₂} (Sheaf K AddCommGrpCat.{w})]
  (pb : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}) [pb.Additive]
  [PreservesFiniteLimits pb] [PreservesFiniteColimits pb]
  (c : (constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ)) ⟶
    pb.obj ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))))

/-- Stub of `sheaf-h-pullback`: the pullback `Hⁿ(C, G) →+ Hⁿ(D, pb G)` of sheaf cohomology. -/
noncomputable def pullback
    (c : (constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ)) ⟶
      pb.obj ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))))
    (G : Sheaf J AddCommGrpCat.{w}) (n : ℕ) : H G n →+ H (pb.obj G) n :=
  sorry

/-- Stub of `sheaf-h-pullback`: the pullback is natural in the coefficient sheaf. -/
lemma pullback_naturality {G₁ G₂ : Sheaf J AddCommGrpCat.{w}} (f : G₁ ⟶ G₂) {n : ℕ}
    (x : H G₁ n) :
    pullback pb c G₂ n (H.map f n x) = H.map (pb.map f) n (pullback pb c G₁ n x) := by
  sorry

end CategoryTheory.Sheaf.H

namespace TauCeti.QCoh

open _root_.AlgebraicGeometry _root_.TauCeti.AlgebraicGeometry.Scheme.Modules

/-- Stub of `qcoh-higher-direct-image-vanishing`: over an affine base, the cohomology of
quasi-coherent modules on the source of a qcqs morphism vanishes in a range depending only on
the morphism. Stacks, Lemmas 30.4.1–30.4.6 (01XH). -/
theorem higherDirectImage_vanishing {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] [IsAffine S] :
    ∃ N : ℕ, ∀ (F : X.Modules) [F.IsQuasicoherent] (p : ℕ), N ≤ p →
      Subsingleton (Cohomology F p) := by
  sorry

end TauCeti.QCoh
