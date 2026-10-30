/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

set_option warningAsError false

/-!
# Lookahead stubs for `sheaf-h-pullback`

These are lookahead stubs for the supplier `sheaf-h-pullback` (SchemeAndStackFoundations §2.1,
open pull request 22647), stated as that pull request states them in
`TauCeti/CategoryTheory/Sites/SheafCohomology/Pullback.lean`. They are to be replaced by the
landed declarations. Only the declarations consumed by the Leray target are restated: the
pullback `Sheaf.H.pullback` itself, together with its degree-zero description, its naturality in
the coefficient sheaf, and its compatibility with connecting homomorphisms.
-/

public section

open CategoryTheory Abelian Limits AddCommGrpCat

universe w w₁ w₂

namespace CategoryTheory.Sheaf.H

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {D : Type*} [Category* D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{w₁} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w₂} (Sheaf K AddCommGrpCat.{w})]

/-- Stub: the pullback `Hⁿ(C, G) →+ Hⁿ(D, pb G)` of sheaf cohomology along an exact additive
functor `pb`, given a map `c : ℤ_K ⟶ pb ℤ_J` between constant sheaves. Its binders are written
out because a definition with a `sorry` body would otherwise omit the unused section variables. -/
@[nolint unusedArguments]
noncomputable def pullback (pb : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w})
    [pb.Additive] [PreservesFiniteLimits pb] [PreservesFiniteColimits pb]
    (c : (constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ)) ⟶
      pb.obj ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))))
    (G : Sheaf J AddCommGrpCat.{w}) (n : ℕ) : H G n →+ H (pb.obj G) n :=
  sorry

variable (pb : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}) [pb.Additive]
  [PreservesFiniteLimits pb] [PreservesFiniteColimits pb]
  (c : (constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ)) ⟶
    pb.obj ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))))

/-- Stub: in degree zero, the pullback sends the class of a map `f : ℤ_J ⟶ G` to
`c ≫ pb.map f`. -/
@[simp]
lemma addEquiv₀_pullback {G : Sheaf J AddCommGrpCat.{w}} (x : H G 0) :
    Ext.addEquiv₀ (pullback pb c G 0 x) = c ≫ pb.map (Ext.addEquiv₀ x) := by
  sorry

/-- Stub: the pullback is natural in the coefficient sheaf. -/
lemma pullback_naturality {G₁ G₂ : Sheaf J AddCommGrpCat.{w}} (f : G₁ ⟶ G₂) {n : ℕ}
    (x : H G₁ n) :
    pullback pb c G₂ n (H.map f n x) = H.map (pb.map f) n (pullback pb c G₁ n x) := by
  sorry

/-- Stub: the pullback commutes with the connecting homomorphisms of a short exact sequence of
abelian sheaves and of its image under `pb`. -/
lemma pullback_δ {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : H S.X₃ n₀) :
    pullback pb c S.X₁ n₁ (H.δ hS n₀ n₁ h x) =
      H.δ (hS.map_of_exact pb) n₀ n₁ h (pullback pb c S.X₃ n₀ x) := by
  sorry

end CategoryTheory.Sheaf.H
