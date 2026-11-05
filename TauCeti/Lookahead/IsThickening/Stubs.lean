/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Torsor

set_option warningAsError false

/-!
# Lookahead stubs for `is-thickening`

These are lookahead stubs for the supplier `equiv-sheaf-h` (SchemeAndStackFoundations §2.3), to
be replaced by the landed declarations. Only what the target consumes is stated: the comparison
`NonabelianH1.equivSheafH` of torsor classes under an abelian sheaf `G`, viewed as a sheaf of
multiplicative groups, with the sheaf cohomology `Sheaf.H G 1`.
-/

public section

open CategoryTheory

universe w' w v u

namespace CategoryTheory.Sheaf.NonabelianH1

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Lookahead stub of `equiv-sheaf-h`: for an abelian sheaf `G`, the torsor classes under `G`
(viewed as a sheaf of multiplicative groups) are the first cohomology `Sheaf.H G 1` (Stacks,
Lemma 21.4.3 (03AJ)). -/
noncomputable def equivSheafH (G : Sheaf J AddCommGrpCat.{w})
    [J.HasSheafCompose (AddCommGrpCat.toCommGrp.{w} ⋙ forget₂ CommGrpCat.{w} GrpCat.{w})]
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] :
    NonabelianH1 ((sheafCompose J
      (AddCommGrpCat.toCommGrp.{w} ⋙ forget₂ CommGrpCat.{w} GrpCat.{w})).obj G) ≃ G.H 1 :=
  sorry

end CategoryTheory.Sheaf.NonabelianH1
