/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finite subsets of filtered colimits in concrete categories

Let `c` be a colimit cocone of a filtered diagram `F` in a concrete category whose forgetful functor
preserves the colimit of `F`. Every element of `c.pt` comes from some stage
(`CategoryTheory.Limits.Concrete.isColimit_exists_rep`); since the images of the stages are
directed, every finite subset of `c.pt` comes from a single stage.

## Main declarations

* `TauCeti.CategoryTheory.Limits.Concrete.exists_subset_range_of_isColimit`: every finite subset
  of a filtered colimit lies in the image of a single stage.
-/

public section

open CategoryTheory Limits

namespace TauCeti.CategoryTheory.Limits.Concrete

variable {C : Type*} [Category* C] {FC : C → C → Type*} {CC : C → Type*}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] {J : Type*} [Category* J]
  [IsFiltered J] {F : J ⥤ C} [PreservesColimit F (forget C)]

/-- Every finite subset of a filtered colimit in a concrete category, whose forgetful functor
preserves the colimit, lies in the image of a single stage. -/
theorem exists_subset_range_of_isColimit {c : Cocone F} (hc : IsColimit c) {s : Set (ToType c.pt)}
    (hs : s.Finite) : ∃ j, s ⊆ Set.range (c.ι.app j) := by
  have range_le {j k : J} (f : j ⟶ k) : Set.range (c.ι.app j) ⊆ Set.range (c.ι.app k) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨F.map f z, by rw [← ConcreteCategory.comp_apply, c.w]⟩
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨IsFiltered.nonempty.some, Set.empty_subset _⟩
  | @insert x s _ _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep F hc x
    exact ⟨IsFiltered.max i j, Set.insert_subset (range_le (IsFiltered.rightToMax i j) ⟨y, rfl⟩)
      (hi.trans (range_le (IsFiltered.leftToMax i j)))⟩

end TauCeti.CategoryTheory.Limits.Concrete
