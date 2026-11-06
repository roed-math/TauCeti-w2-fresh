/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# The sections functor of sheaves

For a preadditive category `A`, the functor `(sheafSections J A).obj X` taking the sections of an
`A`-valued sheaf over an object `X` of the site is additive
(`CategoryTheory.sheafSections_obj_additive`), since it is evaluation of the underlying presheaf
at `X`.
-/

public section

open CategoryTheory

namespace CategoryTheory

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)

/-- The functor of sections over an object of the site is additive. -/
instance sheafSections_obj_additive {A : Type*} [Category* A] [Preadditive A] (X : Cᵒᵖ) :
    ((sheafSections J A).obj X).Additive :=
  inferInstanceAs (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj X).Additive

end CategoryTheory
