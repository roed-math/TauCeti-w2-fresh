/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.CommSq

/-!
# Precomposing lifts in commutative squares

A lift `l : B ⟶ X` in a commutative square `f ≫ p = i ≫ g` precomposes, along a map
`(a, b) : i' ⟶ i` of arrows (`a ≫ i = i' ≫ b`), to the lift `b ≫ l` in the square
`f' ≫ p = i' ≫ g'` with `f' = a ≫ f` and `g' = b ≫ g`.

## Main definitions

* `CategoryTheory.CommSq.LiftStruct.precomp`: the lift `b ≫ l` of the precomposed square.
-/

public section

namespace CategoryTheory.CommSq.LiftStruct

variable {C : Type*} [Category* C] {A B X Y A' B' : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y}
  {g : B ⟶ Y} {sq : CommSq f i p g} {f' : A' ⟶ X} {i' : A' ⟶ B'} {g' : B' ⟶ Y}

/-- Along a map `(a, b)` from `i'` to `i` of arrows, a lift `l` in the square `f ≫ p = i ≫ g`
gives the lift `b ≫ l` in the square `f' ≫ p = i' ≫ g'`, where `f' = a ≫ f` and `g' = b ≫ g`. -/
@[expose, simps]
def precomp (l : sq.LiftStruct) {a : A' ⟶ A} {b : B' ⟶ B} (hab : a ≫ i = i' ≫ b)
    (hf : a ≫ f = f') (hg : b ≫ g = g') (sq' : CommSq f' i' p g') : sq'.LiftStruct where
  l := b ≫ l.l
  fac_left := by rw [← Category.assoc, ← hab, Category.assoc, l.fac_left, hf]
  fac_right := by rw [Category.assoc, l.fac_right, hg]

end CategoryTheory.CommSq.LiftStruct
