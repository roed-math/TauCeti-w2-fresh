/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Swapping nested evaluations in a symmetric monoidal category

Let `f : A ⊗ A' ⟶ 𝟙_ C` and `g : B ⊗ B' ⟶ 𝟙_ C` be pairings to the unit. On `(B ⊗ A) ⊗ (A' ⊗ B')`
the *nested* evaluation applies `f` to the inner factors `A ⊗ A'` and then `g` to the outer factors
`B ⊗ B'`. In a symmetric monoidal category, braiding `B` past `A` and `A'` past `B'` turns it into
the nested evaluation with the roles of `f` and `g` exchanged
(`TauCeti.braiding_tensorHom_braiding_comp_nestedEvaluation`). This is the commutativity input for
products of functionals: if `φ`, `ψ` are functionals on line bundles `L`, `K`, the products
`φ ψ` and `ψ φ`, which are functionals on `K ⊗ L` and `L ⊗ K`, agree through the braiding.

In any monoidal category, a morphism on the outer factor also commutes past an inner evaluation
(`TauCeti.whiskerLeft_whiskerLeft_comp_evaluate`).

## Main results

* `TauCeti.whiskerLeft_whiskerLeft_comp_evaluate`: moving a morphism past an evaluation.
* `TauCeti.nestedEvaluation_eq_tensorHom`: a nested evaluation is a tensor product of
  evaluations after a braiding.
* `TauCeti.braiding_tensorHom_braiding_comp_nestedEvaluation`: swapping nested evaluations.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A morphism `g` acting on the factor `C` commutes past an evaluation `f : A ⊗ B ⟶ 𝟙_ C` of the
other two factors. -/
@[reassoc]
theorem whiskerLeft_whiskerLeft_comp_evaluate {A B X Y : C} (f : A ⊗ B ⟶ 𝟙_ C) (g : X ⟶ Y) :
    A ◁ B ◁ g ≫ (α_ A B Y).inv ≫ f ▷ Y ≫ (λ_ Y).hom =
      ((α_ A B X).inv ≫ f ▷ X ≫ (λ_ X).hom) ≫ g := by
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, leftUnitor_naturality,
    Category.assoc, Category.assoc]

section Symmetric

variable [SymmetricCategory C]

/-- **The nested evaluation as a tensor product**: on `(B ⊗ A) ⊗ (A' ⊗ B')`, evaluating
`f : A ⊗ A' ⟶ 𝟙_ C` on the inner factors and then `g : B ⊗ B' ⟶ 𝟙_ C` on the outer ones is
moving `B'` past `A ⊗ A'` and then evaluating `g ⊗ f`. -/
theorem nestedEvaluation_eq_tensorHom {A A' B B' : C} (f : A ⊗ A' ⟶ 𝟙_ C)
    (g : B ⊗ B' ⟶ 𝟙_ C) :
    (α_ B A (A' ⊗ B')).hom ≫ B ◁ (α_ A A' B').inv ≫ B ◁ (f ▷ B') ≫ B ◁ (λ_ B').hom ≫ g =
      (α_ B A (A' ⊗ B')).hom ≫ B ◁ (α_ A A' B').inv ≫ B ◁ (β_ (A ⊗ A') B').hom ≫
        (α_ B B' (A ⊗ A')).inv ≫ (g ⊗ₘ f) ≫ (λ_ (𝟙_ C)).hom := by
  rw [← braiding_rightUnitor]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc B (f ▷ B'), braiding_naturality_left,
    MonoidalCategory.whiskerLeft_comp_assoc, tensorHom_def', Category.assoc, unitors_equal,
    rightUnitor_naturality]
  monoidal

/-- The rearrangements of `(B ⊗ A) ⊗ (A' ⊗ B')` underlying the two nested evaluations
(`nestedEvaluation_eq_tensorHom`) differ by braiding `B` past `A` and `A'` past `B'`. -/
@[reassoc]
theorem nestedEvaluation_braiding (A A' B B' : C) :
    (α_ B A (A' ⊗ B')).hom ≫ B ◁ (α_ A A' B').inv ≫ B ◁ (β_ (A ⊗ A') B').hom ≫
        (α_ B B' (A ⊗ A')).inv ≫ (β_ (B ⊗ B') (A ⊗ A')).hom =
      ((β_ B A).hom ⊗ₘ (β_ A' B').hom) ≫ (α_ A B (B' ⊗ A')).hom ≫ A ◁ (α_ B B' A').inv ≫
        A ◁ (β_ (B ⊗ B') A').hom ≫ (α_ A A' (B ⊗ B')).inv := by
  have h : ∀ X Y : C, (β_ X Y).inv ≫ (β_ Y X).inv = 𝟙 _ := fun X Y ↦ by
    rw [← SymmetricCategory.braiding_swap_eq_inv_braiding, Iso.hom_inv_id]
  simp only [SymmetricCategory.braiding_swap_eq_inv_braiding, braiding_tensor_right_inv,
    MonoidalCategory.whiskerLeft_comp, braiding_tensor_left_inv, comp_whiskerRight, whisker_assoc,
    Category.assoc, pentagon_inv_inv_hom_hom_inv, pentagon_inv_assoc, Iso.inv_hom_id_assoc,
    whiskerLeft_hom_inv_assoc, whiskerLeft_inv_hom_assoc, tensorHom_def, whiskerRight_tensor,
    tensor_whiskerLeft]
  -- Cancel the crossings of `A` with `B'` and of `A'` with `B'` against their inverses.
  rw [← MonoidalCategory.whiskerLeft_comp_assoc B ((β_ B' A).inv ▷ A'), ← comp_whiskerRight, h,
    id_whiskerRight, MonoidalCategory.whiskerLeft_id, Category.id_comp,
    ← MonoidalCategory.whiskerLeft_comp_assoc B (α_ A B' A').inv, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp,
    ← MonoidalCategory.whiskerLeft_comp_assoc B (A ◁ (β_ B' A').inv),
    ← MonoidalCategory.whiskerLeft_comp, h, MonoidalCategory.whiskerLeft_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp,
    ← MonoidalCategory.whiskerLeft_comp_assoc A (B ◁ (β_ B' A').inv),
    ← MonoidalCategory.whiskerLeft_comp, h, MonoidalCategory.whiskerLeft_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  monoidal

/-- **Swapping nested evaluations**: on `(B ⊗ A) ⊗ (A' ⊗ B')`, evaluating `f : A ⊗ A' ⟶ 𝟙_ C`
on the inner factors and then `g : B ⊗ B' ⟶ 𝟙_ C` on the outer ones is braiding `B` past `A` and
`A'` past `B'`, and then evaluating `g` on the inner factors and `f` on the outer ones. -/
theorem braiding_tensorHom_braiding_comp_nestedEvaluation {A A' B B' : C}
    (f : A ⊗ A' ⟶ 𝟙_ C) (g : B ⊗ B' ⟶ 𝟙_ C) :
    ((β_ B A).hom ⊗ₘ (β_ A' B').hom) ≫ (α_ A B (B' ⊗ A')).hom ≫ A ◁ (α_ B B' A').inv ≫
        A ◁ (g ▷ A') ≫ A ◁ (λ_ A').hom ≫ f =
      (α_ B A (A' ⊗ B')).hom ≫ B ◁ (α_ A A' B').inv ≫ B ◁ (f ▷ B') ≫ B ◁ (λ_ B').hom ≫ g := by
  conv_rhs => rw [nestedEvaluation_eq_tensorHom, unitors_equal, ← braiding_leftUnitor,
    braiding_naturality_assoc, nestedEvaluation_braiding_assoc]
  rw [nestedEvaluation_eq_tensorHom, unitors_equal]

end Symmetric

end TauCeti
