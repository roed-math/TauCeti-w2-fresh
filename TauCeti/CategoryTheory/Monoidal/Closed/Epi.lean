/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Tensor products of epimorphisms in braided closed monoidal categories

In a closed monoidal category tensoring on the left is a left adjoint, so it preserves
epimorphisms; in a braided one, tensoring on the right is conjugate to it under the braiding.
Hence the tensor product `f ⊗ₘ g` of two epimorphisms is an epimorphism.

## Main declarations

* `TauCeti.MonoidalClosed.epi_whiskerRight`: `f ▷ Z` is an epimorphism when `f` is;
* `TauCeti.MonoidalClosed.epi_tensorHom`: `f ⊗ₘ g` is an epimorphism when `f` and `g` are.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.MonoidalClosed

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

/-- In a braided closed monoidal category, whiskering an epimorphism on the right gives an
epimorphism: it is conjugate under the braiding to whiskering on the left, and tensoring on the
left is a left adjoint. -/
theorem epi_whiskerRight {A B : C} (f : A ⟶ B) [Epi f] (Z : C) : Epi (f ▷ Z) := by
  rw [(Iso.eq_comp_inv _).mpr (BraidedCategory.braiding_naturality_left f Z)]
  have : Epi (Z ◁ f) := (tensorLeft Z).map_epi f
  infer_instance

/-- In a braided closed monoidal category, the tensor product of two epimorphisms is an
epimorphism. -/
theorem epi_tensorHom {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B') [Epi f] [Epi g] :
    Epi (f ⊗ₘ g) := by
  have := epi_whiskerRight f A'
  have : Epi (B ◁ g) := (tensorLeft B).map_epi g
  rw [tensorHom_def]
  infer_instance

end TauCeti.MonoidalClosed
