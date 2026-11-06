/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Tensor products of cokernels in a closed category

In a braided closed category, tensoring on either side is a left adjoint (on the right by the
braiding, an instance in Mathlib), so it preserves cokernels. This file uses this to compute the
tensor product of two cokernels `coker (f : A' ⟶ A) ⊗ coker (g : B' ⟶ B)` in the situation of a
filtered multiplication: if `A ◁ g` factors through `f ▷ B`, then `coker f ◁ g = 0`, and the tensor
product of the two cokernels is the cokernel of `f ▷ B` (`TauCeti.cokernelTensorCokernelIso`).

For the graded pieces of a filtration with a multiplication, such as the pole filtration
`𝒪(aD) ⟶ 𝒪((a + 1)D)` of an effective Cartier divisor, this says that the multiplication passes to
the graded pieces.
-/

public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace TauCeti

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  [Preadditive C] [HasCokernels C] {A' A B' B : C} (f : A' ⟶ A) (g : B' ⟶ B)

/-- If `A ◁ g` factors through `f ▷ B`, then `g` becomes zero after tensoring with `coker f`. -/
theorem cokernel_whiskerLeft_eq_zero {h : A ⊗ B' ⟶ A' ⊗ B} (hgf : A ◁ g = h ≫ f ▷ B) :
    cokernel f ◁ g = 0 := by
  have : Epi ((tensorRight B').map (cokernel.π f)) := inferInstance
  rw [← cancel_epi ((tensorRight B').map (cokernel.π f))]
  change cokernel.π f ▷ B' ≫ _ = _
  rw [← whisker_exchange, hgf, Category.assoc, ← comp_whiskerRight, cokernel.condition, comp_zero]
  change h ≫ (tensorRight B).map 0 = 0
  rw [Functor.map_zero, comp_zero]

/-- **The tensor product of two cokernels in a filtered situation**: if `A ◁ g` factors through
`f ▷ B`, then `coker f ⊗ coker g ≅ coker (f ▷ B)`. Tensoring with `coker f` identifies
`coker f ⊗ coker g` with the cokernel of `coker f ◁ g`, which is zero
(`TauCeti.cokernel_whiskerLeft_eq_zero`), and `coker f ⊗ B` is the cokernel of `f ▷ B`. -/
def cokernelTensorCokernelIso {h : A ⊗ B' ⟶ A' ⊗ B} (hgf : A ◁ g = h ≫ f ▷ B) :
    cokernel f ⊗ cokernel g ≅ cokernel (f ▷ B) :=
  PreservesCokernel.iso (tensorLeft (cokernel f)) g ≪≫
    cokernelIsoOfEq (cokernel_whiskerLeft_eq_zero f g hgf) ≪≫ cokernelZeroIsoTarget ≪≫
    PreservesCokernel.iso (tensorRight B) f

/-- The identification `coker f ⊗ coker g ≅ coker (f ▷ B)` is induced by the projections: it sends
`π_f ⊗ π_g` to the projection of `A ⊗ B` onto `coker (f ▷ B)`. -/
@[reassoc (attr := simp)]
theorem tensorHom_π_cokernelTensorCokernelIso_hom {h : A ⊗ B' ⟶ A' ⊗ B}
    (hgf : A ◁ g = h ≫ f ▷ B) :
    (cokernel.π f ⊗ₘ cokernel.π g) ≫ (cokernelTensorCokernelIso f g hgf).hom =
      cokernel.π (f ▷ B) := by
  rw [tensorHom_def', Category.assoc, whisker_exchange_assoc, cokernelTensorCokernelIso,
    Iso.trans_hom, Iso.trans_hom, Iso.trans_hom]
  have hL := PreservesCokernel.π_iso_hom (tensorLeft (cokernel f)) g
  have hR := PreservesCokernel.π_iso_hom (tensorRight B) f
  change cokernel f ◁ cokernel.π g ≫ _ = cokernel.π (cokernel f ◁ g) at hL
  rw [reassoc_of% hL, π_comp_cokernelIsoOfEq_hom_assoc]
  simpa [cokernelZeroIsoTarget] using hR

end

end TauCeti
