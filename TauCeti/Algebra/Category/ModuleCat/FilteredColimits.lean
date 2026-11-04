/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures

/-!
# Filtered colimits of functors between module categories

For a filtered diagram `D : J ⥤ ModuleCat R ⥤ ModuleCat R`, the value of `colimit D` at a module
`X` is the filtered colimit of the values `(D.obj j).obj X`. So its elements come from stages, and
an element of a stage vanishes in the colimit once it vanishes at a later stage. Consequently maps
between such values that are induced stage by stage by natural maps inherit exactness, and the
vanishing of composites, from the stages. This is how exactness properties of a system of functors,
such as `Ext(R ⧸ Iⁿ, -)`, pass to its colimit, such as local cohomology.

## Main results

* `TauCeti.ModuleCat.exists_colimit_ι_app_eq`: every element of `(colimit D).obj X` comes from a
  stage.
* `TauCeti.ModuleCat.exists_map_app_eq_zero`: an element of a stage that vanishes in the colimit
  vanishes at a later stage.
* `TauCeti.ModuleCat.exists_eq_of_stages`: maps induced stage by stage are exact once every stage
  is.
* `TauCeti.ModuleCat.comp_eq_zero_of_stages`: maps induced stage by stage compose to zero once
  they do at every stage.
-/

public section

universe u

open CategoryTheory Limits

namespace TauCeti.ModuleCat

variable {R : Type u} [Ring R] {J : Type} [SmallCategory J] [IsFiltered J]

/-- Every element of the value at `X` of a filtered colimit of functors between module categories
comes from some stage. -/
theorem exists_colimit_ι_app_eq (D : J ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    (X : ModuleCat.{u} R) (x : (colimit D).obj X) :
    ∃ (j : J) (y : (D.obj j).obj X), (colimit.ι D j).app X y = x := by
  have : PreservesColimit (D ⋙ (evaluation _ _).obj X) (forget (ModuleCat.{u} R)) :=
    have := preservesFilteredColimitsOfSize_shrink.{0, u, 0, u} (forget (ModuleCat.{u} R))
    inferInstance
  obtain ⟨j, y, hy⟩ := Concrete.colimit_exists_rep (D ⋙ (evaluation _ _).obj X)
    ((colimitObjIsoColimitCompEvaluation D X).hom x)
  refine ⟨j, y, ?_⟩
  rw [← colimitObjIsoColimitCompEvaluation_ι_inv, ModuleCat.comp_apply, hy,
    Iso.hom_inv_id_apply]

/-- An element of a stage of a filtered colimit of functors between module categories that
vanishes in the colimit already vanishes at a later stage. -/
theorem exists_map_app_eq_zero (D : J ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    {X : ModuleCat.{u} R} {j : J} (y : (D.obj j).obj X) (hy : (colimit.ι D j).app X y = 0) :
    ∃ (k : J) (i : j ⟶ k), (D.map i).app X y = 0 := by
  have : PreservesColimit (D ⋙ (evaluation _ _).obj X) (forget (ModuleCat.{u} R)) :=
    have := preservesFilteredColimitsOfSize_shrink.{0, u, 0, u} (forget (ModuleCat.{u} R))
    inferInstance
  have h₁ : (colimitObjIsoColimitCompEvaluation D X).inv
      (colimit.ι (D ⋙ (evaluation _ _).obj X) j y) = 0 :=
    (ConcreteCategory.congr_hom (colimitObjIsoColimitCompEvaluation_ι_inv D j X) y).trans hy
  have h : colimit.ι (D ⋙ (evaluation _ _).obj X) j y = 0 := by
    rw [← Iso.inv_hom_id_apply (colimitObjIsoColimitCompEvaluation D X)
      (colimit.ι (D ⋙ (evaluation _ _).obj X) j y), h₁, map_zero]
  exact Concrete.colimit_rep_eq_zero R (D ⋙ (evaluation _ _).obj X) j y h

/-- Exactness passes to filtered colimits of functors between module categories: maps `Φ` and `Ψ`
between values of colimits, induced stage by stage by natural maps `φ` and `ψ`, are exact at the
middle term as soon as every stage is. -/
theorem exists_eq_of_stages {D₁ D₂ D₃ : J ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R}
    {X₁ X₂ X₃ : ModuleCat.{u} R}
    (φ : D₁ ⋙ (evaluation _ _).obj X₁ ⟶ D₂ ⋙ (evaluation _ _).obj X₂)
    (ψ : D₂ ⋙ (evaluation _ _).obj X₂ ⟶ D₃ ⋙ (evaluation _ _).obj X₃)
    (Φ : (colimit D₁).obj X₁ ⟶ (colimit D₂).obj X₂) (Ψ : (colimit D₂).obj X₂ ⟶ (colimit D₃).obj X₃)
    (hΦ : ∀ j, (colimit.ι D₁ j).app X₁ ≫ Φ = φ.app j ≫ (colimit.ι D₂ j).app X₂)
    (hΨ : ∀ j, (colimit.ι D₂ j).app X₂ ≫ Ψ = ψ.app j ≫ (colimit.ι D₃ j).app X₃)
    (h : ∀ (j : J) (y : (D₂.obj j).obj X₂), ψ.app j y = 0 → ∃ x, φ.app j x = y)
    (y : (colimit D₂).obj X₂) (hy : Ψ y = 0) : ∃ x, Φ x = y := by
  obtain ⟨j, y, rfl⟩ := exists_colimit_ι_app_eq D₂ X₂ y
  have h₀ : (colimit.ι D₃ j).app X₃ (ψ.app j y) = 0 :=
    (ConcreteCategory.congr_hom (hΨ j) y).symm.trans hy
  obtain ⟨k, i, hk⟩ := exists_map_app_eq_zero D₃ _ h₀
  have hk' : ψ.app k ((D₂.map i).app X₂ y) = 0 :=
    (ConcreteCategory.congr_hom (ψ.naturality i) y).trans hk
  obtain ⟨x, hx⟩ := h k _ hk'
  refine ⟨(colimit.ι D₁ k).app X₁ x, ?_⟩
  refine (ConcreteCategory.congr_hom (hΦ k) x).trans ?_
  change (colimit.ι D₂ k).app X₂ (φ.app k x) = _
  rw [hx]
  exact ConcreteCategory.congr_hom (congrArg (NatTrans.app · X₂) (colimit.w D₂ i)) y

/-- A composite of maps between values of filtered colimits of functors between module categories,
induced stage by stage by natural maps `φ` and `ψ`, vanishes as soon as `φ ≫ ψ` vanishes at every
stage. -/
theorem comp_eq_zero_of_stages {D₁ D₂ D₃ : J ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R}
    {X₁ X₂ X₃ : ModuleCat.{u} R}
    (φ : D₁ ⋙ (evaluation _ _).obj X₁ ⟶ D₂ ⋙ (evaluation _ _).obj X₂)
    (ψ : D₂ ⋙ (evaluation _ _).obj X₂ ⟶ D₃ ⋙ (evaluation _ _).obj X₃)
    (Φ : (colimit D₁).obj X₁ ⟶ (colimit D₂).obj X₂) (Ψ : (colimit D₂).obj X₂ ⟶ (colimit D₃).obj X₃)
    (hΦ : ∀ j, (colimit.ι D₁ j).app X₁ ≫ Φ = φ.app j ≫ (colimit.ι D₂ j).app X₂)
    (hΨ : ∀ j, (colimit.ι D₂ j).app X₂ ≫ Ψ = ψ.app j ≫ (colimit.ι D₃ j).app X₃)
    (h : ∀ j, φ.app j ≫ ψ.app j = 0) : Φ ≫ Ψ = 0 := by
  ext x
  obtain ⟨j, x, rfl⟩ := exists_colimit_ι_app_eq D₁ X₁ x
  have hj : (colimit.ι D₁ j).app X₁ ≫ Φ ≫ Ψ = 0 := by
    rw [reassoc_of% (hΦ j), hΨ j, reassoc_of% (h j), zero_comp]
  exact ConcreteCategory.congr_hom hj x

end TauCeti.ModuleCat
