/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Flat

import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-!
# Left Kan extension along a flat functor into a large category

Mathlib's `CategoryTheory.lan_preservesFiniteLimits_of_flat` shows that left Kan extension of
presheaves along a representably flat functor `F : C ⥤ D` is exact when `C` and `D` are both
small. The proof only uses that the categories of costructured arrows over the objects of `Dᵒᵖ`
are small relative to the coefficient category, so it applies verbatim when `C` is small and `D`
is only locally small, as for the inclusion of the open subsets of a scheme into the category of
schemes étale over it, and to large `C` and `D` with coefficients in a larger universe, as for the
inclusion of the small étale site of a scheme into its big étale site.

## Main declarations

* `TauCeti.CategoryTheory.lanCompEvaluationIsoColim`: the value at `X` of the left Kan extension
  along `F` is the colimit over the costructured arrows over `X`, naturally in the functor.
* `TauCeti.CategoryTheory.lan_preservesFiniteLimits_of_flat`: if `F : C ⥤ D` is representably
  flat and its categories of costructured arrows are small relative to a concrete category `E`
  in which filtered colimits commute with finite limits, then `F.op.lan` preserves finite limits
  of presheaves with values in `E`.
-/

public section

open CategoryTheory Limits Functor

universe w u₁ v₁ u₂ v₂ u₃

namespace TauCeti.CategoryTheory

section

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (E : Type*) [Category* E]

/-- The value at `X` of the left Kan extension along `F` is the colimit over the costructured
arrows over `X`, naturally in the functor being extended. This is
`CategoryTheory.lanEvaluationIsoColim` without its smallness assumptions. -/
noncomputable def lanCompEvaluationIsoColim (F : C ⥤ D) (X : D)
    [∀ X : D, HasColimitsOfShape (CostructuredArrow F X) E] :
    F.lan ⋙ (evaluation D E).obj X ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
  (NatIso.ofComponents (fun G ↦ (F.leftKanExtensionObjIsoColimit G X).symm) fun {G₁ G₂} φ ↦
    colimit.hom_ext fun T ↦ by
      dsimp only [Functor.lan]
      simp only [Functor.comp_obj, Functor.whiskeringLeft_obj_obj, colim_obj, Functor.comp_map,
        Functor.whiskeringLeft_obj_map, Iso.symm_hom, ι_leftKanExtensionObjIsoColimit_inv_assoc,
        evaluation_obj_map]
      rw [NatTrans.naturality, descOfIsLeftKanExtension_fac_app_assoc, colim_map,
        ι_colimMap_assoc]
      simp).symm




end

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (E : Type u₃) [Category.{w} E]
  {FE : E → E → Type*} {CE : E → Type w} [∀ X Y, FunLike (FE X Y) (CE X) (CE Y)]
  [ConcreteCategory E FE] [HasFiniteLimits E] [HasColimitsOfSize.{v₁, max u₁ v₂} E]
  [PreservesFiniteLimits (forget E)] [(forget E).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{v₁, max u₁ v₂} (forget E)]

/-- If `F : C ⥤ D` is a representably flat functor whose categories of costructured arrows are
small relative to the concrete category `E`, then the functor `Lan F.op` that takes presheaves over
`C` to presheaves over `D` preserves finite limits. This is
`CategoryTheory.lan_preservesFiniteLimits_of_flat` without the assumption that `C` and `D` are
small: it applies to a small `C` and a locally small `D`, and to the inclusion of the small étale
site of a scheme into its big site. -/
instance lan_preservesFiniteLimits_of_flat (F : C ⥤ D) [RepresentablyFlat F]
    [∀ K : Dᵒᵖ, Small.{w} (CostructuredArrow F.op K)] :
    PreservesFiniteLimits (F.op.lan : _ ⥤ Dᵒᵖ ⥤ E) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{0}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation (F.op.lan : (Cᵒᵖ ⥤ E) ⥤ Dᵒᵖ ⥤ E) J
  intro K
  have : IsFiltered (CostructuredArrow F.op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (Opposite.unop K))
  exact preservesLimitsOfShape_of_natIso (lanCompEvaluationIsoColim E F.op K).symm

end TauCeti.CategoryTheory
