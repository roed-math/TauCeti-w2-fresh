/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Terminal

/-!
# Cohomology on a localized site

Cohomology at an object agrees with cohomology of the restricted sheaf on the localized site
when restriction and its left adjoint are exact. On a preorder site, this left adjoint is
extension by zero to the ambient site. For the site of open subsets of a space, the comparison
identifies cohomology on an open subset with cohomology of the restricted sheaf.

The comparison uses the action of the left adjoint on free abelian representable sheaves and
Mathlib's `CategoryTheory.Adjunction.extEquiv` for exact adjunctions.

## Main declarations

* `CategoryTheory.GrothendieckTopology.sheafPullbackFreeYonedaIso`: extension on the source
  objects defining cohomology on an object of the site.
* `CategoryTheory.GrothendieckTopology.cohomologyPresheafEvaluationIsoFunctorOverH`: the comparison,
  natural in the coefficient sheaf.
* `CategoryTheory.Sheaf.cohomologyPresheafObjIsoOverH`: `Hⁿ(U, F) ≅ Hⁿ(F.over U)`.
* `CategoryTheory.Sheaf.cohomologyPresheafObjIsoOverH'`: `Hⁿ(V.left, F) ≅ Hⁿ(V, F.over U)` for
  `V : Over U`.

This comparison transports acyclicity of the restricted sheaf to vanishing of cohomology on
the corresponding object, for instance from affine acyclicity to local vanishing hypotheses.
-/

public section

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology

open TauCeti.CategoryTheory

universe u v w

noncomputable section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify (J.over U) AddCommGrpCat.{v}]
  [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint]

private def extendedSectionsCorepresentation (V : Over U) :
    ((sheafSections J AddCommGrpCat.{v}).obj (op V.left) ⋙ forget AddCommGrpCat).CorepresentableBy
      (((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J).obj
        ((freeYonedaSheafFunctor (J.over U)).obj V)) where
  homEquiv :=
    ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J).homEquiv _ _ |>.trans
      (freeYonedaSheafSectionsEquiv (J.over U) V _).toEquiv
  homEquiv_comp g f := by
    let adj := (Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J
    exact (congrArg (freeYonedaSheafSectionsEquiv (J.over U) V _)
      (adj.homEquiv_naturality_right f g)).trans
      (freeYonedaSheafSectionsEquiv_naturality_right (J.over U) _
        ((J.overPullback AddCommGrpCat.{v} U).map g))

/-- Extension to the ambient site sends the free abelian sheaf on `V : Over U` to the free
abelian sheaf on `V.left`. -/
def sheafPullbackFreeYonedaIso (V : Over U) :
    ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J).obj
      ((freeYonedaSheafFunctor (J.over U)).obj V) ≅ (freeYonedaSheafFunctor J).obj V.left :=
  (extendedSectionsCorepresentation J U V).uniqueUpToIso (freeYonedaSheafCorepresentableBy J V.left)

omit [HasSheafify J AddCommGrpCat.{v}] in
private lemma extendedSectionsCorepresentation_homEquiv (V : Over U)
    {G : Sheaf J AddCommGrpCat.{v}}
    (h : ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J).obj
      ((freeYonedaSheafFunctor (J.over U)).obj V) ⟶ G) :
    (extendedSectionsCorepresentation J U V).homEquiv h =
      freeYonedaSheafSectionsEquiv (J.over U) V _
        (((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J).homEquiv
          _ _ h) :=
  (rfl)

private lemma extendedSectionsCorepresentation_homEquiv_sheafPullbackFreeYonedaIso_hom_comp
    (V : Over U) {G : Sheaf J AddCommGrpCat.{v}} (k : (freeYonedaSheafFunctor J).obj V.left ⟶ G) :
    (extendedSectionsCorepresentation J U V).homEquiv
        ((sheafPullbackFreeYonedaIso J U V).hom ≫ k) =
      freeYonedaSheafSectionsEquiv J V.left G k := by
  have h :
      (extendedSectionsCorepresentation J U V).homEquiv (sheafPullbackFreeYonedaIso J U V).hom =
        (freeYonedaSheafCorepresentableBy J V.left).homEquiv (𝟙 _) :=
    Equiv.apply_symm_apply _ _
  rw [Functor.CorepresentableBy.homEquiv_comp, h, ← Functor.CorepresentableBy.homEquiv_comp,
    Category.id_comp, freeYonedaSheafCorepresentableBy_homEquiv]

/-- The isomorphism `sheafPullbackFreeYonedaIso` is natural in `V : Over U`. -/
@[reassoc]
lemma sheafPullbackFreeYonedaIso_hom_naturality {V W : Over U} (g : V ⟶ W) :
    ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J).map
        ((freeYonedaSheafFunctor (J.over U)).map g) ≫ (sheafPullbackFreeYonedaIso J U W).hom =
      (sheafPullbackFreeYonedaIso J U V).hom ≫ (freeYonedaSheafFunctor J).map g.left := by
  apply (extendedSectionsCorepresentation J U V).homEquiv.injective
  have hW := extendedSectionsCorepresentation_homEquiv_sheafPullbackFreeYonedaIso_hom_comp J U W
    (𝟙 _)
  rw [Category.comp_id] at hW
  rw [extendedSectionsCorepresentation_homEquiv_sheafPullbackFreeYonedaIso_hom_comp,
    ← Category.comp_id ((freeYonedaSheafFunctor J).map g.left),
    freeYonedaSheafSectionsEquiv_naturality_left, ← hW,
    extendedSectionsCorepresentation_homEquiv,
    extendedSectionsCorepresentation_homEquiv, Adjunction.homEquiv_naturality_left,
    freeYonedaSheafSectionsEquiv_naturality_left]
  rfl

end

local instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
    [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint] :
    ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J).IsLeftAdjoint :=
  ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J).isLeftAdjoint

/-- Restriction of abelian sheaves to a localized site is additive. -/
instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C) :
    (J.overPullback AddCommGrpCat.{v} U).Additive where
  map_add := rfl

noncomputable section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify (J.over U) AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
  [HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{v})]
  [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint]
  [PreservesFiniteColimits (J.overPullback AddCommGrpCat.{v} U)]
  [PreservesFiniteLimits ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J)]

local instance : ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Under an exact restriction adjunction, cohomology at `V.left` agrees with cohomology at
`V : Over U` of the restricted sheaf on the localized site, naturally in the coefficient sheaf. -/
def cohomologyPresheafEvaluationIsoOver (n : ℕ) (V : Over U) :
    _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor J n ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op V.left) ≅
    J.overPullback AddCommGrpCat.{v} U ⋙
      _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor (J.over U) n ⋙
        (evaluation (Over U)ᵒᵖ AddCommGrpCat.{w}).obj (op V) := by
  rw [cohomologyPresheafFunctor_eq, cohomologyPresheafFunctor_eq]
  exact (Abelian.extFunctor n).mapIso (sheafPullbackFreeYonedaIso J U V).op ≪≫
    NatIso.ofComponents
      (fun F ↦ AddEquiv.toAddCommGrpIso
        (((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J).extEquiv))
      (by
        intro F G f
        ext x
        let adj := (Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J
        exact adj.extEquiv_naturality_right₀ x f)

/-- The comparison `cohomologyPresheafEvaluationIsoOver` is natural in `V : Over U`: it carries the
restriction maps of the cohomology presheaf of `F` along the morphisms `g.left` to those of the
cohomology presheaf of the restriction of `F` along `g`. -/
@[reassoc]
lemma cohomologyPresheafEvaluationIsoOver_hom_app_naturality (n : ℕ) {V W : Over U} (g : V ⟶ W)
    (F : Sheaf J AddCommGrpCat.{v}) :
    (F.cohomologyPresheaf n).map g.left.op ≫
        (cohomologyPresheafEvaluationIsoOver J U n V).hom.app F =
      (cohomologyPresheafEvaluationIsoOver J U n W).hom.app F ≫
        (((J.overPullback AddCommGrpCat.{v} U).obj F).cohomologyPresheaf n).map g.op := by
  ext x
  -- The cohomology group `Hⁿ(W.left, F)` is by definition `Ext(ℤ[W.left], F)`.
  obtain ⟨y, rfl⟩ : ∃ y : Abelian.Ext ((freeYonedaSheafFunctor J).obj W.left) F n, y = x :=
    ⟨x, rfl⟩
  have h := ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J
    ).extEquiv_naturality_left₀ ((freeYonedaSheafFunctor (J.over U)).map g)
      ((Abelian.Ext.mk₀ (sheafPullbackFreeYonedaIso J U W).hom).comp y (zero_add n))
  rw [Abelian.Ext.mk₀_comp_mk₀_assoc, sheafPullbackFreeYonedaIso_hom_naturality,
    ← Abelian.Ext.mk₀_comp_mk₀_assoc] at h
  -- Both sides of the goal unfold, through `cohomologyPresheafFunctor_eq` and the components of
  -- `cohomologyPresheafEvaluationIsoOver`, to the two sides of `h`.
  exact h

/-- Under an exact restriction adjunction, cohomology at `U` agrees with the cohomology of the
restricted sheaf, naturally in the coefficient sheaf. -/
def cohomologyPresheafEvaluationIsoFunctorOverH (n : ℕ) :
    _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor J n ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U) ≅
    J.overPullback AddCommGrpCat.{v} U ⋙ _root_.CategoryTheory.Sheaf.functorH (J.over U) n :=
  cohomologyPresheafEvaluationIsoOver J U n (Over.mk (𝟙 U)) ≪≫
    Functor.isoWhiskerLeft (J.overPullback AddCommGrpCat.{v} U)
      (_root_.CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH (J.over U) n
        (Over.mkIdTerminal (X := U)))

end

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- Under an exact restriction adjunction, cohomology at an object is the cohomology of the
restricted sheaf on the localized site. -/
noncomputable def cohomologyPresheafObjIsoOverH (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{v})]
    [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint]
    [PreservesFiniteColimits (J.overPullback AddCommGrpCat.{v} U)]
    [PreservesFiniteLimits ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J)] :
    H' F n U ≅ AddCommGrpCat.of (H (F.over U) n) :=
  (J.cohomologyPresheafEvaluationIsoFunctorOverH U n).app F

/-- Under an exact restriction adjunction, cohomology at `V.left` is the cohomology at
`V : Over U` of the restricted sheaf on the localized site. -/
noncomputable def cohomologyPresheafObjIsoOverH' (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U : C}
    (V : Over U) [HasSheafify (J.over U) AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{v})]
    [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint]
    [PreservesFiniteColimits (J.overPullback AddCommGrpCat.{v} U)]
    [PreservesFiniteLimits ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J)] :
    H' F n V.left ≅ H' (F.over U) n V :=
  (J.cohomologyPresheafEvaluationIsoOver U n V).app F

/-- The comparison `cohomologyPresheafObjIsoOverH'` is natural in `V : Over U`. -/
@[reassoc]
lemma cohomologyPresheafObjIsoOverH'_hom_naturality (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)
    {U : C} {V W : Over U} (g : V ⟶ W) [HasSheafify (J.over U) AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{v})]
    [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint]
    [PreservesFiniteColimits (J.overPullback AddCommGrpCat.{v} U)]
    [PreservesFiniteLimits ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J)] :
    (F.cohomologyPresheaf n).map g.left.op ≫ (F.cohomologyPresheafObjIsoOverH' n V).hom =
      (F.cohomologyPresheafObjIsoOverH' n W).hom ≫ ((F.over U).cohomologyPresheaf n).map g.op :=
  J.cohomologyPresheafEvaluationIsoOver_hom_app_naturality U n g F

/-- The inverse of `cohomologyPresheafObjIsoOverH'` is natural in `V : Over U`. -/
@[reassoc]
lemma cohomologyPresheafObjIsoOverH'_inv_naturality (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)
    {U : C} {V W : Over U} (g : V ⟶ W) [HasSheafify (J.over U) AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{v})]
    [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint]
    [PreservesFiniteColimits (J.overPullback AddCommGrpCat.{v} U)]
    [PreservesFiniteLimits ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J)] :
    ((F.over U).cohomologyPresheaf n).map g.op ≫ (F.cohomologyPresheafObjIsoOverH' n V).inv =
      (F.cohomologyPresheafObjIsoOverH' n W).inv ≫ (F.cohomologyPresheaf n).map g.left.op := by
  rw [Iso.comp_inv_eq, Category.assoc, cohomologyPresheafObjIsoOverH'_hom_naturality,
    Iso.inv_hom_id_assoc]

end CategoryTheory.Sheaf
