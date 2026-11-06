/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Comparison
public import TauCeti.AlgebraicGeometry.Sites.SmallEtaleBaseChange
public import TauCeti.CategoryTheory.Functor.Flat
public import TauCeti.CategoryTheory.Sites.ConstantSheaf
public import TauCeti.CategoryTheory.Sites.PullbackFullyFaithful

/-!
# The comparison morphisms from the big sites of a scheme to its small étale site

The inclusion `Scheme.Etale.forget X : X.Etale ⥤ Over X` of the small étale site of a scheme `X`
into its big étale site is continuous and representably flat, so it induces a morphism of topoi
`π_X : Sh((Sch/X)_ét) ⥤ Sh(X_ét)`, given here through its exact inverse image `piX X A`, the
étale sheafification of the left Kan extension of a sheaf on `X_ét`; it sends constant sheaves to
constant sheaves. Composing with the inverse
image `ε⁻¹ = epsilonFppfEtale X A` from the big étale site to the big fppf site gives the inverse
image `aX X A` of the morphism of topoi `a_X : Sh((Sch/X)_fppf) ⥤ Sh(X_ét)` (Stacks, Section 59.100
(0DDK)).

Both inverse images commute with base change along a morphism `g : Y ⟶ X`, where the small étale
site changes by the pullback along `Etale.pullback g` and the big sites by restriction. Since the
inclusion of the small étale site is moreover fully faithful and cocontinuous, `π_X⁻¹` is fully
faithful, and the sections of `π_X⁻¹ F` over a scheme `h : T ⟶ X` are the global sections
`Γ(T_ét, h⁻¹ F)` of the pullback of `F` to the small étale site of `T`.

## Main declarations

* `AlgebraicGeometry.Scheme.coverPreserving_etaleForget`: étale coverings in `X.Etale` are étale
  coverings of schemes over `X`.
* `AlgebraicGeometry.Scheme.piX`, `piXAdjunction`: the inverse image of `π_X` and its adjunction
  with the direct image, which restricts a big étale sheaf to the small étale site.
* `AlgebraicGeometry.Scheme.aX`, `aXAdjunction`: the inverse image of `a_X` and its adjunction with
  the direct image.
* `AlgebraicGeometry.Scheme.constantSheafCompPiXIso`, `constantSheafCompAXIso`: `π_X⁻¹` and `a_X⁻¹`
  send constant sheaves to constant sheaves.
* `AlgebraicGeometry.Scheme.piXBaseChangeIso`, `aXBaseChangeIso`: `π_X⁻¹` and `a_X⁻¹` commute with
  base change.
* `AlgebraicGeometry.Scheme.fullyFaithfulPiX`: `π_X⁻¹` is fully faithful.
* `AlgebraicGeometry.Scheme.piXObjIso`: the sections of `π_X⁻¹ F` over `h : T ⟶ X` are
  `Γ(T_ét, h⁻¹ F)`.
* `AlgebraicGeometry.Scheme.aXObjIsoOfIsSheaf`: when `π_X⁻¹ F` is an fppf sheaf, the sections of
  `a_X⁻¹ F` over `h : T ⟶ X` are `Γ(T_ét, h⁻¹ F)`.

## References

* [Stacks Project, Section 59.100 (0DDK)](https://stacks.math.columbia.edu/tag/0DDK)
-/

public section

open CategoryTheory Limits GrothendieckTopology Opposite

universe w w' u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The inclusion of the small étale site of `X` into its big étale site sends étale coverings to
étale coverings. -/
theorem coverPreserving_etaleForget :
    CoverPreserving X.smallEtaleTopology (etaleTopology.over X) (Etale.forget X) := by
  have : MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Etale :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  exact @Functor.coverPreserving_restrictedTopology _ _ _ _ (Etale.forget X) (etaleTopology.over X)
    (locallyCoverDense_of_le X le_rfl) _ _

/-- The inclusion of the small étale site of `X` into its big étale site is representably flat,
since it preserves finite limits. -/
instance : RepresentablyFlat (Etale.forget X) :=
  flat_of_preservesFiniteLimits _

/-- The inclusion of the small étale site of `X` into its big étale site is final. -/
instance : (Etale.forget X).Final :=
  final_of_representablyFlat _

/-- The inclusion of the small étale site of `X` into its big étale site is continuous. -/
instance : (Etale.forget X).IsContinuous X.smallEtaleTopology (etaleTopology.over X) :=
  Functor.isContinuous_iff_coverPreserving.mpr (coverPreserving_etaleForget X)

/-- The inclusion of the small étale site of `X` into its big étale site is cocontinuous: an étale
covering of a scheme étale over `X` consists of schemes étale over `X`. -/
instance : (Etale.forget X).IsCocontinuous X.smallEtaleTopology (etaleTopology.over X) := by
  have : MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Etale :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  -- Instance search does not find the cocontinuity of the inclusion for the restricted topology
  -- here, so the instance is applied to the local cover density explicitly.
  exact @Functor.instIsCocontinuousRestrictedTopology _ _ _ _ (Etale.forget X)
    (etaleTopology.over X) (locallyCoverDense_of_le X le_rfl)

section

variable (A : Type w) [Category.{w'} A]
  [∀ F : X.Etaleᵒᵖ ⥤ A, (Etale.forget X).op.HasLeftKanExtension F]

section Etale

variable [HasWeakSheafify (etaleTopology.over X) A]

/-- The inverse image of the morphism of topoi `π_X` from the big étale site to the small étale
site of `X`: the pullback of sheaves along the inclusion `X.Etale ⥤ Over X`. -/
@[expose] noncomputable def piX : Sheaf X.smallEtaleTopology A ⥤ Sheaf (etaleTopology.over X) A :=
  (Etale.forget X).sheafPullback A _ _

/-- The inverse image `π_X⁻¹` is left adjoint to the direct image, which restricts a sheaf on the
big étale site to the small étale site. -/
@[expose] noncomputable def piXAdjunction :
    piX X A ⊣ (Etale.forget X).sheafPushforwardContinuous A _ (etaleTopology.over X) :=
  (Etale.forget X).sheafAdjunctionContinuous A _ _

/-- The inverse image `π_X⁻¹` is a left adjoint. -/
instance : (piX X A).IsLeftAdjoint :=
  (piXAdjunction X A).isLeftAdjoint

/-- The inverse image `π_X⁻¹` sends the constant sheaf on the small étale site to the constant
sheaf on the big étale site. -/
noncomputable def constantSheafCompPiXIso [HasWeakSheafify X.smallEtaleTopology A] :
    constantSheaf _ A ⋙ piX X A ≅ constantSheaf _ A :=
  (Etale.forget X).constantSheafCompSheafPullbackIso A _ _

/-- The comparison `M_big ⟶ π_X⁻¹ M_small` of constant sheaves is the comparison of constant
sheaves for the pullback along `Etale.forget X`. -/
lemma constantSheafCompPiXIso_inv_app [HasWeakSheafify X.smallEtaleTopology A] (M : A) :
    (constantSheafCompPiXIso X A).inv.app M =
      ((Etale.forget X).sheafPullbackConstantSheafIso A _ _ M).inv := by
  rw [constantSheafCompPiXIso, Functor.constantSheafCompSheafPullbackIso_inv_app]

end Etale

variable [HasWeakSheafify (etaleTopology.over X) A] [HasWeakSheafify (fppfTopology.over X) A]

/-- The inverse image of the morphism of topoi `a_X` from the big fppf site to the small étale
site of `X`: the composite of `π_X⁻¹` and `ε⁻¹`. Stacks, Section 59.100 (0DDK). -/
@[expose] noncomputable def aX : Sheaf X.smallEtaleTopology A ⥤ Sheaf (fppfTopology.over X) A :=
  piX X A ⋙ epsilonFppfEtale X A

/-- The inverse image `a_X⁻¹` is left adjoint to the direct image, which regards a sheaf on the big
fppf site as a sheaf on the big étale site and restricts it to the small étale site. -/
noncomputable def aXAdjunction :
    aX X A ⊣ sheafDirectImageOfLE A (etaleTopology_over_le_fppfTopology_over X) ⋙
      (Etale.forget X).sheafPushforwardContinuous A _ (etaleTopology.over X) :=
  (piXAdjunction X A).comp (epsilonFppfEtaleAdjunction X A)

/-- The unit of `a_X⁻¹ ⊣ a_{X,*}` is the unit of `π_X⁻¹ ⊣ π_{X,*}` followed by the direct image of
the unit of `ε⁻¹ ⊣ ε_*`. -/
lemma aXAdjunction_unit_app (F : Sheaf X.smallEtaleTopology A) :
    (aXAdjunction X A).unit.app F = (piXAdjunction X A).unit.app F ≫
      ((Etale.forget X).sheafPushforwardContinuous A _ (etaleTopology.over X)).map
        ((epsilonFppfEtaleAdjunction X A).unit.app ((piX X A).obj F)) :=
  Adjunction.comp_unit_app _ _ _

/-- The inverse image `a_X⁻¹` is a left adjoint. -/
instance : (aX X A).IsLeftAdjoint :=
  (aXAdjunction X A).isLeftAdjoint

/-- The inverse image `a_X⁻¹` sends the constant sheaf on the small étale site to the constant
sheaf on the big fppf site. -/
noncomputable def constantSheafCompAXIso [HasWeakSheafify X.smallEtaleTopology A] :
    constantSheaf _ A ⋙ aX X A ≅ constantSheaf _ A :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (constantSheafCompPiXIso X A) _ ≪≫
    constantSheafCompEpsilonFppfEtaleIso X A

/-- The comparison `M_fppf ⟶ a_X⁻¹ M_ét` of constant sheaves is the comparison for `ε` followed by
`ε⁻¹` of the comparison for `π_X`. -/
lemma constantSheafCompAXIso_inv_app [HasWeakSheafify X.smallEtaleTopology A] (M : A) :
    (constantSheafCompAXIso X A).inv.app M =
      (constantSheafCompEpsilonFppfEtaleIso X A).inv.app M ≫
        (epsilonFppfEtale X A).map ((constantSheafCompPiXIso X A).inv.app M) := by
  -- `simp` does not unfold `Iso.trans` here; the components of the associator are identities, so
  -- the composite reduces to the right-hand side followed by an identity.
  exact Category.comp_id _

/-- The inverse image `a_X⁻¹` is exact if `π_X⁻¹` is. -/
instance [HasFiniteLimits A] [HasSheafify (fppfTopology.over X) A]
    [PreservesFiniteLimits (piX X A)] : PreservesFiniteLimits (aX X A) := by
  dsimp only [aX]
  infer_instance

end

section BaseChange

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X) (A : Type w) [Category.{w'} A]
  [∀ F : X.Etaleᵒᵖ ⥤ A, (Etale.forget X).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ A, (Etale.forget Y).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ A, (Etale.pullback g).op.HasLeftKanExtension F]
  [HasWeakSheafify (etaleTopology.over X) A] [HasWeakSheafify (etaleTopology.over Y) A]
  [HasWeakSheafify Y.smallEtaleTopology A]

/-- The direct image of `π_Y` followed by the direct image of the small étale base change
`g_ét : Y_ét ⥤ X_ét` is the direct image along the big-site base change `Over.pullback g` followed
by the direct image of `π_X`, since base change of schemes étale over `X` is base change of schemes
over `X`. -/
noncomputable def piXDirectImageBaseChangeIso :
    (Etale.forget Y).sheafPushforwardContinuous A Y.smallEtaleTopology (etaleTopology.over Y) ⋙
        (Etale.pullback g).sheafPushforwardContinuous A X.smallEtaleTopology Y.smallEtaleTopology ≅
      (CategoryTheory.Over.pullback g).sheafPushforwardContinuous A (etaleTopology.over X)
          (etaleTopology.over Y) ⋙
        (Etale.forget X).sheafPushforwardContinuous A X.smallEtaleTopology (etaleTopology.over X) :=
  have := Functor.isContinuous_comp (Etale.forget X) (CategoryTheory.Over.pullback g)
    X.smallEtaleTopology (etaleTopology.over X) (etaleTopology.over Y)
  Functor.sheafPushforwardContinuousComp' (Etale.pullbackCompForgetIso g) _ _ _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp _ _ _ _ _ _).symm

/-- **The inverse image `π_X⁻¹` commutes with base change**: for a morphism `g : Y ⟶ X`,
restricting `π_X⁻¹ F` to the big étale site over `Y` is `π_Y⁻¹` of the pullback of `F` to the
small étale site of `Y`. -/
noncomputable def piXBaseChangeIso :
    piX X A ⋙ etaleTopology.overMapPullback A g ≅
      (Etale.pullback g).sheafPullback A X.smallEtaleTopology Y.smallEtaleTopology ⋙ piX Y A :=
  (conjugateIsoEquiv
    (((Etale.pullback g).sheafAdjunctionContinuous A _ _).comp (piXAdjunction Y A))
    ((piXAdjunction X A).comp
      ((CategoryTheory.Over.mapPullbackAdj g).sheafPushforwardContinuous (E := A) _ _))).symm
    (piXDirectImageBaseChangeIso g A)

variable [HasWeakSheafify (fppfTopology.over X) A] [HasWeakSheafify (fppfTopology.over Y) A]
  [∀ F : (Over Y)ᵒᵖ ⥤ A, (Over.map g).op.HasPointwiseRightKanExtension F]

/-- **The inverse image `a_X⁻¹` commutes with base change**: for a morphism `g : Y ⟶ X`,
restricting `a_X⁻¹ F` to the big fppf site over `Y` is `a_Y⁻¹` of the pullback of `F` to the
small étale site of `Y`. -/
noncomputable def aXBaseChangeIso :
    aX X A ⋙ fppfTopology.overMapPullback A g ≅
      (Etale.pullback g).sheafPullback A X.smallEtaleTopology Y.smallEtaleTopology ⋙ aX Y A :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (epsilonFppfEtaleBaseChangeIso X A g) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (piXBaseChangeIso g A) _ ≪≫
    Functor.associator _ _ _

end BaseChange

section Sections

variable {X} {T : Scheme.{u}} (h : T ⟶ X) (A : Type w) [Category.{w'} A]
  [∀ F : X.Etaleᵒᵖ ⥤ A, (Etale.forget X).op.HasLeftKanExtension F]
  [∀ F : T.Etaleᵒᵖ ⥤ A, (Etale.forget T).op.HasPointwiseLeftKanExtension F]
  [∀ F : T.Etaleᵒᵖ ⥤ A, (Etale.forget T).op.HasPointwiseRightKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ A, (Etale.pullback h).op.HasLeftKanExtension F]
  [HasWeakSheafify (etaleTopology.over X) A] [HasWeakSheafify (etaleTopology.over T) A]
  [HasWeakSheafify T.smallEtaleTopology A]

/-- **The values of `π_X⁻¹ F`**: for a scheme `h : T ⟶ X` over `X` and a sheaf `F` on the small
étale site of `X`, the sections of `π_X⁻¹ F` over `T` are the global sections `Γ(T_ét, h⁻¹ F)` of
the pullback of `F` to the small étale site of `T`. -/
noncomputable def piXObjIso (F : Sheaf X.smallEtaleTopology A) :
    ((piX X A).obj F).obj.obj (op (Over.mk h)) ≅
      (((Etale.pullback h).sheafPullback A X.smallEtaleTopology T.smallEtaleTopology).obj F).obj.obj
        (op (Etale.mk (𝟙 T))) :=
  ((piX X A).obj F).obj.mapIso (Over.isoMk (Iso.refl T) : Over.mk (𝟙 T ≫ h) ≅ Over.mk h).op ≪≫
    ((sheafToPresheaf _ A).mapIso ((piXBaseChangeIso h A).app F)).app
      (op (Over.mk (𝟙 T))) ≪≫
    ((sheafToPresheaf _ A).mapIso (((Etale.forget T).sheafPullbackCompSheafPushforwardContinuousIso
      A T.smallEtaleTopology (etaleTopology.over T)).app _)).app (op (Etale.mk (𝟙 T)))

/-- **The values of `a_X⁻¹ F` when `π_X⁻¹ F` is an fppf sheaf**: if the big étale sheaf `π_X⁻¹ F`
is already an fppf sheaf, then the sections of `a_X⁻¹ F` over a scheme `h : T ⟶ X` over `X` are
the global sections `Γ(T_ét, h⁻¹ F)` of the pullback of `F` to the small étale site of `T`. -/
noncomputable def aXObjIsoOfIsSheaf [HasWeakSheafify (fppfTopology.over X) A]
    (F : Sheaf X.smallEtaleTopology A)
    (hF : Presheaf.IsSheaf (fppfTopology.over X) ((piX X A).obj F).obj) :
    ((aX X A).obj F).obj.obj (op (Over.mk h)) ≅
      (((Etale.pullback h).sheafPullback A X.smallEtaleTopology T.smallEtaleTopology).obj F).obj.obj
        (op (Etale.mk (𝟙 T))) :=
  ((sheafToPresheaf _ A).mapIso (epsilonFppfEtaleObjIsoOfIsSheaf X A _ hF)).app
      (op (Over.mk h)) ≪≫
    piXObjIso h A F

end Sections

section FullyFaithful

variable (A : Type w) [Category.{w'} A]
  [∀ F : X.Etaleᵒᵖ ⥤ A, (Etale.forget X).op.HasPointwiseLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ A, (Etale.forget X).op.HasPointwiseRightKanExtension F]
  [HasWeakSheafify X.smallEtaleTopology A] [HasWeakSheafify (etaleTopology.over X) A]

/-- The inverse image `π_X⁻¹` from the small to the big étale site is fully faithful: restricting
`π_X⁻¹ F` to the small étale site gives `F` back. -/
noncomputable def fullyFaithfulPiX : (piX X A).FullyFaithful :=
  (Etale.forget X).fullyFaithfulSheafPullback A _ _

/-- The inverse image `π_X⁻¹` is full. -/
instance : (piX X A).Full :=
  (fullyFaithfulPiX X A).full

/-- The inverse image `π_X⁻¹` is faithful. -/
instance : (piX X A).Faithful :=
  (fullyFaithfulPiX X A).faithful

end FullyFaithful

section Exact

variable (A : Type w) [Category.{u + 1} A] {FA : A → A → Type*} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] [HasFiniteLimits A]
  [HasColimitsOfSize.{u, u + 1} A] [PreservesFiniteLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u + 1} (CategoryTheory.forget A)]
  [HasSheafify X.smallEtaleTopology A] [HasSheafify (etaleTopology.over X) A]

/-- The inverse image `π_X⁻¹` is exact. -/
instance : PreservesFiniteLimits (piX X A) := by
  dsimp only [piX]
  infer_instance

end Exact

/-- The inverse image `π_X⁻¹` on abelian sheaves with sections in `Type (u + 1)` is exact. -/
instance : PreservesFiniteLimits (piX X AddCommGrpCat.{u + 1}) :=
  have := hasColimitsOfSizeShrink.{u, u + 1, u + 1, 0} AddCommGrpCat.{u + 1}
  have := preservesFilteredColimitsOfSize_shrink.{u + 1, 0, u, u + 1}
    (CategoryTheory.forget AddCommGrpCat.{u + 1})
  inferInstance

end AlgebraicGeometry.Scheme
