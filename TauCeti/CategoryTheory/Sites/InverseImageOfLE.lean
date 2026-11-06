/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Comparison of sheaves for two topologies on the same category

Let `J ≤ K` be Grothendieck topologies on a category `C`. Every `K`-sheaf is a `J`-sheaf, and the
identity of `C` induces a morphism of topoi from `K`-sheaves to `J`-sheaves. Its direct image
`sheafDirectImageOfLE A h : Sheaf K A ⥤ Sheaf J A` regards a `K`-sheaf as a `J`-sheaf, and its
inverse image `sheafInverseImage J K A : Sheaf J A ⥤ Sheaf K A` is the `K`-sheafification of the
underlying presheaf. The inverse image is left adjoint to the direct image, it is exact as soon as
`K`-sheafification exists, and it sends constant sheaves to constant sheaves. When topologies on
two categories are related by a functor that is continuous for both pairs and cocontinuous for the
finer pair, the inverse images commute with restriction along the functor; when it is continuous
for both pairs, they commute with pullback along the functor. The comparisons are
coherent: for `J` itself the inverse image is the identity, and the inverse images for `J ≤ K` and
`K ≤ L` compose to the one for `J ≤ L`.

This is the common shape of the comparison morphisms between the topologies of a scheme, such as
the big fppf and big étale topologies over a scheme, or the small étale and Nisnevich topologies.

## Main declarations

* `CategoryTheory.GrothendieckTopology.sheafDirectImageOfLE`: a `K`-sheaf is a `J`-sheaf.
* `CategoryTheory.GrothendieckTopology.sheafInverseImage`: `K`-sheafification of a `J`-sheaf.
* `CategoryTheory.GrothendieckTopology.sheafAdjunctionOfLE`: the inverse image is left adjoint to
  the direct image.
* `CategoryTheory.GrothendieckTopology.sheafInverseImageObjIsoOfIsSheaf`: the inverse image of a
  `J`-sheaf that is already a `K`-sheaf is the sheaf itself.
* `CategoryTheory.GrothendieckTopology.sheafInverseImageRefl`: the comparison of a topology with
  itself is the identity.
* `CategoryTheory.GrothendieckTopology.sheafInverseImageTrans`: the comparisons compose.
* `CategoryTheory.GrothendieckTopology.constantSheafCompSheafInverseImageIso`: the inverse image
  of a constant sheaf is constant.
* `CategoryTheory.GrothendieckTopology.sheafInverseImageCompSheafPushforwardContinuousIso`: the
  comparisons commute with restriction along a continuous and cocontinuous functor.
-/

@[expose] public section

open CategoryTheory Limits

universe v u w w'

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J K L : GrothendieckTopology C}
  (A : Type w) [Category.{w'} A]

/-- The direct image of the comparison of two topologies `J ≤ K` on the same category: a sheaf
for the finer topology `K` is a sheaf for `J`. -/
def sheafDirectImageOfLE (h : J ≤ K) : Sheaf K A ⥤ Sheaf J A :=
  ObjectProperty.ιOfLE fun _ hF ↦ hF.of_le h

/-- The underlying presheaf of the direct image of a sheaf is the sheaf itself. -/
@[simp]
lemma sheafDirectImageOfLE_obj_obj (h : J ≤ K) (F : Sheaf K A) :
    ((sheafDirectImageOfLE A h).obj F).obj = F.obj :=
  rfl

/-- The underlying morphism of presheaves of the direct image of a morphism of sheaves is the
morphism itself. -/
@[simp]
lemma sheafDirectImageOfLE_map_hom (h : J ≤ K) {F G : Sheaf K A} (f : F ⟶ G) :
    ((sheafDirectImageOfLE A h).map f).hom = f.hom :=
  rfl

/-- The direct image of the comparison of two topologies is fully faithful. -/
def fullyFaithfulSheafDirectImageOfLE (h : J ≤ K) : (sheafDirectImageOfLE A h).FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE _

instance (h : J ≤ K) : (sheafDirectImageOfLE A h).Full :=
  (fullyFaithfulSheafDirectImageOfLE A h).full

instance (h : J ≤ K) : (sheafDirectImageOfLE A h).Faithful :=
  (fullyFaithfulSheafDirectImageOfLE A h).faithful

/-- The direct images of comparisons compose: the composite of the direct images for `J ≤ K`
and `K ≤ L` is the direct image for `J ≤ L`. -/
lemma sheafDirectImageOfLE_comp (h : J ≤ K) (h' : K ≤ L) :
    sheafDirectImageOfLE A h' ⋙ sheafDirectImageOfLE A h = sheafDirectImageOfLE A (h.trans h') :=
  rfl

variable (J K) in
/-- The `K`-sheafification of a `J`-sheaf. When `J ≤ K`, this is the inverse image of the
comparison of the two topologies (`sheafAdjunctionOfLE`). -/
noncomputable def sheafInverseImage [HasWeakSheafify K A] : Sheaf J A ⥤ Sheaf K A :=
  sheafToPresheaf J A ⋙ presheafToSheaf K A

/-- The inverse image of a sheaf is the sheafification of its underlying presheaf. -/
@[simp]
lemma sheafInverseImage_obj [HasWeakSheafify K A] (F : Sheaf J A) :
    (sheafInverseImage J K A).obj F = (presheafToSheaf K A).obj F.obj :=
  rfl

/-- The inverse image of a morphism of sheaves is the sheafification of the underlying morphism of
presheaves. -/
@[simp]
lemma sheafInverseImage_map [HasWeakSheafify K A] {F G : Sheaf J A} (f : F ⟶ G) :
    (sheafInverseImage J K A).map f = (presheafToSheaf K A).map f.hom :=
  rfl

/-- The inverse image of the comparison of two topologies is exact: it preserves finite limits,
since sheafification does. -/
instance [HasFiniteLimits A] [HasSheafify K A] :
    PreservesFiniteLimits (sheafInverseImage J K A) := by
  dsimp only [sheafInverseImage]
  infer_instance

/-- The inverse image of the comparison of two topologies `J ≤ K` is left adjoint to its direct
image. -/
noncomputable def sheafAdjunctionOfLE [HasWeakSheafify K A] (h : J ≤ K) :
    sheafInverseImage J K A ⊣ sheafDirectImageOfLE A h :=
  (sheafificationAdjunction K A).restrictFullyFaithful (fullyFaithfulSheafToPresheaf J A)
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

instance [HasWeakSheafify K A] (h : J ≤ K) : (sheafDirectImageOfLE A h).IsRightAdjoint :=
  (sheafAdjunctionOfLE A h).isRightAdjoint

/-- The `K`-sheafification of a `J`-sheaf preserves all colimits, when `J ≤ K`. -/
lemma preservesColimits_sheafInverseImage [HasWeakSheafify K A] (h : J ≤ K) :
    PreservesColimitsOfSize.{w', w'} (sheafInverseImage J K A) :=
  (sheafAdjunctionOfLE A h).leftAdjoint_preservesColimits

/-- **The inverse image does not change a sheaf for the finer topology**: if the underlying
presheaf of a `J`-sheaf `F` is a `K`-sheaf, then the inverse image of `F` is `F` itself,
regarded as a `K`-sheaf. -/
noncomputable def sheafInverseImageObjIsoOfIsSheaf [HasWeakSheafify K A] (h : J ≤ K)
    (F : Sheaf J A) (hF : Presheaf.IsSheaf K F.obj) :
    (sheafInverseImage J K A).obj F ≅ ⟨F.obj, hF⟩ :=
  (asIso (sheafAdjunctionOfLE A h).counit).app ⟨F.obj, hF⟩

variable (J) in
/-- **The comparison of a topology with itself is the identity**: sheafifying a sheaf gives the
sheaf back. -/
noncomputable def sheafInverseImageRefl [HasWeakSheafify J A] :
    sheafInverseImage J J A ≅ 𝟭 (Sheaf J A) :=
  (asIso (sheafificationAdjunction J A).counit :
    sheafToPresheaf J A ⋙ presheafToSheaf J A ≅ 𝟭 (Sheaf J A))

/-- **The comparisons compose**: for `J ≤ K ≤ L`, the inverse images for `J ≤ K` and `K ≤ L`
compose to the inverse image for `J ≤ L`. -/
noncomputable def sheafInverseImageTrans [HasWeakSheafify K A] [HasWeakSheafify L A]
    (h : J ≤ K) (h' : K ≤ L) :
    sheafInverseImage J K A ⋙ sheafInverseImage K L A ≅ sheafInverseImage J L A :=
  ((sheafAdjunctionOfLE A h).comp (sheafAdjunctionOfLE A h')).leftAdjointUniq
    (sheafAdjunctionOfLE A (h.trans h'))

/-- Sheafifying for `J` and then for a finer topology `K` is sheafifying for `K`. -/
noncomputable def presheafToSheafCompSheafInverseImageIso [HasWeakSheafify J A]
    [HasWeakSheafify K A] (h : J ≤ K) :
    presheafToSheaf J A ⋙ sheafInverseImage J K A ≅ presheafToSheaf K A :=
  ((sheafificationAdjunction J A).comp (sheafAdjunctionOfLE A h)).leftAdjointUniq
    (sheafificationAdjunction K A)

/-- The comparison `P^K ⟶ (P^J)^K` of sheafifications, precomposed with the `K`-sheafification
map of `P`, is the `J`-sheafification map of `P` followed by the unit `P^J ⟶ (P^J)^K` of the
adjunction between inverse and direct images. -/
lemma toSheafify_comp_presheafToSheafCompSheafInverseImageIso_inv_app_hom [HasWeakSheafify J A]
    [HasWeakSheafify K A] (h : J ≤ K) (P : Cᵒᵖ ⥤ A) :
    CategoryTheory.toSheafify K P ≫ ((presheafToSheafCompSheafInverseImageIso A h).inv.app P).hom =
      CategoryTheory.toSheafify J P ≫
        ((sheafAdjunctionOfLE A h).unit.app ((presheafToSheaf J A).obj P)).hom := by
  have h₁ := Adjunction.unit_leftAdjointUniq_hom_app
    ((sheafificationAdjunction J A).comp (sheafAdjunctionOfLE A h)) (sheafificationAdjunction K A) P
  rw [Adjunction.comp_unit_app] at h₁
  have h₂ := congrArg (fun f ↦ f ≫ ((presheafToSheafCompSheafInverseImageIso A h).inv.app P).hom) h₁
  have h₃ := congrArg (fun f ↦ f.hom)
    ((presheafToSheafCompSheafInverseImageIso A h).hom_inv_id_app P)
  simp only [Category.assoc] at h₂
  simp only [ObjectProperty.FullSubcategory.comp_hom] at h₃
  -- The composites live in presheaf categories whose objects are only defeq to each other, so
  -- `rw` fails on them; the identities are assembled as terms.
  exact h₂.symm.trans ((Category.assoc _ _ _).trans (congrArg _ ((Category.assoc _ _ _).trans
    ((congrArg _ h₃).trans (Category.comp_id _)))))

/-- The inverse image of the comparison of two topologies `J ≤ K` sends the constant `J`-sheaf to
the constant `K`-sheaf. -/
noncomputable def constantSheafCompSheafInverseImageIso [HasWeakSheafify J A]
    [HasWeakSheafify K A] (h : J ≤ K) :
    constantSheaf J A ⋙ sheafInverseImage J K A ≅ constantSheaf K A :=
  Functor.isoWhiskerLeft (Functor.const Cᵒᵖ) (presheafToSheafCompSheafInverseImageIso A h)

/-- **The comparisons commute with base change**: let `G : C ⥤ D` be a functor that is continuous
for topologies `J₁` and `K₁`, and continuous and cocontinuous for topologies `J₂` and `K₂`. Then
the inverse images of the comparisons on `D` and on `C` commute with restriction along `G`. -/
noncomputable def sheafInverseImageCompSheafPushforwardContinuousIso {D : Type*} [Category* D]
    (G : C ⥤ D) (J₁ J₂ : GrothendieckTopology C) (K₁ K₂ : GrothendieckTopology D)
    [G.IsContinuous J₁ K₁] [G.IsContinuous J₂ K₂] [G.IsCocontinuous J₂ K₂]
    [∀ F : Cᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension F]
    [HasWeakSheafify J₂ A] [HasWeakSheafify K₂ A] :
    sheafInverseImage K₁ K₂ A ⋙ G.sheafPushforwardContinuous A J₂ K₂ ≅
      G.sheafPushforwardContinuous A J₁ K₁ ⋙ sheafInverseImage J₁ J₂ A :=
  Functor.isoWhiskerLeft (sheafToPresheaf K₁ A)
      (G.pushforwardContinuousSheafificationCompatibility A J₂ K₂).symm ≪≫
    Functor.isoWhiskerRight (G.sheafPushforwardContinuousCompSheafToPresheafIso A J₁ K₁).symm
      (presheafToSheaf J₂ A)

/-- **The comparisons commute with pullback**: let `G : C ⥤ D` be a functor that is continuous
for topologies `J₁ ≤ J₂` on `C` and `K₁ ≤ K₂` on `D`. Then the inverse images of the comparisons
on `C` and on `D` commute with the pullbacks of sheaves along `G`. -/
noncomputable def sheafInverseImageCompSheafPullbackIso {D : Type*} [Category* D]
    (G : C ⥤ D) {J₁ J₂ : GrothendieckTopology C} {K₁ K₂ : GrothendieckTopology D}
    (hJ : J₁ ≤ J₂) (hK : K₁ ≤ K₂) [G.IsContinuous J₁ K₁] [G.IsContinuous J₂ K₂]
    [(G.sheafPushforwardContinuous A J₁ K₁).IsRightAdjoint]
    [(G.sheafPushforwardContinuous A J₂ K₂).IsRightAdjoint]
    [HasWeakSheafify J₂ A] [HasWeakSheafify K₂ A] :
    sheafInverseImage J₁ J₂ A ⋙ G.sheafPullback A J₂ K₂ ≅
      G.sheafPullback A J₁ K₁ ⋙ sheafInverseImage K₁ K₂ A :=
  (conjugateIsoEquiv ((G.sheafAdjunctionContinuous A J₁ K₁).comp (sheafAdjunctionOfLE A hK))
    ((sheafAdjunctionOfLE A hJ).comp (G.sheafAdjunctionContinuous A J₂ K₂))).symm (Iso.refl _)

end CategoryTheory.GrothendieckTopology
