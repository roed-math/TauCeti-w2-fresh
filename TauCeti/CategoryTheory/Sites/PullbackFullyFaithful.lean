/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Pullback of sheaves along a fully faithful continuous and cocontinuous functor

Let `G : C ⥤ D` be a fully faithful functor which is continuous and cocontinuous for topologies
`J` on `C` and `K` on `D`. Then restricting the pullback `G⁻¹ F` of a sheaf `F` on `C` back along
`G` gives `F` again: restriction along `G` commutes with sheafification (since `G` is
cocontinuous), and restricting the left Kan extension along `G.op` of a presheaf gives the
presheaf back (since `G` is fully faithful).

An example is the inclusion of the small étale site of a scheme into its big étale site: an étale
covering of a scheme étale over `X` consists of schemes étale over `X`.

## Main declarations

* `CategoryTheory.Functor.sheafPullbackCompSheafPushforwardContinuousIso`: the natural
  isomorphism `G⁻¹ ⋙ G^* ≅ 𝟭`.
* `CategoryTheory.Functor.fullyFaithfulSheafPullback`: the pullback `G⁻¹` is fully faithful.
-/

@[expose] public section

open CategoryTheory Limits

universe w w'

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D) [G.Full] [G.Faithful]
  (A : Type w) [Category.{w'} A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ F : Cᵒᵖ ⥤ A, G.op.HasPointwiseLeftKanExtension F]
  [∀ F : Cᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension F]
  [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- For a fully faithful functor `G` which is continuous and cocontinuous, the pullback of
sheaves along `G` followed by the restriction along `G` is the identity. -/
noncomputable def sheafPullbackCompSheafPushforwardContinuousIso :
    G.sheafPullback A J K ⋙ G.sheafPushforwardContinuous A J K ≅ 𝟭 _ :=
  isoWhiskerRight ((G.sheafAdjunctionContinuous A J K).leftAdjointUniq
      (sheafPullbackConstruction.sheafAdjunctionContinuous G A J K)) _ ≪≫
    isoWhiskerLeft (sheafToPresheaf J A ⋙ G.op.lan)
      (G.pushforwardContinuousSheafificationCompatibility A J K).symm ≪≫
    isoWhiskerRight (isoWhiskerLeft (sheafToPresheaf J A) (asIso G.op.lanUnit).symm)
      (presheafToSheaf J A) ≪≫
    asIso (sheafificationAdjunction J A).counit

/-- For a fully faithful functor `G` which is continuous and cocontinuous, the pullback of
sheaves along `G` is fully faithful. -/
noncomputable def fullyFaithfulSheafPullback : (G.sheafPullback A J K).FullyFaithful :=
  (G.sheafAdjunctionContinuous A J K).fullyFaithfulLOfCompIsoId
    (G.sheafPullbackCompSheafPushforwardContinuousIso A J K)

/-- The pullback along a fully faithful continuous and cocontinuous functor is full. -/
instance : (G.sheafPullback A J K).Full :=
  (G.fullyFaithfulSheafPullback A J K).full

/-- The pullback along a fully faithful continuous and cocontinuous functor is faithful. -/
instance : (G.sheafPullback A J K).Faithful :=
  (G.fullyFaithfulSheafPullback A J K).faithful

end CategoryTheory.Functor
