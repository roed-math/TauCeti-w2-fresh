/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Abelian.AcyclicResolution
public import TauCeti.CategoryTheory.Abelian.RightDerived

/-!
# Comparing right derived functors through adapted resolutions

An exact functor need not preserve injectives. It suffices for a comparison of
right derived functors that it send injectives to an adapted class for the functor
on the other side. The comparison below is natural and is computed using the
image of an injective resolution. This applies, for example, to forgetting the
scalars of a sheaf of modules: injective module sheaves become flasque abelian
sheaves.

## References

* The Stacks Project, Derived Categories, Lemma 13.16.7 (tag 015E).
-/

public section

open CategoryTheory Limits CochainComplex

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace TauCeti

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {C' : Type u₃} [Category.{v₃} C'] [Abelian C'] [EnoughInjectives C']
  {D' : Type u₄} [Category.{v₄} D'] [Abelian D']
  (F : C ⥤ D) [F.Additive] (G : D ⥤ D') [G.Additive] [G.PreservesHomology]
  (H : C ⥤ C') [H.Additive] [H.PreservesHomology]
  (F' : C' ⥤ D') [F'.Additive]
  (P : ObjectProperty C') [P.IsClosedUnderIsomorphisms]
  (hinj : ∀ Y : C', Injective Y → P Y)
  (hP : ∀ S : ShortComplex C', S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
  (hF : ∀ S : ShortComplex C', S.ShortExact → P S.X₁ → P S.X₂ →
    (S.map F').ShortExact)
  (hH : ∀ Y : C, Injective Y → P (H.obj Y))
  (e : F ⋙ G ≅ H ⋙ F')

private abbrev imageResolutionι {X : C} (I : InjectiveResolution X) :
    (single₀ C').obj (H.obj X) ⟶ (H.mapHomologicalComplex _).obj I.cocomplex :=
  (HomologicalComplex.singleMapHomologicalComplex H _ 0).inv.app X ≫
    (H.mapHomologicalComplex _).map I.ι

private instance {X : C} (I : InjectiveResolution X) :
    QuasiIso (imageResolutionι H I) := by
  dsimp only [imageResolutionι]
  infer_instance

private def comparisonOnComplexes (n : ℕ) :
    (F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n) ⋙ G ≅
      H.mapHomologicalComplex (ComplexShape.up ℕ) ⋙ F'.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (G.mapHomologicalComplexCompHomologyFunctorIso _ n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso e _ ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ F')) _).symm) _ ≪≫
    Functor.associator _ _ _

/-- An image injective resolution computes the comparison of derived functors
when its terms belong to an adapted class. -/
def rightDerivedCompObjIsoOfAdapted {X : C} (I : InjectiveResolution X) (n : ℕ) :
    G.obj ((F.rightDerived n).obj X) ≅ (F'.rightDerived n).obj (H.obj X) :=
  G.mapIso (I.isoRightDerivedObj F n) ≪≫
    (comparisonOnComplexes F G H F' e n).app I.cocomplex ≪≫
    (F'.rightDerivedObjIsoOfResolution P hinj hP hF (imageResolutionι H I)
      (fun n ↦ hH _ (I.injective n)) n).symm

/-- The adapted-resolution comparison is natural in a map between injective
resolutions lifting a coefficient morphism. -/
@[reassoc]
lemma rightDerivedCompObjIsoOfAdapted_hom_naturality {X Y : C}
    (I : InjectiveResolution X) (J : InjectiveResolution Y) (f : X ⟶ Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι ≫ φ = (single₀ C).map f ≫ J.ι) (n : ℕ) :
    G.map ((F.rightDerived n).map f) ≫
        (rightDerivedCompObjIsoOfAdapted F G H F' P hinj hP hF hH e J n).hom =
      (rightDerivedCompObjIsoOfAdapted F G H F' P hinj hP hF hH e I n).hom ≫
        (F'.rightDerived n).map (H.map f) := by
  have hφ₀ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 := by
    simpa using congrArg (fun a ↦ a.f 0) hφ
  have himage : imageResolutionι H I ≫ (H.mapHomologicalComplex _).map φ =
      (single₀ C').map (H.map f) ≫ imageResolutionι H J := by
    dsimp only [imageResolutionι]
    rw [Category.assoc, ← Functor.map_comp, hφ, Functor.map_comp, ← Category.assoc]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun a ↦ a ≫ (H.mapHomologicalComplex _).map J.ι)
        ((HomologicalComplex.singleMapHomologicalComplex H _ 0).inv.naturality f).symm
  have h₁ := InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ hφ₀ F n
  have h₂ := F'.rightDerivedObjIsoOfResolution_hom_naturality P hinj hP hF
    (imageResolutionι H I) (fun n ↦ hH _ (I.injective n))
    (imageResolutionι H J) (fun n ↦ hH _ (J.injective n))
    (H.map f) ((H.mapHomologicalComplex _).map φ) himage n
  dsimp only [rightDerivedCompObjIsoOfAdapted, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  apply (cancel_mono
    (F'.rightDerivedObjIsoOfResolution P hinj hP hF (imageResolutionι H J)
      (fun n ↦ hH _ (J.injective n)) n).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h₂, ← Category.assoc, ← Category.assoc, ← Category.assoc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← G.map_comp, h₁, G.map_comp, Category.assoc]
  exact congrArg (fun a ↦ G.map (I.isoRightDerivedObj F n).hom ≫ a)
    ((comparisonOnComplexes F G H F' e n).hom.naturality φ)

/-- Right derived functors commute across an exact comparison square if the
image of every injective is adapted to the functor on the other side. -/
def rightDerivedCompIsoOfAdapted (n : ℕ) :
    F.rightDerived n ⋙ G ≅ H ⋙ F'.rightDerived n :=
  NatIso.ofComponents
    (fun X ↦ rightDerivedCompObjIsoOfAdapted F G H F' P hinj hP hF hH e
      (injectiveResolution X) n)
    (fun f ↦ rightDerivedCompObjIsoOfAdapted_hom_naturality F G H F' P hinj hP hF hH e
      _ _ f (InjectiveResolution.desc f _ _)
      (InjectiveResolution.desc_commutes f _ _) n)

/-- The natural comparison is computed using the chosen injective resolution. -/
@[simp]
lemma rightDerivedCompIsoOfAdapted_app (n : ℕ) (X : C) :
    (rightDerivedCompIsoOfAdapted F G H F' P hinj hP hF hH e n).app X =
      rightDerivedCompObjIsoOfAdapted F G H F' P hinj hP hF hH e (injectiveResolution X) n :=
  (rfl)

/-- Computing the comparison with any injective resolution gives the same map. -/
lemma rightDerivedCompObjIsoOfAdapted_eq {X : C} (I : InjectiveResolution X) (n : ℕ) :
    rightDerivedCompObjIsoOfAdapted F G H F' P hinj hP hF hH e I n =
      (rightDerivedCompIsoOfAdapted F G H F' P hinj hP hF hH e n).app X := by
  apply Iso.ext
  simpa using (rightDerivedCompObjIsoOfAdapted_hom_naturality F G H F' P hinj hP hF hH e
    I (injectiveResolution X) (𝟙 X) (InjectiveResolution.desc (𝟙 X) _ _)
    (InjectiveResolution.desc_commutes (𝟙 X) _ _) n).symm

end

end TauCeti
