/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.LocalCohomology.Basic
public import TauCeti.CategoryTheory.Abelian.RightDerived
public import TauCeti.CategoryTheory.Sites.SheafCohomology.AcyclicResolution
import TauCeti.CategoryTheory.Abelian.Injective.Ext
import TauCeti.Algebra.Homology.HomologicalComplex.FunctorCategory
import TauCeti.CategoryTheory.Sites.Limits

/-!
# Derived supported sections and the local cohomology sheaves

Applying supported sections to an injective resolution computes the presheaf
`W ↦ H_Z^q(W,F)` before sheafification. Sheafification is exact, so its sheafified
homology is the right derived supported-section sheaf. This identifies the
sheafification definition of local cohomology with the derived-functor one.

The cycle construction follows the sections-of-resolutions comparison
`CategoryTheory.Sheaf.H'.homologyIsoCohomologyPresheaf`, using the relative free
abelian sheaf representing supported sections in place of the free sheaf on an
open subset.

## References

* The Stacks Project, Cohomology of Sheaves, Sections 20.21 and 20.34.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace Abelian
open TauCeti.CategoryTheory

universe u

namespace TauCeti

noncomputable section

variable {X : TopCat.{u}} (Z : Closeds X)
  {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
  (I : InjectiveResolution F)

private abbrev supportedSectionsResolutionComplex :=
  ((sheafToPresheaf _ _).mapHomologicalComplex _).obj
    (((Sheaf.supportedSectionsFunctor Z).mapHomologicalComplex _).obj I.cocomplex)

private def supportedSubtypeHom (W : Opens X) (G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    G.supportedSections Z W ≃+ (relativeFreeYonedaSheaf _ (Z.complInclusion W) ⟶ G) :=
  { toFun s := (relativeFreeYonedaSheafHomEquiv _ _ G).symm
      ⟨s.1, (G.mem_supportedSections_iff).1 s.2⟩
    invFun f := ⟨(relativeFreeYonedaSheafHomEquiv _ _ G f).1,
      (G.mem_supportedSections_iff).2 (relativeFreeYonedaSheafHomEquiv _ _ G f).2⟩
    left_inv s := by
      apply Subtype.ext
      exact congrArg (fun t : (G.obj.map (Z.complInclusion W).op).hom.ker ↦ t.1)
        ((relativeFreeYonedaSheafHomEquiv _ _ G).apply_symm_apply
        ⟨s.1, (G.mem_supportedSections_iff).1 s.2⟩)
    right_inv f := (relativeFreeYonedaSheafHomEquiv _ _ G).symm_apply_apply f
    map_add' s t := by simp only [← map_add]; rfl }

private def supportedSectionHom (W : Opens X) (G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((Sheaf.supportedSectionsFunctor Z).obj G).obj.obj (op W) ≃+
      (relativeFreeYonedaSheaf _ (Z.complInclusion W) ⟶ G) :=
  (AddEquiv.refl (G.supportedSections Z W)).trans (supportedSubtypeHom Z W G)

private lemma supportedSectionHom_coe (W : Opens X) (G : TopCat.Sheaf AddCommGrpCat.{u} X)
    (s : ((Sheaf.supportedSectionsFunctor Z).obj G).obj.obj (op W)) :
    (relativeFreeYonedaSheafHomEquiv _ _ G (supportedSectionHom Z W G s)).1 = s.1 := by
  exact congrArg (fun t : (G.obj.map (Z.complInclusion W).op).hom.ker ↦ t.1)
        ((relativeFreeYonedaSheafHomEquiv _ _ G).apply_symm_apply
    ⟨s.1, (G.mem_supportedSections_iff).1 s.2⟩)

private lemma supportedSectionHom_naturality (W : Opens X)
    {G G' : TopCat.Sheaf AddCommGrpCat.{u} X} (f : G ⟶ G')
    (s : ((Sheaf.supportedSectionsFunctor Z).obj G).obj.obj (op W)) :
    supportedSectionHom Z W G' (((Sheaf.supportedSectionsFunctor Z).map f).hom.app (op W) s) =
      supportedSectionHom Z W G s ≫ f := by
  apply (relativeFreeYonedaSheafHomEquiv _ _ G').injective
  apply Subtype.ext
  rw [supportedSectionHom_coe, relativeFreeYonedaSheafHomEquiv_naturality_right,
    supportedSectionHom_coe]
  exact Sheaf.coe_supportedSectionsFunctor_map_hom_app_apply Z f (op W) s

/-- The supported cohomology class of a supported cocycle in an injective resolution. -/
def supportedResolutionClass {n : ℕ} (W : Opens X)
    (s : (((Sheaf.supportedSectionsFunctor Z).obj (I.cocomplex.X n)).obj.obj (op W)))
    (hs : ((Sheaf.supportedSectionsFunctor Z).map (I.cocomplex.d n (n + 1))).hom.app
      (op W) s = 0) : F.supportedH Z W n :=
  I.extMk (supportedSectionHom Z W _ s) (n + 1) rfl (by
    rw [← supportedSectionHom_naturality, hs, map_zero])

/-- The class of a sum of supported cocycles is the sum of their classes. -/
lemma supportedResolutionClass_add {n : ℕ} (W : Opens X)
    (s t : (((Sheaf.supportedSectionsFunctor Z).obj (I.cocomplex.X n)).obj.obj (op W)))
    (hs : ((Sheaf.supportedSectionsFunctor Z).map (I.cocomplex.d n (n + 1))).hom.app
      (op W) s = 0)
    (ht : ((Sheaf.supportedSectionsFunctor Z).map (I.cocomplex.d n (n + 1))).hom.app
      (op W) t = 0) :
    supportedResolutionClass Z I W (s + t) (by rw [map_add, hs, ht, add_zero]) =
      supportedResolutionClass Z I W s hs + supportedResolutionClass Z I W t ht := by
  simp only [supportedResolutionClass, map_add]
  exact (I.add_extMk _ _ _ rfl _ _).symm

/-- Classes of supported cocycles commute with restriction to smaller open subsets. -/
lemma supportedResolutionClass_restrict {n : ℕ} {W V : Opens X} (h : V ≤ W)
    (s : (((Sheaf.supportedSectionsFunctor Z).obj (I.cocomplex.X n)).obj.obj (op W)))
    (hs : ((Sheaf.supportedSectionsFunctor Z).map (I.cocomplex.d n (n + 1))).hom.app
      (op W) s = 0) :
    F.supportedHRestrict Z h n (supportedResolutionClass Z I W s hs) =
      supportedResolutionClass Z I V
        (((Sheaf.supportedSectionsFunctor Z).obj (I.cocomplex.X n)).obj.map (homOfLE h).op s)
        (by rw [NatTrans.naturality_apply, hs, map_zero]) := by
  rw [supportedResolutionClass, Sheaf.supportedHRestrict_apply,
    I.mk₀_comp_extMk, supportedResolutionClass]
  congr 1
  apply (relativeFreeYonedaSheafHomEquiv _ _ _).injective
  apply Subtype.ext
  rw [coe_relativeFreeYonedaSheafHomEquiv_map_comp, supportedSectionHom_coe,
    supportedSectionHom_coe]
  exact (Sheaf.coe_supportedSectionsPresheaf_map_apply _ _ _ _).symm

/-- Every supported cohomology class is represented by a supported cocycle. -/
lemma supportedResolutionClass_surjective {n : ℕ} (W : Opens X)
    (x : F.supportedH Z W n) :
    ∃ (s : (((Sheaf.supportedSectionsFunctor Z).obj (I.cocomplex.X n)).obj.obj (op W)))
      (hs : ((Sheaf.supportedSectionsFunctor Z).map (I.cocomplex.d n (n + 1))).hom.app
        (op W) s = 0), supportedResolutionClass Z I W s hs = x := by
  obtain ⟨f, hf, hx⟩ := I.extMk_surjective x (n + 1) rfl
  let s := (supportedSectionHom Z W _).symm f
  have hs : ((Sheaf.supportedSectionsFunctor Z).map (I.cocomplex.d n (n + 1))).hom.app
      (op W) s = 0 := by
    apply (supportedSectionHom Z W _).injective
    rw [supportedSectionHom_naturality, AddEquiv.apply_symm_apply, hf, map_zero]
  refine ⟨s, hs, ?_⟩
  simpa only [supportedResolutionClass, s, AddEquiv.apply_symm_apply] using hx

/-- A degree-zero supported cocycle has zero class exactly when it is zero. -/
lemma supportedResolutionClass_zero_eq_zero_iff (W : Opens X)
    (s : (((Sheaf.supportedSectionsFunctor Z).obj (I.cocomplex.X 0)).obj.obj (op W)))
    (hs : ((Sheaf.supportedSectionsFunctor Z).map (I.cocomplex.d 0 1)).hom.app (op W) s = 0) :
    supportedResolutionClass Z I W s hs = 0 ↔ s = 0 := by
  rw [supportedResolutionClass, I.extMk_eq_zero_iff_eq_zero,
    map_eq_zero_iff _ (supportedSectionHom Z W _).injective]

/-- A positive-degree supported cocycle has zero class exactly when it is a supported boundary. -/
lemma supportedResolutionClass_succ_eq_zero_iff {n : ℕ} (W : Opens X)
    (s : (((Sheaf.supportedSectionsFunctor Z).obj (I.cocomplex.X (n + 1))).obj.obj (op W)))
    (hs : ((Sheaf.supportedSectionsFunctor Z).map
      (I.cocomplex.d (n + 1) (n + 1 + 1))).hom.app (op W) s = 0) :
    supportedResolutionClass Z I W s hs = 0 ↔
      ∃ t : (((Sheaf.supportedSectionsFunctor Z).obj (I.cocomplex.X n)).obj.obj (op W)),
        ((Sheaf.supportedSectionsFunctor Z).map (I.cocomplex.d n (n + 1))).hom.app
          (op W) t = s := by
  rw [supportedResolutionClass, I.extMk_eq_zero_iff _ _ _ _ n rfl]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨(supportedSectionHom Z W _).symm g, ?_⟩
    apply (supportedSectionHom Z W _).injective
    rw [supportedSectionHom_naturality, AddEquiv.apply_symm_apply, hg]
  · rintro ⟨t, ht⟩
    exact ⟨supportedSectionHom Z W _ t,
      (supportedSectionHom_naturality Z W _ t).symm.trans (congrArg _ ht)⟩

private def supportedCyclesToH (n : ℕ) (W : (Opens X)ᵒᵖ) :
    ((supportedSectionsResolutionComplex Z I).cycles n).obj W →+ F.supportedH Z W.unop n :=
  AddMonoidHom.mk'
    (fun s ↦ supportedResolutionClass Z I W.unop
      (((supportedSectionsResolutionComplex Z I).iCycles n).app W s)
      (Sheaf.H'.d_hom_app_iCycles_app
        (K := ((Sheaf.supportedSectionsFunctor Z).mapHomologicalComplex _).obj I.cocomplex) n s))
    (fun s t ↦ by
      simp only [map_add]
      exact supportedResolutionClass_add Z I W.unop _ _ _ _)

private lemma supportedCyclesToH_naturality (n : ℕ) {W V : (Opens X)ᵒᵖ} (f : W ⟶ V)
    (s : ((supportedSectionsResolutionComplex Z I).cycles n).obj W) :
    supportedCyclesToH Z I n V (((supportedSectionsResolutionComplex Z I).cycles n).map f s) =
      (F.supportedHPresheaf Z n).map f (supportedCyclesToH Z I n W s) := by
  have h := supportedResolutionClass_restrict Z I (leOfHom f.unop)
    (((supportedSectionsResolutionComplex Z I).iCycles n).app W s)
    (Sheaf.H'.d_hom_app_iCycles_app
        (K := ((Sheaf.supportedSectionsFunctor Z).mapHomologicalComplex _).obj I.cocomplex) n s)
  -- Unbundle the presheaf value and map before comparing the Ext classes.
  change supportedCyclesToH Z I n V
      (((supportedSectionsResolutionComplex Z I).cycles n).map f s) =
    F.supportedHRestrict Z (leOfHom f.unop) n (supportedCyclesToH Z I n W s)
  simp only [supportedCyclesToH, AddMonoidHom.mk'_apply]
  rw [h]
  congr 1
  exact NatTrans.naturality_apply ((supportedSectionsResolutionComplex Z I).iCycles n) f s

private def supportedCyclesToPresheaf (n : ℕ) :
    (supportedSectionsResolutionComplex Z I).cycles n ⟶ F.supportedHPresheaf Z n where
  app W := AddCommGrpCat.ofHom (supportedCyclesToH Z I n W)
  naturality W V f := by
    ext s
    exact supportedCyclesToH_naturality Z I n f s

private lemma toCycles_supportedCyclesToPresheaf (n i : ℕ) :
    (supportedSectionsResolutionComplex Z I).toCycles i n ≫
      supportedCyclesToPresheaf Z I n = 0 := by
  by_cases hi : (ComplexShape.up ℕ).Rel i n
  · obtain rfl : i + 1 = n := hi
    ext W s
    exact (supportedResolutionClass_succ_eq_zero_iff Z I W.unop _
      (Sheaf.H'.d_hom_app_iCycles_app
        (K := ((Sheaf.supportedSectionsFunctor Z).mapHomologicalComplex _).obj I.cocomplex) _ _)).2
      ⟨s, ((supportedSectionsResolutionComplex Z I).iCycles_app_toCycles_app i (i + 1) s).symm⟩
  · rw [(supportedSectionsResolutionComplex Z I).toCycles_eq_zero hi, zero_comp]

private def homologyToSupportedHPresheaf (n : ℕ) :
    (supportedSectionsResolutionComplex Z I).homology n ⟶ F.supportedHPresheaf Z n :=
  ((supportedSectionsResolutionComplex Z I).homologyIsCokernel _ n rfl).desc
    (CokernelCofork.ofπ _ (toCycles_supportedCyclesToPresheaf Z I n _))

private lemma homologyπ_homologyToSupportedHPresheaf (n : ℕ) :
    (supportedSectionsResolutionComplex Z I).homologyπ n ≫
      homologyToSupportedHPresheaf Z I n = supportedCyclesToPresheaf Z I n :=
  Cofork.IsColimit.π_desc ((supportedSectionsResolutionComplex Z I).homologyIsCokernel _ n rfl)

private instance isIso_homologyToSupportedHPresheaf (n : ℕ) :
    IsIso (homologyToSupportedHPresheaf Z I n) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  have hπ : Function.Surjective (((supportedSectionsResolutionComplex Z I).homologyπ n).app W) :=
    (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
  have hi : Function.Injective (((supportedSectionsResolutionComplex Z I).iCycles n).app W) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have hfac (s : ((supportedSectionsResolutionComplex Z I).cycles n).obj W) :
      (homologyToSupportedHPresheaf Z I n).app W
        (((supportedSectionsResolutionComplex Z I).homologyπ n).app W s) =
          supportedCyclesToH Z I n W s :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (homologyπ_homologyToSupportedHPresheaf Z I n) W) s
  refine ⟨(injective_iff_map_eq_zero ((homologyToSupportedHPresheaf Z I n).app W).hom).2
    (fun s hs ↦ ?_), fun x ↦ ?_⟩
  · obtain ⟨s, rfl⟩ := hπ s
    rw [hfac] at hs
    cases n with
    | zero =>
      have hz := (supportedResolutionClass_zero_eq_zero_iff Z I W.unop _
        (Sheaf.H'.d_hom_app_iCycles_app
          (K := ((Sheaf.supportedSectionsFunctor Z).mapHomologicalComplex _).obj
            I.cocomplex) 0 s)).1 hs
      rw [hi (hz.trans (map_zero _).symm), map_zero]
    | succ n =>
      obtain ⟨t, ht⟩ := (supportedResolutionClass_succ_eq_zero_iff Z I W.unop _
        (Sheaf.H'.d_hom_app_iCycles_app
        (K := ((Sheaf.supportedSectionsFunctor Z).mapHomologicalComplex _).obj
          I.cocomplex) _ s)).1 hs
      have hs' : s = ((supportedSectionsResolutionComplex Z I).toCycles n (n + 1)).app W t :=
        hi (by rw [HomologicalComplex.iCycles_app_toCycles_app]; exact ht.symm)
      rw [hs', ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
        HomologicalComplex.toCycles_comp_homologyπ, NatTrans.app_zero]
      rfl
  · obtain ⟨s, hs, rfl⟩ := supportedResolutionClass_surjective Z I W.unop x
    obtain ⟨t, rfl⟩ := (supportedSectionsResolutionComplex Z I).exists_iCycles_app_eq
      (n + 1) (by simp) s hs
    exact ⟨((supportedSectionsResolutionComplex Z I).homologyπ n).app W t, hfac t⟩

/-- The supported sections of an injective resolution compute the supported
cohomology presheaf in every degree, including its restriction maps. -/
def homologyIsoSupportedHPresheaf (n : ℕ) :
    (((sheafToPresheaf _ _).mapHomologicalComplex _).obj
      (((Sheaf.supportedSectionsFunctor Z).mapHomologicalComplex _).obj I.cocomplex)).homology n ≅
        F.supportedHPresheaf Z n :=
  asIso (homologyToSupportedHPresheaf Z I n)

/-- The homology comparison sends a cycle to its supported cohomology class. -/
@[simp]
lemma homologyIsoSupportedHPresheaf_hom_app_homologyπ_apply (n : ℕ) :
    let K := ((sheafToPresheaf _ _).mapHomologicalComplex _).obj
      (((Sheaf.supportedSectionsFunctor Z).mapHomologicalComplex _).obj I.cocomplex)
    ∀ (W : (Opens X)ᵒᵖ) (s : (K.cycles n).obj W),
      (homologyIsoSupportedHPresheaf Z I n).hom.app W ((K.homologyπ n).app W s) =
        supportedResolutionClass Z I W.unop ((K.iCycles n).app W s)
          (Sheaf.H'.d_hom_app_iCycles_app
            (K := ((Sheaf.supportedSectionsFunctor Z).mapHomologicalComplex _).obj
              I.cocomplex) n s) := by
  intro K W s
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (homologyπ_homologyToSupportedHPresheaf Z I n) W) s

/-- Sheafifying the supported-section homology of an injective resolution
identifies the right derived supported-section sheaf with local cohomology. -/
def rightDerivedSupportedSectionsIsoSheaf (n : ℕ) :
    ((Sheaf.supportedSectionsFunctor Z).rightDerived n).obj F ≅ F.supportedHSheaf Z n := by
  let U := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let a := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let K := ((Sheaf.supportedSectionsFunctor Z).mapHomologicalComplex _).obj I.cocomplex
  let ε := asIso (sheafificationAdjunction (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).counit
  haveI : a.Additive := inferInstance
  haveI : a.PreservesHomology := Functor.preservesHomologyOfExact a
  exact I.isoRightDerivedObj (Sheaf.supportedSectionsFunctor Z) n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((Functor.mapHomologicalComplexCompIso ε _).app K).symm ≪≫
    (a.mapHomologicalComplexCompHomologyFunctorIso _ n).app
      ((U.mapHomologicalComplex _).obj K) ≪≫
    a.mapIso (homologyIsoSupportedHPresheaf Z I n)

end

end TauCeti
