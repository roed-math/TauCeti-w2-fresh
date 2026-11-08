/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Support
public import TauCeti.CategoryTheory.Abelian.RightDerived
public import TauCeti.Topology.Sheaves.LocalCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Local cohomology as a sheaf of modules on a scheme

The sections of an `𝒪_X`-module supported in a closed subset `Z` form an
`𝒪_X`-submodule sheaf. Its local scalar action is inherited from the coefficient
sheaf, including over opens whose functions do not extend globally. Deriving this
left exact functor in the category of all `𝒪_X`-modules defines the local cohomology
sheaves. We regard them as sheaves on `X`, with support in `Z`.

In degree zero the derived functor recovers the supported subsheaf, whose global
sections are the module of sections with support. The construction is natural in
the coefficient sheaf and its higher degrees vanish on injective modules.

## References

* The Stacks Project, Cohomology of Sheaves, Sections 20.21 and 20.34.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X : Scheme.{u}} (Z : Closeds X)

private def supportedPresheafSubmodule (M : X.Modules) : M.val.Submodule where
  obj W :=
    let N : Submodule Γ(X, W.unop) Γ(M, W.unop) :=
      { toAddSubmonoid := (((toSheaf X).obj M).supportedSections Z W.unop).toAddSubmonoid
        smul_mem' r s hs := by
          have hs' : M.presheaf.map (Z.complInclusion W.unop).op s = 0 :=
            (Sheaf.mem_supportedSections_iff _).1 hs
          exact (Sheaf.mem_supportedSections_iff _).2
            ((M.map_smul (Z.complInclusion W.unop) r s).trans (by rw [hs', smul_zero]; rfl)) }
    N
  map f := fun s hs ↦
    ((toSheaf X).obj M).map_mem_supportedSections_of_le (leOfHom f.unop) hs

private def supportedPresheafForgetIso (M : X.Modules) :
    (supportedPresheafSubmodule Z M).toPresheafOfModules.presheaf ≅
      ((toSheaf X).obj M).supportedSectionsPresheaf Z :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The `𝒪_X`-submodule sheaf of sections of `M` supported in `Z`, regarded as a
sheaf on `X`. Its sections on `W` vanish upon restriction to `W ∖ Z`. -/
def supportedSubsheaf (M : X.Modules) : X.Modules where
  val := (supportedPresheafSubmodule Z M).toPresheafOfModules
  isSheaf := (Presheaf.isSheaf_of_iso_iff (supportedPresheafForgetIso Z M)).2
    (((toSheaf X).obj M).isSheaf_supportedSectionsPresheaf Z)

/-- The inclusion of the supported subsheaf into its coefficient sheaf. -/
def supportedSubsheafι (M : X.Modules) : supportedSubsheaf Z M ⟶ M :=
  ⟨(supportedPresheafSubmodule Z M).ι⟩

/-- A section of the supported subsheaf vanishes on the complement of `Z`. -/
@[simp]
lemma restrict_supportedSubsheafι_app (M : X.Modules) (W : X.Opens)
    (s : Γ(supportedSubsheaf Z M, W)) :
    M.presheaf.map (Z.complInclusion W).op ((supportedSubsheafι Z M).app W s) = 0 :=
  (Sheaf.mem_supportedSections_iff _).1 s.2

/-- Global sections of the supported subsheaf are precisely global sections
with support, including their module structure over global functions. -/
def supportedSubsheafGlobalSectionsLinearEquiv (M : X.Modules) :
    Γ(supportedSubsheaf Z M, ⊤) ≃ₗ[Γ(X, ⊤)] sectionsWithSupport Z M where
  toFun s := ⟨s.1, (mem_sectionsWithSupport_iff Z).2 s.2⟩
  invFun s := ⟨s.1, (mem_sectionsWithSupport_iff Z).1 s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma coe_supportedSubsheafGlobalSectionsLinearEquiv (M : X.Modules)
    (s : Γ(supportedSubsheaf Z M, ⊤)) :
    (supportedSubsheafGlobalSectionsLinearEquiv Z M s).1 =
      (supportedSubsheafι Z M).app ⊤ s :=
  (rfl)

instance mono_supportedSubsheafι (M : X.Modules) : Mono (supportedSubsheafι Z M) := by
  have : Mono (supportedSubsheafι Z M).val :=
    inferInstanceAs (Mono (supportedPresheafSubmodule Z M).ι)
  exact (_root_.AlgebraicGeometry.Scheme.Modules.toPresheafOfModules X).mono_of_mono_map this

/-- A morphism whose sections vanish off `Z` factors through the supported
subsheaf. The factorization is unique since its inclusion is a monomorphism. -/
def supportedSubsheafLift {M N : X.Modules} (f : N ⟶ M)
    (h : ∀ (W : X.Opens) (s : Γ(N, W)),
      M.presheaf.map (Z.complInclusion W).op (f.app W s) = 0) :
    N ⟶ supportedSubsheaf Z M :=
  ⟨{ app W := ModuleCat.ofHom
        { toFun s := ⟨(f.val.app W).hom s, (Sheaf.mem_supportedSections_iff _).2 (h W.unop s)⟩
          map_add' s t := Subtype.ext (map_add (f.val.app W).hom s t)
          map_smul' r s := Subtype.ext ((f.val.app W).hom.map_smul r s) }
     naturality i := by
       ext s
       apply Subtype.ext
       exact ConcreteCategory.congr_hom (f.val.naturality i) s }⟩

@[reassoc (attr := simp)]
lemma supportedSubsheafLift_ι {M N : X.Modules} (f : N ⟶ M)
    (h : ∀ (W : X.Opens) (s : Γ(N, W)),
      M.presheaf.map (Z.complInclusion W).op (f.app W s) = 0) :
    supportedSubsheafLift Z f h ≫ supportedSubsheafι Z M = f :=
  (rfl)

/-- Applying a coefficient morphism to the supported subsheaves. -/
private def supportedSubsheafMap {M N : X.Modules} (f : M ⟶ N) :
    supportedSubsheaf Z M ⟶ supportedSubsheaf Z N :=
  supportedSubsheafLift Z (supportedSubsheafι Z M ≫ f) fun _ s ↦
    (Sheaf.mem_supportedSections_iff _).1
      (Sheaf.map_mem_supportedSections ((toSheaf X).map f) s.2)

@[reassoc (attr := simp)]
private lemma supportedSubsheafMap_ι {M N : X.Modules} (f : M ⟶ N) :
    supportedSubsheafMap Z f ≫ supportedSubsheafι Z N = supportedSubsheafι Z M ≫ f := by
  rfl

/-- The functor taking a module sheaf to its supported subsheaf. -/
def supportedSubsheafFunctor : X.Modules ⥤ X.Modules where
  obj := supportedSubsheaf Z
  map := supportedSubsheafMap Z
  map_id M := by
    rw [← cancel_mono (supportedSubsheafι Z M)]
    simp
  map_comp f g := by
    rw [← cancel_mono (supportedSubsheafι Z _)]
    simp

@[simp]
lemma supportedSubsheafFunctor_obj (M : X.Modules) :
    (supportedSubsheafFunctor Z).obj M = supportedSubsheaf Z M :=
  (rfl)

/-- The natural inclusion of the supported-subsheaf functor into the identity. -/
def supportedSubsheafFunctorι : supportedSubsheafFunctor Z ⟶ 𝟭 X.Modules where
  app M := eqToHom (supportedSubsheafFunctor_obj Z M) ≫ supportedSubsheafι Z M
  naturality _ _ _ := by rfl

@[simp]
lemma supportedSubsheafFunctorι_app (M : X.Modules) :
    (supportedSubsheafFunctorι Z).app M =
      eqToHom (supportedSubsheafFunctor_obj Z M) ≫ supportedSubsheafι Z M :=
  (rfl)

instance additive_supportedSubsheafFunctor : (supportedSubsheafFunctor Z).Additive where
  map_add := by intros; rfl

/-- Forgetting scalars identifies the supported subsheaf with the usual abelian
sheaf of supported sections, naturally in the coefficient module. -/
def supportedSubsheafFunctorForgetIso :
    supportedSubsheafFunctor Z ⋙ toSheaf X ≅ toSheaf X ⋙ Sheaf.supportedSectionsFunctor Z := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (supportedPresheafForgetIso Z M)) ?_
  intro M N f
  apply Sheaf.hom_ext
  ext W s
  apply Subtype.ext
  exact (Sheaf.coe_supportedSectionsFunctor_map_hom_app_apply Z
    ((toSheaf X).map f) W s).symm

/-- The supported-subsheaf functor preserves finite limits. -/
instance preservesFiniteLimits_supportedSubsheafFunctor :
    PreservesFiniteLimits (supportedSubsheafFunctor Z) := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2
  intro S hS
  let U := toSheaf X
  have hSU := shortExact_map_toSheaf hS
  have := hS.mono_f
  have : Mono ((toSheaf X).map S.f) := Functor.map_mono _ _
  have := hSU.mono_f
  have he := Sheaf.exact_map_supportedSectionsFunctor Z hSU.exact
  have hm : Mono ((Sheaf.supportedSectionsFunctor Z).map (U.map S.f)) := inferInstance
  have he' : ((S.map (supportedSubsheafFunctor Z)).map U).Exact := by
    rw [← ShortComplex.map_comp]
    exact (ShortComplex.exact_iff_of_iso
      (S.mapNatIso (supportedSubsheafFunctorForgetIso Z))).2
      (by simpa only [ShortComplex.map_comp] using he)
  have hm' : Mono (U.map ((supportedSubsheafFunctor Z).map S.f)) := by
    have h : U.map ((supportedSubsheafFunctor Z).map S.f) ≫
        (supportedSubsheafFunctorForgetIso Z).hom.app S.X₂ =
        (supportedSubsheafFunctorForgetIso Z).hom.app S.X₁ ≫
          (Sheaf.supportedSectionsFunctor Z).map (U.map S.f) :=
      (supportedSubsheafFunctorForgetIso Z).hom.naturality S.f
    have : Mono (U.map ((supportedSubsheafFunctor Z).map S.f) ≫
        (supportedSubsheafFunctorForgetIso Z).hom.app S.X₂) := by
      rw [h]
      exact mono_comp _ _
    exact mono_of_mono _ ((supportedSubsheafFunctorForgetIso Z).hom.app S.X₂)
  exact ⟨U.reflects_exact_of_faithful _ he', U.mono_of_mono_map hm'⟩

/-- The supported subsheaf has zero stalks outside its prescribed support. -/
theorem isZero_stalk_supportedSubsheaf_of_notMem (M : X.Modules) {x : X} (hx : x ∉ Z) :
    IsZero (TopCat.Presheaf.stalk ((toSheaf X).obj (supportedSubsheaf Z M)).obj x) := by
  let S := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have h := Sheaf.isZero_stalk_supportedHSheaf_of_notMem ((toSheaf X).obj M) Z hx 0
  exact h.of_iso (S.mapIso ((supportedSubsheafFunctorForgetIso Z).app M) ≪≫
    S.mapIso (((toSheaf X).obj M).supportedHSheafZeroIso Z).symm)

/-- The local cohomology sheaf `𝓗_Z^q(M) = R^q H_Z(M)` of `𝒪_X`-modules,
computed by an injective resolution in the category of all `𝒪_X`-modules. -/
abbrev localCohomologySheaf (M : X.Modules) (q : ℕ) : X.Modules :=
  ((supportedSubsheafFunctor Z).rightDerived q).obj M

/-- Zeroth local cohomology recovers the supported subsheaf, naturally in `M`. -/
def localCohomologySheafZeroIso :
    (supportedSubsheafFunctor Z).rightDerived 0 ≅ supportedSubsheafFunctor Z :=
  (supportedSubsheafFunctor Z).rightDerivedZeroIsoSelf

/-- The global sections of zeroth local cohomology recover sections with
support, linearly over the global functions. -/
def localCohomologySheafZeroSectionsLinearEquiv (M : X.Modules) :
    Γ(localCohomologySheaf Z M 0, ⊤) ≃ₗ[Γ(X, ⊤)] sectionsWithSupport Z M :=
  (AlgebraicGeometry.Scheme.Modules.sectionsLinearEquiv
    ((localCohomologySheafZeroIso Z).app M) ⊤).trans
      (supportedSubsheafGlobalSectionsLinearEquiv Z M)

/-- Global sections of zeroth local cohomology agree with degree-zero
cohomology with supports. -/
def localCohomologySheafZeroCohomologyWithSupportLinearEquiv (M : X.Modules) :
    Γ(localCohomologySheaf Z M 0, ⊤) ≃ₗ[Γ(X, ⊤)] cohomologyWithSupport Z M 0 :=
  (localCohomologySheafZeroSectionsLinearEquiv Z M).trans
    (cohomologyWithSupportZeroLinearEquiv Z M).symm

/-- Every local cohomology sheaf has zero stalks off `Z`. No finiteness or
quasi-coherence hypothesis is needed. -/
theorem isZero_stalk_localCohomologySheaf_of_notMem (M : X.Modules) {x : X}
    (hx : x ∉ Z) (q : ℕ) :
    IsZero (TopCat.Presheaf.stalk ((toSheaf X).obj (localCohomologySheaf Z M q)).obj x) := by
  let G := toSheaf X ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let P := injectiveResolution M
  let K := ((supportedSubsheafFunctor Z).mapHomologicalComplex _).obj P.cocomplex
  refine IsZero.of_iso ?_ (G.mapIso (P.isoRightDerivedObj (supportedSubsheafFunctor Z) q) ≪≫
    ((G.mapHomologicalComplexCompHomologyFunctorIso _ q).app K).symm)
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ q).1
  exact ShortComplex.exact_of_isZero_X₂ _
    (isZero_stalk_supportedSubsheaf_of_notMem Z (P.cocomplex.X q) hx)

/-- Higher local cohomology sheaves vanish on injective coefficient modules. -/
theorem isZero_localCohomologySheaf_succ_of_injective (M : X.Modules) [Injective M] (q : ℕ) :
    IsZero (localCohomologySheaf Z M (q + 1)) :=
  (supportedSubsheafFunctor Z).isZero_rightDerived_obj_injective_succ q M

end

end TauCeti.AlgebraicGeometry.Scheme.Modules
