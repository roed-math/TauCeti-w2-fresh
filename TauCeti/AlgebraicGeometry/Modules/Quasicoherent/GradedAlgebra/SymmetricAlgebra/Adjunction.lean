/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.GradedAlgebra.Sections
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Sections
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.GradedMap
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous

/-!
# The universal property of the graded symmetric algebra

For a quasicoherent sheaf `F` on a scheme `X` and a graded quasicoherent algebra `A = ⨁ₙ Aₙ`,
a morphism of quasicoherent sheaves `φ : F ⟶ A₁` extends uniquely to a morphism of graded
quasicoherent algebras `Sym F ⟶ A`. In other words, the graded symmetric algebra functor is left
adjoint to the degree-one functor:

`gradedSymmetricAlgebraAdjunction X : gradedSymmetricAlgebra X ⊣ degreeOne`.

Its counit `Sym A₁ ⟶ A` extends the identity of `A₁`
(`gradedSymmetricAlgebraAdjunction_counit_app`). Its unit is the identification `F ≅ Sym¹ F`
(`gradedSymmetricAlgebraAdjunction_unit`), an isomorphism, matching the fact that
`gradedSymmetricAlgebra X` is fully faithful: it identifies quasicoherent sheaves with its
essential image, the graded quasicoherent algebras freely generated in degree one. Under graded
relative `Spec` these are the coordinate algebras of the linear schemes `Spec_X Sym F` over `X`.

The extension `Symⁿ F ⟶ Aₙ` is built over each open `U` from the universal property of the
symmetric algebra of the `Γ(X, U)`-module `Γ(F, U)`, with values in the graded ring
`⨁ n, Γ(Aₙ, U)` of sections of `A`, and then sheafified
(`TauCeti.SheafOfModules.symmetricPowerLift`); its compatibility with the unit and
the multiplication is checked on sections and transported along the monoidal sheafification
adjunction. Uniqueness holds because `Sym F` is generated in degree one
(`gradedSymmetricAlgebra_hom_ext`).

## Main declarations

* `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebraLift`: the morphism `Sym F ⟶ A` of graded
  quasicoherent algebras extending `φ : F ⟶ A₁`, characterized by
  `gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift`, and natural on both
  sides (`gradedSymmetricAlgebraLift_comp`, `gradedSymmetricAlgebra_map_comp_lift`);
* `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebraAdjunction`: the adjunction
  `gradedSymmetricAlgebra X ⊣ degreeOne`, whose unit is the identification `F ≅ Sym¹ F`
  (`gradedSymmetricAlgebraAdjunction_unit`) and whose counit `Sym A₁ ⟶ A` extends the identity
  of `A₁` (`gradedSymmetricAlgebraAdjunction_counit_app`).
* `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebraSectionsEquiv`: over an affine open `U`, the
  sections of `Sym F` are the symmetric algebra of the sections, `Sym Γ(F, U) ≃ ⨁ n, Γ(Symⁿ F, U)`,
  degree by degree (`gradedSymmetricAlgebraSectionsEquiv_mem`,
  `gradedSymmetricAlgebraSectionsEquiv_symm_mem`); in particular they are generated in degree one
  (`adjoin_gradedSectionsGrading_one_gradedSymmetricAlgebra`).

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
-/

public section

open CategoryTheory MonoidalCategory Opposite DirectSum

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory.CommMon GradedQuasicoherentAlgebra

universe u

noncomputable section

section Sections

/-! ### The extension on sections -/

variable {X : Scheme.{u}} {F : X.Modules} {A : CommMon (GradedObject ℕ X.Modules)}

/-- Over an open `U`, the algebra map `Sym Γ(F, U) → ⨁ n, Γ(Aₙ, U)` extending the sections
`Γ(F, U) → Γ(A₁, U)` of `φ` into degree one. -/
private def sectionsLift (φ : F ⟶ A.X 1) (U : X.Opens) :
    SymmetricAlgebra Γ(X, U) (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op U))
      →ₐ[Γ(X, U)] ⨁ n, Γ(A.X n, U) :=
  SymmetricAlgebra.lift ((DirectSum.lof Γ(X, U) ℕ (fun n ↦ Γ(A.X n, U)) 1) ∘ₗ
    ((Scheme.Modules.sectionsFunctor U).map φ).hom)

private lemma sectionsLift_ι (φ : F ⟶ A.X 1) (U : X.Opens)
    (m : PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op U)) :
    sectionsLift φ U (SymmetricAlgebra.ι _ _ m) =
      DirectSum.of (fun n ↦ Γ(A.X n, U)) 1 (φ.app U m) :=
  SymmetricAlgebra.lift_ι_apply _ m

/-- The degree-`n` part `Symⁿ Γ(F, U) → Γ(Aₙ, U)` of the extension on sections. -/
private def presheafLiftApp (φ : F ⟶ A.X 1) (n : ℕ) (U : X.Opens) :
    (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op U)).symmetricPower n ⟶
      (Scheme.Modules.sectionsFunctor U).obj (A.X n) :=
  ConcreteCategory.ofHom (C := ModuleCat (X.presheaf.obj (op U)))
    (DirectSum.component (X.presheaf.obj (op U)) ℕ (fun n ↦ Γ(A.X n, U)) n ∘ₗ
    (sectionsLift φ U).toLinearMap ∘ₗ
      (SymmetricAlgebra.homogeneousSubmodule Γ(X, U)
        (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op U)) n).subtype)

private lemma presheafLiftApp_apply (φ : F ⟶ A.X 1) (n : ℕ) (U : X.Opens)
    (x : (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op U)).symmetricPower n) :
    presheafLiftApp φ n U x = sectionsLift φ U x.1 n :=
  (rfl)

/-- The extension on sections commutes with restriction. -/
private lemma sectionsLift_restrict (φ : F ⟶ A.X 1) {U V : X.Opens} (f : V ⟶ U) :
    (sectionsLift φ V : SymmetricAlgebra Γ(X, V)
        (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op V)) →+* _).comp
      (SymmetricAlgebra.mapₛₗ
        ((ModuleCat.semilinearMapAddEquiv (X.presheaf.map f.op).hom _ _).symm
          (PresheafOfModulesOfCommRing.map (R := X.presheaf) F.val f.op))) =
      (A.restrictGradedSections f).comp (sectionsLift φ U : SymmetricAlgebra Γ(X, U)
        (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op U)) →+* _) := by
  refine SymmetricAlgebra.ringHom_ext (RingHom.ext fun r ↦ ?_) fun m ↦ ?_
  · simp
  · simp only [RingHom.comp_apply, SymmetricAlgebra.mapₛₗ_ι]
    -- The restricted generator lives in the sections over `V` written through the semilinear
    -- restriction map; `sectionsLift_ι` sees them only up to unfolding that map.
    erw [sectionsLift_ι, sectionsLift_ι, restrictGradedSections_of]
    exact congrArg _ (PresheafOfModules.naturality_apply φ.val f.op m)

/-- The degree-`n` part of the extension, as a morphism of presheaves of modules
`Symⁿ F.val ⟶ Aₙ.val` out of the presheaf symmetric power. -/
private def presheafLift (φ : F ⟶ A.X 1) (n : ℕ) :
    (PresheafOfModulesOfCommRing.symmetricPower (R := X.presheaf) n).obj F.val ⟶ (A.X n).val :=
  PresheafOfModulesOfCommRing.homMk (fun U ↦ presheafLiftApp φ n U.unop)
    (fun {U V} f ↦ by
      ext x
      -- Restriction of scalars and the sections of the presheaves are `rfl`-wrappers that `rw`
      -- does not see through.
      erw [ModuleCat.comp_apply, ModuleCat.restrictScalars.map_apply, ModuleCat.comp_apply,
        presheafLiftApp_apply, presheafLiftApp_apply,
        PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply]
      exact (congrArg (· n) (RingHom.congr_fun (sectionsLift_restrict φ f.unop) x.1)).trans
        (A.restrictGradedSections_apply f.unop _ n))

private lemma presheafLift_app_apply (φ : F ⟶ A.X 1) (n : ℕ) (U : X.Opensᵒᵖ)
    (x : (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val U).symmetricPower n) :
    (presheafLift φ n).app U x = sectionsLift φ U.unop x.1 n :=
  (rfl)

variable (X) in
/-- The inclusion of `𝒪_X`-modules into presheaves of modules over the commutative structure
presheaf, the form in which its lax monoidal structure is used here. -/
private abbrev forgetPresheaf : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
  SheafOfModules.forget _

private instance : (forgetPresheaf X).LaxMonoidal :=
  TauCeti.SheafOfModules.forgetLaxMonoidal X.sheaf

/-- On a pure tensor `x ⊗ₜ y` of sections over `U`, the tensor product of the degree-`i` and
degree-`j` parts of the extension, followed by the multiplication of `A`, is the multiplication of
`A` applied to the tensor product of the homogeneous components of the images of `x` and `y`
(their product in the graded ring of sections, by `sections_gMul_def`). -/
private lemma presheafLift_tensorHom_comp_mul_app_tmul (φ : F ⟶ A.X 1) (i j : ℕ)
    (U : X.Opensᵒᵖ)
    (x : (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val U).symmetricPower i)
    (y : (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val U).symmetricPower j) :
    ((presheafLift φ i ⊗ₘ presheafLift φ j) ≫
        Functor.LaxMonoidal.μ (forgetPresheaf X) (A.X i) (A.X j) ≫
          (forgetPresheaf X).map (A.toMon.mul i j)).app U (x ⊗ₜ y) =
      (A.toMon.mul i j).app U.unop
        (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U.unop) _ _
          (sectionsLift φ U.unop x.1 i ⊗ₜ sectionsLift φ U.unop y.1 j)) :=
  (rfl)

/-- The extension is multiplicative on sections. -/
private lemma presheafLift_mul (φ : F ⟶ A.X 1) (i j : ℕ) :
    (presheafLift φ i ⊗ₘ presheafLift φ j) ≫
        Functor.LaxMonoidal.μ (forgetPresheaf X) (A.X i) (A.X j) ≫
          (forgetPresheaf X).map (A.toMon.mul i j) =
      PresheafOfModulesOfCommRing.symmetricPowerMul F.val i j ≫ presheafLift φ (i + j) := by
  ext1 U
  refine ModuleCat.MonoidalCategory.tensor_ext fun x y ↦ ?_
  have hx : sectionsLift φ U.unop x.1 = DirectSum.of _ i (sectionsLift φ U.unop x.1 i) :=
    SymmetricAlgebra.lift_lof_comp_apply_of_mem_homogeneousSubmodule _ _ _ x.2
  have hy : sectionsLift φ U.unop y.1 = DirectSum.of _ j (sectionsLift φ U.unop y.1 j) :=
    SymmetricAlgebra.lift_lof_comp_apply_of_mem_homogeneousSubmodule _ _ _ y.2
  refine (presheafLift_tensorHom_comp_mul_app_tmul φ i j U x y).trans ?_
  refine Eq.trans ?_ (presheafLift_app_apply φ (i + j) U
    ((PresheafOfModulesOfCommRing.symmetricPowerMul F.val i j).app U (x ⊗ₜ y))).symm
  rw [← sections_gMul_def]
  -- The sections of the presheaf symmetric power are those of `ModuleCat.symmetricPower` only up
  -- to `rfl`.
  conv_rhs => erw [PresheafOfModulesOfCommRing.symmetricPowerMul_app,
    ModuleCat.symmetricPower.coe_mul_tmul, map_mul, hx, hy, DirectSum.of_mul_of]
  exact (DirectSum.of_eq_same (β := fun n ↦ Γ(A.X n, U.unop)) _ _).symm

/-- The extension is unital on sections. -/
private lemma presheafLift_one (φ : F ⟶ A.X 1) :
    (PresheafOfModulesOfCommRing.symmetricPowerZeroIso X.presheaf).inv.app F.val ≫
        presheafLift φ 0 =
      A.toMon.one.val := by
  ext1 U
  -- `PresheafOfModulesOfCommRing.symmetricPowerZeroIso` is stated over `X.presheaf`, the
  -- composite over the ring presheaf of `X.ringCatSheaf`.
  erw [PresheafOfModules.comp_app, PresheafOfModulesOfCommRing.symmetricPowerZeroIso_inv_app_app]
  ext
  refine Eq.trans (presheafLift_app_apply φ 0 U _) ?_
  refine (congrArg (fun z ↦ sectionsLift φ U.unop z 0)
    (ModuleCat.symmetricPower.coe_iso₀_inv_apply _ 1)).trans ?_
  rw [map_one, map_one, DirectSum.one_def, DirectSum.of_eq_same, sections_gOne_def,
    Scheme.Modules.sectionsFunctor_ε]
  exact Scheme.Modules.Hom.app_apply A.toMon.one U.unop _

/-- In degree one, the extension restricts to `φ` along `Sym¹ F.val ≅ F.val`. -/
private lemma presheafLift_degreeOne (φ : F ⟶ A.X 1) :
    (PresheafOfModulesOfCommRing.symmetricPowerOneIso X.presheaf).inv.app F.val ≫
        presheafLift φ 1 = φ.val := by
  ext1 U
  -- As in `presheafLift_one`.
  erw [PresheafOfModules.comp_app, PresheafOfModulesOfCommRing.symmetricPowerOneIso_inv_app_app]
  ext m
  refine Eq.trans (presheafLift_app_apply φ 1 U _) ?_
  refine (congrArg (fun z ↦ sectionsLift φ U.unop z 1)
    (ModuleCat.symmetricPower.coe_iso₁_inv_apply
      (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val U) m)).trans ?_
  refine (congrArg (· 1) (sectionsLift_ι φ U.unop m)).trans ?_
  rw [DirectSum.of_eq_same]
  exact Scheme.Modules.Hom.app_apply φ U.unop m

variable (F) in
/-- The symmetric power `Symⁿ F`, typed as an `𝒪_X`-module so that the monoidal structure of
`X.Modules` applies to it. -/
private abbrev symPow (n : ℕ) : X.Modules :=
  (SheafOfModules.symmetricPower X.sheaf n).obj F

variable (F) in
/-- The multiplication `Symⁱ F ⊗ Symʲ F ⟶ Symⁱ⁺ʲ F`, typed in `X.Modules`. -/
private abbrev symPowMul (i j : ℕ) : symPow F i ⊗ symPow F j ⟶ symPow F (i + j) :=
  SheafOfModules.symmetricPowerMul F i j

/-- The degree-`n` component `Symⁿ F ⟶ Aₙ` of the extension of `φ`. -/
private def liftDegree (φ : F ⟶ A.X 1) (n : ℕ) : symPow F n ⟶ A.X n :=
  TauCeti.SheafOfModules.symmetricPowerLift (R := X.sheaf) (presheafLift φ n)

private lemma liftDegree_mul (φ : F ⟶ A.X 1) (i j : ℕ) :
    (liftDegree φ i ⊗ₘ liftDegree φ j) ≫ A.toMon.mul i j =
      symPowMul F i j ≫ liftDegree φ (i + j) :=
  TauCeti.SheafOfModules.symmetricPowerLift_mul (R := X.sheaf) (presheafLift φ) A.toMon.mul
    (presheafLift_mul φ) i j

private lemma liftDegree_one (φ : F ⟶ A.X 1) :
    ((SheafOfModules.symmetricPowerZeroIso X.sheaf).inv.app F : 𝟙_ X.Modules ⟶ symPow F 0) ≫
      liftDegree φ 0 = A.toMon.one :=
  TauCeti.SheafOfModules.symmetricPowerZeroIso_inv_app_comp_symmetricPowerLift (R := X.sheaf)
    (presheafLift_one φ)

/-- In degree one, the extension of `φ` restricts to `φ` along `F ≅ Sym¹ F`. It is stated for `φ`
followed by an identification `h` of its target with `A₁`, the form in which
`gradedSymmetricAlgebraLift` uses it. -/
private lemma liftDegree_degreeOne {M : X.Modules} (φ : F ⟶ M) (h : M = A.X 1) :
    ((SheafOfModules.symmetricPowerOneIso X.sheaf).inv.app F : F ⟶ symPow F 1) ≫
      liftDegree (φ ≫ eqToHom h) 1 ≫ eqToHom h.symm = φ := by
  subst h
  -- `symPow F 1` is a module over `ringCatSheaf X.sheaf`, identified with an object of
  -- `X.Modules` only by unfolding, so the identity laws are rewritten up to that unfolding.
  erw [eqToHom_refl, Category.comp_id, Category.comp_id]
  exact TauCeti.SheafOfModules.symmetricPowerOneIso_inv_app_comp_symmetricPowerLift
    (R := X.sheaf) (presheafLift_degreeOne φ)

/-- On the sections over an affine open `U`, the degree-`n` component of the extension of `φ`,
precomposed with the identification `Symⁿ Γ(F, U) ≅ Γ(Symⁿ F, U)`, is the degree-`n` part of the
extension on sections. -/
private lemma liftDegree_app_symmetricPowerSectionsIso_hom [F.IsQuasicoherent] (φ : F ⟶ A.X 1)
    (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (x : (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op U)).symmetricPower n) :
    (liftDegree φ n).app U ((F.symmetricPowerSectionsIso hU n).hom x) =
      presheafLiftApp φ n U x := by
  -- `liftDegree` is the sheafification of `presheafLift` after `symmetricPowerIso`, so on the
  -- image of the sheafification unit it is `presheafLift`, by the triangle identity.
  have key : (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((PresheafOfModulesOfCommRing.symmetricPower (R := X.presheaf) n).obj F.val) ≫
      ((SheafOfModules.symmetricPowerIso n F).inv ≫
        TauCeti.SheafOfModules.symmetricPowerLift (R := X.sheaf) (presheafLift φ n)).val =
      presheafLift φ n := by
    -- `rw` sees the module sheaves of `X.Modules` and of the sheaf of rings only up to
    -- unfolding, so `symmetricPowerLift_def` and the cancellation are applied as terms.
    have e := (congrArg ((SheafOfModules.symmetricPowerIso n F).inv ≫ ·)
      (TauCeti.SheafOfModules.symmetricPowerLift_def (R := X.sheaf) (presheafLift φ n))).trans
        (Iso.inv_hom_id_assoc _ _)
    exact (congrArg (_ ≫ ·) (congrArg _root_.SheafOfModules.Hom.val e)).trans
      (TauCeti.SheafOfModules.unit_comp_val_sheafification_map_comp_sheafificationIso_hom _)
  rw [Scheme.Modules.symmetricPowerSectionsIso_hom_apply]
  exact ConcreteCategory.congr_hom (congrArg (fun α ↦ α.app (op U)) key) x

/-- Over an affine open `U`, if the degree-`n` component of the extension of `φ` is an
isomorphism, then every section of `Aₙ` over `U` is the degree-`n` part of the extension on
sections of an element of `Symⁿ Γ(F, U)`. -/
private lemma exists_mem_sectionsLift_eq_of [F.IsQuasicoherent] (φ : F ⟶ A.X 1) (n : ℕ)
    [IsIso (liftDegree φ n)] {U : X.Opens} (hU : IsAffineOpen U) (y : Γ(A.X n, U)) :
    ∃ x ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(X, U)
        (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op U)) n,
      sectionsLift φ U x = DirectSum.of (fun n ↦ Γ(A.X n, U)) n y := by
  have : IsIso ((_root_.SheafOfModules.forget X.ringCatSheaf).map (liftDegree φ n)) :=
    Functor.map_isIso _ (liftDegree φ n)
  have hbij : Function.Bijective ((liftDegree φ n).app U) :=
    ConcreteCategory.bijective_of_isIso ((PresheafOfModules.evaluation _ (op U)).map
      ((_root_.SheafOfModules.forget _).map (liftDegree φ n)))
  obtain ⟨z, rfl⟩ := hbij.2 y
  obtain ⟨x, rfl⟩ :=
    (ConcreteCategory.bijective_of_isIso (F.symmetricPowerSectionsIso hU n).hom).2 z
  refine ⟨x.1, x.2, ?_⟩
  rw [liftDegree_app_symmetricPowerSectionsIso_hom, presheafLiftApp_apply]
  exact SymmetricAlgebra.lift_lof_comp_apply_of_mem_homogeneousSubmodule _ _ _ x.2

/-- Over an affine open `U`, if every component of the extension of `φ` is an isomorphism, then
the extension on sections is injective. Its degree-`n` part is the bijection
`Symⁿ Γ(F, U) ≅ Γ(Symⁿ F, U)` followed by the degree-`n` component of the extension, and the
degree-`n` parts span `Sym Γ(F, U)`. -/
private lemma sectionsLift_injective_of [F.IsQuasicoherent] (φ : F ⟶ A.X 1)
    [∀ n, IsIso (liftDegree φ n)] {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective (sectionsLift φ U) := by
  have hinj (n : ℕ) : Function.Injective (presheafLiftApp φ n U) := by
    have : IsIso ((_root_.SheafOfModules.forget X.ringCatSheaf).map (liftDegree φ n)) :=
      Functor.map_isIso _ (liftDegree φ n)
    intro x y h
    rw [← liftDegree_app_symmetricPowerSectionsIso_hom φ n hU,
      ← liftDegree_app_symmetricPowerSectionsIso_hom φ n hU] at h
    exact (ConcreteCategory.bijective_of_isIso (F.symmetricPowerSectionsIso hU n).hom).1
      ((ConcreteCategory.bijective_of_isIso ((PresheafOfModules.evaluation _ (op U)).map
        ((_root_.SheafOfModules.forget _).map (liftDegree φ n)))).1 h)
  refine (injective_iff_map_eq_zero (sectionsLift φ U)).mpr fun x hx ↦ ?_
  have hmem : x ∈ ⨆ n, TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(X, U)
      (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op U)) n := by
    rw [TauCeti.SymmetricAlgebra.iSup_homogeneousSubmodule_eq_top]
    trivial
  obtain ⟨c, hc, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hmem
  have hof (m : ℕ) : sectionsLift φ U (c m) =
      DirectSum.of (fun n ↦ Γ(A.X n, U)) m (sectionsLift φ U (c m) m) :=
    SymmetricAlgebra.lift_lof_comp_apply_of_mem_homogeneousSubmodule _ _ _ (hc m)
  have hzero (n : ℕ) : c n = 0 := by
    have h := congrArg (DirectSum.component Γ(X, U) ℕ (fun n ↦ Γ(A.X n, U)) n) hx
    rw [map_finsuppSum, map_finsuppSum, map_zero, Finsupp.sum_eq_single n] at h
    · refine congrArg Subtype.val (hinj n (a₁ := ⟨c n, hc n⟩) (a₂ := 0) ?_)
      rw [map_zero, presheafLiftApp_apply]
      exact h
    · intro m _ hmn
      rw [hof, ← DirectSum.apply_eq_component, DirectSum.of_eq_of_ne _ _ _ hmn.symm]
    · intro _
      rw [map_zero, map_zero]
  exact Finset.sum_eq_zero fun n _ ↦ hzero n

/-- Over an affine open `U`, if every component of the extension of `φ` is an isomorphism, then
the extension on sections `Sym Γ(F, U) → ⨁ n, Γ(Aₙ, U)` is bijective. -/
private lemma bijective_sectionsLift_of [F.IsQuasicoherent] (φ : F ⟶ A.X 1)
    [∀ n, IsIso (liftDegree φ n)] {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (sectionsLift φ U) := by
  refine ⟨sectionsLift_injective_of φ hU, fun w ↦ ?_⟩
  induction w using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of n y =>
    obtain ⟨x, -, hx⟩ := exists_mem_sectionsLift_eq_of φ n hU y
    exact ⟨x, hx⟩
  | add w w' hw hw' =>
    obtain ⟨x, rfl⟩ := hw
    obtain ⟨x', rfl⟩ := hw'
    exact ⟨x + x', map_add _ _ _⟩

end Sections

/-! ### The universal property -/

variable {X : Scheme.{u}}

/-- The morphism of graded quasicoherent algebras `Sym F ⟶ A` extending a morphism
`φ : F ⟶ A₁` of quasicoherent sheaves into the degree-one component of `A`
(`gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift`). -/
def gradedSymmetricAlgebraLift {F : QuasicoherentSheaf X} {A : GradedQuasicoherentAlgebra X}
    (φ : F ⟶ degreeOne.obj A) : (gradedSymmetricAlgebra X).obj F ⟶ A :=
  homMkOfEq (funext (gradedSymmetricAlgebra_obj_obj_X F)) rfl (one_gradedSymmetricAlgebra F)
    (Category.comp_id _).symm (mul_gradedSymmetricAlgebra F)
    (fun i j ↦ by
      rw [eqToHom_refl, eqToHom_refl, Category.id_comp]
      exact (Category.comp_id _).symm)
    (liftDegree (A := A.obj) (φ.hom ≫ eqToHom (degree_obj_obj A 1)))
    (liftDegree_one _) (liftDegree_mul _)

/-- The degree-`n` component of `gradedSymmetricAlgebraLift φ` is `liftDegree`, up to the
identification `gradedSymmetricAlgebra_obj_obj_X`. -/
private lemma gradedSymmetricAlgebraLift_hom_hom_hom {F : QuasicoherentSheaf X}
    {A : GradedQuasicoherentAlgebra X} (φ : F ⟶ degreeOne.obj A) (n : ℕ) :
    (gradedSymmetricAlgebraLift φ).hom.hom.hom n =
      eqToHom (gradedSymmetricAlgebra_obj_obj_X F n) ≫
        liftDegree (A := A.obj) (φ.hom ≫ eqToHom (degree_obj_obj A 1)) n ≫ eqToHom rfl :=
  homMkOfEq_hom_hom_hom _ _ _ _ _ _ _ _ _ n

/-- The degree-`n` component of `gradedSymmetricAlgebraLift φ`, as a morphism of quasicoherent
sheaves, is `liftDegree`, up to the identifications `degree_obj_gradedSymmetricAlgebra_obj` and
`degree_obj_obj`. -/
private lemma degree_map_gradedSymmetricAlgebraLift_hom {F : QuasicoherentSheaf X}
    {A : GradedQuasicoherentAlgebra X} (φ : F ⟶ degreeOne.obj A) (n : ℕ) :
    ((degree n).map (gradedSymmetricAlgebraLift φ)).hom =
      eqToHom (degree_obj_gradedSymmetricAlgebra_obj F n) ≫
        liftDegree (A := A.obj) (φ.hom ≫ eqToHom (degree_obj_obj A 1)) n ≫
        eqToHom (degree_obj_obj A n).symm := by
  rw [degree_map_hom, gradedSymmetricAlgebraLift_hom_hom_hom]
  -- As in `degree_map_gradedSymmetricAlgebra_map_hom`, the transports are composed partly in
  -- `SheafOfModules X.ringCatSheaf` and partly in `X.Modules`, whose instances `simp` does not
  -- identify, so they are removed up to heterogeneous equality.
  exact eq_of_heq (((eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans
    ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)))).trans
      ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm)

/-- The degree-one component of `gradedSymmetricAlgebraLift φ` is `φ`, through the
identification `F ≅ Sym¹ F`. -/
@[reassoc (attr := simp)]
theorem gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift
    {F : QuasicoherentSheaf X} {A : GradedQuasicoherentAlgebra X} (φ : F ⟶ degreeOne.obj A) :
    (gradedSymmetricAlgebraDegreeOneIso X).inv.app F ≫
      degreeOne.map (gradedSymmetricAlgebraLift φ) = φ := by
  ext1
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    gradedSymmetricAlgebraDegreeOneIso_inv_app_hom, degree_map_gradedSymmetricAlgebraLift_hom,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact liftDegree_degreeOne _ _

variable (X) in
/-- The graded symmetric algebra functor is left adjoint to the degree-one functor: morphisms of
graded quasicoherent algebras `Sym F ⟶ A` correspond to morphisms of quasicoherent sheaves
`F ⟶ A₁`, by restriction to degree one along `F ≅ Sym¹ F` and by `gradedSymmetricAlgebraLift`. -/
def gradedSymmetricAlgebraAdjunction :
    gradedSymmetricAlgebra X ⊣ (degreeOne : GradedQuasicoherentAlgebra X ⥤ QuasicoherentSheaf X) :=
  Adjunction.mkOfHomEquiv
    { homEquiv F A :=
        { toFun f := (gradedSymmetricAlgebraDegreeOneIso X).inv.app F ≫ degreeOne.map f
          invFun := gradedSymmetricAlgebraLift
          left_inv f := gradedSymmetricAlgebra_hom_ext (by
            rw [← cancel_epi ((gradedSymmetricAlgebraDegreeOneIso X).inv.app F),
              gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift])
          right_inv := gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift }
      homEquiv_naturality_left_symm {F' F A} g φ := by
        refine gradedSymmetricAlgebra_hom_ext ?_
        simp only [Equiv.coe_fn_symm_mk]
        rw [← cancel_epi ((gradedSymmetricAlgebraDegreeOneIso X).inv.app F'),
          gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift, Functor.map_comp,
          ← Functor.comp_map, ← NatTrans.naturality_assoc, Functor.id_map,
          gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift]
      homEquiv_naturality_right f g := by
        simp only [Equiv.coe_fn_mk, Functor.map_comp, Category.assoc] }

/-- The bijection of `gradedSymmetricAlgebraAdjunction` restricts a morphism `Sym F ⟶ A` to
degree one. -/
@[simp]
theorem gradedSymmetricAlgebraAdjunction_homEquiv_apply {F : QuasicoherentSheaf X}
    {A : GradedQuasicoherentAlgebra X} (f : (gradedSymmetricAlgebra X).obj F ⟶ A) :
    (gradedSymmetricAlgebraAdjunction X).homEquiv F A f =
      (gradedSymmetricAlgebraDegreeOneIso X).inv.app F ≫ degreeOne.map f := by
  simp only [gradedSymmetricAlgebraAdjunction, Adjunction.mkOfHomEquiv_homEquiv, Equiv.coe_fn_mk]

/-- The inverse bijection of `gradedSymmetricAlgebraAdjunction` is `gradedSymmetricAlgebraLift`. -/
@[simp]
theorem gradedSymmetricAlgebraAdjunction_homEquiv_symm_apply {F : QuasicoherentSheaf X}
    {A : GradedQuasicoherentAlgebra X} (φ : F ⟶ degreeOne.obj A) :
    ((gradedSymmetricAlgebraAdjunction X).homEquiv F A).symm φ = gradedSymmetricAlgebraLift φ := by
  simp only [gradedSymmetricAlgebraAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
    Equiv.coe_fn_symm_mk]

/-- Postcomposing `gradedSymmetricAlgebraLift φ` with a morphism `f` of graded quasicoherent
algebras extends `φ` followed by the degree-one component of `f`. -/
@[simp, reassoc]
theorem gradedSymmetricAlgebraLift_comp {F : QuasicoherentSheaf X}
    {A B : GradedQuasicoherentAlgebra X} (φ : F ⟶ degreeOne.obj A) (f : A ⟶ B) :
    gradedSymmetricAlgebraLift φ ≫ f = gradedSymmetricAlgebraLift (φ ≫ degreeOne.map f) := by
  rw [← gradedSymmetricAlgebraAdjunction_homEquiv_symm_apply,
    ← gradedSymmetricAlgebraAdjunction_homEquiv_symm_apply,
    Adjunction.homEquiv_naturality_right_symm]

/-- Precomposing `gradedSymmetricAlgebraLift φ` with the map `Sym F' ⟶ Sym F` induced by a
morphism `g : F' ⟶ F` extends `g ≫ φ`. -/
@[simp, reassoc]
theorem gradedSymmetricAlgebra_map_comp_lift {F' F : QuasicoherentSheaf X}
    {A : GradedQuasicoherentAlgebra X} (g : F' ⟶ F) (φ : F ⟶ degreeOne.obj A) :
    (gradedSymmetricAlgebra X).map g ≫ gradedSymmetricAlgebraLift φ =
      gradedSymmetricAlgebraLift (g ≫ φ) := by
  rw [← gradedSymmetricAlgebraAdjunction_homEquiv_symm_apply,
    ← gradedSymmetricAlgebraAdjunction_homEquiv_symm_apply,
    Adjunction.homEquiv_naturality_left_symm]

variable (X) in
/-- The unit of `gradedSymmetricAlgebraAdjunction` is the identification `F ≅ Sym¹ F`. -/
theorem gradedSymmetricAlgebraAdjunction_unit :
    (gradedSymmetricAlgebraAdjunction X).unit = (gradedSymmetricAlgebraDegreeOneIso X).inv := by
  ext F : 2
  rw [← Adjunction.homEquiv_id, gradedSymmetricAlgebraAdjunction_homEquiv_apply,
    CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- The counit of `gradedSymmetricAlgebraAdjunction` at `A` is the morphism `Sym A₁ ⟶ A`
extending the identity of the degree-one component `A₁`. -/
@[simp]
theorem gradedSymmetricAlgebraAdjunction_counit_app (A : GradedQuasicoherentAlgebra X) :
    (gradedSymmetricAlgebraAdjunction X).counit.app A =
      gradedSymmetricAlgebraLift (𝟙 (degreeOne.obj A)) := by
  rw [← gradedSymmetricAlgebraAdjunction_homEquiv_symm_apply, Adjunction.homEquiv_counit,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The extension of the identification `F ≅ Sym¹ F` is the identity of `Sym F`. -/
private lemma gradedSymmetricAlgebraLift_degreeOneIso_inv (F : QuasicoherentSheaf X) :
    gradedSymmetricAlgebraLift ((gradedSymmetricAlgebraDegreeOneIso X).inv.app F) = 𝟙 _ := by
  have h := (gradedSymmetricAlgebraAdjunction X).homEquiv_id F
  rw [gradedSymmetricAlgebraAdjunction_unit] at h
  rw [← gradedSymmetricAlgebraAdjunction_homEquiv_symm_apply, ← h]
  exact Equiv.symm_apply_apply _ _

/-- The degree-`n` components of the extension of the identification `F ≅ Sym¹ F` are
isomorphisms, since the extension is the identity of `Sym F`. -/
private lemma isIso_liftDegree_degreeOneIso_inv (F : QuasicoherentSheaf X) (n : ℕ) :
    IsIso (liftDegree (A := ((gradedSymmetricAlgebra X).obj F).obj)
      (((gradedSymmetricAlgebraDegreeOneIso X).inv.app F).hom ≫
        eqToHom (degree_obj_obj ((gradedSymmetricAlgebra X).obj F) 1)) n) := by
  let A := (gradedSymmetricAlgebra X).obj F
  let φ := (gradedSymmetricAlgebraDegreeOneIso X).inv.app F
  have h := degree_map_gradedSymmetricAlgebraLift_hom φ n
  rw [gradedSymmetricAlgebraLift_degreeOneIso_inv, CategoryTheory.Functor.map_id] at h
  have : IsIso (eqToHom (degree_obj_gradedSymmetricAlgebra_obj F n) ≫
      liftDegree (A := A.obj) (φ.hom ≫ eqToHom (degree_obj_obj A 1)) n ≫
      eqToHom (degree_obj_obj A n).symm) := h ▸ inferInstance
  -- The transports are morphisms of `X.Modules`, where typeclass search does not find their
  -- `IsIso` instances, so they are supplied by hand.
  have hi {B C : X.Modules} (p : B = C) : IsIso (eqToHom p) := (eqToIso p).isIso_hom
  have := hi (degree_obj_gradedSymmetricAlgebra_obj F n)
  have h' := IsIso.of_isIso_comp_left (eqToHom (degree_obj_gradedSymmetricAlgebra_obj F n))
    (liftDegree (A := A.obj) (φ.hom ≫ eqToHom (degree_obj_obj A 1)) n ≫
      eqToHom (degree_obj_obj A n).symm)
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (hi _) h'

/-- **The sections of `Sym F` over an affine open are the symmetric algebra of the sections.** For
a quasicoherent sheaf `F` and an affine open `U`, the algebra map
`Sym Γ(F, U) → ⨁ n, Γ(Symⁿ F, U)` sending a section of `F` to its image in degree one under
`F ≅ Sym¹ F` (`gradedSymmetricAlgebraSectionsEquiv_ι`) is an isomorphism of `Γ(X, U)`-algebras. -/
def gradedSymmetricAlgebraSectionsEquiv (F : QuasicoherentSheaf X) {U : X.Opens}
    (hU : IsAffineOpen U) :
    SymmetricAlgebra Γ(X, U) (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.obj.val (op U))
      ≃ₐ[Γ(X, U)] ⨁ n, Γ(((gradedSymmetricAlgebra X).obj F).obj.X n, U) :=
  have := isIso_liftDegree_degreeOneIso_inv F
  AlgEquiv.ofBijective _ (bijective_sectionsLift_of (F := F.obj)
    (((gradedSymmetricAlgebraDegreeOneIso X).inv.app F).hom ≫
      eqToHom (degree_obj_obj ((gradedSymmetricAlgebra X).obj F) 1)) hU)

/-- `gradedSymmetricAlgebraSectionsEquiv` sends a section of `F` to its image in degree one under
the identification `F ≅ Sym¹ F`. -/
@[simp]
theorem gradedSymmetricAlgebraSectionsEquiv_ι (F : QuasicoherentSheaf X) {U : X.Opens}
    (hU : IsAffineOpen U)
    (m : PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.obj.val (op U)) :
    gradedSymmetricAlgebraSectionsEquiv F hU (SymmetricAlgebra.ι _ _ m) =
      DirectSum.of (fun n ↦ Γ(((gradedSymmetricAlgebra X).obj F).obj.X n, U)) 1
        (Scheme.Modules.Hom.app (((gradedSymmetricAlgebraDegreeOneIso X).inv.app F).hom ≫
          eqToHom (degree_obj_obj ((gradedSymmetricAlgebra X).obj F) 1)) U m) :=
  sectionsLift_ι _ U m

/-- `gradedSymmetricAlgebraSectionsEquiv` maps `Symⁿ Γ(F, U)` into the degree-`n` summand
`Γ(Symⁿ F, U)`. -/
theorem gradedSymmetricAlgebraSectionsEquiv_mem (F : QuasicoherentSheaf X) {U : X.Opens}
    (hU : IsAffineOpen U) {n : ℕ} {x : SymmetricAlgebra Γ(X, U)
      (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.obj.val (op U))}
    (hx : x ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule _ _ n) :
    gradedSymmetricAlgebraSectionsEquiv F hU x ∈
      ((gradedSymmetricAlgebra X).obj F).obj.gradedSectionsGrading U n := by
  have h : gradedSymmetricAlgebraSectionsEquiv F hU x =
      DirectSum.of _ n (gradedSymmetricAlgebraSectionsEquiv F hU x n) :=
    SymmetricAlgebra.lift_lof_comp_apply_of_mem_homogeneousSubmodule _ _ _ hx
  rw [h]
  exact ((gradedSymmetricAlgebra X).obj F).obj.of_mem_gradedSectionsGrading n _

/-- The inverse of `gradedSymmetricAlgebraSectionsEquiv` maps the degree-`n` summand
`Γ(Symⁿ F, U)` into `Symⁿ Γ(F, U)`. -/
theorem gradedSymmetricAlgebraSectionsEquiv_symm_mem (F : QuasicoherentSheaf X) {U : X.Opens}
    (hU : IsAffineOpen U) {n : ℕ} {y : ⨁ n, Γ(((gradedSymmetricAlgebra X).obj F).obj.X n, U)}
    (hy : y ∈ ((gradedSymmetricAlgebra X).obj F).obj.gradedSectionsGrading U n) :
    (gradedSymmetricAlgebraSectionsEquiv F hU).symm y ∈
      TauCeti.SymmetricAlgebra.homogeneousSubmodule _ _ n := by
  have := isIso_liftDegree_degreeOneIso_inv F
  obtain ⟨z, rfl⟩ := DirectSum.mem_summand.mp hy
  obtain ⟨x, hx, hxz⟩ := exists_mem_sectionsLift_eq_of (F := F.obj)
    (((gradedSymmetricAlgebraDegreeOneIso X).inv.app F).hom ≫
      eqToHom (degree_obj_obj ((gradedSymmetricAlgebra X).obj F) 1)) n hU z
  rwa [(gradedSymmetricAlgebraSectionsEquiv F hU).symm_apply_eq.mpr hxz.symm]

/-- **The sections of `Sym F` over an affine open are generated in degree one.** For a
quasicoherent sheaf `F` and an affine open `U`, the graded ring `⨁ n, Γ(Symⁿ F, U)` of sections of
the graded symmetric algebra is generated over `Γ(X, U)` by its degree-one sections. -/
theorem adjoin_gradedSectionsGrading_one_gradedSymmetricAlgebra (F : QuasicoherentSheaf X)
    {U : X.Opens} (hU : IsAffineOpen U) :
    Algebra.adjoin Γ(X, U)
        (((gradedSymmetricAlgebra X).obj F).obj.gradedSectionsGrading U 1 :
          Set (⨁ n, Γ(((gradedSymmetricAlgebra X).obj F).obj.X n, U))) = ⊤ := by
  let e := gradedSymmetricAlgebraSectionsEquiv F hU
  have h := congrArg (Subalgebra.map e.toAlgHom) (TauCeti.SymmetricAlgebra.adjoin_range_ι Γ(X, U)
    (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.obj.val (op U)))
  rw [AlgHom.map_adjoin, Algebra.map_top] at h
  refine eq_top_iff.mpr fun w _ ↦ ?_
  obtain ⟨x, rfl⟩ := e.surjective w
  have hx := e.toAlgHom.mem_range_self x
  rw [← h] at hx
  refine Algebra.adjoin_mono ?_ hx
  rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
  rw [AlgEquiv.coe_toAlgHom, gradedSymmetricAlgebraSectionsEquiv_ι]
  exact ((gradedSymmetricAlgebra X).obj F).obj.of_mem_gradedSectionsGrading 1 _

end

end TauCeti.AlgebraicGeometry
