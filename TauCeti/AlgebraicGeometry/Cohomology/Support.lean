/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Module.Basic
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.Topology.Sheaves.SupportedCohomology.Univ
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Cohomology with supports of a sheaf of modules on a scheme

Let `X` be a scheme, `Z ⊆ X` a closed subset and `M` a sheaf of `𝒪_X`-modules. The cohomology
`H_Z^q(X, M)` of `M` with supports in `Z` (Stacks, Section 20.34 (0G6Y)) is the cohomology with
supports `CategoryTheory.Sheaf.supportedH` of the underlying abelian sheaf of `M` on the whole
space. As for `Scheme.Modules.Cohomology`, the global functions act on it through their action
on `M` by scalar endomorphisms, which makes `H_Z^q(X, M)` a `Γ(X, ⊤)`-module and every map
induced by a morphism of coefficient sheaves `Γ(X, ⊤)`-linear. A short exact sequence of sheaves
of modules gives a long exact sequence of cohomology with supports, whose connecting maps are the
Yoneda products with its extension class.

In degree zero, `H_Z^0(X, M)` is the `Γ(X, ⊤)`-submodule `Γ_Z(X, M)` of global sections whose
restriction to `X ∖ Z` vanishes. With supports in `Z = X` it is ordinary cohomology, and with
supports in `Z = ∅` it vanishes.

## Main declarations

* `Scheme.Modules.cohomologyWithSupport Z M q`: the group `H_Z^q(X, M)`;
* `Scheme.Modules.cohomologyWithSupportMap`: the map induced by a morphism of sheaves of modules,
  and `Scheme.Modules.cohomologyWithSupportMapLinear`, the same map as a `Γ(X, ⊤)`-linear map;
* `Scheme.Modules.cohomologyWithSupportModule`: the `Γ(X, ⊤)`-module structure;
* `Scheme.Modules.cohomologyWithSupportδ`: the connecting map of a short exact sequence of
  sheaves of modules, with the exactness of the long exact sequence
  (`Scheme.Modules.exact_cohomologyWithSupportMap_cohomologyWithSupportMap`,
  `Scheme.Modules.exact_cohomologyWithSupportMap_cohomologyWithSupportδ`,
  `Scheme.Modules.exact_cohomologyWithSupportδ_cohomologyWithSupportMap`), its naturality and its
  linearity over global functions;
* `Scheme.Modules.sectionsWithSupport Z M`: the `Γ(X, ⊤)`-submodule `Γ_Z(X, M)` of `Γ(M, ⊤)`,
  all of `Γ(M, ⊤)` for `Z = X` (`Scheme.Modules.sectionsWithSupport_top`);
* `Scheme.Modules.cohomologyWithSupportZeroLinearEquiv`: `H_Z^0(X, M) ≃ₗ[Γ(X, ⊤)] Γ_Z(X, M)`,
  and `Scheme.Modules.cohomologyWithSupportZeroLinearEquivOfEqTop`:
  `H_Z^0(X, M) ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤)` when `Z = X`;
* `Scheme.Modules.cohomologyWithSupportTopEquiv`: `H_X^q(X, M) ≃+ H^q(X, M)`, natural in `M`,
  and `Scheme.Modules.cohomologyWithSupportTopLinearEquiv`, the same identification as a
  `Γ(X, ⊤)`-linear equivalence;
* `Scheme.Modules.subsingleton_cohomologyWithSupport_bot`: `H_∅^q(X, M) = 0`.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules Opposite Abelian

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}} (Z : Closeds X) {M N : X.Modules}

/-- The cohomology `H_Z^q(X, M)` of a sheaf of modules `M` on a scheme `X` with supports in the
closed subset `Z`: the cohomology with supports in `Z` of the underlying abelian sheaf of `M`, on
the whole space. -/
abbrev cohomologyWithSupport (M : X.Modules) (q : ℕ) : Type u :=
  ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).supportedH Z ⊤ q

/-- The map `H_Z^q(X, M) → H_Z^q(X, N)` induced by a morphism of sheaves of modules. -/
def cohomologyWithSupportMap (f : M ⟶ N) (q : ℕ) :
    cohomologyWithSupport Z M q →+ cohomologyWithSupport Z N q :=
  (Ext.mk₀ ((SheafOfModules.toSheaf X.ringCatSheaf).map f)).postcomp _ (add_zero q)

lemma cohomologyWithSupportMap_apply (f : M ⟶ N) (q : ℕ) (x : cohomologyWithSupport Z M q) :
    cohomologyWithSupportMap Z f q x =
      x.comp (Ext.mk₀ ((SheafOfModules.toSheaf X.ringCatSheaf).map f)) (add_zero q) :=
  (rfl)

@[simp]
lemma cohomologyWithSupportMap_id (M : X.Modules) (q : ℕ) :
    cohomologyWithSupportMap Z (𝟙 M) q = AddMonoidHom.id _ := by
  ext x
  have h : (SheafOfModules.toSheaf X.ringCatSheaf).map (𝟙 M : M ⟶ M) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  rw [cohomologyWithSupportMap_apply, h, Ext.comp_mk₀_id, AddMonoidHom.id_apply]

@[simp]
lemma cohomologyWithSupportMap_comp {P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) (q : ℕ) :
    cohomologyWithSupportMap Z (f ≫ g) q =
      (cohomologyWithSupportMap Z g q).comp (cohomologyWithSupportMap Z f q) := by
  ext x
  have h : (SheafOfModules.toSheaf X.ringCatSheaf).map (f ≫ g : M ⟶ P) =
      (SheafOfModules.toSheaf X.ringCatSheaf).map f ≫
        (SheafOfModules.toSheaf X.ringCatSheaf).map g :=
    CategoryTheory.Functor.map_comp _ _ _
  rw [AddMonoidHom.comp_apply, cohomologyWithSupportMap_apply, cohomologyWithSupportMap_apply,
    cohomologyWithSupportMap_apply, h, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_third_deg_zero]

@[simp]
lemma cohomologyWithSupportMap_zero (M N : X.Modules) (q : ℕ) :
    cohomologyWithSupportMap Z (0 : M ⟶ N) q = 0 := by
  ext x
  have h : (SheafOfModules.toSheaf X.ringCatSheaf).map (0 : M ⟶ N) = 0 :=
    Functor.map_zero _ _ _
  rw [cohomologyWithSupportMap_apply, h, Ext.mk₀_zero, Ext.comp_zero, AddMonoidHom.zero_apply]

@[simp]
lemma cohomologyWithSupportMap_add (f g : M ⟶ N) (q : ℕ) :
    cohomologyWithSupportMap Z (f + g) q =
      cohomologyWithSupportMap Z f q + cohomologyWithSupportMap Z g q := by
  ext x
  have h : (SheafOfModules.toSheaf X.ringCatSheaf).map (f + g) =
      (SheafOfModules.toSheaf X.ringCatSheaf).map f +
        (SheafOfModules.toSheaf X.ringCatSheaf).map g :=
    Functor.map_add _
  rw [cohomologyWithSupportMap_apply, h, Ext.mk₀_add, Ext.comp_add, AddMonoidHom.add_apply,
    cohomologyWithSupportMap_apply, cohomologyWithSupportMap_apply]

/-- The action of global functions on cohomology with supports, bundled as a ring homomorphism
into additive endomorphisms. -/
def cohomologyWithSupportAction (M : X.Modules) (q : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End (cohomologyWithSupport Z M q) where
  toFun r := cohomologyWithSupportMap Z (M.globalSectionsSmul r) q
  map_one' := by
    rw [globalSectionsSmul_one, cohomologyWithSupportMap_id]
    rfl
  map_mul' r s := by
    rw [globalSectionsSmul_mul, cohomologyWithSupportMap_comp]
    rfl
  map_zero' := by
    rw [globalSectionsSmul_zero, cohomologyWithSupportMap_zero]
    rfl
  map_add' r s := by
    rw [globalSectionsSmul_add, cohomologyWithSupportMap_add]
    rfl

/-- Cohomology with supports is canonically a module over the ring of global functions. -/
instance cohomologyWithSupportModule (M : X.Modules) (q : ℕ) :
    Module Γ(X, ⊤) (cohomologyWithSupport Z M q) :=
  Module.compHom _ (cohomologyWithSupportAction Z M q)

/-- Scalar multiplication on cohomology with supports is induced by the corresponding scalar
endomorphism of the coefficient sheaf. -/
lemma smul_cohomologyWithSupport (M : X.Modules) (q : ℕ) (r : Γ(X, ⊤))
    (x : cohomologyWithSupport Z M q) :
    r • x = cohomologyWithSupportMap Z (M.globalSectionsSmul r) q x :=
  (rfl)

/-- The map on cohomology with supports induced by a morphism of coefficient sheaves is linear
over global functions. -/
def cohomologyWithSupportMapLinear (f : M ⟶ N) (q : ℕ) :
    cohomologyWithSupport Z M q →ₗ[Γ(X, ⊤)] cohomologyWithSupport Z N q where
  __ := cohomologyWithSupportMap Z f q
  map_smul' r x := by
    simp only [AddMonoidHom.toFun_eq_coe, smul_cohomologyWithSupport, RingHom.id_apply]
    rw [← AddMonoidHom.comp_apply, ← cohomologyWithSupportMap_comp,
      globalSectionsSmul_naturality, cohomologyWithSupportMap_comp, AddMonoidHom.comp_apply]

@[simp]
lemma cohomologyWithSupportMapLinear_apply (f : M ⟶ N) (q : ℕ)
    (x : cohomologyWithSupport Z M q) :
    cohomologyWithSupportMapLinear Z f q x = cohomologyWithSupportMap Z f q x :=
  (rfl)

section connecting

variable {S : ShortComplex X.Modules} (hS : S.ShortExact)

/-- The connecting map `H_Z^{n₀}(X, M₃) →+ H_Z^{n₁}(X, M₁)`, for `n₀ + 1 = n₁`, of the long exact
sequence of cohomology with supports of a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of sheaves
of modules: the Yoneda product with the extension class of the underlying short exact sequence of
abelian sheaves. -/
def cohomologyWithSupportδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    cohomologyWithSupport Z S.X₃ n₀ →+ cohomologyWithSupport Z S.X₁ n₁ :=
  (shortExact_map_toSheaf hS).extClass.postcomp _ h

lemma cohomologyWithSupportδ_eq (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    cohomologyWithSupportδ Z hS n₀ n₁ h = (shortExact_map_toSheaf hS).extClass.postcomp _ h :=
  (rfl)

lemma cohomologyWithSupportδ_apply (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : cohomologyWithSupport Z S.X₃ n₀) :
    cohomologyWithSupportδ Z hS n₀ n₁ h x = x.comp (shortExact_map_toSheaf hS).extClass h :=
  (rfl)

include hS in
/-- The long exact sequence of cohomology with supports is exact at `H_Z^n(X, M₂)`. -/
theorem exact_cohomologyWithSupportMap_cohomologyWithSupportMap (n : ℕ) :
    Function.Exact (cohomologyWithSupportMap Z S.f n) (cohomologyWithSupportMap Z S.g n) := by
  have := Ext.covariant_sequence_exact₂'
    (TauCeti.CategoryTheory.relativeFreeYonedaSheaf _ (Z.complInclusion ⊤))
    (shortExact_map_toSheaf hS) n
  rwa [ShortComplex.ab_exact_iff_function_exact] at this

/-- The long exact sequence of cohomology with supports is exact at `H_Z^{n₀}(X, M₃)`. -/
theorem exact_cohomologyWithSupportMap_cohomologyWithSupportδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyWithSupportMap Z S.g n₀) (cohomologyWithSupportδ Z hS n₀ n₁ h) := by
  have := Ext.covariant_sequence_exact₃'
    (TauCeti.CategoryTheory.relativeFreeYonedaSheaf _ (Z.complInclusion ⊤))
    (shortExact_map_toSheaf hS) n₀ n₁ h
  rwa [ShortComplex.ab_exact_iff_function_exact] at this

/-- The long exact sequence of cohomology with supports is exact at `H_Z^{n₁}(X, M₁)`. -/
theorem exact_cohomologyWithSupportδ_cohomologyWithSupportMap (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyWithSupportδ Z hS n₀ n₁ h) (cohomologyWithSupportMap Z S.f n₁) := by
  have := Ext.covariant_sequence_exact₁'
    (TauCeti.CategoryTheory.relativeFreeYonedaSheaf _ (Z.complInclusion ⊤))
    (shortExact_map_toSheaf hS) n₀ n₁ h
  rwa [ShortComplex.ab_exact_iff_function_exact] at this

omit hS in
/-- The connecting map of cohomology with supports is natural in the short exact sequence. -/
theorem cohomologyWithSupportδ_naturality {S₁ S₂ : ShortComplex X.Modules} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : cohomologyWithSupport Z S₁.X₃ n₀) :
    cohomologyWithSupportMap Z φ.τ₁ n₁ (cohomologyWithSupportδ Z h₁ n₀ n₁ h x) =
      cohomologyWithSupportδ Z h₂ n₀ n₁ h (cohomologyWithSupportMap Z φ.τ₃ n₀ x) := by
  have key := (shortExact_map_toSheaf h₁).extClass_naturality (shortExact_map_toSheaf h₂)
    ((toSheaf X).mapShortComplex.map φ)
  have e₁ := Ext.comp_assoc_of_third_deg_zero x (shortExact_map_toSheaf h₁).extClass
    (Ext.mk₀ ((toSheaf X).map φ.τ₁)) h
  have e₂ := Ext.comp_assoc_of_second_deg_zero x (Ext.mk₀ ((toSheaf X).map φ.τ₃))
    (shortExact_map_toSheaf h₂).extClass h
  rw [cohomologyWithSupportMap_apply, cohomologyWithSupportδ_apply, cohomologyWithSupportδ_apply,
    cohomologyWithSupportMap_apply]
  exact e₁.trans ((congrArg (fun e ↦ x.comp e h) key).trans e₂.symm)

/-- The connecting map of cohomology with supports is linear over global functions. -/
theorem cohomologyWithSupportδ_smul (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (r : Γ(X, ⊤))
    (x : cohomologyWithSupport Z S.X₃ n₀) :
    cohomologyWithSupportδ Z hS n₀ n₁ h (r • x) = r • cohomologyWithSupportδ Z hS n₀ n₁ h x := by
  let φ : S ⟶ S :=
    { τ₁ := S.X₁.globalSectionsSmul r
      τ₂ := S.X₂.globalSectionsSmul r
      τ₃ := S.X₃.globalSectionsSmul r
      comm₁₂ := globalSectionsSmul_naturality S.f r
      comm₂₃ := globalSectionsSmul_naturality S.g r }
  rw [smul_cohomologyWithSupport, smul_cohomologyWithSupport]
  exact (cohomologyWithSupportδ_naturality Z hS hS φ n₀ n₁ h x).symm

end connecting

/-- The `Γ(X, ⊤)`-submodule `Γ_Z(X, M)` of global sections of `M` supported in `Z`, that is,
whose restriction to `X ∖ Z` vanishes. -/
def sectionsWithSupport (M : X.Modules) : Submodule Γ(X, ⊤) Γ(M, ⊤) where
  toAddSubmonoid :=
    (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).supportedSections Z ⊤).toAddSubmonoid
  smul_mem' r s hs := by
    rw [← globalSectionsSmul_app_top_apply]
    exact Sheaf.map_mem_supportedSections
      ((SheafOfModules.toSheaf X.ringCatSheaf).map (M.globalSectionsSmul r)) hs

lemma mem_sectionsWithSupport_iff {M : X.Modules} {s : Γ(M, ⊤)} :
    s ∈ sectionsWithSupport Z M ↔
      s ∈ ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).supportedSections Z ⊤ :=
  Iff.rfl

/-- Every global section is supported in the whole space. -/
@[simp]
theorem sectionsWithSupport_top (M : X.Modules) : sectionsWithSupport ⊤ M = ⊤ := by
  refine eq_top_iff.2 fun s _ => ?_
  have h : (⊤ : X.Opens) ⊓ (⊤ : Closeds X).compl = ⊥ := Opens.ext (by simp)
  have : Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.obj
      (op ((⊤ : X.Opens) ⊓ (⊤ : Closeds X).compl))) := by
    rw [h]
    exact AddCommGrpCat.subsingleton_of_isZero
      (TopCat.Sheaf.isTerminalOfEmpty (C := AddCommGrpCat.{u}) _).isZero
  exact (mem_sectionsWithSupport_iff ⊤).2
    ((Sheaf.mem_supportedSections_iff _).2 (Subsingleton.elim _ _))

/-- Degree-zero cohomology with supports in `Z` is the module `Γ_Z(X, M)` of global sections
supported in `Z`, linearly over global functions. -/
def cohomologyWithSupportZeroLinearEquiv (M : X.Modules) :
    cohomologyWithSupport Z M 0 ≃ₗ[Γ(X, ⊤)] sectionsWithSupport Z M where
  __ := ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).supportedHZeroEquiv Z ⊤
  map_smul' r x := by
    apply Subtype.ext
    exact (Sheaf.coe_supportedHZeroEquiv_apply _ Z ⊤ _).trans
      (((Sheaf.relativeH'.coe_zeroEquiv_naturality_right _ _ x).trans
        (congrArg _ (Sheaf.coe_supportedHZeroEquiv_apply _ Z ⊤ x).symm)).trans
          (globalSectionsSmul_app_top_apply M r _))

@[simp]
lemma coe_cohomologyWithSupportZeroLinearEquiv_apply (M : X.Modules)
    (x : cohomologyWithSupport Z M 0) :
    (cohomologyWithSupportZeroLinearEquiv Z M x).1 =
      (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).supportedHZeroEquiv Z ⊤ x).1 :=
  (rfl)

variable {Z} in
/-- With supports in a closed subset equal to the whole space, degree-zero cohomology with
supports is the module of all global sections. -/
def cohomologyWithSupportZeroLinearEquivOfEqTop (hZ : Z = ⊤) (M : X.Modules) :
    cohomologyWithSupport Z M 0 ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤) :=
  (cohomologyWithSupportZeroLinearEquiv Z M).trans
    (LinearEquiv.ofTop _ (by rw [hZ]; exact sectionsWithSupport_top M))

variable {Z} in
@[simp]
lemma cohomologyWithSupportZeroLinearEquivOfEqTop_apply (hZ : Z = ⊤) (M : X.Modules)
    (x : cohomologyWithSupport Z M 0) :
    cohomologyWithSupportZeroLinearEquivOfEqTop hZ M x =
      (cohomologyWithSupportZeroLinearEquiv Z M x).1 :=
  (rfl)

/-- With supports in the whole space, cohomology with supports is ordinary cohomology:
`H_X^q(X, M) ≃+ H^q(X, M)`. -/
def cohomologyWithSupportTopEquiv (M : X.Modules) (q : ℕ) :
    cohomologyWithSupport ⊤ M q ≃+ Cohomology M q :=
  (TauCeti.CategoryTheory.supportedHTopEquiv _ ⊤ q).trans
    (cohomologyOnTopIso M q).addCommGroupIsoToAddEquiv

/-- The identification `H_X^q(X, M) ≃+ H^q(X, M)` is natural in the coefficient sheaf. -/
lemma cohomologyWithSupportTopEquiv_naturality (f : M ⟶ N) (q : ℕ)
    (x : cohomologyWithSupport ⊤ M q) :
    cohomologyWithSupportTopEquiv N q (cohomologyWithSupportMap ⊤ f q x) =
      (cohomologyFunctor X q).map f (cohomologyWithSupportTopEquiv M q x) := by
  have h := ConcreteCategory.congr_hom
    ((Sheaf.cohomologyPresheafEvaluationIsoFunctorH _ q isTerminalTop).hom.naturality
      ((SheafOfModules.toSheaf X.ringCatSheaf).map f))
    (TauCeti.CategoryTheory.supportedHTopEquiv _ ⊤ q x)
  rw [cohomologyWithSupportMap_apply, cohomologyWithSupportTopEquiv, AddEquiv.trans_apply,
    TauCeti.CategoryTheory.supportedHTopEquiv_naturality]
  -- `cohomologyOnTopIso` is the component of `cohomologyPresheafEvaluationIsoFunctorH`, and
  -- `cohomologyFunctor` is `functorH` after `toSheaf`, so `h` is the goal up to these abbrevs.
  exact h

/-- With supports in the whole space, cohomology with supports is ordinary cohomology, linearly
over global functions. -/
def cohomologyWithSupportTopLinearEquiv (M : X.Modules) (q : ℕ) :
    cohomologyWithSupport ⊤ M q ≃ₗ[Γ(X, ⊤)] Cohomology M q where
  __ := cohomologyWithSupportTopEquiv M q
  map_smul' r x := by
    -- The inherited additive-equivalence fields compute through their coercion to functions.
    change cohomologyWithSupportTopEquiv M q (r • x) = r • cohomologyWithSupportTopEquiv M q x
    rw [smul_cohomologyWithSupport, cohomology_smul, cohomologyWithSupportTopEquiv_naturality]

@[simp]
lemma cohomologyWithSupportTopLinearEquiv_apply (M : X.Modules) (q : ℕ)
    (x : cohomologyWithSupport ⊤ M q) :
    cohomologyWithSupportTopLinearEquiv M q x = cohomologyWithSupportTopEquiv M q x :=
  (rfl)

/-- With supports in the empty set, cohomology with supports vanishes. -/
instance subsingleton_cohomologyWithSupport_bot (M : X.Modules) (q : ℕ) :
    Subsingleton (cohomologyWithSupport ⊥ M q) :=
  Sheaf.subsingleton_supportedH_of_le_compl _ ⊥
    (fun x _ => show x ∉ ((⊥ : Closeds X) : Set X) by simp) q

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
