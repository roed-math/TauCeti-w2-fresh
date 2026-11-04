/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.LocalCohomology
public import TauCeti.Algebra.Homology.Ext.Comparison
public import TauCeti.Algebra.Homology.LocalCohomology.DegreeZero
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import TauCeti.Algebra.Category.ModuleCat.FilteredColimits

/-!
# The long exact sequence of local cohomology

Mathlib defines `localCohomology I q` as the colimit over `n` of the derived-functor
`Ext^q_A(A/Iⁿ, -)`. For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of `A`-modules this file
constructs the connecting maps `Hⁿ_I(X₃) → Hⁿ⁺¹_I(X₁)` and proves that

`0 → H⁰_I(X₁) → H⁰_I(X₂) → H⁰_I(X₃) → H¹_I(X₁) → ⋯ → Hⁿ_I(X₃) → Hⁿ⁺¹_I(X₁) → Hⁿ⁺¹_I(X₂) → ⋯`

is exact, over every commutative ring: the native local cohomology functors form a `δ`-functor
(Stacks, Lemma 47.8.2 (0954)).

Stage by stage, `TauCeti.Supports.extLinearEquiv` identifies the derived-functor `Extⁿ(N, -)`
with the derived-category `Extⁿ(N, -)`, naturally in both arguments: in degree zero both are
`Hom(N, -)`, and in positive degrees this is `TauCeti.extSuccLinearEquiv`. There the long exact
sequence of `Ext` in the second argument is Mathlib's `Ext.covariant_sequence_exact₁`, `₂` and
`₃`, and the connecting map is the Yoneda product with the class `hS.extClass` of the extension.
Exactness then passes to the filtered colimit over `n`, by `TauCeti.ModuleCat.exists_eq_of_stages`,
`TauCeti.ModuleCat.comp_eq_zero_of_stages` and `TauCeti.ModuleCat.injective_of_stages`.

## Main definitions

* `TauCeti.Supports.extLinearEquiv`: the derived-functor `Extⁿ(N, Y)` of modules is the
  derived-category `Extⁿ(N, Y)`, in every degree.
* `TauCeti.Supports.extδ`: the connecting map `Extⁿ(N, X₃) → Extⁿ⁺¹(N, X₁)` of the derived-functor
  `Ext`.
* `TauCeti.Supports.localCohomologyδ`: the connecting map `Hⁿ_I(X₃) → Hⁿ⁺¹_I(X₁)` of local
  cohomology.

## Main results

* `TauCeti.Supports.localCohomology_zero_map_f_injective`: `H⁰_I(X₁) → H⁰_I(X₂)` is injective.
* `TauCeti.Supports.localCohomology_sequence_exact₂`: exactness at `Hⁿ_I(X₂)`, with the
  elementwise form `TauCeti.Supports.exists_localCohomology_map_f_eq`.
* `TauCeti.Supports.localCohomology_sequence_exact₃`: exactness at `Hⁿ_I(X₃)`, with the
  elementwise form `TauCeti.Supports.exists_localCohomology_map_g_eq`.
* `TauCeti.Supports.localCohomology_sequence_exact₁`: exactness at `Hⁿ⁺¹_I(X₁)`, with the
  elementwise form `TauCeti.Supports.exists_localCohomologyδ_eq`.
-/

public section

universe u

open CategoryTheory CategoryTheory.Abelian Limits Opposite

namespace TauCeti.Supports

variable {A : Type u} [CommRing A]

section Comparison

variable (N : ModuleCat.{u} A)

/-- **The two `Ext`s of modules agree in every degree**: the derived-functor `Extⁿ(N, Y)` of
`Mathlib.CategoryTheory.Abelian.Ext`, on which `localCohomology` is built, is `A`-linearly
equivalent to the derived-category `Extⁿ(N, Y)`. In degree zero both are `Hom(N, Y)`
(`extZeroIso` and `Ext.linearEquiv₀`); in positive degrees this is `extSuccLinearEquiv` for the
chosen projective resolution of `N`. -/
noncomputable def extLinearEquiv (Y : ModuleCat.{u} A) :
    ∀ n : ℕ, ((_root_.Ext A (ModuleCat.{u} A) n).obj (op N)).obj Y ≃ₗ[A] Ext N Y n
  | 0 => ((extZeroIso Y).app (op N)).toLinearEquiv ≪≫ₗ Ext.linearEquiv₀.symm
  | p + 1 => extSuccLinearEquiv.{u} A (projectiveResolution N) Y p

/-- In degree zero, `extLinearEquiv` is `Ext.mk₀` of the morphism given by `extZeroIso`. -/
theorem extLinearEquiv_zero_apply (Y : ModuleCat.{u} A)
    (x : ((_root_.Ext A (ModuleCat.{u} A) 0).obj (op N)).obj Y) :
    extLinearEquiv N Y 0 x = Ext.mk₀ ((extZeroIso Y).hom.app (op N) x) := by
  simp only [extLinearEquiv]
  rfl

/-- `extLinearEquiv` is natural in the second argument: the map induced by `f : Y ⟶ Y'` on the
derived-functor `Ext` becomes the Yoneda product with `Ext.mk₀ f`. -/
theorem extLinearEquiv_Ext_obj_map {Y Y' : ModuleCat.{u} A} (f : Y ⟶ Y') :
    ∀ (n : ℕ) (x : ((_root_.Ext A (ModuleCat.{u} A) n).obj (op N)).obj Y),
      extLinearEquiv N Y' n (((_root_.Ext A (ModuleCat.{u} A) n).obj (op N)).map f x) =
        (extLinearEquiv N Y n x).comp (Ext.mk₀ f) (add_zero n)
  | 0, x => by
    rw [extLinearEquiv_zero_apply, extLinearEquiv_zero_apply]
    exact (congrArg Ext.mk₀
      (ConcreteCategory.congr_hom (extZeroIso_hom_naturality_right N f) x)).trans
        (Ext.mk₀_comp_mk₀ _ _).symm
  | p + 1, x => extSuccLinearEquiv_Ext_obj_map _ f p x

/-- `extLinearEquiv` is natural in the first argument: the map induced by `g : N' ⟶ N` on the
derived-functor `Ext` becomes the Yoneda product with `Ext.mk₀ g`. -/
theorem extLinearEquiv_Ext_map {N' : ModuleCat.{u} A} (g : N' ⟶ N) (Y : ModuleCat.{u} A) :
    ∀ (n : ℕ) (x : ((_root_.Ext A (ModuleCat.{u} A) n).obj (op N)).obj Y),
      extLinearEquiv N' Y n (((_root_.Ext A (ModuleCat.{u} A) n).map g.op).app Y x) =
        (Ext.mk₀ g).comp (extLinearEquiv N Y n x) (zero_add n)
  | 0, x => by
    rw [extLinearEquiv_zero_apply, extLinearEquiv_zero_apply]
    exact (congrArg Ext.mk₀
      (ConcreteCategory.congr_hom ((extZeroIso Y).hom.naturality g.op) x)).trans
        (Ext.mk₀_comp_mk₀ _ _).symm
  | p + 1, x => extSuccLinearEquiv_Ext_map g _ _ Y p x

end Comparison

section Ext

variable (N : ModuleCat.{u} A) {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (n : ℕ)

include hS in
/-- The derived-functor `Ext⁰(N, -)` is left exact: `Ext⁰(N, X₁) → Ext⁰(N, X₂)` is injective. -/
theorem Ext_zero_map_f_injective :
    Function.Injective (((_root_.Ext A (ModuleCat.{u} A) 0).obj (op N)).map S.f) := by
  have := hS.mono_f
  intro x y h
  apply (extLinearEquiv N S.X₁ 0).injective
  apply Ext.postcomp_mk₀_injective_of_mono N S.f
  change (extLinearEquiv N S.X₁ 0 x).comp (Ext.mk₀ S.f) (add_zero 0) =
    (extLinearEquiv N S.X₁ 0 y).comp (Ext.mk₀ S.f) (add_zero 0)
  rw [← extLinearEquiv_Ext_obj_map, ← extLinearEquiv_Ext_obj_map, h]

include hS in
/-- The derived-functor `Extⁿ(N, -)` is exact at the middle of a short exact sequence. -/
theorem exists_Ext_map_f_eq
    (y : ((_root_.Ext A (ModuleCat.{u} A) n).obj (op N)).obj S.X₂)
    (hy : ((_root_.Ext A (ModuleCat.{u} A) n).obj (op N)).map S.g y = 0) :
    ∃ x, ((_root_.Ext A (ModuleCat.{u} A) n).obj (op N)).map S.f x = y := by
  let e := fun Y => extLinearEquiv N Y n
  have h₀ : (e S.X₂ y).comp (Ext.mk₀ S.g) (add_zero _) = 0 := by
    rw [← extLinearEquiv_Ext_obj_map, hy, map_zero]
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₂ N hS (e S.X₂ y) h₀
  refine ⟨(e S.X₁).symm x, (e S.X₂).injective ?_⟩
  rw [extLinearEquiv_Ext_obj_map, LinearEquiv.apply_symm_apply, hx]

/-- The derived-functor `Extⁿ(N, -)` carries the composite `X₁ → X₂ → X₃` of a short complex to
zero. -/
theorem Ext_map_f_comp_map_g :
    ((_root_.Ext A (ModuleCat.{u} A) n).obj (op N)).map S.f ≫
      ((_root_.Ext A (ModuleCat.{u} A) n).obj (op N)).map S.g = 0 := by
  rw [← Functor.map_comp, S.zero]
  ext x
  apply (extLinearEquiv N S.X₃ n).injective
  rw [extLinearEquiv_Ext_obj_map, Ext.mk₀_zero, Ext.comp_zero]
  simp

/-- The connecting map `Extⁿ(N, X₃) → Extⁿ⁺¹(N, X₁)` of the derived-functor `Ext` along a short
exact sequence: the Yoneda product with the class of the extension, computed on the
derived-category `Ext`. -/
noncomputable def extδ :
    ((_root_.Ext A (ModuleCat.{u} A) n).obj (op N)).obj S.X₃ ⟶
      ((_root_.Ext A (ModuleCat.{u} A) (n + 1)).obj (op N)).obj S.X₁ :=
  ModuleCat.ofHom <|
    (extLinearEquiv N S.X₁ (n + 1)).symm.toLinearMap ∘ₗ
      Ext.postcompOfLinear hS.extClass A N rfl ∘ₗ
        (extLinearEquiv N S.X₃ n).toLinearMap

/-- Under the comparison of the two `Ext`s, `extδ` is the Yoneda product with the class of the
extension. -/
theorem extLinearEquiv_extδ
    (x : ((_root_.Ext A (ModuleCat.{u} A) n).obj (op N)).obj S.X₃) :
    extLinearEquiv N S.X₁ (n + 1) (extδ N hS n x) =
      (extLinearEquiv N S.X₃ n x).comp hS.extClass rfl :=
  LinearEquiv.apply_symm_apply _ _

/-- `extδ` is natural in the first argument. -/
theorem extδ_naturality {N' : ModuleCat.{u} A} (g : N' ⟶ N) :
    ((_root_.Ext A (ModuleCat.{u} A) n).map g.op).app S.X₃ ≫ extδ N' hS n =
      extδ N hS n ≫ ((_root_.Ext A (ModuleCat.{u} A) (n + 1)).map g.op).app S.X₁ := by
  ext x
  apply (extLinearEquiv N' S.X₁ (n + 1)).injective
  simp only [ModuleCat.comp_apply]
  rw [extLinearEquiv_extδ, extLinearEquiv_Ext_map _ g,
    extLinearEquiv_Ext_map _ g, extLinearEquiv_extδ,
    Ext.comp_assoc _ _ _ (zero_add _) rfl (by lia)]

/-- The composite of `Extⁿ(N, X₂) → Extⁿ(N, X₃)` with the connecting map vanishes. -/
theorem Ext_map_g_comp_extδ :
    ((_root_.Ext A (ModuleCat.{u} A) n).obj (op N)).map S.g ≫ extδ N hS n = 0 := by
  ext x
  apply (extLinearEquiv N S.X₁ (n + 1)).injective
  rw [ModuleCat.comp_apply, extLinearEquiv_extδ, extLinearEquiv_Ext_obj_map,
    Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  simp

/-- The composite of the connecting map with `Extⁿ⁺¹(N, X₁) → Extⁿ⁺¹(N, X₂)` vanishes. -/
theorem extδ_comp_Ext_map_f :
    extδ N hS n ≫ ((_root_.Ext A (ModuleCat.{u} A) (n + 1)).obj (op N)).map S.f = 0 := by
  ext x
  apply (extLinearEquiv N S.X₂ (n + 1)).injective
  rw [ModuleCat.comp_apply, extLinearEquiv_Ext_obj_map, extLinearEquiv_extδ,
    Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]
  simp

/-- The derived-functor `Ext(N, -)` is exact at `Extⁿ(N, X₃)`: a class killed by the connecting
map comes from `X₂`. -/
theorem exists_Ext_map_g_eq
    (y : ((_root_.Ext A (ModuleCat.{u} A) n).obj (op N)).obj S.X₃)
    (hy : extδ N hS n y = 0) :
    ∃ x, ((_root_.Ext A (ModuleCat.{u} A) n).obj (op N)).map S.g x = y := by
  let e := fun Y => extLinearEquiv N Y n
  have h₀ : (e S.X₃ y).comp hS.extClass rfl = 0 := by
    rw [← extLinearEquiv_extδ, hy, map_zero]
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ N hS (e S.X₃ y) rfl h₀
  refine ⟨(e S.X₂).symm x, (e S.X₃).injective ?_⟩
  rw [extLinearEquiv_Ext_obj_map, LinearEquiv.apply_symm_apply, hx]

/-- The derived-functor `Ext(N, -)` is exact at `Extⁿ⁺¹(N, X₁)`: a class killed by `X₁ → X₂` is
in the image of the connecting map. -/
theorem exists_extδ_eq
    (y : ((_root_.Ext A (ModuleCat.{u} A) (n + 1)).obj (op N)).obj S.X₁)
    (hy : ((_root_.Ext A (ModuleCat.{u} A) (n + 1)).obj (op N)).map S.f y = 0) :
    ∃ x, extδ N hS n x = y := by
  let e := extLinearEquiv N S.X₁ (n + 1)
  have h₀ : (e y).comp (Ext.mk₀ S.f) (add_zero _) = 0 := by
    rw [← extLinearEquiv_Ext_obj_map, hy, map_zero]
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₁ N hS (e y) h₀ rfl
  refine ⟨(extLinearEquiv N S.X₃ n).symm x, e.injective ?_⟩
  rw [extLinearEquiv_extδ, LinearEquiv.apply_symm_apply, hx]

end Ext

section LocalCohomology

variable (I : Ideal A) {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (n : ℕ)

/-- The maps of local cohomology are computed stage by stage. -/
theorem ι_app_localCohomology_map (q : ℕ)
    {X Y : ModuleCat.{u} A} (f : X ⟶ Y) (j : (ℕᵒᵖ)ᵒᵖ) :
    (colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram I) q) j).app X ≫
        (localCohomology I q).map f =
      ((localCohomology.diagram (localCohomology.idealPowersDiagram I) q).obj j).map f ≫
        (colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram I) q) j).app Y :=
  (NatTrans.naturality
    (colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram I) q) j) f).symm

include hS in
/-- **Local cohomology is left exact**: `H⁰_I(X₁) → H⁰_I(X₂)` is injective for a short exact
sequence `0 → X₁ → X₂ → X₃ → 0`. -/
theorem localCohomology_zero_map_f_injective :
    Function.Injective ((localCohomology I 0).map S.f) :=
  ModuleCat.injective_of_stages
    (D₁ := localCohomology.diagram (localCohomology.idealPowersDiagram I) 0)
    (D₂ := localCohomology.diagram (localCohomology.idealPowersDiagram I) 0)
    (Functor.whiskerLeft _ ((evaluation _ _).map S.f)) _
    (ι_app_localCohomology_map I 0 S.f)
    (fun _ => Ext_zero_map_f_injective _ hS)

/-- The stages of the connecting map of local cohomology, natural along the system `A ⧸ Iⁿ`. -/
noncomputable def localCohomologyDiagramδ :
    localCohomology.diagram (localCohomology.idealPowersDiagram I) n ⋙
        (evaluation _ _).obj S.X₃ ⟶
      localCohomology.diagram (localCohomology.idealPowersDiagram I) (n + 1) ⋙
        (evaluation _ _).obj S.X₁ where
  app _ := extδ _ hS n
  naturality _ _ _ := extδ_naturality _ hS n _

/-- The connecting map `Hⁿ_I(X₃) → Hⁿ⁺¹_I(X₁)` of local cohomology along a short exact
sequence `0 → X₁ → X₂ → X₃ → 0`: the colimit of the connecting maps of `Ext(A ⧸ Iⁿ, -)`. -/
noncomputable def localCohomologyδ :
    (localCohomology I n).obj S.X₃ ⟶ (localCohomology I (n + 1)).obj S.X₁ :=
  (colimitObjIsoColimitCompEvaluation _ _).hom ≫ colim.map (localCohomologyDiagramδ I hS n) ≫
    (colimitObjIsoColimitCompEvaluation _ _).inv

/-- The connecting map of local cohomology is computed stage by stage. -/
theorem ι_app_localCohomologyδ (j : (ℕᵒᵖ)ᵒᵖ) :
    (colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram I) n) j).app
        S.X₃ ≫ localCohomologyδ I hS n =
      extδ _ hS n ≫
        (colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram I) (n + 1)) j).app
          S.X₁ := by
  -- unfold `localCohomologyδ`, with `localCohomology I q` as the colimit defining it
  change _ ≫ (colimitObjIsoColimitCompEvaluation _ S.X₃).hom ≫
    colim.map (localCohomologyDiagramδ I hS n) ≫ (colimitObjIsoColimitCompEvaluation _ S.X₁).inv = _
  rw [colimitObjIsoColimitCompEvaluation_ι_app_hom_assoc, colim_map, ι_colimMap_assoc,
    colimitObjIsoColimitCompEvaluation_ι_inv]
  rfl

include hS in
/-- **Local cohomology is exact at `Hⁿ_I(X₂)`** along a short exact sequence
`0 → X₁ → X₂ → X₃ → 0`, over any commutative ring. -/
theorem exists_localCohomology_map_f_eq (y : (localCohomology I n).obj S.X₂)
    (hy : (localCohomology I n).map S.g y = 0) :
    ∃ x, (localCohomology I n).map S.f x = y :=
  ModuleCat.exists_eq_of_stages
    (D₁ := localCohomology.diagram (localCohomology.idealPowersDiagram I) n)
    (D₂ := localCohomology.diagram (localCohomology.idealPowersDiagram I) n)
    (D₃ := localCohomology.diagram (localCohomology.idealPowersDiagram I) n)
    (Functor.whiskerLeft _ ((evaluation _ _).map S.f))
    (Functor.whiskerLeft _ ((evaluation _ _).map S.g)) _ _
    (ι_app_localCohomology_map I n S.f)
    (ι_app_localCohomology_map I n S.g)
    (fun _ y hy => exists_Ext_map_f_eq _ hS n y hy) y hy

/-- **Local cohomology is exact at `Hⁿ_I(X₃)`**: a class killed by the connecting map comes
from `Hⁿ_I(X₂)`. -/
theorem exists_localCohomology_map_g_eq (y : (localCohomology I n).obj S.X₃)
    (hy : localCohomologyδ I hS n y = 0) :
    ∃ x, (localCohomology I n).map S.g x = y :=
  ModuleCat.exists_eq_of_stages
    (D₁ := localCohomology.diagram (localCohomology.idealPowersDiagram I) n)
    (D₂ := localCohomology.diagram (localCohomology.idealPowersDiagram I) n)
    (D₃ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (n + 1))
    (Functor.whiskerLeft _ ((evaluation _ _).map S.g))
    (localCohomologyDiagramδ I hS n) _ _
    (ι_app_localCohomology_map I n S.g)
    (ι_app_localCohomologyδ I hS n)
    (fun _ y hy => exists_Ext_map_g_eq _ hS n y hy) y hy

/-- **Local cohomology is exact at `Hⁿ⁺¹_I(X₁)`**: a class killed by `X₁ → X₂` is in the image
of the connecting map. -/
theorem exists_localCohomologyδ_eq (y : (localCohomology I (n + 1)).obj S.X₁)
    (hy : (localCohomology I (n + 1)).map S.f y = 0) :
    ∃ x, localCohomologyδ I hS n x = y :=
  ModuleCat.exists_eq_of_stages
    (D₁ := localCohomology.diagram (localCohomology.idealPowersDiagram I) n)
    (D₂ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (n + 1))
    (D₃ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (n + 1))
    (localCohomologyDiagramδ I hS n)
    (Functor.whiskerLeft _ ((evaluation _ _).map S.f)) _ _
    (ι_app_localCohomologyδ I hS n)
    (ι_app_localCohomology_map I (n + 1) S.f)
    (fun _ y hy => exists_extδ_eq _ hS n y hy) y hy

/-- Local cohomology carries the composite `X₁ → X₂ → X₃` of a short complex to zero in positive
degrees. -/
theorem localCohomology_map_f_comp_map_g :
    (localCohomology I n).map S.f ≫ (localCohomology I n).map S.g = 0 :=
  ModuleCat.comp_eq_zero_of_stages
    (D₁ := localCohomology.diagram (localCohomology.idealPowersDiagram I) n)
    (D₂ := localCohomology.diagram (localCohomology.idealPowersDiagram I) n)
    (D₃ := localCohomology.diagram (localCohomology.idealPowersDiagram I) n)
    (Functor.whiskerLeft _ ((evaluation _ _).map S.f))
    (Functor.whiskerLeft _ ((evaluation _ _).map S.g)) _ _
    (ι_app_localCohomology_map I n S.f)
    (ι_app_localCohomology_map I n S.g)
    (fun _ => Ext_map_f_comp_map_g _ n)

/-- The composite of `Hⁿ_I(X₂) → Hⁿ_I(X₃)` with the connecting map vanishes. -/
theorem localCohomology_map_g_comp_localCohomologyδ :
    (localCohomology I n).map S.g ≫ localCohomologyδ I hS n = 0 :=
  ModuleCat.comp_eq_zero_of_stages
    (D₁ := localCohomology.diagram (localCohomology.idealPowersDiagram I) n)
    (D₂ := localCohomology.diagram (localCohomology.idealPowersDiagram I) n)
    (D₃ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (n + 1))
    (Functor.whiskerLeft _ ((evaluation _ _).map S.g))
    (localCohomologyDiagramδ I hS n) _ _
    (ι_app_localCohomology_map I n S.g)
    (ι_app_localCohomologyδ I hS n)
    (fun _ => Ext_map_g_comp_extδ _ hS n)

/-- The composite of the connecting map with `Hⁿ⁺¹_I(X₁) → Hⁿ⁺¹_I(X₂)` vanishes. -/
theorem localCohomologyδ_comp_localCohomology_map_f :
    localCohomologyδ I hS n ≫ (localCohomology I (n + 1)).map S.f = 0 :=
  ModuleCat.comp_eq_zero_of_stages
    (D₁ := localCohomology.diagram (localCohomology.idealPowersDiagram I) n)
    (D₂ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (n + 1))
    (D₃ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (n + 1))
    (localCohomologyDiagramδ I hS n)
    (Functor.whiskerLeft _ ((evaluation _ _).map S.f)) _ _
    (ι_app_localCohomologyδ I hS n)
    (ι_app_localCohomology_map I (n + 1) S.f)
    (fun _ => extδ_comp_Ext_map_f _ hS n)

include hS in
/-- **The long exact sequence of local cohomology, at `Hⁿ_I(X₂)`**: for a short exact sequence
`0 → X₁ → X₂ → X₃ → 0`, `Hⁿ_I(X₁) → Hⁿ_I(X₂) → Hⁿ_I(X₃)` is exact. -/
theorem localCohomology_sequence_exact₂ :
    (ShortComplex.mk _ _ (localCohomology_map_f_comp_map_g I (S := S) n)).Exact :=
  ShortComplex.moduleCat_exact_iff _ |>.2 (exists_localCohomology_map_f_eq I hS n)

/-- **The long exact sequence of local cohomology, at `Hⁿ_I(X₃)`**:
`Hⁿ_I(X₂) → Hⁿ_I(X₃) → Hⁿ⁺¹_I(X₁)` is exact. -/
theorem localCohomology_sequence_exact₃ :
    (ShortComplex.mk _ _ (localCohomology_map_g_comp_localCohomologyδ I hS n)).Exact :=
  ShortComplex.moduleCat_exact_iff _ |>.2 (exists_localCohomology_map_g_eq I hS n)

/-- **The long exact sequence of local cohomology, at `Hⁿ⁺¹_I(X₁)`**:
`Hⁿ_I(X₃) → Hⁿ⁺¹_I(X₁) → Hⁿ⁺¹_I(X₂)` is exact. -/
theorem localCohomology_sequence_exact₁ :
    (ShortComplex.mk _ _ (localCohomologyδ_comp_localCohomology_map_f I hS n)).Exact :=
  ShortComplex.moduleCat_exact_iff _ |>.2 (exists_localCohomologyδ_eq I hS n)

end LocalCohomology

end TauCeti.Supports
