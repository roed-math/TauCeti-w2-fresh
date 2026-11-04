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
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import TauCeti.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Local cohomology of a short exact sequence in positive degrees

Mathlib defines `localCohomology I q` as the colimit over `n` of the derived-functor
`Ext^q_A(A/Iⁿ, -)`. For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of `A`-modules this file
constructs the connecting map `H^{p+1}_I(X₃) → H^{p+2}_I(X₁)` and proves that

`H^{p+1}_I(X₁) → H^{p+1}_I(X₂) → H^{p+1}_I(X₃) → H^{p+2}_I(X₁) → H^{p+2}_I(X₂)`

is exact at the three inner terms, so that the positive-degree part of the long exact sequence of
local cohomology holds for every commutative ring (Stacks, Lemma 47.8.2 (0954), in the form of a
`δ`-functor).

Stage by stage, `TauCeti.extSuccLinearEquiv` identifies the derived-functor `Extᵖ⁺¹(N, -)` with
the derived-category `Extᵖ⁺¹(N, -)`, naturally in both arguments. There the long exact sequence of
`Ext` in the second argument is Mathlib's `Ext.covariant_sequence_exact₁`, `₂` and `₃`, and the
connecting map is the Yoneda product with the class `hS.extClass` of the extension. Exactness
then passes to the filtered colimit over `n`, by `TauCeti.ModuleCat.exists_eq_of_stages` and
`TauCeti.ModuleCat.comp_eq_zero_of_stages`.

## Main definitions

* `TauCeti.Supports.extSuccδ`: the connecting map `Extᵖ⁺¹(N, X₃) → Extᵖ⁺²(N, X₁)` of the
  derived-functor `Ext`.
* `TauCeti.Supports.localCohomologySuccδ`: the connecting map
  `H^{p+1}_I(X₃) → H^{p+2}_I(X₁)` of local cohomology.

## Main results

* `TauCeti.Supports.localCohomology_sequence_exact₂`: exactness at `H^{p+1}_I(X₂)`, with the
  elementwise form `TauCeti.Supports.exists_localCohomology_map_f_eq`.
* `TauCeti.Supports.localCohomology_sequence_exact₃`: exactness at `H^{p+1}_I(X₃)`, with the
  elementwise form `TauCeti.Supports.exists_localCohomology_map_g_eq`.
* `TauCeti.Supports.localCohomology_sequence_exact₁`: exactness at `H^{p+2}_I(X₁)`, with the
  elementwise form `TauCeti.Supports.exists_localCohomologySuccδ_eq`.
-/

public section

universe u

open CategoryTheory CategoryTheory.Abelian Limits Opposite

namespace TauCeti.Supports

variable {A : Type u} [CommRing A]

section Ext

variable (N : ModuleCat.{u} A) {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (p : ℕ)

include hS in
/-- The derived-functor `Extᵖ⁺¹(N, -)` is exact at the middle of a short exact sequence. -/
theorem exists_Ext_map_f_eq
    (y : ((_root_.Ext A (ModuleCat.{u} A) (p + 1)).obj (op N)).obj S.X₂)
    (hy : ((_root_.Ext A (ModuleCat.{u} A) (p + 1)).obj (op N)).map S.g y = 0) :
    ∃ x, ((_root_.Ext A (ModuleCat.{u} A) (p + 1)).obj (op N)).map S.f x = y := by
  let e := fun Y => extSuccLinearEquiv.{u} A (projectiveResolution N) Y p
  have h₀ : (e S.X₂ y).comp (Ext.mk₀ S.g) (add_zero _) = 0 := by
    rw [← extSuccLinearEquiv_Ext_obj_map, hy, map_zero]
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₂ N hS (e S.X₂ y) h₀
  refine ⟨(e S.X₁).symm x, (e S.X₂).injective ?_⟩
  rw [extSuccLinearEquiv_Ext_obj_map, LinearEquiv.apply_symm_apply, hx]

/-- The derived-functor `Extᵖ⁺¹(N, -)` carries the composite `X₁ → X₂ → X₃` of a short complex to
zero. -/
theorem Ext_map_f_comp_map_g :
    ((_root_.Ext A (ModuleCat.{u} A) (p + 1)).obj (op N)).map S.f ≫
      ((_root_.Ext A (ModuleCat.{u} A) (p + 1)).obj (op N)).map S.g = 0 := by
  rw [← Functor.map_comp, S.zero]
  ext x
  apply (extSuccLinearEquiv.{u} A (projectiveResolution N) S.X₃ p).injective
  rw [extSuccLinearEquiv_Ext_obj_map, Ext.mk₀_zero, Ext.comp_zero]
  simp

/-- The connecting map `Extᵖ⁺¹(N, X₃) → Extᵖ⁺²(N, X₁)` of the derived-functor `Ext` along a short
exact sequence: the Yoneda product with the class of the extension, computed on the
derived-category `Ext`. -/
noncomputable def extSuccδ :
    ((_root_.Ext A (ModuleCat.{u} A) (p + 1)).obj (op N)).obj S.X₃ ⟶
      ((_root_.Ext A (ModuleCat.{u} A) (p + 2)).obj (op N)).obj S.X₁ :=
  ModuleCat.ofHom <|
    (extSuccLinearEquiv.{u} A (projectiveResolution N) S.X₁ (p + 1)).symm.toLinearMap ∘ₗ
      Ext.postcompOfLinear hS.extClass A N rfl ∘ₗ
        (extSuccLinearEquiv.{u} A (projectiveResolution N) S.X₃ p).toLinearMap

/-- Under the comparison of the two `Ext`s, `extSuccδ` is the Yoneda product with the class of the
extension. -/
theorem extSuccLinearEquiv_extSuccδ
    (x : ((_root_.Ext A (ModuleCat.{u} A) (p + 1)).obj (op N)).obj S.X₃) :
    extSuccLinearEquiv.{u} A (projectiveResolution N) S.X₁ (p + 1) (extSuccδ N hS p x) =
      (extSuccLinearEquiv.{u} A (projectiveResolution N) S.X₃ p x).comp hS.extClass rfl :=
  LinearEquiv.apply_symm_apply _ _

/-- `extSuccδ` is natural in the first argument. -/
theorem extSuccδ_naturality {N' : ModuleCat.{u} A} (g : N' ⟶ N) :
    ((_root_.Ext A (ModuleCat.{u} A) (p + 1)).map g.op).app S.X₃ ≫ extSuccδ N' hS p =
      extSuccδ N hS p ≫ ((_root_.Ext A (ModuleCat.{u} A) (p + 2)).map g.op).app S.X₁ := by
  ext x
  apply (extSuccLinearEquiv.{u} A (projectiveResolution N') S.X₁ (p + 1)).injective
  simp only [ModuleCat.comp_apply]
  rw [extSuccLinearEquiv_extSuccδ, extSuccLinearEquiv_Ext_map g _ (projectiveResolution N'),
    extSuccLinearEquiv_Ext_map g _ (projectiveResolution N'), extSuccLinearEquiv_extSuccδ,
    Ext.comp_assoc _ _ _ (zero_add _) rfl (by lia)]

/-- The composite of `Extᵖ⁺¹(N, X₂) → Extᵖ⁺¹(N, X₃)` with the connecting map vanishes. -/
theorem Ext_map_g_comp_extSuccδ :
    ((_root_.Ext A (ModuleCat.{u} A) (p + 1)).obj (op N)).map S.g ≫ extSuccδ N hS p = 0 := by
  ext x
  apply (extSuccLinearEquiv.{u} A (projectiveResolution N) S.X₁ (p + 1)).injective
  rw [ModuleCat.comp_apply, extSuccLinearEquiv_extSuccδ, extSuccLinearEquiv_Ext_obj_map,
    Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  simp

/-- The composite of the connecting map with `Extᵖ⁺²(N, X₁) → Extᵖ⁺²(N, X₂)` vanishes. -/
theorem extSuccδ_comp_Ext_map_f :
    extSuccδ N hS p ≫ ((_root_.Ext A (ModuleCat.{u} A) (p + 2)).obj (op N)).map S.f = 0 := by
  ext x
  apply (extSuccLinearEquiv.{u} A (projectiveResolution N) S.X₂ (p + 1)).injective
  rw [ModuleCat.comp_apply, extSuccLinearEquiv_Ext_obj_map, extSuccLinearEquiv_extSuccδ,
    Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]
  simp

/-- The derived-functor `Ext(N, -)` is exact at `Extᵖ⁺¹(N, X₃)`: a class killed by the connecting
map comes from `X₂`. -/
theorem exists_Ext_map_g_eq
    (y : ((_root_.Ext A (ModuleCat.{u} A) (p + 1)).obj (op N)).obj S.X₃)
    (hy : extSuccδ N hS p y = 0) :
    ∃ x, ((_root_.Ext A (ModuleCat.{u} A) (p + 1)).obj (op N)).map S.g x = y := by
  let e := fun Y => extSuccLinearEquiv.{u} A (projectiveResolution N) Y p
  have h₀ : (e S.X₃ y).comp hS.extClass rfl = 0 := by
    rw [← extSuccLinearEquiv_extSuccδ, hy, map_zero]
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ N hS (e S.X₃ y) rfl h₀
  refine ⟨(e S.X₂).symm x, (e S.X₃).injective ?_⟩
  rw [extSuccLinearEquiv_Ext_obj_map, LinearEquiv.apply_symm_apply, hx]

/-- The derived-functor `Ext(N, -)` is exact at `Extᵖ⁺²(N, X₁)`: a class killed by `X₁ → X₂` is
in the image of the connecting map. -/
theorem exists_extSuccδ_eq
    (y : ((_root_.Ext A (ModuleCat.{u} A) (p + 2)).obj (op N)).obj S.X₁)
    (hy : ((_root_.Ext A (ModuleCat.{u} A) (p + 2)).obj (op N)).map S.f y = 0) :
    ∃ x, extSuccδ N hS p x = y := by
  let e := extSuccLinearEquiv.{u} A (projectiveResolution N) S.X₁ (p + 1)
  have h₀ : (e y).comp (Ext.mk₀ S.f) (add_zero _) = 0 := by
    rw [← extSuccLinearEquiv_Ext_obj_map, hy, map_zero]
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₁ N hS (e y) h₀ rfl
  refine ⟨(extSuccLinearEquiv.{u} A (projectiveResolution N) S.X₃ p).symm x, e.injective ?_⟩
  rw [extSuccLinearEquiv_extSuccδ, LinearEquiv.apply_symm_apply, hx]

end Ext

section LocalCohomology

variable (I : Ideal A) {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (p : ℕ)

/-- The stages of the connecting map of local cohomology, natural along the system `A ⧸ Iⁿ`. -/
noncomputable def localCohomologyDiagramδ :
    localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1) ⋙
        (evaluation _ _).obj S.X₃ ⟶
      localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 2) ⋙
        (evaluation _ _).obj S.X₁ where
  app _ := extSuccδ _ hS p
  naturality _ _ _ := extSuccδ_naturality _ hS p _

/-- The maps of local cohomology are computed stage by stage. -/
theorem ι_app_localCohomology_map (q : ℕ)
    {X Y : ModuleCat.{u} A} (f : X ⟶ Y) (j : (ℕᵒᵖ)ᵒᵖ) :
    (colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram I) q) j).app X ≫
        (localCohomology I q).map f =
      ((localCohomology.diagram (localCohomology.idealPowersDiagram I) q).obj j).map f ≫
        (colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram I) q) j).app Y :=
  (NatTrans.naturality
    (colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram I) q) j) f).symm

/-- The connecting map `H^{p+1}_I(X₃) → H^{p+2}_I(X₁)` of local cohomology along a short exact
sequence `0 → X₁ → X₂ → X₃ → 0`: the colimit of the connecting maps of `Ext(A ⧸ Iⁿ, -)`. -/
noncomputable def localCohomologySuccδ :
    (localCohomology I (p + 1)).obj S.X₃ ⟶ (localCohomology I (p + 2)).obj S.X₁ :=
  (colimitObjIsoColimitCompEvaluation _ _).hom ≫ colim.map (localCohomologyDiagramδ I hS p) ≫
    (colimitObjIsoColimitCompEvaluation _ _).inv

/-- The connecting map of local cohomology is computed stage by stage. -/
theorem ι_app_localCohomologySuccδ (j : (ℕᵒᵖ)ᵒᵖ) :
    (colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1)) j).app
        S.X₃ ≫ localCohomologySuccδ I hS p =
      extSuccδ _ hS p ≫
        (colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 2)) j).app
          S.X₁ := by
  -- unfold `localCohomologySuccδ`, with `localCohomology I q` as the colimit defining it
  change _ ≫ (colimitObjIsoColimitCompEvaluation _ S.X₃).hom ≫
    colim.map (localCohomologyDiagramδ I hS p) ≫ (colimitObjIsoColimitCompEvaluation _ S.X₁).inv = _
  rw [colimitObjIsoColimitCompEvaluation_ι_app_hom_assoc, colim_map, ι_colimMap_assoc,
    colimitObjIsoColimitCompEvaluation_ι_inv]
  rfl

include hS in
/-- **Local cohomology is exact at `H^{p+1}_I(X₂)`** along a short exact sequence
`0 → X₁ → X₂ → X₃ → 0`, over any commutative ring. -/
theorem exists_localCohomology_map_f_eq (y : (localCohomology I (p + 1)).obj S.X₂)
    (hy : (localCohomology I (p + 1)).map S.g y = 0) :
    ∃ x, (localCohomology I (p + 1)).map S.f x = y :=
  ModuleCat.exists_eq_of_stages
    (D₁ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1))
    (D₂ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1))
    (D₃ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1))
    (Functor.whiskerLeft _ ((evaluation _ _).map S.f))
    (Functor.whiskerLeft _ ((evaluation _ _).map S.g)) _ _
    (ι_app_localCohomology_map I (p + 1) S.f)
    (ι_app_localCohomology_map I (p + 1) S.g)
    (fun _ y hy => exists_Ext_map_f_eq _ hS p y hy) y hy

/-- **Local cohomology is exact at `H^{p+1}_I(X₃)`**: a class killed by the connecting map comes
from `H^{p+1}_I(X₂)`. -/
theorem exists_localCohomology_map_g_eq (y : (localCohomology I (p + 1)).obj S.X₃)
    (hy : localCohomologySuccδ I hS p y = 0) :
    ∃ x, (localCohomology I (p + 1)).map S.g x = y :=
  ModuleCat.exists_eq_of_stages
    (D₁ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1))
    (D₂ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1))
    (D₃ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 2))
    (Functor.whiskerLeft _ ((evaluation _ _).map S.g))
    (localCohomologyDiagramδ I hS p) _ _
    (ι_app_localCohomology_map I (p + 1) S.g)
    (ι_app_localCohomologySuccδ I hS p)
    (fun _ y hy => exists_Ext_map_g_eq _ hS p y hy) y hy

/-- **Local cohomology is exact at `H^{p+2}_I(X₁)`**: a class killed by `X₁ → X₂` is in the image
of the connecting map. -/
theorem exists_localCohomologySuccδ_eq (y : (localCohomology I (p + 2)).obj S.X₁)
    (hy : (localCohomology I (p + 2)).map S.f y = 0) :
    ∃ x, localCohomologySuccδ I hS p x = y :=
  ModuleCat.exists_eq_of_stages
    (D₁ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1))
    (D₂ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 2))
    (D₃ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 2))
    (localCohomologyDiagramδ I hS p)
    (Functor.whiskerLeft _ ((evaluation _ _).map S.f)) _ _
    (ι_app_localCohomologySuccδ I hS p)
    (ι_app_localCohomology_map I (p + 2) S.f)
    (fun _ y hy => exists_extSuccδ_eq _ hS p y hy) y hy

/-- Local cohomology carries the composite `X₁ → X₂ → X₃` of a short complex to zero in positive
degrees. -/
theorem localCohomology_map_f_comp_map_g :
    (localCohomology I (p + 1)).map S.f ≫ (localCohomology I (p + 1)).map S.g = 0 :=
  ModuleCat.comp_eq_zero_of_stages
    (D₁ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1))
    (D₂ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1))
    (D₃ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1))
    (Functor.whiskerLeft _ ((evaluation _ _).map S.f))
    (Functor.whiskerLeft _ ((evaluation _ _).map S.g)) _ _
    (ι_app_localCohomology_map I (p + 1) S.f)
    (ι_app_localCohomology_map I (p + 1) S.g)
    (fun _ => Ext_map_f_comp_map_g _ p)

/-- The composite of `H^{p+1}_I(X₂) → H^{p+1}_I(X₃)` with the connecting map vanishes. -/
theorem localCohomology_map_g_comp_localCohomologySuccδ :
    (localCohomology I (p + 1)).map S.g ≫ localCohomologySuccδ I hS p = 0 :=
  ModuleCat.comp_eq_zero_of_stages
    (D₁ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1))
    (D₂ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1))
    (D₃ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 2))
    (Functor.whiskerLeft _ ((evaluation _ _).map S.g))
    (localCohomologyDiagramδ I hS p) _ _
    (ι_app_localCohomology_map I (p + 1) S.g)
    (ι_app_localCohomologySuccδ I hS p)
    (fun _ => Ext_map_g_comp_extSuccδ _ hS p)

/-- The composite of the connecting map with `H^{p+2}_I(X₁) → H^{p+2}_I(X₂)` vanishes. -/
theorem localCohomologySuccδ_comp_localCohomology_map_f :
    localCohomologySuccδ I hS p ≫ (localCohomology I (p + 2)).map S.f = 0 :=
  ModuleCat.comp_eq_zero_of_stages
    (D₁ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1))
    (D₂ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 2))
    (D₃ := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 2))
    (localCohomologyDiagramδ I hS p)
    (Functor.whiskerLeft _ ((evaluation _ _).map S.f)) _ _
    (ι_app_localCohomologySuccδ I hS p)
    (ι_app_localCohomology_map I (p + 2) S.f)
    (fun _ => extSuccδ_comp_Ext_map_f _ hS p)

include hS in
/-- **The long exact sequence of local cohomology, at `H^{p+1}_I(X₂)`**: for a short exact sequence
`0 → X₁ → X₂ → X₃ → 0`, `H^{p+1}_I(X₁) → H^{p+1}_I(X₂) → H^{p+1}_I(X₃)` is exact. -/
theorem localCohomology_sequence_exact₂ :
    (ShortComplex.mk _ _ (localCohomology_map_f_comp_map_g I (S := S) p)).Exact :=
  ShortComplex.moduleCat_exact_iff _ |>.2 (exists_localCohomology_map_f_eq I hS p)

/-- **The long exact sequence of local cohomology, at `H^{p+1}_I(X₃)`**:
`H^{p+1}_I(X₂) → H^{p+1}_I(X₃) → H^{p+2}_I(X₁)` is exact. -/
theorem localCohomology_sequence_exact₃ :
    (ShortComplex.mk _ _ (localCohomology_map_g_comp_localCohomologySuccδ I hS p)).Exact :=
  ShortComplex.moduleCat_exact_iff _ |>.2 (exists_localCohomology_map_g_eq I hS p)

/-- **The long exact sequence of local cohomology, at `H^{p+2}_I(X₁)`**:
`H^{p+1}_I(X₃) → H^{p+2}_I(X₁) → H^{p+2}_I(X₂)` is exact. -/
theorem localCohomology_sequence_exact₁ :
    (ShortComplex.mk _ _ (localCohomologySuccδ_comp_localCohomology_map_f I hS p)).Exact :=
  ShortComplex.moduleCat_exact_iff _ |>.2 (exists_localCohomologySuccδ_eq I hS p)

end LocalCohomology

end TauCeti.Supports
