/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Homology.Ext.ProjectiveResolution

/-!
# Comparing the two `Ext`s in positive degrees

Mathlib has two `Ext`s: the derived functor `Ext k C n` of `Mathlib.CategoryTheory.Abelian.Ext`
(on which `localCohomology` is built), computed from a projective resolution `P` of `X` by
`ProjectiveResolution.isoExt`, and the derived-category `CategoryTheory.Abelian.Ext`, computed from
the same resolution by `ProjectiveResolution.extMk`. Both are the cohomology of the complex
`Hom(P, Y)`. This file turns that observation into a `k`-linear equivalence in positive degrees,
natural in both arguments. Naturality in the second argument rests on
`ProjectiveResolution.leftDerived_app_eq`.

## Main definitions

* `TauCeti.extSuccClass P Y p f hf`: the class in the derived-functor `Extᵖ⁺¹(X, Y)` of a cocycle
  `f : Pₚ₊₁ ⟶ Y`.
* `TauCeti.extSuccLinearEquiv P Y p`: the `k`-linear equivalence between the derived-functor
  `Extᵖ⁺¹(X, Y)` and the derived-category `Extᵖ⁺¹(X, Y)`, sending the class of a cocycle `f` to
  `P.extMk f`.

## Main results

* `TauCeti.HomologicalComplex.homologyMap_comp_homologyIsoSc'_hom`,
  `TauCeti.ShortComplex.moduleCatHomologyIso_hom_homologyMap_inv_mk`: maps induced on homology,
  computed through explicit short complexes and, for modules, on classes of cycles.
* `TauCeti.extSuccLinearEquiv_extSuccClass`: the equivalence sends the class of `f` to
  `P.extMk f`.
* `TauCeti.Ext_map_extSuccClass`: the map induced by `g : X' ⟶ X` on the derived-functor `Ext`
  precomposes cocycles with a chain map lying over `g`.
* `TauCeti.map_extSuccClass_of_comp_isoExt_hom`: a map of derived-functor `Ext` groups computed on
  `Hom`-complexes by a chain map acts on classes of cocycles through that chain map.
* `TauCeti.extSuccLinearEquiv_Ext_map`: the equivalence is natural in the first argument; the map
  induced by `g` becomes the Yoneda product with `Ext.mk₀ g`.
* `TauCeti.Ext_obj_map_comp_isoExt_hom`, `TauCeti.Ext_obj_map_extSuccClass`: `isoExt` is natural
  in the second argument, which acts on cocycles by postcomposition.
* `TauCeti.extSuccLinearEquiv_Ext_obj_map`: the equivalence is natural in the second argument;
  the map induced by `f` becomes the Yoneda product with `Ext.mk₀ f`.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.5, for `Ext` computed from a
  projective resolution, and Section 10.7, for `Ext` as morphisms in the derived category.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Ring k] [Linear k C]
  [HasExt.{w} C] [EnoughProjectives C] {X Y : C}

/-- `HomologicalComplex.homologyIsoSc'` is natural: computing homology in degree `j` through the
explicit short complexes `sc' i j k` commutes with the maps induced by a chain map. -/
theorem HomologicalComplex.homologyMap_comp_homologyIsoSc'_hom {D : Type*} [Category* D]
    [Abelian D] {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex D c} (ψ : K ⟶ L)
    (i j l : ι) (hi : c.prev j = i) (hl : c.next j = l) :
    HomologicalComplex.homologyMap ψ j ≫ (L.homologyIsoSc' i j l hi hl).hom =
      (K.homologyIsoSc' i j l hi hl).hom ≫
        ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor' D c i j l).map ψ) := by
  rw [HomologicalComplex.homologyIsoSc', HomologicalComplex.homologyIsoSc',
    ShortComplex.homologyMapIso_hom, ShortComplex.homologyMapIso_hom,
    HomologicalComplex.homologyMap]
  -- `erw`: `K.homology j` is only definitionally the homology of `K.sc j`
  erw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1
  exact (HomologicalComplex.natIsoSc' D c i j l hi hl).hom.naturality ψ

/-- On the explicit homology `ker g ⧸ im f` of short complexes of modules, the map induced on
homology by `φ` sends the class of a cycle `z` to the class of `φ.τ₂ z`. -/
theorem ShortComplex.moduleCatHomologyIso_hom_homologyMap_inv_mk {R : Type*} [Ring R]
    {S₁ S₂ : ShortComplex (ModuleCat R)} (φ : S₁ ⟶ S₂) (z : LinearMap.ker S₁.g.hom) :
    S₂.moduleCatHomologyIso.hom (ShortComplex.homologyMap φ
      (S₁.moduleCatHomologyIso.inv (Submodule.Quotient.mk z))) =
      Submodule.Quotient.mk ⟨φ.τ₂ z.1, by
        rw [LinearMap.mem_ker, ← ModuleCat.comp_apply, φ.comm₂₃, ModuleCat.comp_apply,
          LinearMap.mem_ker.1 z.2, map_zero]⟩ := by
  have hz : φ.τ₂ z.1 ∈ LinearMap.ker S₂.g.hom := by
    rw [LinearMap.mem_ker, ← ModuleCat.comp_apply, φ.comm₂₃, ModuleCat.comp_apply,
      LinearMap.mem_ker.1 z.2, map_zero]
  have h₁ : S₁.moduleCatHomologyIso.inv (Submodule.Quotient.mk z) =
      S₁.homologyπ (S₁.moduleCatCyclesIso.inv z) :=
    (ShortComplex.moduleCatCyclesIso_inv_π_apply S₁ z).symm
  have h₂ : S₂.moduleCatCyclesIso.hom (ShortComplex.cyclesMap φ (S₁.moduleCatCyclesIso.inv z)) =
      ⟨φ.τ₂ z.1, hz⟩ := by
    apply Subtype.ext
    have := ShortComplex.moduleCatCyclesIso_hom_i_apply S₂
      (ShortComplex.cyclesMap φ (S₁.moduleCatCyclesIso.inv z))
    refine this.trans ?_
    rw [← ModuleCat.comp_apply, ShortComplex.cyclesMap_i, ModuleCat.comp_apply]
    exact congrArg φ.τ₂ (ShortComplex.moduleCatCyclesIso_inv_iCycles_apply S₁ z)
  have h₃ := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality φ)
    (S₁.moduleCatCyclesIso.inv z)
  simp only [ConcreteCategory.comp_apply] at h₃
  rw [h₁, h₃, ShortComplex.π_moduleCatCyclesIso_hom_apply, h₂]
  rfl

variable (k) in
/-- The cohomology of `Hom(P, Y)` in degree `p + 1`, as the explicit quotient of cocycles by
coboundaries, is the derived-category `Extᵖ⁺¹(X, Y)`: the class of a cocycle `f` goes to
`P.extMk f`. -/
noncomputable def homologyLinearEquivExt (P : ProjectiveResolution X) (Y : C) (p : ℕ) :
    ((P.complex.linearYonedaObj k Y).sc' p (p + 1) (p + 2)).moduleCatLeftHomologyData.H ≃ₗ[k]
      Ext.{w} X Y (p + 1) := by
  let S := (P.complex.linearYonedaObj k Y).sc' p (p + 1) (p + 2)
  let L : LinearMap.ker S.g.hom →ₗ[k] Ext.{w} X Y (p + 1) :=
    { toFun := fun f => P.extMk (f.1 : P.complex.X (p + 1) ⟶ Y) (p + 2) rfl f.2
      map_add' := fun f g => (P.add_extMk f.1 g.1 (p + 2) rfl f.2 g.2).symm
      map_smul' := fun c f => (P.smul_extMk c f.1 (p + 2) rfl f.2).symm }
  refine LinearEquiv.ofBijective
    ((LinearMap.range S.moduleCatToCycles).liftQ L ?_) ⟨?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    exact (P.extMk_eq_zero_iff _ (p + 2) rfl (S.moduleCatToCycles g).2 p rfl).2 ⟨g, rfl⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨g, hg⟩ := (P.extMk_eq_zero_iff _ (p + 2) rfl f.2 p rfl).1 hx
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨g, Subtype.ext hg⟩
  · intro α
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective α (p + 2) rfl
    exact ⟨Submodule.Quotient.mk ⟨f, hf⟩, rfl⟩

omit [EnoughProjectives C] in
/-- `homologyLinearEquivExt` sends the class of a cocycle `f` to `P.extMk f`. -/
@[simp]
theorem homologyLinearEquivExt_mk (P : ProjectiveResolution X) (Y : C) (p : ℕ)
    (f : P.complex.X (p + 1) ⟶ Y) (hf : P.complex.d (p + 2) (p + 1) ≫ f = 0) :
    homologyLinearEquivExt k P Y p (Submodule.Quotient.mk ⟨f, hf⟩) = P.extMk f (p + 2) rfl hf := by
  refine Submodule.liftQ_apply _ _ (h := ?_) _
  rintro _ ⟨g, rfl⟩
  exact (P.extMk_eq_zero_iff _ (p + 2) rfl
    (((P.complex.linearYonedaObj k Y).sc' p (p + 1) (p + 2)).moduleCatToCycles g).2 p rfl).2
    ⟨g, rfl⟩

variable (k) in
/-- The derived-functor `Extᵖ⁺¹(X, Y)` as the explicit quotient of the cocycles of `Hom(P, Y)` in
degree `p + 1` by the coboundaries. -/
noncomputable def extSuccIsoHomology (P : ProjectiveResolution X) (Y : C) (p : ℕ) :
    ((_root_.Ext k C (p + 1)).obj (op X)).obj Y ≅
      ((P.complex.linearYonedaObj k Y).sc' p (p + 1) (p + 2)).moduleCatLeftHomologyData.H :=
  P.isoExt (p + 1) Y ≪≫ (P.complex.linearYonedaObj k Y).homologyIsoSc' p (p + 1) (p + 2)
    (by simp) (by simp) ≪≫ ShortComplex.moduleCatHomologyIso _

variable (k) in
/-- The class in the derived-functor `Extᵖ⁺¹(X, Y)` of a cocycle `f : Pₚ₊₁ ⟶ Y` of the complex
`Hom(P, Y)`. -/
noncomputable def extSuccClass (P : ProjectiveResolution X) (Y : C) (p : ℕ)
    (f : P.complex.X (p + 1) ⟶ Y) (hf : P.complex.d (p + 2) (p + 1) ≫ f = 0) :
    ((_root_.Ext k C (p + 1)).obj (op X)).obj Y :=
  (extSuccIsoHomology k P Y p).inv (Submodule.Quotient.mk ⟨f, hf⟩)

omit [HasExt C] in
/-- Every element of the derived-functor `Extᵖ⁺¹(X, Y)` is the class of a cocycle. -/
theorem extSuccClass_surjective (P : ProjectiveResolution X) (Y : C) (p : ℕ)
    (α : ((_root_.Ext k C (p + 1)).obj (op X)).obj Y) :
    ∃ (f : P.complex.X (p + 1) ⟶ Y) (hf : P.complex.d (p + 2) (p + 1) ≫ f = 0),
      extSuccClass k P Y p f hf = α := by
  obtain ⟨⟨f, hf⟩, h⟩ := Submodule.Quotient.mk_surjective _ ((extSuccIsoHomology k P Y p).hom α)
  refine ⟨f, hf, ?_⟩
  -- unfold `extSuccClass`
  change (extSuccIsoHomology k P Y p).inv _ = α
  rw [h, Iso.hom_inv_id_apply (extSuccIsoHomology k P Y p)]

variable (k) in
/-- **The two `Ext`s agree in positive degrees.** For a projective resolution `P` of `X`, the
derived-functor `Extᵖ⁺¹(X, Y)` of `Mathlib.CategoryTheory.Abelian.Ext` is `k`-linearly equivalent
to the derived-category `Extᵖ⁺¹(X, Y)`; the class of a cocycle `f` goes to `P.extMk f`. -/
noncomputable def extSuccLinearEquiv (P : ProjectiveResolution X) (Y : C) (p : ℕ) :
    ((_root_.Ext k C (p + 1)).obj (op X)).obj Y ≃ₗ[k] Ext.{w} X Y (p + 1) :=
  (extSuccIsoHomology k P Y p).toLinearEquiv ≪≫ₗ homologyLinearEquivExt k P Y p

/-- `extSuccLinearEquiv` sends the class of a cocycle `f` to `P.extMk f`. -/
@[simp]
theorem extSuccLinearEquiv_extSuccClass (P : ProjectiveResolution X) (Y : C) (p : ℕ)
    (f : P.complex.X (p + 1) ⟶ Y) (hf : P.complex.d (p + 2) (p + 1) ≫ f = 0) :
    extSuccLinearEquiv.{w} k P Y p (extSuccClass k P Y p f hf) = P.extMk f (p + 2) rfl hf := by
  -- unfold `extSuccLinearEquiv` and `extSuccClass`
  change homologyLinearEquivExt k P Y p ((extSuccIsoHomology k P Y p).hom
    ((extSuccIsoHomology k P Y p).inv _)) = _
  have h := Iso.inv_hom_id_apply (extSuccIsoHomology k P Y p) (Submodule.Quotient.mk ⟨f, hf⟩)
  exact (congrArg (homologyLinearEquivExt k P Y p) h).trans (homologyLinearEquivExt_mk P Y p f hf)

/-- The inverse of `extSuccLinearEquiv` sends `P.extMk f` to the class of `f`. -/
@[simp]
theorem extSuccLinearEquiv_symm_extMk (P : ProjectiveResolution X) (Y : C) (p : ℕ)
    (f : P.complex.X (p + 1) ⟶ Y) (hf : P.complex.d (p + 2) (p + 1) ≫ f = 0) :
    (extSuccLinearEquiv.{w} k P Y p).symm (P.extMk f (p + 2) rfl hf) = extSuccClass k P Y p f hf :=
  (LinearEquiv.symm_apply_eq _).2 (extSuccLinearEquiv_extSuccClass P Y p f hf).symm

omit [HasExt C] in
/-- A map `m` between derived-functor `Ext` groups that `isoExt` turns into the map on cohomology
induced by a chain map `ψ` of `Hom`-complexes sends the class of a cocycle `f` to the class of
`ψ f`. -/
theorem map_extSuccClass_of_comp_isoExt_hom {X' Y' : C} (P : ProjectiveResolution X)
    (P' : ProjectiveResolution X') (p : ℕ)
    (ψ : P.complex.linearYonedaObj k Y ⟶ P'.complex.linearYonedaObj k Y')
    (m : ((_root_.Ext k C (p + 1)).obj (op X)).obj Y ⟶
      ((_root_.Ext k C (p + 1)).obj (op X')).obj Y')
    (hm : m ≫ (P'.isoExt (p + 1) Y').hom =
      (P.isoExt (p + 1) Y).hom ≫ HomologicalComplex.homologyMap ψ (p + 1))
    (f : P.complex.X (p + 1) ⟶ Y) (hf : P.complex.d (p + 2) (p + 1) ≫ f = 0)
    (hψ : P'.complex.d (p + 2) (p + 1) ≫ ψ.f (p + 1) f = 0) :
    m (extSuccClass k P Y p f hf) = extSuccClass k P' Y' p (ψ.f (p + 1) f) hψ := by
  let K := P.complex.linearYonedaObj k Y
  let K' := P'.complex.linearYonedaObj k Y'
  have hsq : (extSuccIsoHomology k P Y p).inv ≫ m ≫ (extSuccIsoHomology k P' Y' p).hom =
      (K.sc' p (p + 1) (p + 2)).moduleCatHomologyIso.inv ≫
        ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor' _ _ p (p + 1) (p + 2)).map ψ) ≫
        (K'.sc' p (p + 1) (p + 2)).moduleCatHomologyIso.hom := by
    simp only [extSuccIsoHomology, Iso.trans_inv, Iso.trans_hom, Category.assoc]
    rw [reassoc_of% hm, Iso.inv_hom_id_assoc,
      reassoc_of% (HomologicalComplex.homologyMap_comp_homologyIsoSc'_hom ψ
        p (p + 1) (p + 2) (by simp) (by simp)), Iso.inv_hom_id_assoc]
  apply (extSuccIsoHomology k P' Y' p).toLinearEquiv.injective
  have := congrArg (fun h => h (Submodule.Quotient.mk ⟨f, hf⟩)) hsq
  simp only at this
  refine this.trans ?_
  refine (ShortComplex.moduleCatHomologyIso_hom_homologyMap_inv_mk _ _).trans ?_
  exact (Iso.inv_hom_id_apply (extSuccIsoHomology k P' Y' p) _).symm

omit [HasExt C] in
/-- The map induced by `g : X' ⟶ X` on the derived-functor `Extᵖ⁺¹(-, Y)` sends the class of a
cocycle `f` of `Hom(P, Y)` to the class of `φ ≫ f`, for any chain map `φ : P' ⟶ P` lying over
`g`. -/
theorem Ext_map_extSuccClass {X' : C} (g : X' ⟶ X) (P : ProjectiveResolution X)
    (P' : ProjectiveResolution X') (φ : P'.complex ⟶ P.complex)
    (comm : φ.f 0 ≫ P.π.f 0 = P'.π.f 0 ≫ g) (Y : C) (p : ℕ)
    (f : P.complex.X (p + 1) ⟶ Y) (hf : P.complex.d (p + 2) (p + 1) ≫ f = 0) :
    ((_root_.Ext k C (p + 1)).map g.op).app Y (extSuccClass k P Y p f hf) =
      extSuccClass k P' Y p (φ.f (p + 1) ≫ f)
        (by rw [← Category.assoc, ← φ.comm, Category.assoc, hf, Limits.comp_zero]) :=
  map_extSuccClass_of_comp_isoExt_hom P P' p _ _
    (Ext_map_comp_isoExt_hom (k := k) g P P' φ comm (p + 1) Y) f hf _

/-- **The comparison of the two `Ext`s is natural in the first argument.** For `g : X' ⟶ X`, the
map induced by `g` on the derived-functor `Extᵖ⁺¹(-, Y)` becomes the Yoneda product with
`Ext.mk₀ g` on the derived-category `Ext`. -/
theorem extSuccLinearEquiv_Ext_map {X' : C} (g : X' ⟶ X) (P : ProjectiveResolution X)
    (P' : ProjectiveResolution X') (Y : C) (p : ℕ)
    (α : ((_root_.Ext k C (p + 1)).obj (op X)).obj Y) :
    extSuccLinearEquiv.{w} k P' Y p (((_root_.Ext k C (p + 1)).map g.op).app Y α) =
      (Ext.mk₀ g).comp (extSuccLinearEquiv.{w} k P Y p α) (zero_add _) := by
  let φ : ProjectiveResolution.Hom P' P g :=
    ⟨ProjectiveResolution.lift g P' P,
      by simpa using ProjectiveResolution.lift_commutes_zero g P' P⟩
  obtain ⟨f, hf, rfl⟩ := extSuccClass_surjective P Y p α
  rw [Ext_map_extSuccClass g P P' φ.hom (ProjectiveResolution.lift_commutes_zero g P' P),
    extSuccLinearEquiv_extSuccClass, extSuccLinearEquiv_extSuccClass,
    ProjectiveResolution.mk₀_comp_extMk f (p + 2) rfl hf φ]

omit [HasExt C] in
/-- **`isoExt` is natural in the second argument.** Computing `Extⁿ(X, -)` from a projective
resolution `P` of `X` turns the map induced by `f : Y ⟶ Y'` into postcomposition with `f` on the
`Hom`-complexes. -/
theorem Ext_obj_map_comp_isoExt_hom (P : ProjectiveResolution X) {Y' : C} (f : Y ⟶ Y') (n : ℕ) :
    ((_root_.Ext k C n).obj (op X)).map f ≫ (P.isoExt n Y').hom =
      (P.isoExt n Y).hom ≫ HomologicalComplex.homologyMap
        ((HomologicalComplex.unopFunctor _ _).map ((NatTrans.mapHomologicalComplex
          ((linearYoneda k C).map f).rightOp _).app P.complex).op) n := by
  let α := ((linearYoneda k C).map f).rightOp
  have h := ProjectiveResolution.leftDerived_app_eq α P n
  have hu : ((_root_.Ext k C n).obj (op X)).map f =
      (P.isoLeftDerivedObj ((linearYoneda k C).obj Y).rightOp n).inv.unop ≫
        (HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α _).app P.complex)
          n).unop ≫
        (P.isoLeftDerivedObj ((linearYoneda k C).obj Y').rightOp n).hom.unop := by
    -- by definition of `Ext`, its second-argument maps are left-derived natural transformations
    change ((NatTrans.leftDerived α n).app X).unop = _
    rw [h]
    rfl
  have hn := TauCeti.HomologicalComplex.homologyUnop_inv_naturality
    ((NatTrans.mapHomologicalComplex α _).app P.complex) n
  -- unfold `isoExt` into its two constituents
  change _ ≫ (P.isoLeftDerivedObj ((linearYoneda k C).obj Y').rightOp n).inv.unop ≫
      (HomologicalComplex.homologyUnop _ n).inv =
    ((P.isoLeftDerivedObj ((linearYoneda k C).obj Y).rightOp n).inv.unop ≫
      (HomologicalComplex.homologyUnop _ n).inv) ≫ _
  have e : (P.isoLeftDerivedObj ((linearYoneda k C).obj Y').rightOp n).hom.unop ≫
      (P.isoLeftDerivedObj ((linearYoneda k C).obj Y').rightOp n).inv.unop = 𝟙 _ := by
    rw [← unop_comp, Iso.inv_hom_id, unop_id]
  rw [hu]
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  congr 1
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ hn)
  exact congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) e).trans (Category.id_comp _)))

omit [HasExt C] in
/-- The map induced by `f : Y ⟶ Y'` on the derived-functor `Extᵖ⁺¹(X, -)` sends the class of a
cocycle `g` of `Hom(P, Y)` to the class of `g ≫ f`. -/
theorem Ext_obj_map_extSuccClass (P : ProjectiveResolution X) {Y' : C} (f : Y ⟶ Y') (p : ℕ)
    (g : P.complex.X (p + 1) ⟶ Y) (hg : P.complex.d (p + 2) (p + 1) ≫ g = 0) :
    ((_root_.Ext k C (p + 1)).obj (op X)).map f (extSuccClass k P Y p g hg) =
      extSuccClass k P Y' p (g ≫ f) (by rw [← Category.assoc, hg, Limits.zero_comp]) :=
  map_extSuccClass_of_comp_isoExt_hom P P p _ _ (Ext_obj_map_comp_isoExt_hom P f (p + 1)) g hg _

/-- **The comparison of the two `Ext`s is natural in the second argument.** For `f : Y ⟶ Y'`, the
map induced by `f` on the derived-functor `Extᵖ⁺¹(X, -)` becomes the Yoneda product with
`Ext.mk₀ f` on the derived-category `Ext`. -/
theorem extSuccLinearEquiv_Ext_obj_map (P : ProjectiveResolution X) {Y' : C} (f : Y ⟶ Y')
    (p : ℕ) (α : ((_root_.Ext k C (p + 1)).obj (op X)).obj Y) :
    extSuccLinearEquiv.{w} k P Y' p (((_root_.Ext k C (p + 1)).obj (op X)).map f α) =
      (extSuccLinearEquiv.{w} k P Y p α).comp (Ext.mk₀ f) (add_zero _) := by
  obtain ⟨g, hg, rfl⟩ := extSuccClass_surjective P Y p α
  rw [Ext_obj_map_extSuccClass, extSuccLinearEquiv_extSuccClass, extSuccLinearEquiv_extSuccClass,
    ProjectiveResolution.extMk_comp_mk₀]

end TauCeti
