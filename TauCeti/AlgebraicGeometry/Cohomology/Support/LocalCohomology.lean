/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import TauCeti.Algebra.Homology.LocalCohomology.DerivedTorsion
public import TauCeti.AlgebraicGeometry.Cohomology.Support.Tilde
import TauCeti.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Native local cohomology and cohomology with supports

Let `R` be a commutative ring and `I` a finitely generated ideal of `R`. Mathlib's local
cohomology `H^q_I(M)` is the colimit over `k` of `Ext^q_R(R ⧸ Iᵏ, M)`. This file constructs the
comparison map `H^q_I(M) ⟶ H^q_{V(I)}(Spec R, M^~)` to cohomology with supports in `V(I)` (Stacks,
Lemma 51.2.1 (0A6T)).

On the stage `Ext^q_R(R ⧸ Iᵏ, M)`, apply the exact functor `M ↦ M^~` (to abelian sheaves), which
gives `Ext^q((R ⧸ Iᵏ)^~, M^~)`, and take the Yoneda product with the global section `1` of
`(R ⧸ Iᵏ)^~`. This section is killed by `Iᵏ`, so it is supported in `V(I)` and it is a morphism
`ℤ_{Spec R, Spec R ∖ V(I)} ⟶ (R ⧸ Iᵏ)^~` out of the relative free sheaf, whose `Ext` groups are
cohomology with supports. The sections `1` are compatible with the projections
`R ⧸ Iᵏ' ⟶ R ⧸ Iᵏ`, so the stage maps form a cocone and induce the comparison map on the colimit.

The comparison map is natural in `M` and commutes with the connecting maps of short exact sequences
of modules, because `Ext.mapExactFunctor` preserves Yoneda products and extension classes. In
degree zero it is bijective for every finitely generated `I`: a morphism `f : R ⧸ Iᵏ ⟶ M` goes to
the section `f(1)` of `M^~`, and both sides are the `I`-power torsion `Γ_I(M)`.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.Modules.quotientPowOne hI k`: the section `1` of
  `(R ⧸ Iᵏ)^~`, as a morphism out of the relative free sheaf of `Spec R ∖ V(I) ⊆ Spec R`;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.extToCohomologyWithSupport hI k M q`: the stage
  `Ext^q_R(R ⧸ Iᵏ, M) ⟶ H^q_{V(I)}(Spec R, M^~)`;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.localCohomologyToCohomologyWithSupport hI q M`: the
  comparison map `H^q_I(M) ⟶ H^q_{V(I)}(Spec R, M^~)`, computed stage by stage by
  `TauCeti.AlgebraicGeometry.Scheme.Modules.localCohomologyToCohomologyWithSupport_ι_app`;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.localCohomologyToCohomologyWithSupport_naturality` and
  `TauCeti.AlgebraicGeometry.Scheme.Modules.localCohomologyToCohomologyWithSupport_δ`: naturality
  in `M` and compatibility with connecting maps;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.bijective_localCohomologyToCohomologyWithSupport_zero`:
  the comparison map is bijective in degree zero.

## References

* [Stacks, Lemma 51.2.1 (0A6T)](https://stacks.math.columbia.edu/tag/0A6T).
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite _root_.AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace Scheme.Modules

variable {R : CommRingCat.{u}} {I : Ideal R}

/-- The class of `1` lies in the `I`-power torsion of `R ⧸ Iᵏ`. -/
lemma one_mem_primaryComponent_quotient_pow (k : ℕ) :
    (Submodule.Quotient.mk 1 : R ⧸ I ^ k) ∈ I.primaryComponent (R ⧸ I ^ k) :=
  (Ideal.primaryComponent_mem _ _ _).2 ⟨k, (Submodule.mem_torsionBySet_iff _ _).2 fun a ↦ by
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, Submodule.Quotient.mk_eq_zero]
    exact a.2⟩

/-- The global section `1` of `(R ⧸ Iᵏ)^~`, which is supported in `V(I)`, as a morphism
`ℤ_{Spec R, Spec R ∖ V(I)} ⟶ (R ⧸ Iᵏ)^~` out of the relative free sheaf. -/
noncomputable def quotientPowOne (hI : I.FG) (k : ℕ) :
    TauCeti.CategoryTheory.relativeFreeYonedaSheaf (Opens.grothendieckTopology (Spec R))
        ((zeroLocusCloseds I).complInclusion ⊤) ⟶
      (tilde.functor R ⋙ toSheaf (Spec R)).obj (ModuleCat.of R (R ⧸ I ^ k)) :=
  (TauCeti.CategoryTheory.relativeFreeYonedaSheafHomEquiv _ _ _).symm
    ⟨(tilde.isoTop (ModuleCat.of R (R ⧸ I ^ k))).hom (Submodule.Quotient.mk 1),
      AddMonoidHom.mem_ker.2 <| (Sheaf.mem_supportedSections_iff _).1 <|
        (mem_sectionsWithSupport_iff _).1 <|
          (mem_sectionsWithSupport_tilde_iff (M := ModuleCat.of R (R ⧸ I ^ k)) hI _).2 <| by
            rw [Iso.hom_inv_id_apply]
            exact one_mem_primaryComponent_quotient_pow k⟩

/-- The sections `1` of the sheaves `(R ⧸ Iᵏ)^~` are compatible with the projections
`R ⧸ Iᵏ' ⟶ R ⧸ Iᵏ` for `k ≤ k'`. -/
lemma quotientPowOne_comp_map (hI : I.FG) {k k' : ℕ} (h : k ≤ k') :
    quotientPowOne hI k' ≫ (tilde.functor R ⋙ toSheaf (Spec R)).map (ModuleCat.ofHom
        (Submodule.mapQ (I ^ k') (I ^ k) LinearMap.id (Ideal.pow_le_pow_right h))) =
      quotientPowOne hI k := by
  apply (TauCeti.CategoryTheory.relativeFreeYonedaSheafHomEquiv _ _ _).injective
  apply Subtype.ext
  refine (TauCeti.CategoryTheory.relativeFreeYonedaSheafHomEquiv_naturality_right _ _ _ _).trans ?_
  simp only [quotientPowOne, AddEquiv.apply_symm_apply]
  exact congr($(tilde.toOpen_map_app (ModuleCat.ofHom (Submodule.mapQ (I ^ k') (I ^ k)
    LinearMap.id (Ideal.pow_le_pow_right h))) ⊤) (Submodule.Quotient.mk 1))

/-- The stage `Ext^q_R(R ⧸ Iᵏ, M) ⟶ H^q_{V(I)}(Spec R, M^~)` of the comparison of local cohomology
with cohomology with supports: apply `M ↦ M^~` and take the Yoneda product with the section `1` of
`(R ⧸ Iᵏ)^~`. -/
noncomputable def extToCohomologyWithSupport (hI : I.FG) (k : ℕ) (M : ModuleCat.{u} R) (q : ℕ) :
    Abelian.Ext (ModuleCat.of R (R ⧸ I ^ k)) M q →+
      cohomologyWithSupport (zeroLocusCloseds I) (tilde M) q :=
  ((Abelian.Ext.mk₀ (quotientPowOne hI k)).precomp _ (zero_add q)).comp
    ((tilde.functor R ⋙ toSheaf (Spec R)).mapExtAddHom _ _ q)

lemma extToCohomologyWithSupport_apply (hI : I.FG) (k : ℕ) (M : ModuleCat.{u} R) (q : ℕ)
    (x : Abelian.Ext (ModuleCat.of R (R ⧸ I ^ k)) M q) :
    extToCohomologyWithSupport hI k M q x =
      (Abelian.Ext.mk₀ (quotientPowOne hI k)).comp
        (Abelian.Ext.mapExactFunctor (tilde.functor R ⋙ toSheaf (Spec R)) x) (zero_add q) :=
  (rfl)

/-- The stages of the comparison map are compatible with the transition maps
`Ext^q(R ⧸ Iᵏ, M) ⟶ Ext^q(R ⧸ Iᵏ', M)` for `k ≤ k'`. -/
lemma extToCohomologyWithSupport_mk₀_comp (hI : I.FG) {k k' : ℕ} (h : k ≤ k')
    (M : ModuleCat.{u} R) (q : ℕ) (x : Abelian.Ext (ModuleCat.of R (R ⧸ I ^ k)) M q) :
    extToCohomologyWithSupport hI k' M q ((Abelian.Ext.mk₀ (ModuleCat.ofHom
        (Submodule.mapQ (I ^ k') (I ^ k) LinearMap.id (Ideal.pow_le_pow_right h)))).comp x
          (zero_add q)) =
      extToCohomologyWithSupport hI k M q x := by
  rw [extToCohomologyWithSupport_apply, extToCohomologyWithSupport_apply,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    ← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    quotientPowOne_comp_map hI h]

variable (I) in
/-- The system `k ↦ Ext^q_R(R ⧸ Iᵏ, M)` whose colimit is `H^q_I(M)`, as abelian groups. -/
noncomputable abbrev localCohomologyStages (q : ℕ) (M : ModuleCat.{u} R) :
    (ℕᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (localCohomology.diagram (localCohomology.idealPowersDiagram I) q ⋙ (evaluation _ _).obj M) ⋙
    forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

/-- The stages of the comparison map, as a cocone over the system defining `H^q_I(M)`. -/
noncomputable def localCohomologyStagesCocone (hI : I.FG) (q : ℕ) (M : ModuleCat.{u} R) :
    Cocone (localCohomologyStages I q M) where
  pt := AddCommGrpCat.of (cohomologyWithSupport (zeroLocusCloseds I) (tilde M) q)
  ι :=
    { app j := AddCommGrpCat.ofHom ((extToCohomologyWithSupport hI (unop (unop j)) M q).comp
        (Supports.extLinearEquiv (ModuleCat.of R (R ⧸ I ^ unop (unop j))) M q).toAddMonoidHom)
      naturality j j' w := by
        ext x
        exact (congrArg (extToCohomologyWithSupport hI _ M q)
          (Supports.extLinearEquiv_Ext_map _ _ M q x)).trans
            (extToCohomologyWithSupport_mk₀_comp hI w.unop.unop.down.down M q _) }

/-- **The comparison map** `H^q_I(M) ⟶ H^q_{V(I)}(Spec R, M^~)` from native local cohomology to
cohomology with supports, for a finitely generated ideal `I`: on the stage `Ext^q_R(R ⧸ Iᵏ, M)`,
apply `M ↦ M^~` and take the Yoneda product with the section `1` of `(R ⧸ Iᵏ)^~`, which is
supported in `V(I)`. -/
noncomputable def localCohomologyToCohomologyWithSupport (hI : I.FG) (q : ℕ)
    (M : ModuleCat.{u} R) :
    (localCohomology I q).obj M →+ cohomologyWithSupport (zeroLocusCloseds I) (tilde M) q :=
  have := preservesFilteredColimitsOfSize_shrink.{0, u, 0, u}
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  ((isColimitOfPreserves (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
      (colimit.isColimit _)).desc (localCohomologyStagesCocone hI q M)).hom.comp
    (colimitObjIsoColimitCompEvaluation
      (localCohomology.diagram (localCohomology.idealPowersDiagram I) q) M).hom.hom.toAddMonoidHom

/-- The comparison map is computed stage by stage. -/
lemma localCohomologyToCohomologyWithSupport_ι_app (hI : I.FG) (q : ℕ) (M : ModuleCat.{u} R)
    (j : (ℕᵒᵖ)ᵒᵖ)
    (x : ((localCohomology.diagram (localCohomology.idealPowersDiagram I) q).obj j).obj M) :
    localCohomologyToCohomologyWithSupport hI q M
        ((colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram I) q) j).app M
          x) =
      extToCohomologyWithSupport hI _ M q (Supports.extLinearEquiv _ M q x) := by
  have := preservesFilteredColimitsOfSize_shrink.{0, u, 0, u}
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  have h := congr($((isColimitOfPreserves (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    (colimit.isColimit _)).fac (localCohomologyStagesCocone hI q M) j) x)
  refine Eq.trans ?_ h
  change _ = ((isColimitOfPreserves (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    (colimit.isColimit _)).desc (localCohomologyStagesCocone hI q M)).hom
      ((colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram I) q ⋙
        (evaluation _ _).obj M) j).hom x)
  change ((isColimitOfPreserves (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    (colimit.isColimit _)).desc (localCohomologyStagesCocone hI q M)).hom
      ((colimitObjIsoColimitCompEvaluation
        (localCohomology.diagram (localCohomology.idealPowersDiagram I) q) M).hom
          ((colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram I) q) j).app M
            x)) = _
  congr 1
  exact ConcreteCategory.congr_hom (colimitObjIsoColimitCompEvaluation_ι_app_hom
    (localCohomology.diagram (localCohomology.idealPowersDiagram I) q) j M) x

/-- The stages of the comparison map are natural in the module. -/
lemma extToCohomologyWithSupport_comp_mk₀ (hI : I.FG) (k : ℕ) {M M' : ModuleCat.{u} R}
    (f : M ⟶ M') (q : ℕ) (z : Abelian.Ext (ModuleCat.of R (R ⧸ I ^ k)) M q) :
    extToCohomologyWithSupport hI k M' q (z.comp (Abelian.Ext.mk₀ f) (add_zero q)) =
      cohomologyWithSupportMap (zeroLocusCloseds I) (tilde.map f) q
        (extToCohomologyWithSupport hI k M q z) := by
  rw [extToCohomologyWithSupport_apply, extToCohomologyWithSupport_apply,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  exact (Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm.trans
    (cohomologyWithSupportMap_apply _ _ _ _).symm

/-- The stages of the comparison map commute with the connecting maps of a short exact sequence
of modules. -/
lemma extToCohomologyWithSupport_comp_extClass (hI : I.FG) (k : ℕ)
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) (n : ℕ)
    (z : Abelian.Ext (ModuleCat.of R (R ⧸ I ^ k)) S.X₃ n) :
    extToCohomologyWithSupport hI k S.X₁ (n + 1) (z.comp hS.extClass rfl) =
      cohomologyWithSupportTildeδ (zeroLocusCloseds I) hS n
        (extToCohomologyWithSupport hI k S.X₃ n z) := by
  rw [extToCohomologyWithSupport_apply, extToCohomologyWithSupport_apply,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_extClass]
  exact (Abelian.Ext.comp_assoc _ _ _ _ rfl (by lia)).symm.trans
    (cohomologyWithSupportTildeδ_apply _ _ _ _).symm

/-- **Naturality of the comparison map** in the module `M`. -/
lemma localCohomologyToCohomologyWithSupport_naturality (hI : I.FG) (q : ℕ)
    {M M' : ModuleCat.{u} R} (f : M ⟶ M') (x : (localCohomology I q).obj M) :
    localCohomologyToCohomologyWithSupport hI q M' ((localCohomology I q).map f x) =
      cohomologyWithSupportMap (zeroLocusCloseds I) (tilde.map f) q
        (localCohomologyToCohomologyWithSupport hI q M x) := by
  obtain ⟨j, y, rfl⟩ := TauCeti.ModuleCat.exists_colimit_ι_app_eq _ M x
  refine (congrArg (localCohomologyToCohomologyWithSupport hI q M')
    (ConcreteCategory.congr_hom (Supports.ι_app_localCohomology_map I q f j) y)).trans ?_
  refine (localCohomologyToCohomologyWithSupport_ι_app hI q M' j _).trans (Eq.trans ?_
    (congrArg (cohomologyWithSupportMap (zeroLocusCloseds I) (tilde.map f) q)
      (localCohomologyToCohomologyWithSupport_ι_app hI q M j y).symm))
  exact (congrArg (extToCohomologyWithSupport hI _ M' q)
    (Supports.extLinearEquiv_Ext_obj_map _ f q y)).trans
      (extToCohomologyWithSupport_comp_mk₀ hI _ f q _)

/-- **The comparison map commutes with the connecting maps** of a short exact sequence of
modules: the native connecting map `Supports.localCohomologyδ` corresponds to the connecting map
`cohomologyWithSupportTildeδ` of cohomology with supports. -/
lemma localCohomologyToCohomologyWithSupport_δ (hI : I.FG) {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (n : ℕ) (x : (localCohomology I n).obj S.X₃) :
    localCohomologyToCohomologyWithSupport hI (n + 1) S.X₁ (Supports.localCohomologyδ I hS n x) =
      cohomologyWithSupportTildeδ (zeroLocusCloseds I) hS n
        (localCohomologyToCohomologyWithSupport hI n S.X₃ x) := by
  obtain ⟨j, y, rfl⟩ := TauCeti.ModuleCat.exists_colimit_ι_app_eq _ S.X₃ x
  refine (congrArg (localCohomologyToCohomologyWithSupport hI (n + 1) S.X₁)
    (ConcreteCategory.congr_hom (Supports.ι_app_localCohomologyδ I hS n j) y)).trans ?_
  refine (localCohomologyToCohomologyWithSupport_ι_app hI (n + 1) S.X₁ j _).trans (Eq.trans ?_
    (congrArg (cohomologyWithSupportTildeδ (zeroLocusCloseds I) hS n)
      (localCohomologyToCohomologyWithSupport_ι_app hI n S.X₃ j y).symm))
  exact (congrArg (extToCohomologyWithSupport hI _ S.X₁ (n + 1))
    (Supports.extLinearEquiv_extδ _ hS n y)).trans
      (extToCohomologyWithSupport_comp_extClass hI _ hS n _)

/-- In degree zero, the stage of the comparison map sends a morphism `f : R ⧸ Iᵏ ⟶ M` to the
section `f(1)` of `M^~`, which is supported in `V(I)`. -/
lemma coe_cohomologyWithSupportZeroLinearEquiv_extToCohomologyWithSupport_mk₀ (hI : I.FG)
    (k : ℕ) (M : ModuleCat.{u} R) (f : ModuleCat.of R (R ⧸ I ^ k) ⟶ M) :
    (cohomologyWithSupportZeroLinearEquiv (zeroLocusCloseds I) (tilde M)
        (extToCohomologyWithSupport hI k M 0 (Abelian.Ext.mk₀ f)) : Γ(tilde M, ⊤)) =
      (tilde.isoTop M).hom (f (Submodule.Quotient.mk 1)) := by
  rw [extToCohomologyWithSupport_apply, Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
  refine (coe_cohomologyWithSupportZeroLinearEquiv_apply _ _ _).trans
    ((Sheaf.coe_supportedHZeroEquiv_apply _ _ _ _).trans
      ((Sheaf.relativeH'.coe_zeroEquiv_apply _ _ _).trans
        ((TauCeti.CategoryTheory.coe_relativeFreeYonedaSheafHomEquiv_apply _ _ _ _).symm.trans
          ?_)))
  have hh := Abelian.Ext.addEquiv₀.apply_symm_apply
    (quotientPowOne hI k ≫ (tilde.functor R ⋙ toSheaf (Spec R)).map f)
  rw [Abelian.Ext.addEquiv₀_symm_apply] at hh
  refine (congrArg (fun g ↦ (TauCeti.CategoryTheory.relativeFreeYonedaSheafHomEquiv
    (Opens.grothendieckTopology (Spec R)) ((zeroLocusCloseds I).complInclusion ⊤)
      ((tilde.functor R ⋙ toSheaf (Spec R)).obj M) g :
        ((tilde.functor R ⋙ toSheaf (Spec R)).obj M).obj.obj (op ⊤))) hh).trans ?_
  refine (TauCeti.CategoryTheory.relativeFreeYonedaSheafHomEquiv_naturality_right _ _ _ _).trans ?_
  simp only [quotientPowOne, AddEquiv.apply_symm_apply]
  exact congr($(tilde.toOpen_map_app f ⊤) (Submodule.Quotient.mk 1))

/-- In degree zero, the comparison map is, under `H⁰_I(M) ≃ Γ_I(M)` and
`H⁰_{V(I)}(Spec R, M^~) ≃ Γ_{V(I)}(Spec R, M^~)`, the inclusion `Γ_I(M) ⟶ Γ(Spec R, M^~)`. -/
lemma coe_cohomologyWithSupportZeroLinearEquiv_localCohomologyToCohomologyWithSupport
    (hI : I.FG) (M : ModuleCat.{u} R) (x : (localCohomology I 0).obj M) :
    (cohomologyWithSupportZeroLinearEquiv (zeroLocusCloseds I) (tilde M)
        (localCohomologyToCohomologyWithSupport hI 0 M x) : Γ(tilde M, ⊤)) =
      (tilde.isoTop M).hom (Supports.localCohomologyZeroLinearEquiv I M x) := by
  obtain ⟨j, y, rfl⟩ := TauCeti.ModuleCat.exists_colimit_ι_app_eq _ M x
  rw [localCohomologyToCohomologyWithSupport_ι_app]
  refine (congrArg (fun z ↦ (cohomologyWithSupportZeroLinearEquiv (zeroLocusCloseds I) (tilde M)
    (extToCohomologyWithSupport hI _ M 0 z) : Γ(tilde M, ⊤)))
      (Supports.extLinearEquiv_zero_apply _ M y)).trans
    ((coe_cohomologyWithSupportZeroLinearEquiv_extToCohomologyWithSupport_mk₀ hI _ M _).trans ?_)
  refine congrArg (ConcreteCategory.hom (tilde.isoTop M).hom) ?_
  exact ((Supports.coe_localCohomologyZeroLinearEquiv_apply I M _).trans
    (Supports.localCohomologyZeroToModule_ι_app (j := j) (y := y))).symm

/-- **The comparison map is bijective in degree zero**, for every finitely generated ideal: both
sides are the `I`-power torsion `Γ_I(M)`. -/
theorem bijective_localCohomologyToCohomologyWithSupport_zero (hI : I.FG)
    (M : ModuleCat.{u} R) :
    Function.Bijective (localCohomologyToCohomologyWithSupport hI 0 M) := by
  have hbij := ConcreteCategory.bijective_of_isIso (tilde.isoTop M).hom
  let e := cohomologyWithSupportZeroLinearEquiv (zeroLocusCloseds I) (tilde M)
  let e₁ := Supports.localCohomologyZeroLinearEquiv I M
  have key := coe_cohomologyWithSupportZeroLinearEquiv_localCohomologyToCohomologyWithSupport hI M
  suffices h : Function.Bijective (e ∘ localCohomologyToCohomologyWithSupport hI 0 M) by
    simpa using e.symm.bijective.comp h
  refine ⟨fun x x' hx ↦ e₁.injective (Subtype.ext (hbij.1 ?_)), fun s ↦ ?_⟩
  · rw [← key, ← key]
    exact congrArg Subtype.val hx
  · have hs := (mem_sectionsWithSupport_tilde_iff hI s.1).1 s.2
    refine ⟨e₁.symm ⟨_, hs⟩, Subtype.ext ((key _).trans ?_)⟩
    rw [LinearEquiv.apply_symm_apply]
    exact Iso.inv_hom_id_apply _ _

end Scheme.Modules

end AlgebraicGeometry

end TauCeti
