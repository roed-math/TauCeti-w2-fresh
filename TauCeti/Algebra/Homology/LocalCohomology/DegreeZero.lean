/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# Degree zero of local cohomology

For a commutative ring `A`, an ideal `I` and an `A`-module `M`, Mathlib defines
`localCohomology I q` as the colimit over `n` of `Ext^q_A(A/Iⁿ, M)`. In degree zero
`Ext⁰_A(A/Iⁿ, M) = Hom_A(A/Iⁿ, M)` is the submodule of `M` killed by `Iⁿ`, so the colimit is the
`I`-power torsion of `M` (Stacks, Lemma 47.8.2 (0954)). No finiteness hypothesis on `A`, `I` or
`M` is needed.

## Main declarations

* `TauCeti.Supports.extZeroIso`: `Ext⁰(−, M) ≅ Hom(−, M)`, naturally in the first argument.
* `TauCeti.Supports.localCohomologyZeroToModule`: evaluation of a class at `1`,
  `H⁰_I(M) ⟶ M`.
* `TauCeti.Supports.localCohomologyZeroToModule_injective` and
  `TauCeti.Supports.range_localCohomologyZeroToModule`: it is injective with image the
  `I`-power torsion.
* `TauCeti.Supports.localCohomology_degreeZero`: `H⁰_I(M)` is in bijection with the elements of
  `M` killed by a power of `I`.
-/

public section

universe v u

open CategoryTheory Limits

namespace TauCeti.Supports

variable {A : Type u} [CommRing A]

/-- `Hom(−, Y)` is left exact on an `R`-linear category. -/
instance preservesFiniteLimits_linearYoneda_obj {R : Type*} [Ring R] {C : Type*} [Category.{v} C]
    [Preadditive C] [Linear R C] (Y : C) : PreservesFiniteLimits ((linearYoneda R C).obj Y) := by
  have : PreservesFiniteLimits ((linearYoneda R C).obj Y ⋙ forget _) :=
    preservesFiniteLimits_of_natIso (F := yoneda.obj Y) (NatIso.ofComponents fun _ => Iso.refl _)
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget (ModuleCat.{v} R))

/-- `Ext⁰(−, M)` is `Hom(−, M)`, naturally in the first argument. -/
noncomputable def extZeroIso (M : ModuleCat.{u} A) :
    (Ext A (ModuleCat.{u} A) 0).flip.obj M ≅ (linearYoneda A (ModuleCat.{u} A)).obj M :=
  have : PreservesFiniteColimits ((linearYoneda A (ModuleCat.{u} A)).obj M).rightOp :=
    preservesFiniteColimits_rightOp _
  ((Functor.leftOpRightOpEquiv _ _).inverse.mapIso
      ((linearYoneda A (ModuleCat.{u} A)).obj M).rightOp.leftDerivedZeroIsoSelf).unop.symm ≪≫
    Functor.rightOpLeftOpIso _


/-- A linear map out of `A ⧸ J` vanishing on the class of `1` is zero. -/
theorem quotient_linearMap_eq_zero {J : Ideal A} {M : Type*} [AddCommGroup M] [Module A M]
    {φ : (A ⧸ J) →ₗ[A] M} (h : φ (Submodule.Quotient.mk 1) = 0) : φ = 0 :=
  Submodule.linearMap_qext _ (LinearMap.ext_ring (by simpa using h))

/-- The image of the class of `1` under a linear map out of `A ⧸ J` is killed by `J`. -/
theorem smul_apply_mk_one_eq_zero {J : Ideal A} {M : Type*} [AddCommGroup M] [Module A M]
    (φ : (A ⧸ J) →ₗ[A] M) {a : A} (ha : a ∈ J) : a • φ (Submodule.Quotient.mk 1) = 0 := by
  rw [← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
    (Submodule.Quotient.mk_eq_zero _).2 ha, map_zero]

/-- Evaluation at the class of `1`, `Hom(A ⧸ J, M) → M`. -/
@[expose] noncomputable def evalOne (J : Ideal A) (M : ModuleCat.{u} A) :
    ModuleCat.of A (ModuleCat.of A (A ⧸ J) ⟶ M) →ₗ[A] M where
  toFun φ := φ.hom (Submodule.Quotient.mk 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem evalOne_apply (J : Ideal A) (M : ModuleCat.{u} A) (φ : ModuleCat.of A (A ⧸ J) ⟶ M) :
    evalOne J M φ = φ.hom (Submodule.Quotient.mk 1) :=
  rfl

variable (I : Ideal A) (M : ModuleCat.{u} A)

/-- The diagram `n ↦ Hom(A ⧸ Iⁿ, M)` computing `H⁰_I(M)`. -/
noncomputable abbrev homDiagram : (ℕᵒᵖ)ᵒᵖ ⥤ ModuleCat.{u} A :=
  (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)).op ⋙
    (linearYoneda A (ModuleCat.{u} A)).obj M

/-- `H⁰_I(M)` is the colimit of `n ↦ Hom(A ⧸ Iⁿ, M)`. -/
noncomputable def localCohomologyZeroIso :
    (localCohomology I 0).obj M ≅ colimit (homDiagram I M) :=
  colimitObjIsoColimitCompEvaluation _ M ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft _ (extZeroIso M))

/-- Evaluation at `1` as a cocone on `n ↦ Hom(A ⧸ Iⁿ, M)` with point `M`. -/
@[expose] noncomputable def evalOneCocone : Cocone (homDiagram I M) where
  pt := M
  ι :=
    { app n := ModuleCat.ofHom (evalOne _ M)
      naturality _ _ _ := by
        ext φ
        rfl }

/-- Evaluation of a degree-zero local cohomology class at `1`, `H⁰_I(M) ⟶ M`. -/
noncomputable def localCohomologyZeroToModule : (localCohomology I 0).obj M ⟶ M :=
  (localCohomologyZeroIso I M).hom ≫ colimit.desc _ (evalOneCocone I M)

/-- The cocone `evalOneCocone` evaluates a representative at `1`. -/
theorem desc_evalOneCocone_ι_apply (n : (ℕᵒᵖ)ᵒᵖ) (φ : (homDiagram I M).obj n) :
    (colimit.desc _ (evalOneCocone I M)).hom ((colimit.ι (homDiagram I M) n).hom φ) =
      φ.hom (Submodule.Quotient.mk 1) := by
  rw [← ModuleCat.comp_apply, colimit.ι_desc]
  rfl

/-- The forgetful functor preserves the filtered colimit of `n ↦ Hom(A ⧸ Iⁿ, M)`. -/
instance : PreservesColimit (homDiagram I M) (forget (ModuleCat.{u} A)) :=
  have := preservesFilteredColimitsOfSize_shrink.{0, u, 0, u} (forget (ModuleCat.{u} A))
  inferInstance

/-- Evaluation at `1` is injective on the colimit of `n ↦ Hom(A ⧸ Iⁿ, M)`. -/
theorem desc_evalOneCocone_injective :
    Function.Injective (colimit.desc _ (evalOneCocone I M)).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨n, φ, rfl⟩ := Concrete.colimit_exists_rep _ x
  rw [desc_evalOneCocone_ι_apply] at hx
  obtain rfl : φ = 0 := ModuleCat.hom_ext (quotient_linearMap_eq_zero hx)
  exact map_zero _

/-- The image of evaluation at `1` on the colimit is the `I`-power torsion of `M`. -/
theorem range_desc_evalOneCocone :
    Set.range (colimit.desc _ (evalOneCocone I M)).hom =
      {m : M | ∃ n : ℕ, ∀ a ∈ I ^ n, a • m = 0} := by
  ext (m : M)
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨n, φ, rfl⟩ := Concrete.colimit_exists_rep _ x
    refine ⟨n.unop.unop, fun a ha => ?_⟩
    rw [desc_evalOneCocone_ι_apply]
    exact smul_apply_mk_one_eq_zero φ.hom ha
  · rintro ⟨n, hn⟩
    refine ⟨(colimit.ι (homDiagram I M) (.op (.op n))).hom
      (ModuleCat.ofHom ((I ^ n).liftQ (LinearMap.toSpanSingleton A M m) fun a ha => hn a ha)), ?_⟩
    exact (desc_evalOneCocone_ι_apply I M _ _).trans (one_smul A m)

/-- A degree-zero local cohomology class is determined by its value at `1`. -/
theorem localCohomologyZeroToModule_injective :
    Function.Injective (localCohomologyZeroToModule I M).hom :=
  (desc_evalOneCocone_injective I M).comp (localCohomologyZeroIso I M).toLinearEquiv.injective

/-- The values at `1` of degree-zero local cohomology classes are exactly the elements of `M`
killed by a power of `I`. -/
theorem range_localCohomologyZeroToModule :
    Set.range (localCohomologyZeroToModule I M).hom =
      {m : M | ∃ n : ℕ, ∀ a ∈ I ^ n, a • m = 0} := by
  rw [← range_desc_evalOneCocone I M]
  change Set.range
    ((colimit.desc _ (evalOneCocone I M)).hom ∘ (localCohomologyZeroIso I M).hom.hom) = _
  have hs : Function.Surjective (localCohomologyZeroIso I M).hom.hom :=
    (localCohomologyZeroIso I M).toLinearEquiv.surjective
  rw [Set.range_comp, hs.range_eq, Set.image_univ]

/-- Degree zero of the colimit-of-`Ext` local cohomology is the `I`-power torsion, for any
commutative ring. Stacks, Lemma 47.8.2 (0954). -/
theorem localCohomology_degreeZero (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) :
    Nonempty ((localCohomology I 0).obj M ≃
      {m : M // ∃ n : ℕ, ∀ a ∈ I ^ n, a • m = 0}) :=
  ⟨(Equiv.ofInjective _ (localCohomologyZeroToModule_injective I M)).trans
    (Equiv.subtypeEquivRight (Set.ext_iff.1 (range_localCohomologyZeroToModule I M)))⟩

end TauCeti.Supports
