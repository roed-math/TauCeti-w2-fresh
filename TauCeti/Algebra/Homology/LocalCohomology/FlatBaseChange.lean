/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import TauCeti.Algebra.Category.ModuleCat.Ext.FlatBaseChange
public import TauCeti.Algebra.Homology.Ext.Basic
public import TauCeti.Algebra.Homology.LocalCohomology.Exact
public import TauCeti.RingTheory.Flat.PowerTorsion
import TauCeti.Algebra.Category.ModuleCat.Ext.Basic
import TauCeti.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Flat base change of local cohomology

Let `A → B` be a flat homomorphism of commutative rings with `A` Noetherian, and `I` an ideal of
`A`. For every `A`-module `M` and every degree `q`, the native local cohomology
`H^q_I(M) = colim_n Ext_A^q(A ⧸ Iⁿ, M)` satisfies

`B ⊗[A] H^q_I(M) ≅ H^q_{IB}(B ⊗[A] M)`

as `B`-modules (Stacks, Lemma 47.10.3 (0BJE)). Extension of scalars is a left adjoint, so it
commutes with the colimit; on the stages, `B ⊗[A] (A ⧸ Iⁿ) = B ⧸ (I B)ⁿ` and
`B ⊗[A] Ext_A^q(A ⧸ Iⁿ, M) = Ext_B^q(B ⧸ (I B)ⁿ, B ⊗[A] M)` is flat base change of `Ext`
(`TauCeti.ModuleCat.extBaseChangeLinearEquiv`), which needs `A ⧸ Iⁿ` finite over the Noetherian
ring `A`. The derived-functor `Ext` of the definition of `localCohomology` is compared with the
derived-category `Ext` by `TauCeti.Supports.extLinearEquiv`.

## Main results

* `TauCeti.Supports.extendScalarsQuotientIso`: `B ⊗[A] (A ⧸ J) ≅ B ⧸ J'` for `J' = J B`,
  natural in the ideals.
* `TauCeti.Supports.extQuotientBaseChangeLinearEquiv`: the stage isomorphism
  `B ⊗[A] Ext_A^q(A ⧸ J, M) ≃ₗ[B] Ext_B^q(B ⧸ J', B ⊗[A] M)`, natural in the ideals
  (`extQuotientBaseChangeLinearEquiv_one_tmul_Ext_map`).
* `TauCeti.Supports.localCohomologyBaseChangeIso`: `B ⊗[A] H^q_I(M) ≅ H^q_{IB}(B ⊗[A] M)`.
* `TauCeti.Supports.localCohomology_flat_baseChange`: the roadmap statement.
* `TauCeti.Supports.exists_pow_smul_localCohomology_eq_zero`: `H^q_I(M)` is `I`-power torsion.
* `TauCeti.Supports.localCohomology_flat_excision`: flat excision (Stacks, Lemma 47.9.7 (0ALZ)):
  if moreover `A ⧸ I → B ⧸ I B` is bijective, then `H^q_I(M) ≅ H^q_{IB}(B ⊗[A] M)` as
  `A`-modules, since `N → B ⊗[A] N` is bijective for `I`-power-torsion `N`.
-/

public section

universe u

open CategoryTheory Abelian Limits TensorProduct
open scoped ChangeOfRings

namespace TauCeti.Supports

open Opposite

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

variable (B) in
/-- Extension of scalars of `A ⧸ J` to `B` is `B ⧸ J'`, for any ideal `J'` equal to `J B`. -/
noncomputable def extendScalarsQuotientIso (J : Ideal A) (J' : Ideal B)
    (h : J.map (algebraMap A B) = J') :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).obj (ModuleCat.of A (A ⧸ J)) ≅
      ModuleCat.of B (B ⧸ J') :=
  ModuleCat.extendScalarsAlgebraMapIso (S := B) _ ≪≫
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J).symm.toLinearEquiv.toModuleIso ≪≫
    (Submodule.quotEquivOfEq _ _ h).toModuleIso

/-- `extendScalarsQuotientIso` sends `1 ⊗ [a]` to `[a]`. -/
@[simp]
lemma extendScalarsQuotientIso_hom_one_tmul (J : Ideal A) (J' : Ideal B)
    (h : J.map (algebraMap A B) = J') (a : A) :
    (extendScalarsQuotientIso B J J' h).hom
        ((1 : B) ⊗ₜ[A, algebraMap A B] (Ideal.Quotient.mk J a)) =
      Ideal.Quotient.mk J' (algebraMap A B a) := by
  have h₁ := ModuleCat.extendScalarsAlgebraMapIso_hom_tmul (S := B)
    (ModuleCat.of A (A ⧸ J)) 1 (Ideal.Quotient.mk J a)
  change Submodule.quotEquivOfEq _ _ h ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J).symm
    ((ModuleCat.extendScalarsAlgebraMapIso (S := B) (ModuleCat.of A (A ⧸ J))).hom
      ((1 : B) ⊗ₜ[A, algebraMap A B] (Ideal.Quotient.mk J a)))) = _
  refine (congrArg (fun y ↦ Submodule.quotEquivOfEq _ _ h
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J).symm y)) h₁).trans ?_
  simp [Algebra.smul_def]
  rfl

/-- `extendScalarsQuotientIso` is natural in the ideals. -/
lemma extendScalars_map_mapQ_comp_extendScalarsQuotientIso {J₁ J₂ : Ideal A} {J₁' J₂' : Ideal B}
    (h₁ : J₁.map (algebraMap A B) = J₁') (h₂ : J₂.map (algebraMap A B) = J₂') (hJ : J₁ ≤ J₂)
    (hJ' : J₁' ≤ J₂') :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).map
        (ModuleCat.ofHom (Submodule.mapQ J₁ J₂ LinearMap.id hJ)) ≫
      (extendScalarsQuotientIso B J₂ J₂' h₂).hom =
    (extendScalarsQuotientIso B J₁ J₁' h₁).hom ≫
      ModuleCat.ofHom (Submodule.mapQ J₁' J₂' LinearMap.id hJ') := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (extendScalarsQuotientIso B J₂ J₂' h₂).hom
      ((1 : B) ⊗ₜ[A, algebraMap A B] (Ideal.Quotient.mk J₂ a)) =
    Submodule.mapQ J₁' J₂' LinearMap.id hJ' ((extendScalarsQuotientIso B J₁ J₁' h₁).hom
      ((1 : B) ⊗ₜ[A, algebraMap A B] (Ideal.Quotient.mk J₁ a)))
  rw [extendScalarsQuotientIso_hom_one_tmul, extendScalarsQuotientIso_hom_one_tmul]
  rfl

variable [IsNoetherianRing A] [Module.Flat A B]

variable (B) in
/-- The stage of flat base change of local cohomology:
`B ⊗[A] Ext_A^q(A ⧸ J, M) ≃ Ext_B^q(B ⧸ J', B ⊗[A] M)` for derived-functor `Ext`, when
`J' = J B`. -/
noncomputable def extQuotientBaseChangeLinearEquiv (J : Ideal A) (J' : Ideal B)
    (h : J.map (algebraMap A B) = J') (M : ModuleCat.{u} A) (q : ℕ) :
    B ⊗[A] ((_root_.Ext A (ModuleCat.{u} A) q).obj (op (ModuleCat.of A (A ⧸ J)))).obj M
      ≃ₗ[B] ((_root_.Ext B (ModuleCat.{u} B) q).obj
        (op (ModuleCat.of B (B ⧸ J')))).obj (ModuleCat.of B (B ⊗[A] M)) :=
  (extLinearEquiv (ModuleCat.of A (A ⧸ J)) M q).baseChange A B _ _ ≪≫ₗ
    ModuleCat.extBaseChangeLinearEquiv B (ModuleCat.of A (A ⧸ J)) M q ≪≫ₗ
    extLinearEquivOfIso B (extendScalarsQuotientIso B J J' h)
      (ModuleCat.extendScalarsAlgebraMapIso (S := B) M) q ≪≫ₗ
    (extLinearEquiv (ModuleCat.of B (B ⧸ J')) (ModuleCat.of B (B ⊗[A] M)) q).symm

/-- On `1 ⊗ x`, the stage isomorphism is the image of `x` under extension of scalars,
transported along `B ⊗[A] (A ⧸ J) ≅ B ⧸ J'` and `B ⊗[A] M = B ⊗[A] M`. -/
lemma extLinearEquiv_extQuotientBaseChangeLinearEquiv_one_tmul (J : Ideal A) (J' : Ideal B)
    (h : J.map (algebraMap A B) = J') (M : ModuleCat.{u} A) (q : ℕ) (x) :
    extLinearEquiv _ _ q (extQuotientBaseChangeLinearEquiv B J J' h M q (1 ⊗ₜ x)) =
      (Ext.mk₀ (extendScalarsQuotientIso B J J' h).inv).comp
        (((extLinearEquiv _ M q x).mapExactFunctor
          (ModuleCat.extendScalars.{u, u, u} (algebraMap A B))).comp
          (Ext.mk₀ (ModuleCat.extendScalarsAlgebraMapIso (S := B) M).hom) (add_zero q))
        (zero_add q) := by
  simp [extQuotientBaseChangeLinearEquiv]


/-- The stage isomorphisms of flat base change of local cohomology are natural in the ideals. -/
lemma extQuotientBaseChangeLinearEquiv_one_tmul_Ext_map {J₁ J₂ : Ideal A} {J₁' J₂' : Ideal B}
    (h₁ : J₁.map (algebraMap A B) = J₁') (h₂ : J₂.map (algebraMap A B) = J₂') (hJ : J₁ ≤ J₂)
    (hJ' : J₁' ≤ J₂') (M : ModuleCat.{u} A) (q : ℕ)
    (x : ((_root_.Ext A (ModuleCat.{u} A) q).obj
      (op (ModuleCat.of A (A ⧸ J₂)))).obj M) :
    extQuotientBaseChangeLinearEquiv B J₁ J₁' h₁ M q (1 ⊗ₜ
        (((_root_.Ext A (ModuleCat.{u} A) q).map
          (ModuleCat.ofHom (Submodule.mapQ J₁ J₂ LinearMap.id hJ)).op).app M x)) =
      ((_root_.Ext B (ModuleCat.{u} B) q).map
          (ModuleCat.ofHom (Submodule.mapQ J₁' J₂' LinearMap.id hJ')).op).app
        (ModuleCat.of B (B ⊗[A] M))
        (extQuotientBaseChangeLinearEquiv B J₂ J₂' h₂ M q (1 ⊗ₜ x)) := by
  apply (extLinearEquiv (ModuleCat.of B (B ⧸ J₁')) (ModuleCat.of B (B ⊗[A] M))
    q).injective
  rw [extLinearEquiv_Ext_map, extLinearEquiv_extQuotientBaseChangeLinearEquiv_one_tmul,
    extLinearEquiv_extQuotientBaseChangeLinearEquiv_one_tmul, extLinearEquiv_Ext_map,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc]
  congr 2
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact extendScalars_map_mapQ_comp_extendScalarsQuotientIso h₁ h₂ hJ hJ'


variable (B) in
/-- The diagram `n ↦ Ext_A^q(A ⧸ Iⁿ, M)` defining `H^q_I(M)`, extended to `B`, is the diagram
`n ↦ Ext_B^q(B ⧸ (I B)ⁿ, B ⊗[A] M)` defining `H^q_{IB}(B ⊗[A] M)`. -/
noncomputable def localCohomologyDiagramBaseChangeIso (I : Ideal A) (q : ℕ)
    (M : ModuleCat.{u} A) :
    (localCohomology.diagram (localCohomology.idealPowersDiagram I) q ⋙
        (evaluation _ _).obj M) ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A B) ≅
      localCohomology.diagram (localCohomology.idealPowersDiagram (I.map (algebraMap A B))) q ⋙
        (evaluation _ _).obj (ModuleCat.of B (B ⊗[A] M)) :=
  NatIso.ofComponents (fun j ↦ ModuleCat.extendScalarsAlgebraMapIso (S := B) _ ≪≫
      (extQuotientBaseChangeLinearEquiv B (I ^ unop (unop j))
        (I.map (algebraMap A B) ^ unop (unop j))
        (Ideal.map_pow _ _ _) M q).toModuleIso)
    (fun {j j'} w ↦ by
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      have h₁ := ModuleCat.extendScalarsAlgebraMapIso_hom_tmul (S := B)
        (((_root_.Ext A (ModuleCat.{u} A) q).obj
          (op (ModuleCat.of A (A ⧸ I ^ unop (unop j'))))).obj M) 1
        (((_root_.Ext A (ModuleCat.{u} A) q).map
          (ModuleCat.ofHom (Submodule.mapQ _ _ LinearMap.id
            (Ideal.pow_le_pow_right w.unop.unop.down.down))).op).app M x)
      have h₂ := ModuleCat.extendScalarsAlgebraMapIso_hom_tmul (S := B)
        (((_root_.Ext A (ModuleCat.{u} A) q).obj
          (op (ModuleCat.of A (A ⧸ I ^ unop (unop j))))).obj M) 1 x
      exact (congrArg (extQuotientBaseChangeLinearEquiv B _ _ (Ideal.map_pow _ _ _) M q) h₁).trans
        ((extQuotientBaseChangeLinearEquiv_one_tmul_Ext_map _ _ _
          (Ideal.pow_le_pow_right w.unop.unop.down.down) M q x).trans
          (congrArg (((_root_.Ext B (ModuleCat.{u} B) q).map _).app _)
            (congrArg (extQuotientBaseChangeLinearEquiv B _ _ (Ideal.map_pow _ _ _) M q) h₂).symm)))

variable (B) in
/-- **Flat base change of local cohomology**, as an isomorphism of `B`-modules
`B ⊗[A] H^q_I(M) ≅ H^q_{IB}(B ⊗[A] M)`: extension of scalars commutes with the filtered colimit
defining local cohomology, and on each stage it is `extQuotientBaseChangeLinearEquiv`. -/
noncomputable def localCohomologyBaseChangeIso (I : Ideal A) (q : ℕ) (M : ModuleCat.{u} A) :
    ModuleCat.of B (B ⊗[A] (localCohomology I q).obj M) ≅
      (localCohomology (I.map (algebraMap A B)) q).obj (ModuleCat.of B (B ⊗[A] M)) :=
  (ModuleCat.extendScalarsAlgebraMapIso (S := B) _).symm ≪≫
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapIso
      (colimitObjIsoColimitCompEvaluation _ M) ≪≫
    preservesColimitIso (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) _ ≪≫
    HasColimit.isoOfNatIso (localCohomologyDiagramBaseChangeIso B I q M) ≪≫
    (colimitObjIsoColimitCompEvaluation _ _).symm

/-- **Flat base change of local cohomology** (Stacks, Lemma 47.10.3 (0BJE)): for a flat
homomorphism `A → B` from a Noetherian ring, `B ⊗[A] H^q_I(M) ≅ H^q_{IB}(B ⊗[A] M)` as
`B`-modules, for every `A`-module `M` and every degree `q`. -/
theorem localCohomology_flat_baseChange (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] (I : Ideal A) (M : ModuleCat.{u} A) (q : ℕ) :
    Nonempty ((B ⊗[A] (localCohomology I q).obj M) ≃ₗ[B]
      (localCohomology (I.map (algebraMap A B)) q).obj (ModuleCat.of B (B ⊗[A] M))) :=
  ⟨(localCohomologyBaseChangeIso B I q M).toLinearEquiv⟩

omit [IsNoetherianRing A] in
/-- Every element of `H^q_I(M)` is killed by a power of `I`: the stage `Ext^q(A ⧸ Iⁿ, M)` is
killed by `Iⁿ`, the annihilator of `A ⧸ Iⁿ`. -/
theorem exists_pow_smul_localCohomology_eq_zero (I : Ideal A) (q : ℕ) (M : ModuleCat.{u} A)
    (x : (localCohomology I q).obj M) : ∃ k : ℕ, ∀ r ∈ I ^ k, r • x = 0 := by
  obtain ⟨j, y, rfl⟩ := TauCeti.ModuleCat.exists_colimit_ι_app_eq _ M x
  refine ⟨unop (unop j), fun r hr ↦ ?_⟩
  have hy : r • y = 0 := (extLinearEquiv _ M q).injective (by
    rw [map_smul, map_zero]
    refine Ext.smul_eq_zero_of_mem_annihilator_left ?_ _
    change r ∈ Module.annihilator A (A ⧸ I ^ unop (unop j))
    rwa [Ideal.annihilator_quotient])
  exact (((colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram I) q) j).app
    M).hom.map_smul r y).symm.trans (by rw [hy, map_zero]; rfl)

/-- **Flat excision** for Noetherian local cohomology (Stacks, Lemma 47.9.7 (0ALZ)): if `A → B` is
flat, `A` is Noetherian and `A ⧸ I → B ⧸ I B` is bijective, then `H^q_I(M) ≅ H^q_{IB}(B ⊗[A] M)`
as `A`-modules, for every `A`-module `M` and every degree `q`. -/
theorem localCohomology_flat_excision (I : Ideal A)
    (hI : Function.Bijective (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
      Ideal.le_comap_map))
    (M : ModuleCat.{u} A) (q : ℕ) :
    Nonempty ((localCohomology I q).obj M ≅ (ModuleCat.restrictScalars (algebraMap A B)).obj
      ((localCohomology (I.map (algebraMap A B)) q).obj (ModuleCat.of B (B ⊗[A] M)))) :=
  ⟨(LinearEquiv.ofBijective (TensorProduct.mk A B ((localCohomology I q).obj M) 1)
      (bijective_one_tmul_of_forall_exists_pow_smul_eq_zero hI
        (exists_pow_smul_localCohomology_eq_zero I q M))).toModuleIso ≪≫
    (ModuleCat.restrictScalarsAlgebraMapIso (B ⊗[A] (localCohomology I q).obj M)).symm ≪≫
    (ModuleCat.restrictScalars (algebraMap A B)).mapIso (localCohomologyBaseChangeIso B I q M)⟩

end TauCeti.Supports
