/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import TauCeti.Algebra.Homology.LocalCohomology.Exact
import TauCeti.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Local cohomology as derived power torsion

For an ideal `I` of a commutative ring `A`, the `I`-power torsion of an `A`-module `M` is the
submodule `Γ_I(M)` of elements killed by some power of `I`, and `M ↦ Γ_I(M)` is an additive
functor `TauCeti.Supports.powerTorsionFunctor I`. Mathlib's `localCohomology I q` is the colimit
over `k` of `Ext^q_A(A ⧸ Iᵏ, -)`. This file proves that `Γ_I` is left exact and that, in every
degree, `H^q_I` is naturally isomorphic to the right-derived functor `R^qΓ_I` (Stacks, Lemma
47.8.2 (0954)). In degree zero both are `Γ_I`, by `TauCeti.Supports.localCohomology_degreeZero`.

The proof follows Stacks. Fix an injective resolution `M → J•`. A class in
`Ext^{p+1}(A ⧸ Iᵏ, M)` is represented by a cocycle `f : A ⧸ Iᵏ ⟶ J^{p+1}`
(`CategoryTheory.InjectiveResolution.extMk`), and `f ↦ f(1)` sends it to a cocycle of the complex
`Γ_I(J•)`. These maps are compatible with the transition maps of the system, so they induce a map
from the colimit to `H^{p+1}(Γ_I(J•))`. It is surjective because every element of `Γ_I(J^{p+1})` is
killed by some `Iᵏ`, and injective because a coboundary `f(1) = d(z)` with `z ∈ Γ_I(Jᵖ)` becomes a
coboundary of `Hom(A ⧸ Iᵐ, J•)` once `Iᵐ` kills `z`. No finiteness hypothesis on `A`, `I` or `M`
is needed.

## Main definitions

* `TauCeti.Supports.powerTorsion I M`: the `I`-power torsion submodule of `M`.
* `TauCeti.Supports.powerTorsionFunctor I`: the functor `Γ_I` on `A`-modules.
* `TauCeti.Supports.localCohomologyZeroLinearEquiv I M`: `H⁰_I(M) ≃ₗ[A] Γ_I(M)`.
* `TauCeti.Supports.localCohomologySuccLinearEquivHomology I R p`: for an injective resolution
  `R` of `M`, `H^{p+1}_I(M)` is the explicit cohomology `ker ⧸ im` of `Γ_I(R)` in degree `p + 1`.
* `TauCeti.Supports.torsionHomologyMap φ`: the map on that cohomology induced by a morphism `φ` of
  injective resolutions.
* `TauCeti.Supports.torsionHomologyIsoRightDerived I R p`: that cohomology is `R^{p+1}Γ_I(M)`.
* `TauCeti.Supports.localCohomologySuccLinearEquiv I p M`:
  `H^{p+1}_I(M) ≃ₗ[A] R^{p+1}Γ_I(M)`.
* `TauCeti.Supports.localCohomologySuccIsoRightDerived I p`: the natural isomorphism
  `H^{p+1}_I ≅ R^{p+1}Γ_I` of functors on `A`-modules.
* `TauCeti.Supports.localCohomologyIsoRightDerived I q`: the natural isomorphism
  `H^q_I ≅ R^qΓ_I` in every degree.

## Main results

* `TauCeti.Supports.mem_powerTorsion_iff`: `m ∈ Γ_I(M)` iff some power of `I` kills `m`.
* The instance `PreservesFiniteLimits (powerTorsionFunctor I)`: `Γ_I` is left exact.
* `TauCeti.Supports.localCohomologySuccLinearEquivHomology_ι_extMk`: the comparison sends the
  class of a cocycle `f : A ⧸ Iᵏ ⟶ J^{p+1}` to the class of `f(1)`.
* `TauCeti.Supports.localCohomologyZeroLinearEquiv_naturality`,
  `TauCeti.Supports.localCohomologySuccLinearEquivHomology_naturality` and
  `TauCeti.Supports.localCohomologySuccLinearEquiv_naturality`: the comparison is natural in `M`.

## References

* [Stacks, Lemma 47.8.2 (0954)](https://stacks.math.columbia.edu/tag/0954).
-/

public section

universe u

open CategoryTheory CategoryTheory.Abelian Limits Opposite

namespace TauCeti.Supports

variable {A : Type u} [CommRing A] (I : Ideal A)

section PowerTorsion

variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- The `I`-power torsion `Γ_I(M)` of `M`: the elements killed by some power of `I`. -/
def powerTorsion (M : Type*) [AddCommGroup M] [Module A M] : Submodule A M :=
  ⨆ n : ℕ, Submodule.torsionBySet A M ↑(I ^ n)

variable {I} in
theorem mem_powerTorsion_iff {m : M} : m ∈ powerTorsion I M ↔ ∃ n : ℕ, ∀ a ∈ I ^ n, a • m = 0 := by
  rw [powerTorsion, Submodule.mem_iSup_of_directed _
    (Monotone.directed_le fun i j h => Submodule.torsionBySet_le_torsionBySet_pow i j h I)]
  simp only [Submodule.mem_torsionBySet_iff, Subtype.forall, SetLike.mem_coe]

variable {I} in
/-- Linear maps preserve `I`-power torsion. -/
theorem map_mem_powerTorsion (f : M →ₗ[A] N) {m : M} (hm : m ∈ powerTorsion I M) :
    f m ∈ powerTorsion I N := by
  obtain ⟨n, hn⟩ := mem_powerTorsion_iff.1 hm
  exact mem_powerTorsion_iff.2 ⟨n, fun a ha => by rw [← map_smul, hn a ha, map_zero]⟩

/-- The `I`-power-torsion functor `Γ_I` on `A`-modules. -/
@[expose] noncomputable def powerTorsionFunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} A where
  obj M := ModuleCat.of A (powerTorsion I M)
  map f := ModuleCat.ofHom (f.hom.restrict fun _ => map_mem_powerTorsion f.hom)

theorem powerTorsionFunctor_obj (M : ModuleCat.{u} A) :
    (powerTorsionFunctor I).obj M = ModuleCat.of A (powerTorsion I M) :=
  rfl

@[simp]
theorem coe_powerTorsionFunctor_map_apply {M M' : ModuleCat.{u} A} (f : M ⟶ M')
    (m : (powerTorsionFunctor I).obj M) :
    (((powerTorsionFunctor I).map f).hom m).1 = f.hom m.1 :=
  rfl

instance : (powerTorsionFunctor I).Additive where
  map_add := rfl

/-- `Γ_I` is left exact. -/
instance : PreservesFiniteLimits (powerTorsionFunctor I) := by
  refine (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2 fun S hS => ?_
  have hf : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective _).1 hS.mono_f
  refine ⟨(ShortComplex.moduleCat_exact_iff _).2 fun x hx => ?_,
    (ModuleCat.mono_iff_injective _).2 fun x y h => Subtype.ext (hf (congrArg Subtype.val h))⟩
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 hS.exact x.1
    (congrArg Subtype.val hx)
  obtain ⟨n, hn⟩ := mem_powerTorsion_iff.1 x.2
  refine ⟨⟨y, mem_powerTorsion_iff.2 ⟨n, fun a ha => hf ?_⟩⟩, Subtype.ext hy⟩
  rw [map_smul, map_zero, hy, hn a ha]

/-- **Degree zero of local cohomology is power torsion**: evaluation at `1` identifies
`H⁰_I(M)` with `Γ_I(M)`. Stacks, Lemma 47.8.2 (0954). -/
noncomputable def localCohomologyZeroLinearEquiv (M : ModuleCat.{u} A) :
    (localCohomology I 0).obj M ≃ₗ[A] powerTorsion I M :=
  LinearEquiv.ofInjective _ (localCohomologyZeroToModule_injective I M) ≪≫ₗ
    LinearEquiv.ofEq _ _ (SetLike.coe_injective <| (LinearMap.coe_range _).trans <|
      (range_localCohomologyZeroToModule I M).trans (Set.ext fun _ => mem_powerTorsion_iff.symm))

@[simp]
theorem coe_localCohomologyZeroLinearEquiv_apply (M : ModuleCat.{u} A)
    (x : (localCohomology I 0).obj M) :
    (localCohomologyZeroLinearEquiv I M x : M) = (localCohomologyZeroToModule I M).hom x := by
  simp [localCohomologyZeroLinearEquiv]

/-- `localCohomologyZeroLinearEquiv` is natural in `M`. -/
theorem localCohomologyZeroLinearEquiv_naturality {M M' : ModuleCat.{u} A} (g : M ⟶ M')
    (x : (localCohomology I 0).obj M) :
    localCohomologyZeroLinearEquiv I M' (((localCohomology I 0).map g).hom x) =
      ((powerTorsionFunctor I).map g).hom (localCohomologyZeroLinearEquiv I M x) := by
  obtain ⟨j, y, rfl⟩ := TauCeti.ModuleCat.exists_colimit_ι_app_eq _ M x
  have hx := ConcreteCategory.congr_hom (ι_app_localCohomology_map I 0 g j) y
  have h₁ := ConcreteCategory.congr_hom (extZeroIso_hom_naturality_right
    ((localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)).obj j.unop) g) y
  refine Subtype.ext ((coe_localCohomologyZeroLinearEquiv_apply I M' _).trans ?_)
  refine (congrArg (localCohomologyZeroToModule I M').hom hx).trans ?_
  refine (localCohomologyZeroToModule_ι_app I M' j _).trans ?_
  refine (congrArg (fun φ => ModuleCat.Hom.hom φ (Submodule.Quotient.mk 1)) h₁).trans ?_
  exact congrArg g.hom ((localCohomologyZeroToModule_ι_app I M j y).symm.trans
    (coe_localCohomologyZeroLinearEquiv_apply I M _).symm)

end PowerTorsion

section Comparison

variable {M : ModuleCat.{u} A} (R : InjectiveResolution M) (p : ℕ)

/-- The short complex of `Γ_I(R)` in degree `p + 1`. -/
noncomputable abbrev torsionSc : ShortComplex (ModuleCat.{u} A) :=
  (((powerTorsionFunctor I).mapHomologicalComplex _).obj R.cocomplex).sc' p (p + 1) (p + 2)

/-- The explicit cohomology `ker ⧸ im` of `Γ_I(R)` in degree `p + 1`. -/
abbrev TorsionHomology : Type u :=
  LinearMap.ker (torsionSc I R p).g.hom ⧸ LinearMap.range (torsionSc I R p).moduleCatToCycles

variable {I R p}

/-- The value `f(1)` of a cocycle `f : A ⧸ Iᵏ ⟶ R^{p+1}`, as a cycle of `Γ_I(R)`. -/
@[expose] noncomputable def torsionCycle {k : ℕ}
    (f : ModuleCat.of A (A ⧸ I ^ k) ⟶ R.cocomplex.X (p + 1))
    (hf : f ≫ R.cocomplex.d (p + 1) (p + 2) = 0) : LinearMap.ker (torsionSc I R p).g.hom :=
  ⟨⟨f.hom (Submodule.Quotient.mk 1),
      mem_powerTorsion_iff.2 ⟨k, fun _ ha => smul_apply_mk_one_eq_zero f.hom ha⟩⟩,
    LinearMap.mem_ker.2 <| Subtype.ext <|
      congrArg (fun g => g.hom (Submodule.Quotient.mk (1 : A))) hf⟩

@[simp]
theorem coe_coe_torsionCycle {k : ℕ} (f : ModuleCat.of A (A ⧸ I ^ k) ⟶ R.cocomplex.X (p + 1))
    (hf : f ≫ R.cocomplex.d (p + 1) (p + 2) = 0) :
    (torsionCycle f hf).1.1 =
      f.hom (Submodule.Quotient.mk 1) :=
  rfl

/-- The class of `f(1)` vanishes exactly when `f(1) = d(z)` for some `z ∈ Γ_I(Rᵖ)`. -/
theorem mk_torsionCycle_eq_zero_iff {k : ℕ}
    (f : ModuleCat.of A (A ⧸ I ^ k) ⟶ R.cocomplex.X (p + 1))
    (hf : f ≫ R.cocomplex.d (p + 1) (p + 2) = 0) :
    (Submodule.Quotient.mk (torsionCycle f hf) : TorsionHomology I R p) = 0 ↔
      ∃ z ∈ powerTorsion I (R.cocomplex.X p),
        (R.cocomplex.d p (p + 1)).hom z = f.hom (Submodule.Quotient.mk 1) := by
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z.1, z.2, congrArg (fun w : LinearMap.ker (torsionSc I R p).g.hom => w.1.1) hz⟩
  · rintro ⟨z, hz, h⟩
    exact ⟨⟨z, hz⟩, Subtype.ext (Subtype.ext h)⟩

variable (I R p)

/-- The cocycles `A ⧸ Iᵏ ⟶ R^{p+1}`. -/
noncomputable abbrev quotientCocycles (k : ℕ) :
    Submodule A (ModuleCat.of A (A ⧸ I ^ k) ⟶ R.cocomplex.X (p + 1)) :=
  LinearMap.ker (Linear.rightComp A _ (R.cocomplex.d (p + 1) (p + 2)))

/-- The class in the derived-category `Ext^{p+1}(A ⧸ Iᵏ, M)` of a cocycle. -/
noncomputable def quotientCocyclesToExt (k : ℕ) :
    quotientCocycles I R p k →ₗ[A] Ext (ModuleCat.of A (A ⧸ I ^ k)) M (p + 1) where
  toFun f := R.extMk f.1 (p + 2) rfl (LinearMap.mem_ker.1 f.2)
  map_add' f g := (R.add_extMk f.1 g.1 _ rfl _ _).symm
  map_smul' c f := (R.smul_extMk c f.1 _ rfl _).symm

/-- The class in `H^{p+1}(Γ_I(R))` of the value at `1` of a cocycle. -/
noncomputable def quotientCocyclesToHomology (k : ℕ) :
    quotientCocycles I R p k →ₗ[A] TorsionHomology I R p :=
  (LinearMap.range (torsionSc I R p).moduleCatToCycles).mkQ ∘ₗ
    { toFun f := torsionCycle f.1 (LinearMap.mem_ker.1 f.2)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

theorem quotientCocyclesToExt_surjective (k : ℕ) :
    Function.Surjective (quotientCocyclesToExt I R p k) := by
  intro α
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective α (p + 2) rfl
  exact ⟨⟨f, LinearMap.mem_ker.2 hf⟩, rfl⟩

theorem ker_quotientCocyclesToExt_le (k : ℕ) :
    LinearMap.ker (quotientCocyclesToExt I R p k) ≤
      LinearMap.ker (quotientCocyclesToHomology I R p k) := by
  intro f hf
  obtain ⟨g, hg⟩ :=
    (R.extMk_eq_zero_iff f.1 (p + 2) rfl (LinearMap.mem_ker.1 f.2) p rfl).1 (LinearMap.mem_ker.1 hf)
  refine LinearMap.mem_ker.2 ((mk_torsionCycle_eq_zero_iff f.1 (LinearMap.mem_ker.1 f.2)).2
    ⟨g.hom (Submodule.Quotient.mk 1), mem_powerTorsion_iff.2
      ⟨k, fun _ ha => smul_apply_mk_one_eq_zero g.hom ha⟩, ?_⟩)
  rw [← hg]
  rfl

/-- The stage map `Ext^{p+1}(A ⧸ Iᵏ, M) → H^{p+1}(Γ_I(R))`, `[f] ↦ [f(1)]`, on the
derived-category `Ext`. -/
noncomputable def extToTorsionHomology (k : ℕ) :
    Ext (ModuleCat.of A (A ⧸ I ^ k)) M (p + 1) →ₗ[A] TorsionHomology I R p :=
  (LinearMap.ker (quotientCocyclesToExt I R p k)).liftQ _ (ker_quotientCocyclesToExt_le I R p k) ∘ₗ
    (LinearMap.quotKerEquivOfSurjective _
      (quotientCocyclesToExt_surjective I R p k)).symm.toLinearMap

variable {I R p}

theorem extToTorsionHomology_extMk {k : ℕ}
    (f : ModuleCat.of A (A ⧸ I ^ k) ⟶ R.cocomplex.X (p + 1))
    (hf : f ≫ R.cocomplex.d (p + 1) (p + 2) = 0) :
    extToTorsionHomology I R p k (R.extMk f (p + 2) rfl hf) =
      Submodule.Quotient.mk (torsionCycle f hf) := by
  have : (LinearMap.quotKerEquivOfSurjective _
      (quotientCocyclesToExt_surjective I R p k)).symm (R.extMk f (p + 2) rfl hf) =
        Submodule.Quotient.mk ⟨f, LinearMap.mem_ker.2 hf⟩ :=
    (LinearEquiv.symm_apply_eq _).2 rfl
  simp only [extToTorsionHomology, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    this, Submodule.liftQ_apply]
  rfl

theorem extToTorsionHomology_comp {k m : ℕ} (h : I ^ m ≤ I ^ k)
    (α : Ext (ModuleCat.of A (A ⧸ I ^ k)) M (p + 1)) :
    extToTorsionHomology I R p m
        ((Ext.mk₀ (ModuleCat.ofHom (Submodule.mapQ (I ^ m) (I ^ k) LinearMap.id h))).comp α
          (zero_add _)) =
      extToTorsionHomology I R p k α := by
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective α (p + 2) rfl
  rw [R.mk₀_comp_extMk, extToTorsionHomology_extMk, extToTorsionHomology_extMk]
  rfl

variable (I R p)

/-- The stage maps `extToTorsionHomology`, on the derived-functor `Ext` of `localCohomology`, as a
cocone on the system computing `H^{p+1}_I(M)`. -/
@[expose] noncomputable def torsionHomologyCocone :
    Cocone (localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1) ⋙
      (evaluation _ _).obj M) where
  pt := ModuleCat.of A (TorsionHomology I R p)
  ι :=
    { app := fun j => ModuleCat.ofHom (extToTorsionHomology I R p j.unop.unop ∘ₗ
        (extLinearEquiv _ M (p + 1)).toLinearMap)
      naturality := fun j j' w => by
        ext y
        refine (congrArg (extToTorsionHomology I R p _)
          (extLinearEquiv_Ext_map _ _ M (p + 1) y)).trans ?_
        exact extToTorsionHomology_comp _ _ }

theorem torsionHomologyCocone_ι_app_apply (j : (ℕᵒᵖ)ᵒᵖ)
    (y : ((localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1) ⋙
      (evaluation _ _).obj M).obj j)) :
    ((torsionHomologyCocone I R p).ι.app j).hom y =
      extToTorsionHomology I R p j.unop.unop (extLinearEquiv _ M (p + 1) y) :=
  rfl

/-- **Local cohomology computes derived power torsion, at the level of an injective
resolution.** For an injective resolution `R` of `M`, `H^{p+1}_I(M)` is the cohomology of
`Γ_I(R)` in degree `p + 1`: the class of a cocycle `f : A ⧸ Iᵏ ⟶ R^{p+1}` goes to the class of
`f(1)`. Stacks, Lemma 47.8.2 (0954). -/
noncomputable def localCohomologySuccLinearEquivHomology :
    (localCohomology I (p + 1)).obj M ≃ₗ[A] TorsionHomology I R p := by
  let D := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1)
  let F := D ⋙ (evaluation _ _).obj M
  let c := torsionHomologyCocone I R p
  have : PreservesColimit F (forget (ModuleCat.{u} A)) :=
    have := preservesFilteredColimitsOfSize_shrink.{0, u, 0, u} (forget (ModuleCat.{u} A))
    inferInstance
  have hι (j : (ℕᵒᵖ)ᵒᵖ) (y : F.obj j) : (colimit.desc F c).hom ((colimit.ι F j).hom y) =
      extToTorsionHomology I R p j.unop.unop (extLinearEquiv _ M (p + 1) y) := by
    rw [← ModuleCat.comp_apply, colimit.ι_desc]
    rfl
  refine (colimitObjIsoColimitCompEvaluation D M).toLinearEquiv ≪≫ₗ
    LinearEquiv.ofBijective (colimit.desc F c).hom ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨j, y, rfl⟩ := Concrete.colimit_exists_rep F x
    obtain ⟨f, hf, hfy⟩ := R.extMk_surjective (X := ModuleCat.of A (A ⧸ I ^ j.unop.unop))
      (extLinearEquiv _ M (p + 1) y) (p + 2) rfl
    have hx' : (Submodule.Quotient.mk (torsionCycle f hf) : TorsionHomology I R p) = 0 := by
      rw [← extToTorsionHomology_extMk, hfy]
      exact (hι j y).symm.trans hx
    obtain ⟨z, hz, hdz⟩ := (mk_torsionCycle_eq_zero_iff f hf).1 hx'
    obtain ⟨n, hn⟩ := mem_powerTorsion_iff.1 hz
    let k := j.unop.unop
    have hm : I ^ max k n ≤ I ^ k := Ideal.pow_le_pow_right (le_max_left k n)
    let w : j ⟶ op (op (max k n)) := (homOfLE (le_max_left k n)).op.op
    have hy : (F.map w).hom y = 0 := by
      refine (extLinearEquiv (ModuleCat.of A (A ⧸ I ^ max k n)) M (p + 1)).injective ?_
      refine ((extLinearEquiv_Ext_map (ModuleCat.of A (A ⧸ I ^ k))
        (ModuleCat.ofHom (Submodule.mapQ _ _ LinearMap.id hm)) M (p + 1) y).trans ?_).trans
          (map_zero _).symm
      rw [← hfy, R.mk₀_comp_extMk]
      refine (R.extMk_eq_zero_iff _ (p + 2) rfl _ p rfl).2
        ⟨ModuleCat.ofHom ((I ^ max k n).liftQ (LinearMap.toSpanSingleton A _ z) fun a ha =>
          hn a (Ideal.pow_le_pow_right (le_max_right k n) ha)), ?_⟩
      refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext_ring ?_))
      exact (congrArg (R.cocomplex.d p (p + 1)).hom (one_smul A z)).trans hdz
    rw [← colimit.w F w, ModuleCat.comp_apply, hy, map_zero]
  · intro q
    obtain ⟨⟨⟨z, hz⟩, hdz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨k, hk⟩ := mem_powerTorsion_iff.1 hz
    let f : ModuleCat.of A (A ⧸ I ^ k) ⟶ R.cocomplex.X (p + 1) :=
      ModuleCat.ofHom ((I ^ k).liftQ (LinearMap.toSpanSingleton A _ z) fun a ha => hk a ha)
    have hf : f ≫ R.cocomplex.d (p + 1) (p + 2) = 0 := by
      refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext_ring ?_))
      exact (congrArg (R.cocomplex.d (p + 1) (p + 2)).hom (one_smul A z)).trans
        (congrArg (fun w : (torsionSc I R p).X₃ => w.1) (LinearMap.mem_ker.1 hdz))
    refine ⟨colimit.ι F (op (op k)) ((extLinearEquiv (ModuleCat.of A (A ⧸ I ^ k)) M (p + 1)).symm
      (R.extMk f (p + 2) rfl hf)), ?_⟩
    refine (hι _ _).trans ?_
    refine (congrArg (extToTorsionHomology I R p k) (LinearEquiv.apply_symm_apply _ _)).trans ?_
    refine (extToTorsionHomology_extMk f hf).trans ?_
    exact congrArg Submodule.Quotient.mk (Subtype.ext (Subtype.ext (one_smul A z)))

/-- `localCohomologySuccLinearEquivHomology` sends the image of the class of a cocycle
`f : A ⧸ Iᵏ ⟶ R^{p+1}` to the class of `f(1)`. -/
theorem localCohomologySuccLinearEquivHomology_ι_extMk {k : ℕ}
    (f : ModuleCat.of A (A ⧸ I ^ k) ⟶ R.cocomplex.X (p + 1))
    (hf : f ≫ R.cocomplex.d (p + 1) (p + 2) = 0) :
    localCohomologySuccLinearEquivHomology I R p
        (((colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1))
          (op (op k))).app M).hom ((extLinearEquiv (ModuleCat.of A (A ⧸ I ^ k)) M (p + 1)).symm
            (R.extMk f (p + 2) rfl hf))) =
      Submodule.Quotient.mk (torsionCycle f hf) := by
  let D := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1)
  let y := (extLinearEquiv (ModuleCat.of A (A ⧸ I ^ k)) M (p + 1)).symm (R.extMk f (p + 2) rfl hf)
  have h₁ : (colimitObjIsoColimitCompEvaluation D M).hom.hom
      (((colimit.ι D (op (op k))).app M).hom y) =
      (colimit.ι (D ⋙ (evaluation _ _).obj M) (op (op k))).hom y :=
    ConcreteCategory.congr_hom (colimitObjIsoColimitCompEvaluation_ι_app_hom D (op (op k)) M) y
  have h₂ : (colimit.desc _ (torsionHomologyCocone I R p)).hom
      ((colimit.ι (D ⋙ (evaluation _ _).obj M) (op (op k))).hom y) =
        extToTorsionHomology I R p k (R.extMk f (p + 2) rfl hf) :=
    (ConcreteCategory.congr_hom (colimit.ι_desc (torsionHomologyCocone I R p) (op (op k))) y).trans
      (congrArg (extToTorsionHomology I R p k) (LinearEquiv.apply_symm_apply _ _))
  exact ((congrArg _ h₁).trans h₂).trans (extToTorsionHomology_extMk f hf)

variable {I R p}

/-- The map induced on `TorsionHomology` by a morphism `φ` of injective resolutions: the map on
cohomology of `Γ_I(φ)`. -/
noncomputable def torsionHomologyMap {M' : ModuleCat.{u} A} {R' : InjectiveResolution M'}
    {g : M ⟶ M'} (φ : InjectiveResolution.Hom R R' g) :
    TorsionHomology I R p →ₗ[A] TorsionHomology I R' p :=
  ((torsionSc I R p).moduleCatHomologyIso.inv ≫
    ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor' _ _ p (p + 1) (p + 2)).map
      (((powerTorsionFunctor I).mapHomologicalComplex _).map φ.hom)) ≫
    (torsionSc I R' p).moduleCatHomologyIso.hom).hom

/-- `torsionHomologyMap φ` sends the class of `f(1)` to the class of `(f ≫ φ)(1)`. -/
theorem torsionHomologyMap_mk_torsionCycle {M' : ModuleCat.{u} A} {R' : InjectiveResolution M'}
    {g : M ⟶ M'} (φ : InjectiveResolution.Hom R R' g) {k : ℕ}
    (f : ModuleCat.of A (A ⧸ I ^ k) ⟶ R.cocomplex.X (p + 1))
    (hf : f ≫ R.cocomplex.d (p + 1) (p + 2) = 0) :
    torsionHomologyMap φ (Submodule.Quotient.mk (torsionCycle f hf)) =
      Submodule.Quotient.mk (torsionCycle (f ≫ φ.hom.f (p + 1)) (by simp [reassoc_of% hf])) :=
  TauCeti.ShortComplex.moduleCatHomologyIso_hom_homologyMap_inv_mk _ _

/-- **Naturality of `localCohomologySuccLinearEquivHomology`**: along a morphism `φ` of injective
resolutions lying over `g : M ⟶ M'`, the map induced by `g` on local cohomology becomes the map
induced by `Γ_I(φ)` on cohomology. -/
theorem localCohomologySuccLinearEquivHomology_naturality {M' : ModuleCat.{u} A}
    {R' : InjectiveResolution M'} {g : M ⟶ M'} (φ : InjectiveResolution.Hom R R' g)
    (x : (localCohomology I (p + 1)).obj M) :
    localCohomologySuccLinearEquivHomology I R' p (((localCohomology I (p + 1)).map g).hom x) =
      torsionHomologyMap φ (localCohomologySuccLinearEquivHomology I R p x) := by
  obtain ⟨⟨⟨k⟩⟩, y, rfl⟩ := TauCeti.ModuleCat.exists_colimit_ι_app_eq _ M x
  obtain ⟨f, hf, hfy⟩ := R.extMk_surjective (X := ModuleCat.of A (A ⧸ I ^ k))
    (extLinearEquiv _ M (p + 1) y) (p + 2) rfl
  obtain rfl : y = (extLinearEquiv (ModuleCat.of A (A ⧸ I ^ k)) M (p + 1)).symm
      (R.extMk f (p + 2) rfl hf) :=
    (LinearEquiv.symm_apply_apply _ y).symm.trans (congrArg _ hfy.symm)
  have hmap : (((_root_.Ext A (ModuleCat.{u} A) (p + 1)).obj
      (op (ModuleCat.of A (A ⧸ I ^ k)))).map g).hom
        ((extLinearEquiv (ModuleCat.of A (A ⧸ I ^ k)) M (p + 1)).symm (R.extMk f (p + 2) rfl hf)) =
      (extLinearEquiv (ModuleCat.of A (A ⧸ I ^ k)) M' (p + 1)).symm
        (R'.extMk (f ≫ φ.hom.f (p + 1)) (p + 2) rfl (by simp [reassoc_of% hf])) := by
    rw [LinearEquiv.eq_symm_apply]
    refine (extLinearEquiv_Ext_obj_map _ g (p + 1) _).trans ?_
    rw [LinearEquiv.apply_symm_apply]
    exact R.extMk_comp_mk₀ f (p + 2) rfl hf φ
  let D := localCohomology.diagram (localCohomology.idealPowersDiagram I) (p + 1)
  let y := (extLinearEquiv (ModuleCat.of A (A ⧸ I ^ k)) M (p + 1)).symm (R.extMk f (p + 2) rfl hf)
  have hx : ((localCohomology I (p + 1)).map g).hom (((colimit.ι D (op (op k))).app M).hom y) =
      ((colimit.ι D (op (op k))).app M').hom (((D.obj (op (op k))).map g).hom y) :=
    ConcreteCategory.congr_hom (ι_app_localCohomology_map I (p + 1) g (op (op k))) y
  refine (congrArg (localCohomologySuccLinearEquivHomology I R' p)
    (hx.trans (congrArg ((colimit.ι D (op (op k))).app M').hom hmap))).trans ?_
  refine (localCohomologySuccLinearEquivHomology_ι_extMk I R' p _ _).trans ?_
  refine Eq.trans ?_ (congrArg (torsionHomologyMap φ)
    (localCohomologySuccLinearEquivHomology_ι_extMk I R p f hf)).symm
  exact (torsionHomologyMap_mk_torsionCycle φ f hf).symm

variable (I R p)

/-- `TorsionHomology I R p` is `R^{p+1}Γ_I(M)`. -/
noncomputable def torsionHomologyIsoRightDerived :
    ModuleCat.of A (TorsionHomology I R p) ≅ ((powerTorsionFunctor I).rightDerived (p + 1)).obj M :=
  (torsionSc I R p).moduleCatHomologyIso.symm ≪≫
    ((((powerTorsionFunctor I).mapHomologicalComplex _).obj R.cocomplex).homologyIsoSc' p (p + 1)
      (p + 2) (by simp) (by simp)).symm ≪≫
    (R.isoRightDerivedObj (powerTorsionFunctor I) (p + 1)).symm

variable {I R p} in
/-- `torsionHomologyIsoRightDerived` is natural: along a morphism `φ` of injective resolutions
lying over `g`, `torsionHomologyMap φ` becomes the map induced by `g` on `R^{p+1}Γ_I`. -/
theorem torsionHomologyMap_comp_torsionHomologyIsoRightDerived_hom {M' : ModuleCat.{u} A}
    {R' : InjectiveResolution M'} {g : M ⟶ M'} (φ : InjectiveResolution.Hom R R' g) :
    ModuleCat.ofHom (torsionHomologyMap φ) ≫ (torsionHomologyIsoRightDerived I R' p).hom =
      (torsionHomologyIsoRightDerived I R p).hom ≫
        ((powerTorsionFunctor I).rightDerived (p + 1)).map g := by
  let ψ := ((powerTorsionFunctor I).mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom
  have h₁ := TauCeti.HomologicalComplex.homologyMap_comp_homologyIsoSc'_hom ψ p (p + 1) (p + 2)
    (by simp) (by simp)
  have h₂ := InjectiveResolution.isoRightDerivedObj_inv_naturality g R R' φ.hom
    (by simpa using φ.ι_f_zero_comp_hom_f_zero) (powerTorsionFunctor I) (p + 1)
  let T := ((powerTorsionFunctor I).mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
  let T' := ((powerTorsionFunctor I).mapHomologicalComplex (ComplexShape.up ℕ)).obj R'.cocomplex
  have key : ((torsionSc I R p).moduleCatHomologyIso.inv ≫ ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' _ _ p (p + 1) (p + 2)).map ψ) ≫
        (torsionSc I R' p).moduleCatHomologyIso.hom) ≫ (torsionSc I R' p).moduleCatHomologyIso.inv ≫
      (T'.homologyIsoSc' p (p + 1) (p + 2) (by simp) (by simp)).inv ≫
        (R'.isoRightDerivedObj (powerTorsionFunctor I) (p + 1)).inv =
      ((torsionSc I R p).moduleCatHomologyIso.inv ≫
        (T.homologyIsoSc' p (p + 1) (p + 2) (by simp) (by simp)).inv ≫
          (R.isoRightDerivedObj (powerTorsionFunctor I) (p + 1)).inv) ≫
        ((powerTorsionFunctor I).rightDerived (p + 1)).map g := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    refine congrArg ((torsionSc I R p).moduleCatHomologyIso.inv ≫ ·) ?_
    let e := T.homologyIsoSc' p (p + 1) (p + 2) (by simp) (by simp)
    let e' := T'.homologyIsoSc' p (p + 1) (p + 2) (by simp) (by simp)
    have h₃ : ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' _ _ p (p + 1) (p + 2)).map ψ) ≫ e'.inv =
          e.inv ≫ HomologicalComplex.homologyMap ψ (p + 1) := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
      exact h₁.symm
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₃).trans
      ((Category.assoc _ _ _).trans ((congrArg (e.inv ≫ ·) h₂.symm).trans
        (Category.assoc _ _ _).symm)))
  exact key

/-- **Local cohomology computes derived power torsion in positive degrees.** For every
commutative ring `A`, ideal `I` and `A`-module `M`, `H^{p+1}_I(M) = colim_k Ext^{p+1}(A ⧸ Iᵏ, M)`
is `A`-linearly the right-derived functor `R^{p+1}Γ_I(M)` of the `I`-power torsion functor.
Stacks, Lemma 47.8.2 (0954). -/
noncomputable def localCohomologySuccLinearEquiv (M : ModuleCat.{u} A) :
    (localCohomology I (p + 1)).obj M ≃ₗ[A] ((powerTorsionFunctor I).rightDerived (p + 1)).obj M :=
  localCohomologySuccLinearEquivHomology I (injectiveResolution M) p ≪≫ₗ
    (torsionHomologyIsoRightDerived I (injectiveResolution M) p).toLinearEquiv

/-- `localCohomologySuccLinearEquiv` is natural in `M`. -/
theorem localCohomologySuccLinearEquiv_naturality {M M' : ModuleCat.{u} A} (g : M ⟶ M')
    (x : (localCohomology I (p + 1)).obj M) :
    localCohomologySuccLinearEquiv I p M' (((localCohomology I (p + 1)).map g).hom x) =
      (((powerTorsionFunctor I).rightDerived (p + 1)).map g).hom
        (localCohomologySuccLinearEquiv I p M x) := by
  let φ : InjectiveResolution.Hom (injectiveResolution M) (injectiveResolution M') g :=
    ⟨InjectiveResolution.desc g _ _, by simpa using InjectiveResolution.desc_commutes_zero g _ _⟩
  have h := ConcreteCategory.congr_hom
    (torsionHomologyMap_comp_torsionHomologyIsoRightDerived_hom (I := I) (p := p) φ)
    (localCohomologySuccLinearEquivHomology I (injectiveResolution M) p x)
  exact (congrArg (torsionHomologyIsoRightDerived I _ p).hom.hom
    (localCohomologySuccLinearEquivHomology_naturality φ x)).trans h

/-- **Local cohomology computes derived power torsion, naturally, in positive degrees**: the
natural isomorphism `H^{p+1}_I ≅ R^{p+1}Γ_I` of functors on `A`-modules. Stacks, Lemma 47.8.2
(0954). -/
noncomputable def localCohomologySuccIsoRightDerived :
    localCohomology I (p + 1) ≅ (powerTorsionFunctor I).rightDerived (p + 1) :=
  NatIso.ofComponents (fun M => (localCohomologySuccLinearEquiv I p M).toModuleIso) fun g =>
    ModuleCat.hom_ext (LinearMap.ext (localCohomologySuccLinearEquiv_naturality I p g))

/-- **Local cohomology computes derived power torsion.** For every commutative ring `A` and ideal
`I`, the functor `H^q_I = colim_k Ext^q(A ⧸ Iᵏ, -)` on `A`-modules is naturally isomorphic to the
right-derived functor `R^qΓ_I` of the `I`-power torsion functor, in every degree `q`. In degree
zero both are `Γ_I`; in positive degrees this is `localCohomologySuccIsoRightDerived`. Stacks,
Lemma 47.8.2 (0954). -/
noncomputable def localCohomologyIsoRightDerived :
    ∀ q : ℕ, localCohomology I q ≅ (powerTorsionFunctor I).rightDerived q
  | 0 => NatIso.ofComponents (fun M => (localCohomologyZeroLinearEquiv I M).toModuleIso)
      (fun g => ModuleCat.hom_ext
        (LinearMap.ext (localCohomologyZeroLinearEquiv_naturality I g))) ≪≫
        (powerTorsionFunctor I).rightDerivedZeroIsoSelf.symm
  | p + 1 => localCohomologySuccIsoRightDerived I p

end Comparison

end TauCeti.Supports
