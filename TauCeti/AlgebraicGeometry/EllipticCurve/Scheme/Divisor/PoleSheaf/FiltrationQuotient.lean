/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.LocallyFree
public import TauCeti.AlgebraicGeometry.Cohomology.FlatBaseChange
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Inclusion.Pullback
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.PoleSheaf.Filtration
public import TauCeti.AlgebraicGeometry.Modules.Pullback.UnitSections
public import TauCeti.AlgebraicGeometry.Modules.Sections
public import TauCeti.RingTheory.Flat.Fiber

/-!
# The quotients of the pole filtration over an arbitrary ring

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, and let `0 < m ≤ n`. The
inclusion `𝒪(m[0]) ⟶ 𝒪(n[0])` of pole sheaves (`WeierstrassCurve.poleSheafMap`) is injective on
`H⁰`, between finite projective `R`-modules of ranks `m` and `n`. This file shows that its image is
a direct summand: the quotient `H⁰(𝒪(n[0])) ⧸ H⁰(𝒪(m[0]))` is finite projective of constant rank
`n - m`. In particular the successive quotients of the pole filtration are line bundles over
`Spec R`, and they split Zariski-locally on `R`.

The point is that the inclusion stays injective after **every** change of the coefficient ring
`R → R'` (`WeierstrassCurve.injective_baseChange_cohomologyMapBaseLinear_poleSheafMap`). Pulling
back along `projModel (W.map (algebraMap R R')) ⟶ projModel W` is not left exact, but it carries
the inclusion of pole sheaves to a monomorphism, because the divisors `m[0] ≤ n[0]` are relative
effective Cartier divisors whose base changes are the divisors `m[0] ≤ n[0]` of `W.map`
(`WeierstrassCurve.mono_pullback_map_poleSheafMap_hom`). Its `H⁰` is then injective, and `H⁰` of a
pole sheaf commutes with base change. With `R'` the residue fields of `R`, Nakayama's lemma gives
the projectivity of the quotient (`Module.Projective.quotient_range_of_injective_baseChange`).

The first step `H⁰(𝒪) = H⁰(𝒪(0[0])) ↪ H⁰(𝒪([0]))` is bijective over every ring: every section of
`𝒪([0])` is constant (`WeierstrassCurve.bijective_cohomologyMapBaseLinear_poleSheafMap_zero_one`).
Here `𝒪(0[0])` has degree zero, so the base change of its `H⁰` is not covered by the positive-degree
theorem. It is checked by hand: `H⁰(𝒪(0[0]))` is free on the section corresponding to the function
`1`, whose pullback is the function `1` (`Scheme.Hom.pullbackObjUnitIso_hom_app_pullbackSections`),
so `K ⊗ H⁰(𝒪(0[0])) ⟶ H⁰(g^*𝒪(0[0]))` is injective over every field `K`
(`WeierstrassCurve.injective_cohomologyBaseChange_zero_poleSheaf_zero`). The cokernel then has rank
`1 - 1 = 0`.

## Main results

* `WeierstrassCurve.mono_pullback_map_poleSheafMap_hom`: the inclusion `𝒪(m[0]) ⟶ 𝒪(n[0])` stays
  a monomorphism after any change of the coefficient ring.
* `WeierstrassCurve.injective_baseChange_cohomologyMapBaseLinear_poleSheafMap`: so does the
  inclusion `H⁰(𝒪(m[0])) ⟶ H⁰(𝒪(n[0]))`, for `m > 0`.
* `WeierstrassCurve.projective_quotient_range_cohomologyMapBaseLinear_poleSheafMap` and
  `WeierstrassCurve.rankAtStalk_quotient_range_cohomologyMapBaseLinear_poleSheafMap`: the quotient
  `H⁰(𝒪(n[0])) ⧸ H⁰(𝒪(m[0]))` is projective of rank `n - m`.
* `WeierstrassCurve.bijective_cohomologyMapBaseLinear_poleSheafMap_zero_one`: `H⁰(𝒪) ≅ H⁰(𝒪([0]))`.
* The forms `…_of_mono_pullback` of these statements, for any morphism `𝒪(m[0]) ⟶ 𝒪(n[0])` whose
  pullbacks to the fibres are monomorphisms; they apply to the pole filtration of an elliptic curve
  transported to a chart.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry TauCeti TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] {m n : ℕ}

/-- **The pole filtration commutes with base change**: the pullback of the inclusion
`𝒪(m[0]) ⟶ 𝒪(n[0])` along `projModel (W.map f) ⟶ projModel W` is a monomorphism, for every ring
map `f : R →+* R'`. -/
theorem mono_pullback_map_poleSheafMap_hom {R' : Type u} [CommRing R'] (f : R →+* R')
    (h : m ≤ n) :
    Mono ((Scheme.Modules.pullback (W.projModelBaseChange f)).map (W.poleSheafMap h).hom) := by
  have hm' := ((W.map f).isRelativeEffectiveCartier_zeroSectionDivisor_pow m).isEffectiveCartier
  have hn' := ((W.map f).isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  rw [W.zeroSectionDivisor_pow_map] at hm' hn'
  have := Scheme.IdealSheafData.IsEffectiveCartier.mono_pullback_map_dualMap_hom
    (W.isRelativeEffectiveCartier_zeroSectionDivisor_pow m).isEffectiveCartier
    (W.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier hm' hn'
    (W.zeroSectionDivisor_pow_le_pow h)
  rw [poleSheafMap_def, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.eqToHom_hom, ObjectProperty.eqToHom_hom,
    Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **A map of pole sheaves which stays a monomorphism stays injective on `H⁰`.** Let
`α : 𝒪(m[0]) ⟶ 𝒪(n[0])` be a morphism whose pullback to `projModel (W.map (algebraMap R R'))` is a
monomorphism, and suppose that the base change map `R' ⊗ H⁰(𝒪(m[0])) ⟶ H⁰(g^*𝒪(m[0]))` is injective
(for instance `m > 0`, `WeierstrassCurve.bijective_cohomologyBaseChange_zero_poleSheaf`). Then the
base change `R' ⊗ H⁰(𝒪(m[0])) ⟶ R' ⊗ H⁰(𝒪(n[0]))` of `H⁰(α)` is injective. -/
theorem injective_baseChange_cohomologyMapBaseLinear_of_mono_pullback
    (α : (W.poleSheaf m).obj ⟶ (W.poleSheaf n).obj) (R' : Type u) [CommRing R'] [Algebra R R']
    [Mono ((Scheme.Modules.pullback (W.projModelBaseChange (algebraMap R R'))).map α)]
    (hbc : Function.Injective (cohomologyBaseChange
      (W.isPullback_projModelBaseChange_over (R' := R')) (W.poleSheaf m).obj 0)) :
    Function.Injective ((cohomologyMapBaseLinear R W.projModel α 0).baseChange R') := by
  have H := W.isPullback_projModelBaseChange_over (R' := R')
  have hnat := cohomologyMapBaseLinear_comp_cohomologyBaseChange H α 0
  have hinj : Function.Injective ((cohomologyMapBaseLinear R' _
      ((Scheme.Modules.pullback (W.projModelBaseChange (algebraMap R R'))).map α) 0).comp
        (cohomologyBaseChange H (W.poleSheaf m).obj 0)) := by
    rw [LinearMap.coe_comp, coe_cohomologyMapBaseLinear]
    exact (cohomologyMap_injective _).comp hbc
  rw [hnat, LinearMap.coe_comp] at hinj
  exact hinj.of_comp

/-- **The cokernel of a map of pole sheaves which stays a monomorphism is projective.** Let
`0 < m ≤ n` and let `α : 𝒪(m[0]) ⟶ 𝒪(n[0])` be a morphism whose pullback to the projective model
over every residue field of `R` is a monomorphism. Then the quotient of `H⁰(𝒪(n[0]))` by the image
of `H⁰(𝒪(m[0]))` is projective, so the image is a direct summand. -/
theorem projective_quotient_range_cohomologyMapBaseLinear_of_mono_pullback (hm : 0 < m)
    (h : m ≤ n) (α : (W.poleSheaf m).obj ⟶ (W.poleSheaf n).obj)
    (hα : ∀ (p : Ideal R) [p.IsPrime], Mono ((Scheme.Modules.pullback
      (W.projModelBaseChange (algebraMap R p.ResidueField))).map α)) :
    Module.Projective R (Scheme.Modules.Cohomology (W.poleSheaf n).obj 0 ⧸
      LinearMap.range (cohomologyMapBaseLinear R W.projModel α 0)) := by
  have := W.finitePresentation_cohomology_zero_poleSheaf hm
  have := W.finitePresentation_cohomology_zero_poleSheaf (hm.trans_le h)
  have := W.projective_cohomology_zero_poleSheaf (hm.trans_le h)
  refine Module.Projective.quotient_range_of_injective_baseChange _ fun p _ ↦ ?_
  have := hα p
  exact W.injective_baseChange_cohomologyMapBaseLinear_of_mono_pullback α p.ResidueField
    (W.bijective_cohomologyBaseChange_zero_poleSheaf hm _).1

/-- **The cokernel of a map of pole sheaves which stays a monomorphism has rank `n - m`.** Let
`0 < m ≤ n` and let `α : 𝒪(m[0]) ⟶ 𝒪(n[0])` be a morphism whose pullback to the projective model
over every residue field of `R` is a monomorphism. Then the quotient of `H⁰(𝒪(n[0]))` by the image
of `H⁰(𝒪(m[0]))` has rank `n - m` at every prime. -/
theorem rankAtStalk_quotient_range_cohomologyMapBaseLinear_of_mono_pullback (hm : 0 < m)
    (h : m ≤ n) (α : (W.poleSheaf m).obj ⟶ (W.poleSheaf n).obj)
    (hα : ∀ (p : Ideal R) [p.IsPrime], Mono ((Scheme.Modules.pullback
      (W.projModelBaseChange (algebraMap R p.ResidueField))).map α))
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (Scheme.Modules.Cohomology (W.poleSheaf n).obj 0 ⧸
      LinearMap.range (cohomologyMapBaseLinear R W.projModel α 0)) p = n - m := by
  have := W.finitePresentation_cohomology_zero_poleSheaf hm
  have := W.finitePresentation_cohomology_zero_poleSheaf (hm.trans_le h)
  have := W.projective_cohomology_zero_poleSheaf hm
  have := W.projective_cohomology_zero_poleSheaf (hm.trans_le h)
  have hr := Module.rankAtStalk_quotient_range_add _ (fun q _ ↦ by
    have := hα q
    exact W.injective_baseChange_cohomologyMapBaseLinear_of_mono_pullback α q.ResidueField
      (W.bijective_cohomologyBaseChange_zero_poleSheaf hm _).1) p
  rw [W.rankAtStalk_cohomology_zero_poleSheaf hm,
    W.rankAtStalk_cohomology_zero_poleSheaf (hm.trans_le h)] at hr
  omega

/-- **The pole filtration on `H⁰` stays injective after base change**: for `0 < m ≤ n` and every
`R`-algebra `R'`, the base change `R' ⊗ H⁰(𝒪(m[0])) ⟶ R' ⊗ H⁰(𝒪(n[0]))` of the inclusion is
injective. -/
theorem injective_baseChange_cohomologyMapBaseLinear_poleSheafMap (hm : 0 < m) (h : m ≤ n)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    Function.Injective
      ((cohomologyMapBaseLinear R W.projModel (W.poleSheafMap h).hom 0).baseChange R') :=
  have := W.mono_pullback_map_poleSheafMap_hom (algebraMap R R') h
  W.injective_baseChange_cohomologyMapBaseLinear_of_mono_pullback _ R'
    (W.bijective_cohomologyBaseChange_zero_poleSheaf hm _).1

/-- **The quotients of the pole filtration are projective**: for `0 < m ≤ n`, the quotient of
`H⁰(projModel W, 𝒪(n[0]))` by the image of `H⁰(projModel W, 𝒪(m[0]))` is a projective `R`-module,
so the image is a direct summand. -/
theorem projective_quotient_range_cohomologyMapBaseLinear_poleSheafMap (hm : 0 < m) (h : m ≤ n) :
    Module.Projective R (Scheme.Modules.Cohomology (W.poleSheaf n).obj 0 ⧸
      LinearMap.range (cohomologyMapBaseLinear R W.projModel (W.poleSheafMap h).hom 0)) :=
  W.projective_quotient_range_cohomologyMapBaseLinear_of_mono_pullback hm h _ fun _ _ ↦
    W.mono_pullback_map_poleSheafMap_hom _ h

/-- **The quotients of the pole filtration have rank `n - m`**: for `0 < m ≤ n`, the quotient of
`H⁰(projModel W, 𝒪(n[0]))` by the image of `H⁰(projModel W, 𝒪(m[0]))` has rank `n - m` at every
prime of `R`. -/
theorem rankAtStalk_quotient_range_cohomologyMapBaseLinear_poleSheafMap (hm : 0 < m) (h : m ≤ n)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (Scheme.Modules.Cohomology (W.poleSheaf n).obj 0 ⧸
      LinearMap.range (cohomologyMapBaseLinear R W.projModel (W.poleSheafMap h).hom 0)) p =
        n - m :=
  W.rankAtStalk_quotient_range_cohomologyMapBaseLinear_of_mono_pullback hm h _
    (fun _ _ ↦ W.mono_pullback_map_poleSheafMap_hom _ h) p

/-- `H⁰(𝒪(0[0]))` is free of rank one, on the class `s` of the section corresponding to the function
`1`, and the pullback of `s` to the model over any field `K` receiving `R` is nonzero. -/
private theorem exists_basis_cohomology_poleSheaf_zero :
    ∃ s : Cohomology (W.poleSheaf 0).obj 0, (∀ x, ∃ r : R, x = r • s) ∧
      (∀ r : R, r • s = 0 → r = 0) ∧
      ∀ (K : Type u) [Field K] [Algebra R K],
        (W.projModelBaseChange (algebraMap R K)).cohomologyPullback _ 0 s ≠ 0 := by
  let M := (W.poleSheaf 0).obj
  obtain ⟨e⟩ := (LineBundleClass.mk_eq_one_iff (L := W.poleSheaf 0)).mp
    (by rw [mk_poleSheaf, pow_zero])
  -- The global section `t` of `𝒪(0[0])` corresponding to the function `1`.
  let t := M.presheaf.map (⊤ : W.projModel.Opens).leTop.op (M.unitHomEquivTop e.inv)
  have he (a : Γ(W.projModel, ⊤)) : e.inv.app ⊤ a = a • t := by
    conv_lhs => rw [← M.unitHomEquivTop.symm_apply_apply e.inv]
    exact M.unitHomEquivTop_symm_val_app _ ⊤ a
  have hhom (y : Γ(M, ⊤)) : e.inv.app ⊤ (e.hom.app ⊤ y) = y := by
    simpa only [sectionsLinearEquiv_apply, sectionsLinearEquiv_symm_apply] using
      (sectionsLinearEquiv e ⊤).symm_apply_apply y
  have hinv (y : Γ(𝟙_ W.projModel.Modules, ⊤)) : e.hom.app ⊤ (e.inv.app ⊤ y) = y := by
    simpa only [sectionsLinearEquiv_apply, sectionsLinearEquiv_symm_apply] using
      (sectionsLinearEquiv e ⊤).apply_symm_apply y
  -- The sections of `𝒪_X` are the functions, so `1` is a section of `𝒪_X` over `X`.
  have het : e.hom.app ⊤ t = ((1 : Γ(W.projModel, ⊤)) : Γ(𝟙_ W.projModel.Modules, ⊤)) := by
    rw [← hinv ((1 : Γ(W.projModel, ⊤)) : Γ(𝟙_ W.projModel.Modules, ⊤)), he, one_smul]
  -- Every element of `H⁰(𝒪(0[0]))` is a multiple of the class `s` of `t`.
  let s : Cohomology M 0 := (cohomologyZeroLinearEquiv M).symm t
  have hs (x : Cohomology M 0) : ∃ r : R, x = r • s := by
    obtain ⟨r, hr⟩ := W.bijective_baseRingToGlobalSections.2
      (e.hom.app ⊤ (cohomologyZeroLinearEquiv M x))
    refine ⟨r, (cohomologyZeroLinearEquiv M).injective ?_⟩
    rw [base_smul_cohomology, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, hr]
    exact (hhom _).symm.trans (he _)
  refine ⟨s, hs, fun r hr ↦ ?_, fun K _ _ ↦ ?_⟩
  · -- `r • s` corresponds to the function `r`, which vanishes only for `r = 0`.
    apply W.bijective_baseRingToGlobalSections.1
    have hst : cohomologyZeroLinearEquiv M s = t := LinearEquiv.apply_symm_apply _ _
    have h := congrArg (fun x ↦ e.hom.app ⊤ (cohomologyZeroLinearEquiv M x)) hr
    simp only [base_smul_cohomology, LinearEquiv.map_smul, map_zero, hst] at h
    rw [Hom.app_smul, het] at h
    rw [map_zero]
    exact (mul_one _).symm.trans h
  -- The pullback of `s` is nonzero: it corresponds to the function `1` on the model over `K`.
  set g := W.projModelBaseChange (algebraMap R K)
  intro h0
  have h1 := congrArg (cohomologyZeroEquiv _) h0
  rw [Scheme.Hom.cohomologyZeroEquiv_cohomologyPullback, map_zero,
    ← cohomologyZeroLinearEquiv_apply, LinearEquiv.apply_symm_apply] at h1
  have h2 : (pullbackObjUnitIso g).hom.app (g ⁻¹ᵁ ⊤)
      (((pullback g).map e.hom).app (g ⁻¹ᵁ ⊤) (g.pullbackSections M ⊤ t)) = 0 := by
    -- `g⁻¹ᵁ ⊤` is `⊤` only up to definitional equality, so the zeros are rewritten with `erw`.
    rw [h1]
    erw [map_zero, map_zero]
  rw [g.pullbackSections_naturality, het, g.pullbackObjUnitIso_hom_app_pullbackSections,
    map_one] at h2
  have h3 : baseRingToGlobalSections K (W.map (algebraMap R K)).projModel 1 =
      baseRingToGlobalSections K (W.map (algebraMap R K)).projModel 0 := by
    rw [map_one, map_zero]
    exact h2
  exact one_ne_zero ((W.map (algebraMap R K)).bijective_baseRingToGlobalSections.1 h3)

/-- Over a field `K` receiving `R`, the base change map `K ⊗ H⁰(𝒪(0[0])) ⟶ H⁰(g^*𝒪(0[0]))` is
injective: `H⁰(𝒪(0[0]))` is generated by the section corresponding to the function `1`, whose
pullback is the function `1` on the model over `K`. -/
theorem injective_cohomologyBaseChange_zero_poleSheaf_zero (K : Type u) [Field K] [Algebra R K] :
    Function.Injective
      (cohomologyBaseChange (W.isPullback_projModelBaseChange_over (R' := K))
        (W.poleSheaf 0).obj 0) := by
  obtain ⟨s, hs, -, hgs⟩ := W.exists_basis_cohomology_poleSheaf_zero
  have hz (z : K ⊗[R] Cohomology (W.poleSheaf 0).obj 0) : ∃ k : K, z = k ⊗ₜ s := by
    induction z using TensorProduct.inductionOn with
    | tmul k x =>
      obtain ⟨r, rfl⟩ := hs x
      exact ⟨r • k, (TensorProduct.smul_tmul _ _ _).symm⟩
    | add a b ha hb =>
      obtain ⟨k₁, rfl⟩ := ha
      obtain ⟨k₂, rfl⟩ := hb
      exact ⟨k₁ + k₂, (TensorProduct.add_tmul _ _ _).symm⟩
  refine (injective_iff_map_eq_zero _).mpr fun z hz0 ↦ ?_
  obtain ⟨k, rfl⟩ := hz z
  rw [cohomologyBaseChange_tmul] at hz0
  obtain rfl | hk := eq_or_ne k 0
  · exact TensorProduct.zero_tmul _ _
  exact absurd ((smul_eq_zero.mp hz0).resolve_left hk) (hgs K)

/-- **A map `𝒪 ⟶ 𝒪([0])` which stays a monomorphism is bijective on `H⁰`.** Let
`α : 𝒪(0[0]) ⟶ 𝒪([0])` be a morphism whose pullback to the projective model over every residue
field of `R` is a monomorphism. Then `H⁰(α)` is bijective. -/
theorem bijective_cohomologyMapBaseLinear_of_mono_pullback_zero_one
    (α : (W.poleSheaf 0).obj ⟶ (W.poleSheaf 1).obj)
    (hα : ∀ (p : Ideal R) [p.IsPrime], Mono ((Scheme.Modules.pullback
      (W.projModelBaseChange (algebraMap R p.ResidueField))).map α)) :
    Function.Bijective (cohomologyMapBaseLinear R W.projModel α 0) := by
  -- `H⁰(𝒪(0[0]))` is free of rank one.
  obtain ⟨s, hs, hs₀, -⟩ := W.exists_basis_cohomology_poleSheaf_zero
  let e : R ≃ₗ[R] Cohomology (W.poleSheaf 0).obj 0 :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton R _ s)
      ⟨(injective_iff_map_eq_zero _).mpr hs₀, fun x ↦ (hs x).imp fun _ h ↦ h.symm⟩
  have := Module.Finite.equiv e
  have := Module.Projective.of_equiv e
  have := W.finitePresentation_cohomology_zero_poleSheaf one_pos
  have := W.projective_cohomology_zero_poleSheaf one_pos
  have hf (p : Ideal R) [p.IsPrime] : Function.Injective
      ((cohomologyMapBaseLinear R W.projModel α 0).baseChange p.ResidueField) := by
    have := hα p
    exact W.injective_baseChange_cohomologyMapBaseLinear_of_mono_pullback _ p.ResidueField
      (W.injective_cohomologyBaseChange_zero_poleSheaf_zero p.ResidueField)
  -- Both modules have rank one.
  have hr₀ (p : PrimeSpectrum R) :
      Module.rankAtStalk (Cohomology (W.poleSheaf 0).obj 0) p = 1 := by
    have := p.nontrivial
    rw [← Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_self, Pi.one_apply]
  -- The cokernel is projective of rank `1 - 1 = 0`, hence zero, so `H⁰(α)` is surjective.
  have := Module.Projective.quotient_range_of_injective_baseChange _ fun p _ ↦ hf p
  have hr : Module.rankAtStalk (R := R) (Cohomology (W.poleSheaf 1).obj 0 ⧸ LinearMap.range
      (cohomologyMapBaseLinear R W.projModel α 0)) = 0 := by
    funext p
    have h := Module.rankAtStalk_quotient_range_add _ (fun q _ ↦ hf q) p
    rw [hr₀, W.rankAtStalk_cohomology_zero_poleSheaf one_pos] at h
    simpa using h
  have := Module.rankAtStalk_eq_zero_iff_subsingleton.mp hr
  have hsurj : Function.Surjective (cohomologyMapBaseLinear R W.projModel α 0) := by
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    infer_instance
  exact Module.bijective_of_surjective_of_rankAtStalk_eq hsurj fun m _ ↦ by
    rw [hr₀, W.rankAtStalk_cohomology_zero_poleSheaf one_pos]

/-- **Every section of `𝒪([0])` is constant**, over any ring: the inclusion
`𝒪 = 𝒪(0[0]) ⟶ 𝒪([0])` is bijective on `H⁰`. This is the first step of the pole filtration. -/
theorem bijective_cohomologyMapBaseLinear_poleSheafMap_zero_one :
    Function.Bijective
      (cohomologyMapBaseLinear R W.projModel (W.poleSheafMap zero_le_one).hom 0) :=
  W.bijective_cohomologyMapBaseLinear_of_mono_pullback_zero_one _ fun _ _ ↦
    W.mono_pullback_map_poleSheafMap_hom _ zero_le_one

end WeierstrassCurve
