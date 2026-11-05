/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Projective.Complement
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.PoleSheaf.FiltrationQuotient
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PoleSheaf.Filtration
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PoleSheaf.LocallyFree
public import TauCeti.AlgebraicGeometry.Modules.AppLinear

/-!
# The quotients of the pole filtration of an elliptic curve

Let `E` be an elliptic curve over a scheme `S`, with structure morphism `π : E ⟶ S`, and let
`0 < m ≤ n`. The inclusion `ℒ_m ⟶ ℒ_n` of pole sheaves pushes forward to a monomorphism
`π_*ℒ_m ⟶ π_*ℒ_n` of locally free sheaves of ranks `m` and `n`. This file shows that,
Zariski-locally on `S`, its image is a direct summand with quotient of rank `n - m`: over the image
`U` of the base of a pointed Weierstrass chart, the quotient of `Γ(U, π_*ℒ_n)` by the image of
`Γ(U, π_*ℒ_m)` is a finitely generated projective `Γ(S, U)`-module of constant rank `n - m`
(`EllipticCurveGeom.projective_quotient_range_pushforward_poleSheafMap` and
`EllipticCurveGeom.rankAtStalk_quotient_range_pushforward_poleSheafMap`). These are the
successive quotients of the pole filtration that the pole-filtration construction of a Weierstrass
equation splits, and they do split over `U`
(`EllipticCurveGeom.exists_isCompl_range_pushforward_poleSheafMap`). For `m = 0` the first step is
an equality: `π_*ℒ_0 ⟶ π_*ℒ_1` is an isomorphism
(`EllipticCurveGeom.isIso_pushforward_map_poleSheafMap_zero_one`), as every section of `𝒪_E([0])`
is a function.

The inclusion `ℒ_m ⟶ ℒ_n` is the dual of the inclusion `𝒪_E(-n[0]) ⊆ 𝒪_E(-m[0])` of the ideal
sheaves of the relative effective Cartier divisors `n[0] ≥ m[0]`. Its pullback along any morphism
`X ⟶ E` along which both divisors pull back to effective Cartier divisors is again a monomorphism
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.mono_pullback_map_poleSheafMap_hom`). On a chart,
transported to the projective model of the chart's equation, it therefore satisfies the
hypothesis of `WeierstrassCurve.projective_quotient_range_cohomologyMapBaseLinear_of_mono_pullback`:
it stays a monomorphism on every fibre. The scheme isomorphisms of the chart carry that statement to
the sections of `π_*ℒ_n` over `U`: `PointedWeierstrassChart.modelCohomologyEquiv` identifies `H⁰` of
the model with the sections over `π⁻¹(U)`, semilinearly over the coefficient ring of the chart.

## Main results

* `TauCeti.AlgebraicGeometry.PointedWeierstrassChart.modelCohomologyEquiv`: on a chart, an
  identification of the restriction of `M` to the model with `N` identifies `H⁰(N)` with the
  sections of `M` over the image of the model, compatibly with morphisms
  (`PointedWeierstrassChart.modelCohomologyEquiv_cohomologyMapBaseLinear`).
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mono_pullback_map_poleSheafMap_hom`: the pullback
  of `ℒ_m ⟶ ℒ_n` along a morphism pulling `m[0]` and `n[0]` back to effective Cartier divisors is a
  monomorphism.
* `EllipticCurveGeom.projective_quotient_range_pushforward_poleSheafMap` and
  `EllipticCurveGeom.rankAtStalk_quotient_range_pushforward_poleSheafMap`: over a chart image `U`,
  `Γ(U, π_*ℒ_n) ⧸ Γ(U, π_*ℒ_m)` is projective of rank `n - m`.
* `EllipticCurveGeom.exists_isCompl_range_pushforward_poleSheafMap`: so the image has a
  complement, the Zariski-local splitting of the pole filtration.
* `EllipticCurveGeom.bijective_app_pushforward_poleSheafMap_zero_one` and
  `EllipticCurveGeom.isIso_pushforward_map_poleSheafMap_zero_one`: `π_*ℒ_0 ⟶ π_*ℒ_1` is bijective
  over every chart image, hence an isomorphism.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1 and 2.2.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace TauCeti.AlgebraicGeometry

namespace PointedWeierstrassChart

open Scheme.Modules

variable {S X : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X} (c : PointedWeierstrassChart π zero)

/-- The coefficient ring of a pointed Weierstrass chart is the ring of functions on the image of
its projective model in `X`: it is the ring of global functions on the model. -/
noncomputable def modelRingEquiv : c.ring ≃+* Γ(X, (c.modelIso.inv ≫ c.toTotal) ''ᵁ ⊤) :=
  (RingEquiv.ofBijective _ c.equation.bijective_baseRingToGlobalSections).trans
    ((c.modelIso.inv ≫ c.toTotal).appIso ⊤).symm.commRingCatIsoToRingEquiv

/-- **Sections over a chart as cohomology of the model.** On a pointed Weierstrass chart, an
identification `e` of the restriction of an `𝒪_X`-module `M` to the projective model of the
chart's equation with a module `N` on the model identifies `H⁰(N)` with the sections of `M` over
the image of the model, semilinearly over `PointedWeierstrassChart.modelRingEquiv`. -/
noncomputable def modelCohomologyEquiv {M : X.Modules} {N : c.equation.projModel.Modules}
    (e : M.restrict (c.modelIso.inv ≫ c.toTotal) ≅ N) :
    Cohomology N 0 ≃ₛₗ[(c.modelRingEquiv : c.ring →+* Γ(X, (c.modelIso.inv ≫ c.toTotal) ''ᵁ ⊤))]
      Γ(M, (c.modelIso.inv ≫ c.toTotal) ''ᵁ ⊤) where
  __ := (cohomologyZeroLinearEquiv N).toAddEquiv.trans (sectionsLinearEquiv e ⊤).symm.toAddEquiv
  map_smul' r x := by
    -- By the definition of `Scheme.Modules.restrictFunctor`, the sections of the restriction over
    -- `⊤` are the sections over the image of the model, on which `Γ(projModel, ⊤)` acts through
    -- `appIso`; and `c.ring` acts on `H⁰(N)` through the global functions of the model.
    have h := (cohomologyZeroLinearEquiv N).map_smul
      (baseRingToGlobalSections c.ring c.equation.projModel r) x
    exact (congrArg (sectionsLinearEquiv e ⊤).symm h).trans (map_smul _ _ _)

theorem modelCohomologyEquiv_apply {M : X.Modules} {N : c.equation.projModel.Modules}
    (e : M.restrict (c.modelIso.inv ≫ c.toTotal) ≅ N) (x : Cohomology N 0) :
    c.modelCohomologyEquiv e x = e.inv.app ⊤ (cohomologyZeroEquiv N x) := by
  change (sectionsLinearEquiv e ⊤).symm (cohomologyZeroLinearEquiv N x) = _
  rw [sectionsLinearEquiv_symm_apply, cohomologyZeroLinearEquiv_apply]

/-- `PointedWeierstrassChart.modelCohomologyEquiv` carries `H⁰` of a morphism of modules on the
model, transported from a morphism `φ : M ⟶ M'` on `X`, to the action of `φ` on sections. -/
theorem modelCohomologyEquiv_cohomologyMapBaseLinear {M M' : X.Modules}
    {N N' : c.equation.projModel.Modules} (e : M.restrict (c.modelIso.inv ≫ c.toTotal) ≅ N)
    (e' : M'.restrict (c.modelIso.inv ≫ c.toTotal) ≅ N') (φ : M ⟶ M') (x : Cohomology N 0) :
    c.modelCohomologyEquiv e' (cohomologyMapBaseLinear c.ring c.equation.projModel
        (e.inv ≫ (restrictFunctor (c.modelIso.inv ≫ c.toTotal)).map φ ≫ e'.hom) 0 x) =
      φ.appLinear _ (c.modelCohomologyEquiv e x) := by
  have h : (e.inv ≫ (restrictFunctor (c.modelIso.inv ≫ c.toTotal)).map φ ≫ e'.hom) ≫ e'.inv =
      e.inv ≫ (restrictFunctor (c.modelIso.inv ≫ c.toTotal)).map φ := by
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [modelCohomologyEquiv_apply, modelCohomologyEquiv_apply, coe_cohomologyMapBaseLinear,
    cohomologyZeroEquiv_cohomologyMap, ← ConcreteCategory.comp_apply, ← Hom.comp_app, h,
    Hom.comp_app, ConcreteCategory.comp_apply]
  -- By the definition of `Scheme.Modules.restrictFunctor`, the restriction of `φ` acts on the
  -- sections over `⊤` as `φ` acts on the sections over the image of the model.
  exact (Hom.appLinear_apply φ _ _).symm

end PointedWeierstrassChart

namespace EllipticCurveGeom

open Scheme.Modules

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) {m n : ℕ}

/-- **The pole filtration commutes with base change**: the pullback of the inclusion `ℒ_m ⟶ ℒ_n`
along a morphism `φ : X ⟶ E` is a monomorphism as soon as the inverse images of `m[0]` and `n[0]`
along `φ` are effective Cartier divisors. -/
theorem mono_pullback_map_poleSheafMap_hom {X : Scheme.{u}} (φ : X ⟶ E.carrier) (h : m ≤ n)
    (hm : ((E.zeroDivisor ^ m).comap φ).IsEffectiveCartier)
    (hn : ((E.zeroDivisor ^ n).comap φ).IsEffectiveCartier) :
    Mono ((Scheme.Modules.pullback φ).map (E.poleSheafMap h).hom) := by
  have := Scheme.IdealSheafData.IsEffectiveCartier.mono_pullback_map_dualMap_hom
    (E.isRelativeEffectiveCartier_zeroDivisor_pow m).isEffectiveCartier
    (E.isRelativeEffectiveCartier_zeroDivisor_pow n).isEffectiveCartier hm hn
    (E.zeroDivisor_pow_le_pow h)
  rw [poleSheafMap_def, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.eqToHom_hom, ObjectProperty.eqToHom_hom,
    Functor.map_comp, Functor.map_comp]
  infer_instance

/-- On a pointed Weierstrass chart, the inverse image of `n[0]` in the projective model of the
chart's equation is the model's divisor `n[0]`. -/
theorem zeroDivisor_pow_comap_modelIso_inv_toTotal
    (c : PointedWeierstrassChart E.structureMap E.zero) (n : ℕ) :
    (E.zeroDivisor ^ n).comap (c.modelIso.inv ≫ c.toTotal) = c.equation.zeroSectionDivisor ^ n := by
  rw [Scheme.IdealSheafData.comap_comp, zeroDivisor_pow_comap_toTotal,
    ← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

/-- On a pointed Weierstrass chart, the inclusion `ℒ_m ⟶ ℒ_n`, transported to the projective model
of the chart's equation along any identifications of the restricted pole sheaves with those of the
model, stays a monomorphism after every change of the coefficient ring. -/
private theorem mono_pullback_map_chart (c : PointedWeierstrassChart E.structureMap E.zero)
    (h : m ≤ n)
    (em : (E.poleSheaf m).obj.restrict (c.modelIso.inv ≫ c.toTotal) ≅ (c.equation.poleSheaf m).obj)
    (en : (E.poleSheaf n).obj.restrict (c.modelIso.inv ≫ c.toTotal) ≅ (c.equation.poleSheaf n).obj)
    {R' : Type u} [CommRing R'] (f : c.ring →+* R') :
    Mono ((Scheme.Modules.pullback (c.equation.projModelBaseChange f)).map (em.inv ≫
      (restrictFunctor (c.modelIso.inv ≫ c.toTotal)).map (E.poleSheafMap h).hom ≫ en.hom)) := by
  set j := c.modelIso.inv ≫ c.toTotal
  set g := c.equation.projModelBaseChange f
  set φ := (E.poleSheafMap h).hom
  let G := Scheme.Modules.pullback g
  have hcomap (k : ℕ) : ((E.zeroDivisor ^ k).comap (g ≫ j)).IsEffectiveCartier := by
    rw [Scheme.IdealSheafData.comap_comp, E.zeroDivisor_pow_comap_modelIso_inv_toTotal,
      ← c.equation.zeroSectionDivisor_pow_map]
    exact ((c.equation.map f).isRelativeEffectiveCartier_zeroSectionDivisor_pow
      k).isEffectiveCartier
  have := E.mono_pullback_map_poleSheafMap_hom (g ≫ j) h (hcomap m) (hcomap n)
  -- Pulling back along `j` and then along `g` is pulling back along `g ≫ j`.
  have : Mono (G.map ((Scheme.Modules.pullback j).map φ)) := by
    have : Mono (G.map ((Scheme.Modules.pullback j).map φ) ≫ (pullbackComp g j).hom.app _) := by
      have h' := (pullbackComp g j).hom.naturality φ
      rw [Functor.comp_map] at h'
      rw [h']
      infer_instance
    exact mono_of_mono _ ((pullbackComp g j).hom.app _)
  -- Restriction along the open immersion `j` is pullback along `j`.
  have : Mono (G.map ((restrictFunctor j).map φ)) := by
    have : Mono (G.map ((restrictFunctor j).map φ) ≫
        G.map ((restrictFunctorIsoPullback j).hom.app _)) := by
      rw [← Functor.map_comp, (restrictFunctorIsoPullback j).hom.naturality φ, Functor.map_comp]
      infer_instance
    exact mono_of_mono _ (G.map ((restrictFunctorIsoPullback j).hom.app _))
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

/-- Over the image `U` of the base of a chart, for `0 < m ≤ n`, the quotient of `Γ(U, π_*ℒ_n)` by
the image of `Γ(U, π_*ℒ_m)` is projective of constant rank `n - m`. -/
private theorem projective_rankAtStalk_quotient_range_pushforward_poleSheafMap
    (c : PointedWeierstrassChart E.structureMap E.zero) (hm : 0 < m) (h : m ≤ n) :
    Module.Projective Γ(S, c.baseMap.opensRange)
        (Γ((pushforward E.structureMap).obj (E.poleSheaf n).obj, c.baseMap.opensRange) ⧸
          LinearMap.range (((pushforward E.structureMap).map
            (E.poleSheafMap h).hom).appLinear c.baseMap.opensRange)) ∧
      ∀ p : PrimeSpectrum Γ(S, c.baseMap.opensRange), Module.rankAtStalk
        (Γ((pushforward E.structureMap).obj (E.poleSheaf n).obj, c.baseMap.opensRange) ⧸
          LinearMap.range (((pushforward E.structureMap).map
            (E.poleSheafMap h).hom).appLinear c.baseMap.opensRange)) p = n - m := by
  let U := c.baseMap.opensRange
  let j := c.modelIso.inv ≫ c.toTotal
  let W := c.equation
  let φ := (E.poleSheafMap h).hom
  obtain ⟨em⟩ := E.nonempty_restrict_poleSheaf_iso c m
  obtain ⟨en⟩ := E.nonempty_restrict_poleSheaf_iso c n
  let α := em.inv ≫ (restrictFunctor j).map φ ≫ en.hom
  -- On the model, `H⁰(𝒪(n[0])) ⧸ H⁰(𝒪(m[0]))` is projective of rank `n - m` over `c.ring`.
  have := W.projective_quotient_range_cohomologyMapBaseLinear_of_mono_pullback hm h α
    fun _ _ ↦ E.mono_pullback_map_chart c h em en _
  have h₀ := W.rankAtStalk_quotient_range_cohomologyMapBaseLinear_of_mono_pullback hm h α
    fun _ _ ↦ E.mono_pullback_map_chart c h em en _
  have := W.finitePresentation_cohomology_zero_poleSheaf (hm.trans_le h)
  -- The same holds for the sections of `ℒ_n` over the image of the model, which is `π⁻¹(U)`.
  have he := c.modelCohomologyEquiv_cohomologyMapBaseLinear em en φ
  have := (c.modelCohomologyEquiv em).projective_quotient_range (c.modelCohomologyEquiv en) he
  have h₃ (q : PrimeSpectrum Γ(E.carrier, j ''ᵁ ⊤)) : Module.rankAtStalk
      (Γ((E.poleSheaf n).obj, j ''ᵁ ⊤) ⧸ LinearMap.range (φ.appLinear (j ''ᵁ ⊤))) q = n - m := by
    rw [(c.modelCohomologyEquiv em).rankAtStalk_quotient_range_eq (c.modelCohomologyEquiv en) he,
      h₀]
  rw [c.image_top_modelIso_inv_toTotal] at this h₃
  -- The same holds for the sections of `π_*ℒ_n` over `U`, as `π` identifies `Γ(S, U)` with
  -- `Γ(E, π⁻¹(U))`.
  have := (E.finite_projective_sections_poleSheaf c (hm.trans_le h)).1
  have := c.isIso_app_opensRange
  let σ₁ : Γ(S, U) ≃+* Γ(E.carrier, E.structureMap ⁻¹ᵁ U) :=
    (asIso (E.structureMap.app U)).commRingCatIsoToRingEquiv
  -- By the definition of `Scheme.Modules.pushforward`, `Γ(S, U)` acts on the sections of the
  -- direct image through `π.app U`, and the direct image of `φ` acts on them as `φ`.
  let e₃ (k : ℕ) : Γ((pushforward E.structureMap).obj (E.poleSheaf k).obj, U)
      ≃ₛₗ[(σ₁ : Γ(S, U) →+* Γ(E.carrier, E.structureMap ⁻¹ᵁ U))]
      Γ((E.poleSheaf k).obj, E.structureMap ⁻¹ᵁ U) :=
    { AddEquiv.refl _ with map_smul' _ _ := rfl }
  have he₃ (x : Γ((E.poleSheaf m).obj, E.structureMap ⁻¹ᵁ U)) : (e₃ n).symm
      (φ.appLinear _ x) = ((pushforward E.structureMap).map φ).appLinear U ((e₃ m).symm x) := by
    rw [Hom.appLinear_apply, Hom.appLinear_apply]
    rfl
  refine ⟨(e₃ m).symm.projective_quotient_range (e₃ n).symm he₃, fun q ↦ ?_⟩
  rw [(e₃ m).symm.rankAtStalk_quotient_range_eq (e₃ n).symm he₃, h₃]

/-- **The successive quotients of the pole filtration are locally free.** Over the image `U` of
the base of a pointed Weierstrass chart of `E`, for `0 < m ≤ n`, the quotient of `Γ(U, π_*ℒ_n)` by
the image of `Γ(U, π_*ℒ_m)` is a projective `Γ(S, U)`-module. So the image is a direct summand. -/
theorem projective_quotient_range_pushforward_poleSheafMap
    (c : PointedWeierstrassChart E.structureMap E.zero) (hm : 0 < m) (h : m ≤ n) :
    Module.Projective Γ(S, c.baseMap.opensRange)
      (Γ((pushforward E.structureMap).obj (E.poleSheaf n).obj, c.baseMap.opensRange) ⧸
        LinearMap.range (((pushforward E.structureMap).map
          (E.poleSheafMap h).hom).appLinear c.baseMap.opensRange)) :=
  (E.projective_rankAtStalk_quotient_range_pushforward_poleSheafMap c hm h).1

/-- **The successive quotients of the pole filtration have rank `n - m`.** Over the image `U` of
the base of a pointed Weierstrass chart of `E`, for `0 < m ≤ n`, the quotient of `Γ(U, π_*ℒ_n)` by
the image of `Γ(U, π_*ℒ_m)` has rank `n - m` at every prime of `Γ(S, U)`. -/
theorem rankAtStalk_quotient_range_pushforward_poleSheafMap
    (c : PointedWeierstrassChart E.structureMap E.zero) (hm : 0 < m) (h : m ≤ n)
    (p : PrimeSpectrum Γ(S, c.baseMap.opensRange)) :
    Module.rankAtStalk
      (Γ((pushforward E.structureMap).obj (E.poleSheaf n).obj, c.baseMap.opensRange) ⧸
        LinearMap.range (((pushforward E.structureMap).map
          (E.poleSheafMap h).hom).appLinear c.baseMap.opensRange)) p = n - m :=
  (E.projective_rankAtStalk_quotient_range_pushforward_poleSheafMap c hm h).2 p

/-- **The pole filtration splits Zariski-locally.** Over the image `U` of the base of a pointed
Weierstrass chart of `E`, for `0 < m ≤ n`, the image of `Γ(U, π_*ℒ_m)` in `Γ(U, π_*ℒ_n)` has a
complement: its quotient is projective. -/
theorem exists_isCompl_range_pushforward_poleSheafMap
    (c : PointedWeierstrassChart E.structureMap E.zero) (hm : 0 < m) (h : m ≤ n) :
    ∃ q : Submodule Γ(S, c.baseMap.opensRange)
        Γ((pushforward E.structureMap).obj (E.poleSheaf n).obj, c.baseMap.opensRange),
      IsCompl (LinearMap.range (((pushforward E.structureMap).map
        (E.poleSheafMap h).hom).appLinear c.baseMap.opensRange)) q :=
  have := E.projective_quotient_range_pushforward_poleSheafMap c hm h
  Submodule.exists_isCompl_of_projective_quotient _

/-- **Every section of `𝒪_E([0])` over a chart is a function.** Over the image `U` of the base of
a pointed Weierstrass chart of `E`, the inclusion `ℒ_0 ⟶ ℒ_1` is bijective on the sections of the
direct images over `U`: every section of `𝒪_E([0])` over `π⁻¹(U)` comes from a unique section of
`𝒪_E(0[0])`, which is a function on `π⁻¹(U)`. -/
theorem bijective_app_pushforward_poleSheafMap_zero_one
    (c : PointedWeierstrassChart E.structureMap E.zero) :
    Function.Bijective (((pushforward E.structureMap).map
      (E.poleSheafMap zero_le_one).hom).app c.baseMap.opensRange) := by
  let j := c.modelIso.inv ≫ c.toTotal
  let φ := (E.poleSheafMap zero_le_one).hom
  obtain ⟨e₀⟩ := E.nonempty_restrict_poleSheaf_iso c 0
  obtain ⟨e₁⟩ := E.nonempty_restrict_poleSheaf_iso c 1
  -- On the model, the inclusion is bijective on `H⁰`.
  have h := c.equation.bijective_cohomologyMapBaseLinear_of_mono_pullback_zero_one
    (e₀.inv ≫ (restrictFunctor j).map φ ≫ e₁.hom)
    fun _ _ ↦ E.mono_pullback_map_chart c zero_le_one e₀ e₁ _
  -- Hence it is bijective on sections over the image of the model, which is `π⁻¹(U)`.
  have h' : Function.Bijective (φ.app (j ''ᵁ ⊤)) := by
    convert (c.modelCohomologyEquiv e₁).bijective.comp
      (h.comp (c.modelCohomologyEquiv e₀).symm.bijective) using 1
    funext y
    rw [Function.comp_apply, Function.comp_apply, c.modelCohomologyEquiv_cohomologyMapBaseLinear,
      LinearEquiv.apply_symm_apply, Hom.appLinear_apply]
  rw [c.image_top_modelIso_inv_toTotal] at h'
  exact h'

/-- **`π_*𝒪_E(0[0]) ≅ π_*𝒪_E([0])`.** For an elliptic curve `π : E ⟶ S`, the direct image of the
inclusion `ℒ_0 ⟶ ℒ_1` is an isomorphism: the first step of the pole filtration of `π_*ℒ_n` is an
equality, as every section of `𝒪_E([0])` is a function. -/
instance isIso_pushforward_map_poleSheafMap_zero_one :
    IsIso ((pushforward E.structureMap).map (E.poleSheafMap zero_le_one).hom) := by
  obtain ⟨A⟩ := E.localModel
  -- the images of the restricted charts form a basis of the topology of `S`
  exact Hom.isIso_of_isBasis _ A.isBasis_range_opensRange_restrict fun p ↦
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (E.bijective_app_pushforward_poleSheafMap_zero_one ((A.chart p.1).restrict p.2))

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
