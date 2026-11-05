/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
equation splits.

The inclusion `ℒ_m ⟶ ℒ_n` is the dual of the inclusion `𝒪_E(-n[0]) ⊆ 𝒪_E(-m[0])` of the ideal
sheaves of the relative effective Cartier divisors `n[0] ≥ m[0]`. Its pullback along any morphism
`X ⟶ E` along which both divisors pull back to effective Cartier divisors is again a monomorphism
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.mono_pullback_map_poleSheafMap_hom`). On a chart,
transported to the projective model of the chart's equation, it therefore satisfies the
hypothesis of `WeierstrassCurve.projective_quotient_range_cohomologyMapBaseLinear_of_mono_pullback`:
it stays a monomorphism on every fibre. The scheme isomorphisms of the chart carry that statement to
the sections of `π_*ℒ_n` over `U`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mono_pullback_map_poleSheafMap_hom`: the pullback
  of `ℒ_m ⟶ ℒ_n` along a morphism pulling `m[0]` and `n[0]` back to effective Cartier divisors is a
  monomorphism.
* `EllipticCurveGeom.projective_quotient_range_pushforward_poleSheafMap` and
  `EllipticCurveGeom.rankAtStalk_quotient_range_pushforward_poleSheafMap`: over a chart image `U`,
  `Γ(U, π_*ℒ_n) ⧸ Γ(U, π_*ℒ_m)` is projective of rank `n - m`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1 and 2.2.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

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
  -- The same holds for the global sections over `Γ(projModel W, ⊤)`, through which `c.ring` acts
  -- by constants.
  let σ₀ : c.ring ≃+* Γ(W.projModel, ⊤) :=
    RingEquiv.ofBijective _ W.bijective_baseRingToGlobalSections
  have := RingHomInvPair.of_ringEquiv σ₀
  have := RingHomInvPair.of_ringEquiv_symm σ₀
  let e₀ (k : ℕ) : Cohomology (W.poleSheaf k).obj 0 ≃ₛₗ[(σ₀ : c.ring →+* Γ(W.projModel, ⊤))]
      Γ((W.poleSheaf k).obj, ⊤) :=
    { (cohomologyZeroLinearEquiv (W.poleSheaf k).obj).toAddEquiv with
      map_smul' r x := (cohomologyZeroLinearEquiv (W.poleSheaf k).obj).map_smul
        (baseRingToGlobalSections c.ring W.projModel r) x }
  have he₀ (x : Cohomology (W.poleSheaf m).obj 0) :
      e₀ n (cohomologyMapBaseLinear c.ring W.projModel α 0 x) = α.appLinear ⊤ (e₀ m x) := by
    have hx := cohomologyZeroEquiv_cohomologyMap α x
    rw [← coe_cohomologyMapBaseLinear (R := c.ring), ← cohomologyZeroLinearEquiv_apply,
      ← cohomologyZeroLinearEquiv_apply] at hx
    rw [Hom.appLinear_apply]
    exact hx
  have := (e₀ m).projective_quotient_range (e₀ n) he₀
  have h₁ (q : PrimeSpectrum Γ(W.projModel, ⊤)) :
      Module.rankAtStalk (Γ((W.poleSheaf n).obj, ⊤) ⧸ LinearMap.range (α.appLinear ⊤)) q =
        n - m := by
    rw [(e₀ m).rankAtStalk_quotient_range_eq (e₀ n) he₀, h₀]
  -- The same holds for the sections of the restriction of `ℒ_n` along `j`.
  have := (W.finite_projective_globalSections_poleSheaf (hm.trans_le h)).1
  have he₁ (x : Γ((W.poleSheaf m).obj, ⊤)) : (sectionsLinearEquiv en ⊤).symm (α.appLinear ⊤ x) =
      ((restrictFunctor j).map φ).appLinear ⊤ ((sectionsLinearEquiv em ⊤).symm x) := by
    have hα : α ≫ en.inv = em.inv ≫ (restrictFunctor j).map φ := by
      simp only [α, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [sectionsLinearEquiv_symm_apply, sectionsLinearEquiv_symm_apply, Hom.appLinear_apply,
      Hom.appLinear_apply, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Hom.comp_app, ← Hom.comp_app, hα]
  have := (sectionsLinearEquiv em ⊤).symm.projective_quotient_range _ he₁
  have h₂ (q : PrimeSpectrum Γ(W.projModel, ⊤)) : Module.rankAtStalk
      (Γ((E.poleSheaf n).obj.restrict j, ⊤) ⧸
        LinearMap.range (((restrictFunctor j).map φ).appLinear ⊤)) q = n - m := by
    rw [(sectionsLinearEquiv em ⊤).symm.rankAtStalk_quotient_range_eq _ he₁, h₁]
  -- The same holds for the sections of `ℒ_n` over the image of `j`, which is `π⁻¹(U)`.
  have := Module.Finite.equiv (sectionsLinearEquiv en ⊤).symm
  let σ₂ : Γ(W.projModel, ⊤) ≃+* Γ(E.carrier, j ''ᵁ ⊤) :=
    (j.appIso ⊤).symm.commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv σ₂
  have := RingHomInvPair.of_ringEquiv_symm σ₂
  -- By the definition of `Scheme.Modules.restrictFunctor`, the sections of the restriction over
  -- `⊤` are the sections over `j ''ᵁ ⊤`, on which `Γ(projModel, ⊤)` acts through
  -- `(j.appIso ⊤).inv`, and the restriction of `φ` acts on them as `φ`.
  let e₂ (k : ℕ) : Γ((E.poleSheaf k).obj.restrict j, ⊤)
      ≃ₛₗ[(σ₂ : Γ(W.projModel, ⊤) →+* Γ(E.carrier, j ''ᵁ ⊤))] Γ((E.poleSheaf k).obj, j ''ᵁ ⊤) :=
    { AddEquiv.refl _ with map_smul' _ _ := rfl }
  have he₂ (x : Γ((E.poleSheaf m).obj.restrict j, ⊤)) :
      e₂ n (((restrictFunctor j).map φ).appLinear ⊤ x) = φ.appLinear (j ''ᵁ ⊤) (e₂ m x) := by
    rw [Hom.appLinear_apply, Hom.appLinear_apply]
    rfl
  have := (e₂ m).projective_quotient_range (e₂ n) he₂
  have h₃ (q : PrimeSpectrum Γ(E.carrier, j ''ᵁ ⊤)) : Module.rankAtStalk
      (Γ((E.poleSheaf n).obj, j ''ᵁ ⊤) ⧸ LinearMap.range (φ.appLinear (j ''ᵁ ⊤))) q = n - m := by
    rw [(e₂ m).rankAtStalk_quotient_range_eq (e₂ n) he₂, h₂]
  have hj : j ''ᵁ ⊤ = E.structureMap ⁻¹ᵁ U := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp_of_isIso,
      c.opensRange_toTotal]
  rw [hj] at this h₃
  -- The same holds for the sections of `π_*ℒ_n` over `U`, as `π` identifies `Γ(S, U)` with
  -- `Γ(E, π⁻¹(U))`.
  have := (E.finite_projective_sections_poleSheaf c (hm.trans_le h)).1
  have := c.isIso_app_opensRange
  let σ₁ : Γ(S, U) ≃+* Γ(E.carrier, E.structureMap ⁻¹ᵁ U) :=
    (asIso (E.structureMap.app U)).commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv σ₁
  have := RingHomInvPair.of_ringEquiv_symm σ₁
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

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
