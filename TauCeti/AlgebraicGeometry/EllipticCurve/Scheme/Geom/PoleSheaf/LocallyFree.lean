/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.PoleSheaf.Cohomology
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PoleSheaf.DirectImage
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import TauCeti.AlgebraicGeometry.Modules.Sheaf

/-!
# `π_*𝒪_E(n[0])` is locally free of rank `n`

Let `E` be an elliptic curve over a scheme `S`, with structure morphism `π : E ⟶ S`, and let
`n > 0`. This file shows that the direct image `π_*𝒪_E(n[0])` of the pole sheaf is a finite
locally free `𝒪_S`-module
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFiniteLocallyFree_pushforward_poleSheaf`) of
rank `n` at every point of `S`
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.rank_pushforward_poleSheaf`).

The direct image is quasi-coherent, since `π` is proper. Over the image `U` of the base of a
pointed Weierstrass chart, which is affine, its sections are the sections of `𝒪_E(n[0])` over
`π⁻¹(U)`, the global sections of the pole sheaf of the projective model of the chart's equation.
These form a finitely generated projective module of constant rank `n` over the global functions
on the model (`WeierstrassCurve.finite_projective_globalSections_poleSheaf`), and the scheme
isomorphisms of the chart identify those functions with `Γ(S, U)`
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.finite_projective_sections_pushforward_poleSheaf`).
A quasi-coherent sheaf with such sections over an affine open cover is finite locally free
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_finite_projective_sections`), with rank
the rank of the sections (`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rank_fromSpec_apply`).

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.finite_projective_sections_poleSheaf`: over the
  image `U` of the base of a chart, `Γ(π⁻¹(U), 𝒪_E(n[0]))` is a finitely generated projective
  `Γ(E, π⁻¹(U))`-module of constant rank `n`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.finite_projective_sections_pushforward_poleSheaf`:
  over the image `U` of the base of a chart, `Γ(U, π_*𝒪_E(n[0]))` is a finitely generated
  projective `Γ(S, U)`-module of constant rank `n`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFiniteLocallyFree_pushforward_poleSheaf`:
  `π_*𝒪_E(n[0])` is finite locally free.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.rank_pushforward_poleSheaf`: it has rank `n`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

open Scheme.Modules

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- **The sections of `𝒪_E(n[0])` over a chart.** Over the image `U` of the base of a pointed
Weierstrass chart of `E`, the sections of `𝒪_E(n[0])` over `π⁻¹(U)` form a finitely generated
projective `Γ(E, π⁻¹(U))`-module of constant rank `n` for `n > 0`: `π⁻¹(U)` is the projective model
of the equation of the chart, and the sections are the global sections of its pole sheaf. -/
theorem finite_projective_sections_poleSheaf
    (c : PointedWeierstrassChart E.structureMap E.zero) {n : ℕ} (hn : 0 < n) :
    Module.Finite Γ(E.carrier, E.structureMap ⁻¹ᵁ c.baseMap.opensRange)
        Γ((E.poleSheaf n).obj, E.structureMap ⁻¹ᵁ c.baseMap.opensRange) ∧
      Module.Projective Γ(E.carrier, E.structureMap ⁻¹ᵁ c.baseMap.opensRange)
        Γ((E.poleSheaf n).obj, E.structureMap ⁻¹ᵁ c.baseMap.opensRange) ∧
      ∀ p : PrimeSpectrum Γ(E.carrier, E.structureMap ⁻¹ᵁ c.baseMap.opensRange),
        Module.rankAtStalk Γ((E.poleSheaf n).obj, E.structureMap ⁻¹ᵁ c.baseMap.opensRange) p =
          n := by
  let j := c.modelIso.inv ≫ c.toTotal
  obtain ⟨e⟩ := E.nonempty_restrict_poleSheaf_iso c n
  obtain ⟨_, _, h₀⟩ := c.equation.finite_projective_globalSections_poleSheaf hn
  -- the sections over `⊤` of the restriction along `j` are those of the pole sheaf of the model
  let e₁ := (sectionsLinearEquiv e ⊤).symm
  have := Module.Finite.equiv e₁
  have := Module.Projective.of_equiv' e₁
  have h₁ := Module.rankAtStalk_eq_of_equiv e₁
  -- and they are the sections over the image of `j`, which is `π⁻¹(U)`
  let σ : Γ(c.equation.projModel, ⊤) ≃+* Γ(E.carrier, j ''ᵁ ⊤) :=
    (j.appIso ⊤).symm.commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  -- by the definition of `Scheme.Modules.restrictFunctor`, `Γ(projModel, ⊤)` acts on the sections
  -- of the restriction through `(j.appIso ⊤).inv` (`Scheme.Modules.smul_restrictAppIso_hom`)
  let e₂ : Γ((E.poleSheaf n).obj.restrict j, ⊤)
      ≃ₛₗ[(σ : Γ(c.equation.projModel, ⊤) →+* Γ(E.carrier, j ''ᵁ ⊤))]
      Γ((E.poleSheaf n).obj, j ''ᵁ ⊤) :=
    { AddEquiv.refl _ with map_smul' _ _ := rfl }
  have h₂ : Module.Finite Γ(E.carrier, j ''ᵁ ⊤) Γ((E.poleSheaf n).obj, j ''ᵁ ⊤) ∧
      Module.Projective Γ(E.carrier, j ''ᵁ ⊤) Γ((E.poleSheaf n).obj, j ''ᵁ ⊤) ∧
      ∀ p : PrimeSpectrum Γ(E.carrier, j ''ᵁ ⊤),
        Module.rankAtStalk Γ((E.poleSheaf n).obj, j ''ᵁ ⊤) p = n := by
    refine ⟨e₂.toLinearMap.finite_of_surjective e₂.surjective, .of_equiv e₂, fun p ↦ ?_⟩
    rw [e₂.rankAtStalk_eq, ← h₁, h₀]
  have hj : j ''ᵁ ⊤ = E.structureMap ⁻¹ᵁ c.baseMap.opensRange := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp_of_isIso,
      c.opensRange_toTotal]
  rwa [hj] at h₂

/-- **The sections of `π_*𝒪_E(n[0])` over a chart.** Over the image `U` of the base of a pointed
Weierstrass chart of `E`, the sections of `π_*𝒪_E(n[0])` form a finitely generated projective
`Γ(S, U)`-module of constant rank `n` for `n > 0`: they are the sections of `𝒪_E(n[0])` over
`π⁻¹(U)`, and `π` identifies the functions on `U` with the functions on `π⁻¹(U)`. -/
theorem finite_projective_sections_pushforward_poleSheaf
    (c : PointedWeierstrassChart E.structureMap E.zero) {n : ℕ} (hn : 0 < n) :
    Module.Finite Γ(S, c.baseMap.opensRange)
        Γ((pushforward E.structureMap).obj (E.poleSheaf n).obj, c.baseMap.opensRange) ∧
      Module.Projective Γ(S, c.baseMap.opensRange)
        Γ((pushforward E.structureMap).obj (E.poleSheaf n).obj, c.baseMap.opensRange) ∧
      ∀ p : PrimeSpectrum Γ(S, c.baseMap.opensRange), Module.rankAtStalk
        Γ((pushforward E.structureMap).obj (E.poleSheaf n).obj, c.baseMap.opensRange) p = n := by
  let U := c.baseMap.opensRange
  obtain ⟨_, _, h⟩ := E.finite_projective_sections_poleSheaf c hn
  have := c.isIso_app_opensRange
  let σ : Γ(S, U) ≃+* Γ(E.carrier, E.structureMap ⁻¹ᵁ U) :=
    (asIso (E.structureMap.app U)).commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  -- by the definition of `Scheme.Modules.pushforward`, `Γ(S, U)` acts on the sections of the direct
  -- image through `π.app U`
  let e : Γ((pushforward E.structureMap).obj (E.poleSheaf n).obj, U)
      ≃ₛₗ[(σ : Γ(S, U) →+* Γ(E.carrier, E.structureMap ⁻¹ᵁ U))]
      Γ((E.poleSheaf n).obj, E.structureMap ⁻¹ᵁ U) :=
    { AddEquiv.refl _ with map_smul' _ _ := rfl }
  refine ⟨e.symm.toLinearMap.finite_of_surjective e.symm.surjective, .of_equiv e.symm,
    fun p ↦ ?_⟩
  rw [e.symm.rankAtStalk_eq, h]

/-- **`π_*𝒪_E(n[0])` is finite locally free.** For an elliptic curve `π : E ⟶ S` and `n > 0`, the
direct image of the pole sheaf `𝒪_E(n[0])` is a finite locally free `𝒪_S`-module. -/
theorem isFiniteLocallyFree_pushforward_poleSheaf {n : ℕ} (hn : 0 < n) :
    isFiniteLocallyFree S ((pushforward E.structureMap).obj (E.poleSheaf n).obj) := by
  obtain ⟨A⟩ := E.localModel
  have : (E.poleSheaf n).obj.IsQuasicoherent :=
    inferInstanceAs
      ((InvertibleSheaf.toFiniteLocallyFree _).obj (E.poleSheaf n)).obj.IsQuasicoherent
  have (i : A.index) := (E.finite_projective_sections_pushforward_poleSheaf (A.chart i) hn).1
  have (i : A.index) := (E.finite_projective_sections_pushforward_poleSheaf (A.chart i) hn).2.1
  refine isFiniteLocallyFree_of_finite_projective_sections _
    (U := fun i ↦ (A.chart i).baseMap.opensRange)
    (fun i ↦ isAffineOpen_opensRange _) (eq_top_iff.mpr fun s _ ↦ ?_)
  obtain ⟨i, x, rfl⟩ := A.covers s
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, x, rfl⟩

/-- **`π_*𝒪_E(n[0])` is locally free of rank `n`.** For an elliptic curve `π : E ⟶ S` and `n > 0`,
the finite locally free sheaf `π_*𝒪_E(n[0])` has rank `n` at every point of `S`. -/
theorem rank_pushforward_poleSheaf {n : ℕ} (hn : 0 < n) (s : S) :
    FiniteLocallyFreeSheaf.rank ⟨_, E.isFiniteLocallyFree_pushforward_poleSheaf hn⟩ s = n := by
  obtain ⟨A⟩ := E.localModel
  obtain ⟨i, x, rfl⟩ := A.covers s
  have hU : IsAffineOpen (A.chart i).baseMap.opensRange := isAffineOpen_opensRange _
  obtain ⟨y, hy⟩ : (A.chart i).baseMap x ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact ⟨x, rfl⟩
  rw [← hy, FiniteLocallyFreeSheaf.rank_fromSpec_apply _ hU]
  exact (E.finite_projective_sections_pushforward_poleSheaf (A.chart i) hn).2.2 y

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
