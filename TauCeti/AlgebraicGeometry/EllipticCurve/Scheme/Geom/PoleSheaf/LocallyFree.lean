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
pointed Weierstrass chart, which is affine, the sections of the direct image `π_*M` of any
`𝒪_E`-module `M` are the sections of `M` over `π⁻¹(U)`, and `π` identifies the functions on `U` with
the functions on `π⁻¹(U)`. A quasi-coherent sheaf with finitely generated projective sections over
an affine open cover is finite locally free
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_finite_projective_sections`), with rank
the rank of the sections (`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rank_fromSpec_apply`).
So `π_*M` is finite locally free of rank `d` as soon as the sections of `M` over the preimages of
the chart images are finitely generated projective of constant rank `d`
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.rank_pushforward_of_finite_projective_sections`).

For the pole sheaf, `π⁻¹(U)` is the projective model of the equation of the chart, and the sections
are the global sections of its pole sheaf. These form a finitely generated projective module of
constant rank `n` over the global functions on the model
(`WeierstrassCurve.finite_projective_globalSections_poleSheaf`).

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.finite_projective_sections_of_restrict_iso`: if the
  restriction of `M` to the model of a chart has finitely generated projective global sections of
  constant rank `d`, so do its sections over the preimage of the chart image.
* `EllipticCurveGeom.isFiniteLocallyFree_pushforward_of_finite_projective_sections`:
  if the sections of a quasi-coherent `M` over the preimage of every chart image are finitely
  generated projective, then `π_*M` is finite locally free.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.rank_pushforward_of_finite_projective_sections`:
  if they also have constant rank `d`, then `π_*M` has rank `d`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.finite_projective_sections_poleSheaf`: over the
  image `U` of the base of a chart, `Γ(π⁻¹(U), 𝒪_E(n[0]))` is a finitely generated projective
  `Γ(E, π⁻¹(U))`-module of constant rank `n`.
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

/-- **The sections over a chart of a module given by the model.** Let `U` be the image of the base
of a pointed Weierstrass chart of `E`, so that `π⁻¹(U)` is the projective model of the equation of
the chart. If the restriction of an `𝒪_E`-module `M` to the model is isomorphic to a module `M'`
whose global sections form a finitely generated projective module of constant rank `d` over the
global functions on the model, then the sections of `M` over `π⁻¹(U)` form a finitely generated
projective `Γ(E, π⁻¹(U))`-module of constant rank `d`. -/
theorem finite_projective_sections_of_restrict_iso (M : E.carrier.Modules)
    (c : PointedWeierstrassChart E.structureMap E.zero) {M' : c.equation.projModel.Modules}
    (e : M.restrict (c.modelIso.inv ≫ c.toTotal) ≅ M') {d : ℕ}
    (hM' : Module.Finite Γ(c.equation.projModel, ⊤) Γ(M', ⊤) ∧
      Module.Projective Γ(c.equation.projModel, ⊤) Γ(M', ⊤) ∧
      ∀ p : PrimeSpectrum Γ(c.equation.projModel, ⊤), Module.rankAtStalk Γ(M', ⊤) p = d) :
    Module.Finite Γ(E.carrier, E.structureMap ⁻¹ᵁ c.baseMap.opensRange)
        Γ(M, E.structureMap ⁻¹ᵁ c.baseMap.opensRange) ∧
      Module.Projective Γ(E.carrier, E.structureMap ⁻¹ᵁ c.baseMap.opensRange)
        Γ(M, E.structureMap ⁻¹ᵁ c.baseMap.opensRange) ∧
      ∀ p : PrimeSpectrum Γ(E.carrier, E.structureMap ⁻¹ᵁ c.baseMap.opensRange),
        Module.rankAtStalk Γ(M, E.structureMap ⁻¹ᵁ c.baseMap.opensRange) p = d := by
  let j := c.modelIso.inv ≫ c.toTotal
  obtain ⟨_, _, h₀⟩ := hM'
  -- the sections over `⊤` of the restriction along `j` are those of `M'`
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
  let e₂ : Γ(M.restrict j, ⊤)
      ≃ₛₗ[(σ : Γ(c.equation.projModel, ⊤) →+* Γ(E.carrier, j ''ᵁ ⊤))] Γ(M, j ''ᵁ ⊤) :=
    { AddEquiv.refl _ with map_smul' _ _ := rfl }
  have h₂ : Module.Finite Γ(E.carrier, j ''ᵁ ⊤) Γ(M, j ''ᵁ ⊤) ∧
      Module.Projective Γ(E.carrier, j ''ᵁ ⊤) Γ(M, j ''ᵁ ⊤) ∧
      ∀ p : PrimeSpectrum Γ(E.carrier, j ''ᵁ ⊤), Module.rankAtStalk Γ(M, j ''ᵁ ⊤) p = d := by
    refine ⟨e₂.toLinearMap.finite_of_surjective e₂.surjective, .of_equiv e₂, fun p ↦ ?_⟩
    rw [e₂.rankAtStalk_eq, ← h₁, h₀]
  rwa [c.image_top_modelIso_inv_toTotal] at h₂

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
          n :=
  E.finite_projective_sections_of_restrict_iso _ c (E.nonempty_restrict_poleSheaf_iso c n).some
    (c.equation.finite_projective_globalSections_poleSheaf hn)

/-- **The sections of a direct image over a chart.** Over the image `U` of the base of a pointed
Weierstrass chart of `E`, if the sections of an `𝒪_E`-module `M` over `π⁻¹(U)` form a finitely
generated projective `Γ(E, π⁻¹(U))`-module, then the sections of `π_*M` over `U` form a finitely
generated projective `Γ(S, U)`-module: they are the same sections, and `π` identifies the functions
on `U` with the functions on `π⁻¹(U)`. -/
theorem finite_projective_sections_pushforward_of_finite_projective_sections
    (M : E.carrier.Modules) (c : PointedWeierstrassChart E.structureMap E.zero)
    (hM : Module.Finite Γ(E.carrier, E.structureMap ⁻¹ᵁ c.baseMap.opensRange)
        Γ(M, E.structureMap ⁻¹ᵁ c.baseMap.opensRange) ∧
      Module.Projective Γ(E.carrier, E.structureMap ⁻¹ᵁ c.baseMap.opensRange)
        Γ(M, E.structureMap ⁻¹ᵁ c.baseMap.opensRange)) :
    Module.Finite Γ(S, c.baseMap.opensRange)
        Γ((pushforward E.structureMap).obj M, c.baseMap.opensRange) ∧
      Module.Projective Γ(S, c.baseMap.opensRange)
        Γ((pushforward E.structureMap).obj M, c.baseMap.opensRange) := by
  let U := c.baseMap.opensRange
  obtain ⟨_, _⟩ := hM
  have := c.isIso_app_opensRange
  let σ : Γ(S, U) ≃+* Γ(E.carrier, E.structureMap ⁻¹ᵁ U) :=
    (asIso (E.structureMap.app U)).commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  -- by the definition of `Scheme.Modules.pushforward`, `Γ(S, U)` acts on the sections of the direct
  -- image through `π.app U`
  let e : Γ((pushforward E.structureMap).obj M, U)
      ≃ₛₗ[(σ : Γ(S, U) →+* Γ(E.carrier, E.structureMap ⁻¹ᵁ U))]
      Γ(M, E.structureMap ⁻¹ᵁ U) :=
    { AddEquiv.refl _ with map_smul' _ _ := rfl }
  exact ⟨e.symm.toLinearMap.finite_of_surjective e.symm.surjective, .of_equiv e.symm⟩

/-- **The rank of the sections of a direct image over a chart.** Over the image `U` of the base of a
pointed Weierstrass chart of `E`, if the sections of an `𝒪_E`-module `M` over `π⁻¹(U)` form a
finitely generated projective `Γ(E, π⁻¹(U))`-module of constant rank `d`, then the sections of
`π_*M` over `U` have constant rank `d` over `Γ(S, U)`. -/
theorem rankAtStalk_sections_pushforward_of_finite_projective_sections
    (M : E.carrier.Modules) (c : PointedWeierstrassChart E.structureMap E.zero) {d : ℕ}
    (hM : Module.Finite Γ(E.carrier, E.structureMap ⁻¹ᵁ c.baseMap.opensRange)
        Γ(M, E.structureMap ⁻¹ᵁ c.baseMap.opensRange) ∧
      Module.Projective Γ(E.carrier, E.structureMap ⁻¹ᵁ c.baseMap.opensRange)
        Γ(M, E.structureMap ⁻¹ᵁ c.baseMap.opensRange) ∧
      ∀ p : PrimeSpectrum Γ(E.carrier, E.structureMap ⁻¹ᵁ c.baseMap.opensRange),
        Module.rankAtStalk Γ(M, E.structureMap ⁻¹ᵁ c.baseMap.opensRange) p = d)
    (p : PrimeSpectrum Γ(S, c.baseMap.opensRange)) :
    Module.rankAtStalk Γ((pushforward E.structureMap).obj M, c.baseMap.opensRange) p = d := by
  let U := c.baseMap.opensRange
  obtain ⟨_, _, h⟩ := hM
  have := c.isIso_app_opensRange
  let σ : Γ(S, U) ≃+* Γ(E.carrier, E.structureMap ⁻¹ᵁ U) :=
    (asIso (E.structureMap.app U)).commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  let e : Γ((pushforward E.structureMap).obj M, U)
      ≃ₛₗ[(σ : Γ(S, U) →+* Γ(E.carrier, E.structureMap ⁻¹ᵁ U))]
      Γ(M, E.structureMap ⁻¹ᵁ U) :=
    { AddEquiv.refl _ with map_smul' _ _ := rfl }
  rw [e.symm.rankAtStalk_eq, h]

/-- **A direct image with finite projective sections over the charts is finite locally free.** For
an elliptic curve `π : E ⟶ S` and a quasi-coherent `𝒪_E`-module `M` whose sections over the
preimage `π⁻¹(U)` of the image `U` of the base of every pointed Weierstrass chart form a finitely
generated projective `Γ(E, π⁻¹(U))`-module, the direct image `π_*M` is a finite locally free
`𝒪_S`-module. -/
theorem isFiniteLocallyFree_pushforward_of_finite_projective_sections (M : E.carrier.Modules)
    [M.IsQuasicoherent]
    (hM : ∀ c : PointedWeierstrassChart E.structureMap E.zero,
      Module.Finite Γ(E.carrier, E.structureMap ⁻¹ᵁ c.baseMap.opensRange)
          Γ(M, E.structureMap ⁻¹ᵁ c.baseMap.opensRange) ∧
        Module.Projective Γ(E.carrier, E.structureMap ⁻¹ᵁ c.baseMap.opensRange)
          Γ(M, E.structureMap ⁻¹ᵁ c.baseMap.opensRange)) :
    isFiniteLocallyFree S ((pushforward E.structureMap).obj M) := by
  obtain ⟨A⟩ := E.localModel
  have (i : A.index) := (E.finite_projective_sections_pushforward_of_finite_projective_sections M
    (A.chart i) (hM (A.chart i))).1
  have (i : A.index) := (E.finite_projective_sections_pushforward_of_finite_projective_sections M
    (A.chart i) (hM (A.chart i))).2
  refine isFiniteLocallyFree_of_finite_projective_sections _
    (U := fun i ↦ (A.chart i).baseMap.opensRange)
    (fun i ↦ isAffineOpen_opensRange _) (eq_top_iff.mpr fun s _ ↦ ?_)
  obtain ⟨i, x, rfl⟩ := A.covers s
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, x, rfl⟩

/-- **A direct image with finite projective sections of rank `d` over the charts has rank `d`.** For
an elliptic curve `π : E ⟶ S` and a quasi-coherent `𝒪_E`-module `M` whose sections over the
preimage `π⁻¹(U)` of the image `U` of the base of every pointed Weierstrass chart form a finitely
generated projective `Γ(E, π⁻¹(U))`-module of constant rank `d`, the finite locally free sheaf
`π_*M` has rank `d` at every point of `S`. -/
theorem rank_pushforward_of_finite_projective_sections (M : E.carrier.Modules)
    [M.IsQuasicoherent] {d : ℕ}
    (hM : ∀ c : PointedWeierstrassChart E.structureMap E.zero,
      Module.Finite Γ(E.carrier, E.structureMap ⁻¹ᵁ c.baseMap.opensRange)
          Γ(M, E.structureMap ⁻¹ᵁ c.baseMap.opensRange) ∧
        Module.Projective Γ(E.carrier, E.structureMap ⁻¹ᵁ c.baseMap.opensRange)
          Γ(M, E.structureMap ⁻¹ᵁ c.baseMap.opensRange) ∧
        ∀ p : PrimeSpectrum Γ(E.carrier, E.structureMap ⁻¹ᵁ c.baseMap.opensRange),
          Module.rankAtStalk Γ(M, E.structureMap ⁻¹ᵁ c.baseMap.opensRange) p = d)
    (s : S) :
    FiniteLocallyFreeSheaf.rank ⟨_, E.isFiniteLocallyFree_pushforward_of_finite_projective_sections
      M fun c ↦ ⟨(hM c).1, (hM c).2.1⟩⟩ s = d := by
  obtain ⟨A⟩ := E.localModel
  obtain ⟨i, x, rfl⟩ := A.covers s
  have hU : IsAffineOpen (A.chart i).baseMap.opensRange := isAffineOpen_opensRange _
  obtain ⟨y, hy⟩ : (A.chart i).baseMap x ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact ⟨x, rfl⟩
  rw [← hy, FiniteLocallyFreeSheaf.rank_fromSpec_apply _ hU]
  exact E.rankAtStalk_sections_pushforward_of_finite_projective_sections M (A.chart i) (hM _) y

/-- **`π_*𝒪_E(n[0])` is finite locally free.** For an elliptic curve `π : E ⟶ S` and `n > 0`, the
direct image of the pole sheaf `𝒪_E(n[0])` is a finite locally free `𝒪_S`-module. -/
theorem isFiniteLocallyFree_pushforward_poleSheaf {n : ℕ} (hn : 0 < n) :
    isFiniteLocallyFree S ((pushforward E.structureMap).obj (E.poleSheaf n).obj) :=
  E.isFiniteLocallyFree_pushforward_of_finite_projective_sections _ fun c ↦
    ⟨(E.finite_projective_sections_poleSheaf c hn).1,
      (E.finite_projective_sections_poleSheaf c hn).2.1⟩

/-- **`π_*𝒪_E(n[0])` is locally free of rank `n`.** For an elliptic curve `π : E ⟶ S` and `n > 0`,
the finite locally free sheaf `π_*𝒪_E(n[0])` has rank `n` at every point of `S`. -/
theorem rank_pushforward_poleSheaf {n : ℕ} (hn : 0 < n) (s : S) :
    FiniteLocallyFreeSheaf.rank ⟨_, E.isFiniteLocallyFree_pushforward_poleSheaf hn⟩ s = n :=
  E.rank_pushforward_of_finite_projective_sections _
    (fun c ↦ E.finite_projective_sections_poleSheaf c hn) s

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
