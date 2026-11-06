/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PoleSheaf.FiltrationQuotient
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.CokernelSections

/-!
# The cokernels of the pole filtration of an elliptic curve

Let `E` be an elliptic curve over a scheme `S`, with structure morphism `π : E ⟶ S`, and let
`0 < m ≤ n`. The direct image `π_*ℒ_m ⟶ π_*ℒ_n` of the inclusion of pole sheaves is a monomorphism
of quasi-coherent `𝒪_S`-modules. This file shows that its cokernel is finite locally free of rank
`n - m` (`EllipticCurveGeom.isFiniteLocallyFree_cokernel_pushforward_poleSheafMap` and
`EllipticCurveGeom.rank_cokernel_pushforward_poleSheafMap`): the successive quotients of the pole
filtration of `π_*ℒ_n` are vector bundles.

Over the image `U` of the base of a pointed Weierstrass chart, which is affine, the sections of the
cokernel are the quotient of `Γ(U, π_*ℒ_n)` by the image of `Γ(U, π_*ℒ_m)`
(`AlgebraicGeometry.Scheme.Modules.cokernelSectionsEquiv`), and that quotient is finitely generated
projective of constant rank `n - m`
(`EllipticCurveGeom.projective_quotient_range_pushforward_poleSheafMap` and
`EllipticCurveGeom.rankAtStalk_quotient_range_pushforward_poleSheafMap`). The chart images cover
`S`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1 and 2.2.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

open Scheme.Modules

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) {m n : ℕ}

/-- **The sections of the cokernels of the pole filtration over a chart.** Over the image `U` of the
base of a pointed Weierstrass chart of `E`, for `0 < m ≤ n`, the sections over `U` of the cokernel
of `π_*ℒ_m ⟶ π_*ℒ_n` form a finitely generated projective `Γ(S, U)`-module of constant rank
`n - m`. -/
theorem finite_projective_sections_cokernel_pushforward_poleSheafMap
    (c : PointedWeierstrassChart E.structureMap E.zero) (hm : 0 < m) (h : m ≤ n) :
    Module.Finite Γ(S, c.baseMap.opensRange)
        Γ(cokernel ((pushforward E.structureMap).map (E.poleSheafMap h).hom),
          c.baseMap.opensRange) ∧
      Module.Projective Γ(S, c.baseMap.opensRange)
        Γ(cokernel ((pushforward E.structureMap).map (E.poleSheafMap h).hom),
          c.baseMap.opensRange) ∧
      ∀ p : PrimeSpectrum Γ(S, c.baseMap.opensRange),
        Module.rankAtStalk Γ(cokernel ((pushforward E.structureMap).map (E.poleSheafMap h).hom),
          c.baseMap.opensRange) p = n - m := by
  have := E.mono_pushforward_map_poleSheafMap h
  let e := cokernelSectionsEquiv ((pushforward E.structureMap).map (E.poleSheafMap h).hom)
    (isAffineOpen_opensRange c.baseMap)
  have hn := E.finite_projective_sections_poleSheaf c (hm.trans_le h)
  have := (E.finite_projective_sections_pushforward_of_finite_projective_sections
    (E.poleSheaf n).obj c ⟨hn.1, hn.2.1⟩).1
  have := E.projective_quotient_range_pushforward_poleSheafMap c hm h
  refine ⟨.equiv e, .of_equiv e, fun p ↦ ?_⟩
  rw [← congrFun (Module.rankAtStalk_eq_of_equiv e) p,
    E.rankAtStalk_quotient_range_pushforward_poleSheafMap c hm h]

/-- **The cokernels of the pole filtration are finite locally free.** For an elliptic curve
`π : E ⟶ S` and `0 < m ≤ n`, the cokernel of the direct image `π_*ℒ_m ⟶ π_*ℒ_n` of the inclusion
of pole sheaves is a finite locally free `𝒪_S`-module. -/
theorem isFiniteLocallyFree_cokernel_pushforward_poleSheafMap (hm : 0 < m) (h : m ≤ n) :
    isFiniteLocallyFree S (cokernel ((pushforward E.structureMap).map (E.poleSheafMap h).hom)) := by
  obtain ⟨A⟩ := E.localModel
  have (i : A.index) :=
    (E.finite_projective_sections_cokernel_pushforward_poleSheafMap (A.chart i) hm h).1
  have (i : A.index) :=
    (E.finite_projective_sections_cokernel_pushforward_poleSheafMap (A.chart i) hm h).2.1
  refine isFiniteLocallyFree_of_finite_projective_sections _
    (U := fun i ↦ (A.chart i).baseMap.opensRange)
    (fun i ↦ isAffineOpen_opensRange _) (eq_top_iff.mpr fun s _ ↦ ?_)
  obtain ⟨i, x, rfl⟩ := A.covers s
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, x, rfl⟩

/-- **The cokernels of the pole filtration have rank `n - m`.** For an elliptic curve `π : E ⟶ S`
and `0 < m ≤ n`, the finite locally free cokernel of `π_*ℒ_m ⟶ π_*ℒ_n` has rank `n - m` at every
point of `S`. -/
theorem rank_cokernel_pushforward_poleSheafMap (hm : 0 < m) (h : m ≤ n) (s : S) :
    FiniteLocallyFreeSheaf.rank
      ⟨_, E.isFiniteLocallyFree_cokernel_pushforward_poleSheafMap hm h⟩ s = n - m := by
  obtain ⟨A⟩ := E.localModel
  obtain ⟨i, x, rfl⟩ := A.covers s
  have hU : IsAffineOpen (A.chart i).baseMap.opensRange := isAffineOpen_opensRange _
  obtain ⟨y, hy⟩ : (A.chart i).baseMap x ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact ⟨x, rfl⟩
  rw [← hy, FiniteLocallyFreeSheaf.rank_fromSpec_apply _ hU]
  exact (E.finite_projective_sections_cokernel_pushforward_poleSheafMap (A.chart i) hm h).2.2 y

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
