/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.PoleSheaf.Cohomology
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.GlobalSections
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PoleSheaf

/-!
# The higher direct image `R¹π_*𝒪_E(n[0])` vanishes

Let `E` be an elliptic curve over a scheme `S`, with structure morphism `π : E ⟶ S`, and let
`n > 0`. This file shows that `R¹π_*𝒪_E(n[0]) = 0`
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.isZero_higherDirectImage_one_poleSheaf`).

On a pointed Weierstrass chart `c` of `E`, the restriction of `E` to the base of `c` is the
projective model of an elliptic Weierstrass curve over a ring, and `𝒪_E(n[0])` restricts to its
pole sheaf (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.nonempty_restrict_poleSheaf_iso`), whose
first cohomology vanishes (`WeierstrassCurve.subsingleton_cohomology_one_poleSheaf`). So
`H¹(π⁻¹(U), 𝒪_E(n[0])) = 0` for the image `U` of the base of every chart. These images, for the
restrictions of the charts of an atlas to the affine opens of their bases, form a basis of the
topology of `S`, and a higher direct image vanishes when the cohomology of the preimages of the
members of a basis does.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.subsingleton_cohomologyOn_one_poleSheaf`: over the
  image `U` of the base of a chart, `H¹(π⁻¹(U), 𝒪_E(n[0])) = 0`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isZero_higherDirectImage_one_poleSheaf`:
  `R¹π_*𝒪_E(n[0]) = 0`.

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

/-- On a pointed Weierstrass chart `c` of `E`, the restriction of `𝒪_E(n[0])` along the open
immersion of the projective model of the equation of `c` into `E` is the pole sheaf `𝒪(n[0])` of
the model. -/
theorem nonempty_restrict_poleSheaf_iso (c : PointedWeierstrassChart E.structureMap E.zero)
    (n : ℕ) :
    Nonempty ((E.poleSheaf n).obj.restrict (c.modelIso.inv ≫ c.toTotal) ≅
      (c.equation.poleSheaf n).obj) := by
  have h : LineBundleClass.pullback (c.modelIso.inv ≫ c.toTotal)
      (LineBundleClass.mk (E.poleSheaf n)) = LineBundleClass.mk (c.equation.poleSheaf n) := by
    rw [← LineBundleClass.pullback_comp, E.pullback_mk_poleSheaf_toTotal,
      LineBundleClass.pullback_comp, Iso.inv_hom_id, LineBundleClass.pullback_id]
  rw [LineBundleClass.pullback_mk, LineBundleClass.mk_eq_mk_iff] at h
  obtain ⟨e⟩ := h
  exact ⟨(restrictFunctorIsoPullback _).app _ ≪≫ e⟩

/-- **`H¹` of `𝒪_E(n[0])` vanishes over a chart.** Over the image `U` of the base of a pointed
Weierstrass chart of `E`, `H¹(π⁻¹(U), 𝒪_E(n[0])) = 0` for `n > 0`: `π⁻¹(U)` is the projective
model of an elliptic Weierstrass curve, on which `𝒪_E(n[0])` is the pole sheaf `𝒪(n[0])`. -/
theorem subsingleton_cohomologyOn_one_poleSheaf
    (c : PointedWeierstrassChart E.structureMap E.zero) {n : ℕ} (hn : 0 < n) :
    Subsingleton (cohomologyOn (E.poleSheaf n).obj 1
      (E.structureMap ⁻¹ᵁ c.baseMap.opensRange)) := by
  obtain ⟨e⟩ := E.nonempty_restrict_poleSheaf_iso c n
  have : Subsingleton ((cohomologyFunctor _ 1).obj (c.equation.poleSheaf n).obj) :=
    c.equation.subsingleton_cohomology_one_poleSheaf hn
  rw [← c.opensRange_toTotal, ← Scheme.Hom.opensRange_comp_of_isIso c.modelIso.inv]
  exact ((cohomologyOnOpensRangeIso _ _ 1 ≪≫
    (cohomologyFunctor _ 1).mapIso e).addCommGroupIsoToAddEquiv).subsingleton

/-- **`R¹π_*𝒪_E(n[0]) = 0`.** For an elliptic curve `π : E ⟶ S` and `n > 0`, the first higher
direct image of the pole sheaf `𝒪_E(n[0])` vanishes. -/
theorem isZero_higherDirectImage_one_poleSheaf {n : ℕ} (hn : 0 < n) :
    IsZero ((E.structureMap.higherDirectImage 1).obj (E.poleSheaf n).obj) := by
  obtain ⟨A⟩ := E.localModel
  refine E.structureMap.isZero_higherDirectImage_succ_of_isBasis _ 0
    A.isBasis_range_opensRange_restrict ?_
  rintro _ ⟨p, rfl⟩
  exact E.subsingleton_cohomologyOn_one_poleSheaf ((A.chart p.1).restrict p.2) hn

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
