/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PoleSheaf
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PositiveDegree.DirectImage

/-!
# The pole sheaves `𝒪_E(n[0])` have degree `n` on every fibre, and `R¹π_*𝒪_E(n[0])` vanishes

Let `E` be an elliptic curve over a scheme `S`, with structure morphism `π : E ⟶ S`. This file
shows that the pole sheaf `𝒪_E(n[0])` has degree `n` on the fibre of `E` over every field-valued
point of `S`
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.eulerDegree_pullback_snd_poleSheaf`), and hence, by
the positive-degree theorem, that `R¹π_*𝒪_E(n[0]) = 0` for `n > 0`
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.isZero_higherDirectImage_one_poleSheaf`).

On a pointed Weierstrass chart `c` of `E`, the restriction of `E` to the base of `c` is the
projective model of an elliptic Weierstrass curve over a ring, and `𝒪_E(n[0])` restricts to its
pole sheaf (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.nonempty_restrict_poleSheaf_iso`). A
field-valued point of `S` factors through the base of a chart, over which the fibre of `E` is the
projective model over the field, where the pole sheaf has degree `n`
(`WeierstrassCurve.eulerDegree_pullback_poleSheaf`).

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.nonempty_restrict_poleSheaf_iso`: on a chart,
  `𝒪_E(n[0])` restricts to the pole sheaf of the Weierstrass model.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.eulerDegree_pullback_snd_poleSheaf`: `𝒪_E(n[0])`
  has degree `n` on every fibre.
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

/-- On a pointed Weierstrass chart `c` of `E`, the class of `𝒪_E(n[0])` pulls back along the open
immersion of the projective model of the equation of `c` into `E` to the class of the pole sheaf
`𝒪(n[0])` of the model. -/
theorem pullback_mk_poleSheaf_modelIso_inv_toTotal
    (c : PointedWeierstrassChart E.structureMap E.zero) (n : ℕ) :
    LineBundleClass.pullback (c.modelIso.inv ≫ c.toTotal) (LineBundleClass.mk (E.poleSheaf n)) =
      LineBundleClass.mk (c.equation.poleSheaf n) := by
  rw [← LineBundleClass.pullback_comp, E.pullback_mk_poleSheaf_toTotal,
    LineBundleClass.pullback_comp, Iso.inv_hom_id, LineBundleClass.pullback_id]

/-- On a pointed Weierstrass chart `c` of `E`, the restriction of `𝒪_E(n[0])` along the open
immersion of the projective model of the equation of `c` into `E` is the pole sheaf `𝒪(n[0])` of
the model. -/
theorem nonempty_restrict_poleSheaf_iso (c : PointedWeierstrassChart E.structureMap E.zero)
    (n : ℕ) :
    Nonempty ((E.poleSheaf n).obj.restrict (c.modelIso.inv ≫ c.toTotal) ≅
      (c.equation.poleSheaf n).obj) := by
  have h := E.pullback_mk_poleSheaf_modelIso_inv_toTotal c n
  rw [LineBundleClass.pullback_mk, LineBundleClass.mk_eq_mk_iff] at h
  obtain ⟨e⟩ := h
  exact ⟨(restrictFunctorIsoPullback _).app _ ≪≫ e⟩

/-- **`𝒪_E(n[0])` has degree `n` on every fibre.** For every point `ξ : Spec K ⟶ S` with values in
a field, the pullback of `𝒪_E(n[0])` to the fibre `Spec K ×_S E` has degree `n`: the point factors
through the base of a chart, over which the fibre is the projective model of a Weierstrass
equation over `K` and `𝒪_E(n[0])` is its pole sheaf. -/
theorem eulerDegree_pullback_snd_poleSheaf {K : Type u} [Field K] (ξ : Spec (.of K) ⟶ S)
    (n : ℕ) :
    letI : (pullback ξ E.structureMap).Over (Spec (.of K)) := ⟨pullback.fst _ _⟩
    LineBundleClass.eulerDegree K
      (LineBundleClass.pullback (pullback.snd ξ E.structureMap) (.mk (E.poleSheaf n))) = n := by
  obtain ⟨A⟩ := E.localModel
  obtain ⟨i, f, rfl⟩ := A.exists_eq_specMap_comp_baseMap ξ
  rw [E.eulerDegree_pullback_snd_specMap_comp, E.pullback_mk_poleSheaf_modelIso_inv_toTotal,
    LineBundleClass.pullback_mk, LineBundleClass.eulerDegree_mk,
    WeierstrassCurve.eulerDegree_pullback_poleSheaf]

/-- **`R¹π_*𝒪_E(n[0]) = 0`.** For an elliptic curve `π : E ⟶ S` and `n > 0`, the first higher
direct image of the pole sheaf `𝒪_E(n[0])` vanishes. This is the positive-degree theorem
`TauCeti.AlgebraicGeometry.EllipticCurveGeom.isZero_higherDirectImage_one_of_forall_eulerDegree_pos`
for a line bundle of degree `n` on every fibre. -/
theorem isZero_higherDirectImage_one_poleSheaf {n : ℕ} (hn : 0 < n) :
    IsZero ((E.structureMap.higherDirectImage 1).obj (E.poleSheaf n).obj) :=
  isZero_higherDirectImage_one_of_forall_eulerDegree_pos fun Ω _ _ ξ ↦ by
    rw [E.eulerDegree_pullback_snd_poleSheaf ξ n]
    exact_mod_cast hn

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
