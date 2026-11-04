/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.PoleSheaf
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PointsDivisor
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
public import TauCeti.AlgebraicGeometry.LineBundle.Dual
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# The divisors `n[0]` and the pole sheaves `𝒪_E(n[0])` of an elliptic curve

Let `E` be an elliptic curve over a scheme `S`, with structure morphism `π : E ⟶ S` and zero
section `0 : S ⟶ E`. The zero section of the smooth separated curve `π` cuts out a relative
effective Cartier divisor `[0]` (`EllipticCurveGeom.zeroDivisor`), the ideal sheaf of `0`. Its
multiples `n[0]` are represented by the powers of that ideal sheaf; they are relative effective
Cartier divisors, finite locally free of constant rank `n` over `S`.

The **pole sheaf** `ℒ_n = 𝒪_E(n[0])` (`EllipticCurveGeom.poleSheaf`) is the line bundle of `n[0]`,
the dual of the invertible ideal sheaf `𝒪_E(-n[0])` of `n[0]`. Its class in the Picard group is the
`n`-th power of the class of `𝒪_E([0])`, so `ℒ_n ≅ ℒ_1^{⊗ n}`, and `ℒ_0` is trivial.

All of this commutes with arbitrary base change: for a pullback square of elliptic curves over
`S' ⟶ S` compatible with the zero sections, the divisor `n[0]` of the base change is the inverse
image of `n[0]`, and the pole sheaf of the base change is the pullback of `ℒ_n`. On a pointed
Weierstrass chart of `E`, the divisor `n[0]` is carried to the divisor `n[0]` of the projective
Weierstrass model (`WeierstrassCurve.zeroSectionDivisor`), whose ideal is described on the
standard affine charts in `TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.Basic`, and
`ℒ_n` to the pole sheaf `WeierstrassCurve.poleSheaf` of the model, whose cohomology over a field
is computed in `TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.PoleSheaf`.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.zeroDivisor E`: the divisor `[0]` of `E`, as the
  ideal sheaf of the zero section.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleSheaf E n`: the line bundle `𝒪_E(n[0])`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isRelativeEffectiveCartier_zeroDivisor_pow`:
  `n[0]` is a relative effective Cartier divisor on `E` over `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.finrank_zeroDivisor_pow`: `n[0]` is finite locally
  free of rank `n` over `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.zeroDivisor_pow_comap_of_isPullback`: `n[0]`
  commutes with base change.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.zeroDivisor_pow_comap_toTotal`: on a pointed
  Weierstrass chart, `n[0]` is the divisor `n[0]` of the projective Weierstrass model.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mk_poleSheaf`: the class of `𝒪_E(n[0])` is the
  `n`-th power of the class of `𝒪_E([0])`, the dual of the ideal sheaf of the zero section
  (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.mk_poleSheaf_one`).
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.pullback_mk_poleSheaf_toTotal`: on a pointed
  Weierstrass chart, `𝒪_E(n[0])` is the pole sheaf `WeierstrassCurve.poleSheaf` of the model.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.pullback_mk_poleSheaf_of_isPullback`: the pole
  sheaves commute with base change.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 1.2 and 2.1.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- The divisor `[0]` of an elliptic curve `E` over `S`: the ideal sheaf of the zero section. Its
powers represent the multiples `n[0]`. -/
noncomputable def zeroDivisor : E.carrier.IdealSheafData :=
  E.zero.ker

/-- The divisor `[0]` is the ideal sheaf of the zero section. -/
theorem zeroDivisor_def : E.zeroDivisor = E.zero.ker :=
  (rfl)

/-- The divisor `n[0]` is the divisor `[0] + ⋯ + [0]` of the family of `n` copies of the zero
point. -/
theorem zeroDivisor_pow_eq_pointsDivisor (n : ℕ) :
    E.zeroDivisor ^ n = E.pointsDivisor fun _ : Fin n ↦ Over.homMk E.zero (by simp) := by
  simp [pointsDivisor_def, zeroDivisor_def]

/-- **The zero section cuts out a relative effective Cartier divisor** `[0]` on `E` over `S`. -/
theorem isRelativeEffectiveCartier_zeroDivisor :
    E.zeroDivisor.IsRelativeEffectiveCartier E.structureMap :=
  Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension (f := E.structureMap)
    E.zero E.zero_comp

/-- **Every multiple `n[0]` is a relative effective Cartier divisor** on `E` over `S`. -/
theorem isRelativeEffectiveCartier_zeroDivisor_pow (n : ℕ) :
    (E.zeroDivisor ^ n).IsRelativeEffectiveCartier E.structureMap :=
  isRelativeEffectiveCartier_pow E.isRelativeEffectiveCartier_zeroDivisor n

/-- The divisor `n[0]` is finite over the base. -/
instance isFinite_zeroDivisor_pow (n : ℕ) :
    IsFinite ((E.zeroDivisor ^ n).subschemeι ≫ E.structureMap) := by
  rw [zeroDivisor_pow_eq_pointsDivisor]
  infer_instance

/-- The divisor `n[0]` is flat over the base. -/
instance flat_zeroDivisor_pow (n : ℕ) :
    Flat ((E.zeroDivisor ^ n).subschemeι ≫ E.structureMap) :=
  (E.isRelativeEffectiveCartier_zeroDivisor_pow n).flat

/-- The divisor `n[0]` is locally of finite presentation over the base. Together with finiteness
and flatness, this makes it finite locally free. -/
instance locallyOfFinitePresentation_zeroDivisor_pow (n : ℕ) :
    LocallyOfFinitePresentation ((E.zeroDivisor ^ n).subschemeι ≫ E.structureMap) := by
  rw [zeroDivisor_pow_eq_pointsDivisor]
  infer_instance

/-- **The divisor `n[0]` has rank `n`** over every point of the base. -/
@[simp]
theorem finrank_zeroDivisor_pow (n : ℕ) (s : S) :
    ((E.zeroDivisor ^ n).subschemeι ≫ E.structureMap).finrank s = n := by
  have h := E.finrank_pointsDivisor (fun _ : Fin n ↦ Over.homMk E.zero (by simp)) s
  rw [← zeroDivisor_pow_eq_pointsDivisor, Fintype.card_fin] at h
  exact h

/-! ### Base change and Weierstrass charts -/

section BaseChange

variable {E} {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S}

/-- **The divisor `[0]` commutes with base change**: for a pullback square of elliptic curves over
`f : S' ⟶ S` compatible with the zero sections, the divisor `[0]` of `E'` is the inverse image
of the divisor `[0]` of `E`. -/
theorem zeroDivisor_comap_of_isPullback (hg : IsPullback g E'.structureMap E.structureMap f)
    (h0 : E'.zero ≫ g = f ≫ E.zero) :
    E'.zeroDivisor = E.zeroDivisor.comap g := by
  have := E.zero.isClosedImmersion_of_comp_eq_id (f := E.structureMap) E.zero_comp
  refine Scheme.IdealSheafData.ker_eq_comap_of_isPullback (g := f) _ ?_
  -- The square `0' ≫ g = f ≫ 0` is the left half of a pasted square whose outer rectangle, the
  -- composite of the zero sections with the structure morphisms, is the identity square over `f`.
  refine IsPullback.of_right ?_ h0 hg.flip
  rw [E'.zero_comp, E.zero_comp]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- **The divisors `n[0]` commute with base change.** -/
theorem zeroDivisor_pow_comap_of_isPullback (hg : IsPullback g E'.structureMap E.structureMap f)
    (h0 : E'.zero ≫ g = f ≫ E.zero) (n : ℕ) :
    E'.zeroDivisor ^ n = (E.zeroDivisor ^ n).comap g := by
  rw [zeroDivisor_comap_of_isPullback hg h0, Scheme.IdealSheafData.comap_pow]

end BaseChange

/-- **On a pointed Weierstrass chart, `[0]` is the zero-section divisor of the model.** The inverse
image of `[0]` in the restriction of `E` to the base of the chart is the inverse image, along the
isomorphism with the projective model `projModel W` of the equation of the chart, of the divisor
`[0 : 1 : 0]` of `projModel W`. -/
theorem zeroDivisor_comap_toTotal (c : PointedWeierstrassChart E.structureMap E.zero) :
    E.zeroDivisor.comap c.toTotal = c.equation.zeroSectionDivisor.comap c.modelIso.hom := by
  have := E.zero.isClosedImmersion_of_comp_eq_id (f := E.structureMap) E.zero_comp
  have := c.equation.isClosedImmersion_projModelZero
  rw [zeroDivisor_def, WeierstrassCurve.zeroSectionDivisor_def,
    ← Scheme.IdealSheafData.ker_eq_comap_of_isPullback (g := c.baseMap) (i' := c.pulledZero) _ ?_,
    ← Scheme.IdealSheafData.ker_eq_comap_of_isPullback (g := c.baseIso.hom) (i' := c.pulledZero) _
      (IsPullback.of_vert_isIso ⟨c.modelIso_zero⟩)]
  -- The square `0_c ≫ toTotal = baseMap ≫ 0` is the left half of a pasted square whose outer
  -- rectangle, the composite of the zero sections with the structure morphisms, is the identity
  -- square over `baseMap`.
  refine IsPullback.of_right ?_ c.pulledZero_toTotal c.isPullback.flip
  rw [c.pulledZero_toBase, E.zero_comp]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- **On a pointed Weierstrass chart, `n[0]` is the divisor `n[0]` of the model.** -/
theorem zeroDivisor_pow_comap_toTotal (c : PointedWeierstrassChart E.structureMap E.zero)
    (n : ℕ) :
    (E.zeroDivisor ^ n).comap c.toTotal =
      (c.equation.zeroSectionDivisor ^ n).comap c.modelIso.hom := by
  rw [Scheme.IdealSheafData.comap_pow, Scheme.IdealSheafData.comap_pow, zeroDivisor_comap_toTotal]

/-! ### The pole sheaves `𝒪_E(n[0])` -/

/-- The **pole sheaf** `ℒ_n = 𝒪_E(n[0])` of an elliptic curve `E`: the line bundle of the divisor
`n[0]`, the dual of the invertible ideal sheaf `𝒪_E(-n[0])` of `n[0]`. -/
noncomputable def poleSheaf (n : ℕ) : InvertibleSheaf E.carrier :=
  InvertibleSheaf.dual
    (E.isRelativeEffectiveCartier_zeroDivisor_pow n).isEffectiveCartier.toInvertibleSheaf

/-- The pole sheaf `𝒪_E(n[0])` is the dual of the ideal sheaf of `n[0]`. -/
theorem poleSheaf_def (n : ℕ) :
    E.poleSheaf n = InvertibleSheaf.dual
      (Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf
        (E.isRelativeEffectiveCartier_zeroDivisor_pow n).isEffectiveCartier) :=
  (rfl)

/-- The pole sheaf `𝒪_E([0])` is the dual of the ideal sheaf of the zero section, on line-bundle
classes. -/
theorem mk_poleSheaf_one :
    LineBundleClass.mk (E.poleSheaf 1) =
      (LineBundleClass.mk (Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf
        E.isRelativeEffectiveCartier_zeroDivisor.isEffectiveCartier))⁻¹ := by
  rw [poleSheaf_def, ← LineBundleClass.inv_mk, LineBundleClass.mk_toInvertibleSheaf_congr _
    E.isRelativeEffectiveCartier_zeroDivisor.isEffectiveCartier (pow_one _)]

/-- **`𝒪_E(n[0]) ≅ 𝒪_E([0])^{⊗ n}`**, on line-bundle classes. -/
theorem mk_poleSheaf (n : ℕ) :
    LineBundleClass.mk (E.poleSheaf n) = LineBundleClass.mk (E.poleSheaf 1) ^ n := by
  rw [mk_poleSheaf_one, poleSheaf_def, ← LineBundleClass.inv_mk,
    LineBundleClass.mk_toInvertibleSheaf_pow
      E.isRelativeEffectiveCartier_zeroDivisor.isEffectiveCartier, inv_pow]

/-- The pole sheaf `𝒪_E(0[0])` is trivial. -/
@[simp]
theorem mk_poleSheaf_zero : LineBundleClass.mk (E.poleSheaf 0) = 1 := by
  rw [mk_poleSheaf, pow_zero]

/-- `𝒪_E((m + n)[0]) ≅ 𝒪_E(m[0]) ⊗ 𝒪_E(n[0])`, on line-bundle classes. -/
theorem mk_poleSheaf_add (m n : ℕ) :
    LineBundleClass.mk (E.poleSheaf (m + n)) =
      LineBundleClass.mk (E.poleSheaf m) * LineBundleClass.mk (E.poleSheaf n) := by
  rw [E.mk_poleSheaf (m + n), E.mk_poleSheaf m, E.mk_poleSheaf n, pow_add]

/-- **On a pointed Weierstrass chart, `𝒪_E(n[0])` is the pole sheaf `𝒪(n[0])` of the model**: its
pullback to the restriction of `E` to the base of the chart is the pullback, along the isomorphism
with the projective model of the equation of the chart, of `𝒪(n[0])`, on line-bundle classes. -/
theorem pullback_mk_poleSheaf_toTotal (c : PointedWeierstrassChart E.structureMap E.zero)
    (n : ℕ) :
    LineBundleClass.pullback c.toTotal (LineBundleClass.mk (E.poleSheaf n)) =
      LineBundleClass.pullback c.modelIso.hom (LineBundleClass.mk (c.equation.poleSheaf n)) := by
  have hn := (E.isRelativeEffectiveCartier_zeroDivisor_pow n).isEffectiveCartier
  have hW := (c.equation.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  have hW' := hW.comap c.modelIso.hom
  have hn' : ((E.zeroDivisor ^ n).comap c.toTotal).IsEffectiveCartier :=
    ((E.isRelativeEffectiveCartier_zeroDivisor_pow n).comap_of_isPullback
      c.isPullback).isEffectiveCartier
  rw [poleSheaf_def, WeierstrassCurve.poleSheaf_def, ← LineBundleClass.inv_mk,
    ← LineBundleClass.inv_mk, LineBundleClass.pullback_inv, LineBundleClass.pullback_inv,
    Scheme.IdealSheafData.IsEffectiveCartier.pullback_mk_toInvertibleSheaf hn hn',
    Scheme.IdealSheafData.IsEffectiveCartier.pullback_mk_toInvertibleSheaf hW hW',
    LineBundleClass.mk_toInvertibleSheaf_congr hn' hW' (zeroDivisor_pow_comap_toTotal E c n)]

section BaseChange

variable {E} {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S}

/-- **The pole sheaves commute with base change**: for a pullback square of elliptic curves over
`f : S' ⟶ S` compatible with the zero sections, the pullback of `𝒪_E(n[0])` along `g` is
`𝒪_{E'}(n[0])`, on line-bundle classes. -/
theorem pullback_mk_poleSheaf_of_isPullback (hg : IsPullback g E'.structureMap E.structureMap f)
    (h0 : E'.zero ≫ g = f ≫ E.zero) (n : ℕ) :
    LineBundleClass.pullback g (LineBundleClass.mk (E.poleSheaf n)) =
      LineBundleClass.mk (E'.poleSheaf n) := by
  have hn := (E.isRelativeEffectiveCartier_zeroDivisor_pow n).isEffectiveCartier
  have hn' := (E'.isRelativeEffectiveCartier_zeroDivisor_pow n).isEffectiveCartier
  rw [zeroDivisor_pow_comap_of_isPullback hg h0 n] at hn'
  rw [poleSheaf_def, poleSheaf_def, ← LineBundleClass.inv_mk, ← LineBundleClass.inv_mk,
    LineBundleClass.pullback_inv,
    Scheme.IdealSheafData.IsEffectiveCartier.pullback_mk_toInvertibleSheaf hn hn',
    LineBundleClass.mk_toInvertibleSheaf_congr hn' _
      (zeroDivisor_pow_comap_of_isPullback hg h0 n).symm]

end BaseChange

/-- The pole sheaves of the base change `E.baseChange f` are the pullbacks of those of `E`. -/
theorem pullback_mk_poleSheaf_baseChange {T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    LineBundleClass.pullback ((E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f)
        (LineBundleClass.mk (E.poleSheaf n)) =
      LineBundleClass.mk ((E.baseChange f).poleSheaf n) :=
  pullback_mk_poleSheaf_of_isPullback (E.isPullback_baseChange f) (by simp) n

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
