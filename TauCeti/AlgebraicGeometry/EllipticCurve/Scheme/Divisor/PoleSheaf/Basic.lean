/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Genus.ConstantExtension
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Integral
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.PicZero
public import TauCeti.AlgebraicGeometry.LineBundle.Dual
public import TauCeti.AlgebraicGeometry.LineBundle.HighDegree
public import TauCeti.AlgebraicGeometry.RationalPoint.IdealSheaf
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Genus
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# The pole sheaves `𝒪(n[0])` of a projective Weierstrass model

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`. The zero section
`[0 : 1 : 0]` of the projective model `projModel W` cuts out the relative effective Cartier
divisor `[0]` (`WeierstrassCurve.zeroSectionDivisor`), and its multiples `n[0]` are represented by
the powers of its ideal sheaf. The **pole sheaf** `𝒪(n[0])` (`WeierstrassCurve.poleSheaf`) is the
line bundle of `n[0]`, the dual of the ideal sheaf of `n[0]`. Its class in the Picard group is the
`n`-th power of the class of `𝒪([0])`, and it commutes with every change of the coefficient ring.

Over a field `K`, the projective model is a smooth proper geometrically integral curve of genus
one (`WeierstrassCurve.genus_projModel`): its genus `dim_K H¹(projModel W, 𝒪)` is the genus of the
function field `K(W)`, which is one. The line bundle `𝒪(n[0])` has degree `n`, since `[0]` is a
rational point. By Riemann–Roch on a curve of genus one, for `n > 0`,

`H¹(projModel W, 𝒪(n[0])) = 0` and `dim_K H⁰(projModel W, 𝒪(n[0])) = n`.

These are the fibrewise vanishing and dimension statements for the pole sheaves of an elliptic
curve over an arbitrary base.

## Main definitions

* `WeierstrassCurve.poleSheaf W n`: the line bundle `𝒪(n[0])` on `projModel W`.

## Main results

* `WeierstrassCurve.mk_poleSheaf`: the class of `𝒪(n[0])` is the `n`-th power of the class of
  `𝒪([0])`, the dual of the ideal sheaf of the zero section (`WeierstrassCurve.mk_poleSheaf_one`).
* `WeierstrassCurve.pullback_mk_poleSheaf_projModelBaseChange` and
  `WeierstrassCurve.nonempty_pullback_poleSheaf_iso`: `𝒪(n[0])` commutes with change of the
  coefficient ring.
* `WeierstrassCurve.genus_projModel`: over a field, the projective model has genus one.
* `WeierstrassCurve.eulerDegree_poleSheaf`: over a field, `𝒪(n[0])` has degree `n`.
* `WeierstrassCurve.finrank_cohomology_zero_poleSheaf`: over a field, `dim H⁰(𝒪(n[0])) = n` for
  `n > 0`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.3.1: the
  Riemann–Roch spaces `L(n O)` have dimension `n` for `n > 0`.
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti TauCeti.AlgebraicGeometry
open Module (finrank)

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- The **pole sheaf** `𝒪(n[0])` of the projective model of an elliptic Weierstrass curve: the
line bundle of the divisor `n[0]`, the dual of the invertible ideal sheaf `𝒪(-n[0])` of `n[0]`. -/
noncomputable def poleSheaf (n : ℕ) : InvertibleSheaf W.projModel :=
  InvertibleSheaf.dual
    (W.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier.toInvertibleSheaf

/-- The pole sheaf `𝒪(n[0])` is the dual of the ideal sheaf of `n[0]`. -/
theorem poleSheaf_def (n : ℕ) :
    W.poleSheaf n = InvertibleSheaf.dual
      (Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf
        (W.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier) :=
  (rfl)

/-- The pole sheaf `𝒪([0])` is the dual of the ideal sheaf of the zero section, on line-bundle
classes. -/
theorem mk_poleSheaf_one :
    LineBundleClass.mk (W.poleSheaf 1) =
      (LineBundleClass.mk (Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf
        W.isRelativeEffectiveCartier_zeroSectionDivisor.isEffectiveCartier))⁻¹ := by
  rw [poleSheaf_def, ← LineBundleClass.inv_mk, LineBundleClass.mk_toInvertibleSheaf_congr _
    W.isRelativeEffectiveCartier_zeroSectionDivisor.isEffectiveCartier (pow_one _)]

/-- **`𝒪(n[0]) ≅ 𝒪([0])^{⊗ n}`**, on line-bundle classes. -/
theorem mk_poleSheaf (n : ℕ) :
    LineBundleClass.mk (W.poleSheaf n) = LineBundleClass.mk (W.poleSheaf 1) ^ n := by
  rw [mk_poleSheaf_one, poleSheaf_def, ← LineBundleClass.inv_mk,
    LineBundleClass.mk_toInvertibleSheaf_pow
      W.isRelativeEffectiveCartier_zeroSectionDivisor.isEffectiveCartier, inv_pow]

/-- `𝒪((m + n)[0]) ≅ 𝒪(m[0]) ⊗ 𝒪(n[0])`, on line-bundle classes. -/
theorem mk_poleSheaf_add (m n : ℕ) :
    LineBundleClass.mk (W.poleSheaf (m + n)) =
      LineBundleClass.mk (W.poleSheaf m) * LineBundleClass.mk (W.poleSheaf n) := by
  rw [W.mk_poleSheaf (m + n), W.mk_poleSheaf m, W.mk_poleSheaf n, pow_add]

/-- **The pole sheaves commute with change of the coefficient ring**: the pullback of `𝒪(n[0])`
along the canonical morphism `projModel (W.map f) ⟶ projModel W` is `𝒪(n[0])`, on line-bundle
classes. -/
theorem pullback_mk_poleSheaf_projModelBaseChange {R' : Type u} [CommRing R'] (f : R →+* R')
    (n : ℕ) :
    LineBundleClass.pullback (W.projModelBaseChange f) (LineBundleClass.mk (W.poleSheaf n)) =
      LineBundleClass.mk ((W.map f).poleSheaf n) := by
  have hn := (W.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  have hn' := ((W.map f).isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  rw [W.zeroSectionDivisor_pow_map f n] at hn'
  rw [poleSheaf_def, poleSheaf_def, ← LineBundleClass.inv_mk, ← LineBundleClass.inv_mk,
    LineBundleClass.pullback_inv,
    Scheme.IdealSheafData.IsEffectiveCartier.pullback_mk_toInvertibleSheaf hn hn',
    LineBundleClass.mk_toInvertibleSheaf_congr hn' _ (W.zeroSectionDivisor_pow_map f n).symm]

/-- **The pole sheaves commute with change of the coefficient ring**, as sheaves up to
isomorphism: the pullback of `𝒪(n[0])` along `projModel (W.map f) ⟶ projModel W` is
isomorphic to `𝒪(n[0])`. -/
theorem nonempty_pullback_poleSheaf_iso {R' : Type u} [CommRing R'] (f : R →+* R') (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback (W.projModelBaseChange f)).obj (W.poleSheaf n).obj ≅
      ((W.map f).poleSheaf n).obj) := by
  have h := W.pullback_mk_poleSheaf_projModelBaseChange f n
  rwa [LineBundleClass.pullback_mk, LineBundleClass.mk_eq_mk_iff] at h

/-! ### Cohomology over a field -/

section Field

-- The function field of the projective model carries the `K`-algebra structure defined by its
-- structure morphism, which is the one used by the genus theory of smooth curves.
attribute [local instance high] Scheme.functionFieldBaseAlgebra

variable {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The projective model of an elliptic curve over a field has genus one**:
`dim_K H¹(projModel W, 𝒪) = 1`. The genus of a smooth proper geometrically integral curve is the
genus of its function field, here `K(W)`, which has genus one. -/
theorem genus_projModel : W.projModel.genus K = 1 := by
  rw [Scheme.genus_eq_genus_functionField_of_smooth, ← W.toAffine.genus_functionField]
  exact genus_eq_of_ringEquiv (RingEquiv.refl K)
    W.projModelFunctionFieldBaseAlgEquiv.symm.toRingEquiv
    fun c ↦ W.projModelFunctionFieldBaseAlgEquiv.symm.commutes c

/-- The genus of the projective model, as the dimension of `H¹(projModel W, 𝒪)`. -/
@[simp]
theorem finrank_cohomology_one_trivial_projModel :
    finrank K (Scheme.Modules.Cohomology (InvertibleSheaf.trivial W.projModel).obj 1) = 1 := by
  rw [← Scheme.genus_def, genus_projModel]

/-- **`𝒪(n[0])` has degree `n`** on the projective model of an elliptic curve over a field: the
zero section is a rational point, so `𝒪([0])` has degree one, and the degree is additive. -/
@[simp]
theorem eulerDegree_poleSheaf (n : ℕ) : (W.poleSheaf n).eulerDegree K = n := by
  have h1 : LineBundleClass.eulerDegree K (LineBundleClass.mk (W.poleSheaf 1)) = 1 := by
    have h0 := Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension
      W.projModelZero W.projModelZero_projModelOver
    rw [mk_poleSheaf_one, LineBundleClass.mk_toInvertibleSheaf_congr _ h0.isEffectiveCartier
      W.zeroSectionDivisor_def, LineBundleClass.inv_mk, LineBundleClass.eulerDegree_mk]
    exact Scheme.Hom.eulerDegree_dual_ker_of_smooth W.projModelZero W.projModelZero_projModelOver
  induction n with
  | zero =>
    rw [← LineBundleClass.eulerDegree_mk, mk_poleSheaf, pow_zero, LineBundleClass.eulerDegree_one,
      Nat.cast_zero]
  | succ n hn =>
    rw [← LineBundleClass.eulerDegree_mk, mk_poleSheaf_add,
      LineBundleClass.eulerDegree_mul_of_smooth, LineBundleClass.eulerDegree_mk, hn, h1,
      Nat.cast_succ]

/-- **`dim_K H⁰(projModel W, 𝒪(n[0])) = n` for `n > 0`** over a field, by Riemann–Roch in genus
one. -/
theorem finrank_cohomology_zero_poleSheaf {n : ℕ} (hn : 0 < n) :
    finrank K (Scheme.Modules.Cohomology (W.poleSheaf n).obj 0) = n := by
  have h := InvertibleSheaf.finrank_cohomology_zero_eq_eulerDegree_add_one_sub_genus Fact.out
    (isFunctionField_functionField_projModel W)
    isIntegrallyClosedIn_functionField_of_geometricallyIntegral (W.poleSheaf n)
    (by rw [finrank_cohomology_one_trivial_projModel, eulerDegree_poleSheaf]; omega)
  rw [finrank_cohomology_one_trivial_projModel, eulerDegree_poleSheaf] at h
  omega

end Field

end WeierstrassCurve
