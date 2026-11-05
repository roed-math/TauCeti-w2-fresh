/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Multiplication
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PoleSheaf.Filtration
public import TauCeti.CategoryTheory.Monoidal.Closed.Basic

/-!
# Multiplication of the pole sheaves of an elliptic curve

Let `E` be an elliptic curve over a scheme `S`. The pole sheaf `ℒ_n = 𝒪_E(n[0])` is the dual
`𝓗om(𝒪_E(-n[0]), 𝒪_E)` of the ideal sheaf of `n[0]`
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleSheaf_obj`), and the inclusion `ℒ_m ⟶ ℒ_n` of
the pole filtration is precomposition with `𝒪_E(-n[0]) ⊆ 𝒪_E(-m[0])`
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleSheafMap_hom_eq`). The multiplication of the
line bundles of multiples of the relative effective Cartier divisor `[0]` therefore gives the
**multiplication maps of the pole sheaves**

`ℒ_a ⊗ ℒ_b ≅ ℒ_(a + b)`

(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleSheafMulIso`), compatible with the pole
filtration
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleSheafMap_hom_whiskerRight_poleSheafMulIso_hom`).
These are the multiplication maps of the pole-filtration construction of a pointed Weierstrass
equation: products of the coordinates `x` and `y`, chosen in pole orders two and three, lie in the
higher pole sheaves, and their unique relation lies in pole order six.

## Main declarations

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleSheafMulIso`: `ℒ_a ⊗ ℒ_b ≅ ℒ_(a + b)`;
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleSheafMap_hom_whiskerRight_poleSheafMulIso_hom`:
  compatibility with the pole filtration.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1 and 2.2.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- The pole sheaf `ℒ_n` is the internal Hom `𝓗om(𝒪_E(-n[0]), 𝒪_E)` out of the ideal sheaf of
`n[0]`. -/
theorem poleSheaf_obj (n : ℕ) :
    (E.poleSheaf n).obj = (ihom (E.zeroDivisor ^ n).sheaf).obj (𝟙_ _) := by
  rw [poleSheaf_def, InvertibleSheaf.dual_obj_eq_ihom,
    Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj]

/-- The inclusion `ℒ_m ⟶ ℒ_n` of the pole filtration is precomposition with the inclusion
`𝒪_E(-n[0]) ⟶ 𝒪_E(-m[0])` of ideal sheaves. -/
theorem poleSheafMap_hom_eq {m n : ℕ} (h : m ≤ n) :
    (E.poleSheafMap h).hom = eqToHom (E.poleSheaf_obj m) ≫
      (pre (Scheme.IdealSheafData.sheafOfLE (E.zeroDivisor_pow_le_pow h))).app (𝟙_ _) ≫
      eqToHom (E.poleSheaf_obj n).symm := by
  simp only [poleSheafMap_def, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.eqToHom_hom, Scheme.IdealSheafData.IsEffectiveCartier.dualMap_def,
    InvertibleSheaf.dualMap_hom, Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheafMap_hom,
    pre_map, NatTrans.comp_app, MonoidalClosed.pre_eqToHom_app, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]

/-- **The multiplication of pole sheaves** `ℒ_a ⊗ ℒ_b ≅ ℒ_(a + b)`: the multiplication of the
line bundles of multiples of the effective Cartier divisor `[0]`. A product `φ ψ` of local
sections, viewed as functionals on `𝒪_E(-a[0])` and `𝒪_E(-b[0])`, evaluates on `t s`, for
`t ∈ 𝒪_E(-b[0])` and `s ∈ 𝒪_E(-a[0])`, to `φ(s) ψ(t)`
(`Scheme.IdealSheafData.IsEffectiveCartier.whiskerLeft_dualPowMulIso_hom_comp_ev`). -/
noncomputable def poleSheafMulIso (a b : ℕ) :
    (E.poleSheaf a).obj ⊗ (E.poleSheaf b).obj ≅ (E.poleSheaf (a + b)).obj :=
  E.isRelativeEffectiveCartier_zeroDivisor.isEffectiveCartier.dualPowMulIsoOfEq E.poleSheaf_obj a b

/-- The multiplication of pole sheaves is the multiplication of the line bundles of multiples
of `[0]`, transported along `poleSheaf_obj`. -/
theorem poleSheafMulIso_def (a b : ℕ) :
    E.poleSheafMulIso a b =
      E.isRelativeEffectiveCartier_zeroDivisor.isEffectiveCartier.dualPowMulIsoOfEq
        E.poleSheaf_obj a b :=
  (rfl)

/-- **The multiplication of pole sheaves is compatible with the pole filtration**: for `a ≤ a'`,
including `ℒ_a` into `ℒ_a'` and multiplying by `ℒ_b` is multiplying and then including
`ℒ_(a + b)` into `ℒ_(a' + b)`. -/
@[reassoc]
theorem poleSheafMap_hom_whiskerRight_poleSheafMulIso_hom {a a' : ℕ} (h : a ≤ a') (b : ℕ) :
    (E.poleSheafMap h).hom ▷ (E.poleSheaf b).obj ≫ (E.poleSheafMulIso a' b).hom =
      (E.poleSheafMulIso a b).hom ≫ (E.poleSheafMap (Nat.add_le_add_right h b)).hom := by
  rw [poleSheafMap_hom_eq, poleSheafMap_hom_eq]
  exact Scheme.IdealSheafData.IsEffectiveCartier.whiskerRight_dualPowMulIsoOfEq_hom
    E.isRelativeEffectiveCartier_zeroDivisor.isEffectiveCartier E.poleSheaf_obj h b

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
