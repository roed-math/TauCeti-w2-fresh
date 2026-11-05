/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Multiplication
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.PoleSheaf.Filtration
public import TauCeti.CategoryTheory.Monoidal.Closed.Basic

/-!
# Multiplication of the pole sheaves of a Weierstrass model

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`. The pole sheaf `𝒪(n[0])` of
`projModel W` is the dual `𝓗om(𝒪(-n[0]), 𝒪)` of the ideal sheaf of `n[0]`
(`WeierstrassCurve.poleSheaf_obj`), and the inclusion `𝒪(m[0]) ⟶ 𝒪(n[0])` of the pole filtration
is precomposition with `𝒪(-n[0]) ⊆ 𝒪(-m[0])` (`WeierstrassCurve.poleSheafMap_hom_eq`). The
multiplication of the line bundles of multiples of the effective Cartier divisor `[0]` therefore
gives the **multiplication maps of the pole sheaves**

`𝒪(a[0]) ⊗ 𝒪(b[0]) ≅ 𝒪((a + b)[0])`

(`WeierstrassCurve.poleSheafMulIso`), compatible with the pole filtration
(`WeierstrassCurve.poleSheafMap_hom_whiskerRight_poleSheafMulIso_hom`). These are the
multiplication maps through which the Weierstrass coordinates `x` and `y` and their relation in
pole order six are produced.

## Main declarations

* `WeierstrassCurve.poleSheafMulIso`: `𝒪(a[0]) ⊗ 𝒪(b[0]) ≅ 𝒪((a + b)[0])`;
* `WeierstrassCurve.poleSheafMap_hom_whiskerRight_poleSheafMulIso_hom`: compatibility with the
  pole filtration.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed AlgebraicGeometry TauCeti
  TauCeti.AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- The pole sheaf `𝒪(n[0])` is the internal Hom `𝓗om(𝒪(-n[0]), 𝒪)` out of the ideal sheaf of
`n[0]`. -/
theorem poleSheaf_obj (n : ℕ) :
    (W.poleSheaf n).obj = (ihom (W.zeroSectionDivisor ^ n).sheaf).obj (𝟙_ _) := by
  rw [poleSheaf_def, InvertibleSheaf.dual_obj_eq_ihom,
    Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj]

/-- The inclusion `𝒪(m[0]) ⟶ 𝒪(n[0])` of the pole filtration is precomposition with the inclusion
`𝒪(-n[0]) ⟶ 𝒪(-m[0])` of ideal sheaves. -/
theorem poleSheafMap_hom_eq {m n : ℕ} (h : m ≤ n) :
    (W.poleSheafMap h).hom = eqToHom (W.poleSheaf_obj m) ≫
      (pre (Scheme.IdealSheafData.sheafOfLE (W.zeroSectionDivisor_pow_le_pow h))).app (𝟙_ _) ≫
      eqToHom (W.poleSheaf_obj n).symm := by
  simp only [poleSheafMap_def, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.eqToHom_hom, Scheme.IdealSheafData.IsEffectiveCartier.dualMap_def,
    InvertibleSheaf.dualMap_hom, Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheafMap_hom,
    pre_map, NatTrans.comp_app, MonoidalClosed.pre_eqToHom_app, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]

/-- **The multiplication of pole sheaves** `𝒪(a[0]) ⊗ 𝒪(b[0]) ≅ 𝒪((a + b)[0])`: the
multiplication of the line bundles of multiples of the effective Cartier divisor `[0]`. A product
`φ ψ` of local sections, viewed as functionals on `𝒪(-a[0])` and `𝒪(-b[0])`, evaluates on `t s`,
for `t ∈ 𝒪(-b[0])` and `s ∈ 𝒪(-a[0])`, to `φ(s) ψ(t)`
(`Scheme.IdealSheafData.IsEffectiveCartier.whiskerLeft_dualPowMulIso_hom_comp_ev`). -/
noncomputable def poleSheafMulIso (a b : ℕ) :
    (W.poleSheaf a).obj ⊗ (W.poleSheaf b).obj ≅ (W.poleSheaf (a + b)).obj :=
  W.isRelativeEffectiveCartier_zeroSectionDivisor.isEffectiveCartier.dualPowMulIsoOfEq
    W.poleSheaf_obj a b

/-- **The multiplication of pole sheaves is compatible with the pole filtration**: for `a ≤ a'`,
including `𝒪(a[0])` into `𝒪(a'[0])` and multiplying by `𝒪(b[0])` is multiplying and then including
`𝒪((a + b)[0])` into `𝒪((a' + b)[0])`. -/
@[reassoc]
theorem poleSheafMap_hom_whiskerRight_poleSheafMulIso_hom {a a' : ℕ} (h : a ≤ a') (b : ℕ) :
    (W.poleSheafMap h).hom ▷ (W.poleSheaf b).obj ≫ (W.poleSheafMulIso a' b).hom =
      (W.poleSheafMulIso a b).hom ≫ (W.poleSheafMap (Nat.add_le_add_right h b)).hom := by
  rw [poleSheafMap_hom_eq, poleSheafMap_hom_eq]
  exact Scheme.IdealSheafData.IsEffectiveCartier.whiskerRight_dualPowMulIsoOfEq_hom
    W.isRelativeEffectiveCartier_zeroSectionDivisor.isEffectiveCartier W.poleSheaf_obj h b

end WeierstrassCurve
