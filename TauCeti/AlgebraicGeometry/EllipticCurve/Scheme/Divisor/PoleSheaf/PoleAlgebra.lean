/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.PoleAlgebra
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.PoleSheaf.Multiplication

/-!
# The pole algebra of a Weierstrass model

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`. The pole algebra of the
effective Cartier divisor `[0]` of `projModel W` is the graded commutative quasi-coherent algebra

`⨁ₙ 𝒪(n[0]) = 𝒪 ⊕ 𝒪([0]) ⊕ 𝒪(2[0]) ⊕ ⋯`

(`WeierstrassCurve.poleAlgebra`). Its homogeneous components are the pole sheaves `𝒪(n[0])`
(`WeierstrassCurve.poleAlgebra_obj_X`) and its homogeneous multiplication is the multiplication
`𝒪(a[0]) ⊗ 𝒪(b[0]) ≅ 𝒪((a + b)[0])` of the pole sheaves (`WeierstrassCurve.mul_poleAlgebra`).
The Weierstrass coordinates `x`, `y` and their relation in pole order six are elements of its
components of degree `2`, `3` and `6`.

## Main declarations

* `WeierstrassCurve.poleAlgebra`: the pole algebra `⨁ₙ 𝒪(n[0])` of `projModel W`;
* `WeierstrassCurve.poleAlgebra_obj_X`, `WeierstrassCurve.mul_poleAlgebra` and
  `WeierstrassCurve.one_poleAlgebra`: its components, multiplication and unit.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1 and 2.2.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- **The pole algebra** `⨁ₙ 𝒪(n[0])` of the projective model of an elliptic Weierstrass curve:
the pole algebra of the effective Cartier divisor `[0]`. Its components are the pole sheaves
(`WeierstrassCurve.poleAlgebra_obj_X`) and its multiplication is their multiplication
(`WeierstrassCurve.mul_poleAlgebra`). -/
noncomputable def poleAlgebra : GradedQuasicoherentAlgebra W.projModel :=
  W.isRelativeEffectiveCartier_zeroSectionDivisor.isEffectiveCartier.poleAlgebra

/-- The homogeneous components of the pole algebra of a Weierstrass model are the pole sheaves
`𝒪(n[0])`. -/
theorem poleAlgebra_obj_X (n : ℕ) : W.poleAlgebra.obj.X n = (W.poleSheaf n).obj := by
  dsimp only [poleAlgebra]
  rw [Scheme.IdealSheafData.IsEffectiveCartier.poleAlgebra_obj_X]
  exact (W.poleSheaf_obj n).symm

/-- The homogeneous multiplication of the pole algebra of a Weierstrass model is the
multiplication `𝒪(a[0]) ⊗ 𝒪(b[0]) ≅ 𝒪((a + b)[0])` of the pole sheaves. -/
theorem mul_poleAlgebra (a b : ℕ) :
    W.poleAlgebra.obj.toMon.mul a b =
      eqToHom (congrArg₂ (· ⊗ ·) (W.poleAlgebra_obj_X a) (W.poleAlgebra_obj_X b)) ≫
        (W.poleSheafMulIso a b).hom ≫ eqToHom (W.poleAlgebra_obj_X (a + b)).symm := by
  refine (W.isRelativeEffectiveCartier_zeroSectionDivisor.isEffectiveCartier.mul_poleAlgebra
    a b).trans ?_
  rw [poleSheafMulIso_def, Scheme.IdealSheafData.IsEffectiveCartier.dualPowMulIsoOfEq_hom,
    Scheme.IdealSheafData.IsEffectiveCartier.poleMul_def]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

/-- The unit of the pole algebra of a Weierstrass model is the unit `𝒪 ⟶ 𝓗om(𝒪, 𝒪)` of the pole
algebra of `[0]`, read in the pole sheaf `𝒪(0[0])`. -/
theorem one_poleAlgebra :
    W.poleAlgebra.obj.toMon.one = Scheme.IdealSheafData.IsEffectiveCartier.poleOne ≫
      eqToHom (W.poleSheaf_obj 0).symm ≫ eqToHom (W.poleAlgebra_obj_X 0).symm := by
  dsimp only [poleAlgebra]
  rw [Scheme.IdealSheafData.IsEffectiveCartier.one_poleAlgebra]
  exact congrArg _ (eqToHom_trans _ _).symm

end WeierstrassCurve
