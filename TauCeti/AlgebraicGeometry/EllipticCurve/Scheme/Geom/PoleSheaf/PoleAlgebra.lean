/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.PoleAlgebra
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PoleSheaf.Multiplication

/-!
# The pole algebra of an elliptic curve

Let `E` be an elliptic curve over a scheme `S`. The pole algebra of the relative effective Cartier
divisor `[0]` of `E` is the graded commutative quasi-coherent `𝒪_E`-algebra

`⨁ₙ ℒ_n = 𝒪_E ⊕ 𝒪_E([0]) ⊕ 𝒪_E(2[0]) ⊕ ⋯`

(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleAlgebra`). Its homogeneous components are the
pole sheaves `ℒ_n` (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleAlgebra_obj_X`) and its
homogeneous multiplication is the multiplication `ℒ_a ⊗ ℒ_b ≅ ℒ_(a + b)` of the pole sheaves
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.mul_poleAlgebra`). The pole-filtration
construction of a pointed Weierstrass equation chooses the coordinates `x` and `y` in its
components of degree `2` and `3`, and their relation lies in its component of degree `6`.

## Main declarations

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleAlgebra`: the pole algebra `⨁ₙ ℒ_n` of `E`;
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleAlgebra_obj_X`,
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mul_poleAlgebra` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.one_poleAlgebra`: its components, multiplication
  and unit.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1 and 2.2.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- **The pole algebra** `⨁ₙ ℒ_n` of an elliptic curve: the pole algebra of the effective Cartier
divisor `[0]`. Its components are the pole sheaves (`EllipticCurveGeom.poleAlgebra_obj_X`) and its
multiplication is their multiplication (`EllipticCurveGeom.mul_poleAlgebra`). -/
noncomputable def poleAlgebra : GradedQuasicoherentAlgebra E.carrier :=
  E.isRelativeEffectiveCartier_zeroDivisor.isEffectiveCartier.poleAlgebra

/-- The homogeneous components of the pole algebra of an elliptic curve are the pole sheaves
`ℒ_n`. -/
theorem poleAlgebra_obj_X (n : ℕ) : E.poleAlgebra.obj.X n = (E.poleSheaf n).obj := by
  dsimp only [poleAlgebra]
  rw [Scheme.IdealSheafData.IsEffectiveCartier.poleAlgebra_obj_X]
  exact (E.poleSheaf_obj n).symm

/-- The homogeneous multiplication of the pole algebra of an elliptic curve is the multiplication
`ℒ_a ⊗ ℒ_b ≅ ℒ_(a + b)` of the pole sheaves. -/
theorem mul_poleAlgebra (a b : ℕ) :
    E.poleAlgebra.obj.toMon.mul a b =
      eqToHom (congrArg₂ (· ⊗ ·) (E.poleAlgebra_obj_X a) (E.poleAlgebra_obj_X b)) ≫
        (E.poleSheafMulIso a b).hom ≫ eqToHom (E.poleAlgebra_obj_X (a + b)).symm := by
  refine (E.isRelativeEffectiveCartier_zeroDivisor.isEffectiveCartier.mul_poleAlgebra
    a b).trans ?_
  rw [poleSheafMulIso_def, Scheme.IdealSheafData.IsEffectiveCartier.dualPowMulIsoOfEq_hom,
    Scheme.IdealSheafData.IsEffectiveCartier.poleMul_def]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

/-- The unit of the pole algebra of an elliptic curve is the unit `𝒪_E ⟶ 𝓗om(𝒪_E, 𝒪_E)` of the
pole algebra of `[0]`, read in the pole sheaf `ℒ_0`. -/
theorem one_poleAlgebra :
    E.poleAlgebra.obj.toMon.one = Scheme.IdealSheafData.IsEffectiveCartier.poleOne ≫
      eqToHom (E.poleSheaf_obj 0).symm ≫ eqToHom (E.poleAlgebra_obj_X 0).symm := by
  dsimp only [poleAlgebra]
  rw [Scheme.IdealSheafData.IsEffectiveCartier.one_poleAlgebra]
  exact congrArg _ (eqToHom_trans _ _).symm

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
