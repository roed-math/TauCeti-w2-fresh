/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PoleSheaf.Multiplication
public import TauCeti.CategoryTheory.Monoidal.Closed.Cokernels
public import TauCeti.CategoryTheory.Monoidal.TensorPow

/-!
# Multiplication on the graded pieces of the pole filtration of an elliptic curve

Let `E` be an elliptic curve over a scheme `S`, with pole sheaves `ℒ_n = 𝒪_E(n[0])`. The graded
pieces of the pole filtration are the cokernels `ℒ_(n + 1) / ℒ_n` of the inclusions of pole
sheaves. The multiplication `ℒ_a ⊗ ℒ_b ≅ ℒ_(a + b)` passes to them: it induces an isomorphism

`ℒ_(a + 1) / ℒ_a ⊗ ℒ_(b + 1) / ℒ_b ≅ ℒ_(a + b + 2) / ℒ_(a + b + 1)`

(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleSheafGradedMulIso`), sending the product of the
classes of two local sections to the class of their product
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.tensorHom_π_poleSheafGradedMulIso_hom`). The proof
is the one for a Weierstrass model (`WeierstrassCurve.poleSheafGradedMulIso`): the multiplication
is compatible with the pole filtration in each factor, and `TauCeti.cokernelTensorCokernelIso`
applies. Iterating it, the `n`-th graded piece is the `(n + 1)`-th tensor power of the first one,
the normal sheaf of `[0]` (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleSheafGradedPowIso`).

## Main declarations

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleSheafGradedMulIso`: the multiplication on the
  graded pieces of the pole filtration;
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.tensorHom_π_poleSheafGradedMulIso_hom`: it is
  induced by the multiplication of pole sheaves;
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleSheafGradedPowIso`: the `n`-th graded piece is
  the `(n + 1)`-th tensor power of the first one.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1 and 2.2.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- Transporting the source of an inclusion of pole sheaves along an equality of indices. -/
@[reassoc]
theorem eqToHom_poleSheafMap_hom {m m' n : ℕ} (e : m = m') (h : m' ≤ n) :
    eqToHom (congrArg (fun k ↦ (E.poleSheaf k).obj) e) ≫ (E.poleSheafMap h).hom =
      (E.poleSheafMap (e.trans_le h)).hom := by
  subst e
  simp

/-- Transporting the target of an inclusion of pole sheaves along an equality of indices. -/
@[reassoc]
theorem poleSheafMap_hom_eqToHom {m n n' : ℕ} (h : m ≤ n) (e : n = n') :
    (E.poleSheafMap h).hom ≫ eqToHom (congrArg (fun k ↦ (E.poleSheaf k).obj) e) =
      (E.poleSheafMap (h.trans_eq e)).hom := by
  subst e
  simp

/-- Multiplying `ℒ_(a + 1)` by the inclusion `ℒ_b ⟶ ℒ_(b + 1)` factors through multiplying the
inclusion `ℒ_a ⟶ ℒ_(a + 1)` by `ℒ_(b + 1)`: both are the inclusion `ℒ_(a + b + 1) ⟶ ℒ_(a + b + 2)`
after multiplication. -/
theorem whiskerLeft_poleSheafMap_hom_succ (a b : ℕ) :
    (E.poleSheaf (a + 1)).obj ◁ (E.poleSheafMap (Nat.le_succ b)).hom =
      ((E.poleSheafMulIso (a + 1) b).hom ≫
          eqToHom (congrArg (fun k ↦ (E.poleSheaf k).obj) (Nat.add_right_comm a 1 b)) ≫
          (E.poleSheafMulIso a (b + 1)).inv) ≫
        (E.poleSheafMap (Nat.le_succ a)).hom ▷ (E.poleSheaf (b + 1)).obj := by
  rw [← cancel_mono (E.poleSheafMulIso (a + 1) (b + 1)).hom,
    whiskerLeft_poleSheafMap_hom_poleSheafMulIso_hom, Category.assoc, Category.assoc,
    Category.assoc, poleSheafMap_hom_whiskerRight_poleSheafMulIso_hom, Iso.inv_hom_id_assoc,
    eqToHom_poleSheafMap_hom]
  omega

/-- Multiplying the inclusion `ℒ_a ⟶ ℒ_(a + 1)` by `ℒ_(b + 1)` is the inclusion
`ℒ_(a + b + 1) ⟶ ℒ_(a + b + 2)` after multiplication, with the indices normalised. -/
theorem poleSheafMap_hom_whiskerRight_poleSheafMulIso_hom_eqToHom (a b : ℕ) :
    (E.poleSheafMap (Nat.le_succ a)).hom ▷ (E.poleSheaf (b + 1)).obj ≫
        (E.poleSheafMulIso (a + 1) (b + 1)).hom ≫
        eqToHom (congrArg (fun k ↦ (E.poleSheaf k).obj) (Nat.add_right_comm a 1 (b + 1))) =
      (E.poleSheafMulIso a (b + 1)).hom ≫ (E.poleSheafMap (Nat.le_succ (a + b + 1))).hom := by
  rw [poleSheafMap_hom_whiskerRight_poleSheafMulIso_hom_assoc, poleSheafMap_hom_eqToHom]
  exact Nat.add_right_comm a 1 (b + 1)

/-- **The multiplication on the graded pieces of the pole filtration**:
`ℒ_(a + 1) / ℒ_a ⊗ ℒ_(b + 1) / ℒ_b ≅ ℒ_(a + b + 2) / ℒ_(a + b + 1)`, induced by the
multiplication of pole sheaves (`EllipticCurveGeom.tensorHom_π_poleSheafGradedMulIso_hom`). -/
noncomputable def poleSheafGradedMulIso (a b : ℕ) :
    cokernel (E.poleSheafMap (Nat.le_succ a)).hom ⊗ cokernel (E.poleSheafMap (Nat.le_succ b)).hom ≅
      cokernel (E.poleSheafMap (Nat.le_succ (a + b + 1))).hom :=
  cokernelTensorCokernelIso _ _ (E.whiskerLeft_poleSheafMap_hom_succ a b) ≪≫
    cokernel.mapIso _ _ (E.poleSheafMulIso a (b + 1))
      (E.poleSheafMulIso (a + 1) (b + 1) ≪≫
        eqToIso (congrArg (fun k ↦ (E.poleSheaf k).obj) (Nat.add_right_comm a 1 (b + 1))))
      (E.poleSheafMap_hom_whiskerRight_poleSheafMulIso_hom_eqToHom a b)

/-- **The multiplication on the graded pieces is induced by the multiplication of pole sheaves**:
the product of the classes of local sections of `ℒ_(a + 1)` and `ℒ_(b + 1)` is the class
of their product in `ℒ_(a + b + 2)`. -/
@[reassoc (attr := simp)]
theorem tensorHom_π_poleSheafGradedMulIso_hom (a b : ℕ) :
    (cokernel.π (E.poleSheafMap (Nat.le_succ a)).hom ⊗ₘ
        cokernel.π (E.poleSheafMap (Nat.le_succ b)).hom) ≫ (E.poleSheafGradedMulIso a b).hom =
      (E.poleSheafMulIso (a + 1) (b + 1)).hom ≫
        eqToHom (congrArg (fun k ↦ (E.poleSheaf k).obj) (Nat.add_right_comm a 1 (b + 1))) ≫
        cokernel.π (E.poleSheafMap (Nat.le_succ (a + b + 1))).hom := by
  delta poleSheafGradedMulIso
  simp [cokernel.mapIso]

/-- **The graded pieces of the pole filtration are tensor powers of the first one**:
`(ℒ_1 / ℒ_0)^⊗(n + 1) ≅ ℒ_(n + 1) / ℒ_n`, built from the multiplication on the
graded pieces. The first graded piece is the normal sheaf of `[0]`, so the `n`-th one is its
`(n + 1)`-th tensor power. -/
noncomputable def poleSheafGradedPowIso :
    (n : ℕ) → tensorPow (cokernel (E.poleSheafMap (Nat.le_succ 0)).hom) (n + 1) ≅
      cokernel (E.poleSheafMap (Nat.le_succ n)).hom
  | 0 => ρ_ _
  | n + 1 => (tensorPowSuccIso _ (n + 1)).symm ≪≫
      whiskerRightIso (poleSheafGradedPowIso n) _ ≪≫ E.poleSheafGradedMulIso n 0

/-- The first graded piece is its own first tensor power. -/
theorem poleSheafGradedPowIso_zero : E.poleSheafGradedPowIso 0 = ρ_ _ :=
  (rfl)

/-- Each further factor of the tensor power is multiplied in on the right. -/
theorem poleSheafGradedPowIso_succ (n : ℕ) :
    E.poleSheafGradedPowIso (n + 1) = (tensorPowSuccIso _ (n + 1)).symm ≪≫
      whiskerRightIso (E.poleSheafGradedPowIso n) _ ≪≫ E.poleSheafGradedMulIso n 0 :=
  (rfl)

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
