/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.PoleSheaf.Multiplication
public import TauCeti.CategoryTheory.Monoidal.Closed.Cokernels

/-!
# Multiplication on the graded pieces of the pole filtration

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`. The graded pieces of the pole
filtration of `projModel W` are the cokernels `𝒪((n + 1)[0]) / 𝒪(n[0])` of the inclusions of pole
sheaves. The multiplication `𝒪(a[0]) ⊗ 𝒪(b[0]) ≅ 𝒪((a + b)[0])` passes to them: it induces an
isomorphism

`𝒪((a + 1)[0]) / 𝒪(a[0]) ⊗ 𝒪((b + 1)[0]) / 𝒪(b[0]) ≅ 𝒪((a + b + 2)[0]) / 𝒪((a + b + 1)[0])`

(`WeierstrassCurve.poleSheafGradedMulIso`), sending the product of the classes of two local
sections to the class of their product
(`WeierstrassCurve.tensorHom_π_poleSheafGradedMulIso_hom`). In other words, the leading term of a
product of functions with poles of orders at most `a + 1` and `b + 1` along `[0]` is the product
of their leading terms. This is how the leading terms of `x², xy, x³, y²` are computed.

The proof is formal. Tensoring with any module sheaf preserves cokernels, since `X.Modules` is
braided closed. Multiplying `𝒪((a + 1)[0])` by the inclusion `𝒪(b[0]) ⟶ 𝒪((b + 1)[0])` factors
through multiplying the inclusion `𝒪(a[0]) ⟶ 𝒪((a + 1)[0])` by `𝒪((b + 1)[0])`, since both are the
inclusion `𝒪((a + b + 1)[0]) ⟶ 𝒪((a + b + 2)[0])` after multiplication, so
`TauCeti.cokernelTensorCokernelIso` applies.

## Main declarations

* `WeierstrassCurve.poleSheafGradedMulIso`: the multiplication on the graded pieces of the pole
  filtration;
* `WeierstrassCurve.tensorHom_π_poleSheafGradedMulIso_hom`: it is induced by the multiplication of
  pole sheaves.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1 and 2.2.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry TauCeti

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- Transporting the source of an inclusion of pole sheaves along an equality of indices. -/
@[reassoc]
theorem eqToHom_poleSheafMap_hom {m m' n : ℕ} (e : m = m') (h : m' ≤ n) :
    eqToHom (congrArg (fun k ↦ (W.poleSheaf k).obj) e) ≫ (W.poleSheafMap h).hom =
      (W.poleSheafMap (e.trans_le h)).hom := by
  subst e
  simp

/-- Transporting the target of an inclusion of pole sheaves along an equality of indices. -/
@[reassoc]
theorem poleSheafMap_hom_eqToHom {m n n' : ℕ} (h : m ≤ n) (e : n = n') :
    (W.poleSheafMap h).hom ≫ eqToHom (congrArg (fun k ↦ (W.poleSheaf k).obj) e) =
      (W.poleSheafMap (h.trans_eq e)).hom := by
  subst e
  simp

/-- Multiplying `𝒪((a + 1)[0])` by the inclusion `𝒪(b[0]) ⟶ 𝒪((b + 1)[0])` factors through
multiplying the inclusion `𝒪(a[0]) ⟶ 𝒪((a + 1)[0])` by `𝒪((b + 1)[0])`: both are the inclusion
`𝒪((a + b + 1)[0]) ⟶ 𝒪((a + b + 2)[0])` after multiplication. -/
theorem whiskerLeft_poleSheafMap_hom_succ (a b : ℕ) :
    (W.poleSheaf (a + 1)).obj ◁ (W.poleSheafMap (Nat.le_succ b)).hom =
      ((W.poleSheafMulIso (a + 1) b).hom ≫
          eqToHom (congrArg (fun k ↦ (W.poleSheaf k).obj) (Nat.add_right_comm a 1 b)) ≫
          (W.poleSheafMulIso a (b + 1)).inv) ≫
        (W.poleSheafMap (Nat.le_succ a)).hom ▷ (W.poleSheaf (b + 1)).obj := by
  rw [← cancel_mono (W.poleSheafMulIso (a + 1) (b + 1)).hom,
    whiskerLeft_poleSheafMap_hom_poleSheafMulIso_hom, Category.assoc, Category.assoc,
    Category.assoc, poleSheafMap_hom_whiskerRight_poleSheafMulIso_hom, Iso.inv_hom_id_assoc,
    eqToHom_poleSheafMap_hom]
  omega

/-- Multiplying the inclusion `𝒪(a[0]) ⟶ 𝒪((a + 1)[0])` by `𝒪((b + 1)[0])` is the inclusion
`𝒪((a + b + 1)[0]) ⟶ 𝒪((a + b + 2)[0])` after multiplication, with the indices normalised. -/
theorem poleSheafMap_hom_whiskerRight_poleSheafMulIso_hom_eqToHom (a b : ℕ) :
    (W.poleSheafMap (Nat.le_succ a)).hom ▷ (W.poleSheaf (b + 1)).obj ≫
        (W.poleSheafMulIso (a + 1) (b + 1)).hom ≫
        eqToHom (congrArg (fun k ↦ (W.poleSheaf k).obj) (Nat.add_right_comm a 1 (b + 1))) =
      (W.poleSheafMulIso a (b + 1)).hom ≫ (W.poleSheafMap (Nat.le_succ (a + b + 1))).hom := by
  rw [poleSheafMap_hom_whiskerRight_poleSheafMulIso_hom_assoc, poleSheafMap_hom_eqToHom]
  exact Nat.add_right_comm a 1 (b + 1)

/-- **The multiplication on the graded pieces of the pole filtration**:
`𝒪((a + 1)[0]) / 𝒪(a[0]) ⊗ 𝒪((b + 1)[0]) / 𝒪(b[0]) ≅ 𝒪((a + b + 2)[0]) / 𝒪((a + b + 1)[0])`,
induced by the multiplication of pole sheaves
(`WeierstrassCurve.tensorHom_π_poleSheafGradedMulIso_hom`). -/
noncomputable def poleSheafGradedMulIso (a b : ℕ) :
    cokernel (W.poleSheafMap (Nat.le_succ a)).hom ⊗ cokernel (W.poleSheafMap (Nat.le_succ b)).hom ≅
      cokernel (W.poleSheafMap (Nat.le_succ (a + b + 1))).hom :=
  cokernelTensorCokernelIso _ _ (W.whiskerLeft_poleSheafMap_hom_succ a b) ≪≫
    cokernel.mapIso _ _ (W.poleSheafMulIso a (b + 1))
      (W.poleSheafMulIso (a + 1) (b + 1) ≪≫
        eqToIso (congrArg (fun k ↦ (W.poleSheaf k).obj) (Nat.add_right_comm a 1 (b + 1))))
      (W.poleSheafMap_hom_whiskerRight_poleSheafMulIso_hom_eqToHom a b)

/-- **The multiplication on the graded pieces is induced by the multiplication of pole sheaves**:
the product of the classes of local sections of `𝒪((a + 1)[0])` and `𝒪((b + 1)[0])` is the class
of their product in `𝒪((a + b + 2)[0])`. -/
@[reassoc (attr := simp)]
theorem tensorHom_π_poleSheafGradedMulIso_hom (a b : ℕ) :
    (cokernel.π (W.poleSheafMap (Nat.le_succ a)).hom ⊗ₘ
        cokernel.π (W.poleSheafMap (Nat.le_succ b)).hom) ≫ (W.poleSheafGradedMulIso a b).hom =
      (W.poleSheafMulIso (a + 1) (b + 1)).hom ≫
        eqToHom (congrArg (fun k ↦ (W.poleSheaf k).obj) (Nat.add_right_comm a 1 (b + 1))) ≫
        cokernel.π (W.poleSheafMap (Nat.le_succ (a + b + 1))).hom := by
  delta poleSheafGradedMulIso
  simp [cokernel.mapIso]

end WeierstrassCurve
