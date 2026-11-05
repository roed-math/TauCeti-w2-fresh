/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
public import TauCeti.AlgebraicGeometry.IdealSheaf.Inclusion
public import TauCeti.AlgebraicGeometry.LineBundle.Dual.Tensor

/-!
# Multiplication of the line bundles of multiples of an effective Cartier divisor

Let `D` be an effective Cartier divisor on a scheme `X`, with ideal sheaf `I = 𝒪_X(-D)`. Since
`aD` is effective Cartier, multiplication of local functions is an isomorphism
`I^b ⊗ I^a ≅ I^(a + b)` (`Scheme.IdealSheafData.IsEffectiveCartier.powTensorIso`). The line
bundle `𝒪_X(nD)` is the dual `𝓗om(I^n, 𝒪_X)` of `I^n`; dualising, and using that the dual of a
tensor product of line bundles is the tensor product of the duals, gives the **multiplication
isomorphisms**

`𝒪_X(aD) ⊗ 𝒪_X(bD) ≅ 𝒪_X((a + b)D)`

(`Scheme.IdealSheafData.IsEffectiveCartier.dualPowMulIso`). A product `φ ψ` of local sections
`φ` of `𝒪_X(aD)` and `ψ` of `𝒪_X(bD)`, which are functionals on `I^a` and `I^b`, is the functional
on `I^(a + b)` sending `t s`, for `t` in `I^b` and `s` in `I^a`, to `φ(s) ψ(t)`
(`Scheme.IdealSheafData.IsEffectiveCartier.whiskerLeft_dualPowMulIso_hom_comp_ev`). The
multiplication is compatible with the inclusions `𝒪_X(aD) ⟶ 𝒪_X(a'D)` for `a ≤ a'`, the duals of
`I^a' ⊆ I^a`
(`Scheme.IdealSheafData.IsEffectiveCartier.pre_sheafOfLE_whiskerRight_dualPowMulIso_hom`): a
function with a pole of order at most `a` along `D`, viewed as one with a pole of order at most
`a'`, has the same products.

## Main declarations

* `Scheme.IdealSheafData.IsEffectiveCartier.powTensorIso`: `I^b ⊗ I^a ≅ I^(a + b)`;
* `Scheme.IdealSheafData.IsEffectiveCartier.dualPowMulIso`: `𝒪_X(aD) ⊗ 𝒪_X(bD) ≅ 𝒪_X((a + b)D)`,
  with its evaluation formula
  `Scheme.IdealSheafData.IsEffectiveCartier.whiskerLeft_dualPowMulIso_hom_comp_ev`;
* `Scheme.IdealSheafData.IsEffectiveCartier.pre_sheafOfLE_whiskerRight_dualPowMulIso_hom`:
  compatibility with the inclusions `𝒪_X(aD) ⟶ 𝒪_X(a'D)`;
* `Scheme.IdealSheafData.IsEffectiveCartier.dualPowMulIsoOfEq` and
  `Scheme.IdealSheafData.IsEffectiveCartier.whiskerRight_dualPowMulIsoOfEq_hom`: the same, for a
  family of modules identified with the `𝒪_X(nD)`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

noncomputable section

variable {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsEffectiveCartier)

/-- **The ideal sheaf of `(a + b)D`**: multiplication of local functions is an isomorphism
`I^b ⊗ I^a ≅ I^(a + b)`, since `aD` is effective Cartier. -/
def powTensorIso (a b : ℕ) : (I ^ b).sheaf ⊗ (I ^ a).sheaf ≅ (I ^ (a + b)).sheaf :=
  sheafMulIso (I ^ b) (TauCeti.isEffectiveCartier_pow hI a) ≪≫
    eqToIso (congrArg sheaf (by rw [← pow_add, add_comm]))

/-- The isomorphism `I^b ⊗ I^a ≅ I^(a + b)` multiplies local functions. -/
@[reassoc]
theorem powTensorIso_hom_sheafι (a b : ℕ) :
    (powTensorIso hI a b).hom ≫ (I ^ (a + b)).sheafι =
      ((I ^ b).sheafι ⊗ₘ (I ^ a).sheafι) ≫ (λ_ (𝟙_ _)).hom :=
  (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (eqToHom_sheafι (by rw [← pow_add, add_comm] : I ^ b * I ^ a = I ^ (a + b)))).trans
    ((congrArg (· ≫ _) (sheafMulIso_hom _ _)).trans (sheafMul_sheafι _ _)))

/-- The multiplication of ideal sheaves is compatible with their inclusions: for `a ≤ a'`,
`I^b ⊗ I^a' ⟶ I^b ⊗ I^a` followed by multiplication is multiplication followed by
`I^(a' + b) ⟶ I^(a + b)`. -/
@[reassoc]
theorem whiskerLeft_sheafOfLE_powTensorIso_hom {a a' : ℕ} (h : a ≤ a') (b : ℕ) :
    (I ^ b).sheaf ◁ sheafOfLE (pow_le_pow_right_of_le_one' le_top h) ≫ (powTensorIso hI a b).hom =
      (powTensorIso hI a' b).hom ≫
        sheafOfLE (pow_le_pow_right_of_le_one' le_top (Nat.add_le_add_right h b)) := by
  refine (cancel_mono (I ^ (a + b)).sheafι).mp ?_
  refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (powTensorIso_hom_sheafι hI a b)).trans ?_)).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (sheafOfLE_sheafι _)).trans
      (powTensorIso_hom_sheafι hI a' b))).symm
  rw [← id_tensorHom]
  exact (tensorHom_comp_tensorHom_assoc _ _ _ _ _).trans
    ((congrArg (fun g ↦ (g ⊗ₘ _) ≫ _) (Category.id_comp _)).trans
      (congrArg (fun g ↦ (_ ⊗ₘ g) ≫ _) (sheafOfLE_sheafι _)))

/-- **The multiplication of the line bundles of multiples of `D`**:
`𝒪_X(aD) ⊗ 𝒪_X(bD) ≅ 𝒪_X((a + b)D)`, where `𝒪_X(nD) = 𝓗om(I^n, 𝒪_X)`. It is the dual of the
multiplication `I^b ⊗ I^a ≅ I^(a + b)` of ideal sheaves, through the dual of a tensor product of
line bundles. -/
def dualPowMulIso (a b : ℕ) :
    (ihom (I ^ a).sheaf).obj (𝟙_ _) ⊗ (ihom (I ^ b).sheaf).obj (𝟙_ _) ≅
      (ihom (I ^ (a + b)).sheaf).obj (𝟙_ _) :=
  (InvertibleSheaf.ihomUnitTensorIso ⟨_, (TauCeti.isEffectiveCartier_pow hI a).isInvertible_sheaf⟩
      ⟨_, (TauCeti.isEffectiveCartier_pow hI b).isInvertible_sheaf⟩).symm ≪≫
    { hom := (pre (powTensorIso hI a b).inv).app (𝟙_ _)
      inv := (pre (powTensorIso hI a b).hom).app (𝟙_ _)
      hom_inv_id := by
        rw [← NatTrans.comp_app, ← pre_map, Iso.hom_inv_id, pre_id, NatTrans.id_app]
      inv_hom_id := by
        rw [← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id, pre_id, NatTrans.id_app] }

/-- **The product of local sections of `𝒪_X(aD)` and `𝒪_X(bD)`**: viewing local sections `φ` of
`𝒪_X(aD)` and `ψ` of `𝒪_X(bD)` as functionals on `I^a` and `I^b`, the product `φ ψ` evaluates on
`t s ∈ I^(a + b)`, for `t ∈ I^b` and `s ∈ I^a`, to `φ(s) ψ(t)`. -/
@[reassoc]
theorem whiskerLeft_dualPowMulIso_hom_comp_ev (a b : ℕ) :
    (I ^ (a + b)).sheaf ◁ (dualPowMulIso hI a b).hom ≫
        (ihom.ev (I ^ (a + b)).sheaf).app (𝟙_ _) =
      (powTensorIso hI a b).inv ▷ _ ≫ (α_ _ _ _).hom ≫ (I ^ b).sheaf ◁ (α_ _ _ _).inv ≫
        (I ^ b).sheaf ◁ ((ihom.ev (I ^ a).sheaf).app (𝟙_ _) ▷ (ihom (I ^ b).sheaf).obj (𝟙_ _)) ≫
        (I ^ b).sheaf ◁ (λ_ _).hom ≫ (ihom.ev (I ^ b).sheaf).app (𝟙_ _) := by
  rw [dualPowMulIso, Iso.trans_hom, Iso.symm_hom, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, id_tensor_pre_app_comp_ev, whisker_exchange_assoc,
    InvertibleSheaf.whiskerLeft_ihomUnitTensorIso_inv_comp_ev
      ⟨_, (TauCeti.isEffectiveCartier_pow hI a).isInvertible_sheaf⟩
      ⟨_, (TauCeti.isEffectiveCartier_pow hI b).isInvertible_sheaf⟩]

/-- **The multiplication is compatible with the inclusions `𝒪_X(aD) ⟶ 𝒪_X(a'D)`**: for
`a ≤ a'`, including `𝒪_X(aD)` into `𝒪_X(a'D)`, by precomposition with `I^a' ⊆ I^a`, and
multiplying by `𝒪_X(bD)` is multiplying and then including `𝒪_X((a + b)D)` into
`𝒪_X((a' + b)D)`. -/
@[reassoc]
theorem pre_sheafOfLE_whiskerRight_dualPowMulIso_hom {a a' : ℕ} (h : a ≤ a') (b : ℕ) :
    (pre (sheafOfLE (pow_le_pow_right_of_le_one' le_top h))).app (𝟙_ _) ▷ _ ≫
        (dualPowMulIso hI a' b).hom =
      (dualPowMulIso hI a b).hom ≫
        (pre (sheafOfLE (pow_le_pow_right_of_le_one' le_top (Nat.add_le_add_right h b)))).app
          (𝟙_ _) := by
  have hι : (powTensorIso hI a' b).inv ≫
      (I ^ b).sheaf ◁ sheafOfLE (pow_le_pow_right_of_le_one' le_top h) =
      sheafOfLE (pow_le_pow_right_of_le_one' le_top (Nat.add_le_add_right h b)) ≫
        (powTensorIso hI a b).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv,
      whiskerLeft_sheafOfLE_powTensorIso_hom hI h b]
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, whiskerLeft_dualPowMulIso_hom_comp_ev,
    id_tensor_pre_app_comp_ev, whisker_exchange_assoc, whisker_exchange_assoc,
    whiskerLeft_dualPowMulIso_hom_comp_ev, ← comp_whiskerRight_assoc, ← hι,
    comp_whiskerRight_assoc]
  congr 1
  -- Both sides evaluate `I^a'` against `𝒪_X(aD)` inside the evaluation of `I^b` against
  -- `𝒪_X(bD)`; the inclusion moves across the inner evaluation.
  rw [associator_naturality_right_assoc, associator_naturality_middle_assoc]
  congr 1
  simp only [← MonoidalCategory.whiskerLeft_comp_assoc]
  congr 2
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    id_tensor_pre_app_comp_ev, comp_whiskerRight_assoc, associator_inv_naturality_left_assoc]

variable {L : ℕ → X.Modules} (hL : ∀ n, L n = (ihom (I ^ n).sheaf).obj (𝟙_ _))

/-- The multiplication `𝒪_X(aD) ⊗ 𝒪_X(bD) ≅ 𝒪_X((a + b)D)`, transported to a family `L` of
`𝒪_X`-modules identified with the `𝒪_X(nD)`, such as line bundles of multiples of `D` defined as
duals of invertible ideal sheaves. -/
def dualPowMulIsoOfEq (a b : ℕ) : L a ⊗ L b ≅ L (a + b) :=
  eqToIso (congrArg₂ (· ⊗ ·) (hL a) (hL b)) ≪≫ dualPowMulIso hI a b ≪≫
    eqToIso (hL (a + b)).symm

/-- The transported multiplication is `dualPowMulIso` between the identifications `hL`. -/
theorem dualPowMulIsoOfEq_hom (a b : ℕ) :
    (dualPowMulIsoOfEq hI hL a b).hom = eqToHom (congrArg₂ (· ⊗ ·) (hL a) (hL b)) ≫
      (dualPowMulIso hI a b).hom ≫ eqToHom (hL (a + b)).symm := by
  simp [dualPowMulIsoOfEq]

/-- The transported multiplication `L a ⊗ L b ≅ L (a + b)` is compatible with the transported
inclusions `L a ⟶ L a'` for `a ≤ a'`. -/
@[reassoc]
theorem whiskerRight_dualPowMulIsoOfEq_hom {a a' : ℕ} (h : a ≤ a') (b : ℕ) :
    (eqToHom (hL a) ≫ (pre (sheafOfLE (pow_le_pow_right_of_le_one' le_top h))).app (𝟙_ _) ≫
        eqToHom (hL a').symm) ▷ L b ≫ (dualPowMulIsoOfEq hI hL a' b).hom =
      (dualPowMulIsoOfEq hI hL a b).hom ≫ eqToHom (hL (a + b)) ≫
        (pre (sheafOfLE (pow_le_pow_right_of_le_one' le_top (Nat.add_le_add_right h b)))).app
          (𝟙_ _) ≫ eqToHom (hL (a' + b)).symm := by
  obtain rfl : L = fun n ↦ (ihom (I ^ n).sheaf).obj (𝟙_ _) := funext hL
  simpa [dualPowMulIsoOfEq] using pre_sheafOfLE_whiskerRight_dualPowMulIso_hom hI h b

end

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
