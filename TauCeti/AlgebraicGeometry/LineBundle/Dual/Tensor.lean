/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.FinitePresentation
public import TauCeti.AlgebraicGeometry.LineBundle.Basic
public import TauCeti.AlgebraicGeometry.Modules.Dual
public import TauCeti.CategoryTheory.Monoidal.Rigid.Closed

/-!
# Duals of tensor products of line bundles

The internal-Hom dual `L^∨ = 𝓗om(L, 𝒪_X)` of a line bundle `L` is a left dual of `L` in the
symmetric monoidal category `X.Modules`, with evaluation the evaluation of the internal Hom
(`InvertibleSheaf.exactPairingIhomUnit`). Tensor products of exact pairings are exact pairings,
and duals are unique, so the dual of a tensor product of line bundles is the tensor product of
their duals: `(K ⊗ L)^∨ ≅ L^∨ ⊗ K^∨` (`InvertibleSheaf.ihomUnitTensorIso`). Its inverse pairs
`s ⊗ t` against `φ ⊗ ψ` as `φ(t) ψ(s)`
(`InvertibleSheaf.whiskerLeft_ihomUnitTensorIso_inv_comp_ev`).

## Main declarations

* `InvertibleSheaf.exactPairingIhomUnit`: `L^∨` is a left dual of `L`;
* `InvertibleSheaf.ihomUnitTensorIso`: `(K ⊗ L)^∨ ≅ L^∨ ⊗ K^∨`, with its evaluation formula
  `InvertibleSheaf.whiskerLeft_ihomUnitTensorIso_inv_comp_ev`.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace InvertibleSheaf

variable {X : Scheme.{u}}

/-- The internal-Hom dual `L^∨ = 𝓗om(L, 𝒪_X)` of a line bundle is a left dual of `L`, the
evaluation of the pairing being the evaluation of the internal Hom
(`InvertibleSheaf.exactPairingIhomUnit_evaluation`).

This is not an instance: `X.Modules` may carry other duals of `L`. -/
@[reducible]
def exactPairingIhomUnit (L : InvertibleSheaf X) :
    ExactPairing ((ihom L.obj).obj (𝟙_ X.Modules)) L.obj :=
  have : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
  -- Instance search does not unfold `X.Modules`, so the sheaf is rebound with the type of sheaves
  -- of modules to find local freeness and finite type.
  let F : _root_.SheafOfModules X.ringCatSheaf := L.obj
  have : L.obj.IsLocallyFree := inferInstanceAs F.IsLocallyFree
  have : L.obj.IsFiniteType := inferInstanceAs F.IsFiniteType
  exactPairingOfIsIsoDualTensorIhom

/-- The evaluation of the pairing of `L^∨` with `L` is the evaluation of the internal Hom. -/
theorem exactPairingIhomUnit_evaluation (L : InvertibleSheaf X) :
    @ExactPairing.evaluation _ _ _ _ _ (exactPairingIhomUnit L) =
      (ihom.ev L.obj).app (𝟙_ X.Modules) := by
  have : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
  let F : _root_.SheafOfModules X.ringCatSheaf := L.obj
  have : L.obj.IsLocallyFree := inferInstanceAs F.IsLocallyFree
  have : L.obj.IsFiniteType := inferInstanceAs F.IsFiniteType
  exact exactPairingOfIsIsoDualTensorIhom_evaluation

/-- **The dual of a tensor product of line bundles**: `(K ⊗ L)^∨ ≅ L^∨ ⊗ K^∨`, from the
uniqueness of duals applied to the tensor product of the pairings of `L` and `K` with their
duals. -/
def ihomUnitTensorIso (L K : InvertibleSheaf X) :
    (ihom (K.obj ⊗ L.obj)).obj (𝟙_ X.Modules) ≅
      (ihom L.obj).obj (𝟙_ X.Modules) ⊗ (ihom K.obj).obj (𝟙_ X.Modules) :=
  letI := exactPairingIhomUnit L
  letI := exactPairingIhomUnit K
  ihomUnitIso _ _

/-- The inverse of `(K ⊗ L)^∨ ≅ L^∨ ⊗ K^∨` pairs `s ⊗ t` against `φ ⊗ ψ` as `φ(t) ψ(s)`: it
evaluates `L^∨` against `L` and then `K^∨` against `K`. -/
@[reassoc]
theorem whiskerLeft_ihomUnitTensorIso_inv_comp_ev (L K : InvertibleSheaf X) :
    (K.obj ⊗ L.obj) ◁ (ihomUnitTensorIso L K).inv ≫ (ihom.ev (K.obj ⊗ L.obj)).app (𝟙_ X.Modules) =
      (α_ _ _ _).hom ≫ K.obj ◁ (α_ _ _ _).inv ≫
        K.obj ◁ ((ihom.ev L.obj).app (𝟙_ X.Modules) ▷ (ihom K.obj).obj (𝟙_ X.Modules)) ≫
        K.obj ◁ (λ_ _).hom ≫ (ihom.ev K.obj).app (𝟙_ X.Modules) := by
  let := exactPairingIhomUnit L
  let := exactPairingIhomUnit K
  rw [ihomUnitTensorIso, whiskerLeft_ihomUnitIso_inv_comp_ev, ExactPairing.tensor_evaluation,
    exactPairingIhomUnit_evaluation, exactPairingIhomUnit_evaluation]
  simp [monoidalComp]

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
