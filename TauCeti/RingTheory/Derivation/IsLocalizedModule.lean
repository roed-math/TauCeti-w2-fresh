/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Derivations into a localized module

Let `A` be an `R`-algebra, `B` an `A`-algebra, and `ι : M →ₗ[B] M'` a localization of
`B`-modules at a submonoid `S` of `B`. If `Ω[A⁄R]` is a finitely presented `A`-module (for example
if `A` is smooth over `R`), then post-composition with `ι` makes `Derivation R A M'` the
localization of `Derivation R A M` at `S`: derivations commute with localization of the target.

The proof goes through `B ⊗[A] Ω[A⁄R]`, a finitely presented `B`-module: a derivation
`A → M` is a `B`-linear map `B ⊗[A] Ω[A⁄R] → M`, and Mathlib's
`Module.FinitePresentation.exists_lift_of_isLocalizedModule` and
`Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule` lift such maps along `ι` after
multiplication by an element of `S`.

This is the algebraic input for the quasi-coherence of the sheaf of derivations into the ideal of
a first-order thickening.

## Main declarations

* `Derivation.baseChangeKaehler D`: a derivation `A → M` into a `B`-module, as a `B`-linear map
  `B ⊗[A] Ω[A⁄R] → M`, with converse `Derivation.ofBaseChangeKaehler`.
* `LinearMap.compDerRestrictScalars ι`: post-composition of derivations with a `B`-linear map
  `ι`, as a `B`-linear map.
* `LinearMap.isLocalizedModule_compDerRestrictScalars`: it is a localization at `S` when `ι` is
  and `Ω[A⁄R]` is finitely presented.
-/

public section

open TensorProduct

variable {R A B M M' : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] [Module R M]
  [IsScalarTower R A M]
  [AddCommGroup M'] [Module A M'] [Module B M'] [IsScalarTower A B M'] [Module R M']
  [IsScalarTower R A M']

namespace Derivation

/-- A derivation `A → M` into a `B`-module, as a `B`-linear map `B ⊗[A] Ω[A⁄R] → M`. -/
noncomputable def baseChangeKaehler (D : Derivation R A M) : B ⊗[A] Ω[A⁄R] →ₗ[B] M :=
  D.liftKaehlerDifferential.liftBaseChange B

theorem baseChangeKaehler_tmul (D : Derivation R A M) (b : B) (ω : Ω[A⁄R]) :
    D.baseChangeKaehler (b ⊗ₜ ω) = b • D.liftKaehlerDifferential ω :=
  (rfl)

@[simp]
theorem baseChangeKaehler_tmul_D (D : Derivation R A M) (b : B) (a : A) :
    D.baseChangeKaehler (b ⊗ₜ KaehlerDifferential.D R A a) = b • D a := by
  simp [baseChangeKaehler_tmul]

/-- The derivation `A → M` obtained from a `B`-linear map `B ⊗[A] Ω[A⁄R] → M`. -/
noncomputable def ofBaseChangeKaehler (φ : B ⊗[A] Ω[A⁄R] →ₗ[B] M) : Derivation R A M :=
  ((φ.restrictScalars A).comp (TensorProduct.mk A B Ω[A⁄R] 1)).compDer (KaehlerDifferential.D R A)

@[simp]
theorem ofBaseChangeKaehler_apply (φ : B ⊗[A] Ω[A⁄R] →ₗ[B] M) (a : A) :
    ofBaseChangeKaehler (R := R) φ a = φ (1 ⊗ₜ KaehlerDifferential.D R A a) :=
  (rfl)

end Derivation

variable [Algebra R B] [IsScalarTower R B M] [IsScalarTower R B M']

namespace LinearMap

variable (R A) in
/-- Post-composition of `R`-derivations of `A` with a `B`-linear map `ι : M →ₗ[B] M'`, as a
`B`-linear map. -/
def compDerRestrictScalars (ι : M →ₗ[B] M') : Derivation R A M →ₗ[B] Derivation R A M' where
  toFun D := (ι.restrictScalars A).compDer D
  map_add' D₁ D₂ := map_add _ D₁ D₂
  map_smul' b D := by ext; simp

@[simp]
theorem compDerRestrictScalars_apply (ι : M →ₗ[B] M') (D : Derivation R A M) (a : A) :
    compDerRestrictScalars R A ι D a = ι (D a) :=
  (rfl)

variable [Module.FinitePresentation A Ω[A⁄R]] (S : Submonoid B) (ι : M →ₗ[B] M')
  [IsLocalizedModule S ι]

/-- If `Ω[A⁄R]` is a finitely presented `A`-module, then post-composition with a localization
`ι : M →ₗ[B] M'` at `S` is a localization `Derivation R A M →ₗ[B] Derivation R A M'` at `S`:
`R`-derivations of `A` commute with localization of the target. -/
instance isLocalizedModule_compDerRestrictScalars :
    IsLocalizedModule S (compDerRestrictScalars R A ι) where
  map_units s := by
    have hs := (Module.End.isUnit_iff _).1 (IsLocalizedModule.map_units ι s)
    refine (Module.End.isUnit_iff _).2 ⟨fun D₁ D₂ e ↦ Derivation.ext fun a ↦ hs.1 ?_, fun D ↦ ?_⟩
    · simpa using congr($e a)
    · let u : Module.End B M' := ↑(IsLocalizedModule.map_units ι s).unit⁻¹
      refine ⟨(u.restrictScalars A).compDer D, Derivation.ext fun a ↦ ?_⟩
      simpa using Module.End.isUnit_apply_inv_apply_of_isUnit (IsLocalizedModule.map_units ι s)
        (D a)
  surj D := by
    obtain ⟨φ, s, e⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S ι
      D.baseChangeKaehler
    refine ⟨⟨Derivation.ofBaseChangeKaehler φ, s⟩, Derivation.ext fun a ↦ ?_⟩
    simpa using (congr($e (1 ⊗ₜ KaehlerDifferential.D R A a))).symm
  exists_of_eq {D₁ D₂} e := by
    have h : (ι.restrictScalars A).comp D₁.liftKaehlerDifferential =
        (ι.restrictScalars A).comp D₂.liftKaehlerDifferential :=
      Derivation.liftKaehlerDifferential_unique _ _ <| Derivation.ext fun a ↦ by
        simpa using congr($e a)
    obtain ⟨s, hs⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S ι
      (D₁.baseChangeKaehler (B := B)) D₂.baseChangeKaehler <| by
        refine TensorProduct.AlgebraTensorModule.ext fun b ω ↦ ?_
        simpa [Derivation.baseChangeKaehler_tmul] using congr(b • $h ω)
    refine ⟨s, Derivation.ext fun a ↦ ?_⟩
    simpa using congr($hs (1 ⊗ₜ KaehlerDifferential.D R A a))

end LinearMap
