/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Kaehler

/-!
# Derivations along formally étale algebras

Let `R → S → T` be a tower of commutative rings with `T` formally étale over `S`, and let `M` be a
`T`-module. Restricting `R`-derivations `T → M` along `S → T` is a bijection: every `R`-derivation
`S → M` extends uniquely to `T`. This is the base change `T ⊗[S] Ω[S⁄R] ≃ Ω[T⁄R]` of Mathlib's
`KaehlerDifferential.isBaseChange_of_formallyEtale`.

For an inclusion `U' ⊆ U` of affine opens of a scheme, it says that the derivations
`Γ(U, ⊤) → M` are the derivations `Γ(U', ⊤) → M`, for a `Γ(U', ⊤)`-module `M`: the change of chart
for the torsor of lifts along a first-order thickening (Stacks, Lemma 37.9.5 (04FJ)).

## Main declarations

* `Derivation.compAlgebraMap_bijective`: restriction of derivations along a formally étale
  algebra is bijective.
* `Derivation.compAlgebraMapEquiv`: the `T`-linear equivalence
  `Derivation R T M ≃ₗ[T] Derivation R S M` given by restriction along `S → T`.
-/

public section

open KaehlerDifferential

namespace Derivation

variable (R S T M : Type*) [CommRing R] [CommRing S] [CommRing T] [AddCommGroup M]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Module T M] [Module S M] [Module R M] [IsScalarTower S T M] [IsScalarTower R T M]
  [IsScalarTower R S M] [Algebra.FormallyEtale S T]

/-- Along a formally étale `S`-algebra `T`, every `R`-derivation `S → M` into a `T`-module `M`
extends uniquely to an `R`-derivation `T → M`. -/
theorem compAlgebraMap_bijective :
    Function.Bijective (compAlgebraMapL R S T M) := by
  have hb := isBaseChange_of_formallyEtale R S T
  refine ⟨fun D₁ D₂ e ↦ ?_, fun D ↦ ?_⟩
  · rw [← D₁.liftKaehlerDifferential_comp, ← D₂.liftKaehlerDifferential_comp]
    refine congrArg (LinearMap.compDer · (KaehlerDifferential.D R T)) ?_
    refine hb.algHom_ext' _ _ (Derivation.liftKaehlerDifferential_unique (M := M) _ _ ?_)
    ext s
    simpa using congr($e s)
  · refine ⟨(hb.lift D.liftKaehlerDifferential).compDer (KaehlerDifferential.D R T), ?_⟩
    ext s
    simpa using
      congr($(hb.lift_comp D.liftKaehlerDifferential) (KaehlerDifferential.D R S s))

/-- Along a formally étale `S`-algebra `T`, restriction `Derivation R T M ≃ₗ[T] Derivation R S M`
along `S → T` is an equivalence, for every `T`-module `M`. -/
noncomputable def compAlgebraMapEquiv :
    Derivation R T M ≃ₗ[T] Derivation R S M :=
  LinearEquiv.ofBijective (compAlgebraMapL R S T M) (compAlgebraMap_bijective R S T M)

@[simp]
theorem compAlgebraMapEquiv_apply (D : Derivation R T M) (s : S) :
    compAlgebraMapEquiv R S T M D s = D (algebraMap S T s) := by
  rfl

@[simp]
theorem compAlgebraMap_compAlgebraMapEquiv_symm (D : Derivation R S M) :
    ((compAlgebraMapEquiv R S T M).symm D).compAlgebraMap S = D :=
  (compAlgebraMapEquiv R S T M).apply_symm_apply D

@[simp]
theorem compAlgebraMapEquiv_symm_apply_algebraMap (D : Derivation R S M) (s : S) :
    (compAlgebraMapEquiv R S T M).symm D (algebraMap S T s) = D s := by
  rw [← compAlgebraMapEquiv_apply, LinearEquiv.apply_symm_apply]

end Derivation
