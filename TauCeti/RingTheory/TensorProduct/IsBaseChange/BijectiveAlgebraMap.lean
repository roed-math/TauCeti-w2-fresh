/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Base change along bijective ring maps

Base change along a bijective ring map `R → S` does nothing: every `S`-module `N` is the base
change of its restriction of scalars to `R`, through the identity
(`IsBaseChange.of_bijective_algebraMap`). Consequently a base change square of modules survives
replacing the rings by isomorphic ones. If `f : M → N` exhibits `N` as the base change of `M`
along `R → T`, and `A → R` and `B → T` are bijective with `A → B → T` equal to `A → R → T`, then
`f` also exhibits `N` as the base change of `M` along `A → B`
(`IsBaseChange.restrictScalars_of_bijective`).

This is how a base change statement proved over the coefficient rings of a chart is read over
the rings of functions on open subschemes isomorphic to their spectra.

## Main results

* `IsBaseChange.of_bijective_algebraMap`: an `S`-module is the base change of itself along a
  bijective `R → S`.
* `IsBaseChange.of_bijective_algebraMap_right`: a base change along `A → T` is a base change
  along `A → B` when `B → T` is bijective.
* `IsBaseChange.restrictScalars_of_bijective`: a base change along `R → T` is a base change along
  `A → B` when `A → R` and `B → T` are bijective.
-/

public section

open scoped TensorProduct

section

variable {R S N : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- If `algebraMap R S` is bijective, every `S`-module is its own base change along `R → S`,
through the identity. -/
theorem IsBaseChange.of_bijective_algebraMap (h : Function.Bijective (algebraMap R S)) :
    IsBaseChange S ((LinearMap.id : N →ₗ[S] N).restrictScalars R) := by
  refine IsBaseChange.iff_liftBaseChange_bijective.mpr ⟨fun x y hxy ↦ ?_, fun n ↦
    ⟨1 ⊗ₜ n, by simp⟩⟩
  -- `n ↦ 1 ⊗ n` is a left inverse: every scalar of `S` comes from `R`
  have key (x : S ⊗[R] N) :
      (1 : S) ⊗ₜ[R] (((LinearMap.id : N →ₗ[S] N).restrictScalars R).liftBaseChange S x) = x := by
    induction x with
    | add x y hx hy => rw [map_add, TensorProduct.tmul_add, hx, hy]
    | tmul s n =>
      obtain ⟨r, rfl⟩ := h.2 s
      rw [LinearMap.liftBaseChange_tmul, LinearMap.restrictScalars_apply, LinearMap.id_apply,
        algebraMap_smul, TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul']
  rw [← key x, ← key y, hxy]

end

section

variable {A B T M N : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring T] [Algebra A B]
  [Algebra A T] [Algebra B T] [IsScalarTower A B T]
  [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N] [Module B N] [Module T N]
  [IsScalarTower A B N] [IsScalarTower B T N] [IsScalarTower A T N]

/-- If `f` exhibits `N` as the base change of `M` along `A → T` and `algebraMap B T` is
bijective, then `f` exhibits `N` as the base change of `M` along `A → B`. -/
theorem IsBaseChange.of_bijective_algebraMap_right {f : M →ₗ[A] N}
    (hb : Function.Bijective (algebraMap B T)) (hf : IsBaseChange T f) : IsBaseChange B f := by
  let e : B ⊗[A] M ≃ₗ[A] T ⊗[A] M :=
    TensorProduct.congr (LinearEquiv.ofBijective (IsScalarTower.toAlgHom A B T).toLinearMap hb)
      (LinearEquiv.refl A M)
  have key (x : B ⊗[A] M) : f.liftBaseChange B x = f.liftBaseChange T (e x) := by
    induction x with
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | tmul s m =>
      rw [LinearMap.liftBaseChange_tmul, TensorProduct.congr_tmul, LinearMap.liftBaseChange_tmul]
      exact (algebraMap_smul T s (f m)).symm
  refine IsBaseChange.iff_liftBaseChange_bijective.mpr ?_
  rw [show ⇑(f.liftBaseChange B) = f.liftBaseChange T ∘ e from funext key]
  exact hf.liftBaseChange_bijective.comp e.bijective

end

section

variable {A B R T M N : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring R] [CommSemiring T]
  [Algebra A B] [Algebra A R] [Algebra R T] [Algebra B T] [Algebra A T] [IsScalarTower A B T]
  [IsScalarTower A R T] [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower A R M]
  [AddCommMonoid N] [Module A N] [Module B N] [Module R N] [Module T N] [IsScalarTower A B N]
  [IsScalarTower B T N] [IsScalarTower A T N] [IsScalarTower R T N] [IsScalarTower A R N]

/-- **Base change is invariant under isomorphisms of the rings.** If `f` exhibits `N` as the base
change of `M` along `R → T`, and `algebraMap A R` and `algebraMap B T` are bijective, with
`A → B → T` equal to `A → R → T`, then `f` exhibits `N` as the base change of `M` along
`A → B`. -/
theorem IsBaseChange.restrictScalars_of_bijective {f : M →ₗ[R] N}
    (ha : Function.Bijective (algebraMap A R)) (hb : Function.Bijective (algebraMap B T))
    (hf : IsBaseChange T f) : IsBaseChange B (f.restrictScalars A) :=
  .of_bijective_algebraMap_right hb ((IsBaseChange.of_bijective_algebraMap (N := M) ha).comp hf)

end
