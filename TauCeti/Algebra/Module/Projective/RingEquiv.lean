/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Finite projective modules along a ring isomorphism

Let `σ : A →+* B` be a ring isomorphism and `e : M ≃ₛₗ[σ] N` a `σ`-semilinear equivalence from an
`A`-module to a `B`-module. This is how the sections of a sheaf of modules are compared along an
isomorphism of rings of functions, for example when a scheme isomorphism identifies the functions
on two opens. If `M` is finitely generated, so is `N`; Mathlib's `Module.Projective.of_equiv`
transports projectivity. If moreover `M` is flat, the rank of `N` at a prime `q` of `B` is the rank
of `M` at `σ⁻¹(q)`: `N` is the base change of `M` along `σ`.

## Main results

* `LinearMap.finite_of_surjective`: the image of a finitely generated module under a
  surjective semilinear map is finitely generated.
* `LinearEquiv.rankAtStalk_eq`: the rank at the stalks is carried along a
  semilinear equivalence over a ring isomorphism.
* `LinearEquiv.map_range_eq_range`, `LinearEquiv.projective_quotient_range` and
  `LinearEquiv.rankAtStalk_quotient_range_eq`: semilinear equivalences intertwining two linear
  maps carry the range of one onto the range of the other, hence projectivity and the ranks of
  their cokernels.
-/

public section

open TensorProduct

variable {A B M N : Type*} [CommRing A] [CommRing B] [AddCommGroup M] [AddCommGroup N]
  [Module A M] [Module B N]

/-- The image of a finitely generated module under a surjective semilinear map is finitely
generated. -/
theorem LinearMap.finite_of_surjective {σ : A →+* B} (f : M →ₛₗ[σ] N)
    (hf : Function.Surjective f) [Module.Finite A M] : Module.Finite B N := by
  let : Algebra A B := σ.toAlgebra
  let : Module A N := Module.compHom N σ
  have : IsScalarTower A B N := ⟨fun a b n ↦ mul_smul (σ a) b n⟩
  -- over `A`, acting through `σ`, the map `f` is linear
  let g : M →ₗ[A] N :=
    { toFun := f, map_add' := f.map_add, map_smul' := fun a m ↦ f.map_smulₛₗ a m }
  have : Module.Finite A N := Module.Finite.of_surjective g hf
  exact Module.Finite.of_restrictScalars_finite A B N

/-- The rank at the stalks is carried along a semilinear equivalence over a ring isomorphism
`σ : A ≃+* B`: the rank of the image at a prime `q` of `B` is the rank at the prime `σ⁻¹(q)`. -/
theorem LinearEquiv.rankAtStalk_eq {σ : A →+* B} {σ' : B →+* A} [RingHomInvPair σ σ']
    [RingHomInvPair σ' σ] (e : M ≃ₛₗ[σ] N) [Module.Flat A M] [Module.Finite A M]
    (q : PrimeSpectrum B) :
    Module.rankAtStalk N q = Module.rankAtStalk M (q.comap σ) := by
  let : Algebra A B := σ.toAlgebra
  let : Module A N := Module.compHom N σ
  have : IsScalarTower A B N := ⟨fun a b n ↦ mul_smul (σ a) b n⟩
  let f : M →ₗ[A] N :=
    { toFun := e, map_add' := e.map_add, map_smul' := fun a m ↦ e.map_smulₛₗ a m }
  -- `N` is the base change of `M` along `σ`
  let g : N →ₗ[B] B ⊗[A] M :=
    { toFun n := 1 ⊗ₜ e.symm n
      map_add' _ _ := by rw [map_add, TensorProduct.tmul_add]
      map_smul' b n := by
        rw [e.symm.map_smulₛₗ, TensorProduct.tmul_smul, RingHom.id_apply,
          TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def,
          mul_one, mul_one, RingHom.algebraMap_toAlgebra, RingHomInvPair.comp_apply_eq₂] }
  let i : B ⊗[A] M ≃ₗ[B] N := LinearEquiv.ofLinearMap (f.liftBaseChange B) g
    (by ext n; simp [g, f])
    (by ext m; simp [g, f])
  rw [← Module.rankAtStalk_eq_of_equiv i, Module.rankAtStalk_baseChange,
    RingHom.algebraMap_toAlgebra]

section QuotientRange

variable {P Q P' Q' : Type*} [AddCommGroup P] [AddCommGroup Q] [AddCommGroup P'] [AddCommGroup Q']
  [Module A P] [Module A Q] [Module B P'] [Module B Q'] {σ : A →+* B} {σ' : B →+* A}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] {f : P →ₗ[A] Q} {f' : P' →ₗ[B] Q'}
  (eP : P ≃ₛₗ[σ] P') (eQ : Q ≃ₛₗ[σ] Q')

/-- Semilinear equivalences intertwining two linear maps carry the range of one onto the range of
the other. -/
theorem LinearEquiv.map_range_eq_range (h : ∀ x, eQ (f x) = f' (eP x)) :
    (LinearMap.range f).map (eQ : Q →ₛₗ[σ] Q') = LinearMap.range f' := by
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨eP x, (h x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨f (eP.symm x), ⟨eP.symm x, rfl⟩, (h _).trans (by rw [LinearEquiv.apply_symm_apply])⟩

/-- Semilinear equivalences intertwining two linear maps carry projectivity of the cokernel of one
to the cokernel of the other. -/
theorem LinearEquiv.projective_quotient_range (h : ∀ x, eQ (f x) = f' (eP x))
    [Module.Projective A (Q ⧸ LinearMap.range f)] :
    Module.Projective B (Q' ⧸ LinearMap.range f') :=
  .of_equiv (Submodule.Quotient.equiv _ _ eQ (eP.map_range_eq_range eQ h))

/-- Semilinear equivalences intertwining two linear maps carry the ranks of the cokernel of one to
the cokernel of the other: the rank at `q` is the rank at `σ⁻¹(q)`. -/
theorem LinearEquiv.rankAtStalk_quotient_range_eq (h : ∀ x, eQ (f x) = f' (eP x))
    [Module.Finite A Q] [Module.Flat A (Q ⧸ LinearMap.range f)] (q : PrimeSpectrum B) :
    Module.rankAtStalk (Q' ⧸ LinearMap.range f') q =
      Module.rankAtStalk (Q ⧸ LinearMap.range f) (q.comap σ) :=
  (Submodule.Quotient.equiv _ _ eQ (eP.map_range_eq_range eQ h)).rankAtStalk_eq q

end QuotientRange
