/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.Over

/-!
# Fibres over a point of an affine open

Let `f : X ⟶ Y` be a morphism of schemes, `V ⊆ Y` an affine open and `U = f⁻¹ V` affine. Through
the ring map `f^* : Γ(Y, V) → Γ(X, U)`, the points of `X` over a point `y ∈ V` are the primes of
`Γ(X, U)` lying over the prime `p_y` of `Γ(Y, V)` corresponding to `y`
(`AlgebraicGeometry.IsAffineOpen.preimageSingletonEquivPrimesOver`). This is how the fibre of a
finite (hence affine) morphism over a point is read off from the rings of an affine
neighbourhood, and it rests on Mathlib's `AlgebraicGeometry.IsAffineOpen.comap_primeIdealOf_appLE`.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- On an affine open `U`, the prime of `Γ(X, U)` of a point `fromSpec q` is `q`. -/
theorem IsAffineOpen.primeIdealOf_fromSpec {U : X.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(X, U)) (hq : hU.fromSpec q ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec q, hq⟩ = q :=
  hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨_, hq⟩)

variable (f : X ⟶ Y) {V : Y.Opens} (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U)
  (hUV : f ⁻¹ᵁ V = U) {y : Y} (hy : y ∈ V)

/-- The points of `X` over `y ∈ V`, for affine opens `V ⊆ Y` and `U = f⁻¹ V ⊆ X`, are the primes of
`Γ(X, U)` over the prime of `y` in `Γ(Y, V)`, through `f^* : Γ(Y, V) → Γ(X, U)`. -/
noncomputable def IsAffineOpen.preimageSingletonEquivPrimesOver :
    letI := (f.appLE V U hUV.ge).hom.toAlgebra
    (f ⁻¹' {y} : Set X) ≃ (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primesOver Γ(X, U) :=
  letI := (f.appLE V U hUV.ge).hom.toAlgebra
  have hmem (x : X) (hx : f x = y) : x ∈ U := hUV ▸ show f x ∈ V from hx ▸ hy
  have hran (q : PrimeSpectrum Γ(X, U)) : hU.fromSpec q ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact ⟨q, rfl⟩
  -- The prime of `x ∈ U` contracts to the prime of `f x`.
  have hcomap (x : X) (hx : x ∈ U) : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.under Γ(Y, V) =
      (hV.primeIdealOf ⟨f x, hUV.ge hx⟩).asIdeal :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV.ge hx).1)
  { toFun x :=
      ⟨(hU.primeIdealOf ⟨x, hmem x x.2⟩).asIdeal, inferInstance, ⟨by
        rw [hcomap]
        congr
        exact x.2.symm⟩⟩
    invFun q :=
      ⟨hU.fromSpec ⟨q.1, q.2.1⟩, by
        have h := hcomap (hU.fromSpec ⟨q.1, q.2.1⟩) (hran _)
        rw [hU.primeIdealOf_fromSpec _ (hran _)] at h
        have := q.2.2
        rw [← Ideal.over_def q.1 (hV.primeIdealOf ⟨y, hy⟩).asIdeal] at h
        have h' := congr(hV.fromSpec $(PrimeSpectrum.ext h))
        rw [hV.fromSpec_primeIdealOf, hV.fromSpec_primeIdealOf] at h'
        exact h'.symm⟩
    left_inv x := Subtype.ext <| hU.fromSpec_primeIdealOf ⟨x, _⟩
    right_inv q := Subtype.ext <| congr($(hU.primeIdealOf_fromSpec ⟨q.1, q.2.1⟩ (hran _)).asIdeal) }

@[simp]
theorem IsAffineOpen.coe_preimageSingletonEquivPrimesOver_apply (x : (f ⁻¹' {y} : Set X))
    (hx : x.1 ∈ U) :
    (hV.preimageSingletonEquivPrimesOver f hU hUV hy x).1 = (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
  (rfl)

@[simp]
theorem IsAffineOpen.coe_preimageSingletonEquivPrimesOver_symm_apply
    (q : letI := (f.appLE V U hUV.ge).hom.toAlgebra
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primesOver Γ(X, U)) :
    ((hV.preimageSingletonEquivPrimesOver f hU hUV hy).symm q).1 = hU.fromSpec ⟨q.1, q.2.1⟩ :=
  (rfl)

end AlgebraicGeometry
