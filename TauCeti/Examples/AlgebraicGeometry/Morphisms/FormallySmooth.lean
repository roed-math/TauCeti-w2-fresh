/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.Affine

/-!
# Examples of formally smooth and formally étale morphisms

These examples test the lifting definitions of formal smoothness and formal étaleness:

* identities are formally étale;
* affine space `𝔸(n; S) ⟶ S` is formally smooth over every base;
* for a field `k`, the origin `Spec k ⟶ 𝔸¹_k` is not formally smooth, since the ideal `(x)` of
  `k[x]` is not idempotent.

## References

* [Stacks Project, Definition 37.11.1](https://stacks.math.columbia.edu/tag/02H0).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Polynomial TauCeti.AlgebraicGeometry

/-- Identities are formally étale. -/
example (X : Scheme.{u}) : FormallyEtale (𝟙 X) := inferInstance

/-- Affine space is formally smooth over every base. -/
example (n : Type u) (S : Scheme.{u}) : FormallySmooth (𝔸(n; S) ↘ S) := inferInstance

/-- The origin `Spec k ⟶ 𝔸¹_k`, cut out by `x`, is not formally smooth: the ideal `(x)` of
`k[x]` is not idempotent, as `x²` does not divide `x`. -/
theorem TauCeti.AlgebraicGeometry.not_formallySmooth_origin (k : Type u) [Field k] :
    ¬ FormallySmooth
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {(X : k[X])})))) := by
  rw [FormallySmooth.SpecMap_iff, CommRingCat.hom_ofHom, ← Ideal.Quotient.algebraMap_eq,
    RingHom.formallySmooth_algebraMap,
    Algebra.FormallySmooth.iff_of_surjective Ideal.Quotient.mk_surjective,
    Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, IsIdempotentElem,
    Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_span_singleton]
  intro h
  have : (X : k[X]) ^ 2 ∣ X ^ 1 := by simpa [pow_two] using h.dvd
  have := (pow_dvd_pow_iff X_ne_zero not_isUnit_X).1 this
  omega
