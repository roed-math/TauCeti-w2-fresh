/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Lookahead.EulerCharacteristicMixed.Stubs
public import TauCeti.RepresentationTheory.Invariants

/-!
# Invariant dimensions under equivariant Kummer theory

The equivariant Kummer equivalence identifies the conjugation representation on first cohomology
with the tensor product of the dual roots-of-unity representation and the power classes. This file
records the resulting equality of invariant dimensions in the form used by the cyclic
prime-to-characteristic Euler-characteristic calculation.
-/

public noncomputable section

namespace TauCeti

universe u v

/-- **Equivariant Kummer preserves invariant dimension.** -/
theorem finrank_invariants_kummerH1FiniteRepresentation_eq
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] [Normal K L]
    (sigma : L →ₐ[K] SeparableClosure K) {ell : ℕ} [Fact ell.Prime]
    (hn : IsUnit (ell : K))
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K ell, g • xi = xi) :
    Module.finrank (ZMod ell) (Representation.invariants (k := ZMod ell)
        (G := Gal(L/K)) (kummerH1FiniteRepresentation sigma ell)) =
      Module.finrank (ZMod ell) (Representation.invariants (k := ZMod ell)
        (G := Gal(L/K))
        (V := TensorProduct (ZMod ell) (Module.Dual (ZMod ell) (KummerCoeff K ell))
          (Additive (powerClassQuotient Lˣ ell)))
        ((kummerCoeffFiniteRepresentation sigma ell hN).dual.tprod
          (powerClassRepresentation (K := K) (L := L) ell))) :=
  (kummerH1FiniteRepresentationEquiv sigma ell hn hN).invariantsLinearEquiv.finrank_eq

end TauCeti
