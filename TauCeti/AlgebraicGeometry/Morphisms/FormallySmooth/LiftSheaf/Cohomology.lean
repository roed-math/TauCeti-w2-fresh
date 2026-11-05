/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Affine
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftSheaf.Module
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftSheaf.Torsor
public import TauCeti.Lookahead.IsThickening.Stubs

/-!
# Lifts along a first-order thickening and the cohomology of the sheaf of derivations

For `f : X ⟶ S` smooth, `i : T ⟶ T'` a first-order thickening, and `a : T ⟶ X`, `h : T' ⟶ S` with
`a ≫ f = i ≫ h`, the obstruction to lifting `a` along `i` over `S` is the class `liftObstruction w`
of the torsor of lifts. Through `CategoryTheory.Sheaf.NonabelianH1.equivSheafH` it lives in the
first cohomology of the sheaf of derivations `liftDerivationSheaf f i a`, so `a` lifts as soon as
that cohomology group vanishes (Stacks, Lemma 37.9.5 (04FJ) and the proof of Lemma 37.11.7
(02H6)). By Serre's vanishing theorem this is the case when `T'` is affine and the sheaf of
derivations, as the sheaf of `𝒪_{T'}`-modules `liftDerivationModule f i a`, is quasi-coherent.

## Main results

* `TauCeti.AlgebraicGeometry.liftObstruction_eq_one_of_subsingleton`: the obstruction class
  vanishes when `H¹(T', liftDerivationSheaf f i a)` does.
* `TauCeti.AlgebraicGeometry.exists_lift_of_subsingleton`: then `a` lifts along `i` over `S`.
* `TauCeti.AlgebraicGeometry.exists_lift_of_isQuasicoherent`: `a` lifts along `i` over `S` when
  `T'` is affine and `liftDerivationModule f i a` is quasi-coherent.

## References

* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ).
* [Stacks Project, Lemma 37.11.7](https://stacks.math.columbia.edu/tag/02H6).
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

variable {X S T T' : Scheme.{u}} {f : X ⟶ S} {i : T ⟶ T'} {a : T ⟶ X} {h : T' ⟶ S}
  [IsFirstOrderThickening i] [Smooth f]

/-- The obstruction to lifting `a` along `i` over `S` vanishes when the sheaf of derivations
`liftDerivationSheaf f i a` has no first cohomology. -/
theorem liftObstruction_eq_one_of_subsingleton (w : a ≫ f = i ≫ h)
    [Subsingleton ((liftDerivationSheaf f i a).H 1)] : liftObstruction w = 1 :=
  (Sheaf.NonabelianH1.equivSheafH (liftDerivationSheaf f i a)).injective (Subsingleton.elim _ _)

/-- If the sheaf of derivations `liftDerivationSheaf f i a` has no first cohomology, then `a` lifts
along the first-order thickening `i` over the smooth morphism `f`. -/
theorem exists_lift_of_subsingleton (w : a ≫ f = i ≫ h)
    [Subsingleton ((liftDerivationSheaf f i a).H 1)] :
    ∃ l : T' ⟶ X, i ≫ l = a ∧ l ≫ f = h :=
  (liftObstruction_eq_one_iff w).1 (liftObstruction_eq_one_of_subsingleton w)

/-- If `T'` is affine and the sheaf of derivations, as the sheaf of `𝒪_{T'}`-modules
`liftDerivationModule f i a`, is quasi-coherent, then `a` lifts along the first-order thickening `i`
over the smooth morphism `f`: by Serre's vanishing theorem the sheaf of derivations has no higher
cohomology. -/
theorem exists_lift_of_isQuasicoherent (w : a ≫ f = i ≫ h) [IsAffine T']
    [(liftDerivationModule f i a).IsQuasicoherent] : ∃ l : T' ⟶ X, i ≫ l = a ∧ l ≫ f = h := by
  have := Scheme.Modules.subsingleton_cohomology_succ_of_isAffine (liftDerivationModule f i a) 0
  rw [Scheme.Modules.Cohomology, liftDerivationModule_toSheaf] at this
  exact exists_lift_of_subsingleton w

end TauCeti.AlgebraicGeometry
