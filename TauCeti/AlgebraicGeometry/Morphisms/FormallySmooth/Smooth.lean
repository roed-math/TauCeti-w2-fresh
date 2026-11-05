/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftSheaf.Cohomology
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftSheaf.Quasicoherent

/-!
# Smooth morphisms are formally smooth

A smooth morphism `f : X ⟶ S` is formally smooth: along a first-order thickening `i : T ⟶ T'` of
an affine scheme `T'`, every `a : T ⟶ X` over `S` lifts to `T'`. The lifts exist locally on `T'`
and form a torsor under the sheaf of derivations `liftDerivationModule f i a`
(`liftTorsor`); this sheaf is quasi-coherent (`isQuasicoherent_liftDerivationModule`), so by
Serre's vanishing theorem the class of the torsor vanishes over an affine `T'`. Together with
`AlgebraicGeometry.Smooth.of_formallySmooth`, this is the infinitesimal lifting criterion: a
morphism locally of finite presentation is smooth if and only if it is formally smooth (Stacks,
Lemma 37.11.7 (02H6)).

## Main results

* `TauCeti.AlgebraicGeometry.liftObstruction_eq_one_of_isAffine`: for `f` smooth and `T'` affine,
  the obstruction class of the torsor of lifts vanishes.
* `TauCeti.AlgebraicGeometry.FormallySmooth.of_smooth`: a smooth morphism is formally smooth.
* `TauCeti.AlgebraicGeometry.smooth_iff_formallySmooth`: a morphism locally of finite
  presentation is smooth if and only if it is formally smooth.

## References

* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ).
* [Stacks Project, Lemma 37.11.7](https://stacks.math.columbia.edu/tag/02H6).
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {X S T T' : Scheme.{u}} {f : X ⟶ S} {i : T ⟶ T'} {a : T ⟶ X} {h : T' ⟶ S}
  [IsFirstOrderThickening i] [Smooth f]

/-- For `f` smooth and `T'` affine, the obstruction class of the torsor of lifts of `a` along the
first-order thickening `i` vanishes: the sheaf of derivations is quasi-coherent, so it has no
first cohomology on the affine scheme `T'`. -/
theorem liftObstruction_eq_one_of_isAffine (w : a ≫ f = i ≫ h) [IsAffine T'] :
    liftObstruction w = 1 :=
  have := isQuasicoherent_liftDerivationModule w
  (liftObstruction_eq_one_iff w).2 (exists_lift_of_isQuasicoherent w)

/-- A smooth morphism is formally smooth (Stacks, Lemma 37.11.7 (02H6)): along a first-order
thickening of an affine scheme, the torsor of lifts is trivial. -/
instance (priority := 100) FormallySmooth.of_smooth (f : X ⟶ S) [Smooth f] : FormallySmooth f where
  exists_lift _ _ _ _ w :=
    have := isQuasicoherent_liftDerivationModule w
    exists_lift_of_isQuasicoherent w

/-- **The infinitesimal lifting criterion.** A morphism locally of finite presentation is smooth
if and only if it is formally smooth (Stacks, Lemma 37.11.7 (02H6)). -/
theorem smooth_iff_formallySmooth (f : X ⟶ S) [LocallyOfFinitePresentation f] :
    Smooth f ↔ FormallySmooth f :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ Smooth.of_formallySmooth f⟩

end TauCeti.AlgebraicGeometry
