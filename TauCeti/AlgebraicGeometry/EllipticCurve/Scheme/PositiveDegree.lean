/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.CohomologyAndBaseChange
public import TauCeti.AlgebraicGeometry.Cohomology.Semicontinuity
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.PoleSheaf.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FiniteCohomology
public import TauCeti.AlgebraicGeometry.LineBundle.HighDegree
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Sections
import TauCeti.AlgebraicGeometry.Cohomology.SectionsQuotient.Linear

/-!
# Line bundles of positive fibre degree on a projective Weierstrass model

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, and let `M` be a line bundle
on its projective model whose restriction to the fibre over every prime `p` of `R` has positive
degree. The fibre over `p` is the projective model of the reduction of `W` to the residue field
`κ(p)`, a smooth proper curve of genus one, so by Riemann–Roch the restriction of `M` there has
no first cohomology, and its sections form a `κ(p)`-vector space of dimension its degree.

The projective model is covered by the two affine charts `D₊(Y)` and `D₊(Z)`, whose overlap
`D₊(YZ)` is affine, and it is smooth, hence flat, over `R`. So the sections of `M` over the charts
and their overlap are flat over `R` (`WeierstrassCurve.flat_sectionsBase`), and the
cohomology-and-base-change theorems for two-affine covers apply. Since `H¹(projModel W, M)` is a
finite `R`-module (`WeierstrassCurve.finite_cohomology_one`), it follows that:

* `H¹(projModel W, M) = 0`;
* `H⁰(projModel W, M)` is a flat `R`-module whose formation commutes with every base change of
  `R`;
* its fibre at every prime `p` has dimension the degree of `M` on the fibre over `p`.

This is the positive-degree theorem on a Weierstrass model. The pole sheaves `𝒪(n[0])`, `n > 0`,
are the case of fibre degree `n`.

## Main results

* `WeierstrassCurve.subsingleton_cohomology_one_of_eulerDegree_pos` and
  `WeierstrassCurve.finrank_cohomology_zero_of_eulerDegree_pos`: over a field, a line bundle of
  positive degree `d` has `H¹ = 0` and `dim H⁰ = d`.
* `WeierstrassCurve.flat_sectionsBase`: the sections of a line bundle over an affine open are flat
  over `R`.
* `WeierstrassCurve.subsingleton_cohomology_one_of_forall_eulerDegree_pos`: `H¹(M) = 0`.
* `WeierstrassCurve.flat_cohomology_zero_of_forall_eulerDegree_pos`: `H⁰(M)` is flat over `R`.
* `WeierstrassCurve.bijective_cohomologyBaseChange_zero_of_forall_eulerDegree_pos`: the formation
  of `H⁰(M)` commutes with every base change of `R`.
* `WeierstrassCurve.finrank_fiber_cohomology_zero_of_forall_eulerDegree_pos`: the fibre of
  `H⁰(M)` at a prime `p` has dimension the degree of `M` on the fibre over `p`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1.
* R. Hartshorne, *Algebraic Geometry*, Theorem III.12.11 (cohomology and base change).
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.3.1: the
  Riemann–Roch spaces `L(n O)` have dimension `n` for `n > 0`.
-/

public section

open CategoryTheory Opposite AlgebraicGeometry TauCeti TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules
open Module (finrank)

universe u

namespace WeierstrassCurve

section Field

-- The function field of the projective model carries the `K`-algebra structure defined by its
-- structure morphism, which is the one used by the genus theory of smooth curves.
attribute [local instance high] Scheme.functionFieldBaseAlgebra

variable {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- Over a field, a line bundle of positive degree on the projective model has no first
cohomology: its degree is above `2g - 2 = 0`. -/
theorem subsingleton_cohomology_one_of_eulerDegree_pos {M : InvertibleSheaf W.projModel}
    (hM : 0 < M.eulerDegree K) : Subsingleton (Cohomology M.obj 1) :=
  InvertibleSheaf.subsingleton_cohomology_one_of_two_mul_genus_sub_two_lt_eulerDegree Fact.out
    (isFunctionField_functionField_projModel W)
    isIntegrallyClosedIn_functionField_of_geometricallyIntegral _
    (by rw [finrank_cohomology_one_trivial_projModel]; omega)

/-- **Riemann–Roch in genus one**: over a field, a line bundle of positive degree `d` on the
projective model has `dim_K H⁰ = d`. -/
theorem finrank_cohomology_zero_of_eulerDegree_pos {M : InvertibleSheaf W.projModel}
    (hM : 0 < M.eulerDegree K) : (finrank K (Cohomology M.obj 0) : ℤ) = M.eulerDegree K := by
  have h := InvertibleSheaf.finrank_cohomology_zero_eq_eulerDegree_add_one_sub_genus Fact.out
    (isFunctionField_functionField_projModel W)
    isIntegrallyClosedIn_functionField_of_geometricallyIntegral M
    (by rw [finrank_cohomology_one_trivial_projModel]; omega)
  rw [finrank_cohomology_one_trivial_projModel] at h
  omega

end Field

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- The sections of a line bundle over an affine open of the projective model are a flat
`R`-module. -/
theorem flat_sectionsBase (M : InvertibleSheaf W.projModel) {U : W.projModel.Opens}
    (hU : IsAffineOpen U) :
    Module.Flat R (((sectionsBasePresheafFunctor R).obj M.obj).obj (op U)) :=
  FiniteLocallyFreeSheaf.flat_sectionsBase ((InvertibleSheaf.toFiniteLocallyFree _).obj M) R hU

variable {W} {M : InvertibleSheaf W.projModel}
  (hM : ∀ p : PrimeSpectrum R, 0 < ((InvertibleSheaf.pullback
    (W.projModelBaseChange (algebraMap R p.asIdeal.ResidueField))).obj M).eulerDegree
      p.asIdeal.ResidueField)
include hM

/-- **`H¹(projModel W, M) = 0` for a line bundle `M` of positive fibre degree**, over any ring.
`H¹` is a finite `R`-module (`WeierstrassCurve.finite_cohomology_one`), and on each fibre it
vanishes by Riemann–Roch in genus one, so no prime of `R` lies in the support of `H¹`
(`TauCeti.AlgebraicGeometry.subsingleton_cohomology_one_pullback_iff_notMem_support`). -/
theorem subsingleton_cohomology_one_of_forall_eulerDegree_pos :
    Subsingleton (Cohomology M.obj 1) := by
  have : M.obj.IsFiniteType :=
    inferInstanceAs ((InvertibleSheaf.toFiniteLocallyFree _).obj M).obj.IsFiniteType
  have := W.finite_cohomology_one M.obj
  rw [← Module.support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
  intro p
  refine (subsingleton_cohomology_one_pullback_iff_notMem_support _
    (isAffineOpen_opensRange (W.chartι 1)) (isAffineOpen_opensRange (W.chartι 2))
    W.isAffineOpen_opensRange_chartι_one_inf_opensRange_chartι_two
    W.opensRange_chartι_one_sup_opensRange_chartι_two p
    (W.isPullback_projModelBaseChange_over (R' := p.asIdeal.ResidueField))).mp ?_
  exact (W.map (algebraMap R p.asIdeal.ResidueField)).subsingleton_cohomology_one_of_eulerDegree_pos
    (hM p)

/-- **`H⁰(projModel W, M)` is flat over `R` for a line bundle `M` of positive fibre degree**. -/
theorem flat_cohomology_zero_of_forall_eulerDegree_pos :
    Module.Flat R (Cohomology M.obj 0) := by
  have := subsingleton_cohomology_one_of_forall_eulerDegree_pos hM
  have := W.flat_sectionsBase M (isAffineOpen_opensRange (W.chartι 1))
  have := W.flat_sectionsBase M (isAffineOpen_opensRange (W.chartι 2))
  have := W.flat_sectionsBase M W.isAffineOpen_opensRange_chartι_one_inf_opensRange_chartι_two
  exact flat_cohomology_zero_of_subsingleton_cohomology_one _ _ _
    W.opensRange_chartι_one_sup_opensRange_chartι_two

/-- **The formation of `H⁰(projModel W, M)` commutes with every base change** for a line bundle
`M` of positive fibre degree: for every pullback square presenting `Y` as `X ×_R R'`, the
canonical map `R' ⊗_R H⁰(X, M) ⟶ H⁰(Y, g^* M)` is bijective. -/
theorem bijective_cohomologyBaseChange_zero_of_forall_eulerDegree_pos {R' : Type u}
    [CommRing R'] [Algebra R R'] {Y : Scheme.{u}} [Y.Over (Spec (.of R'))] {g : Y ⟶ W.projModel}
    (H : IsPullback g (Y ↘ Spec (.of R')) (W.projModel ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :
    Function.Bijective (cohomologyBaseChange H M.obj 0) := by
  have := subsingleton_cohomology_one_of_forall_eulerDegree_pos hM
  have := W.flat_sectionsBase M W.isAffineOpen_opensRange_chartι_one_inf_opensRange_chartι_two
  exact bijective_cohomologyBaseChange_zero_of_subsingleton_cohomology_one H _
    (isAffineOpen_opensRange (W.chartι 1)) (isAffineOpen_opensRange (W.chartι 2))
    W.isAffineOpen_opensRange_chartι_one_inf_opensRange_chartι_two
    W.opensRange_chartι_one_sup_opensRange_chartι_two

/-- **The fibres of `H⁰(projModel W, M)` have dimension the fibre degree of `M`** for a line bundle
`M` of positive fibre degree: `dim_{κ(p)} κ(p) ⊗_R H⁰(M)` is the degree of the restriction of `M`
to the fibre over `p`, at every prime `p` of `R`. -/
theorem finrank_fiber_cohomology_zero_of_forall_eulerDegree_pos (p : PrimeSpectrum R) :
    (finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (Cohomology M.obj 0)) : ℤ) =
      ((InvertibleSheaf.pullback
        (W.projModelBaseChange (algebraMap R p.asIdeal.ResidueField))).obj M).eulerDegree
          p.asIdeal.ResidueField := by
  have := subsingleton_cohomology_one_of_forall_eulerDegree_pos hM
  have := W.flat_sectionsBase M W.isAffineOpen_opensRange_chartι_one_inf_opensRange_chartι_two
  rw [← finrank_cohomology_zero_pullback_eq_finrank_fiber p
    (W.isPullback_projModelBaseChange_over (R' := p.asIdeal.ResidueField)) _
    (isAffineOpen_opensRange (W.chartι 1)) (isAffineOpen_opensRange (W.chartι 2))
    W.isAffineOpen_opensRange_chartι_one_inf_opensRange_chartι_two
    W.opensRange_chartι_one_sup_opensRange_chartι_two, ← InvertibleSheaf.pullback_obj_obj]
  exact (W.map (algebraMap R p.asIdeal.ResidueField)).finrank_cohomology_zero_of_eulerDegree_pos
    (hM p)

end WeierstrassCurve
