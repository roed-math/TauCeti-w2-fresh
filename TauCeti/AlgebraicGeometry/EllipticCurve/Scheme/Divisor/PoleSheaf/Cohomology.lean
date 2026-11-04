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
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Sections
import TauCeti.AlgebraicGeometry.Cohomology.SectionsQuotient.Linear

/-!
# Cohomology of the pole sheaves over a ring

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, and let `𝒪(n[0])` be the
pole sheaf on its projective model (`WeierstrassCurve.poleSheaf`). The projective model is covered
by the two affine charts `D₊(Y)` and `D₊(Z)`, whose overlap `D₊(YZ)` is affine
(`WeierstrassCurve.opensRange_chartι_one_sup_opensRange_chartι_two`), and it is smooth, hence flat,
over `R`. So the sections of `𝒪(n[0])` over the charts and their overlap are flat over `R`
(`WeierstrassCurve.flat_sectionsBase_poleSheaf`), and the cohomology-and-base-change theorems for
two-affine covers apply.

The fibre of the projective model at a prime `p` of `R` is the projective model of the reduction
of `W` to the residue field `κ(p)`, and `𝒪(n[0])` pulls back to `𝒪(n[0])` on it
(`WeierstrassCurve.nonempty_pullback_poleSheaf_iso`). Over a field, Riemann–Roch in genus one
gives `H¹(𝒪(n[0])) = 0` for `n > 0`. Since `H¹(projModel W, 𝒪(n[0]))` is a finite `R`-module
(`WeierstrassCurve.finite_cohomology_one`), it follows that for `n > 0`:

* `H¹(projModel W, 𝒪(n[0])) = 0`;
* `H⁰(projModel W, 𝒪(n[0]))` is a flat `R`-module whose formation commutes with every base
  change of `R`;
* its fibre at every prime `p` has dimension `n` over `κ(p)`.

## Main results

* `WeierstrassCurve.flat_sectionsBase_poleSheaf`: the sections of `𝒪(n[0])` over an affine open
  are flat over `R`.
* `WeierstrassCurve.subsingleton_cohomology_one_poleSheaf`: `H¹(𝒪(n[0])) = 0`.
* `WeierstrassCurve.flat_cohomology_zero_poleSheaf`: `H⁰(𝒪(n[0]))` is flat over `R`.
* `WeierstrassCurve.bijective_cohomologyBaseChange_zero_poleSheaf`: the formation of
  `H⁰(𝒪(n[0]))` commutes with every base change of `R`.
* `WeierstrassCurve.finrank_fiber_cohomology_zero_poleSheaf`: the fibre of
  `H⁰(𝒪(n[0]))` at every prime has dimension `n`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1.
* R. Hartshorne, *Algebraic Geometry*, Theorem III.12.11 (cohomology and base change).
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

/-- Over a field, `H¹(projModel W, 𝒪(n[0])) = 0` for `n > 0`: `𝒪(n[0])` has degree `n`, above
`2g - 2 = 0`. -/
private theorem subsingleton_cohomology_one_poleSheaf_field {K : Type u} [Field K]
    (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ} (hn : 0 < n) :
    Subsingleton (Cohomology (W.poleSheaf n).obj 1) :=
  InvertibleSheaf.subsingleton_cohomology_one_of_two_mul_genus_sub_two_lt_eulerDegree Fact.out
    (isFunctionField_functionField_projModel W)
    isIntegrallyClosedIn_functionField_of_geometricallyIntegral _
    (by rw [finrank_cohomology_one_trivial_projModel, eulerDegree_poleSheaf]; omega)

end Field

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- The sections of the pole sheaf `𝒪(n[0])` over an affine open of the projective model are a
flat `R`-module. -/
theorem flat_sectionsBase_poleSheaf (n : ℕ) {U : W.projModel.Opens} (hU : IsAffineOpen U) :
    Module.Flat R (((sectionsBasePresheafFunctor R).obj (W.poleSheaf n).obj).obj (op U)) :=
  FiniteLocallyFreeSheaf.flat_sectionsBase ((InvertibleSheaf.toFiniteLocallyFree _).obj
    (W.poleSheaf n)) R hU

variable {n : ℕ}

/-- **`H¹(projModel W, 𝒪(n[0])) = 0` for `n > 0`** over any ring. `H¹` is a finite `R`-module
(`WeierstrassCurve.finite_cohomology_one`), and on each fibre it vanishes by Riemann–Roch in genus
one, so no prime of `R` lies in the support of `H¹`
(`TauCeti.AlgebraicGeometry.subsingleton_cohomology_one_pullback_iff_notMem_support`). -/
theorem subsingleton_cohomology_one_poleSheaf (hn : 0 < n) :
    Subsingleton (Cohomology (W.poleSheaf n).obj 1) := by
  have : (W.poleSheaf n).obj.IsFiniteType :=
    inferInstanceAs ((InvertibleSheaf.toFiniteLocallyFree _).obj (W.poleSheaf n)).obj.IsFiniteType
  have := W.finite_cohomology_one (W.poleSheaf n).obj
  rw [← Module.support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
  intro p
  refine (subsingleton_cohomology_one_pullback_iff_notMem_support _
    (isAffineOpen_opensRange (W.chartι 1)) (isAffineOpen_opensRange (W.chartι 2))
    W.isAffineOpen_opensRange_chartι_one_inf_opensRange_chartι_two
    W.opensRange_chartι_one_sup_opensRange_chartι_two p
    (W.isPullback_projModelBaseChange_over (R' := p.asIdeal.ResidueField))).mp ?_
  obtain ⟨e⟩ := W.nonempty_pullback_poleSheaf_iso (algebraMap R p.asIdeal.ResidueField) n
  have :=
    subsingleton_cohomology_one_poleSheaf_field (W.map (algebraMap R p.asIdeal.ResidueField)) hn
  exact (cohomologyBaseLinearEquivOfIso p.asIdeal.ResidueField e 1).toEquiv.subsingleton

/-- **`H⁰(projModel W, 𝒪(n[0]))` is flat over `R` for `n > 0`**. -/
theorem flat_cohomology_zero_poleSheaf (hn : 0 < n) :
    Module.Flat R (Cohomology (W.poleSheaf n).obj 0) := by
  have := W.subsingleton_cohomology_one_poleSheaf hn
  have := W.flat_sectionsBase_poleSheaf n (isAffineOpen_opensRange (W.chartι 1))
  have := W.flat_sectionsBase_poleSheaf n (isAffineOpen_opensRange (W.chartι 2))
  have := W.flat_sectionsBase_poleSheaf n
    W.isAffineOpen_opensRange_chartι_one_inf_opensRange_chartι_two
  exact flat_cohomology_zero_of_subsingleton_cohomology_one _ _ _
    W.opensRange_chartι_one_sup_opensRange_chartι_two

/-- **The formation of `H⁰(projModel W, 𝒪(n[0]))` commutes with every base change** for `n > 0`:
for every pullback square presenting `Y` as `X ×_R R'`, the canonical map
`R' ⊗_R H⁰(X, 𝒪(n[0])) ⟶ H⁰(Y, g^* 𝒪(n[0]))` is bijective. -/
theorem bijective_cohomologyBaseChange_zero_poleSheaf (hn : 0 < n) {R' : Type u}
    [CommRing R'] [Algebra R R'] {Y : Scheme.{u}} [Y.Over (Spec (.of R'))] {g : Y ⟶ W.projModel}
    (H : IsPullback g (Y ↘ Spec (.of R')) (W.projModel ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :
    Function.Bijective (cohomologyBaseChange H (W.poleSheaf n).obj 0) := by
  have := W.subsingleton_cohomology_one_poleSheaf hn
  have := W.flat_sectionsBase_poleSheaf n
    W.isAffineOpen_opensRange_chartι_one_inf_opensRange_chartι_two
  exact bijective_cohomologyBaseChange_zero_of_subsingleton_cohomology_one H _
    (isAffineOpen_opensRange (W.chartι 1)) (isAffineOpen_opensRange (W.chartι 2))
    W.isAffineOpen_opensRange_chartι_one_inf_opensRange_chartι_two
    W.opensRange_chartι_one_sup_opensRange_chartι_two

/-- **The fibres of `H⁰(projModel W, 𝒪(n[0]))` have dimension `n`** for `n > 0`:
`dim_{κ(p)} κ(p) ⊗_R H⁰(𝒪(n[0])) = n` at every prime `p` of `R`. -/
theorem finrank_fiber_cohomology_zero_poleSheaf (hn : 0 < n) (p : PrimeSpectrum R) :
    finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (Cohomology (W.poleSheaf n).obj 0)) = n := by
  have := W.subsingleton_cohomology_one_poleSheaf hn
  have := W.flat_sectionsBase_poleSheaf n
    W.isAffineOpen_opensRange_chartι_one_inf_opensRange_chartι_two
  obtain ⟨e⟩ := W.nonempty_pullback_poleSheaf_iso (algebraMap R p.asIdeal.ResidueField) n
  rw [← finrank_cohomology_zero_pullback_eq_finrank_fiber p
    (W.isPullback_projModelBaseChange_over (R' := p.asIdeal.ResidueField)) _
    (isAffineOpen_opensRange (W.chartι 1)) (isAffineOpen_opensRange (W.chartι 2))
    W.isAffineOpen_opensRange_chartι_one_inf_opensRange_chartι_two
    W.opensRange_chartι_one_sup_opensRange_chartι_two,
    (cohomologyBaseLinearEquivOfIso p.asIdeal.ResidueField e 0).finrank_eq]
  exact (W.map (algebraMap R p.asIdeal.ResidueField)).finrank_cohomology_zero_poleSheaf hn

end WeierstrassCurve
