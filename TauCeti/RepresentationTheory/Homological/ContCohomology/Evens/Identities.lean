/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Corestriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Inflation
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Polarization
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Restriction

/-!
# Characterizing identities of the index-two Evens graph class

For an index-two open subgroup `U` of a topological group `G`, the choice-free class
`TauCeti.ContCohomology.explicitGraphClass` of the two-point graph cocycle lives in the explicit
inhomogeneous model `H²(G, 𝔽₂)`. This file upgrades the landed representative-level computations
to that class, proving the four identities that characterize the degree-one, index-two Evens
norm:

* restriction is the cup product with the conjugate class;
* polarization is corestriction of the corresponding mixed cup product;
* degree-one corestriction is represented by the Shapiro sum `b₁ + bₛ`;
* the graph class commutes with inflation from a quotient.

All four are statements in the explicit model that carries the landed low-degree restriction, cup,
corestriction and inflation operations, not about canonical `continuousCohomology` classes; the
bridge to the canonical class is `TauCeti.ContCohomology.graphClass_eq_explicitGraphClass`. They
therefore do not presuppose the future all-degree Evens norm, and the canonical `evensNorm_*`
names are left for the statements about that norm.

## Main results

* `TauCeti.ContCohomology.explicitRes2_explicitGraphClass`
* `TauCeti.ContCohomology.explicitGraphClass_polarization`
* `TauCeti.ContCohomology.explicitCor1_evensHomCocycleAmbient` (from the imported corestriction
  module)
* `TauCeti.ContCohomology.explicitInfl2_explicitGraphClass`

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313, Lemma 2.4.
-/

public section

namespace TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- `G` acts continuously on the trivial coefficients `𝔽₂`, which are smooth discrete. The name is
given explicitly because the imported `Evens` files carry the same local instance. -/
local instance continuousSMul_trivialF2_identities : ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

/-- **Restriction identity for the index-two Evens graph class.** Restriction of the choice-free
graph class is the cup product of `α` with its choice-free conjugate. Both sides lie in explicit
`H²(U, 𝔽₂)`; unlike `explicitRes2_evensGraphCocycle`, neither mentions a representative. -/
theorem explicitRes2_explicitGraphClass (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    explicitRes2 G (trivialF2 G).V U.toSubgroup (explicitGraphClass U hU α hα) =
      explicitCup11 U.toSubgroup (trivialF2 G).V (trivialF2 G).V (trivialF2 G).V
        (trivialF2Pairing G) continuous_of_discreteTopology
        (fun u m n => trivialF2Pairing_smul_smul G (u : G) m n)
        (evensHomCocycleAmbient U.toSubgroup α hα : H1 U.toSubgroup (trivialF2 G).V)
        (evensConj1 G (trivialF2 G).V U.toSubgroup hU U.isOpen'
          (evensHomCocycleAmbient U.toSubgroup α hα : H1 U.toSubgroup (trivialF2 G).V)) := by
  let _ : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  obtain ⟨s, hs, -⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp hU
  rw [explicitGraphClass_eq_evensGraphCocycle U hU s hs α hα,
    explicitRes2_evensGraphCocycle U hU hs α hα]

/-- **Polarization identity for the index-two Evens graph class.** The failure of additivity of the
choice-free graph class is the corestriction of the cup product of the first class with the
conjugate of the second. -/
theorem explicitGraphClass_polarization (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (α β : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α)
    (hβ : Continuous β) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    explicitGraphClass U hU (α * β) (hα.mul hβ) - explicitGraphClass U hU α hα -
        explicitGraphClass U hU β hβ =
      explicitCor2 G (trivialF2 G).V U.toSubgroup U.isOpen'
        (explicitCup11 U.toSubgroup (trivialF2 G).V (trivialF2 G).V (trivialF2 G).V
          (trivialF2Pairing G) continuous_of_discreteTopology
          (fun u m n => trivialF2Pairing_smul_smul G (u : G) m n)
          (evensHomCocycleAmbient U.toSubgroup α hα : H1 U.toSubgroup (trivialF2 G).V)
          (evensConj1 G (trivialF2 G).V U.toSubgroup hU U.isOpen'
            (evensHomCocycleAmbient U.toSubgroup β hβ :
              H1 U.toSubgroup (trivialF2 G).V))) := by
  let _ : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  obtain ⟨s, hs, -⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp hU
  rw [explicitGraphClass_eq_evensGraphCocycle U hU s hs (α * β) (hα.mul hβ),
    explicitGraphClass_eq_evensGraphCocycle U hU s hs α hα,
    explicitGraphClass_eq_evensGraphCocycle U hU s hs β hβ,
    evensGraphCocycle_polarization U hU hs α β hα hβ]

/-- **Inflation identity for the index-two Evens graph class.** For a normal subgroup `N ≤ U`,
inflation of the quotient graph-cocycle class on `U / N` is the choice-free graph class of the
pulled-back character on `U`. The left-hand side is the fixed-point-valued representative required
by explicit inflation, for an arbitrary element outside `U`; the right-hand side involves no
choice. -/
theorem explicitInfl2_explicitGraphClass {N : Subgroup G} [N.Normal] (U : OpenSubgroup G)
    (hNU : N ≤ U) (hU : U.toSubgroup.index = 2) (s : G) (hs : s ∉ U)
    (α : (quotientOpenSubgroup N U).toSubgroup →* Multiplicative (ZMod 2))
    (hα : Continuous α) :
    explicitInfl2 G (trivialF2 G).V N
        (evensGraphCocycleFixedPoints U hNU hU s hs α hα :
          H2 (G ⧸ N) (FixedPoints.addSubgroup N (trivialF2 G).V)) =
      explicitGraphClass U hU (evensInflatedHom U α) (continuous_evensInflatedHom U hα) := by
  rw [explicitInfl2_evensGraphCocycle U hNU hU s hs α hα]
  exact (explicitGraphClass_eq_evensGraphCocycle U hU s hs (evensInflatedHom U α)
    (continuous_evensInflatedHom U hα)).symm

end TauCeti.ContCohomology
