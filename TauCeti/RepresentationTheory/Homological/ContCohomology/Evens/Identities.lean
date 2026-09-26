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

For an index-two open subgroup `U` of a topological group `G`, the two-point graph cocycle gives a
class in explicit continuous `H²(G, 𝔽₂)`. Although its cochain formula uses an element outside
`U`, its class does not. This file packages that choice-free explicit class and proves the four
identities that characterize the degree-one, index-two Evens norm:

* restriction is the cup product with the conjugate class;
* polarization is corestriction of the corresponding mixed cup product;
* degree-one corestriction is represented by the Shapiro sum `b₁ + bₛ`;
* the graph class commutes with inflation from a quotient.

`graphClass_eq_explicitGraphClass` identifies the explicit class with the already constructed
class in Mathlib's canonical `continuousCohomology`. Thus the class-level formulas use only the
landed low-degree restriction, cup, corestriction and inflation operations; they do not
presuppose the future all-degree Evens norm.

## Main definitions

* `TauCeti.ContCohomology.explicitGraphClass`: the choice-free explicit graph-cocycle class.

## Main results

* `TauCeti.ContCohomology.graphClass_eq_explicitGraphClass`
* `TauCeti.ContCohomology.evensNorm_res`
* `TauCeti.ContCohomology.evensNorm_polarization`
* `TauCeti.ContCohomology.evensNorm_cor_shapiro` (from the imported corestriction formula)
* `TauCeti.ContCohomology.evensNorm_identity_infl`

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313, Lemma 2.4.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

section Choice

variable {G : Type u} [Group G] [TopologicalSpace G]

private noncomputable def explicitGraphElement (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) : G :=
  Classical.choose (Subgroup.index_eq_two_iff_exists_notMem_and.mp hU)

private theorem explicitGraphElement_not_mem (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) : explicitGraphElement U hU ∉ U :=
  (Classical.choose_spec (Subgroup.index_eq_two_iff_exists_notMem_and.mp hU)).1

end Choice

section Class

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

local instance continuousSMul_trivialF2_identities : ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

/-- The choice-free explicit `H²(G, 𝔽₂)` class of the two-point graph cocycle.

An element outside `U` is chosen only in the body. The theorem
`explicitGraphClass_eq_evensGraphCocycle` identifies the result with the graph cocycle formed from
every possible such element, so no choice occurs in the public interface. -/
noncomputable def explicitGraphClass (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    H2 G (trivialF2 G).V :=
  (evensGraphCocycle U (explicitGraphElement U hU) α hU
    (explicitGraphElement_not_mem U hU) hα : H2 G (trivialF2 G).V)

/-- The choice-free explicit graph class is represented by the graph cocycle formed using every
element outside `U`. -/
theorem explicitGraphClass_eq_evensGraphCocycle (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) (s : G) (hs : s ∉ U)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    explicitGraphClass U hU α hα =
      (evensGraphCocycle U s α hU hs hα : H2 G (trivialF2 G).V) := by
  unfold explicitGraphClass
  rw [H2pi_eq_iff]
  refine mem_B2_iff'.2 ⟨fun g => (trivialF2Equiv G).symm
    (evensExtend U.toSubgroup α (s⁻¹ * explicitGraphElement U hU) *
      evensExtend U.toSubgroup α g), ?_, ?_⟩
  · exact (continuous_of_discreteTopology : Continuous (trivialF2Equiv G).symm).comp
      ((continuous_of_discreteTopology : Continuous (fun x : ZMod 2 =>
        evensExtend U.toSubgroup α (s⁻¹ * explicitGraphElement U hU) * x)).comp
          (continuous_evensExtend U.toSubgroup α U.isOpen' hα))
  · intro g h
    apply (trivialF2Equiv G).injective
    simp only [TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply,
      map_sub, map_add, AddEquiv.apply_symm_apply, coe_evensGraphCocycle, Pi.sub_apply]
    exact (evensGraphCochain_sub_evensGraphCochain hU hs
      (explicitGraphElement_not_mem U hU) g h).symm

/-- The canonical graph class is the image of the choice-free explicit graph class under the
degree-two comparison. -/
theorem graphClass_eq_explicitGraphClass [LocallyCompactSpace G] (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) (α : U.toSubgroup →* Multiplicative (ZMod 2))
    (hα : Continuous α) :
    graphClass U hU α hα =
      (eqToHom (congrArg (continuousCohomology 2)
        (ofDiscreteModule_trivialF2 G))).hom
        (explicitH2AddEquivContinuousCohomology G (trivialF2 G).V
          (explicitGraphClass U hU α hα)) := by
  rw [graphClass_eq_cochainClass U hU (explicitGraphElement U hU)
    (explicitGraphElement_not_mem U hU) α hα, evensGraphCochainClass_def,
    explicitGraphClass_eq_evensGraphCocycle U hU (explicitGraphElement U hU)
      (explicitGraphElement_not_mem U hU) α hα]

/-- **Restriction identity for the index-two Evens graph class.** Restriction of
`Nᴱᶠ(α)` is the cup product of `α` with its choice-free conjugate. This is an equality of
explicit cohomology classes and is therefore independent of the representative used to define
the graph cochain. -/
theorem evensNorm_res (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
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
  rw [explicitGraphClass_eq_evensGraphCocycle U hU (explicitGraphElement U hU)
    (explicitGraphElement_not_mem U hU) α hα,
    explicitRes2_evensGraphCocycle U hU (explicitGraphElement_not_mem U hU) α hα]

/-- **Polarization identity for the index-two Evens graph class.** The failure of additivity is
the corestriction of the cup product of the first class with the conjugate of the second. -/
theorem evensNorm_polarization (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
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
  rw [explicitGraphClass_eq_evensGraphCocycle U hU (explicitGraphElement U hU)
      (explicitGraphElement_not_mem U hU) (α * β) (hα.mul hβ),
    explicitGraphClass_eq_evensGraphCocycle U hU (explicitGraphElement U hU)
      (explicitGraphElement_not_mem U hU) α hα,
    explicitGraphClass_eq_evensGraphCocycle U hU (explicitGraphElement U hU)
      (explicitGraphElement_not_mem U hU) β hβ,
    evensGraphCocycle_polarization U hU (explicitGraphElement_not_mem U hU) α β hα hβ]

/-- A fixed-point-valued representative of the quotient graph class, using the same internally
chosen element outside `U` as the ambient explicit graph class. This is the input required by
explicit inflation; `evensNorm_identity_infl` shows that its inflation is choice-free. -/
noncomputable def explicitGraphClassFixedPoints {N : Subgroup G} [N.Normal]
    (U : OpenSubgroup G) (hNU : N ≤ U) (hU : U.toSubgroup.index = 2)
    (α : (quotientOpenSubgroup N U).toSubgroup →* Multiplicative (ZMod 2))
    (hα : Continuous α) : H2 (G ⧸ N) (FixedPoints.addSubgroup N (trivialF2 G).V) :=
  (evensGraphCocycleFixedPoints U hNU hU (explicitGraphElement U hU)
    (explicitGraphElement_not_mem U hU) α hα :
    H2 (G ⧸ N) (FixedPoints.addSubgroup N (trivialF2 G).V))

/-- **Inflation identity for the index-two Evens graph class.** For a normal subgroup `N ≤ U`,
inflation of the graph class on `U / N` is the graph class of the pulled-back character on `U`.
The quotient class is first transported to the fixed-point coefficients required by explicit
inflation. -/
theorem evensNorm_identity_infl {N : Subgroup G} [N.Normal] (U : OpenSubgroup G) (hNU : N ≤ U)
    (hU : U.toSubgroup.index = 2)
    (α : (quotientOpenSubgroup N U).toSubgroup →* Multiplicative (ZMod 2))
    (hα : Continuous α) :
    explicitInfl2 G (trivialF2 G).V N
        (explicitGraphClassFixedPoints U hNU hU α hα) =
      explicitGraphClass U hU (evensInflatedHom U α) (continuous_evensInflatedHom U hα) := by
  rw [explicitGraphClassFixedPoints,
    explicitInfl2_evensGraphCocycle U hNU hU (explicitGraphElement U hU)
      (explicitGraphElement_not_mem U hU) α hα]
  exact (explicitGraphClass_eq_evensGraphCocycle U hU (explicitGraphElement U hU)
    (explicitGraphElement_not_mem U hU) (evensInflatedHom U α)
    (continuous_evensInflatedHom U hα)).symm

end Class

end TauCeti.ContCohomology
