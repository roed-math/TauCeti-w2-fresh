<!--tauceti-lookahead:v1 {"area":"ClassFieldTheory","slug":"euler-characteristic-mixed","main":"639cb3ebbfe504f23010bf461ea4bdc254c4f41c","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: reduce the local Euler characteristic by modular Artin induction"},{"n":2,"after":[],"title":"feat: compare induced local Euler characteristics by Shapiro"},{"n":3,"after":[],"title":"feat: compute cyclic prime-to-characteristic Euler characteristics"},{"n":4,"after":[1,2,3],"title":"feat: prove the mixed-characteristic Euler characteristic formula"}]}-->

# Mixed-characteristic Euler characteristic lookahead

This branch develops `euler-characteristic-mixed` on main commit
`639cb3ebbfe504f23010bf461ea4bdc254c4f41c`. It proves the modular-Artin reduction, including an
objectwise interface for the forthcoming Shapiro calculation; proves that induction preserves
invariant dimension, both for finite-dimensional representations and on the group-algebra
Grothendieck group; and proves the final numerical conversion from `χ_F(A) = φ_F(A)` to the
cardinality and `𝔽_p`-finrank formulae. These are coherent parts of the target, but the branch does
not claim either exported target theorem.

## Supplier stubs

There are no supplier stubs on this revision of the branch. The only stub consumed by the prior
revision was for `modular-artin-exists-nsmul-mem-ind-cyclic-coprime`; PR #13595 has since landed on
`main`, and this branch now imports its real declarations
`TauCeti.modularArtin_natCard_nsmul_mem_indCyclicCoprime` and
`TauCeti.modularArtin_exists_nsmul_mem_indCyclicCoprime` from
`TauCeti.RepresentationTheory.Induction.Artin.Spanning`.

The two other suppliers are not stubbed because the proved portion does not consume them. Open PR
#13295 supplies fixed-field and continuous-cohomology plumbing but does not yet state the final
Euler-characteristic Shapiro comparison pinned by `euler-characteristic-shapiro`. Open PR #13607
packages finite-layer Kummer representations but does not yet state the final equivariant Kummer
equivalence pinned by `kummer-equiv-mixed-equivariant`. Guessing either final declaration would not
faithfully restate the supplier's current PR form.

## Pull-request split plan

1. **feat: reduce the local Euler characteristic by modular Artin induction.** Files:
   `TauCeti/RepresentationTheory/GrothendieckGroup/GroupAlgebra/Induction.lean` and
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/ModularInduction.lean`.
   Adds `comp_indK0_eq_of_eq_on_indFDRep`,
   `eq_of_comp_indK0_eq_of_cyclic_coprime`,
   `localEulerCharacteristicK0_eq_localCardNormK0_of_indCyclicCoprime`,
   `forall_localEulerCharacteristic_eq_localCardNorm_of_indCyclicCoprime`, and
   `forall_localEulerCharacteristic_eq_localCardNorm_of_indFDRep`. Needs no earlier split.

2. **feat: compare induced local Euler characteristics by Shapiro.** Files:
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/Shapiro.lean` and a focused
   comparison module beside it if the landed supplier API makes that separation useful. Adds the
   equalities of `localEulerCharacteristic` and `localCardNorm` between an inflated induced module
   over `F` and the original module over `shapiroField F V C`. Needs no earlier target split, but
   is opened only after `euler-characteristic-shapiro` lands.

3. **feat: compute cyclic prime-to-characteristic Euler characteristics.** Files: a focused
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/CyclicCoprime.lean` module,
   `TauCeti/RepresentationTheory/Induction/FrobeniusReciprocity.lean`, and
   `TauCeti/RepresentationTheory/GrothendieckGroup/GroupAlgebra/Invariants.lean`. Adds
   `finrank_invariants_indFDRep`, `finrankInvariantsK0_indK0`, and the cyclic
   prime-to-characteristic calculation using equivariant Kummer, the landed power-class `K₀`
   identity, `finrankTensorInvariantsK0`, `finrank_H1_eq_finrank_representationInvariants`, and the
   degree-two duality formula. Needs no earlier target split, but is opened only after
   `kummer-equiv-mixed-equivariant` lands.

4. **feat: prove the mixed-characteristic Euler characteristic formula.** Files:
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/Formula.lean` and
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/Mixed.lean`. Adds
   `natCard_continuousCohomology_one_eq_mul_of_localEulerCharacteristic_eq_localCardNorm`,
   `finrank_continuousCohomology_one_eq_add_of_localEulerCharacteristic_eq_localCardNorm`, the
   prime-power and primary-decomposition devissage, and exports `eulerCharacteristic_mixed` and
   `eulerCharacteristic_finrank_fp`. Needs splits 1, 2, and 3; it is the only split that completes
   the roadmap target.

## Partial status

Proved:

- equality of two additive invariants on modular `ExactK0` from equality after induction from
  every cyclic subgroup of order prime to the characteristic;
- equality after `indK0` from equality on actual induced finite-dimensional representations;
- the corresponding equality of `localEulerCharacteristicK0` and `localCardNormK0` for one finite
  Galois quotient;
- the global reduction for all finite smooth discrete `ZMod ℓ` Galois representations, both in
  homomorphism form and in the objectwise form expected from Shapiro;
- induction preserves the dimension of invariant vectors for finite-dimensional representations;
- invariant dimension after `indK0` equals invariant dimension over the subgroup;
- the elementary conversion of `localEulerCharacteristic = localCardNorm` into the pinned
  cardinality formula;
- the conversion of the same equality into the pinned `ZMod p` finrank formula.

Remaining:

- consume the final Shapiro supplier API and identify the induced quotient representation with
  the Galois representation over the fixed field;
- consume the final equivariant Kummer supplier API and perform the cyclic
  prime-to-characteristic `H¹` calculation using the landed power-class `K₀` identity;
- combine that calculation with the landed `H²` dual formula and coprime descent;
- prove the prime-power and primary-decomposition devissage from the prime-coefficient formula;
- apply the proved numerical conversion lemmas to export `eulerCharacteristic_mixed` and
  `eulerCharacteristic_finrank_fp` with their pinned statements.
