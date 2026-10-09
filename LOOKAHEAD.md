<!--tauceti-lookahead:v1 {"area":"ClassFieldTheory","slug":"euler-characteristic-mixed","main":"5946afd420963656ee276c03160777cd1b5adf74","status":"partial","suppliers":["modular-artin-exists-nsmul-mem-ind-cyclic-coprime"],"splits":[{"n":1,"after":[],"title":"feat: reduce the local Euler characteristic by modular Artin induction"},{"n":2,"after":[],"title":"feat: compare induced local Euler characteristics by Shapiro"},{"n":3,"after":[],"title":"feat: compute the cyclic prime-to-characteristic Euler characteristic"},{"n":4,"after":[1,2,3],"title":"feat: prove the mixed-characteristic Euler characteristic formula"}]}-->

# Mixed-characteristic Euler characteristic lookahead

This branch develops the `euler-characteristic-mixed` target on main commit
`5946afd420963656ee276c03160777cd1b5adf74`. It currently proves the modular-Artin reduction and
the final numerical conversion from `χ_F(A) = φ_F(A)` to the cardinality and `𝔽_p`-finrank
formulae. These are coherent parts of the target. It does not claim the two exported target
theorems.

## Supplier stubs

Only the modular-Artin supplier is consumed by the part proved here. The later Shapiro and
equivariant-Kummer suppliers are therefore not stubbed: a lookahead stub must expose only an API
actually used by the proof. In particular, PR #13295 contains plumbing for its first Shapiro split
but not the final Euler-characteristic comparison, while the merged part of #13296 contains the
generic rank-one twist helper but not the final equivariant Kummer export. Guessing either final
signature would not be a faithful supplier stub.

### `modularArtin_natCard_nsmul_mem_indCyclicCoprime`

Pinned signature in
`RepresentationTheory/ModularInduction/Suggested.lean` (with its surrounding variables
`{G : Type u} [Group G] [Finite G]`, `(k : Type u) [Field k]`, and
`(ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]`):

```lean
theorem modularArtin_natCard_nsmul_mem_indCyclicCoprime (x : modRepK0 k G) :
    Nat.card G • x ∈ modRepK0.indCyclicCoprime k G ℓ := by
```

Stub, copied from the statement in open PR #13595:

```lean
theorem modularArtin_natCard_nsmul_mem_indCyclicCoprime
    (x : ExactK0 (finiteModulesExactStructure k[G])) :
    Nat.card G • x ∈
      ⨆ (D : Subgroup G) (_ : IsCyclic D ∧ ¬ p ∣ Nat.card D), (indK0 k D).range := by
  sorry
```

The PR uses the landed `ExactK0 (finiteModulesExactStructure k[G])` API instead of the roadmap's
older `modRepK0` name. It expands the roadmap's named `indCyclicCoprime` subgroup as the supremum
of the ranges of `indK0`, because the names and ring structure anticipated by the older sketch are
owned by other work. It states prime-to-`p` as `¬ p ∣ Nat.card D` rather than a `Nat.Coprime`
predicate. These changes are exactly those in PR #13595, not local alterations.

### `modularArtin_exists_nsmul_mem_indCyclicCoprime`

Pinned signature in
`RepresentationTheory/ModularInduction/Suggested.lean` (with the same surrounding variables):

```lean
theorem modularArtin_exists_nsmul_mem_indCyclicCoprime (x : modRepK0 k G) :
    ∃ N : ℕ, 0 < N ∧ N • x ∈ modRepK0.indCyclicCoprime k G ℓ :=
  ⟨Nat.card G, Nat.card_pos, modularArtin_natCard_nsmul_mem_indCyclicCoprime k ℓ x⟩
```

Stub, copied from the statement in open PR #13595:

```lean
theorem modularArtin_exists_nsmul_mem_indCyclicCoprime
    (x : ExactK0 (finiteModulesExactStructure k[G])) :
    ∃ N : ℕ, 0 < N ∧ N • x ∈
      ⨆ (D : Subgroup G) (_ : IsCyclic D ∧ ¬ p ∣ Nat.card D), (indK0 k D).range := by
  sorry
```

The differences from the pinned form are the same `ExactK0` and explicit-supremum API changes as
for the preceding theorem. The PR also infers `k` and supplies only `p` explicitly when invoking
the first theorem, following the actual declaration's argument order.

## Pull-request split plan

1. **feat: reduce the local Euler characteristic by modular Artin induction.** Files:
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/ModularInduction.lean`.
   Adds `eq_of_comp_indK0_eq_of_cyclic_coprime`,
   `localEulerCharacteristicK0_eq_localCardNormK0_of_indCyclicCoprime`, and
   `forall_localEulerCharacteristic_eq_localCardNorm_of_indCyclicCoprime`. Needs no earlier
   split. The supplier stub is replaced by the declarations landed from PR #13595 before this PR
   is opened.
2. **feat: compare induced local Euler characteristics by Shapiro.** Files: the supplier's
   canonical local Euler-characteristic Shapiro module and its focused comparison module. Adds
   the induced `GalRep` construction and the equalities of `localEulerCharacteristic` and
   `localCardNorm` under induction from a subgroup. Needs no earlier split; it can be opened in
   parallel with splits 1 and 3 after `euler-characteristic-shapiro` lands.
3. **feat: compute the cyclic prime-to-characteristic Euler characteristic.** Files: focused
   modules beside the local Euler-characteristic Kummer and power-class modules. Adds the cyclic
   prime-to-characteristic calculation using equivariant Kummer, `finrankTensorInvariantsK0`, the
   unit power-class identity, `finrank_H1_eq_finrank_representationInvariants`, and the degree-two
   duality formula. Needs no earlier split; it can be opened in parallel with splits 1 and 2 after
   `kummer-equiv-mixed-equivariant` lands.
4. **feat: prove the mixed-characteristic Euler characteristic formula.** Files:
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/Formula.lean`,
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/Mixed.lean`, and the existing
   target-facing import location selected by neighbouring modules. Adds
   `natCard_continuousCohomology_one_eq_mul_of_localEulerCharacteristic_eq_localCardNorm`,
   `finrank_continuousCohomology_one_eq_add_of_localEulerCharacteristic_eq_localCardNorm`, the
   prime-power and primary-decomposition devissage, and exports `eulerCharacteristic_mixed` and
   `eulerCharacteristic_finrank_fp`. Needs splits 1, 2, and 3, and is the only split that completes
   the roadmap target.

## Partial status

Proved:

- equality of two additive invariants on modular `ExactK0` from equality after induction from
  every cyclic subgroup of order prime to the characteristic;
- the corresponding equality of `localEulerCharacteristicK0` and `localCardNormK0` for one finite
  Galois quotient;
- the global reduction for all finite smooth discrete `ZMod ℓ` Galois representations.
- the elementary conversion of `localEulerCharacteristic = localCardNorm` into the pinned
  cardinality formula;
- the conversion of the same equality into the pinned `ZMod p` finrank formula.

Remaining:

- replace the modular-Artin stubs after PR #13595 lands;
- consume the final Shapiro supplier API and identify the induced quotient representation with
  the Galois representation over the fixed field;
- consume the final equivariant Kummer supplier API and perform the cyclic
  prime-to-characteristic `H¹` calculation using the landed power-class `K₀` identity;
- combine that calculation with the landed `H²` dual formula and coprime descent;
- carry out prime-power and primary-decomposition devissage;
- apply the proved numerical conversion lemmas to export `eulerCharacteristic_mixed` and
  `eulerCharacteristic_finrank_fp` with their pinned statements.
