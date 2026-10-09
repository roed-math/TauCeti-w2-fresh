<!--tauceti-lookahead:v1 {"area":"ClassFieldTheory","slug":"euler-characteristic-mixed","main":"f847e07773fd67fbdd93708c4068a829ee7276ff","status":"partial","suppliers":["euler-characteristic-shapiro","kummer-equiv-mixed-equivariant"],"splits":[{"n":1,"after":[],"title":"feat: reduce the local Euler characteristic by modular Artin induction"},{"n":2,"after":[],"title":"feat: transport the local Euler characteristic across Shapiro"},{"n":3,"after":[],"title":"feat: compute cyclic prime-to-characteristic Euler characteristics"},{"n":4,"after":[],"title":"feat: reduce the local Euler characteristic formula to prime coefficients"},{"n":5,"after":[1,2,3,4],"title":"feat: prove the mixed-characteristic Euler characteristic formula"}]}-->

# Mixed-characteristic Euler characteristic lookahead

This branch develops `euler-characteristic-mixed` on main commit
`f847e07773fd67fbdd93708c4068a829ee7276ff`. It proves the modular-Artin reduction, the numerical
conversion from `χ_F(A) = φ_F(A)` to both pinned formulae, the dévissage reducing `χ_F = φ_F` for
every finite smooth `A : GalRep n F` to prime-field coefficients, the
induction/invariant-dimension infrastructure, the Shapiro transport for both the canonical fixed field and Tau Ceti's
finite-dimensional induction model, the invariant-dimension consequence of equivariant Kummer,
and the equivariant identification of additive reduction of `Lˣ` with its power classes. It does
not yet prove either exported target theorem.

## Supplier stubs

All stubs are in `TauCeti/Lookahead/EulerCharacteristicMixed/Stubs.lean`. The definitions are
opaque to the proof: only the separately stated API is used.

### `kummer-equiv-mixed-equivariant`

The only declaration named `kummerEquiv_mixed` in the roadmap's `Suggested.lean` is the older,
non-equivariant local Kummer equivalence (copied verbatim):

```lean
noncomputable def kummerEquiv_mixed (p : ℕ) [Fact p.Prime] (F : Type) [Field F]
    [Algebra ℚ_[p] F] [Module.Finite ℚ_[p] F] (n : ℕ) (_hn : n ≠ 0) :
    Additive (Fˣ ⧸ (powMonoidHom n : Fˣ →* Fˣ).range) ≃+ H n F 1 (muNRep n F)
```

Its pinned computation rule is (also verbatim):

```lean
theorem kummerEquiv_mixed_mk (p : ℕ) [Fact p.Prime] (F : Type) [Field F]
    [Algebra ℚ_[p] F] [Module.Finite ℚ_[p] F] (n : ℕ) (hn : n ≠ 0) (a : Fˣ) :
    kummerEquiv_mixed p F n hn (Additive.ofMul (QuotientGroup.mk a)) = kummerClass n F a
```

The supplier target's definitive README step instead pins an equivariant statement:
`H¹(L,𝔽_ℓ) ≅ μ_ℓ^{−1} ⊗ Lˣ/(Lˣ)^ℓ` as `𝔽_ℓ[G]`-modules, natural in the
`K`-automorphisms of `L`. PR #13607 has landed on `main` and supplies the finite-layer
representations (`kummerH1FiniteRepresentation`, `kummerCoeffFiniteRepresentation`,
`powerClassRepresentation`) and their action lemmas, so none of those is stubbed. The open supplier
PR #13645 states the final equivalence under the name `kummerH1FiniteRepresentationEquiv`, in
`TauCeti/FieldTheory/GaloisCohomology/EquivariantKummer.lean`, section `FiniteGalois` (section
variables `[Normal K L] (sigma : L →ₐ[K] SeparableClosure K) (n : ℕ)`). The stub copies that
form from PR #13645's diff, unchanged:

```lean
def kummerH1FiniteRepresentationEquiv (hn : IsUnit (n : K))
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K n, g • xi = xi) :
    (kummerH1FiniteRepresentation sigma n).Equiv
      ((kummerCoeffFiniteRepresentation sigma n hN).dual.tprod
        (powerClassRepresentation (K := K) (L := L) n))
```

Differences from `Suggested.lean`: the name (`kummerH1FiniteRepresentationEquiv`, not
`kummerEquiv_mixed`), and the statement is an equivalence of `Gal(L/K)`-representations at a
finite Galois layer with any `n` invertible in `K`, not the older additive equivalence over one
local field. Its hypotheses therefore include `Normal K L`, an embedding `sigma`, and triviality of
the fixing subgroup on the Kummer coefficient, and its codomain carries the inverse cyclotomic
twist. The README, rather than `Suggested.lean`, is definitive for this supplier list item, and
PR #13645 is what will land. The PR's `dualTensorHom_kummerH1FiniteRepresentationEquiv` is not
stubbed because the target does not consume it. (An earlier session stubbed this equivalence
under the README name `kummerEquiv_mixed` with `ell` prime; it now follows the PR.)

### `euler-characteristic-shapiro`

`Suggested.lean` contains no declaration signature for this supplier. Its README pins the
following statement: `χ_K(Ind B) = χ_{K_C}(B)` and `φ_K(Ind B) = φ_{K_C}(B)`, with the second
identity following from `[K_C:ℚ_p] = [K_C:K][K:ℚ_p]`. The declarations below are copied from
open PR #13633's diff and stated unchanged, except that the stub spells out section variables in
the definition header:

```lean
def shapiroGalRep (sigma : L →ₐ[K] SeparableClosure K) (n : ℕ)
    {V : OpenNormalSubgroup (Field.absoluteGaloisGroup K)}
    {C : Subgroup (Field.absoluteGaloisGroup K ⧸ V.toSubgroup)}
    (hσ : (absoluteGaloisGroupExtend K L sigma).range =
      C.comap (QuotientGroup.mk' V.toSubgroup))
    (B : Rep (ZMod n) C) : GalRep n L

instance : DiscreteTopology (shapiroGalRep sigma n hσ B).V
instance [Finite B] : Finite (shapiroGalRep sigma n hσ B).V
instance : Fact (IsSmoothDiscrete (ZMod n) (shapiroGalRep sigma n hσ B))

theorem localEulerCharacteristic_galRepOfQuotient_ind
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (hn : (n : K) ≠ 0) [Finite B] :
    localEulerCharacteristic hn ((galRepOfQuotient n K V).obj (Rep.ind C.subtype B)) =
      localEulerCharacteristic
        (map_natCast (algebraMap K L) n ▸ (map_ne_zero (algebraMap K L)).2 hn)
        (shapiroGalRep sigma n hσ B)

theorem localCardNorm_galRepOfQuotient_ind (p : ℕ) [Fact p.Prime]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [FinitePadicExtension K p] [FinitePadicExtension L p]
    [IsScalarTower ℚ_[p] K L] [Finite B] :
    localCardNorm p ((galRepOfQuotient n K V).obj (Rep.ind C.subtype B)) =
      localCardNorm p (shapiroGalRep sigma n hσ B)
```

Differences: PR #13633 writes `shapiroGalRep` with surrounding section variables;
the stub spells its binders out so the opaque body does not erase `sigma` and `hσ`. This is the
same elaborated signature. The three instances and both comparison theorems are verbatim from the
PR modulo those explicit binders. The PR's carrier linear equivalence, action formula, and index
lemma are not stubbed because the target does not consume them.

## Pull-request split plan

1. **feat: reduce the local Euler characteristic by modular Artin induction.** Files:
   `TauCeti/RepresentationTheory/GrothendieckGroup/GroupAlgebra/Induction.lean` and
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/ModularInduction.lean`.
   Adds `comp_indK0_eq_of_eq_on_indFDRep`,
   `eq_of_comp_indK0_eq_of_cyclic_coprime`,
   `localEulerCharacteristicK0_eq_localCardNormK0_of_indCyclicCoprime`,
   `forall_localEulerCharacteristic_eq_localCardNorm_of_indCyclicCoprime`, and
   `forall_localEulerCharacteristic_eq_localCardNorm_of_indFDRep`. Needs no earlier split.

2. **feat: transport the local Euler characteristic across Shapiro.** File:
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/Shapiro.lean` (appended to the
   file `main` already has). Adds
   `localEulerCharacteristic_eq_localCardNorm_galRepOfQuotient_ind_of_shapiro`,
   `localEulerCharacteristic_eq_localCardNorm_fdGalRepOfQuotient_indFDRep_of_shapiro`, and
   `localEulerCharacteristic_eq_localCardNorm_galRepOfQuotient_ind_of_shapiroField`. Needs no
   earlier target split; open it after `euler-characteristic-shapiro` (PR #13633) lands.

3. **feat: compute cyclic prime-to-characteristic Euler characteristics.** Files:
   `TauCeti/RepresentationTheory/Induction/FrobeniusReciprocity.lean`,
   `TauCeti/RepresentationTheory/GrothendieckGroup/GroupAlgebra/Invariants.lean`,
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/PowerClasses.lean`,
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/KummerInvariants.lean`, and a
   focused `CyclicCoprime.lean` (not yet written). Adds `finrank_invariants_indFDRep`,
   `finrankInvariantsK0_indK0`, the reduction/power-class representation equivalence
   `quotSMulTopUnitsPowerClassRepresentationEquiv`,
   `finrank_invariants_kummerH1FiniteRepresentation_eq`, and the cyclic calculation. Needs no
   earlier target split; open it after `kummer-equiv-mixed-equivariant` (PR #13645) and
   `euler-characteristic-shapiro` (PR #13633, for the action formula of `shapiroGalRep`) land.

4. **feat: reduce the local Euler characteristic formula to prime coefficients.** Files:
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/Devissage.lean` and
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/Formula.lean`. Adds
   `localEulerCharacteristic_eq_localCardNorm_of_nsmul_eq_zero`,
   `localEulerCharacteristic_eq_localCardNorm_of_forall_prime` (steps 1–2: the coefficient change
   to `ZMod ℓ` for an `ℓ`-torsion module and the induction on `#A` along
   `0 → A[ℓ] → A → A / A[ℓ] → 0`),
   `natCard_continuousCohomology_one_eq_mul_of_localEulerCharacteristic_eq_localCardNorm`, and
   `finrank_continuousCohomology_one_eq_add_of_localEulerCharacteristic_eq_localCardNorm`.
   Needs no earlier split and no supplier: it can be opened on current `main`.

5. **feat: prove the mixed-characteristic Euler characteristic formula.** File:
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/Mixed.lean` (not yet
   written). Combines splits 1–3 into `χ_F = φ_F` for every finite smooth `ZMod ℓ`-module, feeds
   it to split 4's `localEulerCharacteristic_eq_localCardNorm_of_forall_prime`, and exports
   `eulerCharacteristic_mixed` and `eulerCharacteristic_finrank_fp` through split 4's numerical
   forms. Needs splits 1, 2, 3 and 4; it is the only split that completes the roadmap target.

## Partial status

Proved:

- equality of additive invariants on modular `ExactK0` from equality after induction from cyclic
  subgroups of order prime to the characteristic;
- equality after `indK0` from equality on actual induced finite-dimensional representations;
- the corresponding fixed-quotient and global modular-Artin reductions for finite smooth discrete
  `ZMod ℓ` Galois representations;
- induction preserves invariant dimension, both for finite-dimensional representations and on the
  group-algebra Grothendieck group;
- the Shapiro implication transporting `χ = φ` from the canonical fixed field to the inflated
  induced module, including transport across Tau Ceti's finite-dimensional induction model;
- equivariant Kummer preserves invariant dimension;
- `G/nG ≃ G/Gⁿ` for a commutative group and, for `G = Lˣ`, this equivalence intertwines the
  `Gal(L/K)`-actions, connecting the landed power-class `K₀` identity
  (`reductionK0_quotSMulTop_units_eq_add_finrank_smul`, `reductionK0_quotSMulTop_units_of_isUnit`)
  to the Kummer representation;
- the dévissage (steps 1–2): `χ_F = φ_F` for every finite smooth discrete `A : GalRep n F`
  follows from `χ_F = φ_F` for every finite smooth discrete `ZMod ℓ`-module, `ℓ` prime
  (`localEulerCharacteristic_eq_localCardNorm_of_forall_prime`);
- the elementary conversion of `localEulerCharacteristic = localCardNorm` into the pinned
  cardinality formula and into the pinned `ZMod p` finrank formula.

Remaining (all for the cyclic calculation of split 3, then the assembly of split 5):

- stub, and consume, PR #13633's action formula `shapiroGalRepLinearEquiv` /
  `shapiroGalRepLinearEquiv_ρ_apply`, which says that `G_{K_C}` acts on `shapiroGalRep B` through
  `C`; it is needed to see that an open normal subgroup of index prime to `ℓ` acts trivially;
- for a finite smooth `ZMod ℓ`-module on which an open normal subgroup `N` of index prime to `ℓ`
  acts trivially: shrink `N` to fix `μ_ℓ` (`exists_openNormalSubgroup_le_muNRep_ρ_eq_self_of_coprime`),
  compute `dim H⁰ = dim A^G`, `dim H¹ = dim (H¹(N, 𝔽_ℓ) ⊗ A)^G`
  (`finrank_H1_eq_finrank_representationInvariants`, after identifying `H1` of the Galois group
  `Field.absoluteGaloisGroup` with `continuousCohomology 1` and `h1ConjRepresentation` with
  `kummerH1FiniteRepresentation` along `absoluteGaloisGroupRestrictEquiv`), and
  `dim H² = dim (μ_ℓ^{−1} ⊗ A)^G` (`finrank_continuousCohomology_two_fdGalRepOfQuotient`);
- evaluate the landed power-class `K₀` identities under `finrankTensorInvariantsK0`, identifying
  `reductionK0 (ZMod ℓ) (quotSMulTop ℓ)` with the class of `powerClassRepresentation` and the
  `ℓ`-torsion of `Lˣ` with `kummerCoeffFiniteRepresentation`; cancel the roots-of-unity term
  against `H²`, and evaluate the regular-representation term `dim (𝔽_ℓ[G] ⊗ A)^G = dim A` when
  `ℓ = p`;
- assemble the cyclic case with splits 1 and 2 into `χ = φ` for every finite smooth `ZMod ℓ`
  representation, then apply split 4 to export `eulerCharacteristic_mixed` and
  `eulerCharacteristic_finrank_fp` with their pinned statements.
