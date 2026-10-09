<!--tauceti-lookahead:v1 {"area":"ClassFieldTheory","slug":"euler-characteristic-mixed","main":"fa036948c1524cdcb329a0a78082f0eb1fa51dc4","status":"partial","suppliers":["euler-characteristic-shapiro","kummer-equiv-mixed-equivariant"],"splits":[{"n":1,"after":[],"title":"feat: reduce the local Euler characteristic by modular Artin induction"},{"n":2,"after":[],"title":"feat: transport the local Euler characteristic across Shapiro"},{"n":3,"after":[],"title":"feat: tensor-invariant dimensions of lines and the regular representation"},{"n":4,"after":[],"title":"feat: the class of the power classes of a local field as a modular representation"},{"n":5,"after":[3,4],"title":"feat: count first-cohomology invariants of a finite Galois layer by Kummer theory"},{"n":6,"after":[5],"title":"feat: compute cyclic prime-to-characteristic Euler characteristics"},{"n":7,"after":[],"title":"feat: reduce the local Euler characteristic formula to prime coefficients"},{"n":8,"after":[1,2,3,4,5,6,7],"title":"feat: prove the mixed-characteristic Euler characteristic formula"}]}-->

# Mixed-characteristic Euler characteristic lookahead

This branch develops `euler-characteristic-mixed` on main commit
`fa036948c1524cdcb329a0a78082f0eb1fa51dc4`. It proves the modular-Artin reduction, the Shapiro
transport, the dévissage to prime-field coefficients, the numerical conversion from
`χ_F(A) = φ_F(A)` to both pinned formulae, and, new in this round, the whole arithmetic count of the
cyclic case at a finite Galois layer: for `L/K` finite Galois with `σ(L) ⊇ μ_ℓ` and `A` an
`𝔽_ℓ[Gal(L/K)]`-module with `ℓ ∤ [L:K]`,
`dim (H¹(Gal(Kˢ/σ(L)), 𝔽_ℓ) ⊗ A)ᴳ = dim (μ_ℓ^∨ ⊗ A)ᴳ + dim Aᴳ + [ℓ = p][K:ℚ_p] dim A`
(README steps 10–12). It does not yet prove either exported target theorem: what remains is the
transport of that count to `continuousCohomology` of a `GalRep ℓ K` (split 6) and the final assembly
(split 8).

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

Differences: PR #13633 writes `shapiroGalRep` with surrounding section variables (now named `σ`
rather than `sigma`); the stub spells its binders out so the opaque body does not erase `sigma` and
`hσ`. This is the same elaborated signature. The three instances and both comparison theorems are
verbatim from the PR modulo those explicit binders; the PR's current head lists the instance
arguments of `localCardNorm_galRepOfQuotient_ind` in the order K-structure, `FinitePadicExtension K
p`, L-structure, `FinitePadicExtension L p`, which changes nothing for callers. The PR's carrier
linear equivalence `shapiroGalRepLinearEquiv` and action formula `shapiroGalRepLinearEquiv_ρ_apply`
are not stubbed yet because nothing on the branch consumes them; split 6 will (see below).

## Pull-request split plan

1. **feat: reduce the local Euler characteristic by modular Artin induction.** Files:
   `TauCeti/RepresentationTheory/GrothendieckGroup/GroupAlgebra/Induction.lean` and
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/ModularInduction.lean`.
   Adds `comp_indK0_eq_of_eq_on_indFDRep`,
   `eq_of_comp_indK0_eq_of_cyclic_coprime`,
   `localEulerCharacteristicK0_eq_localCardNormK0_of_indCyclicCoprime`,
   `forall_localEulerCharacteristic_eq_localCardNorm_of_indCyclicCoprime`, and
   `forall_localEulerCharacteristic_eq_localCardNorm_of_indFDRep`. Needs no earlier split
   (about 190 lines).

2. **feat: transport the local Euler characteristic across Shapiro.** File:
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/Shapiro.lean` (appended to the
   file `main` already has). Adds
   `localEulerCharacteristic_eq_localCardNorm_galRepOfQuotient_ind_of_shapiro`,
   `localEulerCharacteristic_eq_localCardNorm_fdGalRepOfQuotient_indFDRep_of_shapiro`, and
   `localEulerCharacteristic_eq_localCardNorm_galRepOfQuotient_ind_of_shapiroField`. Needs no
   earlier target split; open it after `euler-characteristic-shapiro` (PR #13633) lands
   (about 160 lines).

3. **feat: tensor-invariant dimensions of lines and the regular representation.** Files:
   `TauCeti/RepresentationTheory/Induction/FrobeniusReciprocity.lean` (appended),
   `TauCeti/RepresentationTheory/GrothendieckGroup/GroupAlgebra/Invariants.lean` (appended) and the
   new `TauCeti/RepresentationTheory/GrothendieckGroup/GroupAlgebra/TensorInvariants.lean`. Adds
   `finrank_invariants_indFDRep`, `finrankInvariantsK0_indK0`,
   `Representation.dualTprodEquivTrivialOfFinrankEqOne` (`V^∨ ⊗ V` is trivial for a line),
   `fdRepK0RingEquiv_dual_mul_self_eq_one` (`[M^∨][M] = 1`),
   `finrankInvariantsK0_permK0_self_mul` (`dim (k[G] ⊗ V)ᴳ = dim V`) and
   `finrankTensorInvariantsK0_dual_mul_one_add_add` (the step-12 count). Needs no earlier split and
   no supplier (about 220 lines).

4. **feat: the class of the power classes of a local field as a modular representation.** Files:
   the new `TauCeti/RepresentationTheory/GrothendieckGroup/GroupAlgebra/LatticeDefect/ZMod.lean`
   and the new `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/PowerClasses.lean`
   (its general `quotSMulTopPowerClassEquiv` part may instead go next to `powerClassQuotient` if a
   reviewer prefers). Adds `Representation.baseChangeRestrictScalarsIntEquiv`,
   `reductionK0_restrictScalarsInt`,
   `zsmulTop_toAddSubgroup_eq_powerSubgroup`, `quotSMulTopPowerClassEquiv`,
   `quotSMulTopUnitsPowerClassRepresentationEquiv`, the finiteness instance of the power classes,
   `exactK0_powerClassRepresentation_of_isUnit` and
   `exactK0_powerClassRepresentation_eq_add_finrank_smul` (README step 11 read on the Kummer side).
   Needs no earlier split and no supplier (about 270 lines).

5. **feat: count first-cohomology invariants of a finite Galois layer by Kummer theory.** File:
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/KummerInvariants.lean` (new).
   Adds `torsionByUnitsEquivKummerCoeff` (`μ_ℓ(L) ≃ μ_ℓ(Kˢ)` as `Gal(L/K)`-representations when
   `σ(L) ⊇ μ_ℓ`),
   `finrank_invariants_kummerH1FiniteRepresentation_tprod_of_isUnit` and
   `finrank_invariants_kummerH1FiniteRepresentation_tprod_of_finitePadicExtension` (README steps
   10–12 at a finite layer). Needs splits 3 and 4; open it after `kummer-equiv-mixed-equivariant`
   (PR #13645) lands, replacing the `Stubs` import by `EquivariantKummer` (about 280 lines).

6. **feat: compute cyclic prime-to-characteristic Euler characteristics.** File:
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/CyclicCoprime.lean` (not yet
   written). For a finite smooth `A : GalRep ℓ F` on which an open normal subgroup of index prime to
   `ℓ` acts trivially, proves `localEulerCharacteristic = localCardNorm`. Needs split 5.

7. **feat: reduce the local Euler characteristic formula to prime coefficients.** Files:
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/Devissage.lean` and
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/Formula.lean`. Adds
   `localEulerCharacteristic_eq_localCardNorm_of_nsmul_eq_zero`,
   `localEulerCharacteristic_eq_localCardNorm_of_forall_prime` (steps 1–2: the coefficient change
   to `ZMod ℓ` for an `ℓ`-torsion module and the induction on `#A` along
   `0 → A[ℓ] → A → A / A[ℓ] → 0`),
   `natCard_continuousCohomology_one_eq_mul_of_localEulerCharacteristic_eq_localCardNorm`, and
   `finrank_continuousCohomology_one_eq_add_of_localEulerCharacteristic_eq_localCardNorm`.
   Needs no earlier split and no supplier: it can be opened on current `main` (about 270 lines).

8. **feat: prove the mixed-characteristic Euler characteristic formula.** File:
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/Mixed.lean` (not yet
   written). Applies split 6 to `shapiroGalRep B` for `C` cyclic of order prime to `ℓ` (its action
   factors through `C`, by PR #13633's `shapiroGalRepLinearEquiv_ρ_apply`), transports through
   split 2 and feeds splits 1 and 7 to export `eulerCharacteristic_mixed` and
   `eulerCharacteristic_finrank_fp` through split 7's numerical forms. Needs every other split; it
   is the only split that completes the roadmap target.

## Partial status

Proved:

- equality of additive invariants on modular `ExactK0` from equality after induction from cyclic
  subgroups of order prime to the characteristic, and the fixed-quotient and global modular-Artin
  reductions for finite smooth discrete `ZMod ℓ` Galois representations (split 1);
- the Shapiro implication transporting `χ = φ` from the canonical fixed field to the inflated
  induced module, including Tau Ceti's finite-dimensional induction model (split 2);
- the representation theory of step 12: induction preserves invariant dimension; `[M^∨][M] = 1` for
  a line; `dim (k[G] ⊗ V)ᴳ = dim V`; and the tensor-invariant dimension of
  `[M^∨](1 + [M] + c[k[G]])` is `dim (M^∨ ⊗ A)ᴳ + dim Aᴳ + c dim A` (split 3);
- the class of `Lˣ/(Lˣ)^ℓ` as a `𝔽_ℓ[Gal(L/K)]`-representation, `1 + [μ_ℓ(L)]` away from `p` and
  `1 + [μ_p(L)] + [K:ℚ_p][𝔽_p[G]]` at `p`, from the landed lattice-defect identities (split 4);
- `μ_ℓ(L) ≃ μ_ℓ(Kˢ)` equivariantly when `σ(L) ⊇ μ_ℓ`, and the count
  `dim (H¹(Gal(Kˢ/σ(L)), 𝔽_ℓ) ⊗ A)ᴳ = dim (μ_ℓ^∨ ⊗ A)ᴳ + dim Aᴳ + [ℓ = p][K:ℚ_p] dim A`
  (split 5, through the Kummer stub);
- the dévissage (steps 1–2) and the conversion of `χ = φ` into both pinned formulae (split 7).

Remaining:

- split 6, the cyclic case over a `GalRep`: for finite smooth `A : GalRep ℓ F` and an open normal
  subgroup `N` of index prime to `ℓ` acting trivially, shrink `N` to fix `μ_ℓ`
  (`exists_openNormalSubgroup_le_muNRep_ρ_eq_self_of_coprime`); realize `A` and `μ_ℓ` as
  `fdGalRepOfQuotient` of representations of `G = G_F/N` (`exists_fdGalRepOfQuotient_iso_muNRep`
  for `μ_ℓ`); then `dim H⁰ = dim Aᴳ`, `dim H² = dim (μ_ℓ^∨ ⊗ A)ᴳ`
  (`finrank_continuousCohomology_two_fdGalRepOfQuotient`), and
  `dim H¹ = dim (h1ConjRepresentation ⊗ A)ᴳ` (`finrank_H1_eq_finrank_representationInvariants`,
  after identifying `continuousCohomology 1` with `H1`). The remaining work is the transport of
  split 5's count across `absoluteGaloisGroupRestrictEquiv` (Mathlib's `Field.absoluteGaloisGroup`
  vs Tau Ceti's `AbsoluteGaloisGroup`), the fixed field `L` of `N` with an embedding `σ`
  (`G_F/N ≃ Gal(L/F)` through `quotientFixingSubgroupFieldRangeEquiv`), and the identification of
  `h1ConjRepresentation` with `kummerH1FiniteRepresentation` and of the `μ_ℓ` representations;
  then the arithmetic `χ = φ`;
- split 8: stub `shapiroGalRepLinearEquiv`/`shapiroGalRepLinearEquiv_ρ_apply` from PR #13633, show
  that the preimage of `⊥ ≤ C` acts trivially on `shapiroGalRep B` with index `#C` prime to `ℓ`,
  apply split 6, and assemble with splits 1, 2 and 7.
