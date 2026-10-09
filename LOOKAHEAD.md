<!--tauceti-lookahead:v1 {"area":"ClassFieldTheory","slug":"euler-characteristic-mixed","main":"3cebb1d38d33d682052c1bebca9050b969f5366d","status":"partial","suppliers":["euler-characteristic-shapiro","kummer-equiv-mixed-equivariant"],"splits":[{"n":1,"after":[],"title":"feat: reduce the local Euler characteristic by modular Artin induction"},{"n":2,"after":[],"title":"feat: transport the local Euler characteristic across Shapiro"},{"n":3,"after":[],"title":"feat: compute cyclic prime-to-characteristic Euler characteristics"},{"n":4,"after":[1,2,3],"title":"feat: prove the mixed-characteristic Euler characteristic formula"}]}-->

# Mixed-characteristic Euler characteristic lookahead

This branch develops `euler-characteristic-mixed` on main commit
`3cebb1d38d33d682052c1bebca9050b969f5366d`. It proves the modular-Artin reduction, the numerical
conversion from `χ_F(A) = φ_F(A)` to both pinned formulae, the induction/invariant-dimension
infrastructure, the Shapiro transport implication, the invariant-dimension consequence of
equivariant Kummer, and the equivariant identification of additive reduction of `Lˣ` with its
power classes. It does not yet prove either exported target theorem.

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
`K`-automorphisms of `L`. PR #13607 provides the finite-layer representations but not yet this
final equivalence. The stubs copied from PR #13607's diff are:

```lean
instance instModuleZModPowerClassQuotient {L : Type*} [Field L] (n : ℕ) :
    Module (ZMod n) (Additive (powerClassQuotient Lˣ n))

def powerClassRepresentation (n : ℕ) :
    Representation (ZMod n) Gal(L/K) (Additive (powerClassQuotient Lˣ n))

@[simp]
theorem powerClassRepresentation_apply (n : ℕ) (tau : Gal(L/K))
    (x : Additive (powerClassQuotient Lˣ n)) :
    powerClassRepresentation (K := K) (L := L) n tau x =
      MonoidHom.toAdditive (powerClassMap n (Units.map (tau : L →* L))) x

def kummerCoeffFiniteRepresentation
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K n, g • xi = xi) :
    Representation (ZMod n) Gal(L/K) (KummerCoeff K n)

def kummerH1FiniteRepresentation :
    Representation (ZMod n) Gal(L/K)
      (H1 sigma.fieldRange.fixingSubgroup (ZMod n))
```

The final stub, copied from the completed supplier lookahead at
`8c82f4be63e36d04948aad075aea6dcd78d72f2a` (the continuation of PR #13607), is:

```lean
def kummerEquiv_mixed {ell : ℕ} [Fact ell.Prime]
    (hn : IsUnit (ell : K))
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K ell, g • xi = xi) :
    (kummerH1FiniteRepresentation sigma ell).Equiv
      ((kummerCoeffFiniteRepresentation sigma ell hN).dual.tprod
        (powerClassRepresentation (K := K) (L := L) ell))
```

Differences: the final form is an equivalence of representations at a finite Galois layer, not the
older additive equivalence over one local field. Consequently its hypotheses include `Normal K L`,
an embedding `sigma`, and triviality of the fixing subgroup on the Kummer coefficient, and its
codomain carries the inverse cyclotomic twist. The old `_mk` rule is not stubbed because this target
does not consume it. Conversely, the finite-layer definitions are absent from `Suggested.lean` but
are stated by PR #13607. The PR's unconsumed `Rep` wrappers and restriction-evaluation lemmas are
not stubbed. The stub omits PR #13607's `@[expose]` implementation attribute because no body is
available and the target consumes only the stated API.

### `euler-characteristic-shapiro`

`Suggested.lean` contains no declaration signature for this supplier. Its README pins the
following statement: `χ_K(Ind B) = χ_{K_C}(B)` and `φ_K(Ind B) = φ_{K_C}(B)`, with the second
identity following from `[K_C:ℚ_p] = [K_C:K][K:ℚ_p]`. PR #13295 supplies the fixed-field,
continuous-equivalence, and finite-index plumbing now present on `main`, but it does not state the
two final comparison theorems. The supplier declarations were therefore taken from the completed
supplier lookahead at `a75a20187d082f40b5bc76be47f711dd27a0bebc`. Its normalized-order theorem
has the following source signature:

```lean
theorem localCardNorm_galRepOfQuotient_ind (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] K]
    [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L] [Finite B] :
    localCardNorm p ((galRepOfQuotient n K V).obj (Rep.ind C.subtype B)) =
      localCardNorm p (shapiroGalRep σ n hσ B)
```

The stubs as stated against the API on current `main` are:

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

Differences: the supplier lookahead writes `shapiroGalRep` with surrounding section variables;
the stub spells its binders out so the opaque body does not erase `sigma` and `hσ`. This is the
same elaborated signature. Its norm theorem uses `[Algebra ℚ_[p] K]` and
`[Algebra ℚ_[p] L]`; against current `main`, `localCardNorm` instead requires the bundled
`FinitePadicExtension` instances, so the stub states those and explicitly includes the local-field
structures they depend on. The Euler-characteristic theorem is unchanged. The supplier's linear
equivalence exposing the carrier of `shapiroGalRep` is not stubbed because the target never uses it.

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
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/Shapiro.lean`, extended with
   the fixed-field specialization when the supplier lands. Adds
   `localEulerCharacteristic_eq_localCardNorm_galRepOfQuotient_ind_of_shapiro` and the application
   to `shapiroField`. Needs no earlier target split; open it after
   `euler-characteristic-shapiro` lands.

3. **feat: compute cyclic prime-to-characteristic Euler characteristics.** Files:
   `TauCeti/RepresentationTheory/Induction/FrobeniusReciprocity.lean`,
   `TauCeti/RepresentationTheory/GrothendieckGroup/GroupAlgebra/Invariants.lean`,
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/PowerClasses.lean`,
   `TauCeti/NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/KummerInvariants.lean`, and a
   focused `CyclicCoprime.lean`. Adds `finrank_invariants_indFDRep`,
   `finrankInvariantsK0_indK0`, the reduction/power-class representation equivalence,
   `finrank_invariants_kummerH1FiniteRepresentation_eq`, and the cyclic calculation. Needs no
   earlier target split; open it after `kummer-equiv-mixed-equivariant` lands.

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

- equality of additive invariants on modular `ExactK0` from equality after induction from cyclic
  subgroups of order prime to the characteristic;
- equality after `indK0` from equality on actual induced finite-dimensional representations;
- the corresponding fixed-quotient and global modular-Artin reductions for finite smooth discrete
  `ZMod ℓ` Galois representations;
- induction preserves invariant dimension, both for finite-dimensional representations and on the
  group-algebra Grothendieck group;
- the Shapiro implication transporting `χ = φ` from the fixed field to the inflated induced module;
- equivariant Kummer preserves invariant dimension;
- `G/nG ≃ G/Gⁿ` for a commutative group and, for `G = Lˣ`, this equivalence intertwines the
  `Gal(L/K)`-actions, connecting the landed power-class `K₀` identity to the Kummer representation;
- the elementary conversion of `localEulerCharacteristic = localCardNorm` into the pinned
  cardinality formula and into the pinned `ZMod p` finrank formula.

Remaining:

- specialize the Shapiro bridge to the actual fixed field for every cyclic subgroup produced by
  modular Artin induction;
- adjoin `μ_ℓ`, apply coprime descent and the `H¹` tensor formula, and identify their quotient
  representations with the finite-layer Kummer representations;
- evaluate the landed power-class `K₀` identities under `finrankTensorInvariantsK0`, cancel the
  roots-of-unity term against the landed `H²` dual formula, and retain the regular-representation
  contribution when `ℓ = p`;
- use that cyclic calculation and Shapiro to prove `localEulerCharacteristic = localCardNorm` for
  every finite smooth `ZMod ℓ` representation;
- prove the prime-power and primary-decomposition devissage for an arbitrary exponent `n`;
- apply the proved numerical conversion lemmas to export `eulerCharacteristic_mixed` and
  `eulerCharacteristic_finrank_fp` with their pinned statements.
