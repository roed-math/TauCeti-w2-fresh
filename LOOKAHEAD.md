<!--tauceti-lookahead:v1 {"area":"ClassFieldTheory","slug":"cyclotomic-character-artin-map-padic","main":"e27e98cc5732fd4a5d9f6d48103b3bac64fcf9cb","status":"complete","suppliers":["cyclotomic-symbol-norm-fixes"],"splits":[{"n":1,"after":[],"title":"feat(ClassFieldTheory/Local): prescribe cyclotomic character and unramified action over Q_p"},{"n":2,"after":[1],"title":"feat(ClassFieldTheory/Local): cyclotomic character of the Artin symbols of units of Q_p"}]}-->

# Lookahead: `cyclotomic-character-artin-map-padic` (ClassFieldTheory, Layer 7, step 4)

Built on `main` at `e27e98cc5732fd4a5d9f6d48103b3bac64fcf9cb`. The whole target is proved on this
branch against one stub, `TauCeti.cyclotomicSymbol_norm_fixes`.

## Stubbed declaration

Supplier: `cyclotomic-symbol-norm-fixes` (Layer 7, step 2). No open PR; the statement comes from
`ClassFieldTheory/Suggested.lean`.

`Suggested.lean` signature (verbatim):

```lean
theorem cyclotomicSymbol_norm_fixes (p : ℕ) [Fact p.Prime] (m : ℕ) [NeZero m]
    (M : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) [FiniteDimensional ℚ_[p] M]
    (hM : M ≤ IntermediateField.adjoin ℚ_[p] {z : AlgebraicClosure ℚ_[p] | z ^ m = 1})
    (y : Mˣ) (σ : Field.absoluteGaloisGroup ℚ_[p])
    (hσ : ∀ z : AlgebraicClosure ℚ_[p], z ^ m = 1 →
      σ.toRingEquiv z =
        z ^ ((cyclotomicSymbol m p (Units.map (Algebra.norm ℚ_[p] : M →* ℚ_[p]) y) :
          ZMod m).val))
    (x : M) :
    σ.toRingEquiv (x : AlgebraicClosure ℚ_[p]) = x :=
  sorry
```

Stub (`TauCeti/Lookahead/CyclotomicCharacterArtinMapPadic/Stubs.lean`): the same statement,
character for character, as `TauCeti.cyclotomicSymbol_norm_fixes`.

Differences: only the namespace. `TauCetiRoadmap.ClassFieldTheory` becomes `TauCeti`, because
the neighbouring `cyclotomicSymbol` (`Local/ExplicitCyclotomicSymbol/Basic.lean`) and
`prod_cyclotomicSymbol` (`.../ProductFormula.lean`) landed in namespace `TauCeti`. `main`'s
`cyclotomicSymbol (m) [NeZero m] (p) [Fact p.Prime]` takes the same arguments as the pinned form,
so nothing else needed adapting. The supplier will probably land in
`Local/ExplicitCyclotomicSymbol/NormFixes.lean`. When it does, replace the import of the stub module
in split 2 with that module and delete `TauCeti/Lookahead/`.

## The target

`TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_padic` (split 2):

```lean
theorem localCyclotomicCharacter_artinMap_padic (u : ℤ_[p]ˣ)
    (σ : Field.absoluteGaloisGroup ℚ_[p])
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization ℚ_[p]) =
      artinMap ℚ_[p] (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u)) :
    localCyclotomicCharacter p ℚ_[p] σ = u⁻¹
```

Departures from the pinned `cyclotomicCharacter_artinMap_padic`, both following `main`'s landed
step 3, `localCyclotomicCharacter_artinMap_padic_uniformizer` (`Local/Cyclotomic.lean`):
- The name and conclusion use `localCyclotomicCharacter p ℚ_[p] σ`. This is `main`'s bundled form
  of the pinned `cyclotomicCharacter (AlgebraicClosure ℚ_[p]) p σ.toRingEquiv`, and the two are
  equal by `localCyclotomicCharacter_apply` (`rfl`).
- There is no `[IsNonarchimedeanLocalField ℚ_[p]]` binder: `main` has that instance globally.

## Split plan

1. **`feat(ClassFieldTheory/Local): prescribe cyclotomic character and unramified action over Q_p`**
   (after: none). Adds
   `TauCeti.ClassFieldTheory.exists_localCyclotomicCharacter_eq_and_apply_of_pow_eq_one` to
   `TauCeti/NumberTheory/ClassFieldTheory/Local/Cyclotomic.lean` (about +90 lines, docstring
   included): for `u ∈ ℤ_pˣ` and `f ≠ 0`, some `ρ ∈ G_{ℚ_p}` has `χ_cyc(ρ) = u` and sends every
   `(p^f − 1)`-st root of unity `ζ` to `ζ ^ p`. This is the "linear disjointness" input of step 4.
   The split also factors the repeated proof that `p` is a uniformizer of `ℚ_[p]` into the private
   `isUniformizer_padic`, now used by `localArtinMap_cyclotomic_padic` as well. It needs no
   supplier and can be opened now. On `main`, nothing imports `Local/Cyclotomic.lean`.
2. **`feat(ClassFieldTheory/Local): cyclotomic character of the Artin symbols of units of Q_p`**
   (after: 1, and the supplier `cyclotomic-symbol-norm-fixes`). About 400 lines:
   - `TauCeti/NumberTheory/ClassFieldTheory/Local/ArtinMap.lean` (+19):
     `mem_normGroup_of_mk_eq_artinMap`. A lift of `Art_K(x)` that fixes a finite Galois `M` makes
     `x` a norm from `M`.
   - new `TauCeti/RingTheory/RootsOfUnity/Coprime.lean` (44 lines):
     `MonoidHom.map_eq_pow_of_coprime`. An endomorphism acting by `z ↦ z ^ c` on `μ_a` and `μ_b`,
     with `a` and `b` coprime, acts by `z ↦ z ^ c` on `μ_{ab}`.
   - new `TauCeti/NumberTheory/ClassFieldTheory/Local/ExplicitCyclotomicSymbol/ArtinMap.lean`
     (338 lines):
     - private helpers on the action of `Field.absoluteGaloisGroup` (`absoluteGaloisGroup_mul_apply`
       and its relatives);
     - `eq_one_mod_of_pow_eq_pow_pow`: the order of `p` modulo `p^f − 1`;
     - `apply_eq_apply_of_toZModPow_eq`, `isUniformizer_mul_unit`,
       `pow_totient_mul_apply_eq_self` and `apply_eq_pow_cyclotomicSymbol`;
     - the comparison at level `p^n`, `exists_localCyclotomicCharacter_eq_inv_and_apply_eq`, which
       uses the stub;
     - the exported theorem `localCyclotomicCharacter_artinMap_padic`.

   This split completes the target. At port time, replace
   `import TauCeti.Lookahead.CyclotomicCharacterArtinMapPadic.Stubs` with the supplier's module.
