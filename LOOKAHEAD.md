<!--tauceti-lookahead:v1 {"area":"ClassFieldTheory","slug":"cyclotomic-character-artin-map","main":"35eba062841377c3f45196bdc1c67a530bd58c82","status":"partial","suppliers":["cyclotomic-character-artin-map-padic"],"splits":[{"n":1,"after":[],"title":"Prove the cyclotomic normalization over finite p-adic extensions"}]}-->

# Cyclotomic character of the local Artin map

This lookahead proves the norm formula for a finite **compatible** extension of `ℚ_[p]`. The exact
pinned target does not assume `ValuativeExtension ℚ_[p] F`, although the landed theorem
`TauCeti.ClassFieldTheory.artinMap_norm` and the local norm-valuation API both require it. No
declaration on `main` derives that compatibility from the target's assumptions. The branch is
therefore partial: it deliberately does not attach the target name to the stronger-hypothesis
result.

## Supplier stub

### `TauCeti.ClassFieldTheory.cyclotomicCharacter_artinMap_padic`

The signature pinned in
`/opt/roadmap/TauCetiRoadmap/ClassFieldTheory/Suggested.lean` is:

```lean
theorem cyclotomicCharacter_artinMap_padic (p : ℕ) [Fact p.Prime]
    [IsNonarchimedeanLocalField ℚ_[p]] (u : ℤ_[p]ˣ)
    (σ : Field.absoluteGaloisGroup ℚ_[p])
    (_hσ : (QuotientGroup.mk σ : Field.absoluteGaloisGroupAbelianization ℚ_[p])
      = artinMap ℚ_[p] (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u)) :
    cyclotomicCharacter (AlgebraicClosure ℚ_[p]) p σ.toRingEquiv = u⁻¹ :=
  sorry
```

The lookahead stub is:

```lean
namespace TauCeti.ClassFieldTheory

theorem cyclotomicCharacter_artinMap_padic (p : ℕ) [Fact p.Prime]
    [IsNonarchimedeanLocalField ℚ_[p]] (u : ℤ_[p]ˣ)
    (σ : Field.absoluteGaloisGroup ℚ_[p])
    (_hσ : (QuotientGroup.mk σ : Field.absoluteGaloisGroupAbelianization ℚ_[p])
      = artinMap ℚ_[p] (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u)) :
    cyclotomicCharacter (AlgebraicClosure ℚ_[p]) p σ.toRingEquiv = u⁻¹ := by
  sorry

end TauCeti.ClassFieldTheory
```

Source: `ClassFieldTheory/Suggested.lean`. The statement is unchanged. Its namespace changes from
the roadmap-only `TauCetiRoadmap.ClassFieldTheory` namespace to the neighbouring library namespace
`TauCeti.ClassFieldTheory`; the body uses `by sorry` rather than `:= sorry`, with no type-level
difference.

Supplier PR #13626 was also inspected at its current two-commit head. It adds
`exists_localCyclotomicCharacter_eq_and_apply_of_pow_eq_one`, a prerequisite for the supplier's
comparison argument, but it does not state `cyclotomicCharacter_artinMap_padic`; its description
explicitly leaves that exported comparison to a follow-up PR. Consequently there is no differing
PR signature to stub, and the stub continues to use the pinned `Suggested.lean` form.

## Split plan

### Split 1 — Prove the cyclotomic normalization over finite p-adic extensions

- Needs: no earlier split; the supplier `cyclotomic-character-artin-map-padic` and a resolution of
  the compatibility gap described below must have landed.
- Files: `TauCeti/NumberTheory/ClassFieldTheory/Local/Cyclotomic.lean`.
- Declaration: the pinned exported theorem
  `TauCeti.ClassFieldTheory.cyclotomicCharacter_artinMap`; the partial helper on this branch is its
  completed proof under the compatibility instance and is not a second permanent API.
- Change at port time: replace the lookahead stub import with the module containing the landed
  supplier theorem, then rename/adapt the partial helper once the target's hypotheses are valid.
- This is the last and only split, needs every other split vacuously, carries the target's exported
  theorem, and is the only split that completes the target.
- PR subject: `Prove the cyclotomic normalization over finite p-adic extensions`.

## Partial status

Proved: if the finite `ℚ_[p]`-algebra `F` carries `[ValuativeExtension ℚ_[p] F]`, then for a
valuation-zero unit `u` and a lift `σ` of `Art_F(u)`, the mapped cyclotomic character is
`N_{F/ℚ_p}(u)⁻¹`. The proof uses the landed norm compatibility of the abelianized cyclotomic
character, converts the norm to a unit of `ℤ_[p]`, and applies the single supplier stub.

Remaining: the exact pinned target omits `[ValuativeExtension ℚ_[p] F]`. The split cannot honestly be
proved from the pinned assumptions with the current API: `artinMap_norm` itself has that instance
argument, and Tau Ceti's `FinitePadicExtension` explicitly bundles it rather than deriving it from
`Algebra` and `Module.Finite`. A human roadmap/API decision must either add the compatibility
hypothesis to the target or identify a landed theorem that derives it. Until then the target name
must not be assigned to the stronger-hypothesis theorem.
