<!--tauceti-lookahead:v1 {"area":"ClassFieldTheory","slug":"cyclotomic-character-artin-map","main":"58dbf602a1d4f7fce8934667f17672f1822513c7","status":"complete","suppliers":["cyclotomic-character-artin-map-padic"],"splits":[{"n":1,"after":[],"title":"feat: every Q_p-algebra structure on a local field is valuative"},{"n":2,"after":[1],"title":"feat: the cyclotomic character of a local Artin symbol is the inverse norm"}]}-->

# Cyclotomic character of the local Artin map

This lookahead proves the exact pinned target
`TauCeti.ClassFieldTheory.cyclotomicCharacter_artinMap` (ClassFieldTheory, Layer 7, the cyclotomic
normalization, step 5): for a finite extension `F/ℚ_p` and `u ∈ Fˣ` of valuation zero, every lift
`σ ∈ G_F` of `Art_F(u)` has `χ_cyc(σ) = N_{F/ℚ_p}(u)⁻¹`, read in `ℚ_pˣ`. The proof assumes only
the supplier stub `cyclotomicCharacter_artinMap_padic`.

The earlier partial state of this branch was blocked because the pinned target does not assume
`[ValuativeExtension ℚ_[p] F]`, which the landed `artinMap_norm` requires. This round closes that
gap honestly: split 1 proves that every `ℚ_[p]`-algebra structure on a nonarchimedean local field
is automatically a `ValuativeExtension` (`TauCeti.Padic.valuativeExtension`), with no continuity
or compatibility assumed. It is a prerequisite that the target needs, not new scope. The old
stronger-hypothesis helper `cyclotomicCharacter_artinMap_of_valuativeExtension` is gone, and the
target now carries its pinned name and signature.

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

Supplier PR #13626 was also inspected at its current two-commit head (`c79671bf`). It adds
`exists_localCyclotomicCharacter_eq_and_apply_of_pow_eq_one`, a prerequisite for the supplier's
comparison argument, but it does not state `cyclotomicCharacter_artinMap_padic`; its description
explicitly leaves that exported comparison to a follow-up PR. Consequently there is no differing
PR signature to stub, and the stub continues to use the pinned `Suggested.lean` form.

## Split plan

### Split 1: `feat: every Q_p-algebra structure on a local field is valuative`

- Needs first: nothing (builds on `main`).
- Files: `TauCeti/NumberTheory/LocalField/Padic.lean` (+120 lines, a new section
  "Algebras over `ℚ_[p]`" in the existing `TauCeti.Padic` namespace, plus module-docstring entries).
- Declarations, all in `TauCeti.Padic`, for `F` a nonarchimedean local field with any
  `[Algebra ℚ_[p] F]`:
  - `normalizedValuation_algebraMap_eq_one`: the normalized valuation of `F` vanishes on the image
    of a `p`-adic unit. `x ^ (p - 1)` is a principal unit
    (`Subgroup.pow_relIndex_mem`, `relIndex_unitFiltration_one_zero`), hence an `n`-th power for
    every `n` prime to `p` (`unitFiltration_one_le_range_powMonoidHom_of_isUnit`), and `ℤ` has
    no nonzero element divisible by all such `n`.
  - `ringChar_residueField_eq`: `ringChar 𝓀[F] = p`.
  - `natCast_ne_zero_of_algebra`: `(p : F) ≠ 0`.
  - `normalizedValuation_algebraMap`: `v_F(x) = v_F(p) · v_p(x)` on `ℚ_[p]ˣ`.
  - `valuativeExtension`: `ValuativeExtension ℚ_[p] F`.
- Roadmap attribution: `Roadmap: ClassFieldTheory` (a prerequisite of the step-5 target).

### Split 2: `feat: the cyclotomic character of a local Artin symbol is the inverse norm`

- Needs first: split 1, and the supplier `cyclotomic-character-artin-map-padic` landed on `main`.
- Files: `TauCeti/NumberTheory/ClassFieldTheory/Local/Cyclotomic.lean` (+57 lines, including the
  stub import that the port removes).
- Declaration: `TauCeti.ClassFieldTheory.cyclotomicCharacter_artinMap`, the pinned exported
  theorem. It gets the compatibility instance from `TauCeti.Padic.valuativeExtension`, applies
  `abelianizedLocalCyclotomicCharacter_artinMap_norm` (already on `main`), turns the norm into a
  unit of `ℤ_[p]` (`PadicInt.mkUnits`) and concludes with the supplier's
  `cyclotomicCharacter_artinMap_padic`.
- Port change: drop `import TauCeti.Lookahead.CyclotomicCharacterArtinMap.Stubs` and import the
  module where the supplier lands `cyclotomicCharacter_artinMap_padic`. If the supplier lands it
  in this same file (`Local/Cyclotomic.lean`, where PR #13626 is working), the import simply goes
  away. Delete `TauCeti/Lookahead/`.
- This is the last split. It needs every other split, carries the target's exported theorem,
  and is the only split that completes the target.

## Status

Complete: the pinned target is proved with exactly its pinned hypotheses, modulo the single
supplier stub.
