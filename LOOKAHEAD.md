<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"qcoh-higher-direct-image-vanishing","main":"ea7e54cf967c2ab502c7e69bf69501e5a3ae3130","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: uniform vanishing of quasi-coherent cohomology on qcqs schemes"}]}-->

# Lookahead: `qcoh-higher-direct-image-vanishing` (SchemeAndStackFoundations, §2.6)

Built on `main` at `ea7e54cf96` (resumed from tip `6e97178a37`, with `origin/main` merged in). The target's only pinned Lean form,
`QCoh.higherDirectImage_vanishing` (`SchemeAndStackFoundations/Suggested.lean`, §2.5–§2.7 block),
is proved here in full, with **no `sorry` anywhere on the branch**. The status is `partial` because
the target's prose (`qcoh_higherDirectImages`) also asks for more about `R^p f_*`; that part is
listed under *What remains* below.

## Stubs: none

The proof does not use the supplier `qcoh-pushforward` (open PR #21787). The bound comes from
results already on `main`:

- Serre vanishing on affine opens (`Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen`,
  `TauCeti/AlgebraicGeometry/Cohomology/Affine.lean`);
- the Mayer–Vietoris step (`TauCeti.AlgebraicGeometry.Scheme.Modules.subsingleton_cohomologyOn_sup_succ`,
  `Cohomology/MayerVietoris.lean`);
- the finite Leray cover bound (`Scheme.Modules.subsingleton_cohomologyOn_sup_of_card_le`,
  `Cohomology/FiniteCover.lean`);
- `Scheme.inf_mem_range_basicOpen` (`Scheme/Opens.lean`);
- Mathlib's `compact_open_induction_on`.

So no `TauCeti/Lookahead/QcohHigherDirectImageVanishing/Stubs.lean` was created, because the
target consumes nothing from the supplier. The header therefore has `"suppliers": []`. This proved
part can be opened as soon as it is wanted: it does not need to wait for PR #21787.

For the record, here is the pinned target and the form proved, which is identical up to the
namespace move (`TauCetiRoadmap.SchemeAndStackFoundations.QCoh` becomes `TauCeti.QCoh`).

`Suggested.lean`, verbatim:

```lean
theorem higherDirectImage_vanishing {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] [IsAffine S] :
    ∃ N : ℕ, ∀ (F : X.Modules) [F.IsQuasicoherent] (p : ℕ), N ≤ p →
      Subsingleton (Scheme.Modules.Cohomology F p) := by
  sorry
```

Branch (`TauCeti.QCoh.higherDirectImage_vanishing`):

```lean
theorem higherDirectImage_vanishing {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] [IsAffine S] :
    ∃ N : ℕ, ∀ (F : X.Modules) [F.IsQuasicoherent] (p : ℕ), N ≤ p →
      Subsingleton (Cohomology F p)
```

`Cohomology` here is `TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology`, which the pin calls
`Scheme.Modules.Cohomology` under `open TauCeti.AlgebraicGeometry`. The pin's spelling does not
resolve inside `namespace TauCeti`, because `Scheme` resolves to Mathlib's `AlgebraicGeometry.Scheme`
there. So the file opens `_root_.TauCeti.AlgebraicGeometry.Scheme.Modules` instead. The meaning is
unchanged.

## Split plan

### Split 1 (needs nothing first): `feat: uniform vanishing of quasi-coherent cohomology on qcqs schemes`

File: `TauCeti/AlgebraicGeometry/Cohomology/QuasiSeparated.lean` (new, 171 lines). Declarations:

- `TauCeti.AlgebraicGeometry.Scheme.Modules.exists_subsingleton_cohomologyOn_of_le_isAffineOpen`:
  a uniform bound for a quasi-compact open contained in an affine open. It is covered by finitely
  many basic opens, whose nonempty intersections are basic opens and so affine.
- `TauCeti.AlgebraicGeometry.Scheme.Modules.exists_subsingleton_cohomologyOn_of_isCompact`: a
  uniform bound for a quasi-compact open of a quasi-separated scheme. Induction on finite affine
  covers with Mayer–Vietoris, using the bound `max N₁ (N₂ + 1)`.
- `TauCeti.AlgebraicGeometry.Scheme.Modules.exists_subsingleton_cohomology`: the bound on a qcqs
  scheme.
- `TauCeti.QCoh.higherDirectImage_vanishing`: the pinned target.
- `TauCeti.QCoh.higherDirectImage_vanishing_of_isAffineOpen`: the README's sentence that on a
  general base the bound is local on affine opens. For `f` qcqs and `U ⊆ S` an affine open there
  is `N` with `Hᵖ(f⁻¹U, F) = 0` for all quasi-coherent `F` and `p ≥ N`. It applies the pinned
  theorem to `f ∣_ U` and transports along `Scheme.Modules.cohomologyOnOpensRangeIso`
  (`Cohomology/OpenImmersion.lean`), using Mathlib's `isQuasicoherent_restrictFunctor`.

This is the only split. It carries the target's exported theorem. The PR would use
`Roadmap: SchemeAndStackFoundations` and cite §2.6 / `QCoh.higherDirectImage_vanishing`.

## What remains (why `partial`)

The target sentence in the README (§2.6, `qcoh_higherDirectImages`) also asks for the following.
For `f : X → S` qcqs and `F` quasi-coherent:

1. `R^p f_* F` (`TauCeti.AlgebraicGeometry.Scheme.Modules.higherDirectImage f p`, on `main`) is
   quasi-coherent;
2. on an affine open `U ⊆ S`, its sections are `H^p(f⁻¹U, F)`;
3. it commutes with flat base change;
4. it commutes with filtered colimits.

None of these has a pinned Lean form in `Suggested.lean`; the only pinned form is the vanishing
theorem above. Item 1 in degree 0 is exactly what the supplier provides: PR #21787's
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward`, an instance with hypotheses
`[M.IsQuasicoherent] [QuasiCompact f] [QuasiSeparated f]` and conclusion
`((pushforward f).obj M).IsQuasicoherent`. That PR's
`Scheme.Modules.isLocalizedModule_basicOpenRestrict_of_qcqs` is the localization step a
higher-degree version would generalise, to `H^p(f⁻¹ D(g), F) = H^p(f⁻¹U, F)_g`. That is where a
stub of the supplier would be needed. Items 3 and 4 also need the Čech comparison for qcqs schemes
(Stacks 30.6.1 (07TB); flat base change Stacks 30.5).

## Resumption log

- Round 2 (2026-10-29): merged `origin/main` (`ea7e54cf96`) into the branch. The merge had no
  conflicts, `lake build` is green and `lookahead-check` passes. Checked the proof file against
  the rubrics again (placement next to `FiniteCover.lean` and `MayerVietoris.lean`, docstrings,
  Stacks references, pinned name and signature, no unused hypotheses) and found nothing to change.
  `main` still has no `TauCeti.QCoh` namespace and no quasi-coherence result for
  `higherDirectImage`, so items 1–4 under *What remains* are still open.
- Round 3 (2026-10-29): `origin/main` was still `ea7e54cf96`, and PR #21787 is still open. Added
  `QCoh.higherDirectImage_vanishing_of_isAffineOpen` (bound local on affine opens of a general
  base), which still needs no stub. `main` still has no comparison of
  `Scheme.Hom.higherDirectImage` with the sheafification of `V ↦ Hᵖ(f⁻¹V, F)`. That comparison
  is the first missing step for items 1–4, so they remain open.
