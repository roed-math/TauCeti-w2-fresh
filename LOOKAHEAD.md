<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"qcoh-higher-direct-image-vanishing","main":"45d6c5cf463be69fd00b2dc1dc7e0a397ff2e540","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: uniform vanishing of quasi-coherent cohomology on qcqs schemes"}]}-->

# Lookahead: `qcoh-higher-direct-image-vanishing` (SchemeAndStackFoundations, §2.6)

Built on `main` at `45d6c5cf46`. The target's only pinned Lean form,
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

File: `TauCeti/AlgebraicGeometry/Cohomology/QuasiSeparated.lean` (new, 148 lines). Declarations:

- `TauCeti.AlgebraicGeometry.Scheme.Modules.exists_subsingleton_cohomologyOn_of_le_isAffineOpen`:
  a uniform bound for a quasi-compact open contained in an affine open. It is covered by finitely
  many basic opens, whose nonempty intersections are basic opens and so affine.
- `TauCeti.AlgebraicGeometry.Scheme.Modules.exists_subsingleton_cohomologyOn_of_isCompact`: a
  uniform bound for a quasi-compact open of a quasi-separated scheme. Induction on finite affine
  covers with Mayer–Vietoris, using the bound `max N₁ (N₂ + 1)`.
- `TauCeti.AlgebraicGeometry.Scheme.Modules.exists_subsingleton_cohomology`: the bound on a qcqs
  scheme.
- `TauCeti.QCoh.higherDirectImage_vanishing`: the pinned target.

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
