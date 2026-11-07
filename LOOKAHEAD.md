<!--tauceti-lookahead:v1 {"area":"ModularForms","slug":"automorphy-sheaf","main":"e7068108eef137a393590a3e2a09f9b2dbb8b9e4","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: local sections of the automorphy sheaf from coefficients at elliptic points and cusps"},{"n":2,"after":[1],"title":"feat: the weight-k automorphy presheaf on the compactified quotient as an O-module"},{"n":3,"after":[1,2],"title":"feat: the weight-k automorphy sheaf on X(Γ) is invertible"}]}-->

# Lookahead: `automorphy-sheaf` (ModularForms, Layer 10C) — partial

Target: the induced invertible sheaf on the coarse compact curve `X(Γ)`, built by explicit local
descent — invariant sections in the linearizing coordinate at an elliptic point, sections in the
width parameter (errata order convention) at a regular or irregular cusp.

Built on `main` at `e7068108eef137a393590a3e2a09f9b2dbb8b9e4`.

## Stubs

None yet. The part proved on this branch is the *local* descent at elliptic points and cusps, and it
uses only what `main` already has (the elliptic and cusp halves of the transition-function
milestone, #22437 and #27354, are merged). No declaration of either supplier is consumed so far, so
`TauCeti/Lookahead/AutomorphySheaf/Stubs.lean` has not been created: the brief allows only stubs that
the proof consumes.

* `automorphy-sheaf-transition-functions` (open PR #29133): its diff adds `differentialFrame` and the
  frame comparison against `automorphyFrame` in `Fuchsian/Elliptic/Automorphy.lean` and
  `Fuchsian/Cusp/Automorphy.lean`. The remaining gluing (split 3) will consume the inter-chart
  frame comparisons on overlaps. The open PR does not state them yet, so they are not stubbed.
* `riemann-surface-structure-sheaf-h1` (open PR #29154): its diff adds Čech-degree-one material in
  `TauCeti/Topology/Sheaves/Cech/DegreeOne.lean`, `Cech/LocallyZero.lean` and `Sheaves/Cartan.lean`
  (`subsingleton_H'_one_of_isZero_cechCohomology`, `isZero_cechCohomology_zero_obj_of_locally_eq_zero`).
  Correction (fourth round): split 2 does **not** need this supplier for `𝒪_X`. `main` already
  has the holomorphic structure sheaf `TauCeti.holomorphicStructureSheaf I X` (sheaf of
  commutative rings) and `TauCeti.holomorphicStructureSheafModules I X` (its `ModuleCat ℂ`
  form) in `TauCeti/Geometry/Manifold/Complex/StructureSheaf/Basic.lean`. It also has the complex
  manifold structure on `Γ.CompactifiedQuotient` (`instChartedSpace`, `instIsManifold` in
  `TauCeti/Analysis/Complex/Fuchsian/Compactification/Manifold.lean`). Earlier rounds missed
  both. The supplier's Čech `H¹` is not consumed by the construction of the sheaf itself, so
  nothing from #29154 is stubbed.

`ModularForms/Suggested.lean` pins no declaration for `automorphy-sheaf` itself: it contains only
the cross-roadmap `#check`s and the concrete dimension `example`s.

## What is proved (split 1, complete on the branch, no `sorry`)

The two-sided local trivialization of the weight-`k` automorphy data at each kind of special point.
`main` already proved one direction: every local section is the frame times a holomorphic
coefficient. This split adds the converse and the round trip, so that the local sections are
*exactly* the frame times the holomorphic functions of the local quotient coordinate.

* `TauCeti/Analysis/Complex/Fuchsian/Elliptic/AutomorphySection.lean` (147 lines), namespace
  `Subgroup.LinearizingCoordinate` (as in the neighbouring `Elliptic/Automorphy.lean`):
  `automorphySection`, `automorphySection_def`, `automorphySection_coe`,
  `mdifferentiableOn_automorphySection`, `automorphySection_smul`,
  `eqOn_automorphyDescent_automorphySection` (the coefficient of the section with coefficient
  `G` is `G`), `automorphySection_automorphyDescent` (every local section is the section of its
  coefficient).
* `TauCeti/Analysis/Complex/Fuchsian/Cusp/AutomorphySection.lean` (157 lines), namespace
  `TauCeti.Subgroup.CuspDatum`: `automorphySection`, `automorphySection_def`,
  `mdifferentiableOn_automorphySection`, `automorphySection_smul` (valid on all of `ℍ`, for the
  generator lift with sign condition `ε ^ k = (-1) ^ r`, covering irregular cusps),
  `isBoundedAtImInfty_slash_automorphySection` (the section is bounded at the cusp when `G` is
  continuous there), `eqOn_automorphyDescent_automorphySection` (the coefficient of the section
  with coefficient `G` is `G`, including at `q = 0`), `automorphySection_automorphyDescent`.

## Split plan

1. **feat: local sections of the automorphy sheaf from coefficients at elliptic points and cusps**
   — the two files above, after `[]`. Ready to open now: it needs no supplier.
2. **feat: the weight-k automorphy presheaf on the compactified quotient as an O-module** — after
   `[1]`. Defines the presheaf of local sections on opens of `X(Γ)`: on an open `U`, the functions
   on the preimage in `ℍ` satisfying the weight-`k` law, holomorphic there and bounded (resp.
   meromorphic with the floor-corrected order) at cusps in `U`. It shows this is a sheaf of
   `𝒪_{X(Γ)}`-modules over `holomorphicStructureSheaf 𝓘(ℂ) Γ.CompactifiedQuotient`, which is
   already on `main`. It needs no supplier, so it can be written and opened now.
3. **feat: the weight-k automorphy sheaf on X(Γ) is invertible** — after `[1, 2]`. Uses split 1 at
   every elliptic point and cusp, and the frame `(τ - conj z)^(-k)`-free trivialization at regular
   interior points, to show the sheaf of split 2 is locally free of rank one. The chart-overlap
   transition functions of `automorphy-sheaf-transition-functions` (#29133) identify the
   trivializations. This is the target's exported theorem and the only split that completes it.

## What remains

* Split 2 (the presheaf of weight-`k` sections on opens of `X(Γ)` and its sheaf and
  `𝒪_{X(Γ)}`-module structure). Its inputs are all on `main`: the structure sheaf, the manifold
  structure on `Γ.CompactifiedQuotient`, and split 1.
* Split 3 (local freeness of rank one). It consumes the chart-overlap frame comparisons of
  `automorphy-sheaf-transition-functions`. #29133 does not state them yet, so they are not
  stubbed.

## Round log

* 2026-11-07: merged `main` at `2f06c0d69fd8`. The build is green and `lookahead-check` passes. I
  re-read both supplier PRs: #29133 (head `12250f710b72`) and #29154 are unchanged since
  2026-11-06 and still state neither `𝒪_X` nor the chart-overlap frame comparisons. So there is
  still nothing to stub, and splits 2 and 3 remain open.
* 2026-11-07 (second round): merged `main` at `5f8b5c6fc72`. The build is green. I re-checked both
  supplier PRs: #29133 (head `12250f710b72`) and #29154 (head `529d0b65eb2e`) are still unchanged
  since 2026-11-06. Neither states `𝒪_X` or the chart-overlap frame comparisons, so there is still
  nothing to stub, and splits 2 and 3 remain open.
* 2026-11-07 (third round): merged `main` at `fc8b2141367`. I re-checked both supplier PRs: #29133
  (head `12250f710b72`) and #29154 (head `529d0b65eb2e`) are still unchanged since 2026-11-06, and
  `main` still has no structure sheaf of a Riemann surface. So there is still nothing to stub, and
  splits 2 and 3 remain open.
* 2026-11-07 (fourth round): merged `main` at `e7068108eef`. #29133 (head `12250f710b72`) and
  #29154 (head `529d0b65eb2e`) are still unchanged since 2026-11-06. I corrected the record:
  `main` has the holomorphic structure sheaf (`holomorphicStructureSheaf`,
  `holomorphicStructureSheafModules`) and the complex manifold structure on
  `Γ.CompactifiedQuotient`, so split 2 is not blocked on any supplier. The round was too short to
  write split 2, so the next round should start there.
