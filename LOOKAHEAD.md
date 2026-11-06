<!--tauceti-lookahead:v1 {"area":"ModularForms","slug":"finite-dimensional-h1-structure-sheaf","main":"afa08a3ed16fb167e35de371afb1eb03fbc5913a","status":"partial","suppliers":["riemann-surface-structure-sheaf-h1"],"splits":[{"n":1,"after":[],"title":"feat: Schwartz's theorem on compact perturbations of surjections"},{"n":2,"after":[],"title":"feat: bounded holomorphic maps on a complex manifold and Montel's theorem"},{"n":3,"after":[1,2],"title":"feat: bounded holomorphic Čech cochains and finiteness of bounded H¹"},{"n":4,"after":[],"title":"feat: holomorphic Čech cocycles extend to larger chart discs up to a coboundary"},{"n":5,"after":[3,4],"title":"feat: bounded holomorphic H¹ of a compact Riemann surface is finite dimensional"},{"n":6,"after":[5],"title":"feat: H¹ of the structure sheaf is computed by bounded cocycles on a chart-disc cover"},{"n":7,"after":[1,2,3,4,5,6],"title":"feat: H¹ of the sheaf of a divisor on a compact Riemann surface is finite dimensional"}]}-->

# Lookahead: `finite-dimensional-h1-structure-sheaf` (ModularForms, Layer 10B (ii))

Target: `dim H¹(X, 𝒪_D) < ∞` for a compact Riemann surface `X` and a divisor `D`
(Forster, *Lectures on Riemann Surfaces*, §14). Built on `main` at
`afa08a3ed16fb167e35de371afb1eb03fbc5913a` (re-merged on 2026-11-06, no new commits on `main`;
`lake build` and `lookahead-check` green). Status: **partial**.

**This round (2026-11-06, second session):** the supplier-independent half of Forster 14.9 is
now closed. Split 4 gained the bounds Forster's argument needs (the partition-of-unity
splitting is bounded by the cocycle; the coboundary `η` is bounded on relatively compact
`V i`), and the new split 5 proves that bounded holomorphic cocycles on nested chart-disc covers
`V ⋐ U ⋐ U'` lift (`exists_restrictCocycles_add_d₀Cocycles_eq`), so that **bounded holomorphic
`H¹` of a compact Riemann surface is finite dimensional on an explicit finite chart-disc cover**
(`exists_chart_ball_cover_finiteDimensional_isCompl_range_d₀Cocycles`). What remains is only the
comparison of this bounded `H¹` with the sheaf-theoretic `Ȟ¹` (needs the supplier) and the
induction over divisors.

## Stubs: none

The supplier `riemann-surface-structure-sheaf-h1` (Layer 10B (i)) still pins **no declarations**
that this target consumes. `ModularForms/Suggested.lean` contains no 10B statement (only the final
dimension examples and the `#check`s of the Fuchsian/degree API). Its assigned in-flight PR is now
#29154 (open, self-described as partial): it proves only the generic bridge
`TauCeti.Topology.subsingleton_H'_one_of_isZero_cechCohomology` (`Ȟ¹(W, F) = 0` for the
cover-colimit Čech cohomology ⇒ sheaf `H¹(W, F) = 0`, for `AddCommGrpCat`-valued sheaves). The
other parts it names are also open: #28963 (degree-one Leray comparison
`homologyCechComplexIsoHOne`, `AddCommGrpCat`-valued, under memberwise `H¹(U i, F) = 0`) and
#28407 (Dolbeault sequence and `Ȟ¹(D, 𝒪) = 0` on discs in `ℂ`). The earlier #27339 was closed.
None of these states what the target consumes — the comparison of `Ȟ¹(X, 𝒪_D)` with the Čech
`H¹` of one finite cover by coordinate discs of a Riemann surface, for `ModuleCat ℂ`-valued
sheaves — so stubbing it would still mean inventing its name and statement. No stub file exists
and nothing on the branch uses `sorry`.

**New on `main` since the last round: the target's carrier.** `main` now has the cover-colimit
Čech cohomology `TauCeti.Topology.cechCohomology` (`Topology/Sheaves/Cech/Colimit.lean`) and the
divisor sheaf `TauCeti.RiemannSurface.divisorSheaf D : TopCat.Sheaf (ModuleCat ℂ) (TopCat.of X)`.
This round checked that the exported statement of split 5 elaborates against them, with imports
`TauCeti.Analysis.Complex.RiemannSurface.Divisor.Sheaf` and
`TauCeti.Topology.Sheaves.Cech.Sheafification` (which supplies the `ModuleCat` colimit instances;
with `Cech.Colimit` alone, `HasProducts (ModuleCat ℂ)` synthesis times out):

```lean
{X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X] …
    (D : TauCeti.AlgebraicGeometry.WeilDivisor X) :
  FiniteDimensional ℂ ((TauCeti.Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
    (TauCeti.RiemannSurface.divisorSheaf D).obj)
```

So the final statement needs no stub; only the comparison input of split 5 waits on the supplier.

## What is proved (all sorry-free, `lake build` green)

### `TauCeti/Analysis/Normed/Operator/Compact/FiniteRank.lean` (existing file, +65 lines)

* `IsCompactOperator.exists_finiteDimensional_dist_le`: a compact operator is approximately of
  finite rank (for every `ε > 0` a finite-dimensional `B` and `M` with every `K x` within
  `ε * ‖x‖` of a point of `B` of norm `≤ M * ‖x‖`). The existing theorem of the file is wrapped
  in `section FiniteRange`; the module title is widened.

### `TauCeti/Analysis/Fredholm/SurjectiveCompactPerturbation.lean` (new, 143 lines)

* `ContinuousLinearMap.finiteDimensional_quotient_range_add_of_surjective` (**Schwartz's
  theorem**), `ContinuousLinearMap.isClosed_range_add_of_surjective`,
  `ContinuousLinearMap.finiteDimensional_quotient_range_of_surjective_coprod`,
  `ContinuousLinearMap.isClosed_range_of_surjective_coprod` (Forster 14.8–14.9 in abstract form).

### `TauCeti/Analysis/Normed/Operator/Compact/Pi.lean` (new, 60 lines)

* `IsCompactOperator.pi`, `IsCompactOperator.piMap`.

### `TauCeti/Geometry/Manifold/Complex/BoundedHolomorphic.lean` (new this round, 357 lines)

For a complex manifold `X` modelled by `I : ModelWithCorners ℂ E H` and a complex normed space
`F`:

* `TauCeti.boundedHolomorphicSections I F W : Submodule ℂ (W →ᵇ F)` — `H^∞(W, F)`, bounded
  continuous maps with a holomorphic (`MDifferentiableOn I 𝓘(ℂ, F)`) ambient representative;
  `mem_boundedHolomorphicSections_iff`, `…_iff_of_eqOn`, `…_iff_extend`.
* `TauCeti.boundedHolomorphicSections_modelWithCornersSelf`: on an open set of a normed space it
  *is* `main`'s `TauCeti.boundedHolomorphicFunctions F U` (so the two are not parallel APIs).
* Chart lemmas: `isOpen_extChartAt_target_inter_preimage_symm`,
  `MDifferentiableOn.differentiableOn_comp_extChartAt_symm`,
  `mdifferentiableAt_of_differentiableAt_comp_extChartAt_symm`.
* `TauCeti.isClosed_boundedHolomorphicSections` (`[CompleteSpace F]`, `X` boundaryless,
  `IsManifold I 1 X`): uniform limits are holomorphic (chart reading +
  `TendstoUniformlyOn.differentiableOn` on `main`); hence the `CompleteSpace` instance.
* Namespace `TauCeti.BoundedHolomorphicSections`: `ext`, `of`/`of_apply`, `extend` and its
  lemmas, `restrict` (CLM, norm `≤ 1`, `restrict_refl`, `restrict_comp_restrict`, `restrict_of`),
  the chart **Cauchy estimate** `dist_apply_le_of_ball_subset`, and **Montel**
  `isCompactOperator_restrict` / `isCompactOperator_restrict_of_isCompact_closure`
  (`[ProperSpace F]`; equicontinuity from the chart Cauchy estimate + Arzelà–Ascoli).
* `MDifferentiableOn.exists_forall_norm_le_of_isCompact_closure`: a holomorphic map is bounded on
  any `W'` with compact closure in `W` (to feed unbounded cocycles into `H^∞` in split 5).

### `TauCeti/Geometry/Manifold/Complex/BoundedCechCochains.lean` (new this round, 330 lines)

Namespace `TauCeti.BoundedCech`, for `U V : ι → Opens X`:

* `restrictBCF` (restriction of `W →ᵇ ℂ` to `W' ≤ W`) and `restrictBCF_mem` (keeps holomorphy).
* Ambient cochains `BoundedCochain₀/₁/₂ U` (products of `→ᵇ ℂ` over `Uᵢ`, `Uᵢ ∩ Uⱼ`,
  `Uᵢ ∩ Uⱼ ∩ Uₖ`), coboundaries `d₀`, `d₁` (CLMs) with `d₁_comp_d₀ = 0`.
* Closed subspaces `cochains₀ I U`, `cochains₁ I U`, `cocycles I U` (+ `mem_*_iff`,
  `isClosed_*`, `CompleteSpace` instances), `d₀Cocycles I U : cochains₀ →L cocycles`.
* Restrictions `restrict₀/₁/₂` commuting with `d₀`, `d₁`; `restrictCochains₀`,
  `restrictCocycles`, `restrictCocycles_comp_d₀Cocycles`.
* `isCompactOperator_restrictCocycles`: for finite `ι` and `closure Vᵢ` compact in `Uᵢ`,
  restriction of holomorphic cocycles is compact (Montel on each `Uᵢ ∩ Uⱼ` + `IsCompactOperator.pi`).
* `exists_finiteDimensional_isCompl_range_d₀Cocycles`: **finiteness of bounded `H¹`** — if every
  bounded holomorphic cocycle on `V` is `restrictCocycles ζ + d₀Cocycles η`, the bounded
  coboundaries on `V` have a finite-dimensional complement in the bounded cocycles (split 1).

**Design note for the next round.** The cochain spaces are deliberately subspaces of products
of `→ᵇ ℂ`, not products of the subspaces `boundedHolomorphicSections`: with the latter, a
`Submodule ℂ` of a `Submodule ℂ` of a product of complex submodules defeats instance synthesis
for `AddCommGroup`/`HasQuotient` (it needs to unfold unexposed `Real` instances), and applying
the Schwartz theorem to `cocycles` timed out in `isDefEq`. Reproduced with Mathlib types only
(`T : Submodule ℂ (W →ᵇ ℂ)`, `C : Submodule ℂ (ι → T)`, `B : Submodule ℂ C` fails; a generic
`M` works). The result is stated with a complement (`IsCompl`) rather than a quotient for the
same reason: consumers can transport finiteness to `H¹` through the complement.

### `TauCeti/Geometry/Manifold/PartitionOfUnity/CechSplitting.lean` (new this round, 95 lines)

First ingredient of split 4, the smooth splitting of a cocycle (Forster 14.7, first step). For
a real model `I`, `IsManifold I ∞ M`, `M` Hausdorff and σ-compact, `E` finite-dimensional:

* `TauCeti.SmoothPartitionOfUnity.contMDiffOn_finsum_smul_of_isSubordinate`: for `ρ`
  subordinate to an open cover `U` and `ξ i j` that are `C^n` on `U i ∩ U j`,
  `∑ᶠ k, ρ k • ξ k i` is `C^n` on `U i`.
* `TauCeti.SmoothPartitionOfUnity.eq_finsum_smul_sub_finsum_smul_of_isSubordinate`: under the
  cocycle relation `ξ i j + ξ j k = ξ i k`, `ξ i j = gⱼ - gᵢ` for these sums.
* `TauCeti.SmoothPartitionOfUnity.norm_finsum_smul_le_of_isSubordinate` (this round): the sum
  `∑ᶠ k, ρ k • ξ k i` is bounded by any common bound of the `ξ k i` (a convex combination).
* `TauCeti.exists_contMDiffOn_eq_sub_of_cocycle`: **smooth Čech `1`-cocycles split** —
  `∃ g, (∀ i, ContMDiffOn I 𝓘(ℝ, F) n (g i) (U i)) ∧ (∀ i j, ∀ x ∈ U i ∩ U j, ξ i j x = g j x - g i x) ∧
  ∀ i C, (∀ k, ∀ x ∈ U k ∩ U i, ‖ξ k i x‖ ≤ C) → ∀ x ∈ U i, ‖g i x‖ ≤ C` (the bound is new).

A Riemann surface `X` (`ChartedSpace ℂ X`, `IsManifold 𝓘(ℂ) n X`) is fed in with the real model
`𝓘(ℝ, ℂ)` via `main`'s `IsManifold.restrictScalars` and `ContMDiffOn.restrictScalars`
(`Geometry/Manifold/{IsManifold,ContMDiff}/RestrictScalars.lean`).

**Correction to the previous round.** The Dolbeault lemma is already on `main`
(`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_eball` /
`…_of_ball`, `TauCeti/Analysis/Complex/Wirtinger/DolbeaultLemma.lean`); #28407 only packages it
as the Dolbeault sequence and `Ȟ¹(D, 𝒪) = 0`. So split 4 does **not** wait on any supplier
PR. This round avoids a global `(0,1)`-form (and the chart change of `∂̄`) altogether: on each
chart disc the `∂̄ (gₖ ∘ chart⁻¹)` already agree on overlaps, so the gluing is done in one chart
at a time (below).

### `TauCeti/Analysis/Complex/Wirtinger/DolbeaultLemma.lean` (existing file, +70 lines, new this round)

New section *Smooth data with holomorphic differences* at the end of `main`'s Dolbeault-lemma
file (its canonical home: it is a corollary of the lemma it follows):

* `ContDiffOn.conjWirtingerDeriv_apply_one`: on an open set, `z ↦ \bar∂ g z 1` of a smooth
  `g : ℂ → W` is smooth.
* `TauCeti.exists_contDiffOn_differentiableOn_sub_of_ball`: if `g k` is smooth on open
  `Ω k ⊆ ℂ` covering `ball c R` and every `g k - g l` is holomorphic on `Ω k ∩ Ω l`, some `f`
  smooth on the disc has every `f - g k` holomorphic on `ball c R ∩ Ω k` (glue the `\bar∂ (g k)`,
  which agree on overlaps, and solve with `main`'s Dolbeault lemma). Smoothness is `C^∞`
  (`(⊤ : ℕ∞)`, spelled so because the file opens `ENNReal`): `\bar∂` loses a derivative.

### `TauCeti/Geometry/Manifold/Complex/DolbeaultGluing.lean` (new this round, 158 lines)

For a Riemann surface `X` (`ChartedSpace ℂ X`, `IsManifold 𝓘(ℂ) 1 X`; smoothness for the real
model `𝓘(ℝ, ℂ)` via `main`'s `IsManifold.restrictScalars_of_ne_zero`, holomorphy for `𝓘(ℂ)`):

* `TauCeti.exists_contMDiffOn_mdifferentiableOn_sub_of_chart_ball`: the same gluing on a chart
  disc `(extChartAt 𝓘(ℂ) x₀).source ∩ extChartAt 𝓘(ℂ) x₀ ⁻¹' ball (extChartAt 𝓘(ℂ) x₀ x₀) R`
  (the disc lying in the chart target).
* `TauCeti.exists_mdifferentiableOn_cocycle_eq_add_sub_of_chart_ball` (**Forster 14.7,
  unbounded form**): `X` Hausdorff and σ-compact, `U i` chart discs, `V i ⊆ U i` open covering
  `X`, `ξ` a holomorphic `1`-cocycle on the `V i`. Then there are a holomorphic `1`-cocycle `ζ` on
  the `U i` and holomorphic `η i` on `V i` with `ζ i j = ξ i j + η j - η i` on `V i ∩ V j`.
  Proof: smooth splitting `ξ i j = g j - g i` (`CechSplitting.lean`), the chart-disc gluing on each
  `U i` gives `f i`, and `ζ i j = f j - f i`, `η i = f i - g i`. New this round: a further
  conclusion that `η i` is bounded on `V i` when `closure (V i)` is compact in `U i` and all
  `ξ k i` share a bound (`f i` is continuous on `U i`, `g i` is bounded by the cocycle).

### `TauCeti/Geometry/Manifold/ExtChartAt.lean` (existing file, +45 lines, new this round)

The module docstring gains one sentence for the two lemmas below; in its existing sentence on
precompact chart covers, the word *admit* became *have* (the lookahead check rejects that token
in changed files outside `TauCeti/Lookahead/`; the port may restore it).

* `TauCeti.closure_extChartAt_source_inter_preimage_ball_subset` (`[ProperSpace E] [T2Space M]`):
  the closure of the chart ball of radius `r` lies in the chart ball of radius `r' > r` when
  `ball (extChartAt I x x) r' ⊆ (extChartAt I x).target` (it lies in the compact
  `e.symm '' closedBall`).
* `TauCeti.exists_finset_iUnion_extChartAt_preimage_ball_eq_univ` (`[I.Boundaryless]
  [CompactSpace M]`): radii `R x > 0` with chart balls inside the chart targets, and for any
  `c > 0` a finite set of points whose chart balls of radii `c * R x` cover `M`.

### `TauCeti/Geometry/Manifold/Complex/BoundedCechLifting.lean` (new this round, 166 lines)

For a compact Hausdorff Riemann surface `X` (`ChartedSpace ℂ X`, `IsManifold 𝓘(ℂ) 1 X`), in
namespace `TauCeti.BoundedCech`:

* `exists_restrictCocycles_add_d₀Cocycles_eq` (**Forster 14.7, bounded form**): finite `ι`,
  `U' i` chart discs, `V U : ι → Opens X` with `closure (V i) ⊆ U i`, `closure (U i) ⊆ U' i`,
  `⋃ V = univ`. Every `ξ : cocycles 𝓘(ℂ) V` is `restrictCocycles _ ζ + d₀Cocycles 𝓘(ℂ) V η` with
  `ζ : cocycles 𝓘(ℂ) U`, `η : cochains₀ 𝓘(ℂ) V`. (Zero-extend `ξ`, apply split 4 on the `U'`
  discs, bound `ζ` on `U i ∩ U j` by compact closure, `η` by split 4's new bound.)
* `exists_finiteDimensional_isCompl_range_d₀Cocycles_of_chart_ball`: hence (split 3) the bounded
  coboundaries on `V` have a finite-dimensional complement in the bounded cocycles.
* `exists_chart_ball_cover_finiteDimensional_isCompl_range_d₀Cocycles` (**Forster 14.9 for
  bounded cochains**): a finite set `t`, radii `R`, and chart discs `V i` of radius `4⁻¹ * R i`
  covering `X`, with a finite-dimensional complement of the bounded coboundaries in the bounded
  cocycles on `V` (discs of radii `2⁻¹ * R`, `R` as `U`, `U'`).

This is split 4(a) of the previous plan, now done: it needed no supplier.

## Split plan

`Compact/Pi.lean` (60 lines) is folded into the bounded Čech split, its only consumer.

1. **feat: Schwartz's theorem on compact perturbations of surjections** — `Compact/FiniteRank.lean`
   (+65), `Fredholm/SurjectiveCompactPerturbation.lean` (143). Adds
   `IsCompactOperator.exists_finiteDimensional_dist_le` and the four `ContinuousLinearMap`
   theorems listed above. Needs: none. **On the branch.**
2. **feat: bounded holomorphic maps on a complex manifold and Montel's theorem** —
   `Geometry/Manifold/Complex/BoundedHolomorphic.lean` (357). Adds `boundedHolomorphicSections` and
   the `BoundedHolomorphicSections` namespace listed above. Needs: none. **On the branch.**
3. **feat: bounded holomorphic Čech cochains and finiteness of bounded H¹** —
   `Analysis/Normed/Operator/Compact/Pi.lean` (60) and
   `Geometry/Manifold/Complex/BoundedCechCochains.lean` (330). Adds `IsCompactOperator.pi`,
   `IsCompactOperator.piMap` and the `BoundedCech` namespace listed above. Needs: 1, 2.
   **On the branch.**
4. **feat: holomorphic Čech cocycles extend to larger chart discs up to a coboundary** —
   `Geometry/Manifold/PartitionOfUnity/CechSplitting.lean` (107),
   `Analysis/Complex/Wirtinger/DolbeaultLemma.lean` (+70),
   `Geometry/Manifold/Complex/DolbeaultGluing.lean` (167). Adds the four `CechSplitting`
   theorems, `ContDiffOn.conjWirtingerDeriv_apply_one`,
   `exists_contDiffOn_differentiableOn_sub_of_ball`,
   `exists_contMDiffOn_mdifferentiableOn_sub_of_chart_ball`,
   `exists_mdifferentiableOn_cocycle_eq_add_sub_of_chart_ball` (with the bounds). Needs: none.
   **On the branch.**
5. **feat: bounded holomorphic H¹ of a compact Riemann surface is finite dimensional** —
   `Geometry/Manifold/ExtChartAt.lean` (+45), `Geometry/Manifold/Complex/BoundedCechLifting.lean`
   (166). Adds `closure_extChartAt_source_inter_preimage_ball_subset`,
   `exists_finset_iUnion_extChartAt_preimage_ball_eq_univ`,
   `BoundedCech.exists_restrictCocycles_add_d₀Cocycles_eq`,
   `BoundedCech.exists_finiteDimensional_isCompl_range_d₀Cocycles_of_chart_ball`,
   `BoundedCech.exists_chart_ball_cover_finiteDimensional_isCompl_range_d₀Cocycles`.
   Needs: 3, 4. **On the branch.** (The two `ExtChartAt` lemmas could also go first as their own
   small PR; they are general manifold topology.)
6. **feat: H¹ of the structure sheaf is computed by bounded cocycles on a chart-disc cover** —
   new file, *needs the supplier*. For the cover `V` of split 5 and a smaller concentric cover
   `W ⋐ V` (radii `8⁻¹ * R`): `Ȟ¹(X, 𝒪)` (cover-colimit, `ModuleCat ℂ`) is a quotient of
   `cocycles 𝓘(ℂ) W` modulo the coboundaries — by the supplier's Leray comparison for covers by
   `𝒪`-acyclic discs, and boundedness of holomorphic cochains on `W ⋐ V` (restrict with
   `MDifferentiableOn.exists_forall_norm_le_of_isCompact_closure`, split 2). Combined with
   split 5 (applied to `W ⋐ V ⋐ U` instead), `dim Ȟ¹(X, 𝒪) < ∞`. Needs: 5 and the supplier.
7. **feat: H¹ of the sheaf of a divisor on a compact Riemann surface is finite dimensional** —
   the exported theorem, `FiniteDimensional ℂ` of
   `(TauCeti.Topology.cechCohomology (TopCat.of X) (ModuleCat ℂ) 1).obj (divisorSheaf D).obj`
   (statement checked above; name to follow the supplier's final `H¹` naming).
   `D = 0` from split 6; general `D` by induction along `0 → 𝒪_D → 𝒪_{D+P} → ℂ_P → 0`
   (`divisorSheafMapOfLE` on `main`) and the long exact Čech sequence
   (`Topology/Sheaves/Cech/Sheafification.lean`, `CategoryTheory/.../Cech/LongExactSequence.lean`).
   Needs: 1–6.

## What remains

Splits 6–7. Everything not involving sheaf cohomology is proved: finiteness of bounded
holomorphic `H¹` on an explicit finite chart-disc cover of a compact Riemann surface (split 5).
Split 6 waits for the supplier `riemann-surface-structure-sheaf-h1` to land the degree-one
Leray comparison for finite covers by coordinate discs of a Riemann surface with `ModuleCat ℂ`
coefficients (its parts #28963, #28407, #29154 are open as of 2026-11-06; #29154 states only
`subsingleton_H'_one_of_isZero_cechCohomology`, and nothing pins the disc-cover comparison, so
there is still nothing to stub). Split 7's statement is already expressible on `main`.
