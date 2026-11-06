<!--tauceti-lookahead:v1 {"area":"ModularForms","slug":"finite-dimensional-h1-structure-sheaf","main":"afa08a3ed16fb167e35de371afb1eb03fbc5913a","status":"partial","suppliers":["riemann-surface-structure-sheaf-h1"],"splits":[{"n":1,"after":[],"title":"feat: Schwartz's theorem on compact perturbations of surjections"},{"n":2,"after":[],"title":"feat: bounded holomorphic maps on a complex manifold and Montel's theorem"},{"n":3,"after":[1,2],"title":"feat: bounded holomorphic Čech cochains and finiteness of bounded H¹"},{"n":4,"after":[3],"title":"feat: bounded cocycles on nested disc covers lift and compute H¹ of the structure sheaf"},{"n":5,"after":[1,2,3,4],"title":"feat: H¹ of the sheaf of a divisor on a compact Riemann surface is finite dimensional"}]}-->

# Lookahead: `finite-dimensional-h1-structure-sheaf` (ModularForms, Layer 10B (ii))

Target: `dim H¹(X, 𝒪_D) < ∞` for a compact Riemann surface `X` and a divisor `D`
(Forster, *Lectures on Riemann Surfaces*, §14). Built on `main` at
`afa08a3ed16fb167e35de371afb1eb03fbc5913a` (re-merged this round; `lake build` and
`lookahead-check` green). Status: **partial**.

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

So the final statement needs no stub; only the comparison input of split 4 waits on the supplier.

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
  any `W'` with compact closure in `W` (to feed unbounded cocycles into `H^∞` in split 4).

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

First ingredient of split 4(a), the smooth splitting of a cocycle (Forster 14.7, first step). For
a real model `I`, `IsManifold I ∞ M`, `M` Hausdorff and σ-compact, `E` finite-dimensional:

* `TauCeti.SmoothPartitionOfUnity.contMDiffOn_finsum_smul_of_isSubordinate`: for `ρ`
  subordinate to an open cover `U` and `ξ i j` that are `C^n` on `U i ∩ U j`,
  `∑ᶠ k, ρ k • ξ k i` is `C^n` on `U i`.
* `TauCeti.SmoothPartitionOfUnity.eq_finsum_smul_sub_finsum_smul_of_isSubordinate`: under the
  cocycle relation `ξ i j + ξ j k = ξ i k`, `ξ i j = gⱼ - gᵢ` for these sums.
* `TauCeti.exists_contMDiffOn_eq_sub_of_cocycle`: **smooth Čech `1`-cocycles split** —
  `∃ g, (∀ i, ContMDiffOn I 𝓘(ℝ, F) n (g i) (U i)) ∧ ∀ i j, ∀ x ∈ U i ∩ U j, ξ i j x = g j x - g i x`.

A Riemann surface `X` (`ChartedSpace ℂ X`, `IsManifold 𝓘(ℂ) n X`) is fed in with the real model
`𝓘(ℝ, ℂ)` via `main`'s `IsManifold.restrictScalars` and `ContMDiffOn.restrictScalars`
(`Geometry/Manifold/{IsManifold,ContMDiff}/RestrictScalars.lean`).

**Correction to the previous round.** The Dolbeault lemma is already on `main`
(`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_eball` /
`…_of_ball`, `TauCeti/Analysis/Complex/Wirtinger/DolbeaultLemma.lean`); #28407 only packages it
as the Dolbeault sequence and `Ȟ¹(D, 𝒪) = 0`. So split 4(a) does **not** wait on any supplier
PR: what it still needs is the chart gluing of `∂̄gᵢ` into a global `(0,1)`-datum (on overlaps
`∂̄gᵢ = ∂̄gⱼ` because `gⱼ - gᵢ = ξᵢⱼ` is holomorphic), then the Dolbeault lemma on a larger disc
in each chart and the boundedness lemma of split 2.

## Split plan

`Compact/Pi.lean` (60 lines, previously its own split) is folded into the bounded Čech split, its
only consumer, so no split is a 60-line PR.

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
4. **feat: bounded cocycles on nested disc covers lift and compute H¹ of the structure sheaf** —
   `Geometry/Manifold/PartitionOfUnity/CechSplitting.lean` (95, **on the branch**) plus the rest;
   part (b) *needs the supplier*. Forster 14.7/14.8 for finite covers `𝔚 ⋐ 𝔙 ⋐ 𝔘*` of compact `X` by
   coordinate discs: (a) every `ξ ∈ cocycles I 𝔙` is `restrictCocycles ζ + d₀Cocycles η` with
   `ζ ∈ cocycles I 𝔘` — split `ξ` by a smooth partition of unity (`ξᵢⱼ = gⱼ - gᵢ`; `main`'s
   `Geometry/Manifold/Sheaf/Smooth/Cech.lean` has the smooth-sheaf contracting homotopy), glue the
   `∂̄gᵢ` in each chart, solve `∂̄fᵢ = ω` on a larger disc with the Dolbeault lemma of #28407
   (bounded on the smaller disc), and take `ζᵢⱼ = fⱼ - fᵢ`, `η = fᵢ - gᵢ`; (b) the cover-colimit
   `Ȟ¹(X, 𝒪)` on `main` is a quotient of the bounded cocycles on `𝔚` (Leray for disc covers;
   `MDifferentiableOn.exists_forall_norm_le_of_isCompact_closure` makes restricted cocycles
   bounded). Needs: 3 and the supplier's Leray comparison for disc covers (#28963 + #28407 + the
   passage to coordinate discs and `ModuleCat ℂ` coefficients).
5. **feat: H¹ of the sheaf of a divisor on a compact Riemann surface is finite dimensional** —
   the exported theorem, `FiniteDimensional ℂ` of
   `(TauCeti.Topology.cechCohomology (TopCat.of X) (ModuleCat ℂ) 1).obj (divisorSheaf D).obj`
   (statement checked above; name to follow the supplier's final `H¹` naming).
   `D = 0` from split 4(b) and `exists_finiteDimensional_isCompl_range_d₀Cocycles` (split 3) fed
   by split 4(a); general `D` by induction along `0 → 𝒪_D → 𝒪_{D+P} → ℂ_P → 0`
   (`divisorSheafMapOfLE` on `main`) and the long exact Čech sequence
   (`Topology/Sheaves/Cech/Sheafification.lean`, `CategoryTheory/.../Cech/LongExactSequence.lean`).
   Needs: 1, 2, 3, 4.

## What remains

Splits 4–5 (split 4's smooth cocycle splitting is on the branch). Split 4(b) waits for the supplier `riemann-surface-structure-sheaf-h1` to land the
degree-one Leray comparison for finite covers by coordinate discs of a Riemann surface (its
parts #28963, #28407, #29154 are open, none pins that statement). Split 4(a) needs no
supplier: the Dolbeault lemma on discs is on `main` and the partition-of-unity splitting is on
the branch; it remains to glue `∂̄gᵢ` across charts (chart change of `∂̄` for holomorphic
transition maps), solve on each disc, and bound on the smaller disc. Split 5's statement is
already expressible on `main`.
