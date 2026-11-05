<!--tauceti-lookahead:v1 {"area":"ModularForms","slug":"finite-dimensional-h1-structure-sheaf","main":"e8758b7b2f82b9b1c3f33b992ab8f499b510240f","status":"partial","suppliers":["riemann-surface-structure-sheaf-h1"],"splits":[{"n":1,"after":[],"title":"feat: Schwartz's theorem on compact perturbations of surjections"},{"n":2,"after":[],"title":"feat: compact operators into finite products"},{"n":3,"after":[],"title":"feat: bounded holomorphic maps on a complex manifold and Montel's theorem"},{"n":4,"after":[1,2,3],"title":"feat: bounded holomorphic Čech cochains and finiteness of bounded H¹"},{"n":5,"after":[4],"title":"feat: bounded cocycles on nested disc covers lift and compute H¹ of the structure sheaf"},{"n":6,"after":[1,2,3,4,5],"title":"feat: H¹ of the sheaf of a divisor on a compact Riemann surface is finite dimensional"}]}-->

# Lookahead: `finite-dimensional-h1-structure-sheaf` (ModularForms, Layer 10B (ii))

Target: `dim H¹(X, 𝒪_D) < ∞` for a compact Riemann surface `X` and a divisor `D`
(Forster, *Lectures on Riemann Surfaces*, §14). Built on `main` at
`e8758b7b2f82b9b1c3f33b992ab8f499b510240f`. Status: **partial**.

## Stubs: none

The supplier `riemann-surface-structure-sheaf-h1` (Layer 10B (i)) still pins **no declarations**:
`ModularForms/Suggested.lean` contains no 10B statement (only the final dimension examples and
the `#check`s of the Fuchsian/degree API). Its in-flight PR #27339 ("the Dolbeault lemma on
discs", still open) states only the local `∂̄`-lemma
(`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_eball` and corollaries on balls
and closed balls in `ℂ`), which the PR describes as partial. The objects the target's final
statement needs — Čech `H¹(X, 𝒪_D)` of the divisor sheaf `TauCeti.RiemannSurface.divisorSheaf D`
(on `main`), its refinement independence, and Forster's Leray theorem 12.8 — are pinned neither
in `Suggested.lean` nor in any PR diff, so stubbing them would mean inventing their names and
statements. No stub file exists and nothing on the branch uses `sorry`.

Everything proved so far is the supplier-independent part of §14: the functional analysis
(splits 1–2), the Banach spaces of bounded holomorphic functions on a complex manifold with
Montel's theorem (split 3), and the bounded Čech complex with the finiteness reduction (split 4).
The supplier is listed in the header because splits 5–6 cannot be written until it lands.

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
  restriction of holomorphic cocycles is compact (Montel on each `Uᵢ ∩ Uⱼ` + split 2).
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

## Split plan

1. **feat: Schwartz's theorem on compact perturbations of surjections** — `Compact/FiniteRank.lean`
   (+65), `Fredholm/SurjectiveCompactPerturbation.lean` (143). Needs: none. **On the branch.**
2. **feat: compact operators into finite products** — `Compact/Pi.lean` (60). Needs: none.
   **On the branch.** (Small; can be folded into split 4, its only consumer.)
3. **feat: bounded holomorphic maps on a complex manifold and Montel's theorem** —
   `Geometry/Manifold/Complex/BoundedHolomorphic.lean` (357). Needs: none. **On the branch.**
4. **feat: bounded holomorphic Čech cochains and finiteness of bounded H¹** —
   `Geometry/Manifold/Complex/BoundedCechCochains.lean` (330). Needs: 1, 2, 3. **On the
   branch.**
5. **feat: bounded cocycles on nested disc covers lift and compute H¹ of the structure sheaf** —
   *needs the supplier*. Forster 14.7/14.8 for finite covers `𝔚 ⋐ 𝔙 ⋐ 𝔘*` of compact `X` by
   coordinate discs: (a) every `ξ ∈ cocycles I 𝔙` is `restrictCocycles ζ + d₀Cocycles η` with
   `ζ ∈ cocycles I 𝔘` — split `ξ` by a smooth partition of unity (`ξᵢⱼ = gⱼ - gᵢ`), glue the
   `∂̄gᵢ` in each chart, solve `∂̄fᵢ = ω` on a larger disc with the Dolbeault lemma of #27339
   (bounded on the smaller disc), and take `ζᵢⱼ = fⱼ - fᵢ`, `η = fᵢ - gᵢ`; (b) the supplier's
   Čech `H¹(X, 𝒪)` is a quotient of the bounded cocycles on `𝔚` (Leray for disc covers;
   `MDifferentiableOn.exists_forall_norm_le_of_isCompact_closure` makes restricted cocycles
   bounded). Needs: 4 and the supplier's Čech `H¹(X, 𝒪_D)` + Leray theorem + Dolbeault lemma.
6. **feat: H¹ of the sheaf of a divisor on a compact Riemann surface is finite dimensional** —
   the exported theorem (`FiniteDimensional ℂ` of the supplier's `H¹(X, 𝒪_D)`; name to follow the
   supplier's `H¹` declaration). `D = 0` from split 5(b) and
   `exists_finiteDimensional_isCompl_range_d₀Cocycles` (split 4) fed by split 5(a); general `D` by
   induction along `0 → 𝒪_D → 𝒪_{D+P} → ℂ_P → 0`. Needs: 1, 2, 3, 4, 5.

## What remains

Splits 5–6. Both wait for the supplier `riemann-surface-structure-sheaf-h1` to pin and land Čech
`H¹(X, 𝒪_D)` (refinement-independent) and the degree-one Leray theorem; PR #27339 (Dolbeault
lemma, open) is one of its parts. Split 5(a) needs only #27339 plus smooth partitions of unity
on `X` and the transformation of `∂̄` under holomorphic chart changes, so once #27339 lands it can
be written before the `H¹` API is pinned.
