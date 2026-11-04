<!--tauceti-lookahead:v1 {"area":"ModularForms","slug":"finite-dimensional-h1-structure-sheaf","main":"52f9d081237dadaf6d4eae13629281f7faa37d54","status":"partial","suppliers":["riemann-surface-structure-sheaf-h1"],"splits":[{"n":1,"after":[],"title":"feat: Schwartz's theorem on compact perturbations of surjections"},{"n":2,"after":[],"title":"feat: compact operators into finite products"},{"n":3,"after":[2],"title":"feat: bounded holomorphic Čech cochains on a compact Riemann surface"},{"n":4,"after":[3],"title":"feat: bounded cocycles on nested covers compute H¹ of the structure sheaf"},{"n":5,"after":[1,2,3,4],"title":"feat: H¹ of the sheaf of a divisor on a compact Riemann surface is finite dimensional"}]}-->

# Lookahead: `finite-dimensional-h1-structure-sheaf` (ModularForms, Layer 10B (ii))

Target: `dim H¹(X, 𝒪_D) < ∞` for a compact Riemann surface `X` and a divisor `D`
(Forster, *Lectures on Riemann Surfaces*, §14). Built on `main` at
`52f9d081237dadaf6d4eae13629281f7faa37d54`. Status: **partial**.

## Stubs: none

The supplier `riemann-surface-structure-sheaf-h1` (Layer 10B (i)) pins **no declarations**:
`ModularForms/Suggested.lean` contains no 10B statement at all (only the final dimension
examples and the `#check`s of the Fuchsian/degree API), and its in-flight PR #27339
("the Dolbeault lemma on discs") states only the local `∂̄`-lemma
(`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_eball` and corollaries), which the
PR itself describes as partial. The objects the target's final statement needs — Čech `H¹(X, 𝒪_D)`
of the divisor sheaf `TauCeti.RiemannSurface.divisorSheaf D` (on `main`), its refinement
independence, and Forster's Leray theorem 12.8 — are pinned neither in `Suggested.lean` nor in
any PR diff, so stubbing them would mean inventing their names and statements.

This round therefore proves the part of the target that does not consume the supplier: the
functional-analytic core of §14 ("the open-mapping theorem for a uniform lifting estimate, and
iteration"), in the abstract form in which the cohomological argument will call it. No stub file
exists and nothing on the branch uses `sorry`. The supplier is still listed in the header because
splits 4–5 cannot be written until it lands.

## What is proved (all sorry-free, `lake build` green)

### `TauCeti/Analysis/Normed/Operator/Compact/FiniteRank.lean` (existing file, +64 lines)

* `IsCompactOperator.exists_finiteDimensional_dist_le`: a compact operator `K : E →L[𝕜] F`
  between seminormed spaces is approximately of finite rank — for every `ε > 0` there are a
  finite-dimensional `B : Submodule 𝕜 F` and `M` with every `K x` within `ε * ‖x‖` of a point of
  `B` of norm `≤ M * ‖x‖`. (The existing theorem of the file, finite rank ⇒ compact, is wrapped in
  `section FiniteRange` so the two variable blocks do not clash; the module title is widened.)

### `TauCeti/Analysis/Fredholm/SurjectiveCompactPerturbation.lean` (new, 143 lines)

* `ContinuousLinearMap.finiteDimensional_quotient_range_add_of_surjective`: **Schwartz's theorem**:
  `T` surjective, `K` compact between Banach spaces ⇒ `F ⧸ range (T + K)` finite dimensional.
  Proof: open mapping (`ContinuousLinearMap.exists_preimage_norm_le`) + the approximation above
  give approximate preimages under `(x, b) ↦ (T + K) x + b` on `E × B`; Tau Ceti's
  `ContinuousLinearMap.exists_preimage_norm_le_of_approx` iterates them (Forster 14.9's
  iteration).
* `ContinuousLinearMap.isClosed_range_add_of_surjective`: the range of `T + K` is closed.
* `ContinuousLinearMap.finiteDimensional_quotient_range_of_surjective_coprod`: if
  `(g, e) ↦ r g + δ e` is surjective and `r` is compact, `F ⧸ range δ` is finite dimensional —
  the exact shape of Forster 14.8–14.9 with `δ` the Čech coboundary on the small cover and `r`
  restriction of cocycles from the larger cover.
* `ContinuousLinearMap.isClosed_range_of_surjective_coprod`: `range δ` is then closed.

### `TauCeti/Analysis/Normed/Operator/Compact/Pi.lean` (new, 60 lines)

* `IsCompactOperator.pi`, `IsCompactOperator.piMap`: maps into finite products with compact
  components, and finite products of compact operators, are compact. Restriction of Čech cochains
  over a finite cover to a relatively compact refinement is such a product of Montel restrictions
  (`TauCeti.BoundedHolomorphicFunctions.isCompactOperator_restrict`, on `main`).

## Split plan

1. **feat: Schwartz's theorem on compact perturbations of surjections** — files
   `Compact/FiniteRank.lean` (+64) and `Fredholm/SurjectiveCompactPerturbation.lean` (143);
   adds `IsCompactOperator.exists_finiteDimensional_dist_le` and the four
   `ContinuousLinearMap` theorems above. Needs: none. **On the branch.**
2. **feat: compact operators into finite products** — `Compact/Pi.lean` (60); adds
   `IsCompactOperator.pi`, `IsCompactOperator.piMap`. Needs: none. **On the branch.** (Small; if
   reviewers prefer, fold it into split 3, its first consumer.)
3. **feat: bounded holomorphic Čech cochains on a compact Riemann surface** — *not yet written*.
   The Banach space `H^∞(W)` of bounded holomorphic functions on an open `W` of a Riemann surface
   (closed in `W →ᵇ ℂ`: uniform limits are holomorphic, read in charts), Montel compactness of
   restriction `W' ⋐ W` (Cauchy estimates in charts + Arzelà–Ascoli, as in
   `BoundedHolomorphicFunctions.isCompactOperator_restrict`), and for a finite family of opens the
   cochain spaces `C⁰_b = Π_i H^∞(U_i)`, `C¹_b = Π_{i,j} H^∞(U_i ∩ U_j)`, the closed subspace
   `Z¹_b`, the coboundary `δ : C⁰_b →L Z¹_b` and compact restriction `Z¹_b(𝔘) →L Z¹_b(𝔙)` for
   `𝔙 ⋐ 𝔘` (via split 2). Needs: 2. Supplier-independent; next thing to write.
4. **feat: bounded cocycles on nested covers compute H¹ of the structure sheaf** — *needs the
   supplier*. For finite covers `𝔚 ⋐ 𝔙 ⋐ 𝔘` by coordinate discs: every cocycle on `𝔚` is
   cohomologous to the restriction of a bounded cocycle on `𝔙` (Forster 14.7, using `H¹(disc, 𝒪) = 0`
   from the Dolbeault lemma of #27339 and Leray 12.8), i.e. `(ζ, η) ↦ ζ|𝔚 + δη` is onto
   `Z¹_b(𝔚)`; and `H¹(X, 𝒪) ≅ Z¹(𝔚)/δC⁰(𝔚)` with bounded representatives. Needs: 3 and the
   supplier's Čech `H¹(X, 𝒪_D)` + Leray theorem.
5. **feat: H¹ of the sheaf of a divisor on a compact Riemann surface is finite dimensional** — the
   exported theorem (`FiniteDimensional ℂ` of the supplier's `H¹(X, 𝒪_D)`; name to follow the
   supplier's `H¹` declaration). `D = 0` from split 4 +
   `ContinuousLinearMap.finiteDimensional_quotient_range_of_surjective_coprod` (split 1) with
   `r` = compact restriction (split 3); general `D` by induction on `D` along
   `0 → 𝒪_D → 𝒪_{D+P} → ℂ_P → 0` (`dim H¹(𝒪_D) ≤ 1 + dim H¹(𝒪_{D+P})`,
   `dim H¹(𝒪_{D+P}) ≤ dim H¹(𝒪_D)`), or directly by the same argument on twisted local frames.
   Needs: 1, 2, 3, 4.

## What remains

Splits 3–5. Split 3 can be written now; splits 4–5 wait for the supplier
`riemann-surface-structure-sheaf-h1` to pin and land Čech `H¹(X, 𝒪_D)` (refinement-independent)
and the degree-one Leray theorem; PR #27339 (Dolbeault lemma) is one of its parts.
