<!--tauceti-lookahead:v1 {"area":"DiophantineApproximationAndTranscendence","slug":"waldschmidt-interpolation-rank","main":"52f9d081237dadaf6d4eae13629281f7faa37d54","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: the rank of Waldschmidt's interpolation matrix and the zero estimate"},{"n":2,"after":[],"title":"feat: a multiplicity estimate on the additive group times the torus"},{"n":3,"after":[1,2],"title":"feat: the rank of Waldschmidt's interpolation matrix"}]}-->

# Lookahead: `waldschmidt-interpolation-rank` (partial)

Target: DiophantineApproximationAndTranscendence §3.6, "Rank and multiplicity for the
interpolation matrix" (`waldschmidtInterpolationRank`; W00 §9.2.3, Proposition 9.16, Lemma 9.17;
§9.3.2, Steps 1–2). Built on `main` at `52f9d081237`.

## Stubs

**None.** The supplier `waldschmidt-interpolation-data` is mostly merged already: #21294, #23592
and #23827 landed the normalization, the grid points, the entry identities, the basis changes and
the upper bound on the rank. That material is in
`TauCeti/NumberTheory/Transcendental/Waldschmidt/Interpolation/{Data,Matrix}.lean`, and the target
uses it directly from `main`: `waldschmidtPoint`, `waldschmidtPointMap`, `waldschmidtOperatorEntry`,
`waldschmidtOperatorEntry_eq_sum_hasseDeriv`, `waldschmidtInterpolationMatrix`,
`rank_waldschmidtInterpolationMatrix_le{,_of_mem}`. The two parts of the supplier still open are:

- open PR #27120: denominators of the entries (`mul_waldschmidtEntry_mem`,
  `mul_waldschmidtInterpolationMatrix_mem`, …);
- the denominators of the delta-polynomial rows.

Both are arithmetic and play no part in the rank. The rank is a statement over the coefficient
field, and it does not depend on the choice of basis (the merged `span_image_*` lemmas). So
nothing needs stubbing, there is no `TauCeti/Lookahead/` file, and `suppliers` is empty. The
roadmap's `Suggested.lean` does not pin a signature for `waldschmidtInterpolationRank` (it is only
named in the §3.6 comment block), so the README text is the specification.

## What is proved (split 1, on this branch)

The linear-algebra half of the target, with no `sorry`:

- `TauCeti.rank_waldschmidtInterpolationMatrix_eq_iff_of_mem`. Take the monomial rows
  `z^τ e^{t(z₀+λ₁z₁+⋯)}` with `|τ| ≤ T₀` and `t ∈ T`, and arbitrary columns `(P c, s c)` whose grid
  points lie in a subspace `W ∋ e₀`. Then the rank equals `(T₀ + dim W choose dim W)·#T` **iff**
  the conclusion of the zero estimate holds on `W`: if the combined entries of polynomials `G_t`
  with `deg ≤ T₀` vanish on all columns, then every `G_t` vanishes on `W`. Equivalently, no
  auxiliary polynomial `Σ_t G_t Y^t` that is nonzero on `W × 𝔾ₘ` vanishes at the columns. This is
  an iff, not a hypothesis-bearing one-way lemma: the hard content (the zero estimate) is
  characterized, not assumed.
- `TauCeti.rank_waldschmidtInterpolationMatrix_eq_iff`: the same for column indices `s` in a
  subspace `V` that contains the coefficient vector `(β₁,…,β_{m−1},−1)`. Here
  `W = V·y + K e₀` and the rank is `L_d = (T₀+d choose d)·#T` with `d = dim V`.
- `TauCeti.finrank_map_waldschmidtPointMap_sup` (moved into `Matrix.lean`):
  `dim(V·y + K e₀) = dim V`, proved in both cases `β₀ ≠ 0` and `β₀ = 0`. The proof of `main`'s
  `rank_waldschmidtInterpolationMatrix_le` now uses it and drops ~30 lines of inline argument.
- `TauCeti.exists_waldschmidtResidualSubspace`: the subspace `V ∋ c` of smallest dimension with
  `(d+1)·#π_V(S) ≤ (m+1)T₀^(m−d)` exists, and `d ≥ 1`. These are the README's first two checks.
- General inputs:
  - `MvPolynomial.eval_pderiv_eq_zero_of_forall_eval_add_smul_single` in
    `RingTheory/MvPolynomial/DirectionalOrder.lean`: over an infinite domain, a polynomial that
    vanishes on a coordinate line through `a` has vanishing partial derivative at `a`.
  - `Matrix.eval_aeval_toMvPolynomial` in `RingTheory/MvPolynomial/LinearSubst.lean`:
    substituting the rows of a rectangular matrix gives `x ↦ p(A x)`.

## What remains (splits 2 and 3)

- **Split 2:** the multiplicity estimate on `𝔾ₐᵈ × 𝔾ₘ` (W00 §9.2.3, the "torus/additive-group
  multiplicity argument"). It covers polynomials `Σ_{|t|≤T₁} G_t(w) Y^t` with `deg G_t ≤ T₀`,
  differentiated along `∂/∂w₀ + Y∂/∂Y` up to order `(m+1)S₀` at the points
  `(s·y, α^s)`, `s ∈ ((S−S)∩V)[m+1]`. It must produce an obstruction subgroup when the
  polynomial is nonzero. This is the bulk of the target and is not started on this branch.
- **Split 3 (exports the target):** `waldschmidtInterpolationRank`. Under the README hypotheses:
  - the `α_j` have multiplicative rank `≥ m−1`;
  - `S₀+1 ≥ 2T₀`;
  - `‖s‖∞ < T₀/4`;
  - `(S₀+1)#S > 2(m+1)T₀^m T₁`;
  - `β₀ ≠ 0` or `(S−S)[2] ∩ ℂ(β₁,…,−1) = {0}`.

  For the minimal `V` from `exists_waldschmidtResidualSubspace`, the columns with `σ ≤ (m+1)S₀`
  and `s ∈ ((S−S)∩V)[m+1]` have rank `L_d`. Proof: by split 1 (`…_eq_iff`, direction `←`) it
  suffices to verify the zero-estimate conclusion. Split 2 provides an obstruction subgroup
  otherwise, and the induction on proper `V′` rules it out. That induction contradicts the
  minimality of `V`, uses the subgroup obstruction from the rank of the `α_j`, and reduces a short
  rational coefficient relation by Liouville.

## Splits

1. **feat: the rank of Waldschmidt's interpolation matrix and the zero estimate.** Needs none.
   - Files:
     - `TauCeti/NumberTheory/Transcendental/Waldschmidt/Interpolation/Rank.lean` (new, 252
       lines);
     - `…/Interpolation/Matrix.lean` (adds `finrank_map_waldschmidtPointMap_sup` and simplifies
       `rank_waldschmidtInterpolationMatrix_le`);
     - `TauCeti/RingTheory/MvPolynomial/DirectionalOrder.lean` (+29);
     - `TauCeti/RingTheory/MvPolynomial/LinearSubst.lean` (+19).
   - Declarations: the ones listed above. About 380 added lines.
2. **feat: a multiplicity estimate on the additive group times the torus.** Needs none. Not on
   this branch.
3. **feat: the rank of Waldschmidt's interpolation matrix.** Needs 1 and 2. Carries
   `waldschmidtInterpolationRank`, completes the target. Not on this branch.

## Self-audit notes (rubrics)

- **Correctness.** The main results are iff statements, so the zero estimate is not moved into a
  hypothesis. `[Infinite K]` is needed because "vanishes on `W`" is pointwise; in the application
  `K` is a number field.
- **Reuse.** Uses Mathlib's `Matrix.toMvPolynomial`, `LinearMap.exists_leftInverse_of_injective`
  and `MvPolynomial.funext`, together with Tau Ceti's `aeval_mem_restrictTotalDegree`,
  `finrank_restrictTotalDegree`, `basisRestrictTotalDegree` and `pderiv_aeval`. I found no existing
  lemma for the derivative along a line or for rectangular linear substitution.
- **API.** The two private lemmas in `Rank.lean` serve this file only:
  `eval_iterate_pderiv_zero_eq_zero` and `exists_restrictTotalDegree_linearMap` (restriction of
  bounded-degree polynomials to a subspace, onto, with vanishing kernel). A reviewer may ask to
  make the second public in `RingTheory/MvPolynomial/Finrank.lean`.
