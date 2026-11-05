<!--tauceti-lookahead:v1 {"area":"DiophantineApproximationAndTranscendence","slug":"waldschmidt-interpolation-rank","main":"e8758b7b2f82b9b1c3f33b992ab8f499b510240f","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: subspaces spanned by Waldschmidt's grid points"},{"n":2,"after":[1],"title":"feat: the rank of Waldschmidt's interpolation matrix and the zero estimate"},{"n":3,"after":[1],"title":"feat: the residual subspace of Waldschmidt's rank argument"},{"n":4,"after":[],"title":"feat: a multiplicity estimate on the additive group times the torus"},{"n":5,"after":[1,2,3,4],"title":"feat: the rank of Waldschmidt's interpolation matrix"}]}-->

# Lookahead: `waldschmidt-interpolation-rank` (partial)

Target: DiophantineApproximationAndTranscendence §3.6, "Rank and multiplicity for the
interpolation matrix" (`waldschmidtInterpolationRank`; W00 §9.2.3, Proposition 9.16, Lemma 9.17;
§9.3.2, Steps 1–2). Built on `main` at `e8758b7b2f8`. This round resumed the branch at
`bcb3693e6d7` and merged `main` into it. It then added the counting half of the induction on
proper subspaces and the translation between index subspaces and grid-point subspaces.

## Stubs

**None.** Most of the supplier `waldschmidt-interpolation-data` has already merged: #21294,
#23592 and #23827 landed the normalization, the grid points, the entry identities, the basis
changes and the upper bound on the rank. That material is in
`TauCeti/NumberTheory/Transcendental/Waldschmidt/Interpolation/{Data,Matrix}.lean`. The target
uses the following from `main` directly: `waldschmidtPoint`, `waldschmidtPointMap`,
`waldschmidtPointMap_snoc`, `waldschmidtOperatorEntry`,
`waldschmidtOperatorEntry_eq_sum_hasseDeriv`, `waldschmidtInterpolationMatrix` and
`rank_waldschmidtInterpolationMatrix_le{,_of_mem}`.

Two parts of the supplier are still open:

- open PR #27120, the denominators of the entries (`mul_waldschmidtEntry_mem`,
  `mul_waldschmidtInterpolationMatrix_mem`, …);
- the denominators of the delta-polynomial rows.

Both are arithmetic and play no part in the rank. The rank is a statement over the coefficient
field. It does not depend on the choice of basis (the merged `span_image_*` lemmas). So nothing
needs stubbing, there is no `TauCeti/Lookahead/` file, and `suppliers` is empty. The roadmap's
`Suggested.lean` pins no signature for `waldschmidtInterpolationRank`: it is only named in the §3.6
comment block. The README text is therefore the specification.

## What is proved on this branch (splits 1–3, no `sorry`)

Throughout, `c = (β₁, …, β_{m-1}, -1)` is the coefficient vector
(`Fin.snoc (fun k ↦ b k.succ) (-1)`), `Y : v ↦ v · y` is the grid point map
`waldschmidtPointMap b`, and `e₀ = Pi.single 0 1`.

**Split 1: subspaces spanned by the grid points.** In `Interpolation/Data.lean`, section
`PointMap`, over any commutative ring:

- `eq_neg_smul_snoc_of_waldschmidtPointMap_mem`: `Y v ∈ R e₀ → v = -v_m • c`.
- `comap_waldschmidtPointMap_span_single`: `Y⁻¹(R e₀) = R c`.
- `comap_waldschmidtPointMap_map_sup`: if `c ∈ V`, then `Y⁻¹(Y(V) + R e₀) = V`.
- `exists_eq_map_waldschmidtPointMap_sup`: if `c ∈ V` and `e₀ ∈ W' ≤ Y(V) + R e₀`, then
  `W' = Y(V') + R e₀` for some `V' ≤ V` with `c ∈ V'`.

New section `FinrankPointMap`, over a field:

- `finrank_map_waldschmidtPointMap_sup`: `dim(Y(V) + K e₀) = dim V` for `c ∈ V`. It moved here
  from `Matrix.lean` and now uses `eq_neg_smul_snoc_of_waldschmidtPointMap_mem`.

`main`'s `rank_waldschmidtInterpolationMatrix_le` in `Matrix.lean` now uses it, which drops about
30 lines of inline argument.

**Split 2: the rank and the zero estimate.** In `Interpolation/Rank.lean`, with `[Infinite K]`:

- `rank_waldschmidtInterpolationMatrix_eq_iff_of_mem`. Take the monomial rows `z^τ e^{t(z₀+⋯)}`
  with `|τ| ≤ T₀` and `t ∈ T`, and columns whose grid points lie in `W ∋ e₀`. Then the rank equals
  `(T₀ + dim W choose dim W)·#T` **iff** the conclusion of the zero estimate holds on `W`: families
  `(G_t)` of degree `≤ T₀` whose combined entries vanish on all columns vanish on `W`. This is an
  iff, so the zero estimate is characterized, not assumed.
- `rank_waldschmidtInterpolationMatrix_eq_iff`: the same for indices in `V ∋ c`, with
  `W = Y(V) + K e₀` and rank `L_d = (T₀+d choose d)·#T`, `d = dim V`.

General inputs:

- `MvPolynomial.eval_pderiv_eq_zero_of_forall_eval_add_smul_single`, in
  `RingTheory/MvPolynomial/DirectionalOrder.lean`;
- `Matrix.eval_aeval_toMvPolynomial`, in `RingTheory/MvPolynomial/LinearSubst.lean`.

**Split 3: the residual subspace and the counting on proper subspaces.**

General lemma, in the new file `Combinatorics/Additive/ImageCard.lean`:

- `AddMonoidHom.ncard_image_le_mul_ncard_image_sub_inter_ker`:
  `#f(S) ≤ #g(S) · #f((S − S) ∩ ker g)` for a finite `S` and additive homomorphisms `f`, `g`.

In the new file `Interpolation/Residual.lean`:

- `exists_waldschmidtResidualSubspace` (moved from `Rank.lean`): the subspace `V ∋ c` of
  smallest dimension `d` with `(d+1)·#π_V(S) ≤ (m+1)T₀^(m−d)` exists, and `d ≥ 1`. These are the
  README's first two checks.
- `mul_pow_lt_mul_ncard_image_mkQ_sub_inter`: for such a minimal `V` and every `V' ∋ c` with
  `d' = dim V' < d`, `(d+1)·T₀^(d−d') < (d'+1)·#π_{V'}((S−S) ∩ V)`. Minimality makes `V'` violate
  the inequality, and the fibres of `π_V` on `S` compare the two counts.
- `mul_pow_lt_mul_ncard_image_mkQ_nsmul`: the same bound for the column indices
  `((S−S) ∩ V)[k]`, `k ≥ 1` (the target uses `k = m+1`).
- `ncard_image_mkQ_waldschmidtPoint`: for `c ∈ V'`, the grid points of a set of indices have as
  many classes modulo `Y(V') + K e₀` as the indices have modulo `V'`.
- `mul_pow_lt_mul_ncard_image_mkQ_waldschmidtPoint`: for a minimal `V` and every proper
  `W' ⊊ Y(V) + K e₀` with `e₀ ∈ W'` and `d' = dim W'`,
  `(d+1)·T₀^(d−d') < (d'+1)·#π_{W'}(((S−S) ∩ V)[k] · y)`. This is the lower bound that the
  induction on proper subspaces sets against an obstruction subgroup `W' × 𝔾ₘ` of the zero
  estimate. The README's check "a grid lying on a proper coefficient subspace requires passage to
  V" is what makes these counts the right ones.

## What remains (splits 4 and 5)

- **Split 4: the multiplicity estimate on `𝔾ₐᵈ × 𝔾ₘ`** (W00 §9.2.3, the README's
  "torus/additive-group multiplicity argument"). Take `P(w, Y) = Σ_{t∈T} G_t(w) Y^t` on `W × 𝔾ₘ`
  with `deg G_t ≤ T₀`. Assume `P` vanishes along `D = ∂/∂w₀ + Y∂/∂Y` to order `> (m+1)S₀` at the
  points `(s·y, α^s)`, `s ∈ ((S−S) ∩ V)[m+1]`. If `P` is nonzero on `W × 𝔾ₘ`, the estimate must
  produce an obstruction subgroup `W' × 𝔾ₘ` or `W' × {1}` with a degree inequality. This is
  Philippon's zero estimate specialised to one multiplicative factor. It needs multiplicity and
  intersection or Hilbert-function theory on `W × 𝔾ₘ` that is not in Mathlib or on `main`. It is
  the bulk of the target and is not started. An elementary route does not seem to exist: even for
  `d = 1` it is a Bézout count on `𝔾ₐ × 𝔾ₘ` with intersection multiplicities along `D`.
- **Split 5 (exports the target): `waldschmidtInterpolationRank`.** Its hypotheses are:
  - the `α_j` have multiplicative rank `≥ m−1`;
  - `S₀+1 ≥ 2T₀`;
  - `‖s‖∞ < T₀/4`;
  - `(S₀+1)#S > 2(m+1)T₀^m T₁`;
  - `β₀ ≠ 0` or `(S−S)[2] ∩ ℂc = {0}`.

  Its conclusion: for the minimal `V` of `exists_waldschmidtResidualSubspace`, the columns with
  `σ ≤ (m+1)S₀` and `s ∈ ((S−S) ∩ V)[m+1]` have rank `L_d`. Proof outline:
  1. By split 2 (`rank_waldschmidtInterpolationMatrix_eq_iff`, direction `←`), it suffices to
     check the zero-estimate conclusion on `W = Y(V) + K e₀`.
  2. Otherwise split 4 gives an obstruction subgroup.
  3. An obstruction `W' × 𝔾ₘ` with `e₀ ∈ W'` is ruled out by
     `mul_pow_lt_mul_ncard_image_mkQ_waldschmidtPoint` (split 3), with `W' = Y(V') + K e₀` by
     `exists_eq_map_waldschmidtPointMap_sup` (split 1).
  4. The obstructions with `e₀ ∉ W'` or with trivial torus part use two more inputs, neither
     formalized yet:
     - the subgroup obstruction from the multiplicative rank of the `α_j`, whose kernel
       `s ↦ α^s` has rank `≤ 1`;
     - the reduction of a short rational coefficient relation by Liouville.

## Splits

1. **feat: subspaces spanned by Waldschmidt's grid points.** Needs none.
   - Files:
     - `…/Waldschmidt/Interpolation/Data.lean` (+137);
     - `…/Interpolation/Matrix.lean` (+11/−37).
   - Declarations:
     - `eq_neg_smul_snoc_of_waldschmidtPointMap_mem`;
     - `comap_waldschmidtPointMap_span_single`;
     - `comap_waldschmidtPointMap_map_sup`;
     - `exists_eq_map_waldschmidtPointMap_sup`;
     - `finrank_map_waldschmidtPointMap_sup`.

   It also simplifies `rank_waldschmidtInterpolationMatrix_le`. About 150 changed lines.
2. **feat: the rank of Waldschmidt's interpolation matrix and the zero estimate.** Needs 1.
   - Files:
     - `…/Interpolation/Rank.lean` (new, 216 lines);
     - `TauCeti/RingTheory/MvPolynomial/DirectionalOrder.lean` (+29);
     - `TauCeti/RingTheory/MvPolynomial/LinearSubst.lean` (+19).
   - Declarations:
     - `rank_waldschmidtInterpolationMatrix_eq_iff_of_mem`;
     - `rank_waldschmidtInterpolationMatrix_eq_iff`;
     - `MvPolynomial.eval_pderiv_eq_zero_of_forall_eval_add_smul_single`;
     - `Matrix.eval_aeval_toMvPolynomial`.

   About 265 lines.
3. **feat: the residual subspace of Waldschmidt's rank argument.** Needs 1.
   - Files:
     - `TauCeti/Combinatorics/Additive/ImageCard.lean` (new, 60 lines);
     - `…/Interpolation/Residual.lean` (new, 228 lines).
   - Declarations:
     - `AddMonoidHom.ncard_image_le_mul_ncard_image_sub_inter_ker`;
     - `exists_waldschmidtResidualSubspace`;
     - `mul_pow_lt_mul_ncard_image_mkQ_sub_inter`;
     - `mul_pow_lt_mul_ncard_image_mkQ_nsmul`;
     - `ncard_image_mkQ_waldschmidtPoint`;
     - `mul_pow_lt_mul_ncard_image_mkQ_waldschmidtPoint`.

   About 290 lines. Splits 2 and 3 do not import each other and can be opened together.
4. **feat: a multiplicity estimate on the additive group times the torus.** Needs none. Not on
   this branch.
5. **feat: the rank of Waldschmidt's interpolation matrix.** Needs 1, 2, 3 and 4. Carries
   `waldschmidtInterpolationRank` and completes the target. Not on this branch.

## Self-audit notes (rubrics)

- **Correctness.** The rank results are iff statements, so the zero estimate is never a
  hypothesis. The counting results take the minimality clause in exactly the form
  `exists_waldschmidtResidualSubspace` returns it. They need `T₀ ≠ 0`, to cancel the factor
  `T₀^(m−d)` shared by the two inequalities, and the sumset form needs `S` nonempty, so that `0 ∈ (S−S) ∩ V`.
- **Reuse.**
  - Rank side: Mathlib's `Matrix.toMvPolynomial`, `LinearMap.exists_leftInverse_of_injective` and
    `MvPolynomial.funext`; Tau Ceti's `aeval_mem_restrictTotalDegree`,
    `finrank_restrictTotalDegree`, `basisRestrictTotalDegree` and `pderiv_aeval`.
  - Counting: Tau Ceti's `Set.encard_image_eq_encard_image_of_eq_iff`, plus `Set.ncard_prod`,
    `Set.subset_nsmul` and `Function.invFunOn`.
  - The inline kernel argument of `finrank_map_waldschmidtPointMap_sup` was replaced by the new
    public `eq_neg_smul_snoc_of_waldschmidtPointMap_mem`, not duplicated.
- **Placement.**
  - The general fibre count lives in `Combinatorics/Additive/ImageCard.lean`, with no roadmap
    vocabulary.
  - The grid-point-map subspace lemmas sit next to `waldschmidtPointMap` in `Data.lean`.
  - The residual-subspace material has its own file, so that splits 2 and 3 are independent.
- **API.** `Rank.lean` keeps two private lemmas for its own use: `eval_iterate_pderiv_zero_eq_zero`
  and `exists_restrictTotalDegree_linearMap`. A reviewer may ask to make the second public in
  `RingTheory/MvPolynomial/Finrank.lean`.
- **Checks run.**
  - `lake build` is green and `lookahead-check` is ok.
  - Batteries environment linters (simpNF, unusedArguments, docBlame, …) pass on all five touched
    modules. This used the `LintEnvDriver.lean` stand-in, not `scripts/lint-env.sh`, which needs
    `uvx`.
  - Lines are ≤ 100 characters.
