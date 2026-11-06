<!--tauceti-lookahead:v1 {"area":"DiophantineApproximationAndTranscendence","slug":"waldschmidt-interpolation-rank","main":"385ec2ddd8ddf8cc779b78c176308cb9c6b55499","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: subspaces spanned by Waldschmidt's grid points"},{"n":2,"after":[1],"title":"feat: the rank of Waldschmidt's interpolation matrix and the zero estimate"},{"n":3,"after":[1],"title":"feat: the residual subspace of Waldschmidt's rank argument"},{"n":4,"after":[],"title":"feat: a multiplicity estimate on the additive group times the torus"},{"n":5,"after":[1,2,3,4],"title":"feat: the rank of Waldschmidt's interpolation matrix"}]}-->

# Lookahead: `waldschmidt-interpolation-rank` (partial)

Target: DiophantineApproximationAndTranscendence §3.6, "Rank and multiplicity for the
interpolation matrix" (`waldschmidtInterpolationRank`; W00 §9.2.3, Proposition 9.16, Lemma 9.17;
§9.3.2, Steps 1–2). Built on `main` at `385ec2ddd8d`.

Earlier rounds added the material of splits 1–3: the counting half of the induction on proper
subspaces, and the translation between index subspaces and grid-point subspaces. Six rounds on
2026-11-06 (the last at 09:37 UTC) found `main` unmoved at `afa08a3ed16` and added no
mathematics. The round resuming at `5bb61a91a0b` (09:55 UTC) again found `main` at `afa08a3ed16`
and supplier PR #28644 still open at head `583a153b95f`. It added one input of the Liouville
reduction to split 5: `eq_neg_div_of_intCast_mem_span_snoc`. The round resuming at `87f036711ab`
(11:40 UTC) merged `main` at `385ec2ddd8d`. Supplier PR #28644 is still open. That merge touched
none of the files on this branch, and it added no multivariable zero or multiplicity estimate.
The zero estimates `main` does have are the one-variable real exponential-polynomial ones in
`Analysis/SpecialFunctions/Exp/ExponentialPolynomial.lean` (Rolle-type, used for
Gelfond–Schneider), and they do not give the estimate on `𝔾ₐᵈ × 𝔾ₘ`. That round added no
mathematics. The round resuming at `73c0d46518e` (13:20 UTC) found `main` still at
`385ec2ddd8d` and PR #28644 still open. It added a second input of split 5, the count by which
the multiplicative rank of the `α_j` enters the subgroup obstruction:
`LinearMap.ncard_setOf_apply_eq_zero_abs_le_le` in the new general file
`TauCeti/LinearAlgebra/FreeModule/BoxPoints.lean`. `main` and pinned Mathlib still have
no zero or multiplicity estimate, Philippon-type or otherwise, that split 4 could reuse. The
round resuming at `40ddadd0cfe` (13:37 UTC) found `main` still at `385ec2ddd8d` and PR #28644
still open at head `583a153b95f`. It added two more inputs of split 5:
`LinearMap.ncard_le_mul_ncard_image_of_ker_le` in `BoxPoints.lean` (the box count fed through
the fibre count of split 3), and the Liouville bridge
`intCast_mul_waldschmidtLinearForm_eq_neg_sum` / `exp_neg_intCast_mul_waldschmidtLinearForm` in
`Data.lean`. The round resuming at `1ce6e5ea7a6` (13:56 UTC) found `main` still at
`385ec2ddd8d` and PR #28644 still open at head `583a153b95f`. It specialised the box counts of
`BoxPoints.lean` to the exponent map `s ↦ α₁ ^ s₁ ⋯ αₘ ^ sₘ` of a family in a commutative group:
`TauCeti.ncard_setOf_prod_zpow_eq_one_abs_le_le` and
`TauCeti.ncard_le_mul_ncard_image_of_prod_zpow_eq_one`. Their rank hypothesis is the README's
"the α_j generate multiplicative rank ≥ m−1", stated as
`m ≤ finrank ℤ (span ℤ (range fun j ↦ Additive.ofMul (α j))) + 1`. The round resuming at `3b7646fd84e` (14:13 UTC) found `main` still at
`385ec2ddd8d` and PR #28644 still open at head `583a153b95f`. It closed the Liouville reduction
of split 5:
- `NumberField.InfinitePlace.exp_neg_le_apply_prod_zpow_sub_one` and
  `NumberField.exp_neg_le_norm_prod_zpow_sub_one`, in `main`'s
  `TauCeti/NumberTheory/Height/FundamentalInequality.lean`. They give Liouville's inequality
  `|α^s - 1| ≥ exp(-([K:ℚ] log 2 + Σ |s_j| h(α_j)))` for `α^s ≠ 1`;
- `min_one_div_two_le_norm_intCast_mul_waldschmidtLinearForm` in `Data.lean`, which turns such a
  lower bound into `min 1 (δ/2) ≤ |s_m Λ|`.

What remains is the multiplicity estimate of split 4, which does not fit in one round, and the
assembly in split 5.

## Stubs

**None.** Most of the supplier `waldschmidt-interpolation-data` has already merged: #21294,
#23592 and #23827 landed the normalization, the grid points, the entry identities, the basis
changes and the upper bound on the rank. That material is in
`TauCeti/NumberTheory/Transcendental/Waldschmidt/Interpolation/{Data,Matrix}.lean`. The target
uses the following from `main` directly: `waldschmidtPoint`, `waldschmidtPointMap`,
`waldschmidtPointMap_snoc`, `waldschmidtOperatorEntry`,
`waldschmidtOperatorEntry_eq_sum_hasseDeriv`, `waldschmidtInterpolationMatrix` and
`rank_waldschmidtInterpolationMatrix_le{,_of_mem}`.

Since the last round, PR #27120 (the denominators of the entries) has landed as
`Interpolation/Denominator.lean`. The one part of the supplier still open is PR #28644, the
delta-polynomial rows. Its diff adds:

- `Interpolation/Delta.lean`;
- lemmas in `Baker/Delta.lean` and `Algebra/MvPolynomial/PDeriv.lean`;
- `waldschmidtOperatorEntry_prod_aeval_X` in `Data.lean`, the entry of a separated row;
- denominator bounds for the delta rows in `Denominator.lean`.

None of this is consumed by the rank argument. The delta rows and their denominators are
arithmetic and play no part in the rank. The rank is a statement over the coefficient
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

**Input to split 5 (Liouville reduction).** Also in section `FinrankPointMap` of `Data.lean`,
with `[CharZero K]`:

- `eq_neg_div_of_intCast_mem_span_snoc`: a nonzero integral `s ∈ K c` has `s_m ≠ 0` and
  `β_k = -s_k / s_m` for `1 ≤ k < m`. So the excluded case `β₀ = 0`, `(S−S)[2] ∩ K c ≠ {0}` makes
  the `β_k` rational with height at most `‖s‖∞`, which is what the Liouville step consumes. It
  belongs to split 5 (+25 lines in `Data.lean`), next to its consumer.

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
       `s ↦ α^s` has rank `≤ 1`. View `s ↦ α^s` as a `ℤ`-linear map into `Additive ℂˣ`.
       This branch now proves (`BoxPoints.lean`, below) that its kernel has rank `≤ 1` and
       meets the box `‖s‖∞ ≤ R` in at most `2R + 1` points, and, through
       `AddMonoidHom.ncard_image_le_mul_ncard_image_sub_inter_ker` (split 3), that a finite `S`
       whose differences lie in that box has `#S ≤ (2R + 1)·#g(S)` for every `g` whose kernel
       lies in that of `s ↦ α^s` (for instance `s ↦ (π_{W'}(s·y), α^s)`, the quotient map of an
       obstruction with trivial torus part). What remains is to put this count into the degree
       inequality that split 4 will produce;
     - the reduction of a short rational coefficient relation by Liouville. Its steps are now
       all on this branch:
       - `eq_neg_div_of_intCast_mem_span_snoc` reads the rational `β_k` off the relation;
       - `exp_neg_intCast_mul_waldschmidtLinearForm` turns the relation into
         `exp(-s_m Λ) = α^s`, so that `Λ ≠ 0` when `α^s ≠ 1`;
       - `NumberField.exp_neg_le_norm_prod_zpow_sub_one` is Liouville's inequality for
         `α^s - 1`;
       - `min_one_div_two_le_norm_intCast_mul_waldschmidtLinearForm` gives
         `min 1 (δ/2) ≤ |s_m Λ|`.

       Split 5 only has to feed the measure's height bounds `h(α_j) ≤ log A_j`, `|s_j| < T₀/2`
       into the exponent. For `α^s = 1`, `exp(-s_m Λ) = 1`, so `s_m Λ ∈ 2πiℤ`; that case is
       left to the assembly.

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
   `waldschmidtInterpolationRank` and completes the target. On this branch so far only two of
   its inputs:
   - `eq_neg_div_of_intCast_mem_span_snoc` (`Data.lean`, +25), the Liouville reduction's
     rational coefficients;
   - `intCast_mul_waldschmidtLinearForm_eq_neg_sum` and
     `exp_neg_intCast_mul_waldschmidtLinearForm` (`Data.lean`, +27): with `β₀ = 0` and
     `β_k = -s_k/s_m`, `s_m Λ = -Σ s_j λ_j` and `exp(-s_m Λ) = ∏ α_j^{s_j}`;
   - `NumberField.InfinitePlace.exp_neg_le_apply_prod_zpow_sub_one` and
     `NumberField.exp_neg_le_norm_prod_zpow_sub_one`
     (`TauCeti/NumberTheory/Height/FundamentalInequality.lean`, +37), Liouville's inequality for
     `α^s - 1` at an infinite place and under a complex embedding;
   - `min_one_div_two_le_norm_intCast_mul_waldschmidtLinearForm` (`Data.lean`, +19):
     `δ ≤ |α^s - 1|` gives `min 1 (δ/2) ≤ |s_m Λ|`;
   - `TauCeti/LinearAlgebra/FreeModule/BoxPoints.lean` (new, 173 lines; imports `ImageCard.lean`
     of split 3), the subgroup obstruction's count:
     - `Submodule.ncard_setOf_mem_abs_le_le_of_finrank_le_one`: a subgroup of `ℤ^m` of rank
       `≤ 1` has at most `2R + 1` points with `‖s‖∞ ≤ R`;
     - `LinearMap.finrank_ker_le_one`: rank-nullity over `ℤ`, a map out of `ℤ^m` with image of
       rank `≥ m − 1` has kernel of rank `≤ 1`;
     - `LinearMap.ncard_setOf_apply_eq_zero_abs_le_le`: such a map vanishes at `≤ 2R + 1`
       points of the box;
     - `LinearMap.ncard_le_mul_ncard_image_of_ker_le`: a finite `S` whose differences lie in
       the box has `#S ≤ #g(S)·(2R + 1)` for every additive `g` with `ker g ≤ ker φ`.
     - `TauCeti.ncard_setOf_prod_zpow_eq_one_abs_le_le` and
       `TauCeti.ncard_le_mul_ncard_image_of_prod_zpow_eq_one`: the two counts above for
       `φ = Fintype.linearCombination ℤ (Additive.ofMul ∘ α)`, i.e. `s ↦ ∏ α_j ^ s_j`, with
       the multiplicative-rank hypothesis on the `α_j` (+43 lines; one private bridge
       `fintypeLinearCombination_ofMul_apply`).

   The rest is not on this branch. If split 5 grows past 600 lines, `BoxPoints.lean` can be
   opened on its own first, once split 3 (which supplies `ImageCard.lean`) has merged.

## Self-audit notes (rubrics)

- **Correctness.** The rank results are iff statements, so the zero estimate is never a
  hypothesis. The counting results take the minimality clause in exactly the form
  `exists_waldschmidtResidualSubspace` returns it. They need `T₀ ≠ 0`, to cancel the factor
  `T₀^(m−d)` shared by the two inequalities, and the sumset form needs `S` nonempty, so
  that `0 ∈ (S−S) ∩ V`.
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
  - `lake build` is green and `lookahead-check` is ok. Both were rerun on 2026-11-06 at about
    10:05 UTC against `main` at `afa08a3ed16`.
  - `eq_neg_div_of_intCast_mem_span_snoc` reuses `comap_waldschmidtPointMap_span_single` and
    `eq_neg_smul_snoc_of_waldschmidtPointMap_mem` rather than redoing the coordinate argument.
  - An earlier round grepped `main` and pinned Mathlib for every helper on the branch. None
    has landed in the meantime.
  - In an earlier round, the Batteries environment linters (simpNF, unusedArguments, docBlame, …) passed
    on all five touched modules. Later rounds changed no declaration, so they were not
    rerun. Those runs used the `LintEnvDriver.lean` stand-in, not `scripts/lint-env.sh`, which
    needs `uvx`.
  - Lines are ≤ 100 characters.
  - 2026-11-06, about 13:25 UTC, against `main` at `385ec2ddd8d`: `lake build` green,
    `lookahead-check` ok, and `lake exe runLinter TauCeti.LinearAlgebra.FreeModule.BoxPoints`
    passed. Before writing `BoxPoints.lean`, `main` and pinned Mathlib were grepped for a box
    count of lattice points or a rank-one kernel bound; neither has one. Its declarations follow
    the neighbouring `FreeModule/*.lean` files, which use Mathlib namespaces (`Submodule`,
    `LinearMap`) rather than `TauCeti`.
  - 2026-11-06, about 13:45 UTC, same `main`: `lake build` green, `lookahead-check` ok, and
    `runLinter` passed on `BoxPoints` and `Interpolation.Data`. Before writing the new lemmas,
    `main` and pinned Mathlib were grepped for a fibre-count/box bound and for an integral form
    of the normalized linear form; neither exists. The bridge reuses Mathlib's
    `Complex.exp_sum` and `Complex.exp_int_mul`; the count reuses split 3's
    `ncard_image_le_mul_ncard_image_sub_inter_ker` with `f = id` rather than recounting fibres.
  - 2026-11-06, about 14:00 UTC, same `main`: `lake build` green, `lookahead-check` ok, and
    `runLinter` passed on `BoxPoints`. `main` and pinned Mathlib were grepped for a count of
    exponent vectors with `∏ α_j ^ s_j = 1`; none exists. The new declarations sit in
    `namespace TauCeti` (they are about a family in a group, not about `LinearMap`), and reuse
    Mathlib's `Fintype.range_linearCombination`, `ofMul_prod` and `ofMul_zpow`.
  - 2026-11-06, about 14:20 UTC, same `main`: `lake build` green, `lookahead-check` ok, and
    `runLinter` passed on `Height.FundamentalInequality` and `Interpolation.Data`. Before adding
    the Liouville lemmas, `main` and pinned Mathlib were grepped. They have the single-place
    bound `InfinitePlace.inv_mulHeight₁_le_min_one_apply` and Mathlib's height arithmetic, which
    the new lemmas reuse: `logHeight₁_sub_le`, `logHeight₁_prod_le`, `logHeight₁_zpow` and
    `totalWeight_eq_finrank`. Neither has the inequality for a product of powers. The analytic
    step reuses `Complex.norm_exp_sub_one_le`. The Liouville lemmas are general, with no
    roadmap vocabulary, so they sit in `FundamentalInequality.lean` next to the bound they
    consume. `Data.lean` gains no height import.
