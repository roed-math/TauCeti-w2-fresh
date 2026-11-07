<!--tauceti-lookahead:v1 {"area":"DiophantineApproximationAndTranscendence","slug":"yu-auxiliary-construction","main":"2f06c0d69fd88750b4be67237a9cd8e6d83b12aa","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat(FieldTheory/Kummer): q-th roots of Kummer-independent generators have degree q^n and independent monomials"},{"n":2,"after":[1],"title":"feat(NumberTheory/Transcendental/Yu): the auxiliary coefficient array of Yu 1990 Lemma 2.1"},{"n":3,"after":[1,2],"title":"feat(NumberTheory/Transcendental/Yu): Yu's quantitative extrapolation (Proposition 2.1, Theorems 2.1-2.2)"}]}-->

# Lookahead: `yu-auxiliary-construction` (DiophantineApproximationAndTranscendence, §3.7)

Built on `main` at `2f06c0d69fd88750b4be67237a9cd8e6d83b12aa`. Status: **partial**.

## Target

README §3.7, *Yu auxiliary system and quantitative extrapolation*: build `yuAuxiliaryConstruction`
for n ≥ 2 in the Kummer-independent case (q ≠ p, ζ_q in the auxiliary field, the q-th root
extension of the chosen generators of the degree forced by independent classes in K×/(K×)^q),
construct the bounded integer array p(λ, d₀, d) of Yu 1990 Lemma 2.1, and prove
`yuQuantitativeExtrapolation` (Yu 1990 §§2.1–2.6, Proposition 2.1, Theorems 2.1–2.2 with the
Yu 1994 §2 replacements). The roadmap's `Suggested.lean` pins no Lean form for either name (they
appear only in the §3.7 dependency list at its end), so the README prose is the specification.

## Stubs

None on this branch. The supplier `yu-local-estimates` (open PR #28709, partial: finite-difference
coefficient bounds for restricted power series, `TauCeti/RingTheory/PowerSeries/Restricted/FwdDiff.lean`)
is consumed only by split 3 (the local analytic upper bound compared at each extrapolation step).
Split 1 needs nothing from it, so no stub file was created this round. `Suggested.lean` pins no
signature for `yuLocalEstimates`; the next round must stub the declarations PR #28709 (or its
successor) actually states, from `gh pr diff`.

## Splits

### Split 1 (proved here) — after: none
`feat(FieldTheory/Kummer): q-th roots of Kummer-independent generators have degree q^n and independent monomials`

Files (both new, ~275 lines together: `Monomial.lean` 160, `Independent.lean` 131), all declarations in `namespace TauCeti`:

`TauCeti/FieldTheory/Kummer/Monomial.lean` (~130 lines, previous round):

* `prod_pow_mem_span_prod_pow_mod`: if `β j ^ q ∈ K` for all `j`, every monomial `∏ β j ^ e j` is a
  `K`-multiple of the reduced monomial with exponents `e j % q`.
* `toSubmodule_adjoin_le_span_prod_pow`: `K[β]` is spanned by the `qⁿ` reduced monomials.
* `finrank_adjoin_range_le_pow`: `[K[β] : K] ≤ qⁿ`.
* `linearIndependent_prod_pow_of_finrank_adjoin_eq`: if `[K[β] : K] = qⁿ` the reduced monomials
  `∏ β j ^ r j`, `r : Fin n → Fin q`, are `K`-linearly independent.
* `linearIndependent_prod_pow_of_finrank_intermediateFieldAdjoin_eq`: the same for `K(β)` inside a
  field `L`.
* `sum_filter_mul_prod_pow_div_eq_zero` (round 3): if the reduced monomials are independent and
  `∑_e c_e ∏ βⱼ ^ eⱼ = 0` (`c_e ∈ K`, arbitrary exponents `e ∈ s`), then for each residue class
  `r` mod `q`, `∑_{e ∈ s, e ≡ r} c_e ∏ aⱼ ^ (eⱼ / q) = 0` where `aⱼ = βⱼ ^ q ∈ K`.

`TauCeti/FieldTheory/Kummer/Independent.lean` (~115 lines, this round): the Kummer-independent
hypothesis of the target in the form the auxiliary construction consumes it.

* `isFiniteRelIndex_range_powMonoidHom_closure` (instance): in a commutative group, `q`-th powers
  have finite index in a finitely generated subgroup (quotient is f.g. and `q`-torsion, via
  Mathlib's `CommGroup.finite_of_fg_isMulTorsion`).
* `exists_mem_adjoin_range_pow_eq_of_mem_closure`: every element of `⟨α₁, …, αₙ⟩` has a `q`-th
  root in `K(β)` when `βⱼ ^ q = αⱼ`.
* `adjoin_range_eq_kummerField`: with `K` containing the `q`-th roots of unity,
  `K(β) = kummerField E q (closure (range α))`.
* `finrank_adjoin_range_eq_relIndex`: `[K(β) : K]` is the order of the image of `⟨α⟩` in
  `Kˣ ⧸ (Kˣ)^q` (from `TauCeti.finrank_kummerField` on `main`).
* `linearIndependent_prod_pow_of_relIndex_eq`: if that order is `qⁿ` (independent classes), the
  reduced monomials `∏ βⱼ ^ rⱼ` are linearly independent over `K`.
* `sum_filter_mul_prod_pow_div_eq_zero_of_relIndex_eq` (round 3): the support-class separation
  above directly under the Kummer-independent hypothesis.

This is the algebraic engine of the step "Kummer conjugates separate support classes" in the
extrapolation: an identity `∑_r c_r ∏ βⱼ ^ rⱼ = 0` with `c_r ∈ K` forces every `c_r = 0`, which is
how the support classes λ mod q are separated.

### Split 2 (remaining) — after: 1
`feat(NumberTheory/Transcendental/Yu): the auxiliary coefficient array of Yu 1990 Lemma 2.1`

`yuAuxiliaryConstruction`: the index ranges (2.53)–(2.54), the linear derivative/grid conditions
(2.55) as an `𝓞 K`-matrix, the strict equation deficit from the parameter inequalities, and the
nonzero bounded integer array obtained from `NumberField.exists_ne_zero_int_vec_abs_le_of_house_le`
(on `main`, `TauCeti/NumberTheory/NumberField/SiegelsLemma.lean`), with its house bounds for the
coefficients ∏ α_j^{λ_j s} times divided binomial values.

### Split 3 (remaining, completes the target) — after: 1, 2
`feat(NumberTheory/Transcendental/Yu): Yu's quantitative extrapolation (Proposition 2.1, Theorems 2.1-2.2)`

`yuQuantitativeExtrapolation`: under ord_𝔭(Θ) large, induct over 0 ≤ J ≤ ⌊log L_n / log q⌋ + 1
through the q-fold support refinements; at each step compare the analytic upper bound (from
`yuLocalEstimates`, supplier, to stub) with the Liouville-type lower bound for a nonzero algebraic
value, separate support classes by split 1, and contradict the retained nonzero coefficient of
split 2. Carries the constants (2.27)–(2.29) with the Yu 1994 replacements, including the dyadic
ones. This split needs the supplier stubs.

## What remains

Round 3 (2026-11-07, on `main` `2f06c0d69fd8`): merged `main`, and added the support-class
separation lemmas `sum_filter_mul_prod_pow_div_eq_zero` and
`sum_filter_mul_prod_pow_div_eq_zero_of_relIndex_eq` to split 1. These are the exact form in
which the extrapolation's q-fold refinement of λ-supports consumes Kummer independence: a vanishing
`K`-combination of monomials in the roots splits into one vanishing combination per class of
exponents modulo `q`, with the class factor removed. PR #28709 (`yu-local-estimates`) is still
open; its diff states `fwdDiff_iter_pow_apply_zero`, `fwdDiff_iter_pow_eq_sum`,
`norm_fwdDiff_iter_pow_mul_pow_le`, `fwdDiff_descPochhammer_succ_eval`,
`fwdDiff_iter_descPochhammer_eval`, `pow_eq_sum_stirlingSecond_mul_descPochhammer_eval`,
`PowerSeries.IsRestricted.hasSum_fwdDiff_iter_evalAt`,
`PowerSeries.IsRestricted.norm_fwdDiff_iter_evalAt_mul_pow_le` and
`PowerSeries.IsRestricted.norm_evalAt_add_nsmul_le_max` — the finite-difference bounds that split 3
will stub (none is consumed by split 1, so there is still no stub file).

Split 1 is complete (round 2 added `Independent.lean`: the Kummer-independent hypothesis
"independent classes in Kˣ/(Kˣ)^q, ζ_q ∈ K" now yields `[K(β) : K] = qⁿ` and the independence of
reduced monomials directly, with no finiteness side condition). Splits 2 and 3 remain in full.
Neither the Yu 1990 nor the Yu 1994 paper was available offline in either round, so the exact
index ranges (2.53)–(2.55) and constants (2.27)–(2.29) could not be transcribed; the next round needs
the papers (numdam links in the README references) before writing split 2. PR #28709
(`yu-local-estimates`, partial) was still open on 2026-11-07; split 3 must stub what it states.
