<!--tauceti-lookahead:v1 {"area":"StableReduction","slug":"normalization-exact-sequence","main":"6c781b0a7341d9d794cf474258f824f4fa65faa2","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: the cokernel of an algebra modulo an ideal inside the base"},{"n":2,"after":[1],"title":"feat: one blowup normalizes a node: conductor, cokernel and regularity"},{"n":3,"after":[1,2],"title":"feat: the quadratic relation of the local ring at a node of a curve"},{"n":4,"after":[1,2,3],"title":"feat: the conductor of the normalization at a node of a curve"},{"n":5,"after":[1,2,3,4],"title":"feat: the normalization exact sequence of a proper nodal curve"}]}-->

# Lookahead: `normalization-exact-sequence` (StableReduction)

Target (StableReduction `README.md`, Layer 1, *nodes, normalization, and dual graphs*): "Develop
normalization, the conductor, and the normalization exact sequence for `𝒪_X`." Built on `main`
at `6c781b0a734`.

Status: **partial**. The branch proves the whole local half of the target at every node of a
nodal curve over a field, split or not, with no extra hypothesis:

* at a point `x` of `Sing(X/K)`, the maximal ideal of `𝒪_{X,x}` is `(u, v)` with
  `a u² + b u v + v² = 0` and `b² - 4a` a unit, and `𝔪 = √(u)`, so `𝒪_{X,x}[1/u]` is the ring of
  functions on the punctured spectrum (split 3);
* blowing up the closed point once gives `B = 𝒪_{X,x}[𝔪/u]`. It is finite over `𝒪_{X,x}`, it is the
  integral closure of `𝒪_{X,x}` in `𝒪_{X,x}[1/u]`, and its local rings at maximal ideals are
  discrete valuation rings (splits 2–3);
* **new this round:** `𝒪_{X,x}` has positive depth, so `u` is a nonzerodivisor, and the conductor
  of `B` is `𝔪` and the cokernel `B / 𝒪_{X,x}` is the residue field
  (`AlgebraicGeometry.Scheme.exists_conductor_stalk_eq_maximalIdeal`, split 4). This is the local
  normalization sequence `0 → 𝒪_{X,x} → B → κ(x) → 0` at every node.

What remains is the globalization (split 5), described at the end.

## Suppliers and stubs

There are **no stubs and no `sorry`** on the branch, and `TauCeti/Lookahead/` does not exist.

The supplier `node-branch-splitting` was stubbed at an earlier tip (`7da6390eda43`) by four
theorems restating the form of its pull request **#23800**: `divBy_sq_add_mul_add_eq_zero`,
`toSubmodule_affineBlowup_eq_span`, `finite_affineBlowup` and `etale_tensor_affineBlowup`.
`StableReduction/Suggested.lean` pins no declaration for this item; it states only
`exists_regular_proper_model`. #23800 has since merged into
`TauCeti/RingTheory/Node/ExceptionalFiber.lean` on `main` with the statements the stubs used, so
the stubs were deleted and `TauCeti/RingTheory/Node/Resolution.lean` imports that module
directly. The other merged parts of `node-branch-splitting` are used directly from `main`: the
plane-curve presentation at a node (`TauCeti/RingTheory/Node/PlaneCurve.lean`), the Hessian
criterion, the cotangent-space computation and the singular-locus criterion.

Splits 1–4 build against `main` alone and can be opened now (in order).

## Splits

1. **`feat: the cokernel of an algebra modulo an ideal inside the base`** (after: none).
   File: `TauCeti/RingTheory/Conductor.lean` (+62 lines). Adds
   `TauCeti.Algebra.map_conductor_le_one`, `TauCeti.Algebra.quotientOneEquivOfLE` (for an ideal
   `I ⊆ A` of `B`, `B / A ≃ₗ[A] (B / I) / A`, the conductor square of a normalization) and
   `TauCeti.Algebra.quotientOneEquivOfLE_mk`.
2. **`feat: one blowup normalizes a node: conductor, cokernel and regularity`** (after: 1).
   Files: new `TauCeti/RingTheory/Node/Resolution.lean` (428 lines), and
   `TauCeti/RingTheory/Ideal/AffineBlowup.lean` (+10 lines). Adds
   `Ideal.algebraMap_affineBlowup_injective`, `TauCeti.maximalIdeal_le_conductor_affineBlowup`,
   `TauCeti.conductor_affineBlowup_eq_maximalIdeal`, `TauCeti.affineBlowupQuotientEquiv`,
   `TauCeti.affineBlowupQuotientEquiv_mk_divBy`, `TauCeti.affineBlowupQuotientEquivFiber`,
   `TauCeti.isRegularLocalRing_localization_affineBlowup`,
   `TauCeti.isDiscreteValuationRing_localization_affineBlowup` and
   `TauCeti.integralClosure_eq_affineBlowup`.
3. **`feat: the quadratic relation of the local ring at a node of a curve`** (after: 1, 2).
   Files: new `TauCeti/RingTheory/Node/QuadraticRelation.lean` (≈300 lines) and new
   `TauCeti/AlgebraicGeometry/Curves/Node/Stalk.lean` holding only its chart lemma
   `exists_chart` and the first two theorems below (≈150 lines). Adds
   `TauCeti.exists_quadratic_relation_of_isUnit_discrim`,
   `TauCeti.exists_quadratic_relation_of_ringEquiv`,
   `TauCeti.radical_span_singleton_eq_maximalIdeal` (`𝔪 = √(x)`),
   `TauCeti.exists_quadratic_relation_of_isUnit_det_hessian`,
   `TauCeti.mem_nonZeroDivisors_of_maximalIdeal_notMem_associatedPrimes`,
   `TauCeti.exists_quadratic_relation_of_formallyUnramified`,
   `Algebra.Presentation.exists_quadratic_relation_of_formallyUnramified`,
   `TauCeti.exists_integralClosure_eq_affineBlowup_of_formallyUnramified`,
   `AlgebraicGeometry.Scheme.exists_quadratic_relation_stalk` and
   `AlgebraicGeometry.Scheme.exists_integralClosure_stalk_eq_affineBlowup`.
4. **`feat: the conductor of the normalization at a node of a curve`** (after: 1, 2, 3).
   Files: `TauCeti/RingTheory/Syntomic/StandardSyntomic.lean` (+14),
   `TauCeti/RingTheory/Unramified/LocalRing.lean` (+18), `TauCeti/RingTheory/Node/Cotangent.lean`
   (+9), and the rest of `TauCeti/AlgebraicGeometry/Curves/Node/Stalk.lean` (≈95 lines). Adds
   `TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.notMem_minimalPrimes_of_isMaximal`
   (over a field, in positive relative dimension, a maximal ideal is not minimal),
   `Ideal.IsPrime.isMaximal_of_formallyUnramified_quotient` (a prime over an ideal with
   unramified quotient over a field is maximal), `TauCeti.not_isPrincipal_maximalIdeal` (the
   maximal ideal at a node is not principal), the private `not_isPrincipal_maximalIdeal_stalk`,
   `AlgebraicGeometry.Scheme.maximalIdeal_stalk_notMem_associatedPrimes` (the local ring at a
   node has positive depth: it is Cohen–Macaulay, and `x` is a closed point of a chart that is
   pure of dimension one) and `AlgebraicGeometry.Scheme.exists_conductor_stalk_eq_maximalIdeal`
   (at a node, `u` is a nonzerodivisor, the conductor of the normalization `𝒪_{X,x}[𝔪/u]` is `𝔪`,
   and the cokernel is `κ(x)`).
5. **`feat: the normalization exact sequence of a proper nodal curve`** (after: 1, 2, 3, 4).
   *Not on the branch.* This split carries the target's exported theorems and is the only one
   that completes the target. If it exceeds 600 lines it splits further, in the order of the
   bullets below.

## What remains (split 5)

Globalize the local results over `Sing(X/K)` for a proper nodal curve `X/K`, in
`TauCeti/AlgebraicGeometry/Curves/Normalization.lean` (the path the README's J-B contract names):

* **The normalization `ν : X̃ → X`.** Take Mathlib's relative normalization
  (`Mathlib/AlgebraicGeometry/Normalization.lean`) of the open immersion
  `j : X ∖ Sing(X/K) → X`. Its affine-local sections are the integral closure of `Γ(X, U)` in
  `Γ(U ∖ Sing)`. Since `Sing` is finite (`Scheme.isFinite_singularLocus_subschemeι_comp`) and
  `𝔪_x = √(u)` (`radical_span_singleton_eq_maximalIdeal`), the punctured neighbourhood of a node
  is `D(u)` locally, so the stalk of `ν_*𝒪_X̃` at a node is the integral closure of `𝒪_{X,x}` in
  `𝒪_{X,x}[1/u]`, which is `𝒪_{X,x}[𝔪/u]` by `exists_conductor_stalk_eq_maximalIdeal`; away from
  `Sing` the curve is smooth, hence normal, and `ν` is an isomorphism. In particular `ν` is finite
  (`IsIntegralHom` from Mathlib plus finiteness of the blowup chart) and scheme-theoretically
  dominant (`isSchemeTheoreticallyDominant_fromNormalization`, `j` being dominant as `u` is a
  nonzerodivisor).
* **The conductor.** `ν.conductor` (`TauCeti/AlgebraicGeometry/IdealSheaf/Conductor.lean`) is the
  ideal sheaf of `Sing(X/K)`, stalkwise by the conductor clause of
  `exists_conductor_stalk_eq_maximalIdeal` and `Ideal.eq_maximalIdeal_of_formallyUnramified_quotient`.
* **The sequence.** `0 → 𝒪_X → ν_*𝒪_X̃ → Q → 0` from
  `TauCeti/AlgebraicGeometry/Modules/StructureSheafSequence.lean`, with `Q` supported on
  `Sing(X/K)` and stalk `κ(x)` at each node by the cokernel clause; by split 1, `Q` is the direct
  image from `Sing(X/K)` of the functions on the branch scheme modulo those on `Sing(X/K)`, an
  invertible `𝒪_{Sing}`-module since the branch scheme is finite étale of degree two.
