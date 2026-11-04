<!--tauceti-lookahead:v1 {"area": "StableReduction", "slug": "normalization-exact-sequence", "main": "6c781b0a7341d9d794cf474258f824f4fa65faa2", "status": "partial", "suppliers": ["node-branch-splitting"], "splits": [{"n": 1, "after": [], "title": "feat: the cokernel of an algebra modulo an ideal inside the base"}, {"n": 2, "after": [1], "title": "feat: one blowup normalizes a node: conductor, cokernel and regularity"}, {"n": 3, "after": [], "title": "feat: the integral closure over a punctured spectrum is determined at the closed point"}, {"n": 4, "after": [2], "title": "feat: the normalization of the local ring at a node of a curve"}, {"n": 5, "after": [2, 3, 4], "title": "feat: the normalization of an affine neighbourhood of a node"}, {"n": 6, "after": [1, 2, 3, 4, 5], "title": "feat: the normalization exact sequence of a proper nodal curve"}]}-->

# Lookahead: `normalization-exact-sequence` (StableReduction)

Target (StableReduction `README.md`, Layer 1, *nodes, normalization, and dual graphs*): "Develop
normalization, the conductor, and the normalization exact sequence for `𝒪_X`." Built on `main`
at `6c781b0a734`.

Status: **partial**. The branch proves the local half of the target at every node of a nodal
curve over a field, split or not, and its first globalization step:

* at a point `x` of `Sing(X/K)`, the maximal ideal of `𝒪_{X,x}` is `(u, v)`, not principal, with
  `u` a nonzerodivisor, `a u² + b u v + v² = 0` and `b² - 4a` a unit, and `𝔪 = √(u)` (split 4);
* one blowup `B = 𝒪_{X,x}[𝔪/u]` is finite over `𝒪_{X,x}`, is its integral closure in
  `𝒪_{X,x}[1/u]`, has discrete valuation rings as local rings at maximal ideals, has conductor
  `𝔪`, and `B / 𝒪_{X,x} ≅ κ(x)` (splits 2 and 4);
* **new this round (split 5):** every node `x` has an affine open neighbourhood `W` with a section
  `r ∈ Γ(X, W)` vanishing on `W` only at `x` (`√(r)` is the prime of `x`), such that the integral
  closure of `Γ(X, W)` in `Γ(X, W)_r` is finite over `Γ(X, W)`, has conductor the prime `𝔭_x` of
  `x`, and has cokernel `Γ(X, W) / 𝔭_x`
  (`AlgebraicGeometry.Scheme.exists_affineOpen_integralClosure_away`).

What remains is the scheme-level split 6, described at the end.

**Changed this round.** The supplier `node-branch-splitting` opened PR #27451, which declares
`TauCeti.exists_quadratic_relation_of_isUnit_det_hessian` — the same name the previous tip used for
its own weaker version in `QuadraticRelation.lean`. The branch now stubs #27451's form, which also
gives that `x` is a nonzerodivisor and that `𝔪` is not principal, and builds on it. This deleted
from the branch the previous tip's coordinate normalization
(`exists_quadratic_relation_of_isUnit_discrim`, the private `(s, t)²` helper and its own Hessian
theorem: #27451 provides these as `exists_eq_unit_mul_quadratic_of_isUnit_discrim` and
`Ideal.mem_span_pair_sq`). It also deleted the positive-depth route to the nonzerodivisor
(`mem_nonZeroDivisors_of_maximalIdeal_notMem_associatedPrimes`,
`Scheme.maximalIdeal_stalk_notMem_associatedPrimes`,
`IsStandardSyntomicOfRelativeDimension.notMem_minimalPrimes_of_isMaximal`,
`TauCeti.not_isPrincipal_maximalIdeal` and the private `not_isPrincipal_maximalIdeal_stalk`), which
the stub supersedes. The branch no longer changes `StandardSyntomic.lean` or `Cotangent.lean`.

## Suppliers and stubs

Supplier: `node-branch-splitting` (StableReduction), open PR #27451 ("feat: the blowup of the local
ring at a node has an étale exceptional fibre of degree two"). `StableReduction/Suggested.lean`
pins **no** declaration for this item: its only theorem is `exists_regular_proper_model`. Both
stubs therefore restate the declarations of #27451's diff, with the same names, namespaces,
hypotheses and conclusions. They live in
`TauCeti/Lookahead/NormalizationExactSequence/Stubs.lean`, which imports the modules #27451's
declarations sit in or import (`LocalRing/Hessian`, `RegularLocalRing/Basic`, `Smooth/Regular`).
Earlier merged parts of the same supplier (#23800's `ExceptionalFiber.lean`, `PlaneCurve.lean`, the
Hessian criterion and the singular-locus criterion) are used directly from `main`.

1. `TauCeti.IsRegularLocalRing.of_formallySmooth` (#27451, `TauCeti/RingTheory/Smooth/Regular.lean`).
   `Suggested.lean`: none. #27451, verbatim (under `variable {R S : Type*} [CommRing R]
   [CommRing S] [Algebra R S]`):
   ```lean
   theorem IsRegularLocalRing.of_formallySmooth [IsRegularRing R] [IsLocalRing S]
       [Algebra.EssFiniteType R S] [Algebra.FormallySmooth R S] : IsRegularLocalRing S
   ```
   Stub: the same, with the section variables written into the signature as
   `{R S : Type*} [CommRing R] [CommRing S] [Algebra R S]`. No other difference.
2. `TauCeti.exists_quadratic_relation_of_isUnit_det_hessian` (#27451, new
   `TauCeti/RingTheory/Node/TangentCone.lean`). `Suggested.lean`: none. #27451, verbatim (under
   `variable {P A : Type*} [CommRing P] [CommRing A]` and `variable [IsRegularLocalRing P]
   [IsLocalRing A] {R : Type*} [CommSemiring R] [Algebra R P] {s : Fin 2 → P}
   {D : Fin 2 → Derivation R P P} {f : P}`):
   ```lean
   theorem exists_quadratic_relation_of_isUnit_det_hessian
       (hs : maximalIdeal P = Ideal.span (Set.range s))
       (hD : ∀ i j, D i (s j) = if i = j then 1 else 0) (hf : f ∈ maximalIdeal P ^ 2)
       (hH : IsUnit (hessian D f).det) (π : P →+* A) (hπ : Function.Surjective π)
       (hker : RingHom.ker π = Ideal.span {f}) :
       ∃ x y a b : A, maximalIdeal A = Ideal.span {x, y} ∧ x ∈ nonZeroDivisors A ∧
         ¬ (maximalIdeal A).IsPrincipal ∧ a * x ^ 2 + b * x * y + y ^ 2 = 0 ∧
         IsUnit (discrim a b 1)
   ```
   Stub: the same, with the section variables written into the signature. No other difference.

**Porting note.** When #27451 lands, delete `Stubs.lean`, import
`TauCeti.RingTheory.Node.TangentCone` (and `TauCeti.RingTheory.Smooth.Regular`) in
`QuadraticRelation.lean` instead. The private `exists_quadratic_relation_of_algEquiv` of
`QuadraticRelation.lean` mirrors #27451's private `exists_etale_tensor_affineBlowup_of_algEquiv`;
if #27451 lands with a public transport lemma, use it.

## Splits

1. **`feat: the cokernel of an algebra modulo an ideal inside the base`** (after: none).
   File: `TauCeti/RingTheory/Conductor.lean` (+62 lines). Adds
   `TauCeti.Algebra.map_conductor_le_one`, `TauCeti.Algebra.quotientOneEquivOfLE` (for an ideal
   `I ⊆ A` of `B`, `B / A ≃ₗ[A] (B / I) / A`) and `TauCeti.Algebra.quotientOneEquivOfLE_mk`.
2. **`feat: one blowup normalizes a node: conductor, cokernel and regularity`** (after: 1).
   Files: new `TauCeti/RingTheory/Node/Resolution.lean` (428 lines) and
   `TauCeti/RingTheory/Ideal/AffineBlowup.lean` (+10). Adds
   `Ideal.algebraMap_affineBlowup_injective`, `TauCeti.maximalIdeal_le_conductor_affineBlowup`,
   `TauCeti.conductor_affineBlowup_eq_maximalIdeal`, `TauCeti.affineBlowupQuotientEquiv`,
   `TauCeti.affineBlowupQuotientEquiv_mk_divBy`, `TauCeti.affineBlowupQuotientEquivFiber`,
   `TauCeti.isRegularLocalRing_localization_affineBlowup`,
   `TauCeti.isDiscreteValuationRing_localization_affineBlowup` and
   `TauCeti.integralClosure_eq_affineBlowup`.
3. **`feat: the integral closure over a punctured spectrum is determined at the closed point`**
   (after: none; it uses only `main`'s `TauCeti.Algebra.conductor`). File: new
   `TauCeti/RingTheory/IntegralClosure/Punctured.lean` (298 lines). Adds
   `TauCeti.isCoprime_pow_of_radical_span_singleton_eq`,
   `TauCeti.exists_notMem_forall_eq_of_isMaximal`,
   `TauCeti.exists_notMem_radical_span_singleton_eq` (**new**: if `u` generates an ideal of radical
   `𝔪` in `A_q`, some basic open `D(g) ∋ q` has `q` as the radical of `(u)`, and `q` stays maximal
   there), `TauCeti.isLocalizedModule_id_of_pow_smul_eq_zero`, `TauCeti.integralClosureMap`,
   `TauCeti.coe_integralClosureMap`, the instance `TauCeti.isLocalizedModule_integralClosureMap`,
   `TauCeti.localized'_one_integralClosureMap`, `TauCeti.integralClosureQuotientEquiv`,
   `TauCeti.integralClosureQuotientEquiv_mk`,
   `TauCeti.conductor_integralClosure_eq_of_conductor_eq_maximalIdeal`,
   `TauCeti.quotientEquivQuotientMaximalIdeal`,
   `TauCeti.integralClosureQuotientEquivOfQuotientEquiv` and
   `TauCeti.finite_integralClosure_of_quotientEquiv`.
   *Reuse notes.* `integralClosureMap` is the structure map of `main`'s
   `TauCeti.integralClosureMapAlgebra`, bundled because the `letI` instance form made instance
   search on the quotients time out. `quotientEquivQuotientMaximalIdeal` is Mathlib's
   `IsLocalization.AtPrime.equivQuotMaximalIdealPow q A_q 1` up to `pow_one`; transporting along
   `pow_one` timed out in `whnf`.
4. **`feat: the normalization of the local ring at a node of a curve`** (after: 2; and the
   supplier #27451 must have landed, replacing the stubs). Files: new
   `TauCeti/RingTheory/Node/QuadraticRelation.lean` (206 lines) and new
   `TauCeti/AlgebraicGeometry/Curves/Node/Stalk.lean` up to and including
   `exists_conductor_stalk_eq_maximalIdeal` (≈190 lines, with the module docstring trimmed to
   these results). Adds `TauCeti.exists_quadratic_relation_of_ringEquiv`,
   `TauCeti.exists_quadratic_relation_mul_unit` (the shape survives multiplying `x` by a unit),
   `TauCeti.radical_span_singleton_eq_maximalIdeal` (`𝔪 = √(x)`), the private
   `exists_quadratic_relation_of_algEquiv`, `TauCeti.exists_quadratic_relation_of_formallyUnramified`,
   `TauCeti.exists_integralClosure_eq_affineBlowup_of_formallyUnramified`,
   `Algebra.Presentation.exists_quadratic_relation_of_formallyUnramified`, the private chart lemma
   `exists_chart`, `AlgebraicGeometry.Scheme.exists_quadratic_relation_stalk`,
   `AlgebraicGeometry.Scheme.exists_integralClosure_stalk_eq_affineBlowup` and
   `AlgebraicGeometry.Scheme.exists_conductor_stalk_eq_maximalIdeal` (at a node, `u` is a
   nonzerodivisor, the conductor of `𝒪_{X,x}[𝔪/u]` is `𝔪`, and its cokernel is `κ(x)`).
5. **`feat: the normalization of an affine neighbourhood of a node`** (after: 2, 3, 4). Files: new
   `TauCeti/RingTheory/Node/Punctured.lean` (90 lines), `TauCeti/RingTheory/Unramified/LocalRing.lean`
   (+18) and the rest of `TauCeti/AlgebraicGeometry/Curves/Node/Stalk.lean` (≈75 lines). Adds
   `TauCeti.conductor_integralClosure_away_eq_of_maximalIdeal_eq_span` (if `√(u) = q` and `A_q`
   has the node shape with first generator `u`, the integral closure of `A` in `A_u` is finite with
   conductor `q` and cokernel `A / q`; its private `conductor_integralClosure_away_eq_aux` states
   it over an abstract localization `L'`, because instance search on the cokernels times out when
   `L'` is the concrete `A_q ⊗[A] A_u`),
   `Ideal.IsPrime.isMaximal_of_formallyUnramified_quotient` (a prime over an ideal with unramified
   quotient over a field is maximal) and
   `AlgebraicGeometry.Scheme.exists_affineOpen_integralClosure_away`.
6. **`feat: the normalization exact sequence of a proper nodal curve`** (after: 1, 2, 3, 4, 5).
   *Not on the branch.* It carries the target's exported theorems and is the only split that
   completes the target. If it exceeds 600 lines it splits further, in the order of the bullets
   below.

## What remains (split 6)

Globalize over `Sing(X/K)` for a proper nodal curve `X/K`, in
`TauCeti/AlgebraicGeometry/Curves/Normalization.lean` (the path the README's J-B contract names):

* **Isolate each node.** Strengthen `exists_affineOpen_integralClosure_away` so that also
  `W ∩ Sing(X/K) = {x}`: `Sing(X/K)` is finite (`Scheme.isFinite_singularLocus_subschemeι_comp`,
  `Curves/Node/FiniteEtale.lean`) and consists of closed points
  (`Ideal.IsPrime.isMaximal_of_formallyUnramified_quotient`), so one more basic-open shrink by a
  product of sections lying in the other singular primes of `W` but not in `𝔭_x` does it (the ring
  lemma `exists_notMem_radical_span_singleton_eq` keeps holding on a further basic open). Then
  `W ∖ Sing = W ∖ {x} = X.basicOpen r` (from `√(r) = 𝔭_x`), so `Γ(W ∖ Sing) = Γ(W)_r`
  (`IsAffineOpen.isLocalization_basicOpen`).
* **The normalization `ν : X̃ → X`.** Take Mathlib's relative normalization
  (`Mathlib/AlgebraicGeometry/Normalization.lean`) of the open immersion `j : X ∖ Sing(X/K) → X`.
  By `normalizationObjIso`, over an affine `W` as above `Γ(ν⁻¹ W)` is the integral closure of
  `Γ(W)` in `Γ(W)_r`: finite, with conductor `𝔭_x` and cokernel `Γ(W) / 𝔭_x` by split 5. Away from
  `Sing` the curve is smooth, hence normal, and `ν` is an isomorphism there. So `ν` is finite
  (`IsIntegralHom` from Mathlib plus the finiteness above) and scheme-theoretically dominant
  (`isSchemeTheoreticallyDominant_fromNormalization`; `j` is dominant as `u` is a nonzerodivisor).
* **The conductor.** `ν.conductor` (`TauCeti/AlgebraicGeometry/IdealSheaf/Conductor.lean`) is the
  ideal sheaf of `Sing(X/K)`, affine-locally by the conductor clause of split 5 and
  `Ideal.eq_maximalIdeal_of_formallyUnramified_quotient`.
* **The sequence.** `0 → 𝒪_X → ν_*𝒪_X̃ → Q → 0` from
  `TauCeti/AlgebraicGeometry/Modules/StructureSheafSequence.lean`, with `Q` supported on `Sing(X/K)`
  and `Q(W) = Γ(W) / 𝔭_x` on the neighbourhoods above by the cokernel clause, so `Q` is the direct
  image of `𝒪_{Sing(X/K)}`; by split 1 it is also the functions on the branch scheme modulo those
  on `Sing(X/K)`.
