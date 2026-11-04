<!--tauceti-lookahead:v1 {"area":"StableReduction","slug":"normalization-exact-sequence","main":"11a5574886a7b084337236bb1f858406b483c6cc","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: the cokernel of an algebra modulo an ideal inside the base"},{"n":2,"after":[1],"title":"feat: one blowup normalizes a node: conductor, cokernel and regularity"},{"n":3,"after":[1,2],"title":"feat: the quadratic relation of the local ring at a node of a curve"},{"n":4,"after":[1,2,3],"title":"feat: the normalization exact sequence of a proper nodal curve"}]}-->

# Lookahead: `normalization-exact-sequence` (StableReduction)

Target (StableReduction `README.md`, Layer 1, *nodes, normalization, and dual graphs*): "Develop
normalization, the conductor, and the normalization exact sequence for `𝒪_X`." Built on `main`
at `11a5574886a`.

Status: **partial**. The branch now proves the whole local half of the target, for an
arbitrary node of a nodal curve over a field, split or not:

* at a point `x` of `Sing(X/K)`, the maximal ideal of `𝒪_{X,x}` is `(u, v)` with
  `a u² + b u v + v² = 0` and `b² - 4a` a unit (split 3);
* blowing up the closed point once gives `B = 𝒪_{X,x}[𝔪/u]`. It is finite over `𝒪_{X,x}`, it is the
  integral closure of `𝒪_{X,x}` in `𝒪_{X,x}[1/u]`, and its local rings at maximal ideals are
  discrete valuation rings (splits 2–3);
* when `u` is a nonzerodivisor (for instance when the local ring is reduced and not a field),
  the conductor of `B` is `𝔪` and the cokernel `B / 𝒪_{X,x}` is the residue field. This is the
  local normalization sequence `0 → A → B → κ → 0`, and its last term is also the cokernel of
  `A` into the functions on the exceptional fibre (splits 1–3).

What remains is listed at the end.

## Suppliers and stubs

The supplier `node-branch-splitting` was stubbed at the previous tip (`7da6390eda43`). The stubs
were four theorems restating the form of its pull request **#23800**: `divBy_sq_add_mul_add_eq_zero`,
`toSubmodule_affineBlowup_eq_span`, `finite_affineBlowup` and `etale_tensor_affineBlowup`.
`StableReduction/Suggested.lean` pins no declaration for this item; it states only
`exists_regular_proper_model`. #23800 has since been merged by Bors into
`TauCeti/RingTheory/Node/ExceptionalFiber.lean` on `main`, with the statements the stubs used.
So this round deleted `TauCeti/Lookahead/` entirely. `TauCeti/RingTheory/Node/Resolution.lean` now
imports `TauCeti.RingTheory.Node.ExceptionalFiber` directly, and the branch has **no stubs and no
`sorry`**. Splits 1–3 build against `main` alone and can be opened now. The other merged parts of
`node-branch-splitting` are used directly from `main`: the plane-curve presentation at a node
(`TauCeti/RingTheory/Node/PlaneCurve.lean`), the Hessian criterion and the cotangent-space
computation.

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
   Files: new `TauCeti/RingTheory/Node/QuadraticRelation.lean` (321 lines) and new
   `TauCeti/AlgebraicGeometry/Curves/Node/Stalk.lean` (136 lines). Adds
   `TauCeti.exists_quadratic_relation_of_isUnit_discrim` (a nondegenerate binary quadratic
   relation `a s² + b s t + c t² = 0` on generators of `𝔪` can be normalized so that `c = 1`;
   over a local ring some coefficient among `a`, `c`, `a - b + c` is a unit),
   `TauCeti.exists_quadratic_relation_of_ringEquiv`,
   `TauCeti.exists_quadratic_relation_of_isUnit_det_hessian` (`P ⧸ (f)` with `f ∈ 𝔪_P²` of unit
   Hessian), `TauCeti.mem_nonZeroDivisors_of_maximalIdeal_notMem_associatedPrimes`,
   `TauCeti.exists_quadratic_relation_of_formallyUnramified`,
   `Algebra.Presentation.exists_quadratic_relation_of_formallyUnramified`,
   `TauCeti.exists_integralClosure_eq_affineBlowup_of_formallyUnramified`,
   `TauCeti.exists_conductor_affineBlowup_eq_maximalIdeal_of_formallyUnramified`,
   `AlgebraicGeometry.Scheme.exists_quadratic_relation_stalk` and
   `AlgebraicGeometry.Scheme.exists_integralClosure_stalk_eq_affineBlowup`.
4. **`feat: the normalization exact sequence of a proper nodal curve`** (after: 1, 2, 3).
   *Not on the branch.* This split carries the target's exported theorems and is the only one
   that completes the target. For a proper nodal curve `X/K` it builds:
   * the normalization `ν : X̃ → X`, as the relative normalization
     (`Mathlib/AlgebraicGeometry/Normalization.lean`), finite, with stalks the blowup charts of
     split 3 at nodes;
   * `ν.conductor` (`TauCeti/AlgebraicGeometry/IdealSheaf/Conductor.lean`) equal to the ideal
     sheaf of `Sing(X/K)`, stalkwise by `conductor_affineBlowup_eq_maximalIdeal`;
   * the sequence `0 → 𝒪_X → ν_*𝒪_X̃ → Q → 0` of
     `TauCeti/AlgebraicGeometry/Modules/StructureSheafSequence.lean`, with `Q` identified by
     split 1 with the direct image from `Sing(X/K)` of the functions on the branch scheme modulo
     those on `Sing(X/K)`. This is an invertible `𝒪_{Sing}`-module, since the branch scheme is
     finite étale of degree two.

   If it exceeds 600 lines it splits further: first the nonzerodivisor input below, then `ν`
   with its conductor, then the sequence.

## What remains

Proved here (splits 1–3): the normalization of the local ring at every node of a nodal curve
over a field as one blowup, with its finiteness and regularity. Assuming the blowup coordinate
`u` is a nonzerodivisor, it also proves the conductor `𝔪` and the cokernel `κ`. Remaining:

* **`u` is a nonzerodivisor in `𝒪_{X,x}`.** By
  `mem_nonZeroDivisors_of_maximalIdeal_notMem_associatedPrimes` it suffices that `𝔪` is not an
  associated prime. The stalk is Cohen–Macaulay
  (`AlgebraicGeometry.Scheme.Hom.isCohenMacaulay_of_syntomic_of_field`), so its associated primes
  are its minimal primes (`Module.satisfiesSerreS_one_iff`). It then remains to show that `𝔪` is
  not minimal: the point `x` is closed, because `Sing(X/K)` is unramified over `K`, so on a chart
  `S ⧸ Fitt₁` has dimension zero; and `Spec S` is pure one-dimensional
  (`Algebra.IsStandardSyntomicOfRelativeDimension.isPureDimensional_primeSpectrum`), so a closed
  point is not a minimal prime. With this,
  `exists_conductor_affineBlowup_eq_maximalIdeal_of_formallyUnramified` applies at every node
  without its reducedness hypothesis.
* **Split 4:** the globalization over `Sing(X/K)` and the scheme-level exact sequence for `𝒪_X`,
  as described above.
