<!--tauceti-lookahead:v1 {"area":"StableReduction","slug":"normalization-exact-sequence","main":"333c9e49143de812ed1452b412193ee9c05501e7","status":"partial","suppliers":["node-branch-splitting"],"splits":[{"n":1,"after":[],"title":"feat: the cokernel of an algebra modulo an ideal inside the base"},{"n":2,"after":[1],"title":"feat: one blowup normalizes a node: conductor, cokernel and regularity"},{"n":3,"after":[1,2],"title":"feat: the normalization exact sequence of a proper nodal curve"}]}-->

# Lookahead: `normalization-exact-sequence` (StableReduction)

Target (StableReduction `README.md`, Layer 1, *nodes, normalization, and dual graphs*): "Develop
normalization, the conductor, and the normalization exact sequence for `𝒪_X`." Built on `main`
at `333c9e49143`.

Status: **partial**. The branch proves the local algebra at an arbitrary node, split or not:
blowing up the closed point once gives a ring `B = A[𝔪/x]` that is the integral closure of `A`
in `A_x` (the normalization of the node), all of whose local rings at maximal ideals are discrete
valuation rings; its conductor over `A` is `𝔪`, and its cokernel `B / A` is the residue field
(the `δ`-invariant is one), equal to the cokernel of `A` into the functions on the exceptional
fibre. It also proves the general conductor-square identity of cokernels. What remains is the
globalization to a proper nodal curve, listed at the end.

## Stubbed declarations (supplier `node-branch-splitting`)

The roadmap's `StableReduction/Suggested.lean` pins **no** declaration for this item (it states
only `exists_regular_proper_model`). Every stub therefore restates the form of the supplier's
open pull request **#23800** (`feat: the exceptional fibre of blowing up a node is étale of degree
two`), which adds them to `TauCeti/RingTheory/Node/ExceptionalFiber.lean`. All four are theorems,
stated with `sorry` in `TauCeti/Lookahead/NormalizationExactSequence/Stubs.lean`. There is no
`Suggested.lean` signature to copy for any of them; the differences listed are between the stub
and PR #23800's diff.

1. `TauCeti.divBy_sq_add_mul_add_eq_zero`. PR #23800:
   ```lean
   variable {A : Type*} [CommRing A] {x y a b : A}
     (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away x S]
   theorem divBy_sq_add_mul_add_eq_zero (hrel : a * x ^ 2 + b * x * y + y ^ 2 = 0) :
       (divBy y x : S) ^ 2 + algebraMap A S b * divBy y x + algebraMap A S a = 0
   ```
   Stub: identical, with the same variable block (`S` explicit).
2. `TauCeti.toSubmodule_affineBlowup_eq_span`. PR #23800 (after `variable {S} {I : Ideal A}`):
   ```lean
   theorem toSubmodule_affineBlowup_eq_span (hI : I = Ideal.span {x, y})
       (hrel : a * x ^ 2 + b * x * y + y ^ 2 = 0) :
       Subalgebra.toSubmodule (I.affineBlowup x S) = Submodule.span A {1, divBy y x}
   ```
   Stub: identical.
3. `TauCeti.finite_affineBlowup`. PR #23800:
   ```lean
   theorem finite_affineBlowup (hI : I = Ideal.span {x, y})
       (hrel : a * x ^ 2 + b * x * y + y ^ 2 = 0) :
       Module.Finite A (I.affineBlowup x S)
   ```
   Stub: identical.
4. `TauCeti.etale_tensor_affineBlowup`. PR #23800 (in `section Fiber`, after
   `variable [IsLocalRing A]` and
   `variable (hm : maximalIdeal A = Ideal.span {x, y}) (hrel : a * x ^ 2 + b * x * y + y ^ 2 = 0)`
   with `include hm hrel`):
   ```lean
   theorem etale_tensor_affineBlowup (hd : IsUnit (discrim a b 1)) :
       Algebra.Etale (ResidueField A) (ResidueField A ⊗[A] (maximalIdeal A).affineBlowup x S)
   ```
   Stub:
   ```lean
   theorem etale_tensor_affineBlowup (hm : maximalIdeal A = Ideal.span {x, y})
       (hrel : a * x ^ 2 + b * x * y + y ^ 2 = 0) (hd : IsUnit (discrim a b 1)) :
       Algebra.Etale (ResidueField A) (ResidueField A ⊗[A] (maximalIdeal A).affineBlowup x S)
   ```
   Difference: the PR's included section variables `hm hrel` are written as explicit binders
   in the same order; the elaborated signature is the same.

PR #23800's other declarations (`finrank_tensor_affineBlowup`, `adjoinRootEquivTensorAffineBlowup`,
`TauCeti.AlgebraicGeometry.isIso_affineBlowupι_of_sq_mem`) are not consumed and not stubbed.
When #23800 lands, delete `TauCeti/Lookahead/` and replace the import
`TauCeti.Lookahead.NormalizationExactSequence.Stubs` in `TauCeti/RingTheory/Node/Resolution.lean`
by `TauCeti.RingTheory.Node.ExceptionalFiber`.

## Splits

1. **`feat: the cokernel of an algebra modulo an ideal inside the base`** — after: none (can be
   opened now; it needs no supplier).
   File: `TauCeti/RingTheory/Conductor.lean` (+62 lines). Adds
   `TauCeti.Algebra.map_conductor_le_one` (the extension of the conductor lies in the image of
   `A`), `TauCeti.Algebra.quotientOneEquivOfLE` (for an ideal `I ⊆ A` of `B`,
   `B / A ≃ₗ[A] (B / I) / A`, the conductor square of a normalization) and
   `TauCeti.Algebra.quotientOneEquivOfLE_mk`.
2. **`feat: one blowup normalizes a node: conductor, cokernel and regularity`** — after: 1 (and
   the supplier #23800 on `main`).
   Files: new `TauCeti/RingTheory/Node/Resolution.lean` (428 lines), and
   `TauCeti/RingTheory/Ideal/AffineBlowup.lean` (+10 lines). Adds
   `Ideal.algebraMap_affineBlowup_injective`, `TauCeti.maximalIdeal_le_conductor_affineBlowup`,
   `TauCeti.conductor_affineBlowup_eq_maximalIdeal`, `TauCeti.affineBlowupQuotientEquiv`,
   `TauCeti.affineBlowupQuotientEquiv_mk_divBy`, `TauCeti.affineBlowupQuotientEquivFiber`,
   `TauCeti.isRegularLocalRing_localization_affineBlowup`,
   `TauCeti.isDiscreteValuationRing_localization_affineBlowup` and
   `TauCeti.integralClosure_eq_affineBlowup`.
3. **`feat: the normalization exact sequence of a proper nodal curve`** — after: 1, 2.
   *Not on the branch.* Carries the target's exported theorems. For a proper nodal curve
   `X/K`: the normalization `ν : X̃ → X` (locally the blowup of split 2 at each node, the
   identity elsewhere), finite with regular source; `ν.conductor`
   (`TauCeti/AlgebraicGeometry/IdealSheaf/Conductor.lean`) equals the ideal sheaf of
   `Sing(X/K)`, by `conductor_affineBlowup_eq_maximalIdeal` and `Algebra.conductor_eq_map`; and
   the sequence `0 → 𝒪_X → ν_*𝒪_X̃ → Q → 0` of
   `TauCeti/AlgebraicGeometry/Modules/StructureSheafSequence.lean`, with `Q` identified, by split
   1 over affine opens, with the direct image from `Sing(X/K)` of the functions on the branch
   scheme modulo those on `Sing(X/K)`, an invertible `𝒪_{Sing}`-module since the branch scheme is
   finite étale of degree two. If it exceeds 600 lines it splits further into the construction
   of `ν` with its conductor, and the sequence.

## What remains

Proved here (splits 1–2): the normalization of a node in the local shape `𝔪 = (x, y)`,
`a x² + b x y + y² = 0`, `b² - 4a` a unit, as one blowup, with its regularity, conductor and
cokernel. Remaining:

* that the local ring of a nodal curve over a field at a node has that shape (a coordinate change
  making the `y²`-coefficient a unit, `x` a nonzerodivisor, and `𝔪` not principal). PR #23800
  lists this as remaining work of the supplier `node-branch-splitting`, which pins no form for it,
  so it is not stubbed; if it does not land there it belongs to split 3;
* split 3, the globalization over `Sing(X/K)` and the scheme-level exact sequence for `𝒪_X`.
