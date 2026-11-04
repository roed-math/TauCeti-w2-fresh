<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"chow-proper-pushforward","main":"81820d6b555f126c9030bfa46d25d61690af4fb6","status":"partial","suppliers":["chow-group"],"splits":[{"n":1,"after":[],"title":"feat: pushforward of cycles over a field and degree of zero-cycles"},{"n":2,"after":[1],"title":"feat: proper pushforward of a principal divisor is the divisor of the norm"},{"n":3,"after":[1],"title":"feat: principal divisors push forward to zero along dimension-dropping proper maps"},{"n":4,"after":[1,2,3],"title":"feat: proper pushforward of Chow groups and the degree of zero-cycles"}]}-->

# Lookahead: `chow-proper-pushforward` (SchemeAndStackFoundations §5.2)

Target (README §5.2, *Chow.properPushforward*): for `f : X → Y` proper, Mathlib's
`AlgebraicCycle.map` with residue-degree weights preserves rational equivalence and gives
`f_* : CH_k(X) → CH_k(Y)` with `(g f)_* = g_* f_*`; for `X` proper over `k`,
`deg : CH_0(X) → ℤ` is well defined and `deg f_* = deg` (Fulton 1998, Theorem 1.4; Stacks,
Sections 42.12, 42.20, 42.41). The target has no pinned form in `Suggested.lean`; the names
below follow the README's *Chow.properPushforward* and the neighbouring code on `main`
(`TauCeti/AlgebraicGeometry/Chow/{Basic,ClosedImmersion}.lean`).

Built on `main` at `81820d6b555f126c9030bfa46d25d61690af4fb6`.

**Status: partial.** The cycle level is proved without stubs beyond the one below: the
pushforward of `n`-cycles over a field, its functoriality, the degree of zero-cycles, and
`deg f_* = deg`. Still to do: proper pushforward preserves rational equivalence (Fulton,
Proposition 1.4), and the descent to Chow groups.

## The supplier `chow-group` and its stub

Everything in `Suggested.lean` §5.1 that this target consumes (`Chow.cyclesOfDimension`,
`Chow.RatEquiv`, `Chow.ChowGroup`, `Chow.cycleClass`) is already on `main` (merged by #22663,
`TauCeti/AlgebraicGeometry/Chow/Basic.lean`), so none of it is stubbed. On `main`, unlike
`Suggested.lean`, these take no field `κ` (they need only `IsLocallyNoetherian X`) and
`RatEquiv` is defined through the structure `Chow.RatEquivFamily`. The target uses `main`'s
forms. The rest of `chow-group` is in flight as PR #27340 (the divisor class comparison).
That PR also adds one general lemma that this target needs, and that lemma is the only stub
(`TauCeti/Lookahead/ChowProperPushforward/Stubs.lean`).

### `TauCeti.height_eq_topologicalKrullDim_closure_singleton`

- `Suggested.lean` signature: none. `Suggested.lean` does not pin this lemma; it is a helper
  that PR #27340 adds to `TauCeti/Topology/KrullDimension/Basic.lean`.
- Stub, copied from PR #27340's diff:

  ```lean
  attribute [local instance] specializationPreorder in
  theorem height_eq_topologicalKrullDim_closure_singleton {α : Type*} [TopologicalSpace α]
      [QuasiSober α] [T0Space α] (x : α) :
      (height x : WithBot ℕ∞) = topologicalKrullDim (closure ({x} : Set α)) := by
    sorry
  ```

- Source: PR #27340's diff. Differences: none in the statement. The stub lives in
  `TauCeti/Lookahead/ChowProperPushforward/Stubs.lean` (namespace `TauCeti`), not in
  `TauCeti/Topology/KrullDimension/Basic.lean`. Only `TauCeti/AlgebraicGeometry/Scheme/LocalDimension.lean`
  imports it. When the port runs, it deletes the stub file and replaces that
  `public import TauCeti.Lookahead.ChowProperPushforward.Stubs` with the landed module
  (`TauCeti.Topology.KrullDimension.Basic`, if it is not already imported transitively).
- Why it is a stub and not proved here: it is PR #27340's declaration. Proving it on this
  branch would duplicate the supplier.

The final split will also use PR #27340's `Chow.RatEquivFamily.component_def` (on `main` the body
of `RatEquivFamily.component` is not exposed outside `Chow/Basic.lean`). Nothing on this branch
uses it yet, so it is not stubbed.

## Split plan

### Split 1: `feat: pushforward of cycles over a field and degree of zero-cycles` (after: none; needs PR #27340 on `main`)

Proved on this branch, about 390 lines.

- `TauCeti/Algebra/BigOperators/Finprod.lean`: `TauCeti.finprod_mem_fiberwise` /
  `TauCeti.finsum_mem_fiberwise`. These regroup a product over a preimage `g ⁻¹' t` by the
  fibres over `t`, and are derived from the existing `TauCeti.finprod_fiberwise`.
- `TauCeti/AlgebraicGeometry/Scheme/BaseAlgebra.lean`: `Scheme.Hom.residueFieldMap_algebraMap`
  (residue field maps of a morphism over `Spec k` are `k`-linear).
- `TauCeti/AlgebraicGeometry/Scheme/LocalDimension.lean`:
  `TauCeti.AlgebraicGeometry.height_eq_toNat_trdeg_residueField` (`height x = trdeg_k κ(x)`) and
  `TauCeti.AlgebraicGeometry.height_apply_eq_height_of_residueDegree_ne_zero`. For a morphism
  over a field between schemes locally of finite type, a point with finite residue extension has
  the dimension of its image, because both are `trdeg_k κ(x)`. This is where the supplier lemma
  is used.
- `TauCeti/AlgebraicGeometry/AlgebraicCycle/Basic.lean` (namespace
  `AlgebraicGeometry.AlgebraicCycle`):
  - `finite_preimage_singleton_inter_support`
  - `map_add`
  - `map_comp` (functoriality of Mathlib's `map` when the multiplicities are multiplicative)
  - `locallyFinite_support_map`
  - `map_locallyFiniteSum`
  - `map_height_comp_of_isClosedImmersion`, generalised from two closed immersions to a closed
    immersion followed by any quasi-compact morphism and now derived from `map_comp`. The one
    caller, `Chow.ChowGroup.pushforward_comp`, is unchanged.
- `TauCeti/AlgebraicGeometry/Chow/Pushforward.lean` (new, namespace `TauCeti.AlgebraicGeometry.Chow`):
  - `mapCoeff_height_eq_residueDegree`, `map_height_apply`, `map_height_comp`
  - `cyclesMap k f : cyclesOfDimension X n →+ cyclesOfDimension Y n` for `f` quasi-compact over
    `k`, with `coe_cyclesMap`, `cyclesMap_apply`, `cyclesMap_id`, `cyclesMap_comp`, and
    `cyclesMap_eq_cyclesPushforward` (agreement with `main`'s closed-immersion pushforward)
  - `cyclesDegree k X : cyclesOfDimension X 0 →+ ℤ` (Mathlib's `AlgebraicCycle.degree` of the
    structure morphism) for quasi-compact `X`, with `cyclesDegree_apply`,
    `cyclesDegree_eq_cyclesMap_apply`, and `cyclesDegree_cyclesMap` (`deg f_* α = deg α`).

### Split 2: `feat: proper pushforward of a principal divisor is the divisor of the norm` (after: 1)

Not started. Let `f : W → W'` be a proper surjective morphism of integral schemes of the same
dimension, locally of finite type over `k`. Then `κ(W)/κ(W')` is finite and
`f_* div r = div (Norm_{κ(W)/κ(W')} r)` (Fulton, Proposition 1.4(b)). The proof reduces to the
codimension-one points of `W'`. Over such a point, `f` is finite near the point (proper and
quasi-finite). It then uses the one-dimensional local-algebra identity
`ord_A(N(r)) = Σ_m [κ(m) : κ(A)] ord_{B_m}(r)` for `B` finite over a one-dimensional Noetherian
local domain `A` (Fulton, Appendix A.3).
Expected files: a new `TauCeti/AlgebraicGeometry/Chow/Norm.lean`, plus a ring-theory file for the
order/norm identity.

### Split 3: `feat: principal divisors push forward to zero along dimension-dropping proper maps` (after: 1)

Not started. If `dim f(W) < dim W`, then `f_* div r = 0` (Fulton, Proposition 1.4(a)). On
`k`-cycles this is automatic for `dim f(W) < k` by the grading of `Chow.cyclesMap`. The case
`dim f(W) = k` reduces to the fact that a principal divisor on a proper curve over the function
field of `f(W)` (the generic fibre) has degree zero. Splits 2 and 3 are independent and can be
opened together.

### Split 4 (final): `feat: proper pushforward of Chow groups and the degree of zero-cycles` (after: 1, 2, 3)

Not started; this is the only split that completes the target. File: a new
`TauCeti/AlgebraicGeometry/Chow/ProperPushforward.lean`.

- `Chow.cyclesMap_mem_ratEquiv`: for `f` proper over `k`, `cyclesMap k f` maps
  `RatEquiv X n` into `RatEquiv Y n`. Proof sketch: write the cycle of a `RatEquivFamily` as a
  locally finite sum with `RatEquivFamily.component_def` and `map_locallyFiniteSum`. Rewrite
  each summand as `(i_j ≫ f)_* div r_j` with `map_height_comp_of_isClosedImmersion`. Apply
  splits 2 and 3 to each summand. Collect the nonzero summands into the family of reduced images
  `f(W_j)`, which is locally finite by quasi-compactness of `f`, as in
  `locallyFinite_support_map`.
- `Chow.ChowGroup.properPushforward k f : ChowGroup X n →+ ChowGroup Y n`, with
  `properPushforward_cycleClass`, `properPushforward_id` and `properPushforward_comp`.
- `Chow.ChowGroup.degree k X : ChowGroup X 0 →+ ℤ` for `X` proper over `k`, with
  `degree_cycleClass` and `degree_properPushforward` (`deg f_* = deg`).
- The README checks `test_pushforward_degree` and `test_pushforward_not_proper`.

## What remains (status `partial`)

Proved: all of split 1. Remaining: splits 2–4. In particular, the statement that proper
pushforward preserves rational equivalence (Fulton, Proposition 1.4; Theorem 1.4) is not proved,
so `f_*` and `deg` are not yet defined on Chow groups.
