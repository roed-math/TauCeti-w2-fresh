<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"chow-proper-pushforward","main":"52f9d081237dadaf6d4eae13629281f7faa37d54","status":"partial","suppliers":["chow-group"],"splits":[{"n":1,"after":[],"title":"feat: pushforward of cycles over a field and degree of zero-cycles"},{"n":2,"after":[],"title":"feat: cokernel length of injective endomorphisms"},{"n":3,"after":[2],"title":"feat: cokernel length is the order of the determinant over one-dimensional domains"},{"n":4,"after":[3],"title":"feat: the order of a norm is a sum of local orders (Fulton A.3)"},{"n":5,"after":[1],"title":"feat: generically finite proper morphisms are finite in codimension one"},{"n":6,"after":[1,4,5],"title":"feat: proper pushforward of a principal divisor is the divisor of the norm"},{"n":7,"after":[1,6],"title":"feat: principal divisors push forward to zero along dimension-dropping proper maps"},{"n":8,"after":[1,2,3,4,5,6,7],"title":"feat: proper pushforward of Chow groups and the degree of zero-cycles"}]}-->

# Lookahead: `chow-proper-pushforward` (SchemeAndStackFoundations §5.2)

Target (README §5.2, *Chow.properPushforward*): for `f : X → Y` proper, Mathlib's
`AlgebraicCycle.map` with residue-degree weights preserves rational equivalence and gives
`f_* : CH_k(X) → CH_k(Y)` with `(g f)_* = g_* f_*`; for `X` proper over `k`,
`deg : CH_0(X) → ℤ` is well defined and `deg f_* = deg` (Fulton 1998, Theorem 1.4; Stacks,
Sections 42.12, 42.20, 42.41). The target has no pinned form in `Suggested.lean`; the names
below follow the README's *Chow.properPushforward* and the neighbouring code on `main`
(`TauCeti/AlgebraicGeometry/Chow/{Basic,ClosedImmersion}.lean`).

Built on `main` at `52f9d081237dadaf6d4eae13629281f7faa37d54`.

**Status: partial.** The cycle level is proved without stubs beyond the one below: the
pushforward of `n`-cycles over a field, its functoriality, the degree of zero-cycles, and
`deg f_* = deg` (split 1). The commutative algebra behind Fulton, Proposition 1.4(b) is proved
in full (splits 2–4, no stubs): the determinant lemma of Fulton's Appendix A.2 (the order of a
determinant is a cokernel length, over any Noetherian domain of dimension at most one), and the
order of a norm of Appendix A.3 in its final form, `ord_A N_{L/K}(r)
= Σ_m [B ⧸ m : κ(A)] ord_{R_m}(r)` for every nonzero `r` in the fraction field of a domain `B`
finite over a local `A`, with the orders taken in arbitrary localizations `R_m` of `B` (for
instance the local rings of a scheme). Split 5 proves the first scheme-level inputs of
Proposition 1.4: a dimension-preserving point has a finite residue field extension, so a dominant
morphism of integral schemes of the same dimension, locally of finite type over `k`, makes
`K(X)` finite over `K(Y)`; and such a morphism, if proper, is finite over a neighbourhood of every
point of codimension one. Still to do: the scheme-level statements of Proposition 1.4(a) and (b)
and the descent to Chow groups (splits 6–8).

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
  imports it (used by `height_eq_toNat_trdeg_residueField` in split 1 and by
  `functionFieldMap_finite_of_topologicalKrullDim_eq` in split 5). When the port runs, it
  deletes the stub file and replaces that
  `public import TauCeti.Lookahead.ChowProperPushforward.Stubs` with the landed module
  (`TauCeti.Topology.KrullDimension.Basic`, if it is not already imported transitively).
- Why it is a stub and not proved here: it is PR #27340's declaration. Proving it on this
  branch would duplicate the supplier.

PR #27340 also adds `Chow.RatEquivFamily.component_def` (on `main` the body of
`RatEquivFamily.component` is not exposed outside `Chow/Basic.lean`). The final split does not need
it: `RatEquivFamily.component_apply` and `component_apply_eq_zero_of_notMem_range`, already on
`main`, determine every summand. So it is not stubbed.

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

### Split 2: `feat: cokernel length of injective endomorphisms` (after: none)

Proved on this branch. File `TauCeti/RingTheory/Length/Endomorphism.lean` (new, 191 lines,
namespace `TauCeti`), the invariant `e_A(φ, M) = length (M ⧸ φ M)` of Fulton, Appendix A.2:

- `length_quotient_eq_length_quotient_comap_subtype_add`, `length_quotient_comap_subtype_range_map`,
  `range_restrict_eq_comap_subtype_map` (filtration and transport helpers);
- `length_quotient_range_comp`: `e(φ ∘ ψ) = e(φ) + e(ψ)` for injective `φ`;
- `length_quotient_range_restrict`: `e` is unchanged on passing to a `φ`-stable submodule of
  finite colength;
- `length_quotient_lsmul_pi`: `length (Aⁿ ⧸ aAⁿ) = n * ord_A a`;
- `exists_linearIndependent_smul_mem_span`: a finitely generated module over a domain has a free
  submodule of full rank with torsion quotient;
- `length_quotient_lsmul_eq_finrank_mul_ord`: `length (M ⧸ aM) = rank M * ord_A a` for `M`
  finitely generated torsion-free over a Noetherian domain of dimension at most one.

Splits 2–4 do not use the stub and do not depend on split 1, so split 2 can open together with
split 1 as soon as the port starts.

### Split 3: `feat: cokernel length is the order of the determinant over one-dimensional domains` (after: 2)

Proved on this branch. File `TauCeti/RingTheory/Length/Determinant.lean` (new, 427 lines). The
matrix, basis and linear-map statements are in the Mathlib namespaces of their first explicit
argument (naming rubric), the rest in `TauCeti`:

- `Matrix.length_quotient_range_diagonal_mulVecLin` (moved here unchanged, same name, from the
  deleted `TauCeti/LinearAlgebra/Matrix/SmithNormalForm/Length.lean`);
- `Module.Basis.length_quotient_range_eq_length_quotient_range_toMatrix` (cokernel of an
  endomorphism = that of its matrix);
- `TauCeti.Ring.ord_prod` (order of a product of nonzero elements);
- `Matrix.eq_zero_of_map_mul_of_diagonal_of_transvection`: a function on nonsingular matrices
  over a domain that is additive under products and vanishes on nonsingular diagonal matrices and
  on transvections vanishes (extension to the fraction field and Mathlib's transvection
  decomposition);
- `Matrix.length_quotient_range_mulVecLin_ne_top` and
  `Matrix.length_quotient_range_mulVecLin_eq_ord_det`: over a Noetherian domain of dimension at
  most one, `length (Aⁿ ⧸ ψ Aⁿ) = ord_A (det ψ)`. This **generalises in place** the previous
  principal-ideal-domain theorem of the same name (Smith normal form proof), which is removed
  together with its file; its one caller, `TauCeti/RingTheory/Trace/Length.lean`, keeps the same
  name and only changes its import to `TauCeti.RingTheory.Length.Determinant`;
- `LinearMap.ordFrac_det_eq_coe_of_length_eq` (Fulton's determinant lemma): for a finitely
  generated `A`-lattice `M` spanning a `K`-vector space `V` and a nonsingular `K`-linear `φ` with
  `φ M ⊆ M`, `ordFrac_A (det φ) = length (M ⧸ φ M)`.

### Split 4: `feat: the order of a norm is a sum of local orders (Fulton A.3)` (after: 3)

Proved on this branch. Files `TauCeti/RingTheory/Length/Norm.lean` (new, 450 lines) and
`TauCeti/RingTheory/OrderOfVanishing.lean` (existing, +19 lines):

- `TauCeti.Ring.ord_ringEquiv` (in `OrderOfVanishing.lean`): `Ring.ord` is invariant under ring
  isomorphisms (a semilinear bijection of the quotients, `LinearMap.length_eq_of_bijective`);
- `TauCeti.span_range_algebraMap_eq_top`: for `B` integral over `A`, `Frac B` is the `K`-span
  of `B`;
- `TauCeti.ordFrac_norm_eq_coe_of_length_eq`: for `B` a domain finite over `A` (Noetherian domain
  of dimension at most one) and `b ≠ 0`, `ordFrac_A (N_{L/K} b) = length_A (B ⧸ bB)`;
- `Localization.localRingHom_surjective_of_surjective`,
  `TauCeti.length_localization_quotient_span_singleton` (`(R ⧸ bR)_q ≅ R_m ⧸ b R_m`, so its
  length is `ord_{R_m} b`), `Ideal.length_residueField_localization_quotient`;
- `TauCeti.exists_maximalSpectrum_comap_mk_eq` (a maximal ideal containing `b` comes from
  `B ⧸ bB`), `TauCeti.isFiniteLength_quotient_span_singleton` (`B ⧸ bB` has finite `A`-length),
  `TauCeti.finite_setOf_mem_maximalSpectrum` (`b ≠ 0` lies in finitely many maximal ideals);
- `TauCeti.length_quotient_span_singleton_eq_finsum` (sum over the maximal ideals of the Artinian
  ring `B ⧸ bB`) and `TauCeti.length_quotient_span_singleton_eq_finsum_ord`: for `A` local,
  `length_A (B ⧸ bB) = Σᶠ m : MaximalSpectrum B, ord_{B_m}(b) * length_A κ(B_m)`;
- `TauCeti.length_residueField_localization_eq` (`length_A κ(B_m) = length_A (B ⧸ m)`),
  `TauCeti.ordFrac_algebraMap_eq_ofAdd_ord` (the order of `b` in any localization `R m` of `B` at
  `m` is its order in `B_m`), `TauCeti.mulSupport_ordFrac_pow_subset`;
- `TauCeti.ordFrac_norm_algebraMap_eq_finprod` and, the main statement,
  `TauCeti.ordFrac_norm_eq_finprod`: for `r ≠ 0` in `L`,
  `Ring.ordFrac A (Algebra.norm K r) = ∏ᶠ m, Ring.ordFrac (R m) r ^ (length_A (B ⧸ m)).toNat`,
  for any family `R m` of localizations of `B` at its maximal ideals with `R m → L` compatible.
  The family carries the instance binders that `Ring.ordFrac (R m)` needs to be stated
  (`IsDomain`, `IsNoetherianRing`, `Ring.KrullDimLE 1`, `IsFractionRing (R m) L`). They follow
  from `IsLocalization.AtPrime` and the tower but are not instances; a generality reviewer may
  ask for them to be derived. At the scheme level (split 6) the stalks carry all of them as
  instances.

### Split 5: `feat: generically finite proper morphisms are finite in codimension one` (after: 1)

Proved on this branch, about 230 lines. Needs split 1 (`height_eq_toNat_trdeg_residueField`) and,
through it, PR #27340 on `main`.

- `TauCeti/AlgebraicGeometry/Morphisms/Dominant.lean`: `Scheme.Hom.functionFieldMap_def` (the
  pullback of rational functions is `stalkSpecializes ≫ stalkMap` at the generic point; the
  definition is not exposed, so downstream proofs need this unfolding lemma).
- `TauCeti/AlgebraicGeometry/Scheme/LocalDimension.lean` (namespace
  `TauCeti.AlgebraicGeometry`):
  - `essFiniteType_residueField` (instance): `κ(x)` is essentially of finite type over `k`;
  - `residueDegree_ne_zero_of_height_apply_eq`: for `f` over `k` between schemes locally of finite
    type, `height (f x) = height x` implies `f.residueDegree x ≠ 0` (the converse of split 1's
    `height_apply_eq_height_of_residueDegree_ne_zero`);
  - `functionFieldMap_finite_of_topologicalKrullDim_eq`: a dominant morphism of integral schemes
    of the same dimension makes `K(X)` finite over `K(Y)`, the finiteness that the norm
    `N_{K(W)/K(W')}` of Proposition 1.4(b) needs;
  - `height_apply_le_height`: a morphism over `k` does not increase heights;
  - `finite_preimage_singleton_of_height_eq`: for `f` quasi-compact over `k`, a fibre all of whose
    points have the height of `y` is finite (it is `T₁`, and it is the underlying space of the
    Noetherian quasi-sober fibre scheme);
  - `exists_isFinite_morphismRestrict_of_height_eq`: for `f` proper, `f` is then finite over an
    open neighbourhood of `y` (Mathlib's
    `exists_isFinite_morphismRestrict_of_finite_preimage_singleton`, Stacks 02UP);
  - `exists_isFinite_morphismRestrict_of_height_add_one`: a proper dominant morphism of integral
    schemes of dimension `n + 1` is finite over a neighbourhood of every point of height `n`.
- `TauCeti/Topology/NoetherianSpace/ClosedPoints.lean`:
  `TauCeti.finite_of_noetherianSpace_of_t1Space` (a Noetherian quasi-sober `T₁` space is finite).

### Split 6: `feat: proper pushforward of a principal divisor is the divisor of the norm` (after: 1, 4, 5)

Not started beyond its first input, which is now in split 5. Let `f : W → W'` be a proper
surjective morphism of integral schemes of the same dimension, locally of finite type over `k`. Then `κ(W)/κ(W')` is finite (split 5) and
`f_* div r = div (Norm_{κ(W)/κ(W')} r)` (Fulton, Proposition 1.4(b)). At a codimension-one point
`y` of `W'`, `f` is finite over a neighbourhood of `y` (proper and quasi-finite there), so with
`A = 𝒪_{W',y}` and `B` the semilocal ring of `W` over `y`, split 4 gives the coefficient
identity: `ordFrac_norm_eq_finprod` with `R m = 𝒪_{W,x}` for the points `x` of `W` over `y`
(whose orders are Mathlib's `Scheme.ord`) and `length_A (B ⧸ m) = [κ(x) : κ(y)]`. The
finiteness of `f` over a neighbourhood of `y` is split 5's
`exists_isFinite_morphismRestrict_of_height_add_one`. The scheme-level input still to prove is the
identification, over an affine open `V ∋ y` with `f⁻¹ V = Spec B` finite over `Γ(V)`, of the
semilocal ring `B_y = B ⊗ 𝒪_{W',y}` with a domain finite over `A = 𝒪_{W',y}` whose fraction field
is `K(W)`, whose maximal ideals are the points of `W` over `y`, and whose localizations there are
the stalks `𝒪_{W,x}` compatibly with `K(W)`; then `length_A (B_y ⧸ m_x) = [κ(x) : κ(y)]`.
Expected file: a new `TauCeti/AlgebraicGeometry/Chow/Norm.lean`.

### Split 7: `feat: principal divisors push forward to zero along dimension-dropping proper maps` (after: 1, 6)

Not started. If `dim f(W) < dim W`, then `f_* div r = 0` (Fulton, Proposition 1.4(a)). On
`k`-cycles this is automatic for `dim f(W) < k` by the grading of `Chow.cyclesMap`. The case
`dim f(W) = k` reduces to the fact that a principal divisor on a proper curve over the function
field of `f(W)` (the generic fibre) has degree zero, which is split 6 applied to the finite map
from the curve to `ℙ¹` given by `r` (Fulton's proof of Proposition 1.4(a)).

### Split 8 (final): `feat: proper pushforward of Chow groups and the degree of zero-cycles` (after: 1, 2, 3, 4, 5, 6, 7)

Not started; this is the only split that completes the target. File: a new
`TauCeti/AlgebraicGeometry/Chow/ProperPushforward.lean`.

- `Chow.cyclesMap_mem_ratEquiv`: for `f` proper over `k`, `cyclesMap k f` maps
  `RatEquiv X n` into `RatEquiv Y n`. Proof sketch: write the cycle of a `RatEquivFamily` as a
  locally finite sum (its summands are determined by `RatEquivFamily.component_apply` and
  `component_apply_eq_zero_of_notMem_range`, so `component_def` is not needed), push it forward
  with `map_locallyFiniteSum`, and rewrite each summand as `(i_j ≫ f)_* div r_j` with
  `map_height_comp_of_isClosedImmersion`. Splits 6 and 7 turn each summand into `0` or
  `(i_V)_* div (N r_j)` on `V = f(W_j)`. Group the nonzero summands by `V`: only finitely many
  `W_j` meet the quasi-compact `f⁻¹(V)`, so the products of the norms over each `V` give a family
  of reduced images that is locally finite, as in `locallyFinite_support_map`.
- `Chow.ChowGroup.properPushforward k f : ChowGroup X n →+ ChowGroup Y n`, with
  `properPushforward_cycleClass`, `properPushforward_id` and `properPushforward_comp`.
- `Chow.ChowGroup.degree k X : ChowGroup X 0 →+ ℤ` for `X` proper over `k`, with
  `degree_cycleClass` and `degree_properPushforward` (`deg f_* = deg`).
- The README checks `test_pushforward_degree` and `test_pushforward_not_proper`.

## What remains (status `partial`)

Proved: splits 1–5, including the finiteness of a proper generically finite morphism over a
neighbourhood of each codimension-one point. Remaining: splits 6–8. In particular, the statement that proper pushforward
preserves rational equivalence (Fulton, Proposition 1.4; Theorem 1.4) is not proved, so `f_*` and `deg` are not yet
defined on Chow groups.
