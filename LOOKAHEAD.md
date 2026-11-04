<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"chow-proper-pushforward","main":"52f9d081237dadaf6d4eae13629281f7faa37d54","status":"partial","suppliers":["chow-group"],"splits":[{"n":1,"after":[],"title":"feat: pushforward of cycles over a field and degree of zero-cycles"},{"n":2,"after":[],"title":"feat: cokernel length of injective endomorphisms"},{"n":3,"after":[2],"title":"feat: cokernel length is the order of the determinant over one-dimensional domains"},{"n":4,"after":[3],"title":"feat: the order of a norm is a sum of local orders (Fulton A.3)"},{"n":5,"after":[4],"title":"feat: the order of a norm over the primes above a prime"},{"n":6,"after":[1],"title":"feat: generically finite proper morphisms are finite in codimension one"},{"n":7,"after":[1,5,6],"title":"feat: proper pushforward of a principal divisor is the divisor of the norm"},{"n":8,"after":[1,7],"title":"feat: principal divisors push forward to zero along dimension-dropping proper maps"},{"n":9,"after":[1,2,3,4,5,6,7,8],"title":"feat: proper pushforward of Chow groups and the degree of zero-cycles"}]}-->

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
in full (splits 2–5, no stubs): the determinant lemma of Fulton's Appendix A.2 (the order of a
determinant is a cokernel length, over any Noetherian domain of dimension at most one), the
order of a norm of Appendix A.3 in its local form, `ord_A N_{L/K}(r)
= Σ_m [B ⧸ m : κ(A)] ord_{R_m}(r)` for `B` finite over a local `A` (split 4), and in its global
form over the primes above a prime (split 5): for `B₀` a domain finite over a domain `A₀`, `p` a
prime of `A₀` with `(A₀)_p` Noetherian of dimension at most one, and `R q` any localizations of
`B₀` at the primes `q` over `p` (for instance the local rings of a scheme at the points of a
fibre), `ord_{(A₀)_p} N(r) = Σ_q [κ(R q) : κ(p)] ord_{R q}(r)`. Split 6 proves the first
scheme-level inputs of Proposition 1.4: a dimension-preserving point has a finite residue field
extension, so a dominant morphism of integral schemes of the same dimension, locally of finite
type over `k`, makes `K(X)` finite over `K(Y)`; and such a morphism, if proper, is finite over a
neighbourhood of every point of codimension one. Split 7 is started: the points of the fibre over
`y ∈ V` (for `V` and `f⁻¹ V` affine) are identified with the primes of `Γ(f⁻¹ V)` over the prime
of `y`. Still to do: the rest of the scheme-level statements of Proposition 1.4(a) and (b) and
the descent to Chow groups (splits 7–9).

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
  `functionFieldMap_finite_of_topologicalKrullDim_eq` in split 6). When the port runs, it
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

Splits 2–5 do not use the stub and do not depend on split 1, so split 2 can open together with
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
  ask for them to be derived. At the scheme level (split 7) the stalks carry all of them as
  instances.

### Split 5: `feat: the order of a norm over the primes above a prime` (after: 4)

Proved on this branch, about 240 lines, no stubs.

- `TauCeti/RingTheory/Localization/AtPrime/Extension.lean` (new, 77 lines, namespace
  `IsLocalization.AtPrime`, beside Mathlib's `Mathlib/RingTheory/Localization/AtPrime/Extension.lean`;
  the directory sits beside `TauCeti/RingTheory/Localization/AtPrime.lean` as `Fibers/` sits beside
  `Fibers.lean` on `main`): `maximalSpectrumEquivPrimesOver p Rₚ Sₚ : MaximalSpectrum Sₚ ≃
  p.primesOver S` for `Sₚ` integral over `Rₚ` (`m ↦ m ∩ S`, inverse `q ↦ q Sₚ`, using Mathlib's
  `Ideal.disjoint_primeCompl_of_liesOver`), with the `@[simp]` lemmas
  `coe_maximalSpectrumEquivPrimesOver_apply` and `maximalSpectrumEquivPrimesOver_symm_apply_asIdeal`
  (proved by `(rfl)`; the body is not exposed). Mathlib's
  `Localization.AtPrime.primesOverEquivPrimesOver` is the Dedekind-domain case.
- `TauCeti/RingTheory/Length/Norm/PrimesOver.lean` (new, 162 lines, namespace `TauCeti`;
  `Norm.lean` from split 4 is unchanged):
  - `ordFrac_norm_eq_finprod_of_isLocalization`: split 4's `ordFrac_norm_eq_finprod` when `B` is
    a localization of a ring `B₀` and the orders are taken in localizations `R m` of `B₀` at
    `m ∩ B₀` (each `R m` is given the `B`-algebra structure of `B_m ≃ₐ[B₀] R m`, and split 4
    applies);
  - `ordFrac_norm_eq_finprod_primesOver` (the global form of Fulton A.3): for `B₀` a domain finite
    over a domain `A₀` with `A₀ → B₀` injective, `p` a prime of `A₀`, `A` a localization of `A₀`
    at `p` that is Noetherian of dimension at most one, and localizations `R q` of `B₀` at each
    `q ∈ p.primesOver B₀` that are `A`-algebras compatibly with `A₀`,
    `Ring.ordFrac A (Algebra.norm K r) = ∏ᶠ q, Ring.ordFrac (R q) r ^ (length_A κ(R q)).toNat`.
    The semilocal ring `(B₀)_p` is built inside the proof, and the residue degrees are compared
    through `B ⧸ m ≅ κ(B_m) ≅ κ(R q)` (Mathlib's `IsLocalRing.ResidueField.mapAlgEquiv`). The
    binder `[∀ q, IsLocalRing (R q)]` follows from `IsLocalization.AtPrime` but is not an
    instance, and is needed to state `κ(R q)`; the stalks of a scheme carry it as an instance.

### Split 6: `feat: generically finite proper morphisms are finite in codimension one` (after: 1)

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

### Split 7: `feat: proper pushforward of a principal divisor is the divisor of the norm` (after: 1, 5, 6)

Started. Let `f : W → W'` be a proper surjective morphism of integral schemes of the same
dimension, locally of finite type over `k`. Then `κ(W)/κ(W')` is finite (split 6) and
`f_* div r = div (Norm_{κ(W)/κ(W')} r)` (Fulton, Proposition 1.4(b)). At a codimension-one point
`y` of `W'`, `f` is finite over an affine neighbourhood `V` of `y` (split 6's
`exists_isFinite_morphismRestrict_of_height_add_one`), so `A₀ = Γ(W', V) → B₀ = Γ(W, f⁻¹ V)` is
finite and injective (`Scheme.Hom.appLE_injective_of_isDominant` on `main`).

Proved on this branch: `TauCeti/AlgebraicGeometry/AffineScheme/PrimesOver.lean` (new, 85 lines,
namespace `AlgebraicGeometry`; the directory sits beside `AffineScheme.lean` as `Fibers/` sits
beside `Fibers.lean` on `main`):

- `IsAffineOpen.primeIdealOf_fromSpec` (the prime of the point `fromSpec q` is `q`);
- `IsAffineOpen.preimageSingletonEquivPrimesOver f hV hU hUV hy : f ⁻¹' {y} ≃
  (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primesOver Γ(X, U)` for affine opens `V ∋ y` and
  `U = f⁻¹ V` (through `f.appLE V U`; Mathlib's `IsAffineOpen.comap_primeIdealOf_appLE`), with
  the `@[simp]` lemmas `coe_preimageSingletonEquivPrimesOver_apply` and
  `coe_preimageSingletonEquivPrimesOver_symm_apply`.

Still to prove, in a new `TauCeti/AlgebraicGeometry/Chow/Norm.lean`: the coefficient identity
`ord_y N(r) = Σ_{x ∈ f⁻¹{y}} [κ(x) : κ(y)] ord_x(r)`, by applying split 5's
`ordFrac_norm_eq_finprod_primesOver` with `A = 𝒪_{W',y}` (Mathlib's
`IsAffineOpen.isLocalization_stalk`), `K = K(W')`, `L = K(W)` (`Algebra K L` from
`functionFieldMap`), and `R q = 𝒪_{W,x}` for `x` the point of `q` under
`preimageSingletonEquivPrimesOver` (an `A`-algebra through `stalkMap` and `f x = y`). This needs:
the scalar towers among `Γ(W', V)`, `Γ(W, f⁻¹ V)`, the two stalks and the two function fields
(`germToFunctionField_functionFieldMap`, `germ_stalkMap`); `coheight x = 1` for the points over
`y`, so that Mathlib's `Scheme.ord` at `x` is `Ring.ordFrac 𝒪_{W,x}` (`ringKrullDim_stalk_eq_coheight`
and the integrality of `𝒪_{W,x}` over `𝒪_{W',y}`); `length_{𝒪_{W',y}} κ(x) = f.residueDegree x`;
and the passage from the product in `ℤᵐ⁰` over the finite fibre to the sum of `Scheme.ord`. Then
`f_* div r = div N(r)` follows coefficientwise, with split 1's `cyclesMap`.

### Split 8: `feat: principal divisors push forward to zero along dimension-dropping proper maps` (after: 1, 7)

Not started. If `dim f(W) < dim W`, then `f_* div r = 0` (Fulton, Proposition 1.4(a)). On
`k`-cycles this is automatic for `dim f(W) < k` by the grading of `Chow.cyclesMap`. The case
`dim f(W) = k` reduces to the fact that a principal divisor on a proper curve over the function
field of `f(W)` (the generic fibre) has degree zero, which is split 7 applied to the finite map
from the curve to `ℙ¹` given by `r` (Fulton's proof of Proposition 1.4(a)).

### Split 9 (final): `feat: proper pushforward of Chow groups and the degree of zero-cycles` (after: 1, 2, 3, 4, 5, 6, 7, 8)

Not started; this is the only split that completes the target. File: a new
`TauCeti/AlgebraicGeometry/Chow/ProperPushforward.lean`.

- `Chow.cyclesMap_mem_ratEquiv`: for `f` proper over `k`, `cyclesMap k f` maps
  `RatEquiv X n` into `RatEquiv Y n`. Proof sketch: write the cycle of a `RatEquivFamily` as a
  locally finite sum (its summands are determined by `RatEquivFamily.component_apply` and
  `component_apply_eq_zero_of_notMem_range`, so `component_def` is not needed), push it forward
  with `map_locallyFiniteSum`, and rewrite each summand as `(i_j ≫ f)_* div r_j` with
  `map_height_comp_of_isClosedImmersion`. Splits 7 and 8 turn each summand into `0` or
  `(i_V)_* div (N r_j)` on `V = f(W_j)`. Group the nonzero summands by `V`: only finitely many
  `W_j` meet the quasi-compact `f⁻¹(V)`, so the products of the norms over each `V` give a family
  of reduced images that is locally finite, as in `locallyFinite_support_map`.
- `Chow.ChowGroup.properPushforward k f : ChowGroup X n →+ ChowGroup Y n`, with
  `properPushforward_cycleClass`, `properPushforward_id` and `properPushforward_comp`.
- `Chow.ChowGroup.degree k X : ChowGroup X 0 →+ ℤ` for `X` proper over `k`, with
  `degree_cycleClass` and `degree_properPushforward` (`deg f_* = deg`).
- The README checks `test_pushforward_degree` and `test_pushforward_not_proper`.

## What remains (status `partial`)

Proved: splits 1–6 and the first part of split 7: the cycle level, the whole commutative algebra
of Fulton's Appendix A (A.2 and both forms of A.3), the finiteness of a proper generically finite
morphism over a neighbourhood of each codimension-one point, and the identification of its fibres
over such a point with the primes over it. Remaining: the scheme-level coefficient identity of
split 7 (listed there), splits 8 and 9. In particular, the statement that proper pushforward
preserves rational equivalence (Fulton, Proposition 1.4; Theorem 1.4) is not proved, so `f_*`
and `deg` are not yet defined on Chow groups.
