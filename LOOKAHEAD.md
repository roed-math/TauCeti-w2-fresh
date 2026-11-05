<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"chow-proper-pushforward","main":"85f3eb5579df5ca44ba8cd0921d614b41ab72174","status":"partial","suppliers":["chow-group"],"splits":[{"n":1,"after":[],"title":"feat: pushforward of cycles over a field and degree of zero-cycles"},{"n":2,"after":[],"title":"feat: cokernel length of injective endomorphisms"},{"n":3,"after":[2],"title":"feat: cokernel length is the order of the determinant over one-dimensional domains"},{"n":4,"after":[3],"title":"feat: the order of a norm is a sum of local orders (Fulton A.3)"},{"n":5,"after":[4],"title":"feat: the order of a norm over the primes above a prime"},{"n":6,"after":[1],"title":"feat: generically finite proper morphisms are finite in codimension one"},{"n":7,"after":[5],"title":"feat: the order of a norm at a point of codimension one"},{"n":8,"after":[1,6,7],"title":"feat: proper pushforward of a principal divisor is the divisor of the norm"},{"n":9,"after":[1,8],"title":"feat: principal divisors push forward to zero along dimension-dropping proper maps"},{"n":10,"after":[1,2,3,4,5,6,7,8,9],"title":"feat: proper pushforward of Chow groups and the degree of zero-cycles"}]}-->

# Lookahead: `chow-proper-pushforward` (SchemeAndStackFoundations §5.2)

Target (README §5.2, *Chow.properPushforward*): for `f : X → Y` proper, Mathlib's
`AlgebraicCycle.map` with residue-degree weights preserves rational equivalence and gives
`f_* : CH_k(X) → CH_k(Y)` with `(g f)_* = g_* f_*`; for `X` proper over `k`,
`deg : CH_0(X) → ℤ` is well defined and `deg f_* = deg` (Fulton 1998, Theorem 1.4; Stacks,
Sections 42.12, 42.20, 42.41). The target has no pinned form in `Suggested.lean`; the names
below follow the README's *Chow.properPushforward* and the neighbouring code on `main`
(`TauCeti/AlgebraicGeometry/Chow/{Basic,ClosedImmersion}.lean`).

Built on `main` at `85f3eb5579df5ca44ba8cd0921d614b41ab72174`.

**Status: partial.** The cycle level is proved without stubs beyond the three below: the
pushforward of `n`-cycles over a field, its functoriality, the degree of zero-cycles, and
`deg f_* = deg` (split 1). The commutative algebra behind Fulton, Proposition 1.4(b) is proved
in full (splits 2–5; splits 4 and 5 use one stubbed helper, `Ring.ord_ringEquiv`): the determinant lemma of Fulton's Appendix A.2 (the order of a
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
neighbourhood of every point of codimension one. Split 7 proves the scheme-level form of
Fulton A.3: for a dominant morphism `f : X ⟶ Y` of locally Noetherian integral schemes, a point
`y` of codimension one and an affine open `V ∋ y` with `f⁻¹ V` affine and finite over `V`,
`ord_y N_{K(X)/K(Y)}(r) = Σ_{f x = y} [κ(x) : κ(y)] ord_x(r)` with Mathlib's `Scheme.ord`.
Split 8 proves Fulton, Proposition 1.4(b) globally: for `f : X ⟶ Y` proper and dominant over `k`
between integral schemes of the same dimension, `f_* div r = div N(r)`, and, through the
scheme-theoretic image, `f_* div r = (f.imageι)_* div N(r)` whenever `f(X)` has the dimension of
`X`. Split 9 has its easy case (a drop of dimension by two or more), and split 10 has the image
family of a rational equivalence. Still to do: the core of Proposition 1.4(a) (split 9) and the
descent to Chow groups (split 10).

## The supplier `chow-group` and its stubs

Everything in `Suggested.lean` §5.1 that this target consumes (`Chow.cyclesOfDimension`,
`Chow.RatEquiv`, `Chow.ChowGroup`, `Chow.cycleClass`) is already on `main` (merged by #22663,
`TauCeti/AlgebraicGeometry/Chow/Basic.lean`), so none of it is stubbed. On `main`, unlike
`Suggested.lean`, these take no field `κ` (they need only `IsLocallyNoetherian X`) and
`RatEquiv` is defined through the structure `Chow.RatEquivFamily`. The target uses `main`'s
forms. The rest of `chow-group` is in flight as PR #27340 (the divisor class comparison).
That PR also adds four lemmas that this target needs, and they are the only stubs
(`TauCeti/Lookahead/ChowProperPushforward/Stubs.lean`). The second and third were added to PR
#27340 after the earlier sessions of this branch had proved them here under the same names
(`Ring.ord_ringEquiv` in split 4, `coheight_add_height_eq_topologicalKrullDim` in split 8); this
session replaced those proofs by stubs, so the branch no longer duplicates the supplier.

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
  imports the stub module for it (used by `height_eq_toNat_trdeg_residueField` in split 1, by
  `topologicalKrullDim_eq_height_genericPoint` in split 6, and through them by splits 6 and 8).
  When the port runs, it
  deletes the stub file and replaces that
  `public import TauCeti.Lookahead.ChowProperPushforward.Stubs` with the landed module
  (`TauCeti.Topology.KrullDimension.Basic`, if it is not already imported transitively).
- Why it is a stub and not proved here: it is PR #27340's declaration. Proving it on this
  branch would duplicate the supplier.

### `TauCeti.Ring.ord_ringEquiv`

- `Suggested.lean` signature: none. `Suggested.lean` does not pin this lemma; it is a helper
  that PR #27340 adds to `TauCeti/RingTheory/OrderOfVanishing.lean` (namespace `TauCeti.Ring`).
- Stub, copied from PR #27340's diff:

  ```lean
  variable {R R' : Type*} [CommRing R] [CommRing R']

  @[simp]
  theorem ord_ringEquiv (σ : R ≃+* R') (x : R) : Ring.ord R' (σ x) = Ring.ord R x := by
    sorry
  ```

- Source: PR #27340's diff. Differences: none in the statement or attributes; the docstring is
  shortened. The stub is in namespace `TauCeti.Ring` of the stub file. Only
  `TauCeti/RingTheory/Length/Norm.lean` (split 4) imports the stub module for it, by a private
  `import`; on the port that import is deleted (the file already imports
  `TauCeti.RingTheory.OrderOfVanishing`, where the supplier puts it).
- An earlier session proved the same statement under the same name in
  `TauCeti/RingTheory/OrderOfVanishing.lean` (split 4). PR #27340 now supplies it, so that proof
  was removed and the file is back to `main`'s.

### `TauCeti.AlgebraicGeometry.coheight_add_height_eq_topologicalKrullDim`

- `Suggested.lean` signature: none. `Suggested.lean` does not pin this lemma; it is a helper
  that PR #27340 adds to `TauCeti/AlgebraicGeometry/Scheme/LocalDimension.lean`.
- Stub, copied from PR #27340's diff (the variables are those of `LocalDimension.lean`):

  ```lean
  variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]

  include k in
  theorem coheight_add_height_eq_topologicalKrullDim [IrreducibleSpace X] (x : X) :
      (Order.coheight x : WithBot ℕ∞) + Order.height x = topologicalKrullDim X := by
    sorry
  ```

- Source: PR #27340's diff. Differences: none in the statement. The stub is in namespace
  `TauCeti.AlgebraicGeometry` of the stub file, which `LocalDimension.lean` imports. It is used
  by `coheight_apply_eq_coheight` (split 8) and by `Chow.map_height_div` (split 8). An earlier
  session proved it, under the same name and statement, in `LocalDimension.lean`; that proof was
  removed when PR #27340 added it.

### `TauCeti.AlgebraicGeometry.Chow.RatEquivFamily.component_def`

- `Suggested.lean` signature: none. `Suggested.lean` does not pin this lemma; PR #27340 adds it
  to `TauCeti/AlgebraicGeometry/Chow/Basic.lean`, because on `main` the body of
  `RatEquivFamily.component` is not exposed outside that file.
- Stub, copied from PR #27340's diff (the variables are those of `Chow/Basic.lean`):

  ```lean
  variable {X : Scheme.{u}} {n : ℤ} [IsLocallyNoetherian X] (F : RatEquivFamily X n)

  lemma component_def (j : F.ι) :
      F.component j = AlgebraicCycle.map (F.i j) height height (AlgebraicCycle.div (F.r j)) := by
    sorry
  ```

- Source: PR #27340's diff. Differences: none in the statement; the PR's proof is
  `by rw [component]`. Only `TauCeti/AlgebraicGeometry/Chow/ProperPushforward.lean` (split 10)
  uses it. Earlier sessions planned to avoid it; the image family of split 10 reads its summands
  off directly, so this session stubs it rather than re-deriving it from `component_apply`.

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

Splits 2 and 3 use no stub and do not depend on split 1, so split 2 can open together with
split 1 as soon as the port starts. Splits 4 and 5 use the stubbed `Ring.ord_ringEquiv`, so like
split 1 they wait for PR #27340.

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

### Split 4: `feat: the order of a norm is a sum of local orders (Fulton A.3)` (after: 3; needs PR #27340 on `main`)

Proved on this branch. File `TauCeti/RingTheory/Length/Norm.lean` (new, 450 lines). It uses
PR #27340's `TauCeti.Ring.ord_ringEquiv` (stubbed):

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

Proved on this branch, about 240 lines, no stubs of its own (it builds on split 4).

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
  - `topologicalKrullDim_eq_height_genericPoint`: an integral scheme has the dimension of the
    height of its generic point (from the stubbed `height_eq_topologicalKrullDim_closure_singleton`;
    used by the next two items and by split 8);
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

### Split 7: `feat: the order of a norm at a point of codimension one` (after: 5)

Proved on this branch, about 315 lines, no stubs. It needs only split 5 (and `main`).

- `TauCeti/AlgebraicGeometry/AffineScheme/PrimesOver.lean` (new, 85 lines, namespace
  `AlgebraicGeometry`; the directory sits beside `AffineScheme.lean` as `Fibers/` sits beside
  `Fibers.lean` on `main`):
  - `IsAffineOpen.primeIdealOf_fromSpec` (the prime of the point `fromSpec q` is `q`);
  - `IsAffineOpen.preimageSingletonEquivPrimesOver f hV hU hUV hy : f ⁻¹' {y} ≃
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primesOver Γ(X, U)` for affine opens `V ∋ y` and
    `U = f⁻¹ V` (through `f.appLE V U`; Mathlib's `IsAffineOpen.comap_primeIdealOf_appLE`), with
    the `@[simp]` lemmas `coe_preimageSingletonEquivPrimesOver_apply` and
    `coe_preimageSingletonEquivPrimesOver_symm_apply`.
- `TauCeti/AlgebraicGeometry/OrderOfVanishing/Norm.lean` (new, 230 lines, namespace
  `TauCeti.AlgebraicGeometry`; beside Mathlib's `Mathlib/AlgebraicGeometry/OrderOfVanishing.lean`,
  which defines `Scheme.ord`):
  - `stalkAlgebraOfApplyEq f h`: for `h : f x = y`, the `𝒪_{Y,y}`-algebra structure on `𝒪_{X,x}`
    (`stalkSpecializes ≫ stalkMap`; stated through `f x = y` so that it can be used for a family
    of points over one fixed `y`);
  - `length_residueField_eq_residueDegree`: `(length_{𝒪_{Y,y}} κ(x)).toNat = f.residueDegree x`
    (both are `0` when `κ(x)/κ(y)` is infinite);
  - `ord_norm_eq_finsum_of_isAffineOpen` (Fulton, Proposition 1.4(b) at one point): for
    `f : X ⟶ Y` dominant between locally Noetherian integral schemes, `V ∋ y` affine with
    `f⁻¹ V` affine and `f.appLE V (f⁻¹ V)` finite, `coheight y = 1` and `r ≠ 0`,
    `Y.ord (Algebra.norm K(Y) r) y = ∑ᶠ x ∈ f ⁻¹' {y}, X.ord r x * f.residueDegree x`, with
    `K(Y) → K(X)` the algebra of `f.functionFieldMap`. The proof applies split 5's
    `ordFrac_norm_eq_finprod_primesOver` to `A₀ = Γ(Y, V) → B₀ = Γ(X, f⁻¹ V)` (injective by
    `Scheme.Hom.appLE_injective_of_isDominant`), `A = 𝒪_{Y,y}` and `R q = 𝒪_{X,x_q}` for the point
    `x_q` of each prime `q` over `y`; the points of the fibre have codimension one since
    `ht q ≤ ht p = 1` by incomparability (`TauCeti.primeSpectrumComap_strictMono_of_isIntegral`)
    and `q ≠ 0`.

### Split 8: `feat: proper pushforward of a principal divisor is the divisor of the norm` (after: 1, 6, 7)

Proved on this branch, about 230 lines, no new stubs (it uses the supplier stub through
`LocalDimension.lean`, like splits 1 and 6).

- `TauCeti/AlgebraicGeometry/Scheme/LocalDimension.lean` (namespace `TauCeti.AlgebraicGeometry`):
  `coheight_apply_eq_coheight`: for `f : X ⟶ Y` between irreducible schemes of the same
  dimension, locally of finite type over `k`, `height (f x) = height x` implies
  `coheight (f x) = coheight x` (from PR #27340's dimension formula
  `coheight_add_height_eq_topologicalKrullDim`, stubbed).
- `TauCeti/AlgebraicGeometry/Morphisms/Finite/Basic.lean` (namespace `AlgebraicGeometry`):
  `Scheme.Hom.exists_isAffineOpen_finite_app_of_isFinite_morphismRestrict`: if `f ∣_ V` is
  finite and `y ∈ V`, there is an affine open `U ⊆ V` containing `y` with `f⁻¹ U` affine and
  `f.app U` finite (through Mathlib's `morphismRestrict_app'` and
  `image_morphismRestrict_preimage`).
- `TauCeti/AlgebraicGeometry/SchemeTheoreticImage/Basic.lean` (namespace
  `AlgebraicGeometry.Scheme.Hom`): instances `isIntegral_image` (the scheme-theoretic image of a
  quasi-compact morphism from an integral scheme is integral) and `isLocallyNoetherian_image`.
- `TauCeti/AlgebraicGeometry/Chow/PrincipalPushforward.lean` (new, 140 lines, namespace
  `TauCeti.AlgebraicGeometry.Chow`):
  - `map_height_div` (Fulton, Proposition 1.4(b)): for `f : X ⟶ Y` proper and dominant over `k`
    between integral schemes locally of finite type over `k` with `dim X = dim Y`, and
    `r : K(X)ˣ`, `AlgebraicCycle.map f height height (div r) = div (Units.map (Algebra.norm K(Y)) r)`
    (with `K(Y) → K(X)` the algebra of `f.functionFieldMap`). Coefficientwise with split 1's
    `map_height_apply`: at `y` of codimension one, `f` is finite over a neighbourhood
    (split 6's `exists_isFinite_morphismRestrict_of_height_add_one`), shrunk to an affine one by
    the lemma above, and split 7's `ord_norm_eq_finsum_of_isAffineOpen` is the identity; at any
    other `y` both sides vanish, since a point over `y` with finite residue extension has the
    height (split 1), hence the codimension (`coheight_apply_eq_coheight`), of `y`.
  - `map_height_div_eq_map_imageι`: for `f : X ⟶ Y` proper over `k` from an integral `X`, with
    `height (f η_X) = height η_X`, `f_* div r = (f.imageι)_* div N_{K(X)/K(f(X))}(r)`: split 8's
    main theorem applied to `f.toImage`, which is proper and dominant onto the integral image of
    the same dimension. This is the form split 10 uses on each summand `(i_j ≫ f)_* div r_j`.

### Split 9: `feat: principal divisors push forward to zero along dimension-dropping proper maps` (after: 1, 8)

Started. If `dim f(W) < dim W`, then `f_* div r = 0` (Fulton, Proposition 1.4(a)). Proved on
this branch, in `TauCeti/AlgebraicGeometry/Chow/PrincipalPushforward.lean` (split 8's file, about
30 lines):

- `Chow.map_height_div_eq_zero_of_height_add_one_lt`: for `f : X ⟶ Y` quasi-compact over `k`
  from an integral `X` with `height (f η_X) + 1 < height η_X`, `f_* div r = 0`. The points of
  `div r` have codimension one, hence height `dim X - 1` (the stubbed dimension formula), and a
  point with finite residue extension keeps its height, which is at most `height (f η_X)`.

Remaining: the case `height (f η_W) + 1 = height η_W`. Then `f_* div r` is concentrated at
`f η_W`, with coefficient `Σ_{f x = f η_W} [κ(x) : κ(f η_W)] ord_x(r)`, the degree of the principal
divisor of `r` on the generic fibre, a proper curve over `κ(f η_W)`. That this degree is zero needs
the generic fibre with its local rings (`𝒪_{W_η, x} = 𝒪_{W, x}`), and either a finite morphism
of the curve to `ℙ¹` given by `r` (to which split 8 applies, the norm of `r` being `t^d` with
degree-zero divisor) or Fulton's closure of the graph of `r`; none of this is on `main`.

### Split 10 (final): `feat: proper pushforward of Chow groups and the degree of zero-cycles` (after: 1, 2, 3, 4, 5, 6, 7, 8, 9)

Started; this is the only split that completes the target. File
`TauCeti/AlgebraicGeometry/Chow/ProperPushforward.lean` (new, about 175 lines so far, namespace
`TauCeti.AlgebraicGeometry.Chow.RatEquivFamily`). Proved on this branch:

- `map_component`, `locallyFinite_support_map_comp`, `map_cycle_apply`: the pushforward of the
  cycle of a family `F` along a quasi-compact `f` is, coefficientwise, `Σ_j (i_j ≫ f)_* div(r_j)`
  (uses the stubbed `component_def` and `map_height_comp_of_isClosedImmersion`);
- `mapIndex F f`: the members `j` with `height (f (i_j η_j)) = height η_j`;
- `map F f : RatEquivFamily Y n` (`@[expose]`, so that its members can be read off) with
  `map_r`: the image family, whose members are the integral scheme-theoretic images
  `(i_j ≫ f).image` for `j ∈ mapIndex F f`, with the norms `N_{K(W_j)/K(f(W_j))}(r_j)`; its
  supports are locally finite because `range (i_j ≫ f).imageι = closure (f '' W_j)` and only
  finitely many `W_j` meet the quasi-compact preimage of an affine open (only `f`
  quasi-compact is needed);
- `map_comp_div_eq_component_map` (split 8's `map_height_div_eq_map_imageι` on each member) and
  `map_cycle_eq_cycle_map_add_finsum`: for `f` proper over `k`, `f_* (cycle F) = cycle (map F f)
  + Σ_{j ∉ mapIndex F f} (i_j ≫ f)_* div(r_j)`;
- `cycle_map_eq_map_cycle`: hence `f_* (cycle F) = cycle (map F f)` once the members outside
  `mapIndex F f` push forward to zero.

Still to add, once split 9 supplies that vanishing (Fulton, Proposition 1.4(a)):

- `Chow.cyclesMap_mem_ratEquiv`: for `f` proper over `k`, `cyclesMap k f` maps `RatEquiv X n` into
  `RatEquiv Y n` (`cycle_map_eq_map_cycle` with `Chow.mem_ratEquiv_iff`; the members outside
  `mapIndex F f` vanish by split 9, since their images have smaller dimension).
- `Chow.ChowGroup.properPushforward k f : ChowGroup X n →+ ChowGroup Y n`, with
  `properPushforward_cycleClass`, `properPushforward_id` and `properPushforward_comp`.
- `Chow.ChowGroup.degree k X : ChowGroup X 0 →+ ℤ` for `X` proper over `k`, with
  `degree_cycleClass` and `degree_properPushforward` (`deg f_* = deg`).
- The README checks `test_pushforward_degree` and `test_pushforward_not_proper`.

## What remains (status `partial`)

Proved: splits 1–8: the cycle level, the whole commutative algebra of Fulton's Appendix A (A.2
and both forms of A.3), the finiteness of a proper generically finite morphism over a
neighbourhood of each codimension-one point, the scheme-level coefficient identity
`ord_y N(r) = Σ_{f x = y} [κ(x) : κ(y)] ord_x(r)`, and Fulton's Proposition 1.4(b) globally
(`Chow.map_height_div`, `Chow.map_height_div_eq_map_imageι`). Split 10 is started: the image
family of a rational equivalence under a proper map and
`f_* (cycle F) = cycle (map F f) + Σ_{dimension-dropping j} (i_j ≫ f)_* div(r_j)`. Split 9 is started (the
case `dim f(W) < dim W - 1`). Remaining: the core of split 9 (Proposition
1.4(a): for `f : W ⟶ Y` proper from an integral `W` with `dim f(W) = dim W - 1`, the
coefficient `Σ_{f x = f η_W} [κ(x) : κ(f η_W)] ord_x(r)` vanishes, that is, a principal divisor
on the proper generic fibre curve has degree zero; it needs that curve and its comparison of
local rings, and a finite map to `ℙ¹` or Fulton's graph closure, none of which is on `main`) and
the rest of split 10 (with split 9, `cyclesMap_mem_ratEquiv`; then the descent to Chow groups,
`f_*`, `deg`, functoriality and `deg f_* = deg`). In particular, the statement that
proper pushforward preserves rational equivalence (Fulton, Theorem 1.4) is not proved, so `f_*`
and `deg` are not yet defined on Chow groups.
