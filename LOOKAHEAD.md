<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"chow-flat-pullback","main":"afa08a3ed16fb167e35de371afb1eb03fbc5913a","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat(AlgebraicGeometry/Chow/OpenRestriction): restrict cycles to open subschemes and prove the cycle-level localisation sequence"},{"n":2,"after":[1],"title":"feat(AlgebraicGeometry/Chow/Localization): restriction of Chow groups to open subschemes and the localisation sequence"},{"n":3,"after":[],"title":"feat(AlgebraicGeometry/Chow/FlatPullback): flat pullback of cycles with generic-length multiplicities"},{"n":4,"after":[2,3],"title":"feat(AlgebraicGeometry/Chow/FlatPullback): flat pullback preserves rational equivalence"},{"n":5,"after":[1,2,3,4],"title":"feat(AlgebraicGeometry/Chow/FlatPullback): flat pullback on Chow groups, functoriality and the base-change square"}]}-->

# Lookahead: `chow-flat-pullback` (SchemeAndStackFoundations, Layer 5, §5.2)

Built on `main` at `afa08a3ed16fb167e35de371afb1eb03fbc5913a`. Status: **partial**. Splits 1 and
2 (the localisation sequence `localization_exact`) are done. The round of 2026-11-06 found `main`
unchanged and started split 3: `TauCeti/AlgebraicGeometry/Chow/FlatPullback.lean` now defines the
cycle-level flat pullback `cycleFlatPullback` with generic-length multiplicities and proves its
local finiteness; its dimension shift and functoriality remain. A second round the same day (main
still `afa08a3ed16`) added the fibre half of the dimension shift (`height_preimage_singleton_eq`)
and the residue-field isomorphism for fibre inclusions. Supplier PRs #29425 (head `d327f903b0`)
and #29451 were still open. A third round the same day (main still `afa08a3ed16`, both supplier
PRs still open) completed the dimension shift (`height_eq_height_add`) and defined
`cyclesFlatPullback : Z_k(Y) →+ Z_{k+n}(X)`; it also dropped the branch's duplicate of `main`'s
`Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks`. A fourth round the same day (main still
`afa08a3ed16`, #29425 still at head `d327f903b0`, #29451 still open) proved functoriality on
cycles: `fiberLength_comp` (multiplicativity of fibre lengths, from Mathlib's
`IsLocalRing.length_baseChange`), `cycleFlatPullback_comp` and `cyclesFlatPullback_comp`. Split 3
is now complete.

The target (README §5.2): flat pullback `f^* : CH_k(Y) → CH_{k+n}(X)` for `f` flat with all fibres
of pure dimension `n`, `f^*[V] = [f⁻¹(V)]` with generic-length multiplicities, functoriality
`(g f)^* = f^* g^*`, the base-change square `f^* g_* = g'_* f'^*` against proper pushforward
(`flatPullback_properPushforward`), and the localisation sequence `localization_exact`:
`CH_k(Y) → CH_k(X) → CH_k(U) → 0` exact for `Y ⊆ X` closed with complement `U`.

## Stubs

None yet. This round proved only the part of the target that needs no supplier, so the branch has
no `TauCeti/Lookahead/ChowFlatPullback/Stubs.lean` and the header lists no suppliers.

The supplier `chow-proper-pushforward` has no pinned declarations in
`SchemeAndStackFoundations/Suggested.lean` (Layer 5 there pins only `cyclesOfDimension`, `RatEquiv`,
`ChowGroup`, `cycleClass` and `CH_coprod`). Its open PR #29425 (head `d327f903b0`) states the
cycle-level pushforward

```lean
noncomputable def cyclesMap (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [QuasiCompact f] {n : ℤ} :
    cyclesOfDimension X n →+ cyclesOfDimension Y n
lemma cyclesMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) [f.IsOver (Spec (.of k))]
    [g.IsOver (Spec (.of k))] [QuasiCompact f] [QuasiCompact g] {n : ℤ} :
    cyclesMap k (f ≫ g) (n := n) = (cyclesMap k g).comp (cyclesMap k f)
noncomputable def cyclesDegree : cyclesOfDimension X 0 →+ ℤ
```

in namespace `TauCeti.AlgebraicGeometry.Chow`. PR #29451 is linear algebra (cokernel lengths) and
pins nothing the target consumes. The Chow-group-level pushforward `CH_k(X) → CH_k(Y)`, which the
base-change square (split 5) consumes, is stated neither in `Suggested.lean` nor in either PR.
Split 5 should stub `cyclesMap` from PR #29425 and the Chow-level descent of `cyclesMap` once its
statement is fixed by the supplier, together with its compatibility with `cycleClass`.

## What is proved

`TauCeti/AlgebraicGeometry/Chow/OpenRestriction.lean` (namespace `TauCeti.AlgebraicGeometry.Chow`),
no `sorry`:

- `height_apply_of_isOpenImmersion`: for `X` locally of finite type over a field `K` and
  `j : U ⟶ X` an open immersion, `height (j x) = height x`;
- `apply_mem_pointsOfDimension_iff`: so `j` preserves `pointsOfDimension`;
- `cycleRestrict`, `cycleRestrict_apply`: pullback of algebraic cycles along an open immersion;
- `cyclesRestrict`, `cyclesRestrict_apply`: the restriction `Z_k(X) →+ Z_k(U)` (the flat pullback
  of relative dimension `0` along `j`, and the second map of the localisation sequence);
- `cycleExtend`, `cycleExtend_apply`, `cycleExtend_apply_of_notMem_range`,
  `cycleRestrict_cycleExtend`: extension by zero of cycles from `U` to a locally Noetherian `X`
  (local finiteness from quasi-compactness of `V ∩ U` in a Noetherian affine `V`);
- `cyclesExtend`, `cyclesRestrict_cyclesExtend`, `cyclesRestrict_surjective`: on `k`-cycles;
- `cyclesRestrict_eq_zero_iff`, `ker_cyclesRestrict_eq_range_cyclesPushforward`: the kernel of
  restriction is the image of `main`'s closed-immersion `cyclesPushforward` along any closed
  immersion onto the complement. Together: `Z_k(Z) → Z_k(X) → Z_k(U) → 0` is exact.

`TauCeti/AlgebraicGeometry/Chow/Localization.lean` (same namespace), no `sorry`:

- `RatEquivFamily.RestrictIndex`, `RatEquivFamily.restrict`: a rational-equivalence family on `X`
  restricted to `U` (members meeting `U`, replaced by `W ×_X U`, which is integral, closed in `U`
  and of the same dimension; rational functions pulled back by `functionFieldMap`);
- `RatEquivFamily.component_restrict`, `RatEquivFamily.cycle_restrict`: its cycle is the
  restriction of the cycle (via `main`'s `Scheme.ord_functionFieldMap`);
- `cyclesRestrict_mem_ratEquiv`: restriction preserves rational equivalence;
- `ChowGroup.restrict`, `ChowGroup.restrict_cycleClass`, `ChowGroup.restrict_surjective`:
  `CH_k(X) →+ CH_k(U)` (flat pullback along `j`), surjective;
- `ChowGroup.restrict_comp_pushforward`: `CH_k(Z) → CH_k(X) → CH_k(U)` composes to zero for a
  closed immersion onto the complement.
- `TauCeti.AlgebraicGeometry.Scheme.Hom.range_imageι` (the scheme-theoretic image of a
  quasi-compact `f` has the closure of `range f` as its points), `Scheme.Hom.isIntegral_image`
  (instance: integral source ⇒ integral image), and
  `Scheme.Hom.isIso_functionFieldMap_of_isOpenImmersion` (instance: a dominant open immersion of
  irreducible schemes induces an isomorphism of function fields);
- `RatEquivFamily.cycle_mem_cyclesOfDimension`: the cycle of a rational-equivalence family is a
  `k`-cycle (codimension-one points of a `(k+1)`-dimensional integral `W` have dimension `k`);
- `RatEquivFamily.closure`: a family on `U` extended to `X` by taking scheme-theoretic images of
  `W ⟶ U ⟶ X` (a quasi-compact immersion, so `toImage` is a dominant open immersion by Mathlib),
  the rational functions transported along the function-field isomorphism; local finiteness from
  quasi-compactness of `j⁻¹ V` for affine `V`;
- `RatEquivFamily.cycleRestrict_cycle_closure`: the closure family restricts to the family;
- `ChowGroup.localization_exact`: `Function.Exact (pushforward i) (restrict j K k)` for a closed
  immersion `i` onto the complement of `U`; with `ChowGroup.restrict_surjective` this is the
  localisation sequence `CH_k(Z) → CH_k(X) → CH_k(U) → 0` (Fulton Proposition 1.8).

`TauCeti/AlgebraicGeometry/Chow/FlatPullback.lean` (split 3, in progress, 426 lines), no `sorry`:

- `TauCeti.GeneralizingMap.maximal_mem_preimage_closure_singleton_iff` (topological) and
  `Chow.maximal_mem_preimage_closure_singleton_iff` (for `[Flat f]`, via Mathlib's
  `Flat.generalizingMap`): the generic points of `f⁻¹(closure {y})` are the generic points of the
  fibre `f⁻¹{y}`; `apply_eq_of_maximal_mem_preimage_closure_singleton`: they lie over `y`;
- `TauCeti.finite_maximal_mem_inter`: a closed set in a quasi-sober `T0` space has finitely many
  generic points inside a Noetherian open subset (via `genericPoints.finite` and Tau Ceti's
  `mem_genericPoints_iff`);
- `maximal_mem_preimage_comp_iff`: for flat `f`, `x` is generic in its `(f ≫ g)`-fibre iff it is
  generic in its `f`-fibre and `f x` is generic in its `g`-fibre (for split 3's functoriality);
- `height_preimage_singleton_eq`: for `[PureRelativeDimension n f]`, a generic point `x` of its
  fibre has height `n` in the fibre `f ⁻¹' {f x}` (its closure there is an irreducible component,
  by `TauCeti.mem_genericPoints_iff` and `height_eq_topologicalKrullDim_closure_singleton`);
- `asFiber_mem_genericPoints`, `height_asFiber_eq`: such an `x` is a generic point of the
  scheme-theoretic fibre `f.fiber (f x)` (Mathlib's `Scheme.Hom.asFiber`), of height `n` there
  (`PureRelativeDimension.isPureDimensional_fiber`);
- `height_asFiber_eq_toNat_trdeg`: for `[LocallyOfFiniteType f]`, that height is
  `trdeg_{κ(f x)} κ_{X_{f x}}(x)` (`topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField`
  over the field `κ(f x)`, with `f.fiberOverSpecResidueField`);
- `algebraMap_residueField_fiber`: the `κ(f x)`-algebra map to `κ_{X_{f x}}(x)` is
  `f.residueFieldMap x ≫ (residueFieldCongr _).inv ≫ (f.fiberι _).residueFieldMap _` (compared
  after `Spec` against the monomorphism `Y.fromSpecResidueField (f x)` via
  `Scheme.eq_of_SpecMap_comp_fromSpecResidueField` and the fibre square `Scheme.Hom.fiber_fac`);
- `trdeg_residueField_lt_aleph0`: residue fields of a scheme locally of finite type over `K` have
  finite transcendence degree (Mathlib's `FinTrdeg` of an `EssFiniteType` residue field, through
  an affine chart and `residueFieldAlgEquivOfIsOpenImmersion`);
- `isScalarTower_residueField`: for `f` over `Spec K`, `K → κ(f x) → κ(x)` is a scalar tower;
- `height_eq_height_add`: **the dimension shift**. For `X`, `Y` locally of finite type over a field
  `K`, `f` over `Spec K` of pure relative dimension `n`, and `x` a generic point of its fibre,
  `height x = height (f x) + n` (`trdeg_add_eq` for the tower, `κ(x) ≅ κ_{X_{f x}}(x)` as
  `κ(f x)`-algebras by `algebraMap_residueField_fiber` and `main`'s
  `Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks`);
- `fiberLength f x := Module.length 𝒪_{X,x} (𝒪_{X,x} ⧸ 𝔪_{f x} 𝒪_{X,x})` and
  `fiberLength_ne_top`: finite at generic points of fibres of a locally Noetherian `X` (primes over
  `𝔪_{f x}𝒪_{X,x}` are generalizations of `x` in the fibre, via `range_fromSpecStalk`; so the ring
  is Noetherian of dimension `0`, hence Artinian by Hopkins–Levitzki);
- `cycleFlatPullback f α` for `[Flat f] [IsLocallyNoetherian X]`: coefficient
  `(fiberLength f x).toNat * α (f x)` at generic points `x` of fibres, `0` elsewhere (the `toNat`
  never truncates there, by `fiberLength_ne_top`); local finiteness via a Noetherian affine
  neighbourhood `V`, the finiteness of `f '' V ∩ supp α`, and `finite_maximal_mem_inter`;
  `cycleFlatPullback_apply`, `cycleFlatPullback_zero`, `cycleFlatPullback_add`;
- `cyclesFlatPullback f K k : cyclesOfDimension Y k →+ cyclesOfDimension X (k + n)` for `f` flat of
  pure relative dimension `n` between schemes locally of finite type over `K` (with
  `[IsLocallyNoetherian X]` stated, as in `Localization.lean`), and `cyclesFlatPullback_apply`.
- `fiberLength_comp`: for flat `f`, `fiberLength (f ≫ g) x = fiberLength f x * fiberLength g (f x)`
  (`𝒪_{X,x} ⧸ 𝔪_z 𝒪_{X,x}` is `𝒪_{X,x} ⊗ (𝒪_{Y,y} ⧸ 𝔪_z 𝒪_{Y,y})` by
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`, then Mathlib's
  `IsLocalRing.length_baseChange` for the flat local map `𝒪_{Y,y} → 𝒪_{X,x}`; this holds at every
  point, with `ℕ∞` lengths, so no finiteness hypothesis is needed);
- `cycleFlatPullback_comp`: `cycleFlatPullback (f ≫ g) α = cycleFlatPullback f (cycleFlatPullback g α)`
  for flat `f`, `g` (supports by `maximal_mem_preimage_comp_iff`, coefficients by
  `fiberLength_comp` and `ENat.toNat_mul`);
- `cyclesFlatPullback_comp`: the same on `k`-cycles, `(f ≫ g)^* α = f^* (g^* α)` in
  `Z_{k+m+n}(X)` as algebraic cycles, for `g` of pure relative dimension `m`, `f` of pure relative
  dimension `n`, and `[PureRelativeDimension (m + n) (f ≫ g)]` stated as an instance argument
  (Tau Ceti has no composition instance for `PureRelativeDimension`; see *What remains*).

## What remains

1. (Optional, general dimension theory) an instance `PureRelativeDimension (m + n) (f ≫ g)` for
   `f`, `g` flat and locally of finite type of pure relative dimensions `n`, `m` (the fibre dimension of a
   composite). `cyclesFlatPullback_comp` currently states it as an instance
   argument; `cycleFlatPullback_comp` on `AlgebraicCycle` needs no dimension hypothesis at all.
2. (Split 4) Fulton Theorem 1.7: flat pullback preserves rational equivalence (via Fulton
   Proposition 1.7 / Stacks 42.20, needs the norm formula from `chow-proper-pushforward`).
3. (Split 5) `Chow.flatPullback` on `ChowGroup`, functoriality, and
   `flatPullback_properPushforward` (Stacks 42.15.1 on cycles, then descent), with the supplier's
   Chow-level pushforward stubbed.

## Notes for the port

- `height_apply_of_isOpenImmersion` and `apply_mem_pointsOfDimension_iff` are general dimension
  theory. At port time move them to `TauCeti/AlgebraicGeometry/Scheme/LocalDimension.lean` (which
  already has the `[X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]` variables),
  next to `topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField`. They were left in
  the Chow file on this branch to avoid rebuilding everything downstream of that module.
- The three `Scheme.Hom` lemmas on scheme-theoretic images in `Localization.lean` are general. At
  port time move them to `TauCeti/AlgebraicGeometry/SchemeTheoreticImage/Basic.lean` (next to
  `isReduced_image`, which `isIntegral_image` uses); they were left here to avoid rebuilding
  everything downstream of that module. If they move, split 2 needs no new prerequisite split.
- `TauCeti.GeneralizingMap.maximal_mem_preimage_closure_singleton_iff` and
  `TauCeti.finite_maximal_mem_inter` are general topology: at port time move them to
  `TauCeti/Topology/Sober.lean` (next to `mem_genericPoints_iff`), in split 3's PR or as a tiny
  prerequisite.
- `trdeg_residueField_lt_aleph0` is general dimension theory: at port time move it to
  `TauCeti/AlgebraicGeometry/Scheme/LocalDimension.lean` (same variables as
  `topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField`).
  `isScalarTower_residueField` belongs next to `Scheme.residueFieldBaseAlgebra` in
  `TauCeti/AlgebraicGeometry/Scheme/BaseAlgebra.lean`, and `asFiber_mem_genericPoints`,
  `algebraMap_residueField_fiber` are about Mathlib's `Scheme.Hom.fiber`; they stay in
  `FlatPullback.lean` on this branch to avoid rebuilding everything downstream of those modules.
- The branch's former duplicate `TauCeti.AlgebraicGeometry.isIso_residueFieldMap_of_surjectiveOnStalks`
  was removed in favour of `main`'s `Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks`
  (`TauCeti/AlgebraicGeometry/ResidueField.lean`).
- `Localization.lean` assumes `[IsLocallyNoetherian X] [IsLocallyNoetherian U]` as instances
  next to `LocallyOfFiniteType (X ↘ Spec (.of K))`, which implies both; the Chow groups need the
  instances to be stated. A reviewer may ask to derive them instead.

## Splits

1. Files: `TauCeti/AlgebraicGeometry/Chow/OpenRestriction.lean` (this branch, done). Adds all the
   declarations listed under *What is proved*. After: none. Subject: *feat(AlgebraicGeometry/Chow/
   OpenRestriction): restrict cycles to open subschemes and prove the cycle-level localisation
   sequence*.
2. Files: `TauCeti/AlgebraicGeometry/Chow/Localization.lean` (this branch, done, 352 lines). Adds
   every declaration listed for it above, ending with `ChowGroup.localization_exact`. After: 1. Subject:
   *feat(AlgebraicGeometry/Chow/Localization): restriction of Chow groups to open subschemes and
   the localisation sequence*.
3. Files: `TauCeti/AlgebraicGeometry/Chow/FlatPullback.lean` (this branch, done, 489 lines); adds
   the declarations listed for it above, through `cyclesFlatPullback_comp`. The port may split it
   in two: dimension shift
   (through `height_eq_height_add`) and the cycle-level pullback, the second after the first. After: none. Subject: *feat(AlgebraicGeometry/Chow/FlatPullback):
   flat pullback of cycles with generic-length multiplicities*.
4. Files: `TauCeti/AlgebraicGeometry/Chow/FlatPullback/RatEquiv.lean`; adds
   `cyclesFlatPullback_mem_ratEquiv`. After: 2, 3.
5. Files: `TauCeti/AlgebraicGeometry/Chow/FlatPullback/BaseChange.lean` (stubs of the supplier in
   `TauCeti/Lookahead/ChowFlatPullback/Stubs.lean` until it lands); adds `ChowGroup.flatPullback`,
   `flatPullback_comp`, `flatPullback_properPushforward`. After: 1, 2, 3, 4. Completes the target.
