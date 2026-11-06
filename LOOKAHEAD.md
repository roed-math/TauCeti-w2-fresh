<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"chow-flat-pullback","main":"3a0189695d62134a412200ef4237d0bbb2e95d75","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat(AlgebraicGeometry/Chow/OpenRestriction): restrict cycles to open subschemes and prove the cycle-level localisation sequence"},{"n":2,"after":[1],"title":"feat(AlgebraicGeometry/Chow/Localization): restriction of Chow groups to open subschemes and the localisation sequence"},{"n":3,"after":[],"title":"feat(AlgebraicGeometry/Chow/FlatPullback): flat pullback of cycles with generic-length multiplicities"},{"n":4,"after":[2,3],"title":"feat(AlgebraicGeometry/Chow/FlatPullback): flat pullback preserves rational equivalence"},{"n":5,"after":[1,2,3,4],"title":"feat(AlgebraicGeometry/Chow/FlatPullback): flat pullback on Chow groups, functoriality and the base-change square"}]}-->

# Lookahead: `chow-flat-pullback` (SchemeAndStackFoundations, Layer 5, §5.2)

Built on `main` at `3a0189695d62134a412200ef4237d0bbb2e95d75` (merged in by the sixteenth round). Status: **partial**. Splits 1 and
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
is now complete. A fifth round the same day (main still `afa08a3ed16`, #29425 still at head
`d327f903b0`, #29451 still open at `ed4b4ac70d`) started split 4 with
`TauCeti/AlgebraicGeometry/Chow/FlatPullback/RatEquiv.lean`: the local computation of Fulton
Proposition 1.7 / Stacks Lemma 42.20.1 (`Ring.ord_algebraMap_of_flat`, `ord_stalkMap`: a flat local
map multiplies orders of vanishing by the fibre length) and the comparison of flat pullback with
restriction to opens (`fiberLength_of_isOpenImmersion`, `cycleFlatPullback_of_isOpenImmersion`).
A sixth round on 2026-11-06 (main still `afa08a3ed16`, #29425 still open at `d327f903b0`, #29451
still open at `ed4b4ac70d`) re-verified the branch and added no Lean. The next step, Stacks'
additivity lemma for `e(M, b)` and the minimal-prime order formula, did not fit in the time left. The
round refined the plan for that step (see *What remains*, item 2). A seventh round on 2026-11-06 merged
`main` at `385ec2ddd8d` (nothing on the Chow, cycle or order-of-vanishing files changed; #29425
still open at `d327f903b0`, #29451 still open at `ed4b4ac70d`, so still no supplier declaration on
`main`) and did step 2(a) of that plan: four general length lemmas in
`TauCeti/RingTheory/Length.lean`, ending with the snake-lemma additivity of
`length (coker φ) - length (ker φ)` in short exact sequences. An eighth round on 2026-11-06 (main still `385ec2ddd8d`,
#29425 still open at `d327f903b0`, #29451 still open at `ed4b4ac70d`) added
`length_quotient_lsmul_submodule_eq` to the same file: the finite-colength invariance of
`ℓ(M ⧸ aM)` that step 2(b) uses to discard the `B ⧸ 𝔪` pieces of a prime filtration. A ninth round on 2026-11-06 (main still `385ec2ddd8d`, #29425 still open at `d327f903b0`,
#29451 still open at `ed4b4ac70d`) added `length_quotient_lsmul_quotient_eq_ord` to the same file:
the contribution `e(B ⧸ 𝔮, b)` of a prime-filtration piece is `ord_{B/𝔮}(b)`. A tenth round on
2026-11-06 (main still `385ec2ddd8d`, #29425 still open at `d327f903b0`, #29451 still open at
`ed4b4ac70d`) finished step 2(b): the new file `TauCeti/RingTheory/OrderOfVanishing/MinimalPrimes.lean`
proves the order formula over minimal primes (`Ring.ord_eq_finsum_minimalPrimes`) by the
prime-filtration induction, and `RatEquiv.lean` gained its flat-local form
`Ring.ord_mul_length_eq_finsum_minimalPrimes`, the algebraic core of Stacks Lemma 42.20.1. An eleventh round on
2026-11-06 (main still `385ec2ddd8d`, #29425 still open at `d327f903b0`, #29451 still open at
`ed4b4ac70d`) started the geometric half of item 2 in `RatEquiv.lean`: `fiberLength` over a point
with field stalk (`fiberLength_of_maximalIdeal_eq_bot`, `fiberLength_of_apply_eq_genericPoint`)
and the length of a stalk localized at a generization (`length_localization_stalkSpecializes`,
via `main`'s `Scheme.isLocalization_stalkSpecializes` and `RingEquiv.length_self_eq`), and the
minimal-prime/component correspondence for stalks
(`Scheme.comap_stalkSpecializes_maximalIdeal_mem_minimalPrimes_iff`). A twelfth round on
2026-11-06 (main still `385ec2ddd8d`, #29425 still open at `d327f903b0`, #29451 still open at
`ed4b4ac70d`) assembled these into the scheme-level local formula `ord_mul_fiberLength_eq_finsum`
(the minimal primes of a stalk reindexed by the components through the point via the bijection
`Scheme.stalkMinimalPrime_bijective`, the weights turned into fibre lengths at the generic points
by `fiberLength_of_forall_specializes`). It also added `Scheme.ord_stalkMap_of_isClosedImmersion`,
which identifies `ord_{B ⧸ 𝔮}` with the order of vanishing on an integral closed subscheme. A
thirteenth round on 2026-11-06 (main still `385ec2ddd8d`, #29425 still open at `d327f903b0`,
#29451 still open at `ed4b4ac70d`) did item 2(i) of *What remains*: the stalks of a base change
along a closed immersion (`Scheme.ker_stalkMap_le_map_ideal_ker`,
`Scheme.ker_stalkMap_pullback_fst_le`, via Mathlib's `IdealSheafData.ker_fst_of_isClosedImmersion`
and `main`'s `IdealSheafData.ideal_comap_of_le`) and the resulting equality of fibre lengths
`fiberLength_pullback_snd`: `fiberLength (X ×_Y W ⟶ W) x = fiberLength f x`. A fourteenth round
on 2026-11-06 (main still `385ec2ddd8d`, #29425 still open at `d327f903b0`, #29451 still open at
`ed4b4ac70d`) did the dimension half of item 2(ii): it split the dimension shift into the general
identity `height_eq_height_add_height_asFiber` (`dim x = dim f(x) + dim_{X_{f x}} x` at every
point) with `height_asFiber_le`, giving the dimension inequality `height_le_height_add`, and proved
`Scheme.ringKrullDim_stalk_le_one`, `ringKrullDim_stalk_pullback_le_one` (local rings of `X ×_Y W`
at points of dimension `k + n` have dimension `≤ 1`), `height_eq_height_genericPoint_add`
(components of a flat `X` over an integral `Y` have dimension `dim Y + n`) and
`height_eq_height_genericPoint_add_of_pullback` (the same for the components of `X ×_Y W`). The other half of
2(ii), the components as integral closed subschemes, is `main`'s
`IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure_singleton`. A fifteenth round on 2026-11-06 (main still
`385ec2ddd8d`, #29425 still open at `d327f903b0`, #29451 still open at `ed4b4ac70d`) started item
2(iii) with its support bookkeeping: the converse of the dimension shift
(`maximal_mem_preimage_singleton_of_height_asFiber_eq`, `maximal_mem_preimage_singleton_of_height_eq`:
a point of fibre-height `n`, equivalently of dimension `dim f(x) + n`, is generic in its fibre, via
the new general bound `height_fiber_le`, of which `height_asFiber_le` is now a corollary) and
`height_snd_eq_and_maximal_of_height_eq` in `RatEquiv.lean`: for `W` integral of dimension `k + 1`,
a point of `X ×_Y W` of dimension `k + n` not over the generic point of `W` lies over a point of
dimension `k` of `W` and is generic in its `f`-fibre (so both sides of Stacks 42.20.1 are supported
on the same points; the points over the generic point of `W` contribute `0` on both sides because
`r` is a unit there).
A sixteenth round on 2026-11-06 merged `main` at `3a0189695d6` (only `.github/` workflows
changed; nothing on the Chow, cycle or order-of-vanishing files), found #29425 still open (head now
`6ce093654c`) and #29451 still open (head now `6844b1fe1c`), so still no supplier declaration on
`main`, and did step (α) of item 2(iii) together with the local half of (β), in `RatEquiv.lean`:
`Scheme.ord_functionFieldMap_algebraMap_stalk` and its quotient form
`Scheme.ord_functionFieldMap_div_algebraMap_stalk` (for an integral closed subscheme
`ι : Z ⟶ X` with `ι η_Z = η` and `h : X ⟶ W` with `ι ≫ h` dominant, the order on `Z` at a
codimension-one `z` of the pullback of `a / b ∈ K(W)` is `ord_{𝒪_{X,ι z} ⧸ 𝔮_η}(h^# a) -
ord_{𝒪_{X,ι z} ⧸ 𝔮_η}(h^# b)`, the prime written exactly as in `ord_mul_fiberLength_eq_finsum`,
via `main`'s `Scheme.Hom.functionFieldMap_algebraMap_stalk` and `Scheme.ord_algebraMap_stalk`),
and `isDominant_subschemeι_pullback_snd` (for `f` flat and `η` the generic point of a component of
`X ×_Y W`, the reduced closure of `η` dominates `W`, via `main`'s
`subschemeι_genericPoint_vanishingIdeal_closure_singleton` and `isDominant_iff_genericPoint_eq`).
So the members `W'` of the pulled-back family are the reduced closures in `X ×_Y W` (embedded into
`X` by `ι ≫ pullback.fst f i`, a closed immersion), with function `φ r` along
`ι ≫ pullback.snd f i`.
A seventeenth round on 2026-11-06 (main still `3a0189695d6`, no supplier declaration on `main`)
did the algebraic part of the rest of (β), in `RatEquiv.lean`: the instance
`finite_generizations_forall_specializes` (the components through a point of a locally Noetherian
scheme are finitely many, via `Scheme.stalkMinimalPrime_bijective` and Mathlib's
`minimalPrimes.finite_of_isNoetherianRing`) and the integer quotient form
`ord_sub_ord_mul_fiberLength_eq_finsum`: for non-zero-divisors `a`, `b` of a one-dimensional
Noetherian `𝒪_{Y,f y}` and `fiberLength f y ≠ ⊤`,
`(ord a - ord b) · fiberLength f y = Σᶠ x, fiberLength f x · (ord_x a - ord_x b)` in `ℤ` (all
`ℕ∞` values through `toNat`, finiteness from `Ring.ord_ne_top` and `ENat.toNat_sum`). It also added
`IdealSheafData.exists_subschemeι_vanishingIdeal_closure_singleton_eq` to `main`'s
`TauCeti/AlgebraicGeometry/IdealSheaf/VanishingIdeal.lean` (+11 lines): a specialization of `η` is
the image of a point of the reduced closure of `η`, which is the point `z` over `y` of each member.
With these the same round finished the scheme-level (β), `ord_mul_fiberLength_eq_finsum_ord`:
for `f` flat over a locally Noetherian integral `Y`, `y : X` with `dim 𝒪_{X,y} ≤ 1`, `f y` of
codimension one, `fiberLength f y ≠ ⊤`, `dim y` finite, every component through `y` of dimension
`dim y + 1`, a point `z_x` over `y` on each reduced component `Z_x` and `Z_x ⟶ Y` dominant (an
instance argument `[∀ x, IsDominant (Z_x.ι ≫ f)]`, which `isDominant_subschemeι_pullback_snd`
discharges for the base change), and `r ≠ 0` in `K(Y)`:
`ord_{f y}(r) · fiberLength f y = Σᶠ x, fiberLength f x · ord_{z_x}((Z_x.ι ≫ f)^* r)` in `ℤ`. Its
inputs: `Scheme.coheight_eq_one_of_height_apply_genericPoint_eq` (a point of an irreducible closed
subscheme whose image has dimension one less than the generic point's, finite, has coheight one)
and the instance `Scheme.IdealSheafData.isLocallyNoetherian_subscheme` (port: next to Mathlib's
`IdealSheafData.subscheme` API, for instance in `IdealSheaf/VanishingIdeal.lean`).
`RatEquiv.lean` is now 872 lines: the next round should put (γ), (δ) and
`cyclesFlatPullback_mem_ratEquiv` in a new file importing it (for instance
`TauCeti/AlgebraicGeometry/Chow/FlatPullback/RatEquivFamily.lean`), and the port may move the
`Ring` and `Scheme` sections of `RatEquiv.lean` (pure local algebra and stalk lemmas) into their
own prerequisite file.

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

`TauCeti/AlgebraicGeometry/Chow/FlatPullback.lean` (split 3, done, 559 lines), no `sorry`:

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
- `height_asFiber_le` (fourteenth round): for `[PureRelativeDimension n f]`, every point of the
  fibre `f.fiber (f x)` has height `≤ n` (its closure lies in an irreducible component);
- `height_eq_height_add_height_asFiber` (fourteenth round): at every point,
  `height x = height (f x) + height (f.asFiber x)` (the proof formerly inside
  `height_eq_height_add`, which is now its two-line corollary); `height_le_height_add`: hence
  `height x ≤ height (f x) + n` everywhere;
- `height_fiber_le` (fifteenth round): every point of a fibre `f.fiber y` has height `≤ n`
  (`height_asFiber_le` is its corollary); `maximal_mem_preimage_singleton_of_height_asFiber_eq`:
  a point of height exactly `n` in its fibre is a generic point of the fibre
  (`Order.height_strictMono`); `maximal_mem_preimage_singleton_of_height_eq`: hence a point with
  `height x = height (f x) + n` (and `height (f x)` finite) is generic in its fibre;
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

`TauCeti/AlgebraicGeometry/Chow/FlatPullback/RatEquiv.lean` (split 4, in progress, 719 lines), no
`sorry`:

- `TauCeti.Ring.ord_algebraMap_of_flat`: for a flat local homomorphism `A → B`,
  `Ring.ord B (algebraMap A B a) = Ring.ord A a * length B (B ⧸ 𝔪_A B)` (`B ⧸ aB ≅ B ⊗ (A ⧸ aA)`
  by `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`, then `IsLocalRing.length_baseChange`);
- `ord_stalkMap`: for `f` flat, `ord_{𝒪_{X,x}}(f^# a) = ord_{𝒪_{Y,f x}}(a) * fiberLength f x`;
- `fiberLength_of_isOpenImmersion`: an open immersion has fibre length `1` everywhere;
- `cycleFlatPullback_of_isOpenImmersion`: `cycleFlatPullback j = cycleRestrict j` for an open
  immersion `j` (so restriction is the relative-dimension-`0` flat pullback, as the README says).
- `fiberLength_of_maximalIdeal_eq_bot`, `fiberLength_of_apply_eq_genericPoint` (eleventh round):
  over a point whose local ring is a field, in particular the generic point of an integral `Y`,
  `fiberLength f x = ℓ(𝒪_{X,x})` (the multiplicity of a component of `f⁻¹(W)` at its generic
  point, for the base change `f⁻¹(W) → W`);
- `length_localization_stalkSpecializes` (eleventh round): for `x ⤳ y`,
  `ℓ((𝒪_{X,y})_𝔮) = ℓ(𝒪_{X,x})` where `𝔮` is the prime of `x` in `𝒪_{X,y}` (the weight
  `ℓ(B_𝔮)` of `Ring.ord_mul_length_eq_finsum_minimalPrimes` read at a generic point).
- `TauCeti.AlgebraicGeometry.Scheme.exists_comap_stalkSpecializes_maximalIdeal_eq`,
  `Scheme.comap_stalkSpecializes_maximalIdeal_mono`,
  `Scheme.comap_stalkSpecializes_maximalIdeal_mem_minimalPrimes_iff` (eleventh round): every
  prime of `𝒪_{X,y}` is the prime of a generization `x ⤳ y`, these primes are ordered as the
  generizations are, and the prime of `x` is minimal iff `x` has no proper generization (`x` is
  the generic point of an irreducible component through `y`).
- `Scheme.stalkMinimalPrime`, `Scheme.stalkMinimalPrime_bijective` (twelfth round): the map from
  generizations of `y` without proper generization to the minimal primes of `𝒪_{X,y}` is a
  bijection (injective by `main`'s `specializes_of_comap_stalkSpecializes_maximalIdeal_le` and
  `T0`, surjective by `exists_comap_stalkSpecializes_maximalIdeal_eq`);
- `Scheme.ker_stalkMap_eq_comap_maximalIdeal`, `Scheme.ord_stalkMap_of_isClosedImmersion`
  (twelfth round): for a closed immersion `i : Z ⟶ X` of an integral scheme, the kernel of
  `𝒪_{X,i z} ↠ 𝒪_{Z,z}` is the prime of `i η_Z` (`𝒪_{Z,z}` embeds into the function field), so
  `ord_{𝒪_{Z,z}}(i^# a) = ord_{𝒪_{X,i z} ⧸ 𝔮}(a)` (`TauCeti.Ring.ord_ringEquiv`);
- `apply_eq_genericPoint_of_forall_specializes`, `fiberLength_of_forall_specializes` (twelfth
  round): a flat `f` to an integral `Y` sends generic points of components of `X` to the generic
  point of `Y`, where the fibre length is `ℓ(𝒪_{X,x})`;
- `ord_mul_fiberLength_eq_finsum` (twelfth round): **the scheme-level local form of Stacks Lemma
  42.20.1**. For `f` flat over an integral `Y`, `X` locally Noetherian, `dim 𝒪_{X,y} ≤ 1` and `a`
  a non-zero-divisor of `𝒪_{Y,f y}`, `ord(a) · fiberLength f y = ∑ᶠ x, fiberLength f x ·
  ord_{𝒪_{X,y} ⧸ 𝔮_x}(f^# a)`, the sum over generic points `x` of the components through `y`.

`TauCeti/RingTheory/Length.lean` (`main`'s file, extended by the seventh round for split 4's order
formula; namespace `TauCeti`), no `sorry`:

- `length_add_length_eq_of_exact`: for an exact `0 → N → M → P → Q → 0`,
  `length M + length Q = length N + length P` (in `ℕ∞`, no finiteness needed);
- `length_add_length_add_length_eq_of_exact`: the same for a six-term exact sequence (even terms
  against odd terms), split at the middle image;
- `length_ker_eq_length_quotient_range`: an endomorphism of a module of finite length has kernel
  and cokernel of the same length (so `e(M, b) = 0` for `M` of finite length);
- `length_ker_add_length_quotient_range_eq_of_exact`: for `0 → N → M → P → 0` exact with
  compatible endomorphisms `φN`, `φM`, `φP`, `ℓ(ker φM) + ℓ(coker φN) + ℓ(coker φP) =
  ℓ(ker φN) + ℓ(ker φP) + ℓ(coker φM)`, from Mathlib's `SnakeLemma.exact_δ'_right`/`_left` (the
  additivity of `e(M, b)` of Stacks Section 42.2, stated without subtraction in `ℕ∞`).
- `length_quotient_lsmul_submodule_eq` (eighth round): if `a` acts injectively on `M` and
  `M ⧸ N` has finite length, then `ℓ(N ⧸ aN) = ℓ(M ⧸ aM)` (the snake-lemma additivity with
  `e(M ⧸ N, a) = 0`). `main`'s `length_quotient_lsmul_ideal_eq_ord` is its special case `M = A`,
  `N = I`; the port may re-derive it from the new lemma.
- `length_quotient_lsmul_quotient_eq_ord` (ninth round): for an ideal `I` and `a : A`,
  `ℓ_A((A ⧸ I) ⧸ a(A ⧸ I)) = Ring.ord (A ⧸ I) (mk a)` (restriction of scalars along
  `A ↠ A ⧸ I` preserves length, by `Module.length_eq_of_surjective`). This is the
  `e(B ⧸ 𝔮, b) = ord_{B/𝔮}(b)` step of 2(b) below; for a prime `𝔮 ∌ b` the kernel vanishes.

`TauCeti/RingTheory/OrderOfVanishing/MinimalPrimes.lean` (tenth round, new, 215 lines; namespace
`TauCeti`), no `sorry`:

- `subsingleton_localizedModule_quotient`: `(A ⧸ 𝔭)_𝔮 = 0` unless `𝔭 ≤ 𝔮` (Mathlib's
  `Module.mem_support_iff_of_finite` and `Ideal.annihilator_quotient`);
- `length_ker_lsmul_ne_top`: over a Noetherian ring of dimension `≤ 1`, a non-zero-divisor has a
  kernel of finite length on a finite module (`main`'s
  `isFiniteLength_of_nonZeroDivisor_mem_annihilator`);
- `length_ker_lsmul_add_finsum_eq`: for `A` Noetherian of dimension `≤ 1`, `a ∈ A⁰` and `M` finite,
  `ℓ(ker a) + ∑ᶠ 𝔮 min, ℓ_{A_𝔮}(M_𝔮) · ord_{A/𝔮}(a) = ℓ(M ⧸ aM)` (Stacks, Section 42.3), by
  Mathlib's `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`: the exact case is
  `length_ker_add_length_quotient_range_eq_of_exact` with exactness of localization; for `A ⧸ 𝔭`,
  a minimal `𝔭` gives `ord_{A/𝔭}(a)` (`length_quotient_lsmul_quotient_eq_ord`,
  `Ideal.length_localizedModule_quotient_eq_one`) and any other `𝔭` is maximal
  (`Ring.krullDimLE_one_iff`) so contributes `0` (`length_ker_eq_length_quotient_range`). The
  minimal primes are indexed as `{𝔮 : PrimeSpectrum A // 𝔮.asIdeal ∈ minimalPrimes A}` so that
  `Localization.AtPrime 𝔮.1.asIdeal` finds its `IsPrime` instance;
- `Ring.ord_eq_finsum_minimalPrimes`: `ord_A(a) = ∑ᶠ 𝔮 min, ℓ_{A_𝔮}(A_𝔮) · ord_{A/𝔮}(a)` for
  `a ∈ A⁰` (the case `M = A`).

`RatEquiv.lean` (thirteenth round) has the base change of fibre lengths along a closed immersion
`i : W ⟶ Y`: `Scheme.ker_stalkMap_le_map_ideal_ker` (for a closed immersion `p : Z ⟶ X` and an
affine open `U ∋ p z`, `ker (𝒪_{X,p z} ↠ 𝒪_{Z,z}) ≤ I_p(U) 𝒪_{X,p z}`),
`Scheme.germ_mem_maximalIdeal_of_mem_ker_app` (for any morphism `i`; the fifteenth round dropped
its unused `[IsClosedImmersion i]`, flagged by `#lint`), `Scheme.ker_stalkMap_pullback_fst_le`
(`ker (𝒪_{X,x} ↠ 𝒪_{X ×_Y W,x}) ≤ 𝔪_{f x} 𝒪_{X,x}`), `fiberLength_comp_of_ker_le`,
`fiberLength_eq_one_of_surjective` (fibre length `1` for a map surjective on stalks) and
`fiberLength_pullback_snd` (for `f` flat, `fiberLength (pullback.snd f i) x =
fiberLength f (pullback.fst f i x)`).

`RatEquiv.lean` (fourteenth round) has the dimension input of item 2(ii):
`Scheme.ringKrullDim_stalk_le_one` (at a point of height `m` of a scheme all of whose points have
height `≤ m + 1`, the stalk has dimension `≤ 1`, from Mathlib's `ringKrullDim_stalk_eq_coheight`
and `Order.krullDim_eq_iSup_height_add_coheight_of_nonempty`), `ringKrullDim_stalk_pullback_le_one`
(for `f` of pure relative dimension `n` over `K`, `i : W ⟶ Y` a closed immersion with all points
of `W` of height `≤ k + 1`, the stalks of `X ×_Y W` at points of height `k + n` have dimension
`≤ 1`, via `height_le_height_add` and `main`'s `Scheme.Hom.height_apply_eq_height`) and
`height_eq_height_genericPoint_add` (for `f` flat of pure relative dimension `n` over an integral
`Y`, a generic point `x` of a component of `X` has `height x = height η_Y + n`) and
`height_eq_height_genericPoint_add_of_pullback` (for `f` flat of pure relative dimension `n` and
`i : W ⟶ Y` a closed immersion of an integral `W`, a generic point `x` of a component of
`X ×_Y W` has `height x = height η_W + n`; computed through `pullback.fst f i` into `X`, with
Mathlib's `Scheme.Pullback.range_fst`, so `X ×_Y W` needs no structure over `K`). The fifteenth
round added `height_snd_eq_and_maximal_of_height_eq`: for `W` integral with
`height η_W = k + 1`, a point `x` of `X ×_Y W` with `height x = k + n` and
`pullback.snd f i x ≠ η_W` has `height (pullback.snd f i x) = k`, and `pullback.fst f i x` is a
generic point of its `f`-fibre (from `height_eq_height_add_height_asFiber`, `height_asFiber_le`,
`Order.height_strictMono` and `maximal_mem_preimage_singleton_of_height_asFiber_eq`).

`RatEquiv.lean` (tenth round) also has `TauCeti.Ring.ord_mul_length_eq_finsum_minimalPrimes`: for a
flat local `A → B` with `B` Noetherian of dimension `≤ 1` and `a ∈ A⁰`,
`ord_A(a) · ℓ_B(B ⧸ 𝔪_A B) = ∑ᶠ 𝔮 min B, ℓ_{B_𝔮}(B_𝔮) · ord_{B/𝔮}(a)` (the image of `a` is a
non-zero-divisor by Mathlib's `Module.Flat.isSMulRegular_of_nonZeroDivisors`).

`RatEquiv.lean` (sixteenth round) has the pullback of rational functions to the components:
`Scheme.ord_functionFieldMap_algebraMap_stalk` (for a closed immersion `ι : Z ⟶ X` of a locally
Noetherian integral `Z` with `ι η_Z = η`, `h : X ⟶ W` to an integral `W` with `ι ≫ h` dominant,
`z : Z` of coheight `1` and a nonzero germ `a` at `h (ι z)`,
`Z.ord ((ι ≫ h)^* a) z = (ord_{𝒪_{X,ι z} ⧸ 𝔮_η}(h^# a)).toNat`, with `𝔮_η` the comap of
`𝔪_{X,η}` along `stalkSpecializes hη`, exactly the ideal of `ord_mul_fiberLength_eq_finsum`),
`Scheme.ord_functionFieldMap_div_algebraMap_stalk` (the same for `a / b`, as a difference) and
`isDominant_subschemeι_pullback_snd` (for `f` flat, `W` integral and `η` without proper
generization in `X ×_Y W`, `(vanishingIdeal (closure {η})).subschemeι ≫ pullback.snd f i` is
dominant).
## What remains

1. (Optional, general dimension theory) an instance `PureRelativeDimension (m + n) (f ≫ g)` for
   `f`, `g` flat and locally of finite type of pure relative dimensions `n`, `m` (the fibre dimension of a
   composite). `cyclesFlatPullback_comp` currently states it as an instance
   argument; `cycleFlatPullback_comp` on `AlgebraicCycle` needs no dimension hypothesis at all.
2. (Split 4, started) Fulton Theorem 1.7: flat pullback preserves rational equivalence. Done: the
   local length computation (`ord_stalkMap`) and the open-immersion comparison. Remaining: for
   `W ⊆ Y` integral of dimension `k + 1` and `r ∈ R(W)^*`, write `f⁻¹(W) = ⋃ W'_i` with
   multiplicities `m_i = fiberLength` at the generic points and show
   `f^*[div r] = Σ m_i [div (r|W'_i)]` (Stacks Lemma 42.20.1). The missing algebra is the order
   formula over minimal primes (Fulton, Appendix A.3, *Order functions*; Stacks Section 42.3):
   for a one-dimensional Noetherian local ring `B` and a nonzerodivisor `b`, `ℓ_B(B ⧸ bB) = Σ_{𝔮 minimal} ℓ_{B_𝔮}(B_𝔮) · ord_{B/𝔮}(b)`, applied to
   `B = 𝒪_{f⁻¹(W),x}` together with `ord_stalkMap`. (**The order formula is done by the tenth
   round**, as `Ring.ord_eq_finsum_minimalPrimes` and its flat-local form
   `Ring.ord_mul_length_eq_finsum_minimalPrimes`; what remains of item 2 is geometric: identify,
   at a codimension-one point `x` of `f⁻¹(W)`, the minimal primes of `𝒪_{f⁻¹(W),x}` with the
   components `W'_i` through `x`, `ℓ(B_𝔮)` with `fiberLength` at their generic points, and
   `B ⧸ 𝔮` with `𝒪_{W'_i,x}`, then assemble the `RatEquivFamily`. The eleventh round did the
   length half of the second identification: `length_localization_stalkSpecializes` turns
   `ℓ(B_𝔮)` into `ℓ(𝒪_{f⁻¹(W),η'})` at the generic point `η'` of the component, and
   `fiberLength_of_apply_eq_genericPoint` turns that into `fiberLength` of the base change
   `f⁻¹(W) → W`, and `Scheme.comap_stalkSpecializes_maximalIdeal_mem_minimalPrimes_iff` is the
   minimal-prime/component bijection at the level of a scheme's stalks. The twelfth round
   assembled the local formula for `f_W : f⁻¹(W) → W` itself (`ord_mul_fiberLength_eq_finsum`)
   and proved `B ⧸ 𝔮 ≅ 𝒪_{W'_i,x}` for a component given as an integral closed subscheme
   (`Scheme.ord_stalkMap_of_isClosedImmersion`). (i) is **done by the thirteenth round** (`fiberLength_pullback_snd`, with no hypothesis beyond
`[Flat f] [IsClosedImmersion i]`). Still missing: ~~(i) stalks of the base change
   `f_W : X ×_Y W → W` along the closed immersion `W ⟶ Y`: `fiberLength f_W x' = fiberLength f x'`
   (both are `ℓ(𝒪_{X,x} ⧸ 𝔪_{f x} 𝒪_{X,x})`; Mathlib has no API for stalks of fibre products,
   so this needs an affine-local computation via `pullbackSpecIso` and
   `IsAffineOpen.isLocalization_stalk`, or a direct argument that the kernel of
   `𝒪_{X,x} ↠ 𝒪_{X_W,x'}` is `I_W 𝒪_{X,x}`)~~ (done, by the direct argument); ~~(ii) the components `W'_i` of `X_W` as integral
   closed subschemes (reduced induced structure on the closure of `η'_i`, of dimension `k + 1` by
   `height_eq_height_add`) and `dim 𝒪_{X_W,x'} ≤ 1` at points of dimension `k`~~ (done by the
   fourteenth round: `ringKrullDim_stalk_pullback_le_one`, `height_eq_height_genericPoint_add`;
   the integral closed subschemes are `main`'s
   `(IdealSheafData.vanishingIdeal ⟨closure {η'}, isClosed_closure⟩).subscheme`, integral by
   `isIntegral_subscheme_vanishingIdeal_closure_singleton`; their dimension `k + 1 + n` is
   `height_eq_height_genericPoint_add_of_pullback`, computed in `X` so that no `K`-structure on
   `X ×_Y W` is needed); (iii) the
   assembly into a `RatEquivFamily`. Its support bookkeeping is done by the fifteenth round
   (`height_snd_eq_and_maximal_of_height_eq`, `maximal_mem_preimage_singleton_of_height_eq`).
   (α) and the local half of (β) below are **done by the sixteenth round**
   (`Scheme.ord_functionFieldMap_div_algebraMap_stalk`, `isDominant_subschemeι_pullback_snd`),
   with the members taken as reduced closures inside `X ×_Y W` rather than inside `X`; the
   subtraction of the two instances of `ord_mul_fiberLength_eq_finsum` and the choice of the point
   over `y` are **done by the seventeenth round** (`ord_sub_ord_mul_fiberLength_eq_finsum`,
   `IdealSheafData.exists_subschemeι_vanishingIdeal_closure_singleton_eq`); what is left of (β)
   is ~~to apply them~~ **done by the same round** (`ord_mul_fiberLength_eq_finsum_ord`, stated
   for a general flat `f` over an integral `Y` and to be applied to `pullback.snd f i`; its
   hypotheses there: `fiberLength ≠ ⊤` from `fiberLength_ne_top` at a point generic in its fibre,
   the heights from `height_eq_height_genericPoint_add_of_pullback` and
   `height_snd_eq_and_maximal_of_height_eq`, the points `z_x` from
   `IdealSheafData.exists_subschemeι_vanishingIdeal_closure_singleton_eq`). Next: (γ), (δ). Plan for the rest: for a family `F` on `Y` (members `W_j`, functions `r_j`), the family `F'` on
   `X` is indexed by `Σ j, {η' : X ×_Y W_j // η' generic in a component}`, with member
   `W' = (IdealSheafData.vanishingIdeal ⟨closure {pullback.fst η'}, _⟩).subscheme` and function
   `(φ r_j) ^ fiberLength f (pullback.fst η')`, where `φ` is the function-field map of the dominant
   `W' ⟶ W_j`. Still to prove: (α) that morphism `W' ⟶ W_j` (through `X ×_Y W_j`) and the
   comparison of `ord` along `W'` with `ord_stalkMap_of_isClosedImmersion`; (β) the extension of
   `ord_mul_fiberLength_eq_finsum` from non-zero-divisors of the stalk to units of the function
   field (write `r = a / b` with `a, b` in `𝒪_{W,w}`, `Scheme.ord` is additive); (γ) local
   finiteness of `F'` (as for `cycleFlatPullback`: Noetherian affine opens meet finitely many
   `W_j`, each with finitely many components there); (δ) the pointwise identity
   `cycleFlatPullback f F.cycle = F'.cycle`: at `x` maximal in its fibre with `f x` of dimension `k`
   by (β) and `fiberLength_pullback_snd`; at other points both sides vanish, by
   `height_snd_eq_and_maximal_of_height_eq` and because `r_j` is a unit over `η_{W_j}`.) Then `cyclesFlatPullback_mem_ratEquiv` follows
   by summing over a `RatEquivFamily` (members `W'_i`, functions `r|W'_i`, local finiteness as in
   `cycleFlatPullback`). This step needs no supplier: Fulton's proof via the norm formula is
   avoidable with the Stacks route.
   Concrete plan for the order formula (sixth round), as a general commutative-algebra file
   (port target `TauCeti/RingTheory/OrderOfVanishing/Minimal.lean` or similar):
   (a) (**done by the seventh round**, as the `ℕ∞` identities in `TauCeti/RingTheory/Length.lean`
   listed under *What is proved*; what is left of (a) is only packaging them as an integer `e`)
   for a Noetherian ring `B`, `b : B` and a finite `B`-module `M` on which `b` has kernel and
   cokernel of finite length, set `e_B(M, b) := ℓ(M ⧸ bM) - ℓ(ker (b • ·))` in `ℤ` (Stacks
   Section 42.2). Prove it is additive in short exact sequences `0 → N → M → P → 0` from Mathlib's
   six-term `SnakeLemma.δ'` (`exact_δ'_left`, `exact_δ'_right` in
   `Mathlib/Algebra/Module/SnakeLemma.lean`) and `Module.length_eq_add_of_exact`, and that it
   vanishes on finite-length `M` (kernel and cokernel of an endomorphism of a finite-length module
   have equal length);
   (b) (the finite-colength step is `length_quotient_lsmul_submodule_eq`, eighth round)
   with Mathlib's prime filtration (`IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime`,
   `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`), applied to the
   one-dimensional local ring `B` and a nonzerodivisor `b`: the quotients `B ⧸ 𝔪` contribute `0`
   by (a), and the number of quotients `B ⧸ 𝔮` for minimal `𝔮` is `ℓ_{B_𝔮}(B_𝔮)` after localising the
   filtration at `𝔮`. Each contributes `e(B ⧸ 𝔮, b) = ord_{B/𝔮}(b)`. (that identity is
   `length_quotient_lsmul_quotient_eq_ord`, ninth round; what is left of (b) is the filtration
   induction and the count of the minimal-prime pieces). With `e_B(B, b) = Ring.ord B b`
   (the kernel vanishes) this is the formula.
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
  `topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField`). So does the fourteenth
  round's `Scheme.ringKrullDim_stalk_le_one` (general dimension theory, in `RatEquiv.lean` on this
  branch); `height_asFiber_le`, `height_eq_height_add_height_asFiber` and `height_le_height_add`
  belong with `height_eq_height_add` wherever the port puts the dimension shift.
  `isScalarTower_residueField` belongs next to `Scheme.residueFieldBaseAlgebra` in
  `TauCeti/AlgebraicGeometry/Scheme/BaseAlgebra.lean`, and `asFiber_mem_genericPoints`,
  `algebraMap_residueField_fiber` are about Mathlib's `Scheme.Hom.fiber`; they stay in
  `FlatPullback.lean` on this branch to avoid rebuilding everything downstream of those modules.
- The branch's former duplicate `TauCeti.AlgebraicGeometry.isIso_residueFieldMap_of_surjectiveOnStalks`
  was removed in favour of `main`'s `Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks`
  (`TauCeti/AlgebraicGeometry/ResidueField.lean`).
- `length_localization_stalkSpecializes` is about stalks only: at port time move it to
  `TauCeti/AlgebraicGeometry/Scheme/StalkSpecializes.lean` (next to
  `isLocalization_stalkSpecializes`), left in `RatEquiv.lean` to avoid a rebuild. The same holds
  for the `TauCeti.AlgebraicGeometry.Scheme` lemmas on primes of stalks in `RatEquiv.lean`
  (already in that namespace, including the twelfth round's `stalkMinimalPrime`; the closed-immersion
  pair `ker_stalkMap_eq_comap_maximalIdeal`, `ord_stalkMap_of_isClosedImmersion` belongs in a
  stalks-of-closed-immersions file next to Mathlib's `IsClosedImmersion`); `main`'s
  `exists_comap_stalkSpecializes_maximalIdeal_eq_span_singleton` can then be shortened by
  starting from `exists_comap_stalkSpecializes_maximalIdeal_eq`, whose proof repeats its first half.
- The thirteenth round's `Scheme.ker_stalkMap_le_map_ideal_ker`,
  `Scheme.germ_mem_maximalIdeal_of_mem_ker_app` and `Scheme.ker_stalkMap_pullback_fst_le` are about
  stalks of closed subschemes, not Chow groups: at port time they belong with
  `ker_stalkMap_eq_comap_maximalIdeal` in a stalks-of-closed-immersions file (or next to
  `IdealSheafData.ideal_comap_of_le` in `TauCeti/AlgebraicGeometry/IdealSheaf/Affine.lean`).
  `RatEquiv.lean` reaches 719 lines with them (sixteenth round), past 600, so the port should
  open these stalk lemmas, with the other `Scheme` stalk lemmas of `RatEquiv.lean`, as a
  prerequisite PR *feat(AlgebraicGeometry): stalks of closed subschemes and their base changes*.
- `TauCeti.Ring.ord_algebraMap_of_flat` is general commutative algebra: at port time move it to
  `TauCeti/RingTheory/OrderOfVanishing.lean` (left in the Chow file to avoid rebuilding everything
  downstream of that module).
- With `cycleFlatPullback_of_isOpenImmersion`, a reviewer may ask to define `cycleRestrict` as
  `cycleFlatPullback j` (Reuse rubric). It is kept separate because `cycleRestrict` needs neither
  flatness nor local Noetherianity and has a definitional `apply` lemma used throughout
  `Localization.lean`; the comparison lemma records the agreement.
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
3. Files: `TauCeti/AlgebraicGeometry/Chow/FlatPullback.lean` (this branch, done, 559 lines); adds
   the declarations listed for it above, through `cyclesFlatPullback_comp`. The port may split it
   in two: dimension shift
   (through `height_eq_height_add`) and the cycle-level pullback, the second after the first. After: none. Subject: *feat(AlgebraicGeometry/Chow/FlatPullback):
   flat pullback of cycles with generic-length multiplicities*.
4. Files: `TauCeti/RingTheory/Length.lean` (six general length lemmas, +179 lines, done; the
   port may open them as a small prerequisite PR *feat(RingTheory/Length): lengths in four- and
   six-term exact sequences*, which needs no other split),
   `TauCeti/RingTheory/OrderOfVanishing/MinimalPrimes.lean` (new, 215 lines, done; general
   commutative algebra, which the port may open with the `Length.lean` lemmas as that prerequisite
   PR, *feat(RingTheory/OrderOfVanishing): the order of vanishing over minimal primes*) and
   `TauCeti/AlgebraicGeometry/Chow/FlatPullback/RatEquiv.lean` (this branch, started, 872
   lines); adds `Ring.ord_algebraMap_of_flat`, `Ring.ord_mul_length_eq_finsum_minimalPrimes`,
   `ord_stalkMap`, `fiberLength_of_maximalIdeal_eq_bot`, `fiberLength_of_apply_eq_genericPoint`,
   `length_localization_stalkSpecializes`, `Scheme.exists_comap_stalkSpecializes_maximalIdeal_eq`,
   `Scheme.comap_stalkSpecializes_maximalIdeal_mono`,
   `Scheme.comap_stalkSpecializes_maximalIdeal_mem_minimalPrimes_iff`,
   `Scheme.stalkMinimalPrime`, `Scheme.stalkMinimalPrime_bijective`,
   `Scheme.ker_stalkMap_eq_comap_maximalIdeal`, `Scheme.ord_stalkMap_of_isClosedImmersion`,
   `apply_eq_genericPoint_of_forall_specializes`, `fiberLength_of_forall_specializes`,
   `ord_mul_fiberLength_eq_finsum`, `fiberLength_of_isOpenImmersion`,
   `cycleFlatPullback_of_isOpenImmersion`, `Scheme.ker_stalkMap_le_map_ideal_ker`,
   `Scheme.germ_mem_maximalIdeal_of_mem_ker_app`, `Scheme.ker_stalkMap_pullback_fst_le`,
   `fiberLength_comp_of_ker_le`, `fiberLength_eq_one_of_surjective`, `fiberLength_pullback_snd`,
   `Scheme.ringKrullDim_stalk_le_one`, `ringKrullDim_stalk_pullback_le_one`,
   `height_eq_height_genericPoint_add`, `height_eq_height_genericPoint_add_of_pullback`,
   `height_snd_eq_and_maximal_of_height_eq` (fifteenth round),
   `Scheme.ord_functionFieldMap_algebraMap_stalk`, `Scheme.ord_functionFieldMap_div_algebraMap_stalk`,
   `isDominant_subschemeι_pullback_snd` (sixteenth round),
   `finite_generizations_forall_specializes`, `ord_sub_ord_mul_fiberLength_eq_finsum`
   (seventeenth round; with
   `IdealSheafData.exists_subschemeι_vanishingIdeal_closure_singleton_eq` in `main`'s
   `TauCeti/AlgebraicGeometry/IdealSheaf/VanishingIdeal.lean`),
   `Scheme.coheight_eq_one_of_height_apply_genericPoint_eq`,
   `Scheme.IdealSheafData.isLocallyNoetherian_subscheme`, `ord_mul_fiberLength_eq_finsum_ord`
   (seventeenth round), and
   (remaining) `cyclesFlatPullback_mem_ratEquiv`.
   After: 2, 3. Subject: *feat(AlgebraicGeometry/Chow/FlatPullback): flat pullback preserves
   rational equivalence*.
5. Files: `TauCeti/AlgebraicGeometry/Chow/FlatPullback/BaseChange.lean` (stubs of the supplier in
   `TauCeti/Lookahead/ChowFlatPullback/Stubs.lean` until it lands); adds `ChowGroup.flatPullback`,
   `flatPullback_comp`, `flatPullback_properPushforward`. After: 1, 2, 3, 4. Completes the target.
