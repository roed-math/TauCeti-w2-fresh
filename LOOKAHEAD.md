<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"leray-spectral-sequence","main":"6c781b0a7341d9d794cf474258f824f4fa65faa2","status":"partial","suppliers":["sheaf-h-pullback"],"splits":[{"n":1,"after":[],"title":"feat: dimension shifting for right derived functors"},{"n":2,"after":[1],"title":"feat: the edge map of the Leray spectral sequence and Leray's acyclicity theorem"},{"n":3,"after":[],"title":"feat: Čech complexes along a functor preserving products"},{"n":4,"after":[3],"title":"feat: Čech complexes of injective sheaves are exact in positive degrees"},{"n":5,"after":[4],"title":"feat: Leray's acyclicity theorem for a covering of a site"},{"n":6,"after":[1],"title":"feat: the Grothendieck spectral sequence of a composite of left exact functors"},{"n":7,"after":[4],"title":"feat: the Čech double complex of a covering with coefficients in an injective resolution"},{"n":8,"after":[1,2,3,4,5,6,7],"title":"feat: the Leray and Čech-to-cohomology spectral sequences"}]}-->

# Lookahead: `leray-spectral-sequence` (SchemeAndStackFoundations §2.2)

Built on `main` at `6c781b0a7341d9d794cf474258f824f4fa65faa2` (this session merged `main` forward
from `8e29268de79`; #27242 is still open, so its stub stays). Status: **partial**.

This session proved the Čech half of the target's inputs on a general site: Čech complexes of
injective sheaves are exact in positive degrees, and Leray's acyclicity theorem for a covering of a
site (the third statement of the target's README). See "New this session" below.

## Supplier state

The supplier `sheaf-h-pullback` (§2.1) has partly landed: `Sheaf.H.pullback` with
`addEquiv₀_pullback`, `pullback_naturality` and `pullback_δ` is on `main`
(`TauCeti/CategoryTheory/Sites/SheafCohomology/Pullback.lean`, from #22647). The stubs of those four
declarations that the previous round of this branch carried are deleted, and
`LerayEdge.lean` now imports the landed module. The higher direct images of §2.1 are in the open
pull request #27242 (head `fc88ca0a5dc24100b268478d2ad74bb1f0259ca8`).

## Stubbed declarations (supplier `sheaf-h-pullback`, PR #27242)

`TauCeti/Lookahead/LeraySpectralSequence/Stubs.lean` holds exactly one declaration.

1. The additivity of the sheaf pushforward along a continuous functor.
   - `Suggested.lean` (SchemeAndStackFoundations): no signature. `grep -n 'higherDirectImage\|sheafPushforwardContinuous' Suggested.lean`
     finds only the unrelated `higherDirectImage_vanishing` for quasi-coherent sheaves on schemes.
     The README §2.1 states in prose: "Define `Sheaf.higherDirectImage pf i := pf.rightDerived i`
     for the sheaf pushforward `pf` of a morphism of sites", which needs `pf` to be additive.
   - PR #27242, file `TauCeti/CategoryTheory/Sites/Continuous.lean`, namespace
     `CategoryTheory.Functor`, section variables
     `{C} [Category* C] {D} [Category* D] (u : C ⥤ D) (A) [Category* A] (J) (K) [u.IsContinuous J K]`:
     `instance [Preadditive A] : (u.sheafPushforwardContinuous A J K).Additive where map_add := rfl`.
   - Stub: the same anonymous instance with the same section variables, body `sorry`.
   - Differences: none from the PR. From the README: the README writes `Sheaf.higherDirectImage pf i`;
     the PR defines it as `Functor.sheafHigherDirectImage u A J K i`, a reducible abbreviation of
     `(u.sheafPushforwardContinuous A J K).rightDerived i`. The branch states its site-level
     hypothesis with `(u.sheafPushforwardContinuous AddCommGrpCat J K).rightDerived (q + 1)`
     directly, which needs nothing from the PR but this instance; once #27242 lands it may be
     written `u.sheafHigherDirectImage AddCommGrpCat J K (q + 1)` with no change of meaning.

The proof uses only the statement of this instance. When #27242 lands: delete `Stubs.lean` and
replace its import in `LerayEdge.lean` by `TauCeti.CategoryTheory.Sites.Continuous`.

## What is proved

`TauCeti/CategoryTheory/Abelian/RightDerived.lean` (existing file on `main`, new section
`DimensionShift`, namespace `CategoryTheory`):

- `InjectiveResolution.ofShortExact hS R` — for `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` short exact with `I`
  injective and an injective resolution `R` of `Q`, the injective resolution `X ⟶ I ⟶ R⁰ ⟶ R¹ ⟶ ⋯`;
- `Functor.rightDerivedObjX₁IsoOfShortExact` (new this session) — `R^{n+2}G(X) ≅ R^{n+1}G(Q)`, read
  off from the two resolutions, whose short complexes in degrees `n + 2` and `n + 1` agree;
- `Functor.isZero_rightDerived_obj_X₃_of_isZero` — `R^{n+2}G(X) = 0 → R^{n+1}G(Q) = 0`, now a
  one-line corollary of the isomorphism;
- `Functor.epi_map_g_of_isZero_rightDerived_one`,
  `Functor.shortExact_map_of_isZero_rightDerived_one` — for left exact `G`, `R¹G(X) = 0` makes
  `0 ⟶ GX ⟶ GI ⟶ GQ ⟶ 0` short exact.

`TauCeti/CategoryTheory/Sites/SheafCohomology/LerayEdge.lean` (namespace `CategoryTheory.Sheaf.H`),
for `adj : pb ⊣ pf` with `pb` exact additive and `c : ℤ_K ⟶ pb ℤ_J` (for a morphism of sites:
`pb = f⁻¹ = u.sheafPullback`, `pf = f_*`, `c` the inverse of `sheafPullbackConstantSheafIso`):

- `lerayEdge adj c F n : H (pf.obj F) n →+ H F n` — the edge map `E₂^{n,0} = Hⁿ(C, f_*F) → Hⁿ(D, F)`,
  with `lerayEdge_apply`, `lerayEdge_naturality`, `lerayEdge_δ`, `addEquiv₀_lerayEdge`,
  `lerayEdge_zero_bijective`, `subsingleton_H_obj_of_injective` (Stacks 072Z input),
  `lerayEdge_id` and `lerayEdge_comp_apply` (new this session: the edge map of the identity is the
  identity, and the edge map of `f ∘ g` is that of `f` for `g_* F` followed by that of `g`, for
  `adj.comp adj₂` and the comparison `c₂ ≫ pb₂.map c`; from `pullback_id_apply` and
  `pullback_comp_apply` on `main` — the edge-map half of the relative form for composites),
  `lerayEdge_one_injective` (first map of the five-term exact sequence) — from the previous round;
- new: `lerayEdge_succ_surjective`, `lerayEdge_succ_injective` — dimension shifting for the edge
  map along `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` with `I` injective and `f_*` of it short exact;
- new: `lerayEdge_bijective_of_isZero_rightDerived` — if `Rᵠ f_* F = 0` for `0 < q ≤ n`, the edge map is
  bijective in degree `n` (for all `n`: Leray's acyclicity theorem, Stacks 0733);
- new: `lerayEdge_injective_of_isZero_rightDerived` — if `Rᵠ f_* F = 0` for `0 < q < n`, it is
  injective in degree `n` (no differential reaches `E₂^{n,0}`);
- `lerayEdge_bijective` — the exact-`f_*` case, now a corollary instead of a separate induction;
- new: `lerayEdge_sheafAdjunctionContinuous_bijective` — Leray acyclicity for a morphism of sites
  `u : C ⥤ D` (uses the stubbed additivity instance).

## New this session (no stub used)

`TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/PreservesProducts.lean` (148 lines, namespace
`TauCeti.CategoryTheory`):

- `cechComplexCompIsoOfIsIso G U Q` — for `G : C ⥤ D` with every `piComparison G (U ∘ a)` an
  isomorphism, `Č(G ∘ U, Q) ≅ Č(U, G.op ⋙ Q)`; with `cechComplexCompIsoOfIsIso_hom_f_π` and
  `exactAt_cechComplexFunctor_obj_comp_iff`. This is `cechComplexCompIso` (`Cech/Functor.lean`,
  thin target) for a target that need not be thin. **Port note:** the port should instead
  generalise `cechComplexCompIso` in place (its thin hypothesis implies the `IsIso` instances, by
  `iso_of_both_ways`), deriving the thin case, so that the two proofs are not duplicated; that
  touches its callers in `Topology/Sheaves/Cech/Pullback.lean`, `AlgebraicGeometry/Cohomology/Cech/`
  and `AdicSpace/Spa/StructurePresheaf/AddCommGrp.lean`.

`TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/Injective.lean` (184 lines):

- `exactAt_cechComplexFunctor_obj_free_op` — for a family of types `S`, the Čech complex of
  `AddCommGrpCat.free.op` (values in `Abᵒᵖ`) is exact in positive degrees (extra degeneracy when
  some `S i` is nonempty, all terms zero otherwise);
- `exactAt_cechComplexFunctor_obj_freeYoneda_op` — the Čech complex of `X ↦ ℤ[y X]` (values in
  `(Cᵒᵖ ⥤ Ab)ᵒᵖ`) is exact in positive degrees, checked at each `W` through `coyoneda.obj (op W)`
  and `exactAt_cechComplexFunctor_obj_comp_iff`;
- `exactAt_cechComplexFunctor_obj_of_injective` — **the Čech complex of an injective presheaf of
  abelian groups is exact in positive degrees, for every family** (apply the exact functor
  `preadditiveYoneda.obj P`, then `P(X) ≅ ULift (Hom(ℤ[y X], P))`);
- `exactAt_cechComplexFunctor_obj_obj_of_injective` — the same for an injective abelian sheaf
  (its presheaf is injective, as sheafification preserves monomorphisms).

`TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/Leray.lean` (379 lines), for a site `(C, J)` with
finite products, terminal `T`, `U : ι → C` with `Sieve.ofArrows U (hT.from ∘ U) ∈ J T`:

- `isSheafFor_ofArrows_of_mem`, `quasiIsoAt_cechAugmentation_zero_of_mem`,
  `homologyZeroCechIso`, `homologyMap_comp_homologyZeroCechIso_hom` — `H⁰(U, F) ≅ H⁰(F)`, natural;
- `homologyCechComplexIsoH U hT hU F hF n` — **Leray's acyclicity theorem for a covering of a
  site**: if `Hᵏ⁺¹(U (a 0) × ⋯ × U (a m), F) = 0` for all `m, a, k`, then
  `Hⁿ(Č(U, F)) ≅ Hⁿ(F)` for every `n`; with `homologyCechComplexIsoH_zero` and the naturality
  `homologyMap_comp_homologyCechComplexIsoH_hom`. For a covering of `V` it applies on `C/V`.
  The proof is the dimension shift of `TauCeti/Topology/Sheaves/Leray.lean` with the flasqueness
  input replaced by `exactAt_cechComplexFunctor_obj_obj_of_injective`; it needs no finiteness of
  `U`. **Port note:** the topological `TauCeti.Topology.homologyCechComplexIsoH` (finite open
  covers) and `TauCeti.Topology.homologyZeroCechIso` should then be derived from these site
  versions (the cover generates a covering sieve of `⊤`; finite products of opens are finite
  intersections), deleting the duplicated dimension shift and dropping `[Finite ι]`; this was
  tried and works except that `homologyCechComplexIsoH_zero` then needs the topological
  `homologyZeroCechIso` (`Topology/Sheaves/Cech/Basic.lean`, unexposed) to be the site one, so it
  belongs in the same refactor of `Topology/Sheaves/Cech/Basic.lean` (split 5's PR or a follow-up
  refactor PR).

## What remains

The spectral sequence itself:
1. A Grothendieck spectral sequence for `G ∘ F` with `F` sending injectives to `G`-acyclics, in
   Mathlib's `Abelian.SpectralObject`/`HasSpectralSequence` language: Cartan–Eilenberg (or
   injective) resolutions, the double complex, and the identification of its `E₂` page
   `R^p G (R^q F)`. `main` has the row-filtration spectral sequence of a first-quadrant
   (homological) bicomplex, `TauCeti/Algebra/Homology/SpectralSequence/Bicomplex.lean`, and
   finite/exhaustive-filtration convergence under `.../SpectralSequence/Filtered/`; the `E₂`
   identification and the cohomological reindexing are not there. The lemma that `G`-acyclic
   resolutions compute `R•G` is the first missing input; `ofShortExact` and the dimension-shift
   lemmas of split 1 are its inductive step.
2. ~~Čech acyclicity of injective abelian sheaves on a general site~~ and ~~Leray's acyclicity
   theorem for coverings~~: **done this session** (`Cech/Injective.lean`, `Cech/Leray.lean`).
3. `leray_spectral_sequence` (natural in `F`, the relative form for `g ∘ f` and the
   identification of its `E₂^{n,0}` edge with `lerayEdge`) and `cech_to_cohomology`, from the
   Čech double complex `Ȟ^p(U, I^q)` of an injective
   resolution `I` (TauCeti's `Cech/` directory has the Čech complex, its augmentation and long
   exact sequence).

## Split plan

1. **feat: dimension shifting for right derived functors** — file:
   `TauCeti/CategoryTheory/Abelian/RightDerived.lean` (+151 lines in the existing file). Adds
   `InjectiveResolution.ofShortExact`, `Functor.rightDerivedObjX₁IsoOfShortExact`,
   `Functor.isZero_rightDerived_obj_X₃_of_isZero`,
   `Functor.epi_map_g_of_isZero_rightDerived_one`,
   `Functor.shortExact_map_of_isZero_rightDerived_one`. After: none. Can be opened now.
2. **feat: the edge map of the Leray spectral sequence and Leray's acyclicity theorem** — file:
   `TauCeti/CategoryTheory/Sites/SheafCohomology/LerayEdge.lean` (new, 350 lines). Adds every
   `lerayEdge*` declaration above and `subsingleton_H_obj_of_injective`. After: 1, and #27242 on
   `main` for its last theorem (`lerayEdge_sheafAdjunctionContinuous_bijective`); without #27242
   that theorem can be held back and everything else opened.
3. **feat: Čech complexes along a functor preserving products** — file:
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/PreservesProducts.lean` (new, 148 lines), or
   better (see the port note) a generalisation of `cechComplexCompIso` in `Cech/Functor.lean` with
   its callers updated. Adds `cechComplexCompIsoOfIsIso`, `cechComplexCompIsoOfIsIso_hom_f_π`,
   `exactAt_cechComplexFunctor_obj_comp_iff`. After: none. Can be opened now.
4. **feat: Čech complexes of injective sheaves are exact in positive degrees** — file:
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/Injective.lean` (new, 184 lines). Adds
   `exactAt_cechComplexFunctor_obj_free_op`, `exactAt_cechComplexFunctor_obj_freeYoneda_op`,
   `exactAt_cechComplexFunctor_obj_of_injective`, `exactAt_cechComplexFunctor_obj_obj_of_injective`.
   After: 3.
5. **feat: Leray's acyclicity theorem for a covering of a site** — file:
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/Leray.lean` (new, 379 lines), plus the
   refactor deriving `TauCeti.Topology.homologyCechComplexIsoH` from it (port note above), which
   removes ~250 duplicated lines. Adds `isSheafFor_ofArrows_of_mem`,
   `quasiIsoAt_cechAugmentation_zero_of_mem`, `homologyZeroCechIso`,
   `homologyMap_comp_homologyZeroCechIso_hom`, `homologyCechComplexIsoH`,
   `homologyCechComplexIsoH_zero`, `homologyMap_comp_homologyCechComplexIsoH_hom`. After: 4.
6. **feat: the Grothendieck spectral sequence of a composite of left exact functors** — files
   under `TauCeti/Algebra/Homology/SpectralSequence/Grothendieck*.lean`. After: 1 (its acyclic
   resolution lemma is proved by the dimension shifting of split 1). Not yet written.
7. **feat: the Čech double complex of a covering with coefficients in an injective resolution** —
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/DoubleComplex.lean`: the double complex
   `Č^p(U, I^q)`, whose rows are exact in positive degrees by split 4. After: 4. Not yet written.
8. **feat: the Leray and Čech-to-cohomology spectral sequences** —
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Leray.lean`: `leray_spectral_sequence`, its
   naturality, relative form and edge maps (identified with `lerayEdge`), `cech_to_cohomology`
   (with its degeneration recovering split 5). After: 1, 2, 3, 4, 5, 6, 7. The only split that
   completes the target. Not yet written.
