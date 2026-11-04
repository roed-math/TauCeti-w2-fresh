<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"leray-spectral-sequence","main":"333c9e49143de812ed1452b412193ee9c05501e7","status":"partial","suppliers":["sheaf-h-pullback"],"splits":[{"n":1,"after":[],"title":"feat: dimension shifting for right derived functors"},{"n":2,"after":[1],"title":"feat: the edge map of the Leray spectral sequence and Leray's acyclicity theorem"},{"n":3,"after":[1],"title":"feat: the Grothendieck spectral sequence of a composite of left exact functors"},{"n":4,"after":[],"title":"feat: the Čech double complex of a covering with coefficients in an injective resolution"},{"n":5,"after":[1,2,3,4],"title":"feat: the Leray and Čech-to-cohomology spectral sequences"}]}-->

# Lookahead: `leray-spectral-sequence` (SchemeAndStackFoundations §2.2)

Built on `main` at `333c9e49143de812ed1452b412193ee9c05501e7`. Status: **partial**.

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
- `Functor.isZero_rightDerived_obj_X₃_of_isZero` — `R^{n+2}G(X) = 0 → R^{n+1}G(Q) = 0`;
- `Functor.epi_map_g_of_isZero_rightDerived_one`,
  `Functor.shortExact_map_of_isZero_rightDerived_one` — for left exact `G`, `R¹G(X) = 0` makes
  `0 ⟶ GX ⟶ GI ⟶ GQ ⟶ 0` short exact.

`TauCeti/CategoryTheory/Sites/SheafCohomology/LerayEdge.lean` (namespace `CategoryTheory.Sheaf.H`),
for `adj : pb ⊣ pf` with `pb` exact additive and `c : ℤ_K ⟶ pb ℤ_J` (for a morphism of sites:
`pb = f⁻¹ = u.sheafPullback`, `pf = f_*`, `c` the inverse of `sheafPullbackConstantSheafIso`):

- `lerayEdge adj c F n : H (pf.obj F) n →+ H F n` — the edge map `E₂^{n,0} = Hⁿ(C, f_*F) → Hⁿ(D, F)`,
  with `lerayEdge_apply`, `lerayEdge_naturality`, `lerayEdge_δ`, `addEquiv₀_lerayEdge`,
  `lerayEdge_zero_bijective`, `subsingleton_H_obj_of_injective` (Stacks 072Z input),
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
2. `leray_spectral_sequence` (natural in `F`, the relative form for `g ∘ f` and the
   identification of its `E₂^{n,0}` edge with `lerayEdge`), `cech_to_cohomology` and Leray's
   acyclicity theorem for coverings, from the Čech double complex `Ȟ^p(U, I^q)` of an injective
   resolution `I` (TauCeti's `Cech/` directory has the Čech complex, its augmentation and long
   exact sequence).

## Split plan

1. **feat: dimension shifting for right derived functors** — file:
   `TauCeti/CategoryTheory/Abelian/RightDerived.lean` (+~145 lines in the existing file). Adds
   `InjectiveResolution.ofShortExact`, `Functor.isZero_rightDerived_obj_X₃_of_isZero`,
   `Functor.epi_map_g_of_isZero_rightDerived_one`,
   `Functor.shortExact_map_of_isZero_rightDerived_one`. After: none. Can be opened now.
2. **feat: the edge map of the Leray spectral sequence and Leray's acyclicity theorem** — file:
   `TauCeti/CategoryTheory/Sites/SheafCohomology/LerayEdge.lean` (new, ~320 lines). Adds every
   `lerayEdge*` declaration above and `subsingleton_H_obj_of_injective`. After: 1, and #27242 on
   `main` for its last theorem (`lerayEdge_sheafAdjunctionContinuous_bijective`); without #27242
   that theorem can be held back and everything else opened.
3. **feat: the Grothendieck spectral sequence of a composite of left exact functors** — files
   under `TauCeti/Algebra/Homology/SpectralSequence/Grothendieck*.lean`. After: 1 (its acyclic
   resolution lemma is proved by the dimension shifting of split 1). Not yet written.
4. **feat: the Čech double complex of a covering with coefficients in an injective resolution** —
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/DoubleComplex.lean`. After: none. Not yet
   written.
5. **feat: the Leray and Čech-to-cohomology spectral sequences** —
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Leray.lean`: `leray_spectral_sequence`, its
   naturality, relative form and edge maps, `cech_to_cohomology`, Leray's acyclicity theorem for
   coverings. After: 1, 2, 3, 4. The only split that completes the target. Not yet written.
