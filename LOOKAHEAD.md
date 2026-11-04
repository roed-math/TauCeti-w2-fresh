<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"leray-spectral-sequence","main":"04dc6d30e3935b9ea621d4ebb74d8ff2b0017a9b","status":"partial","suppliers":["sheaf-h-pullback"],"splits":[{"n":1,"after":[],"title":"feat: dimension shifting for right derived functors"},{"n":2,"after":[],"title":"feat: Ext and sheaf cohomology from acyclic resolutions"},{"n":3,"after":[1],"title":"feat: the edge map of the Leray spectral sequence and Leray's acyclicity theorem"},{"n":4,"after":[],"title":"feat: Čech complexes along a functor preserving products"},{"n":5,"after":[4],"title":"feat: Čech complexes of injective sheaves are exact in positive degrees"},{"n":6,"after":[5],"title":"feat: Leray's acyclicity theorem for a covering of a site"},{"n":7,"after":[1,2],"title":"feat: the Grothendieck spectral sequence of a composite of left exact functors"},{"n":8,"after":[],"title":"feat: total complexes of first-quadrant cochain bicomplexes"},{"n":9,"after":[2,5,6,8],"title":"feat: the Čech double complex of a complex of abelian sheaves"},{"n":10,"after":[8],"title":"feat: the spectral sequence of a first-quadrant cochain bicomplex"},{"n":11,"after":[9,10],"title":"feat: the Čech-to-cohomology spectral sequence"},{"n":12,"after":[],"title":"feat: the connecting map of a degreewise split short exact sequence"},{"n":13,"after":[1,2,3,4,5,6,7,8,9,10,11,12],"title":"feat: the Leray and Čech-to-cohomology spectral sequences"}]}-->

# Lookahead: `leray-spectral-sequence` (SchemeAndStackFoundations §2.2)

Built on `main` at `04dc6d30e3935b9ea621d4ebb74d8ff2b0017a9b` (this session, 2026-11-04, merged `main`
forward from `7ed979dc2ea`; #27242 is still open at head `fc88ca0a5dc2`, so its stub stays). Status:
**partial**.

Earlier sessions proved the Čech half of the target's inputs on a general site (Čech complexes of
injective sheaves are exact in positive degrees; Leray's acyclicity theorem for a covering of a site,
the third statement of the target's README), the Leray edge map with Leray's acyclicity theorem for
a morphism of sites, that acyclic resolutions compute `Ext` and sheaf cohomology, and the Čech
double complex `Čᵖ(U, Kᵠ)` with its column cohomology `∏ₐ Hᵠ(U_a, F)` (the first page of
`cech_to_cohomology`). This session added total complexes of first-quadrant *cochain* bicomplexes
(`up ℕ × up ℕ`, absent from Mathlib and `main`), with the quasi-isomorphism from exact coaugmented
rows, and applied it to the Čech double complex: **the cohomology of `Tot Čᵖ(U, Iᵠ)` for an
injective resolution `I` of `F` is `Hⁿ(T, F)`**, the abutment of `cech_to_cohomology`. The latest
session (2026-11-04, second round, same `main`) built the **spectral sequence of a first-quadrant
cochain bicomplex** filtered by rows or columns, with its first page and convergence, and applied it
to the Čech double complex: the **Čech-to-cohomology spectral sequence with first page
`Čᵖ(U, Hᵠ(F))` and abutment `Hⁿ(T, F)`**. See "New in the latest session" below.

The newest session (2026-11-04, third round, `main` `04dc6d30e39`) identified the **first
differential** of the cochain bicomplex spectral sequence with the connecting map of
`Tot (rows ≥ s + 1) ⟶ Tot (rows ≥ s) ⟶ row s` followed by the projection onto row `s + 1`, and
proved that the connecting map of a degreewise split short exact sequence of cochain complexes is
the cohomology map of Mathlib's `homOfDegreewiseSplit`. See "New in the newest session".

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
- `Functor.rightDerivedObjX₁IsoOfShortExact` (earlier session) — `R^{n+2}G(X) ≅ R^{n+1}G(Q)`, read
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
  `lerayEdge_id` and `lerayEdge_comp_apply` (earlier session: the edge map of the identity is the
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

## New in the newest session: the first differential (no stub used)

`TauCeti/Algebra/Homology/SpectralSequence/Filtered/FirstPage.lean` (existing file on `main`, +38):

- `CochainComplex.spectralSequence_first_page_d_eq_δ_comp_homologyMap_π` — for any
  `F : EInt ⥤ CochainComplex C ℤ` with monomorphic steps, the first differential from `(p, q)` to
  `(p + 2, q - 1)` is the connecting map of `F_q ⟶ F_{q+1} ⟶ F_{q+1}/F_q` followed by the
  projection `F_q ⟶ F_q/F_{q-1}` (from `main`'s `spectralSequence_first_page_d_eq` and the
  naturality of connecting maps along `main`'s `TauCeti.cokernelSequenceToSnakeInputL₃`).

`TauCeti/Algebra/Homology/SpectralSequence/Bicomplex/UpNat.lean` (now 534 lines):

- new `rowFiltrationUpObjIso s i hi` (the filtration term of index `i = -s` is `Tot (rows ≥ s)`,
  extended to `ℤ`), `rowFiltrationUpObjIso_hom_extendMap_totalRowsGEUpι`,
  `filtrationFunctor_map_rowFiltrationUpObjIso_hom`;
- `rowFiltrationUpGradedIso` and `π_rowFiltrationUpGradedIso_hom` now take the two filtration
  indices `i₁ i₂` with `i₁ = -(s + 1)`, `i₂ = i₁ + 1` (needed to compare graded pieces at `q` and
  `q - 1`), and are rebuilt from `rowFiltrationUpObjIso` by `cokernel.mapIso`: the documented
  `erw` of the previous round is gone, and `TauCeti.cokernelOfLEMkIso`/`π_cokernelOfLEMkIso_hom`
  (added to `ShortComplex/ShortExact.lean` by an earlier round) are no longer used — **drop them
  when porting split 10** (they are left on the branch only because removing them rebuilds ~640
  modules);
- `rowFiltrationUpSpectralSequenceFirstPageXIsoTotalRow` now takes `(pq) (i₁ i₂) … (s) (hs) (n) (hn)`
  mirroring `CochainComplex.spectralSequenceFirstPageXIsoCokernel`, and uses
  `HomologicalComplex.homologyMapIso`;
- **`rowFiltrationUpSpectralSequence_page_two_d`**: for `q = -(s + 1)`, the differential
  `(p, q) ⟶ (p + 2, q - 1)` of the first page is, under the identifications with the cohomology of
  rows `s` and `s + 1`, the connecting map `Hⁿ(row s) ⟶ Hⁿ⁺¹(Tot (rows ≥ s + 1))` of
  `totalRowUpShortComplex s` (extended to `ℤ`) followed by `Hⁿ⁺¹` of the projection
  `totalRowUpπ (s + 1)`. One hand-written reassociation (commented): the connecting maps are typed
  through `ShortComplex.cokernelSequence`, which `rw`/`simp` do not see through.

`TauCeti/Algebra/Homology/HomotopyCategory/DegreewiseSplit.lean` (new, 76 lines):

- **`CochainComplex.homologyMap_homOfDegreewiseSplit`**: for a short exact sequence of cochain
  complexes over `ℤ` with degreewise splittings `σ`,
  `homologyMap (homOfDegreewiseSplit S σ) n₀ = hS.δ n₀ n₁ h ≫ (shiftIso 1 n₀ n₁ _).inv.app S.X₁`
  (proved by the cycle chase `HomologySequence.δ_eq` and Mathlib's
  `liftCycles_shift_homologyπ`). Not in Mathlib or on `main`. It is the tool for the remaining
  half of "What remains" 3(a).

## Earlier session: the cochain bicomplex spectral sequence (no stub used)

`TauCeti/Algebra/Homology/SpectralSequence/Bicomplex/UpNat.lean` (new, ~440 lines, namespace
`HomologicalComplex₂`), the cohomological counterpart of `main`'s
`TauCeti/Algebra/Homology/SpectralSequence/Bicomplex.lean`, built on split 8's `rowsSuccUp`,
`rowsSuccUpι`, `rowZeroUpπ` and `rowsSuccUpShortComplex_shortExact`:

- `totalRowsGEUp K s` (total complex of the rows `≥ s`, placed in its degrees), `totalRowsGEUpι`
  (inclusion into `Tot K`, instance `mono_totalRowsGEUpι`), `totalRowsGEUpMap` (rows `≥ s + 1` into
  rows `≥ s`, instance `mono_totalRowsGEUpMap`), `totalRowUp K s` (row `s` placed in its degrees),
  `totalRowUpπ`; `totalRowsGEUpι_zero`, `totalRowsGEUpMap_totalRowsGEUpι`,
  `totalRowsGEUpMap_totalRowUpπ`, `isZero_totalRowsGEUp_X`, `totalRowUpShortComplex` and
  `totalRowUpShortComplex_shortExact` (degreewise split), `totalRowUpHomologyIso`,
  `isZero_totalRowUp_homology`;
- the increasing filtration `rowFiltrationUp K : ℤ → Subobject ((Tot K).extend embeddingUpNat)`
  (index `-s` is the rows `≥ s`; everything for indices `≥ 0`) with `rowFiltrationUp_eq`,
  `rowFiltrationUp_eq_succ`, `monotone_rowFiltrationUp`, `rowFiltrationUp_eq_top`,
  `isZero_rowFiltrationUp_X`; graded pieces `rowFiltrationUpGradedIso` (row `s`) with
  `π_rowFiltrationUpGradedIso_hom`;
- `rowFiltrationUpSpectralSequence` (Mathlib's `coreE₂Cohomological`, via `main`'s
  `CochainComplex.spectralSequence` of a filtration), first page
  `rowFiltrationUpSpectralSequenceFirstPageXIsoTotalRow` and
  `rowFiltrationUpSpectralSequenceFirstPageXIso` (at `(k + 2s + 1, -(s + 1))`: `Hᵏ` of row `s`),
  vanishing `isZero_rowFiltrationUpSpectralSequence_page_two_X_of_lt` / `_of_nonneg`, abutment
  `rowFiltrationUpAbutmentIso`, convergence `rowFiltrationUpSpectralSequencePageXIsoEInfty`,
  `isZero_rowFiltrationUp_abutmentFiltration`, `isIso_rowFiltrationUp_abutmentFiltrationι`;
- the column versions `columnFiltrationUpSpectralSequence := K.flip.rowFiltrationUpSpectralSequence`,
  `columnFiltrationUpSpectralSequenceFirstPageXIso` (vertical cohomology of the columns) and
  `columnFiltrationUpAbutmentIso` (via `totalFlipIso`, which uses split 8's
  `totalComplexShapeSymmetryUpNat`).

Small additions to existing files on `main`, used by the above:
`TauCeti/Algebra/Homology/ShortComplex/ShortExact.lean` (+28): `TauCeti.cokernelOfLEMkIso` (for
monomorphisms `a`, `b`, the quotient of the subobject `b` by `a ≫ b` is `cokernel a`) and
`TauCeti.π_cokernelOfLEMkIso_hom` (superseded in the newest session: now unused, not to be
ported); `TauCeti/Algebra/Homology/Embedding/ExtendHomology/Sequence.lean`
(+7): the instance `HomologicalComplex.mono_extendMap`, twin of the existing `epi_extendMap`.

`TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/SpectralSequence.lean` (new, ~105 lines,
namespace `TauCeti.CategoryTheory`):

- `cechToCohomologySpectralSequence U K` (the column-filtration spectral sequence of
  `cechDoubleComplex U K`, i.e. filtered by Čech degree) and `cechToCohomologySpectralObject U K`;
- **`cechToCohomologySpectralSequenceFirstPageAddEquiv`**: for an acyclic resolution `F ⟶ K`, the
  first page at `(q + 2p + 1, -(p + 1))` is `∀ a : Fin (p + 1) → ι, F.H' q (∏ⱼ U (a j))`,
  i.e. `Čᵖ(U, Hᵠ(F))`;
- **`cechToCohomologyAbutmentAddEquiv`**: for an injective resolution and a covering family, the
  abutment in degree `n` is `F.H' n T`. Convergence is `rowFiltrationUpSpectralSequencePageXIsoEInfty`
  applied to this abbreviation.

**Port notes.** (i) Placement: `SpectralSequence/Bicomplex.lean` (on `main`) and the new
`SpectralSequence/Bicomplex/UpNat.lean` sit side by side, as `TotalComplex.lean` and
`TotalComplex/UpNat.lean` do; if the placement rubric asks, move `Bicomplex.lean` to
`Bicomplex/Basic.lean` (a `git mv` plus import updates) in the same PR. (ii) The `erw` this
round used in `π_rowFiltrationUpGradedIso_hom` was removed in the newest session. (iii) Names carry `Up` because `main`'s homological file already
owns `rowFiltration`, `totalRowsGE`, `columnFiltrationSpectralSequence`, ….

## Previous session: cochain total complexes and the Čech abutment (no stub used)

`TauCeti/Algebra/Homology/ComplexShape/Signs.lean` (existing file on `main`, +37 lines):

- the instance `ComplexShape.tensorSignsUpNat : TensorSigns (ComplexShape.up ℕ)` (sign `(-1)ⁿ`;
  Mathlib has only `down ℕ` and `up ℤ`) and its simp lemma `ComplexShape.ε_up_ℕ`;
- the instance `HomologicalComplex₂.totalComplexShapeSymmetryUpNat` (Koszul sign `(-1)^(pq)`), the
  `up ℕ` twin of `main`'s `totalComplexShapeSymmetryDownNat`: it gives Mathlib's
  `totalFlipIso : Tot K.flip ≅ Tot K`, which the column filtration ("What remains" 3(a)) needs
  to pass between rows and columns.

`TauCeti/Algebra/Homology/Embedding/ExtendHomology/Basic.lean` (existing file on `main`, +12 lines):

- `HomologicalComplex.mono_homologyMap_extendMap_iff`, the monomorphism counterpart of the existing
  `epi_homologyMap_extendMap_iff`.

`TauCeti/Algebra/Homology/TotalComplex/UpNat.lean` (new, 611 lines, namespace
`HomologicalComplex₂`), the cohomological counterpart of `main`'s
`TauCeti/Algebra/Homology/TotalComplex.lean`:

- `hasTotal_up_nat`; `totalCoaugmentation K η hη : E ⟶ Tot K` for `η : E ⟶ K.X 0` killed by
  `K.d 0 1`, with `totalCoaugmentation_f`, `comp_totalCoaugmentation`,
  `totalCoaugmentation_total_map`; `isIso_totalCoaugmentation_single` (+
  `singleObjXSelf_inv_comp_single_d`, `singleObjXSelf_inv_comp_f_zero_d`);
- `rowsSuccUp K` (the rows `≥ 1`), `rowsSuccUpι : Tot(rowsSuccUp K)[-1] ⟶ Tot K`,
  `rowZeroUpπ : Tot K ⟶ row 0`, `rowsSuccUpShortComplex`, `rowsSuccUpShortComplex_shortExact`
  (degreewise split), with `ιTotal_rowsSuccUpι_f`, `ιTotal_rowZeroUpπ_f_zero/succ`,
  `rowsSuccUpι_rowZeroUpπ`;
- `quasiIso_total_map_of_rows_up` (a map that is a quasi-isomorphism on every row is one on total
  complexes; induction with `mono_homologyMap_τ₂`/`isIso_homologyMap_τ₂`),
  `quasiIso_totalCoaugmentation_of_rows` (from the single-column bicomplex);
- `rowCoaugmentation K η hη q : single₀ (E.X q) ⟶ row q` (+ `rowCoaugmentation_f_zero`) and
  **`quasiIso_totalCoaugmentation`**: exact coaugmented rows make `E ⟶ Tot K` a quasi-isomorphism.
  Names carry `Up` where `main`'s homological file already uses the plain name (`rowsSucc`,
  `quasiIso_total_map_of_rows`).
- **Port notes.** (i) The file mirrors `main`'s `TotalComplex.lean` (rows `≥ 1` are a subcomplex
  here and a quotient there, so the short exact sequence and the induction run the other way:
  `mono_homologyMap_τ₂` replaces `epi_homologyMap_τ₂`); a reuse reviewer may ask why the two are
  not one construction. They cannot share the short exact sequence, but if asked, `rowsSucc`
  and `rowsSuccUp` can become one definition over any vertical shape on `ℕ` whose relation is
  invariant under `q ↦ q + 1`. (ii) Placement: `TotalComplex.lean` and `TotalComplex/UpNat.lean`
  sit side by side; if the placement rubric asks, move the former to `TotalComplex/Basic.lean`
  (a `git mv` plus import updates) in the same PR. (iii) Three `change`s in `DoubleComplex.lean`
  restate goals in terms of `cechComplexFunctor`/`single₀`, whose terms `cechDoubleComplex` and
  `sectionsComplex` only unfold to. Each carries a comment, as the proof-quality rubric asks.

`TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/DoubleComplex.lean` (+118 lines, now 305):

- `cechDoubleComplexCoaugmentation U K hT : sectionsComplex K T ⟶ (cechDoubleComplex U K).X 0`
  (degree `0` of `cechAugmentation`, natural in `q` by `cechAugmentation_naturality`), with
  `cechDoubleComplexCoaugmentation_f`, `cechDoubleComplexCoaugmentation_f_π` (restriction to the
  members of `U`),
  `cechDoubleComplexCoaugmentation_comp_d` and
  `rowCoaugmentation_cechDoubleComplexCoaugmentation` (its coaugmented rows are the augmented Čech
  complexes `cechAugmentation U hT (K.X q).obj`);
- `quasiIso_totalCoaugmentation_cechDoubleComplex U K hT hU` — for a covering family and a complex
  of injective sheaves, `K(T) ⟶ Tot Č•(U, K•)` is a quasi-isomorphism;
- **`homologyTotalCechDoubleComplexAddEquiv U hT ε hε hε' hK hU n : Hⁿ(Tot Čᵖ(U, Iᵠ)) ≃+ Hⁿ(T, F)`**
  for an injective resolution `ε : F ⟶ I⁰` (via `Sheaf.H'.addEquivHomologyOfResolution`).

## Earlier session: the Čech double complex (no stub used)

`TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/DoubleComplex.lean` (new, 189 lines, namespace
`TauCeti.CategoryTheory`), for a site `(C, J)` with finite products, `U : ι → C` and a cochain complex
`K` of abelian sheaves:

- `quasiIso_cechAugmentation_of_injective` — for a covering family of maps to the terminal object
  `T`, the augmented Čech complex `0 ⟶ I(T) ⟶ Č⁰(U, I) ⟶ ⋯` of an injective abelian sheaf is exact;
- `cechDoubleComplex U K : HomologicalComplex₂ Ab (up ℕ) (up ℕ)` — `Čᵖ(U, Kᵠ)`, outer index the Čech
  degree `p` (main's `HomologicalComplex₂` convention: `.flip.X q` is the row `Č(U, Kᵠ)`,
  `.X p` the column of `p`-cochains), with the definitional lemmas `cechDoubleComplex_d_f`
  (horizontal: Čech differentials) and `cechDoubleComplex_X_d` (vertical: induced by `K`);
- `sectionsComplex K W` — the complex of sections `K(W)` (abbreviation, the form used by
  `Sheaf.H'.addEquivHomologyOfResolution`);
- `cechDoubleComplexXIsoPi U K p` (+ `cechDoubleComplexXIsoPi_inv_f_π`) — column `p` is
  `∏ₐ K(U (a 0) × ⋯ × U (a p))` as a product of complexes;
- `cechDoubleComplexHomologyIsoPi U K p q` — its cohomology is `∏ₐ Hᵠ(K(U_a))` (products of abelian
  groups are exact, `TauCeti.homologicalComplexHomologyFunctor_preservesLimitsOfShape`);
- `cechDoubleComplexHomologyAddEquiv` — for a resolution `F ⟶ K` whose terms are acyclic on all
  finite products of members of `U` (e.g. an injective resolution), the cohomology of column `p`
  in degree `q` is `∀ a : Fin (p + 1) → ι, F.H' q (∏ⱼ U (a j))`: the `E₁` page of `cech_to_cohomology`.

## Earlier session: `Ext` from acyclic resolutions (no stub used)

`TauCeti/Algebra/Homology/Ext/AcyclicResolution.lean` (new, 311 lines, namespace
`TauCeti.CategoryTheory`), in an abelian category with `HasExt`:

- `bijective_extClass_postcomp`, `extClassPostcompAddEquiv` (+ `_apply`) — for `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`
  with `Extᵐ(P, X₂) = Extᵐ⁺¹(P, X₂) = 0`, the connecting map `Extᵐ(P, X₃) ≃+ Extᵐ⁺¹(P, X₁)`;
- `extClass_postcomp_mk₀_eq_zero_iff`, `surjective_extClass_postcomp_mk₀` — `Ext¹(P, X₁)` is the
  cokernel of `Hom(P, X₂) ⟶ Hom(P, X₃)` when `Ext¹(P, X₂) = 0`;
- for an additive `G : C ⥤ Ab` with `R : (G ⋙ forget Ab).CorepresentableBy P` (e.g. `Hom(P, -)`, or
  the sections over `V`, corepresented by `ℤ[V]` via `freeYonedaSheafCorepresentableBy` on `main`):
  `homologyClassOfCycles G k : G(Zᵏ⁺¹K) →+ Hᵏ⁺¹(G(K))`, `surjective_homologyClassOfCycles`,
  `homologyClassOfCycles_eq_zero_iff`, `extOneAddEquivHomology`;
- **`extAddEquivHomologyOfResolution G R ι hι hι' hK hKP n : Ext P F n ≃+ Hⁿ(G(K))`** for every `n`,
  for a resolution `0 ⟶ F ⟶ K⁰ ⟶ ⋯` with `Extᵏ⁺¹(P, Kʲ) = 0` (Hartshorne III.1.2A). The statement
  takes a corepresentable `G` rather than `Hom(P, -)` because `Hom(ℤ[V], -)` on sheaves lands in
  `Ab.{max u v}` while sections land in `Ab.{v}`.

`TauCeti/CategoryTheory/Sites/SheafCohomology/AcyclicResolution.lean` (existing file on `main`,
+34/−49 lines):

- new `Sheaf.H'.addEquivHomologyOfResolution ι hι hι' hK V hKV n : F.H' n V ≃+ Hⁿ(K(V))` — sheaf
  cohomology over `V` from a resolution whose terms are acyclic over `V`;
- `Sheaf.H'.exists_d_hom_app_eq_of_resolution` (on `main`, statement unchanged) is now a five-line
  corollary of it; its private dimension-shift lemma `subsingleton_H'_cycles` is deleted. Its one
  user, `AlgebraicGeometry/Cohomology/HigherDirectImage/Affine.lean`, builds unchanged.

## Earlier session (no stub used)

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
  belongs in the same refactor of `Topology/Sheaves/Cech/Basic.lean` (split 6's PR or a follow-up
  refactor PR).

## What remains

The spectral sequence itself:
1. A Grothendieck spectral sequence for `G ∘ F` with `F` sending injectives to `G`-acyclics, in
   Mathlib's `Abelian.SpectralObject`/`HasSpectralSequence` language: Cartan–Eilenberg (or
   injective) resolutions, the double complex, and the identification of its `E₂` page
   `R^p G (R^q F)`. `main` has the row-filtration spectral sequence of a first-quadrant
   (homological) bicomplex, `TauCeti/Algebra/Homology/SpectralSequence/Bicomplex.lean`, and
   finite/exhaustive-filtration convergence under `.../SpectralSequence/Filtered/`; the `E₂`
   identification and the cohomological reindexing are not there. Acyclic resolutions computing
   `Ext(P, -)`, hence `Hⁿ(V, -)`, are now done (split 2): with `I` an injective resolution of `F`,
   this identifies `Hⁿ(C, F)` with `Hⁿ(Γ(D, f_* I))` (the abutment; `f_*` preserves injectives as
   the right adjoint of an exact functor). The analogue for a general left exact `G` (`R•G` rather
   than `Ext`) still needs a long exact sequence of `Functor.rightDerived`, which neither Mathlib
   nor `main` has; `ofShortExact` and the dimension-shift lemmas of split 1 are its inductive step.
2. ~~Čech acyclicity of injective abelian sheaves on a general site~~ and ~~Leray's acyclicity
   theorem for coverings~~: **done** (`Cech/Injective.lean`, `Cech/Leray.lean`).
3. The Čech double complex `Čᵖ(U, Iᵠ)` is defined, with exact augmented rows, column cohomology
   `∏ₐ Hᵠ(U_a, F)` and — new this session — its cochain total complex with
   `Hⁿ(Tot Č(U, I)) ≃+ Hⁿ(T, F)` (**done**, `TotalComplex/UpNat.lean`, `Cech/DoubleComplex.lean`).
   Now also done (latest session): (a′) the row/column-filtration spectral sequence of a
   first-quadrant *cochain* bicomplex with first page, abutment and convergence
   (`SpectralSequence/Bicomplex/UpNat.lean`), and the Čech-to-cohomology spectral sequence with
   `E₁ = Čᵖ(U, Hᵠ(F))` and abutment `Hⁿ(T, F)` (`Cech/SpectralSequence.lean`).
   Still missing for `cech_to_cohomology`:
   (a) the identification of the first differential. **Half done** (newest session):
   `rowFiltrationUpSpectralSequence_page_two_d` reduces `d₁` to the connecting map `δ` of
   `Tot (rows ≥ s + 1) ⟶ Tot (rows ≥ s) ⟶ row s` followed by the projection onto row `s + 1`.
   Remaining: (a1) show that composite is the map induced in cohomology by the vertical
   differential `row s ⟶ (row s + 1)[1]` with the total-complex sign — apply
   `CochainComplex.homologyMap_homOfDegreewiseSplit` to the extension of
   `totalRowUpShortComplex s`, which needs a degreewise splitting of it (the splittings of
   `rowsSuccUpShortComplex` in `TotalComplex/UpNat.lean` are `private`; make them public, extend
   them along `embeddingUpNatAdd` and `embeddingUpNat`) and the computation
   `homOfDegreewiseSplit ≫ (extendMap (totalRowUpπ (s + 1)))⟦1⟧' = ±(vertical differential)`;
   transport to the column filtration through `K.flip`; (a2) for the Čech double complex, that
   under `cechDoubleComplexHomologyAddEquiv` this is the Čech differential of the presheaf
   `Hᵠ(-, F)` — which needs naturality of `Sheaf.H'.addEquivHomologyOfResolution` in `V`, not
   yet proved. This gives `E₂ = Ȟᵖ(U, Hᵠ(F))`, the statement of `cech_to_cohomology`.
   (b) `leray_spectral_sequence` (natural in `F`, the relative form for `g ∘ f` and the
   identification of its `E₂^{n,0}` edge with `lerayEdge`), from item 1.

## Split plan

1. **feat: dimension shifting for right derived functors** — file:
   `TauCeti/CategoryTheory/Abelian/RightDerived.lean` (+151 lines in the existing file). Adds
   `InjectiveResolution.ofShortExact`, `Functor.rightDerivedObjX₁IsoOfShortExact`,
   `Functor.isZero_rightDerived_obj_X₃_of_isZero`,
   `Functor.epi_map_g_of_isZero_rightDerived_one`,
   `Functor.shortExact_map_of_isZero_rightDerived_one`. After: none. Can be opened now.
2. **feat: Ext and sheaf cohomology from acyclic resolutions** — files:
   `TauCeti/Algebra/Homology/Ext/AcyclicResolution.lean` (new, 311 lines) and
   `TauCeti/CategoryTheory/Sites/SheafCohomology/AcyclicResolution.lean` (+34/−49). Adds
   `bijective_extClass_postcomp`, `extClassPostcompAddEquiv`, `extClassPostcompAddEquiv_apply`,
   `extClass_postcomp_mk₀_eq_zero_iff`, `surjective_extClass_postcomp_mk₀`,
   `homologyClassOfCycles`, `surjective_homologyClassOfCycles`,
   `homologyClassOfCycles_eq_zero_iff`, `extOneAddEquivHomology`,
   `extAddEquivHomologyOfResolution`, `Sheaf.H'.addEquivHomologyOfResolution`, and rederives
   `Sheaf.H'.exists_d_hom_app_eq_of_resolution` from them. After: none. Can be opened now.
3. **feat: the edge map of the Leray spectral sequence and Leray's acyclicity theorem** — file:
   `TauCeti/CategoryTheory/Sites/SheafCohomology/LerayEdge.lean` (new, 350 lines). Adds every
   `lerayEdge*` declaration above and `subsingleton_H_obj_of_injective`. After: 1, and #27242 on
   `main` for its last theorem (`lerayEdge_sheafAdjunctionContinuous_bijective`); without #27242
   that theorem can be held back and everything else opened.
4. **feat: Čech complexes along a functor preserving products** — file:
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/PreservesProducts.lean` (new, 148 lines), or
   better (see the port note) a generalisation of `cechComplexCompIso` in `Cech/Functor.lean` with
   its callers updated. Adds `cechComplexCompIsoOfIsIso`, `cechComplexCompIsoOfIsIso_hom_f_π`,
   `exactAt_cechComplexFunctor_obj_comp_iff`. After: none. Can be opened now.
5. **feat: Čech complexes of injective sheaves are exact in positive degrees** — file:
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/Injective.lean` (new, 184 lines). Adds
   `exactAt_cechComplexFunctor_obj_free_op`, `exactAt_cechComplexFunctor_obj_freeYoneda_op`,
   `exactAt_cechComplexFunctor_obj_of_injective`, `exactAt_cechComplexFunctor_obj_obj_of_injective`.
   After: 4.
6. **feat: Leray's acyclicity theorem for a covering of a site** — file:
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/Leray.lean` (new, 379 lines), plus the
   refactor deriving `TauCeti.Topology.homologyCechComplexIsoH` from it (port note above), which
   removes ~250 duplicated lines. Adds `isSheafFor_ofArrows_of_mem`,
   `quasiIsoAt_cechAugmentation_zero_of_mem`, `homologyZeroCechIso`,
   `homologyMap_comp_homologyZeroCechIso_hom`, `homologyCechComplexIsoH`,
   `homologyCechComplexIsoH_zero`, `homologyMap_comp_homologyCechComplexIsoH_hom`. After: 5.
7. **feat: the Grothendieck spectral sequence of a composite of left exact functors** — files
   under `TauCeti/Algebra/Homology/SpectralSequence/Grothendieck*.lean`. After: 1, 2 (split 2
   identifies the abutment; the `R•G` analogue of split 2 is proved by the dimension shifting of
   split 1 once a long exact sequence of right derived functors exists). Not yet written.
8. **feat: total complexes of first-quadrant cochain bicomplexes** — files:
   `TauCeti/Algebra/Homology/TotalComplex/UpNat.lean` (new, 611 lines),
   `TauCeti/Algebra/Homology/ComplexShape/Signs.lean` (+37) and
   `TauCeti/Algebra/Homology/Embedding/ExtendHomology/Basic.lean` (+12). Adds the instances
   `ComplexShape.tensorSignsUpNat`, `HomologicalComplex₂.totalComplexShapeSymmetryUpNat`,
   `ComplexShape.ε_up_ℕ`,
   `HomologicalComplex.mono_homologyMap_extendMap_iff`, `hasTotal_up_nat`, `totalCoaugmentation`
   (+ `_f`, `comp_totalCoaugmentation`, `totalCoaugmentation_total_map`),
   `singleObjXSelf_inv_comp_single_d`, `isIso_totalCoaugmentation_single`,
   `singleObjXSelf_inv_comp_f_zero_d`, `rowsSuccUp`, `rowsSuccUpι`, `ιTotal_rowsSuccUpι_f`,
   `rowZeroUpπ`, `ιTotal_rowZeroUpπ_f_zero`, `ιTotal_rowZeroUpπ_f_succ`, `rowsSuccUpι_rowZeroUpπ`,
   `rowsSuccUpShortComplex`, `rowsSuccUpShortComplex_shortExact`, `quasiIso_total_map_of_rows_up`,
   `quasiIso_totalCoaugmentation_of_rows`, `rowCoaugmentation`, `rowCoaugmentation_f_zero`,
   `quasiIso_totalCoaugmentation`. After: none. Can be opened now. (If a reviewer asks for it, the
   ~30-line `Signs.lean` instance can be its own tiny PR first.)
9. **feat: the Čech double complex of a complex of abelian sheaves** — file:
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/DoubleComplex.lean` (new, 305 lines). Adds
   `quasiIso_cechAugmentation_of_injective`, `cechDoubleComplex`, `cechDoubleComplex_d_f`,
   `cechDoubleComplex_X_d`, `sectionsComplex`,
   `cechDoubleComplexXIsoPi`, `cechDoubleComplexXIsoPi_inv_f_π`, `cechDoubleComplexHomologyIsoPi`,
   `cechDoubleComplexHomologyAddEquiv`, `cechDoubleComplexCoaugmentation`,
   `cechDoubleComplexCoaugmentation_f`, `cechDoubleComplexCoaugmentation_f_π`,
   `cechDoubleComplexCoaugmentation_comp_d`, `rowCoaugmentation_cechDoubleComplexCoaugmentation`,
   `quasiIso_totalCoaugmentation_cechDoubleComplex`, `homologyTotalCechDoubleComplexAddEquiv`.
   After: 2 (`Sheaf.H'.addEquivHomologyOfResolution`), 5, 6 (`isSheafFor_ofArrows_of_mem`), 8.
   Written.
10. **feat: the spectral sequence of a first-quadrant cochain bicomplex** — files:
   `TauCeti/Algebra/Homology/SpectralSequence/Bicomplex/UpNat.lean` (new, 534 lines),
   `TauCeti/Algebra/Homology/SpectralSequence/Filtered/FirstPage.lean` (+38) and
   `TauCeti/Algebra/Homology/Embedding/ExtendHomology/Sequence.lean` (+7). Adds
   `HomologicalComplex.mono_extendMap`,
   `CochainComplex.spectralSequence_first_page_d_eq_δ_comp_homologyMap_π`,
   `totalRowsGEUp`, `totalRowsGEUpι`, `totalRowsGEUpMap`, `totalRowUp`, `totalRowUpπ`,
   `totalRowsGEUpι_zero`, `totalRowsGEUpMap_totalRowsGEUpι`, `totalRowsGEUpMap_totalRowUpπ`,
   `isZero_totalRowsGEUp_X`, `totalRowUpShortComplex`, `totalRowUpShortComplex_shortExact`,
   `mono_totalRowsGEUpι`, `mono_totalRowsGEUpMap`, `totalRowUpHomologyIso`,
   `isZero_totalRowUp_homology`, `rowFiltrationUp`, `rowFiltrationUp_eq`, `rowFiltrationUp_eq_succ`,
   `monotone_rowFiltrationUp`, `rowFiltrationUp_eq_top`, `isZero_rowFiltrationUp_X`,
   `rowFiltrationUpObjIso`, `rowFiltrationUpObjIso_hom_extendMap_totalRowsGEUpι`,
   `filtrationFunctor_map_rowFiltrationUpObjIso_hom`,
   `rowFiltrationUpGradedIso`, `π_rowFiltrationUpGradedIso_hom`, `rowFiltrationUpSpectralSequence`,
   `rowFiltrationUpSpectralSequenceFirstPageXIsoTotalRow`,
   `rowFiltrationUpSpectralSequence_page_two_d`,
   `rowFiltrationUpSpectralSequenceFirstPageXIso`,
   `isZero_rowFiltrationUpSpectralSequence_page_two_X_of_lt`,
   `isZero_rowFiltrationUpSpectralSequence_page_two_X_of_nonneg`, `rowFiltrationUpAbutmentIso`,
   `rowFiltrationUpSpectralSequencePageXIsoEInfty`, `isZero_rowFiltrationUp_abutmentFiltration`,
   `isIso_rowFiltrationUp_abutmentFiltrationι`, `columnFiltrationUpSpectralSequence`,
   `columnFiltrationUpSpectralSequenceFirstPageXIso`, `columnFiltrationUpAbutmentIso`. After: 8.
   Written. The branch still carries `TauCeti.cokernelOfLEMkIso` and `π_cokernelOfLEMkIso_hom` in
   `TauCeti/Algebra/Homology/ShortComplex/ShortExact.lean` (+28) from an earlier round; nothing
   uses them any more, so the port leaves that file untouched. (~580 lines; if a reviewer asks,
   the FirstPage lemma and `rowFiltrationUpSpectralSequence_page_two_d` can be a follow-up PR.)
11. **feat: the Čech-to-cohomology spectral sequence** — file:
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/SpectralSequence.lean` (new, ~105 lines).
   Adds `cechToCohomologySpectralSequence`, `cechToCohomologySpectralObject`,
   `cechToCohomologySpectralSequenceFirstPageAddEquiv`, `cechToCohomologyAbutmentAddEquiv`, and
   (not yet written) the `E₂ = Ȟᵖ(U, Hᵠ(F))` identification. After: 9, 10. Written in part.
12. **feat: the connecting map of a degreewise split short exact sequence** — file:
   `TauCeti/Algebra/Homology/HomotopyCategory/DegreewiseSplit.lean` (new, 76 lines). Adds
   `CochainComplex.homologyMap_homOfDegreewiseSplit`. After: none. Can be opened now. (Small; if
   a reviewer prefers, it can travel with the PR that finishes "What remains" 3(a1), which uses
   it.)
13. **feat: the Leray and Čech-to-cohomology spectral sequences** —
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Leray.lean`: `leray_spectral_sequence`, its
   naturality, relative form and edge maps (identified with `lerayEdge`), `cech_to_cohomology`
   (with its degeneration recovering split 6; its first page `Hᵠ(U_a, F)` read off by split 2).
   After: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12. The only split that
   completes the target. Not yet written.
