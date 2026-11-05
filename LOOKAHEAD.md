<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"leray-spectral-sequence","main":"e8758b7b2f82b9b1c3f33b992ab8f499b510240f","status":"partial","suppliers":["sheaf-h-pullback"],"splits":[{"n":1,"after":[],"title":"feat: dimension shifting for right derived functors"},{"n":2,"after":[],"title":"feat: Ext and sheaf cohomology from acyclic resolutions"},{"n":3,"after":[1],"title":"feat: the edge map of the Leray spectral sequence and Leray's acyclicity theorem"},{"n":4,"after":[],"title":"feat: Čech complexes along a functor preserving products"},{"n":5,"after":[4],"title":"feat: Čech complexes of injective sheaves are exact in positive degrees"},{"n":6,"after":[5],"title":"feat: Leray's acyclicity theorem for a covering of a site"},{"n":7,"after":[8,10,14,15],"title":"feat: the Grothendieck spectral sequence"},{"n":8,"after":[],"title":"feat: total complexes of first-quadrant cochain bicomplexes"},{"n":9,"after":[2,5,6,8],"title":"feat: the Čech double complex of a complex of abelian sheaves"},{"n":10,"after":[8],"title":"feat: the spectral sequence of a first-quadrant cochain bicomplex"},{"n":11,"after":[9,10],"title":"feat: the Čech-to-cohomology spectral sequence"},{"n":12,"after":[],"title":"feat: the connecting map of a degreewise split short exact sequence"},{"n":13,"after":[11],"title":"feat: the Čech-to-cohomology spectral sequence of a covering of an object"},{"n":14,"after":[],"title":"feat: the horseshoe lemma for injective resolutions"},{"n":15,"after":[14],"title":"feat: Cartan–Eilenberg resolutions of cochain complexes"},{"n":16,"after":[7],"title":"feat: degeneration of the Cartan–Eilenberg spectral sequence at E₂"},{"n":17,"after":[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],"title":"feat: the Leray and Čech-to-cohomology spectral sequences"}]}-->

# Lookahead: `leray-spectral-sequence` (SchemeAndStackFoundations §2.2)

Built on `main` at `e8758b7b2f82b9b1c3f33b992ab8f499b510240f` (eleventh round, 2026-11-05; `main`
has not moved since the tenth round; #27242 is still open, so its stub stays). Status:
**partial**.

The eleventh round proved the **degeneration of the Grothendieck and Leray spectral sequences**
when the higher derived functors vanish, and with it the roadmap check `leray_test_identity` in
the form "for `f = 𝟙` all differentials vanish from `E₂` on" (see "New in the eleventh round").
What remains of the target is unchanged: naturality in `F` and the identification of the edge map
with `lerayEdge`.

The tenth round built the **Leray spectral sequence itself**: the `E₂ = RˢG(Hᵏ)` page and the
abutment of the Cartan–Eilenberg spectral sequence, the **Grothendieck spectral sequence**
`RˢG(RᵏF(X)) ⇒ Rˢ⁺ᵏ(F ⋙ G)(X)`, and from it `leraySpectralSequence` with
`E₂^{p,q} = Hᵖ(C, Rᵠ f_* F)` and abutment `Hᵖ⁺ᵠ(D, F)`, and the relative form
`Rᵖ g_* Rᵠ f_* F ⇒ Rᵖ⁺ᵠ(g ∘ f)_* F`. See "New in the tenth round". What remains of the target is
naturality in `F` and the identification of the edge map with `lerayEdge` (see "What remains").

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

The latest session (2026-11-04, fourth round, `main` `5f78b5307b9`) computed the **connecting maps
of the row filtration**: the connecting map of `Tot (rows ≥ s + 1) ⟶ Tot (rows ≥ s) ⟶ row s`
followed by the projection onto the row `s + 1` is `(-1)ⁿ` times the map induced in cohomology by
the vertical differentials, and hence identified the **first differential** of the row- and
column-filtration spectral sequences (item (a1) of "What remains" 3(a), now done). See "New in the
latest round".

The newest round (2026-11-04, fifth round, merged `main` forward to `52f9d081237`; #27242 still open
at `fc88ca0a5dc2`, so the stub stays) closed item (a2) of "What remains" 3: **the first
differential of the Čech-to-cohomology spectral sequence is `(-1)ᵠ` times the Čech differential of
the cohomology presheaf `Hᵠ(-, F)`**, so its second page is `Ȟᵖ(U, Hᵠ(F))`. See "New in the fifth
round".

The sixth round (2026-11-04, same `main` `52f9d081237`; #27242 still open at `fc88ca0a5dc2`, so
the stub stays) moved `cech_to_cohomology` from coverings of the terminal object to **coverings of
an arbitrary object `V`**, via the localized site `J.over V`. See "New in the sixth round".

The eighth round (2026-11-05, merged `main` forward to `85f3eb5579d`; #27242 still open at
`fc88ca0a5dc2`, so the stub stays) started the Leray half: the **horseshoe lemma** for injective
resolutions and **Cartan–Eilenberg double complexes** of cochain complexes, the input of the
Grothendieck spectral sequence. See "New in the eighth round".

The seventh round (2026-11-04, merged `main` forward to `57ab0f657d7`; #27242 still open at
`fc88ca0a5dc2`, so the stub stays) closed the remaining Čech item (a3) of "What remains" 3: the
**first differential of the Čech-to-cohomology spectral sequence of a covering of an object `V`**
is `(-1)ᵠ` times the Čech differential of `Hᵠ(-, F)` on `C`. See "New in the seventh round".

## New in the eleventh round: degeneration at `E₂` (no stub used)

No new file; two files of the tenth round grew.

- `TauCeti/Algebra/Homology/SpectralSequence/CartanEilenberg.lean` (now 474 lines, +178; it now
  also imports `TauCeti.CategoryTheory.Abelian.RightDerived` from `main` for the additivity of
  `RˢG`), new section `Degeneration`, namespace `CochainComplex`, for a complex `K` whose
  cohomology is concentrated in degree `0` (`hK : ∀ k, IsZero (K.homology (k + 1))`):
  `isZero_cartanEilenbergSpectralSequence_page_X` (from page `3` on the objects off the row
  `E₂^{s,0}`, i.e. with `p + 2q + 1 ≠ 0`, vanish),
  **`cartanEilenbergSpectralSequence_page_d_eq_zero`** (every differential from page `3` on
  vanishes), `cartanEilenbergSpectralSequencePageSuccXIso` and
  `cartanEilenbergSpectralSequencePageXIsoPageThree` (pages `3 + m` agree with page `3`),
  **`cartanEilenbergSpectralSequenceEInftyIso`** (`E∞` of degree `s` at the filtration index
  `-(s + 1)` is `E₂^{s,0} = RˢG(H⁰(K))`), `isZero_cartanEilenbergSpectralSequenceEInfty` (the
  other limit objects vanish), `isIso_cartanEilenbergSpectralSequence_abutmentFiltrationι` (the
  filtration of the abutment of degree `n` is everything from the index `-n` on) and
  **`cartanEilenbergSpectralSequenceEInftyIsoAbutment`** (that `E∞` is the whole abutment).
  (Generality: stated for the Cartan–Eilenberg spectral sequence of any such `K`, so that the
  Grothendieck and Leray cases are corollaries.)
- `TauCeti/Algebra/Homology/SpectralSequence/Grothendieck.lean` (now 132 lines, +42), new section
  `Degeneration`, namespace `CategoryTheory.Functor`, for an `F`-acyclic object `X`
  (`hX : ∀ k, IsZero ((F.rightDerived (k + 1)).obj X))`): `isZero_homology_mapHomologicalComplex_succ`
  (the cohomology of `F(I)` is then concentrated in degree `0`),
  **`grothendieckSpectralSequence_page_d_eq_zero`** and **`grothendieckSpectralSequenceEInftyIso`**
  (`E∞ ≅ RˢG(R⁰F(X))`).
- `TauCeti/CategoryTheory/Sites/SheafCohomology/Leray/SpectralSequence.lean` (now 275 lines, +78),
  new sections `Degeneration` and `Identity`, namespace `CategoryTheory.Sheaf.H`, for
  `hF : ∀ q, IsZero ((pf.rightDerived (q + 1)).obj F)`: `isZero_leraySpectralSequence_page_X`,
  **`leraySpectralSequence_page_d_eq_zero`**, `leraySpectralSequenceEInftyAddEquiv`
  (`E∞ ≃+ Hᵖ(C, f_* F)`, through `rightDerivedZeroIsoSelf` of the left exact `pf`),
  **`leraySpectralSequenceEInftyAddEquivH`** (`E∞ ≃+ Hⁿ(D, F)`), and
  **`leraySpectralSequence_id_page_d_eq_zero`** — the roadmap check `leray_test_identity`: for
  `pf = 𝟭` (exact, so `Functor.isZero_rightDerived_succ` of `main` applies) every differential
  from `E₂` on vanishes. The stronger reading of the check — that the resulting identification
  `Hᵖ(F) ≅ E₂^{p,0} ≅ E∞ ≅ Hᵖ(F)` is the identity — is the edge-map item (ii) of "What remains".

## New in the tenth round: the Grothendieck and Leray spectral sequences (no stub used)

New files (no existing file changed except the move of `LerayEdge.lean`, below):

- `TauCeti/Algebra/Homology/SpectralSequence/CartanEilenberg.lean` (296 lines):
  - namespace `CategoryTheory.InjectiveResolution`: **`quasiIso_of_isZero_rightDerived`** — for
    `G` left exact and `RⁿG(X) = 0` (`n > 0`), any cochain map from `G(X)` in degree `0` to a
    complex isomorphic to `G(I)`, compatible with `G(X ⟶ I⁰)`, is a quasi-isomorphism.
    **Port note:** general; it belongs in `TauCeti/CategoryTheory/Abelian/RightDerived.lean`
    (split 1's file), kept here to avoid rebuilding that `main` file's dependents.
  - namespace `CochainComplex`, for `G : C ⥤ D` additive: `mapCartanEilenberg G` (`G(J)` as a
    bicomplex, `abbrev`), `cartanEilenbergSpectralSequence G` (its row-filtration spectral
    sequence, filtered by the resolution degree, `abbrev`), `mapCartanEilenbergRowIso` (the row
    `s` of `G(J)` is `cartanEilenbergRow G s`; this explicit isomorphism with identity components
    replaces the definitional equality, which is not reducible and broke `rw`/`simp`),
    `mapCartanEilenbergRowIso_inv_dRow_hom`, `cartanEilenbergSpectralSequenceFirstPageXIso`
    (`E₁ = G(J(Hᵏ)ˢ)`), `cartanEilenbergSpectralSequenceFirstPageXIso_inv_d_hom` (`d₁ = (-1)ᵏ G(d)`),
    `cartanEilenbergSpectralSequencePageTwoHomologyIsoOfEpi` and
    `cartanEilenbergSpectralSequencePageTwoHomologyIso` (the cohomology of the first page is that
    of `G(J(Hᵏ))`, by a morphism of short complexes with the sign `(-1)ᵏ` absorbed in its last
    components), **`cartanEilenbergSpectralSequencePageThreeXIso G s k`** (the classical `E₂`:
    `((…).page 3).X (k + 2s + 1, -(s + 1)) ≅ (G.rightDerived s).obj (K.homology k)`);
    the abutment: `mapCartanEilenbergCoaugmentation` (`G(K) ⟶` row `0` of `G(J)`),
    `mapCartanEilenbergCoaugmentation_comp_d`, **`quasiIso_totalCoaugmentation_mapCartanEilenberg`**
    (for `G` left exact and `Kᵠ` `G`-acyclic, `G(K) ⟶ Tot G(J)` is a quasi-isomorphism, from
    split 8's `quasiIso_totalCoaugmentation` on the flipped bicomplex) and
    **`cartanEilenbergSpectralSequenceAbutmentIso`** (`abutment n ≅ Hⁿ(G(K))`, through split 10's
    `rowFiltrationUpAbutmentIso` and Mathlib's `totalFlipIso`).
- `TauCeti/Algebra/Homology/SpectralSequence/Grothendieck.lean` (90 lines), namespace
  `CategoryTheory.Functor`, for `F : C ⥤ D`, `G : D ⥤ E` additive and an injective resolution `I`
  of `X`: `grothendieckSpectralSequence F G I` (the Cartan–Eilenberg spectral sequence of `G` at
  `F(I)`), **`grothendieckSpectralSequencePageThreeXIso`** (`E₂^{s,k} ≅ RˢG(RᵏF(X))`) and
  **`grothendieckSpectralSequenceAbutmentIso`** (for `G` left exact and `F` sending injectives to
  `G`-acyclics: `abutment n ≅ Rⁿ(F ⋙ G)(X)`).
- `TauCeti/CategoryTheory/Sites/SheafCohomology/Leray/SpectralSequence.lean` (197 lines):
  - namespace `TauCeti.CategoryTheory` (that of split 2's `Ext/AcyclicResolution.lean`):
    **`rightDerivedObjAddEquivExt`** — `RⁿG(F) ≃+ Extⁿ(P, F)` for `G : C ⥤ Ab` corepresented by `P`
    (split 2's `extAddEquivHomologyOfResolution` on the chosen injective resolution). **Port
    note:** general; it belongs at the end of split 2's `Ext/AcyclicResolution.lean` (with a
    `Mathlib.CategoryTheory.Abelian.RightDerived` import), kept here to avoid rebuilding the
    `main` dependents of `Sites/SheafCohomology/AcyclicResolution.lean`.
  - namespace `CategoryTheory.Sheaf.H`, in the setting of `Leray/Edge.lean` (`adj : pb ⊣ pf`, `pb`
    left exact, `pf` additive, now `c : ℤ_K ≅ pb ℤ_J` an isomorphism, enough injectives on both
    sheaf categories): `globalSectionsCorepresentableBy` (`Hom(ℤ_J, -)` is corepresented by
    `ℤ_J`), `pushforwardGlobalSectionsCorepresentableBy` (`Hom(ℤ_J, pf -)` is corepresented by
    `ℤ_K`), **`leraySpectralSequence pf I`**, **`leraySpectralSequencePageThreeXAddEquiv`**
    (`E₂^{p,q} ≃+ H ((pf.rightDerived q).obj F) p`) and
    **`leraySpectralSequenceAbutmentAddEquiv`** (`abutment n ≃+ H F n`), and the relative form
    **`relativeLeraySpectralSequence pf I pg`**, `relativeLeraySpectralSequencePageThreeXIso`
    (`Rᵖ g_* Rᵠ f_* F`) and `relativeLeraySpectralSequenceAbutmentIso` (`Rⁿ(f_* ⋙ g_*) F`).
- Moved (branch-only file, so no compatibility concern): `Sites/SheafCohomology/LerayEdge.lean`
  is now `Sites/SheafCohomology/Leray/Edge.lean`, since `Leray.lean`-style siblings sharing the
  `Leray` prefix must form a directory (placement rubric). Its content is unchanged.

These statements are the target's spectral sequence for a morphism of sites with the higher direct
images written `pf.rightDerived q` (PR #27242 makes `sheafHigherDirectImage` a reducible
abbreviation of exactly this), Mathlib's `Sheaf.H`, and Mathlib's `SpectralSequence` with the
convergence lemmas of split 10.

## New in the ninth round: the rows of the Cartan–Eilenberg double complex (no stub used)

This round proved the Cartan–Eilenberg row property, item 1 of "What remains" (the input of the
`E₂ = RᵖG(Hᵠ)` page of the Grothendieck spectral sequence filtered by the resolution degree). It
extends `TauCeti/CategoryTheory/Abelian/Injective/CartanEilenberg.lean` (split 15; now 470 lines,
+276) and touches no other file:

- general (namespace `CategoryTheory.ShortComplex.LeftHomologyData`):
  `lift_eq_of_factorization` and `ofFactorization` (`@[simps]`) — the left homology data of a
  short complex whose first map factors as `X₁ ↠ A ⟶ Z ⟶ X₂` and whose second map factors as
  `X₂ ⟶ B ↪ X₃`, with `Z` a kernel of `X₂ ⟶ B` and `H` a cokernel of `A ⟶ Z`;
- general (namespace `CategoryTheory.InjectiveResolution`): `ofIso` (`@[simps cocomplex]`), the
  injective resolution of `Z'` with the complex of a resolution of `Z ≅ Z'`. **Port note:** it
  belongs in `main`'s `TauCeti/CategoryTheory/Abelian/Injective/Resolution.lean` (with `ι₀`, see
  the eighth round), kept here to avoid rebuilding that file's dependents;
- namespace `CochainComplex`: `homologyResolution` (`J(Hᵠ)`: `J(Z⁰)` transported along
  `isoHomologyπ₀` in degree `0`, the chosen `injectiveResolution` in degree `q + 1`, so that
  `RᵖG(Hᵠ)` is read off it), `cyclesResolutionSnd` (the chain map `J(Zᵠ) ⟶ J(Hᵠ)`: identity in
  degree `0`, the horseshoe projection in degree `q + 1`), split-mono/epi instances for the
  degreewise components of `cyclesResolutionInl`, `cokernelCyclesResolutionInl`,
  `cartanEilenbergResolutionSnd`, `cyclesResolutionSnd` (and `IsIso` of the last in degree `0`);
- for an additive functor `G : C ⥤ D` into an abelian category: `cartanEilenbergRow G p` (the
  row `q ↦ G(J(Kᵠ)ᵖ)`, defined as `(G.mapHomologicalComplex _).obj (K.cartanEilenberg.flip.X p)`,
  which is definitionally the row `p` of `G` applied to the bicomplex, as split 10's
  `rowFiltrationUpSpectralSequenceFirstPageXIso` and `dRow` use it), `cartanEilenbergRowι`,
  `cartanEilenbergRowSnd` with their `Mono`/`Epi` instances, `cartanEilenbergRowι_cartanEilenbergRowSnd`,
  `cartanEilenbergRow_d`, `cartanEilenbergRowι_d`, `cartanEilenbergRowι_comp_map_flip_d_f`,
  `cartanEilenbergRowLeftHomologyDataZero`, `cartanEilenbergRowLeftHomologyDataSucc`,
  **`cartanEilenbergRowHomologyIso G p q : (cartanEilenbergRow G p).homology q ≅
  G.obj ((homologyResolution q).cocomplex.X p)`**, its characterization
  `liftCycles_homologyπ_cartanEilenbergRowHomologyIso_hom` (the class of a cycle of `G(J(Zᵠ)ᵖ)`
  goes to its image under `G(J(Zᵠ) ⟶ J(Hᵠ))`), the `Epi` instance of `liftCycles ≫ homologyπ`,
  and **`homologyMap_map_flip_d_cartanEilenbergRowHomologyIso_hom`**: under these isomorphisms
  the vertical differentials of `G(J)` induce the differentials of `G(J(Hᵠ))`.

Gotcha for the next round: `(K.cartanEilenberg.flip.X p).X q` and
`(K.cartanEilenbergResolution q).cocomplex.X p` are only definitionally (not reducibly) equal,
so any statement mixing `G.map ((…).f p)` with the row's objects is type-incorrect at reducible
transparency and breaks `rw`/`simp`. The fix used here: wrap the maps into and out of the rows
in typed definitions (`cartanEilenbergRowι`, `cartanEilenbergRowSnd`), prove the bridging lemmas
(`cartanEilenbergRow_d`, `cartanEilenbergRowι_comp_map_flip_d_f`) by `Eq.trans` in term mode, and
make the homology data `abbrev`s so their `K`/`H` reduce.

Next: with split 10 applied to `L = G(cartanEilenberg K)` (rows in resolution degree), combine
`rowFiltrationUpSpectralSequenceFirstPageXIso` with `cartanEilenbergRowHomologyIso` and
`rowFiltrationUpSpectralSequenceFirstPageXIso_inv_d_hom` with
`homologyMap_map_flip_d_cartanEilenbergRowHomologyIso_hom` to get `E₂^{p,q} = RᵖG(Hᵠ(K))`
(through `(homologyResolution q).isoRightDerivedObj`); then the column filtration
(`E₁ = Hᵖ(G J(Kᵠ))`, zero for `p > 0` when `Kᵠ` is `G`-acyclic) for the abutment `Hⁿ(G K)`.

## New in the eighth round: horseshoes and Cartan–Eilenberg resolutions (no stub used)

The remaining half of the target, `leray_spectral_sequence`, is a Grothendieck spectral sequence,
whose input is a Cartan–Eilenberg resolution of the complex `f_* I` (for an injective resolution
`I` of `F`). Neither Mathlib nor `main` has the horseshoe lemma for Mathlib's
`InjectiveResolution` (main's `TauCeti/CategoryTheory/Exact/Resolution/Horseshoe.lean` is for
*finite projective* resolutions in exact categories, and `ExactStructure.exists_conflation_of_
conflation_of_injective` is only its one-step form) or Cartan–Eilenberg resolutions. This round
adds both, as two new files with no dependency on the rest of the branch.

`TauCeti/CategoryTheory/Abelian/Injective/Horseshoe.lean` (new, 357 lines; split 14; under
`@[expose] public section`, since consumers need `horseshoeCocomplex.X n` to unfold to the biproduct), namespace
`CategoryTheory.InjectiveResolution`, for `hS : S.ShortExact` in an abelian category and injective
resolutions `I₁`, `I₃` of `S.X₁`, `S.X₃`:

- `ι₀ I : Z ⟶ I⁰` (the augmentation with source `Z` itself, through `fromSingle₀Equiv`, as the
  branch's `ofShortExact` already does inline), `ι₀_comp_d`, its `Mono` instance, `exact_ι₀`.
  Using `I.ι.f 0` instead makes every composite with `S.f`/`S.g` type-incorrect at reducible
  transparency (its source is the degree-`0` object of the single complex), which breaks `simp`
  and `rw`. **Port note:** this section is general and belongs in `main`'s
  `TauCeti/CategoryTheory/Abelian/Injective/Resolution.lean`; it stays in `Horseshoe.lean` on the
  branch only to avoid rebuilding that file's ~600 dependents, and `ofShortExact`
  (`RightDerived.lean`) can then use `R.ι₀`;
- the inductive construction of the off-diagonal components `σ n : I₃ⁿ ⟶ I₁ⁿ⁺¹`:
  `horseshoeι₀Fst`, `f_comp_horseshoeι₀Fst`, `horseshoeτ`, `g_comp_horseshoeτ`, `horseshoeτ_comp_d`,
  `horseshoeσ₀`, `ι₀_comp_horseshoeσ₀`, the structure `HorseshoeStep` with `horseshoeStepZero`,
  `HorseshoeStep.next`, `horseshoeStep`, and `horseshoeσ`, `horseshoeσ_zero`, `horseshoeσ_comm`,
  `g_comp_ι₀_comp_horseshoeσ_zero`;
- the middle complex: `horseshoeD` (the matrix `[[d, σ], [0, d]]`) with `inl_horseshoeD`,
  `horseshoeD_snd`, `horseshoeD_fst`, `horseshoeD_comp_horseshoeD`, `horseshoeCocomplex`
  (`_X`, `_d`), the augmentation `horseshoeι₀` (`_fst`, `_snd`, `f_comp_horseshoeι₀`,
  `horseshoeι₀_comp_horseshoeD`, `horseshoeι₀_comp_horseshoeCocomplex_d`);
- the chain maps `horseshoeInl`, `horseshoeSnd`, `horseshoeShortComplex` and
  **`horseshoeShortComplex_shortExact`** (degreewise split);
- `mono_horseshoeι₀`, `horseshoe_exact₀` (by refinements) and **`horseshoe : InjectiveResolution
  S.X₂`** (quasi-isomorphism in degree `0` from those, in positive degrees from Mathlib's
  `ShortComplex.ShortExact.exactAt_X₂`), with `horseshoe_cocomplex`, `horseshoe_ι₀`,
  `ι₀_comp_horseshoeInl_f_zero`, `horseshoe_ι₀_comp_horseshoeSnd_f_zero`.

`TauCeti/CategoryTheory/Abelian/Injective/CartanEilenberg.lean` (new, 198 lines; split 15),
namespace `CochainComplex`, for `K : CochainComplex C ℕ` (with `[HasInjectiveResolutions C]` from
`cyclesResolution` on):

- `cyclesShortComplex` (`Zᵠ ⟶ Kᵠ ⟶ Kᵠ/Zᵠ`) with `cyclesShortComplex_shortExact`;
  `cokernelCyclesToCycles` (`Kᵠ/Zᵠ ⟶ Zᵠ⁺¹`) with `π_cokernelCyclesToCycles`,
  `cokernelCyclesToCycles_homologyπ`, its `Mono` instance, `boundariesShortComplex`
  (`Kᵠ/Zᵠ ⟶ Zᵠ⁺¹ ⟶ Hᵠ⁺¹`) with `boundariesShortComplex_shortExact`;
- `cyclesResolution` (`J(Z⁰)` chosen, `J(Zᵠ⁺¹)` the horseshoe of `boundariesShortComplex q`),
  `cartanEilenbergResolution` (`J(Kᵠ)`, the horseshoe of `cyclesShortComplex q`), the chain maps
  `cyclesResolutionInl`, `cartanEilenbergResolutionSnd`, `cokernelCyclesResolutionInl` with their
  augmentation lemmas, `cyclesResolutionInl_cartanEilenbergResolutionSnd`;
- `cartanEilenbergD` (`J(Kᵠ) ⟶ J(Kᵠ/Zᵠ) ⟶ J(Zᵠ⁺¹) ⟶ J(Kᵠ⁺¹)`),
  `cartanEilenbergD_comp_cartanEilenbergD`, **`cartanEilenberg K`** (a
  `HomologicalComplex₂ C (up ℕ) (up ℕ)` whose `q`-th column is `J(Kᵠ)`), `cartanEilenberg_X`,
  `cartanEilenberg_d`, and `cartanEilenbergResolution_ι₀_comp_cartanEilenbergD_f` (the
  augmentations commute with the differentials).

Next (item 1 of "What remains"): the Cartan–Eilenberg property of the rows. In resolution degree
`p` the row `q ↦ J(Kᵠ)ᵖ = (J(Kᵠ⁻¹/Zᵠ⁻¹)ᵖ ⊞ J(Hᵠ)ᵖ) ⊞ J(Kᵠ/Zᵠ)ᵖ` has differential `inl ∘ inl ∘ snd`,
so it is a direct sum of split pieces, preserved by every additive functor `G`; its cohomology is
`J(Hᵠ)ᵖ`. With the branch's cochain bicomplex spectral sequence (split 10) filtered by the
resolution degree this gives `E₁^{p,q} = G(J(Hᵠ)ᵖ)`, `E₂ = RᵖG(Hᵠ(K))`; filtered the other way,
`E₁ = RᵖG(Kᵠ)`, which vanishes for `p > 0` when the `Kᵠ` are `G`-acyclic (for `K = f_* I`: injective),
so the abutment is `Hⁿ(G K)`. For Leray, `G = Γ(D, -)` and `K = f_* I`.

## New in the seventh round: `E₂ = Ȟᵖ(U, Hᵠ(F))` for a covering of `V` (no stub used)

`TauCeti/CategoryTheory/Sites/SheafCohomology/FreeYoneda.lean` (existing file on `main`, +1):
`freeYonedaSheafFunctor` is now `@[expose]`. Its body is needed outside the module to identify an
element of `Hⁿ(W.left, F)` with an element of `Ext(ℤ[W.left], F)` in a proof (Mathlib defines
`Sheaf.H'` through the unfolded functor, and `Sheaf.H'AddEquivExt` cannot be unfolded either).

`TauCeti/CategoryTheory/Sites/SheafCohomology/Over.lean` (existing file on `main`; split 13):

- private `extendedSectionsCorepresentation_homEquiv` and
  `extendedSectionsCorepresentation_homEquiv_sheafPullbackFreeYonedaIso_hom_comp` (the
  corepresentation computes `sheafPullbackFreeYonedaIso`);
- **`GrothendieckTopology.sheafPullbackFreeYonedaIso_hom_naturality`** (`@[reassoc]`): the
  isomorphism `pb ℤ[V] ≅ ℤ[V.left]` is natural in `V : Over U`;
- **`GrothendieckTopology.cohomologyPresheafEvaluationIsoOver_hom_app_naturality`** (`@[reassoc]`)
  and **`Sheaf.cohomologyPresheafObjIsoOverH'_hom_naturality`** /
  **`Sheaf.cohomologyPresheafObjIsoOverH'_inv_naturality`** (`@[reassoc]`): the comparison
  `Hⁿ(V.left, F) ≅ Hⁿ(V, F.over U)` is natural in `V : Over U` (from
  `Adjunction.extEquiv_naturality_left₀`; one `exact` unfolds the components of the comparison,
  with a comment). **Port note:** add the naturality to the module docstring's "Main
  declarations" entry for `cohomologyPresheafObjIsoOverH'` (left out on the branch only to avoid
  a further full rebuild).

`TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/SpectralSequenceOver.lean` (split 13):
**`cechToCohomologyOverSpectralSequenceFirstPageAddEquiv_d`** — under
`cechToCohomologyOverSpectralSequenceFirstPageAddEquiv`, the first differential sends the Čech
cochain `c` of `Hᵠ(-, F)` to `(-1)ᵠ δc`, the restrictions being along the maps
`(Pi.lift fun y ↦ Pi.π _ (m.succAbove y)).left` of fibre products over `V`. With the first page
and abutment of the sixth round this is `cech_to_cohomology` for a covering of an arbitrary object:
`Ȟᵖ(U, Hᵠ(F)) ⇒ Hᵖ⁺ᵠ(V, F)`.

## New in the sixth round: coverings of an object `V` (no stub used)

`TauCeti/CategoryTheory/Sites/SheafCohomology/Over.lean` (existing file on `main`, +22/−8; new
split 13): the comparison of `main`'s `Over.lean` is generalised from the terminal object
`Over.mk (𝟙 U)` of `Over U` to an arbitrary `V : Over U`, which is a modest generalisation of
existing code:

- `GrothendieckTopology.cohomologyPresheafEvaluationIsoOver J U n V` (was `private`, at
  `Over.mk (𝟙 U)` only; now public and for every `V : Over U`):
  `Hⁿ(V.left, -) ≅ Hⁿ(V, (-).over U)`, natural in the coefficient sheaf;
- `Sheaf.cohomologyPresheafObjIsoOverH' F n V : H' F n V.left ≅ H' (F.over U) n V`;
- the instance `(J.overPullback AddCommGrpCat U).Additive` (was a `local instance`; now global with
  a docstring, since the new file needs it too).

`TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/SpectralSequenceOver.lean` (new, 147 lines;
split 13), for a family `f i : u i ⟶ V`, `[HasFiniteProducts (Over V)]` (for instance from
Mathlib's `Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks`), and the exactness
hypotheses of `main`'s `Over.lean` (restriction to `J.over V` preserves finite colimits, its left
adjoint finite limits):

- `ofArrows_mem_over_iff`: `Sieve.ofArrows (Over.mk ∘ f) _ ∈ J.over V (Over.mk (𝟙 V)) ↔
  Sieve.ofArrows u f ∈ J V`;
- `injective_overPullback_obj` (restriction to `J.over V` preserves injective abelian sheaves) and
  the private helper `exactAt_overPullback` (it preserves exactness of a complex in positive
  degrees); with `ShortComplex.Exact.map` these carry an injective resolution of `F` to one of
  `F.over V`. (The port may move `injective_overPullback_obj` into `Over.lean`.);
- `cechToCohomologyOverSpectralSequence f K` and `cechToCohomologyOverSpectralObject f K` (abbrevs:
  the Čech-to-cohomology spectral sequence of the family `Over.mk (f i)` with coefficients in the
  restriction of `K`);
- **`cechToCohomologyOverSpectralSequenceFirstPageAddEquiv`**: its first page at
  `(q + 2p + 1, -(p + 1))` is `∏ₐ Hᵠ(u (a 0) ×_V ⋯ ×_V u (a p), F)` (the fibre products being
  `(∏ᶜ Over.mk (f (a j))).left`), cohomology of `F` itself on `C`;
- **`cechToCohomologyOverAbutmentAddEquiv`**: for a covering family `f`, its abutment in degree
  `n` is `Hⁿ(V, F)`.

The first differential of this spectral sequence is already identified on the localized site by
`cechToCohomologySpectralSequenceFirstPageAddEquiv_d` (applied to `J.over V`, `F.over V`): it is
`(-1)ᵠ` times the Čech differential of `Hᵠ(-, F.over V)`. Transporting it to the Čech differential
of `Hᵠ(-, F)` on `C` needs the naturality of `cohomologyPresheafObjIsoOverH'` in `V : Over U`. The
round attempted it: the free-sheaf half (`sheafPullbackFreeYonedaIso` commutes with the maps induced
by `g : V ⟶ W` and `g.left`) is a short corepresentation argument (`e.homEquiv ((e.uniqueUpToIso
e').hom ≫ k) = e'.homEquiv k`, then `Adjunction.homEquiv_naturality_left` and
`freeYonedaSheafSectionsEquiv_naturality_left`), but the cohomology half cannot unfold
`cohomologyPresheafEvaluationIsoOver`, which is built by `rw [cohomologyPresheafFunctor_eq]` across
the unexposed `freeYonedaSheafFunctor`. The next round should rebuild that isomorphism from
components `F.H'AddEquivExt`, precomposition with `Ext.mk₀ (sheafPullbackFreeYonedaIso J U V).hom`
and `Adjunction.extEquiv` (so that its value is computable), then prove the naturality with
`Adjunction.extEquiv_naturality_left₀`, and state the `_d` theorem for
`cechToCohomologyOverSpectralSequenceFirstPageAddEquiv`.

## New in the fifth round: `E₂ = Ȟᵖ(U, Hᵠ(F))` (no stub used)

`TauCeti/Algebra/Homology/Ext/AcyclicResolution.lean` (+144, now 461 lines; split 2), new section
`Naturality`: for `a : P' ⟶ P` and `τ : G ⟶ G'` with
`hτ : R'.homEquiv (a ≫ f) = τ.app X (R.homEquiv f)` (compatible corepresentations),

- `extOneAddEquivHomology_mk₀_comp` (the class of `φ : P ⟶ Zᵏ⁺¹` goes to the cohomology class of
  `R.homEquiv φ`), `extOneAddEquivHomology_naturality`, `extClassPostcompAddEquiv_mk₀_comp`,
  `extClassPostcompAddEquiv_symm_mk₀_comp`, private `extCyclesAddEquiv_mk₀_comp` (induction);
- **`extAddEquivHomologyOfResolution_naturality`**: `extAddEquivHomologyOfResolution` carries
  precomposition with `a` on `Extⁿ(P, F)` to `Hⁿ` of `(NatTrans.mapHomologicalComplex τ _).app K`.

`TauCeti/CategoryTheory/Sites/SheafCohomology/FreeYoneda.lean` (+7, existing file on `main`):
`freeYonedaSheafCorepresentableBy_homEquiv` (simp; the corepresentation's body is not exposed).

`TauCeti/CategoryTheory/Sites/SheafCohomology/AcyclicResolution.lean` (+24; split 2):
**`Sheaf.H'.addEquivHomologyOfResolution_naturality`** — for `i : V' ⟶ V`, the restriction map of
`F.cohomologyPresheaf n` corresponds to `Hⁿ` of the restriction of sections `K(V) ⟶ K(V')`.

`TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/DoubleComplex.lean` (+102, now 410 lines;
split 9): `sectionsComplexMap` (abbrev, restriction of complexes of sections),
`cechDoubleComplexXIsoPi_hom_f_π_f`, `cechDoubleComplex_d_comp_XIsoPi_hom_π` (the horizontal
differential on products of sections complexes is the alternating sum of face restrictions),
`cechDoubleComplexHomologyIsoPi_hom_π`, `homologyMap_cechDoubleComplex_d_comp_π`,
`cechDoubleComplexHomologyAddEquiv_apply`, and **`cechDoubleComplexHomologyAddEquiv_homologyMap_d`**:
under `cechDoubleComplexHomologyAddEquiv`, `Hᵠ` of the horizontal differential is the Čech
differential `(δc)(b) = ∑ₘ (-1)ᵐ (Hᵠ(-, F)).map (face m) (c (b ∘ m.succAbove))`.

`TauCeti/Algebra/Homology/SpectralSequence/Bicomplex/UpNat.lean` (+50, now 808 lines; split 10):
private `rowFiltrationUpSpectralSequenceFirstPageXIsoTotalRow_congr` (transport along equal
positions, by `subst`), **`rowFiltrationUpSpectralSequenceFirstPageXIso_inv_d_hom`** and
**`columnFiltrationUpSpectralSequenceFirstPageXIso_inv_d_hom`**: the first differential stated
through the bundled identifications `…FirstPageXIso` (the "optional polish" of the previous
round): `iso.inv ≫ d ≫ iso'.hom = (-1)ᵏ • Hᵏ(d_h)`.

`TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/SpectralSequence.lean` (+29; split 11):
**`cechToCohomologySpectralSequenceFirstPageAddEquiv_d`** — under
`cechToCohomologySpectralSequenceFirstPageAddEquiv`, the first differential from
`(q + 2p + 1, -(p + 1))` to `(q + 2(p + 1) + 1, -((p + 1) + 1))` sends the Čech cochain `c` of
`Hᵠ(-, F)` to `(-1)ᵠ δc`. With the first page and abutment already on the branch, this is the
`cech_to_cohomology` spectral sequence `Ȟᵖ(U, Hᵠ(F)) ⇒ Hᵖ⁺ᵠ(T, F)` for a covering family `U` of the
terminal object (the target's "covering of `V`" is this applied on the slice site `C/V`, or with
`T := V` when `C` has a terminal `V`; that restatement is now split 13, see the sixth round).

## New in the latest round: the connecting maps of the row filtration (no stub used)

`TauCeti/Algebra/Homology/SpectralSequence/Bicomplex/UpNat.lean` (now 749 lines, +215):

- `HomologicalComplex₂.dRow K q q'` (`@[expose, simps]`, any shapes `c₁ c₂`): the vertical
  differentials of `K` from the row `q` to the row `q'`, as a morphism between the row complexes
  `((eval C c₂ q).mapHomologicalComplex c₁).obj K`. Not in Mathlib.
- `HomologicalComplex₂.rowsSuccUpShortComplex_δ_comp n`: for `Tot (rows ≥ 1) ⟶ Tot K ⟶ row 0`, the
  connecting map in degree `n`, followed by `Hⁿ⁺¹` of the projection onto the row `0` of
  `K.rowsSuccUp` (the row `1` of `K`) and `extendHomologyIso`, is `(-1)ⁿ • Hⁿ(dRow 0 1)` (cycle
  chase with `HomologySequence.δ_eq`: a cycle `z` of the row `0` lifts to the summand
  `(K.X n).X 0` of `Tot K`, whose total differential is `(-1)ⁿ d_v z`).
- **`HomologicalComplex₂.totalRowUpShortComplex_δ_comp s n`**: for every `s`, under
  `totalRowUpHomologyIso`, the connecting map of `Tot (rows ≥ s + 1) ⟶ Tot (rows ≥ s) ⟶ row s` in
  degree `n + s` followed by `H` of `totalRowUpπ (s + 1)` is `(-1)ⁿ • Hⁿ(dRow s (s + 1))`
  (induction on `s` through `K.rowsSuccUp`, using `main`'s
  `ShortExact.extend_δ_comp_extendHomologyIso_hom` and Mathlib's
  `extendHomologyIso_hom_naturality`).
- **`HomologicalComplex₂.rowFiltrationUpSpectralSequence_page_two_d_eq_dRow p q s k hq hk`**: for
  `q = -(s + 1)` and `p + q = k + s`, the first differential `(p, q) ⟶ (p + 2, q - 1)` is
  `(-1)ᵏ • Hᵏ(dRow s (s + 1))` under the identifications
  `FirstPageXIsoTotalRow ≪≫ extendHomologyIso ≪≫ totalRowUpHomologyIso` of both ends with the
  cohomology of the rows `s` and `s + 1` (these are the isomorphisms that make up
  `rowFiltrationUpSpectralSequenceFirstPageXIso`, with the indices `page_two_d` uses).
- **`HomologicalComplex₂.columnFiltrationUpSpectralSequence_page_two_d_eq`**: the column version,
  `(-1)ᵏ • Hᵏ(K.d s (s + 1))` on the vertical cohomology of the columns (`K.flip.dRow` is `K.d` by
  definition).

The degreewise splitting / `homOfDegreewiseSplit` route suggested by the previous round turned out
unnecessary: a direct cycle chase at `s = 0` plus the induction avoids the `private` splittings.
Split 12 (`CochainComplex.homologyMap_homOfDegreewiseSplit`) is therefore no longer used by the
proof; it is kept in the plan as an independent, correct lemma but the port may drop it.

Lean pitfalls hit (for the next round): writing `rfl` for a `(up ℕ).Rel i j` argument (e.g. of
`ShortExact.δ`) makes the statement type-incorrect at `implicit` transparency, so later `rw`s fail
with "motive is not type correct"/"did not find pattern"; use `ComplexShape.up_mk _ _ rfl`. The
same holds for `extendHomologyIso … (j := k + s) rfl` inside `totalRowUpHomologyIso`: unfold it
by stated `rfl` equations (`e₁`, `e₂` in the proof), not by `simp only [totalRowUpHomologyIso]`.

## Supplier state

The supplier `sheaf-h-pullback` (§2.1) has partly landed: `Sheaf.H.pullback` with
`addEquiv₀_pullback`, `pullback_naturality` and `pullback_δ` is on `main`
(`TauCeti/CategoryTheory/Sites/SheafCohomology/Pullback.lean`, from #22647). The stubs of those four
declarations that the previous round of this branch carried are deleted, and
`LerayEdge.lean` (now `Leray/Edge.lean`) imports the landed module. The higher direct images of §2.1 are in the open
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
replace its import in `Leray/Edge.lean` by `TauCeti.CategoryTheory.Sites.Continuous`.

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

`TauCeti/CategoryTheory/Sites/SheafCohomology/Leray/Edge.lean` (formerly `LerayEdge.lean`; namespace `CategoryTheory.Sheaf.H`),
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
1. ~~A Grothendieck spectral sequence for `G ∘ F`~~: **done** (tenth round, split 7:
   `grothendieckSpectralSequence` with `E₂ = RˢG(RᵏF(X))` and abutment `R•(F ⋙ G)(X)`), and with it
   the **Leray spectral sequence** `leraySpectralSequence` (`E₂ = Hᵖ(C, Rᵠ f_* F) ⇒ Hᵖ⁺ᵠ(D, F)`) and
   its relative form, in `Leray/SpectralSequence.lean` (split 17). Still missing for
   `leray_spectral_sequence` (see 3(b)): (i) **naturality in `F`** — the spectral sequence is
   attached to a chosen resolution `I`; a map `F ⟶ F'` lifts to `I ⟶ I'` and induces a map of
   Cartan–Eilenberg bicomplexes only up to homotopy, so naturality needs either functorial
   Cartan–Eilenberg resolutions (`InjectiveResolution.desc` is not functorial on the nose) or the
   independence of the spectral sequence from page `3` on of the choice (a map of filtered
   complexes inducing an isomorphism on page `3`; morphisms of filtered complexes induce
   morphisms of spectral sequences by `CochainComplex.filtrationFunctorMap` in `main`'s
   `SpectralSequence/Filtered/Naturality.lean`); (ii) the **edge map** `E₂^{n,0} ⟶ Hⁿ(D, F)` identified with
   `lerayEdge` (split 3) — the edge `Hⁿ(C, f_* F) = E₂^{n,0} ↠ E∞^{n,0} ↪ Hⁿ(D, F)` must be compared
   with the pullback-then-counit definition, through `rightDerivedObjAddEquivExt` on both sides;
   (iii) the `Checks` of the README: `leray_test_identity` is **done** in the form "all
   differentials vanish" (eleventh round, `leraySpectralSequence_id_page_d_eq_zero`, with the
   general degeneration `leraySpectralSequence_page_d_eq_zero`); that the collapse isomorphism is
   the identity follows from `lerayEdge_id` once (ii) holds. The other two checks are about
   schemes (`leray_test_finite_cover` needs JacobianChallenge Layer B; `leray_test_not_degenerate`
   needs `R¹f_* O ≠ 0` on `𝔸² ∖ {0}`) and are outside this branch.
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
   (a1) **Done** (latest round): `rowFiltrationUpSpectralSequence_page_two_d_eq_dRow` and
   `columnFiltrationUpSpectralSequence_page_two_d_eq`. (Optional polish for the port: bundle
   `FirstPageXIsoTotalRow ≪≫ extendHomologyIso ≪≫ totalRowUpHomologyIso` into one isomorphism
   taking the filtration indices `i₁ i₂ n` as `FirstPageXIsoTotalRow` does, redefine
   `rowFiltrationUpSpectralSequenceFirstPageXIso` through it, and restate the two theorems as
   `iso.hom ≫ (-1)ᵏ • Hᵏ(…) ≫ iso'.inv`.)
   (a2) **Done** (fifth round): for the Čech double complex, under
   `cechToCohomologySpectralSequenceFirstPageAddEquiv` the first differential is `(-1)ᵠ` times the
   Čech differential of `Hᵠ(-, F)` (`cechToCohomologySpectralSequenceFirstPageAddEquiv_d`), from
   the naturality of `Sheaf.H'.addEquivHomologyOfResolution` in `V`. This gives
   `E₂ = Ȟᵖ(U, Hᵠ(F))`. (a3) **Mostly done** (sixth round): for a covering `f i : u i ⟶ V` of an
   arbitrary object, `cechToCohomologyOverSpectralSequence` with first page
   `∏ₐ Hᵠ(u (a 0) ×_V ⋯ ×_V u (a p), F)` and abutment `Hⁿ(V, F)` (split 13), and (seventh round)
   its first differential in terms of `Hᵠ(-, F)` on `C`
   (`cechToCohomologyOverSpectralSequenceFirstPageAddEquiv_d`). Still missing: the degeneration
   recovering split 6 (optional; split 6 already proves Leray's acyclicity theorem directly).
   (b) `leray_spectral_sequence`: the spectral sequence, its `E₂` page, abutment and the relative
   form for `g ∘ f` are **done** (tenth round, `Leray/SpectralSequence.lean`); naturality in `F`
   and the identification of its edge map with `lerayEdge` remain (item 1 (i)–(ii)).

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
   `Sheaf.H'.exists_d_hom_app_eq_of_resolution` from them; (fifth round, +168 lines) the
   naturality section `extOneAddEquivHomology_mk₀_comp`, `extOneAddEquivHomology_naturality`,
   `extClassPostcompAddEquiv_mk₀_comp`, `extClassPostcompAddEquiv_symm_mk₀_comp`,
   `extAddEquivHomologyOfResolution_naturality`, `Sheaf.H'.addEquivHomologyOfResolution_naturality`
   and `freeYonedaSheafCorepresentableBy_homEquiv` (+7 in `FreeYoneda.lean`). About 480 lines in
   all; if a reviewer asks, the naturality section can be its own follow-up PR (after 2).
   After: none. Can be opened now.
3. **feat: the edge map of the Leray spectral sequence and Leray's acyclicity theorem** — file:
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Leray/Edge.lean` (new, 350 lines). Adds every
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
7. **feat: the Grothendieck spectral sequence** — files:
   `TauCeti/Algebra/Homology/SpectralSequence/CartanEilenberg.lean` (new, 474 lines) and
   `TauCeti/Algebra/Homology/SpectralSequence/Grothendieck.lean` (new, 132 lines). Adds every
   declaration listed in "New in the tenth round" and "New in the eleventh round" for those files
   except the eleventh-round `Degeneration` sections, which are split 16
   (`InjectiveResolution.quasiIso_of_isZero_rightDerived` moved into split 1's `RightDerived.lean`
   by the port, see the port note). After: 8, 10, 14, 15 (and 1 if the port moves
   `quasiIso_of_isZero_rightDerived` into split 1's file). Written.
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
   `quasiIso_totalCoaugmentation_cechDoubleComplex`, `homologyTotalCechDoubleComplexAddEquiv`, and
   (fifth round, +102, now 410 lines) `sectionsComplexMap`, `cechDoubleComplexXIsoPi_hom_f_π_f`,
   `cechDoubleComplex_d_comp_XIsoPi_hom_π`, `cechDoubleComplexHomologyIsoPi_hom_π`,
   `homologyMap_cechDoubleComplex_d_comp_π`, `cechDoubleComplexHomologyAddEquiv_apply`,
   `cechDoubleComplexHomologyAddEquiv_homologyMap_d`.
   After: 2 (`Sheaf.H'.addEquivHomologyOfResolution` and its naturality), 5, 6
   (`isSheafFor_ofArrows_of_mem`), 8. Written.
10. **feat: the spectral sequence of a first-quadrant cochain bicomplex** — files:
   `TauCeti/Algebra/Homology/SpectralSequence/Bicomplex/UpNat.lean` (new, 749 lines),
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
   `columnFiltrationUpSpectralSequenceFirstPageXIso`, `columnFiltrationUpAbutmentIso`, and (latest
   round) `dRow`, `rowsSuccUpShortComplex_δ_comp`, `totalRowUpShortComplex_δ_comp`,
   `rowFiltrationUpSpectralSequence_page_two_d_eq_dRow`,
   `columnFiltrationUpSpectralSequence_page_two_d_eq`, and (fifth round, +50) the private
   `rowFiltrationUpSpectralSequenceFirstPageXIsoTotalRow_congr`,
   `rowFiltrationUpSpectralSequenceFirstPageXIso_inv_d_hom`,
   `columnFiltrationUpSpectralSequenceFirstPageXIso_inv_d_hom` (these three go with the
   first-differential file below). After: 8.
   Written (808 lines in `UpNat.lean`; this is above the 600-line guideline, so the port should
   move the first-differential material — the `FirstPage.lean` lemma, `page_two_d`, `dRow`, the two
   `δ_comp` lemmas and the two `page_two_d_eq` theorems, ~330 lines — into its own file
   `SpectralSequence/Bicomplex/UpNat/FirstDifferential.lean` and PR, after this one). The branch still carries `TauCeti.cokernelOfLEMkIso` and `π_cokernelOfLEMkIso_hom` in
   `TauCeti/Algebra/Homology/ShortComplex/ShortExact.lean` (+28) from an earlier round; nothing
   uses them any more, so the port leaves that file untouched. (~580 lines; if a reviewer asks,
   the FirstPage lemma and `rowFiltrationUpSpectralSequence_page_two_d` can be a follow-up PR.)
11. **feat: the Čech-to-cohomology spectral sequence** — file:
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/SpectralSequence.lean` (new, ~105 lines).
   Adds `cechToCohomologySpectralSequence`, `cechToCohomologySpectralObject`,
   `cechToCohomologySpectralSequenceFirstPageAddEquiv`, `cechToCohomologyAbutmentAddEquiv`, and
   (fifth round) the `E₂ = Ȟᵖ(U, Hᵠ(F))` identification
   `cechToCohomologySpectralSequenceFirstPageAddEquiv_d` (now 140 lines). After: 9, 10. Written.
12. **feat: the connecting map of a degreewise split short exact sequence** — file:
   `TauCeti/Algebra/Homology/HomotopyCategory/DegreewiseSplit.lean` (new, 76 lines). Adds
   `CochainComplex.homologyMap_homOfDegreewiseSplit`. After: none. Can be opened now. (No longer
   used by the proof since the latest round computed the connecting maps directly; the port may
   drop this split.)
13. **feat: the Čech-to-cohomology spectral sequence of a covering of an object** — files:
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Over.lean` (+22/−8, existing file on `main`) and
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/SpectralSequenceOver.lean` (new, 147 lines).
   Adds (public) `GrothendieckTopology.cohomologyPresheafEvaluationIsoOver` for every `V : Over U`,
   `Sheaf.cohomologyPresheafObjIsoOverH'`, the global `Additive` instance for `J.overPullback`,
   `ofArrows_mem_over_iff`, `injective_overPullback_obj`, `cechToCohomologyOverSpectralSequence`,
   `cechToCohomologyOverSpectralObject`, `cechToCohomologyOverSpectralSequenceFirstPageAddEquiv`,
   `cechToCohomologyOverAbutmentAddEquiv`, and (seventh round) the naturality lemmas
   `sheafPullbackFreeYonedaIso_hom_naturality`,
   `cohomologyPresheafEvaluationIsoOver_hom_app_naturality`,
   `Sheaf.cohomologyPresheafObjIsoOverH'_hom_naturality`,
   `Sheaf.cohomologyPresheafObjIsoOverH'_inv_naturality` and
   `cechToCohomologyOverSpectralSequenceFirstPageAddEquiv_d`, with `@[expose]` on
   `freeYonedaSheafFunctor` (`FreeYoneda.lean`, +1). The `Over.lean` naturality (~75 lines) is
   independent of the spectral sequence and may be ported as its own PR first if a reviewer asks.
   After: 11. Written.
14. **feat: the horseshoe lemma for injective resolutions** — file:
   `TauCeti/CategoryTheory/Abelian/Injective/Horseshoe.lean` (new, 357 lines). Adds every
   declaration listed in "New in the eighth round" for that file. After: none. Can be opened now.
15. **feat: Cartan–Eilenberg resolutions of cochain complexes** — file:
   `TauCeti/CategoryTheory/Abelian/Injective/CartanEilenberg.lean` (new, 470 lines). Adds every
   declaration listed in "New in the eighth round" and "New in the ninth round" for that file.
   After: 14. Written. (If a reviewer finds it too long, the ninth-round row property, ~275
   lines, can be its own follow-up PR `feat: the rows of a Cartan–Eilenberg double complex`.)
16. **feat: degeneration of the Cartan–Eilenberg spectral sequence at E₂** — files: the
   `Degeneration` sections (eleventh round) of
   `TauCeti/Algebra/Homology/SpectralSequence/CartanEilenberg.lean` (+178, with the
   `TauCeti.CategoryTheory.Abelian.RightDerived` import) and
   `TauCeti/Algebra/Homology/SpectralSequence/Grothendieck.lean` (+42). Adds every declaration
   listed for those two files in "New in the eleventh round". After: 7. Written. (Split 17's
   degeneration section and `leray_test_identity` use it.)
17. **feat: the Leray and Čech-to-cohomology spectral sequences** —
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Leray/SpectralSequence.lean` (new, 275 lines
   now): `rightDerivedObjAddEquivExt` (moved by the port into split 2's file, see the port note),
   `globalSectionsCorepresentableBy`, `pushforwardGlobalSectionsCorepresentableBy`,
   `leraySpectralSequence`, `leraySpectralSequencePageThreeXAddEquiv`,
   `leraySpectralSequenceAbutmentAddEquiv`, `relativeLeraySpectralSequence`,
   `relativeLeraySpectralSequencePageThreeXIso`, `relativeLeraySpectralSequenceAbutmentIso`,
   and (eleventh round) `isZero_leraySpectralSequence_page_X`,
   `leraySpectralSequence_page_d_eq_zero`, `leraySpectralSequenceEInftyAddEquiv`,
   `leraySpectralSequenceEInftyAddEquivH`, `leraySpectralSequence_id_page_d_eq_zero`
   (written), and still to write: the naturality in `F`, the edge map identified with
   `lerayEdge`, and `cech_to_cohomology` gathered from splits 11 and 13 (with its degeneration
   recovering split 6). After: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16. The only
   split that completes the target. Partly written.
