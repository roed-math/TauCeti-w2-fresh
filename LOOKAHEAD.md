<!--tauceti-lookahead:v1 {"area":"StableReduction","slug":"relative-ampleness","main":"e8758b7b2f82b9b1c3f33b992ab8f499b510240f","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"refactor(AlgebraicGeometry/RelativeProj): name the generated-in-degree-one condition"},{"n":2,"after":[],"title":"feat(AlgebraicGeometry/LineBundle): tensor powers of line bundles"},{"n":3,"after":[2],"title":"feat(AlgebraicGeometry/LineBundle): global generation of trivial bundles, pullbacks, tensor products and tensor powers"},{"n":4,"after":[2,3],"title":"feat(AlgebraicGeometry/LineBundle): nonvanishing loci pull back; ampleness under affine pullback, powers and globally generated twists"},{"n":5,"after":[4],"title":"feat(AlgebraicGeometry/LineBundle): schemes with an ample line bundle are separated; ampleness on basic-open covers and of exterior products"},{"n":6,"after":[4],"title":"feat(AlgebraicGeometry/ProjectiveSpectrum): O(1) pulls back to an ample line bundle along immersions from quasi-compact schemes"},{"n":7,"after":[1],"title":"feat(AlgebraicGeometry/RelativeProj): the symmetric algebra is generated in degree one and its relative Proj is proper"},{"n":8,"after":[2,4,5],"title":"feat(AlgebraicGeometry/LineBundle): sections over nonvanishing loci extend; ampleness pulls back along immersions"},{"n":9,"after":[2,3,4,5,8],"title":"feat(AlgebraicGeometry/LineBundle): relatively ample line bundles"},{"n":10,"after":[2,3,4,5,8,9],"title":"feat(AlgebraicGeometry/LineBundle): relative ampleness composes after twisting by a large power"},{"n":11,"after":[],"title":"feat(AlgebraicGeometry/IntersectionNumber): intersection numbers of powers"},{"n":12,"after":[],"title":"feat(AlgebraicGeometry/Modules): the sheaf associated with a finite module is of finite type"},{"n":13,"after":[],"title":"feat(RingTheory/GradedAlgebra): finiteness and generation of the degree-one part of a graded algebra"},{"n":14,"after":[1,2,3,4,5,6,7,8,9,10,11,12],"title":"feat(AlgebraicGeometry/Morphisms): relatively very ample line bundles, projective morphisms, projective bundles and blowups"},{"n":15,"after":[],"title":"feat(AlgebraicGeometry/RelativeGluing): recognise the glued scheme of a relative gluing datum"},{"n":16,"after":[],"title":"feat(AlgebraicGeometry/Modules): pull back graded sections, and Proj of them as a base change over affine opens"},{"n":17,"after":[1,16],"title":"feat(AlgebraicGeometry/RelativeProj): charts of the base change of a relative Proj over small affine opens, and the pulled-back algebra stays of finite type and generated in degree one"},{"n":18,"after":[1,15,16,17],"title":"feat(AlgebraicGeometry/RelativeProj): the relative Proj commutes with base change"},{"n":19,"after":[],"title":"feat(AlgebraicGeometry/RelativeProj): functoriality of the relative Proj"},{"n":20,"after":[1,7,13,19],"title":"feat(AlgebraicGeometry/RelativeProj): closed immersions of relative Proj from maps surjective in degree one"},{"n":21,"after":[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20],"title":"feat(AlgebraicGeometry/Morphisms): projective schemes over a ring are the projective morphisms to its spectrum, and projective morphisms are stable under base change"}]}-->
# Lookahead: `relative-ampleness` (StableReduction, Layer 2)

Built on `main` at `e8758b7b2f82b9b1c3f33b992ab8f499b510240f`. Status: **partial**. Target text
(StableReduction README, Layer 2): "Extend Tau Ceti's invertible-sheaf API with tensor powers,
Cartier divisors, pullback, degree on components, global generation, and relative ampleness.
Build projective morphisms and relative `Proj` of a finitely generated graded quasi-coherent
algebra." The target has no pinned forms in `StableReduction/Suggested.lean`.

## Stubbed declarations: none left

Sixth session (2026-11-04, 00:05 UTC), still true in the twenty-seventh. The supplier `relative-proj-twisting-sheaf`
(SchemeAndStackFoundations §0.3) has landed the part this target consumes, in
`TauCeti/AlgebraicGeometry/RelativeProj/TwistingSheaf.lean` on `main`. The stub file
`TauCeti/Lookahead/RelativeAmpleness/Stubs.lean` is deleted and the proof now uses the landed
declarations. No `sorry` remains anywhere on the branch. The supplier's open PR #27145
(`O(m) ⊗ O(n) ≅ O(m + n)`) is not consumed, so it is not stubbed. `suppliers` in the header is
therefore empty. `SchemeAndStackFoundations/Suggested.lean` pins no Lean signature for this
supplier: grepping it for `twist`, `relativeProj` and `GeneratedInDegreeOne` finds only unrelated
Frobenius-twist declarations.

The earlier stubs and what replaced them:

1. `CategoryTheory.CommMon.relativeProjTwistingSheaf (n : ℤ) : A.relativeProj.Modules`. This is
   now on `main` with the same signature the stub had, which was copied from the earlier
   supplier PR #22384. It is used unchanged.
2. `CategoryTheory.CommMon.isInvertible_relativeProjTwistingSheaf_one (hA : A.IsGeneratedInDegreeOne) :
   isInvertible _ (A.relativeProjTwistingSheaf 1)` (stub). `main` landed the stronger
   ```
   theorem _root_.CategoryTheory.CommMon.isInvertible_relativeProjTwistingSheaf
       (h : ∀ U : X.Opens, IsAffineOpen U →
         Algebra.adjoin (A.gradedSectionsGrading U 0)
           (A.gradedSectionsGrading U 1 : Set (⨁ n, Γ(A.X n, U))) = ⊤)
       (n : ℤ) : AlgebraicGeometry.SheafOfModules.isInvertible A.relativeProj (A.relativeProjTwistingSheaf n)
   ```
   and the proof uses it at `n = 1`.
3. `CategoryTheory.CommMon.IsGeneratedInDegreeOne` (stub, a `sorry` predicate). `main` writes the
   condition inline, as the hypothesis `h` above. Split 1 names it: it adds the predicate
   `CommMon.IsGeneratedInDegreeOne A` with exactly that body, plus `isGeneratedInDegreeOne_iff`,
   and restates `isInvertible_relativeProjTwistingSheaf` with `(h : A.IsGeneratedInDegreeOne)`.
   That theorem has no other users on `main`.

## Changes in the twenty-seventh session (2026-11-05, 06:10 UTC)

- `main` is still `e8758b7b2f82b9b1c3f33b992ab8f499b510240f` (`git merge origin/main`: already up
  to date). The supplier PR #27145 is still not consumed, so there are still no stubs.
- **First step towards composition: functoriality of the relative `Proj` and closed immersions
  between relative `Proj`s.** The composition plan below needs to compare relative `Proj`s along
  morphisms of graded algebras; nothing on `main` or the branch did that before.
  - New file `TauCeti/AlgebraicGeometry/RelativeProj/Functor.lean` (new split 19, needs only
    `main`). For `φ : A ⟶ B` a morphism of graded algebras with quasi-coherent components:
    `CommMon.gradedSectionsGradedHom φ U`, the graded ring homomorphism
    `⨁ n, Γ(Aₙ, U) → ⨁ n, Γ(Bₙ, U)` (on `main`'s `CommMon.gradedSectionsMap`), commuting with
    restriction; the condition `CommMon.IrrelevantLeMap φ` (over every affine open the irrelevant
    ideal of the target lies in the ideal generated by that of the source, as `Proj.map` needs),
    implied by surjectivity in positive degrees (`CommMon.irrelevantLeMap_of_surjective`); the
    morphism `CommMon.relativeProjMap φ hφ : Proj_X(B) ⟶ Proj_X(A)` (Mathlib's `colimMap` of the
    natural transformation `Proj (⨁ Γ(Bₙ, U)) ⟶ Proj (⨁ Γ(Aₙ, U))` between the gluing diagrams,
    kept private), with its value on charts (`relativeProjCover_f_relativeProjMap`), lying over
    `X` (`relativeProjMap_relativeProjToBase`), `relativeProjMap_id`, `relativeProjMap_comp`,
    the cartesian square with the charts (`isPullback_relativeProjMap`, by pasting with `main`'s
    `isPullback_relativeProjCover`), and `isClosedImmersion_relativeProjMap`: surjective in
    positive degrees on sections over affine opens ⇒ closed immersion (local on the target over
    the charts, where it is `main`'s `Proj.isClosedImmersion_map_of_grade_subset_range`).
  - New file `TauCeti/AlgebraicGeometry/RelativeProj/ClosedImmersion.lean` (new split 20):
    `CommMon.surjective_app_of_isGeneratedInDegreeOne` (into an algebra generated in degree one,
    surjectivity on affine sections in degree one gives it in every positive degree, through
    split 13's `GradedAlgebra.mem_closure_grade_one`), the resulting closed-immersion criterion
    `CommMon.isClosedImmersion_relativeProjMap_of_isGeneratedInDegreeOne` and
    `CommMon.irrelevantLeMap_of_isGeneratedInDegreeOne`, and two consequences:
    `GradedQuasicoherentAlgebra.isClosedImmersion_relativeProjMap_counit` (**`Proj_X(A)` is a
    closed subscheme of `ℙ(A₁) = Proj_X(Sym A₁)` for `A` generated in degree one**, through the
    counit `Sym A₁ ⟶ A` of `main`'s adjunction, an isomorphism in degree one by the instance
    `isIso_counit_app_hom_hom_hom_one`), and
    `isClosedImmersion_relativeProjMap_gradedSymmetricAlgebra_map` (**an epimorphism
    `F ⟶ E` of quasicoherent sheaves gives a closed immersion `ℙ(E) ⟶ ℙ(F)`**, via the instance
    `epi_gradedSymmetricAlgebra_map_hom_hom_hom_one` and `main`'s
    `Scheme.Modules.Hom.app_surjective_of_epi_of_isAffineOpen`). The docstring of
    `Morphisms/Projective.lean` states the first fact in prose; it is now a theorem.
- Splits renumbered: the two new files are splits 19 and 20; the old split 19
  (`Morphisms/ProjectiveOver.lean`, base change) is now split 21 and still the last one, listed
  after every other split.
- Verified: `lake build` green and `lookahead-check` ok. No `sorry` anywhere on the branch.
  `#lint` (Batteries' environment linters) passes on both new modules.
- Rubric audit:
  - API: `relativeProjMap` comes with its chart description, base compatibility, identity and
    composition laws and the cartesian square; it and the gluing transformation are not exposed
    (the chart lemma is the interface), and the transformation is private;
  - generality: the closed-immersion criterion is proved once for any `φ` into an algebra
    generated in degree one, and the counit and `Sym ψ` cases are one-line consequences;
  - naming/placement: the declarations about graded algebras sit in `CategoryTheory.CommMon`
    like `main`'s `relativeProj`, `relativeProjCover` and `gradedSectionsMap`;
  - proof quality: where the open cover's index type is an affine open only up to unfolding,
    or where instance search does not see through `X.Modules`, the proofs use explicit
    `Eq.trans` chains or supplied instances, each with a comment.

## Changes in the twenty-sixth session (2026-11-05, 04:20 UTC)

- `main` moved to `e8758b7b2f82b9b1c3f33b992ab8f499b510240f` and is merged in with no conflicts.
  Its only new commit changes a CI workflow, no file of this branch. The supplier PR #27145 is
  still not consumed, so there are still no stubs.
- **Steps 2 and 4 of the general base change are finished: projective morphisms are stable under
  arbitrary base change.**
  - New file `TauCeti/AlgebraicGeometry/RelativeProj/BaseChange.lean` (new split 18). Rather than
    gluing a chart over every affine open of `S'` (the plan of the twenty-fifth session), it
    restricts the gluing to the affine opens of `S'` lying over affine opens of `S`:
    `AffineZariskiSiteOver g` (a subtype of `S'.AffineZariskiSite`, with its basic-open order) and
    the open cover `directedCoverOver g`. Its `LocallyDirected` instance is inherited from
    Mathlib's `directedCover` through `exists_lift_trans_eq` (a basic open of such an affine open
    again lies over an affine open of `S`), so no `set_option` is needed.
    `GradedQuasicoherentAlgebra.relativeProjGluingDataOver` restricts `main`'s
    `relativeProjGluingData` to this cover. Split 15's `RelativeGluingData.isoOfIsPullback` is then
    applied twice: once with the charts of `Proj_{S'}(g^* A)` itself
    (`relativeProjGluingDataOverIso`), once with split 17's charts
    `projPullbackToPullbackRelativeProj` into `Proj_S(A) ×_S S'`, which are natural by split 17's
    `proj_map_restrict_projPullbackToRelativeProj` and `projPullbackToRelativeProj_eq`
    (`relativeProjGluingDataOverToPullback`). The result:
    `GradedQuasicoherentAlgebra.relativeProjPullbackIso : Proj_{S'}(g^* A) ≅ Proj_S(A) ×_S S'`,
    over `S'` (`relativeProjPullbackIso_hom_snd`), given on charts by
    `projPullbackToPullbackRelativeProj` (`relativeProjCover_f_relativeProjPullbackIso_hom`), and
    the cartesian square `isPullback_relativeProjPullback`.
  - `Morphisms/ProjectiveOver.lean` (now split 19): the instance
    `TauCeti.AlgebraicGeometry.isProjective_pullback_snd`, `X ×_S S' ⟶ S'` is projective for every
    projective `f : X ⟶ S` and every `g : S' ⟶ S` (the base change of the closed immersion into
    `Proj_S(A)` is a closed immersion into `Proj_S(A) ×_S S' ≅ Proj_{S'}(g^* A)`, which is
    projective by `isProjective_relativeProjToBase_pullback`), and its mirror
    `isProjective_pullback_fst`. With them, `IsProjective` respects isomorphisms
    (`respectsIso_isProjective`: postcomposition with `e : S ≅ S'` is base change along `e.inv`)
    and is stable under base change as a `MorphismProperty`
    (`isStableUnderBaseChange_isProjective`), as Mathlib has for `IsProper`.
  - The five special cases of base change, now consequences of the general instance, are deleted:
    `isProjective_pullback_snd_spec_map_algebraMap`, `isProjective_pullback_snd_spec_map`,
    `isProjective_pullback_snd_fromSpec`, `isProjective_pullback_snd_spec_map_fromSpec` and
    `isProjective_pullback_snd_of_isAffine`. Nothing else used them, and the file no longer
    imports `main`'s `ProjectiveSpectrum/SymmetricBaseChange.lean`.
- Verified: `lake build` green and `lookahead-check` ok. No `sorry` anywhere on the branch. The
  environment linters (simpNF, unusedArguments, docBlame, …) pass on the three touched modules.
- Rubric audit:
  - reuse: the gluing reuses split 15's recognition lemma twice instead of a hand-made
    `glueMorphisms` over every affine open; local directedness reuses Mathlib's
    `Cover.exists_lift_trans_eq` for `directedCover`; the general base change replaced (rather than
    sat beside) the five affine special cases;
  - API: the isomorphism comes with its compatibility over `S'`, on charts, and as an
    `IsPullback`; the projectivity statements are instances, as for Mathlib's `IsProper`;
  - proof quality: the naturality proofs are term-mode chains, with a comment, because the indices
    are not reducibly affine opens and `rw` motives are ill-typed (as in split 17);
  - documentation: the `@[stacks]` tags were left off because the tags could not be checked from
    the sandbox; `RelativeProj/Pullback.lean`'s docstring now points to the new file.

## Changes in the twenty-fifth session (2026-11-05, 03:10 UTC)

- `main` is still `85f3eb5579df5ca44ba8cd0921d614b41ab72174` (`git merge origin/main`: already up
  to date). The supplier PR #27145 is still not consumed, so there are still no stubs.
- **Step 3 of the general base change is finished: generation in degree one over arbitrary affine
  opens.**
  - New file `TauCeti/RingTheory/Localization/Closure.lean` (77 lines), pure commutative algebra:
    for a localization `T = M⁻¹S` and a subring `B ⊆ S` containing `M`, if every element of
    `G ⊆ T` is `y / m` with `y ∈ B`, `m ∈ M`, then so is every element of the subring generated by
    `G` (`TauCeti.IsLocalization.exists_mul_eq_algebraMap_of_mem_closure`), and an `x ∈ S` whose
    image lies in that subring has a multiple `m * x ∈ B`
    (`TauCeti.IsLocalization.exists_mul_mem_of_mem_closure`). Working with abstract rings `S`, `T`
    avoids the heartbeat timeouts of the twenty-fourth session, which came from unifying powers in
    `⨁ n, Γ(Aₙ, U)`.
  - `main`'s `Modules/GradedAlgebra/Localization.lean`: the private
    `exists_pow_mul_of_eq_restrictGradedSections` (homogeneous sections over `D(f)` are
    restrictions of homogeneous sections over `U` up to a power of `f`, from `main`'s
    `Scheme.Modules.exists_pow_smul_eq_map`) and the locality lemma
    `CategoryTheory.CommMon.adjoin_gradedSectionsGrading_eq_top_of_span_eq_top` (generation in
    degree one over an affine `U` follows from generation over basic opens `D(f)`, `f` ranging over
    a set generating the unit ideal). The proof writes the adjoined subalgebra as the subring
    generated by degrees `0` and `1` (Mathlib's `Algebra.adjoin_eq_ring_closure`), applies the
    lemma above to `⨁ n, Γ(Aₙ, U) → ⨁ n, Γ(Aₙ, D(f))` (a localization away from `f` by `main`'s
    `CommMon.isLocalization_gradedSections_basicOpen`), and concludes with Mathlib's
    `Submodule.mem_of_span_eq_top_of_smul_pow_mem`.
  - `RelativeProj/Pullback.lean`: `GradedQuasicoherentAlgebra.isGeneratedInDegreeOne_pullback`,
    `g^* A` is generated in degree one when `A` is. The file now imports `main`'s
    `RelativeProj/TwistingSheaf.lean` (where `IsGeneratedInDegreeOne` lives, after split 1) instead
    of `RelativeProj/Basic.lean`, which `TwistingSheaf.lean` imports.
- `Morphisms/ProjectiveOver.lean` (split 18):
  `TauCeti.AlgebraicGeometry.isProjective_relativeProjToBase_pullback`, the relative `Proj` of
  `g^* A` is projective over the new base for every `g : S' ⟶ S`, when `A` is generated in degree
  one, of finite type and with finite degree-zero part. What remains of base change is to identify
  `Proj_{S'}(g^* A)` with `Proj_S(A) ×_S S'` (steps 2 and 4 below).
- **Step 2 started: the charts do not depend on `U`** (split 17,
  `GradedQuasicoherentAlgebra.projPullbackToRelativeProj_eq`). For affine opens `U₁`, `U₂` of `X`
  with `V ⊆ g⁻¹ U₁ ∩ g⁻¹ U₂`, the charts over `V` through `U₁` and through `U₂` are equal. They agree
  on the basic opens `D(h) ⊆ V` lying over basic opens common to `U₁` and `U₂` (Mathlib's
  `exists_basicOpen_le_affine_inter`), by naturality in `V` and `projPullbackToRelativeProj_basicOpen`,
  and `Proj` of the sections over these `D(h)` is an open cover of `Proj (⨁ n, Γ((g^* A)ₙ, V))`
  (open immersions by `main`'s `CommMon.isPullback_proj_restrictGradedSections`), so Mathlib's
  `Scheme.Cover.hom_ext` applies. Three private helpers: the agreement on one `D(h)`
  (`proj_map_restrict_projPullbackToRelativeProj_eq`), the open immersion
  (`isOpenImmersion_proj_map_restrictGradedSections`), and covering
  (`exists_basicOpen_le_preimage_basicOpen`, `exists_proj_map_restrictGradedSections_eq`). This
  removes the need to fix a `U` per affine open of `S'` in the gluing of step 2. Also new: the
  charts into `Proj_X(A) ×_X Y` are open immersions (instance
  `isOpenImmersion_projPullbackToPullbackRelativeProj`) and cover it
  (`exists_projPullbackToPullbackRelativeProj_eq`). Lean pitfall: an
  anonymous constructor `⟨⟨h, …⟩, p, hp⟩` for the subtype-indexed cover timed out at `whnf`, but
  binding the index first (`let j : J := ⟨h, …⟩`) and applying the helper to `j.1` is instant.
  Likewise `obtain` on a hypothesis in a goal that mentions `(Scheme.Cover.mkOfCovers …).f h`
  timed out, so the per-index equality is a separate lemma.
- Split 17 now also needs split 1 (`IsGeneratedInDegreeOne`); it is already after 16, and 16 is
  after nothing, so its `after` list becomes `[1, 16]`.
- Verified: `lake build` green and `lookahead-check` ok. No `sorry` anywhere on the branch.
- Rubric audit:
  - reuse: the algebraic step is stated once for abstract localizations rather than inline for
    graded sections; it reuses Mathlib's `Subring.closure_induction`, `IsLocalization.exists_of_eq`,
    `Algebra.adjoin_eq_ring_closure` and `Submodule.mem_of_span_eq_top_of_smul_pow_mem`, and
    `main`'s `exists_pow_smul_eq_map` and `isLocalization_gradedSections_basicOpen`; the pullback
    statement reuses split 16's `adjoin_gradedSectionsGrading_pullback_eq_top` and split 17's
    `span_setOf_basicOpen_le_preimage_eq_top`, exactly as the two finiteness transfers do;
  - API: the locality lemma has the same shape as `finiteType_gradedSections_of_span_eq_top` next
    to it; the predicate `IsGeneratedInDegreeOne` is not exposed under the module system, so the
    pullback statement goes through `isGeneratedInDegreeOne_iff`;
  - placement: the commutative-algebra lemma lives under `RingTheory/Localization`, beside the
    existing `IntegerMultiple.lean`, not in the scheme files.

## Changes in the twenty-fourth session (2026-11-05, 01:10 UTC)

- `main` moved to `85f3eb5579df5ca44ba8cd0921d614b41ab72174` and is merged in with no conflicts.
  Its new commits (exponential decay, a tooling bump) touch no file of this branch. The supplier
  PR #27145 is still not consumed, so there are still no stubs.
- **Step 1 of the general base change is finished** (new split 17,
  `AlgebraicGeometry/RelativeProj/Pullback.lean`). For `g : Y ⟶ X`, a graded quasicoherent
  algebra `A` on `X`, and affine opens `U` of `X` and `V ⊆ g⁻¹ U` of `Y`:
  - `GradedQuasicoherentAlgebra.projPullbackToRelativeProj` is the morphism
    `Proj (⨁ n, Γ((g^* A)ₙ, V)) ⟶ Proj (⨁ n, Γ(Aₙ, U)) ⟶ Proj_X(A)`, and
    `isPullback_projPullbackToRelativeProj` shows it is cartesian over `Spec Γ(Y, V) ⟶ Y ⟶ X`,
    by pasting split 16's square with the chart of `Proj_X(A)` over `U`;
  - `projPullbackToPullbackRelativeProj` and `isPullback_projPullbackToPullbackRelativeProj`:
    `Proj (⨁ n, Γ((g^* A)ₙ, V))` is the preimage of `V` in `Proj_X(A) ×_X Y ⟶ Y`;
  - `proj_map_restrict_projPullbackToRelativeProj` (naturality in `V`) and
    `projPullbackToRelativeProj_basicOpen` (independence of `U` along a basic open of `U`), the
    compatibilities the gluing of step 2 needs.
  The chart over `U` read over `Spec Γ(X, U)`, which `Morphisms/ProjectiveOver.lean` proved inline,
  is now the lemma `CommMon.isPullback_relativeProjCover_fromSpec` in `main`'s
  `RelativeProj/Basic.lean`, and `ProjectiveOver.lean` uses it.
- **Step 3 over small affine opens** (split 16, `PullbackSections.lean`): the pulled-back graded
  sections span the sections of `g^* A` over `V` (`span_range_pullbackGradedSectionsLE`, from the
  base-change statement already proved there), so generation in degree one
  (`adjoin_gradedSectionsGrading_pullback_eq_top`), finite type (`finiteType_pullback_sections`)
  and finiteness in degree zero (`finite_pullback_sections_zero`) pass from `U` to `V`. Two
  restriction lemmas for the pulled-back sections were added for the naturality above
  (`restrictGradedSections_comp_pullbackGradedSectionsLE`,
  `pullbackGradedSectionsLE_comp_restrictGradedSections`).
- **Step 3 over arbitrary affine opens, for the two finiteness conditions** (split 17): finite type
  of the graded sections is local on basic-open covers
  (`CommMon.finiteType_gradedSections_of_span_eq_top` in `main`'s
  `Modules/GradedAlgebra/Localization.lean`, from Mathlib's `RingHom.finiteType_ofLocalizationSpan`
  and `main`'s `CommMon.isLocalization_gradedSections_basicOpen`), and the basic opens of an affine
  `V ⊆ Y` lying over affine opens of `X` cover `V`. Hence
  `GradedQuasicoherentAlgebra.finiteType_pullback_sections_of_isAffineOpen` and
  `finite_pullback_sections_zero_of_isAffineOpen` (the latter by Mathlib's
  `Module.Finite.of_localizationSpan'`, as in `main`'s `finite_sections_of_isAffineOpen`).
- **Not finished: generation in degree one over arbitrary affine opens.** The mathematics is
  written out (a section over `V` that is a polynomial in degree-one sections over each `D(h)` is,
  after multiplication by a power of `h`, one over `V`, by `exists_pow_smul_eq_map` and
  `IsLocalization.exists_of_eq`), but the Lean proof hit heartbeat timeouts and was removed. Pitfalls
  for the next attempt: (1) never let `rw` unify two different powers `a ^ m₁`, `a ^ m₂` of an
  element of `⨁ n, Γ(Aₙ, U)`: the unifier unfolds the direct-sum power; combine equations with
  `congrArg₂` instead, and `generalize` the image of `f` to an opaque `a`; (2) state the homogeneous
  step for a general degree `k` and membership in `gradedSectionsGrading _ k` (instantiating a
  lemma at the literal `0` with a witness from `DirectSum.mem_summand` timed out); (3) prove
  `h ▸ Algebra.mem_top` memberships as `Algebra.eq_top_iff.mp h _`; (4) passing an equation
  produced by one private lemma (`ι a ^ m * ι x = ι y`) to another private lemma with the
  syntactically same hypothesis still timed out in the main proof, so the localization step
  (`IsLocalization.exists_of_eq` for `ι.toAlgebra`) should live in the same lemma as the
  `Algebra.adjoin_induction`, or the equation should be stated at `U` level (`aᵏ (aᵐ x) = aᵏ y`)
  before leaving that lemma.
- The old final split 17 is now split 18, listed after the new split 17.
- Verified: `lake build` green and `lookahead-check` ok. No `sorry` anywhere on the branch.
- Rubric audit:
  - reuse: the inline chart-over-`Spec` square of `ProjectiveOver.lean` was factored into the
    lemma above rather than duplicated; the cartesian squares are pasted with Mathlib's
    `IsPullback.paste_horiz` and `IsPullback.of_right`; the compatibility along basic opens is
    `colimit.w` of the gluing diagram, and the restriction lemmas reuse `main`'s
    `Scheme.Hom.pullbackSectionsLE_map` and `CommMon.restrictGradedSections_comp`;
  - API: the spanning statement is public, since the three transfer theorems and the remaining
    step 3 over arbitrary affine opens all go through it; the base-change existence statement
    stays private;
  - proof quality: the morphism equalities are stated by term-mode `trans` chains because the
    chart index `⟨U, hU⟩ : X.AffineZariskiSite` is not reducibly the cover's index type, which
    makes `rw` motives ill-typed; one `have key` restates a goal whose open is
    `(toOpensFunctor X).obj U'` as `U`, which the comment explains.

## Changes in the twenty-third session (2026-11-05, 00:10 UTC)

- `main` moved to `67aa17161ba1908f8a85182bfdf2d4ccaf21171c` and is merged in with no conflicts. None of its new commits touches a file
  of this branch or adds one of its declarations. The supplier PR #27145 is still not consumed, so
  there are still no stubs.
- **Step 1 of the general base change is done** (new independent split 16). For `g : Y ⟶ X`, a
  graded quasicoherent algebra `A` on `X`, and affine opens `U` of `X` and `V ⊆ g⁻¹ U` of `Y`:
  - pulling back sections is a graded ring homomorphism
    `⨁ n, Γ(Aₙ, U) → ⨁ n, Γ((g^* A)ₙ, V)` (`pullbackGradedSectionsLEGradedHom`). It is
    multiplicative because the tensor comparison `g^* (M ⊗ N) ⟶ g^* M ⊗ g^* N` sends the pullback
    of `x ⊗ y` to `g^* x ⊗ g^* y` (`Scheme.Hom.δ_app_pullbackSections_μ`, from Mathlib's
    `Adjunction.unit_app_tensor_comp_map_δ` and `main`'s `pushforward_μ_app_tmul`);
  - it exhibits the target as the base change of the source along `g.appLE U V`, degreewise by
    `main`'s `isBaseChange_pullbackSectionsLEBaseLinear` for the square `g ≫ 𝟙 = 𝟙 ≫ g`;
  - hence `Proj (⨁ n, Γ((g^* A)ₙ, V))` is the fibre product of `Proj (⨁ n, Γ(Aₙ, U))` and
    `Spec Γ(Y, V)` over `Spec Γ(X, U)`
    (`isPullback_proj_map_pullbackGradedSectionsLEGradedHom`, by `main`'s
    `Proj.isPullback_map_of_isBaseChange`).
- The old final split 16 is now split 17, listed after the new split 16.
- Verified: `lake build` green and `lookahead-check` ok. `#lint` passes over the import closure of
  `GradedAlgebra/PullbackSections.lean`. No `sorry` anywhere on the branch.
- Rubric audit:
  - reuse: no new base-change machinery. The degreewise base change is `main`'s
    `isBaseChange_pullbackSectionsLEBaseLinear`, the direct sum is Mathlib's
    `TensorProduct.directSumRight` and `DirectSum.congrLinearEquiv`, and the ring map follows the
    pattern of `main`'s `restrictGradedSections` (`DirectSum.toSemiring`);
  - API: the existence statement packaging the irrelevant-ideal condition with the cartesian
    square is private; the public API is the ring maps, their evaluation lemmas, the
    irrelevant-ideal lemma and the cartesian square;
  - proof quality: each `erw` is needed because `Scheme.Hom.pullbackSections` and
    `pullbackSectionsLEBaseLinear` are not exposed, which the comments say.

## Changes in the twenty-second session (2026-11-04, 21:20 UTC)

- `main` moved to `57ab0f657d7` and is merged in with no conflicts. None of its 40 new commits
  touches a file of this branch or adds a declaration of it. The supplier PR #27145 is still open
  and still not consumed, so there are still no stubs.
- **The glued scheme of a relative gluing datum is recognised by its charts**
  (`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.isIso_desc_of_isPullback` and
  `isoOfIsPullback`, new file `AlgebraicGeometry/RelativeGluing.lean`, new independent split 15):
  a scheme `p : Y ⟶ S` with compatible maps `φᵢ : Xᵢ ⟶ Y` exhibiting each chart `Xᵢ` as the base
  change of `p` along `Uᵢ ⟶ S` is the glued scheme, through the colimit map. Mathlib's
  `RelativeGluing.lean` has only the forward direction (the glued scheme has the `Xᵢ` as
  preimages). This is the gluing input of the general base change of projective morphisms; the
  remaining steps are listed at the end of this file.
- The old final split 15 is now split 16, and it is listed after the new split 15.
- Verified: `lake build` green and `lookahead-check` ok. `#lint` (`docBlame`, `unusedArguments`,
  `simpNF`, `checkType`, `synTaut`, `unusedHavesSuffices`) passes over the import closure of
  `RelativeGluing.lean`. No `sorry` anywhere on the branch.
- Rubric audit:
  - reuse: the proof uses Mathlib's `isPullback_natTrans_ι_toBase`, `IsPullback.of_right` and
    `IsZariskiLocalAtTarget.of_openCover` for the isomorphism property; no new cover API;
  - placement: the file mirrors Mathlib's `AlgebraicGeometry/RelativeGluing.lean`, and the
    declarations extend Mathlib's `RelativeGluingData` namespace, like the neighbouring
    `_root_` extensions on `main`.

## Changes in the twenty-first session (2026-11-04, 19:20 UTC)

- `main` is still at `52f9d081237`, so nothing new is merged. The supplier PR #27145 is still not
  consumed, so there are still no stubs.
- **Projectivity is stable under base change to an affine open of the base**
  (`TauCeti.AlgebraicGeometry.isProjective_pullback_snd_fromSpec`, split 15): for `f : X ⟶ S`
  projective and `U` an affine open of an arbitrary base `S`, the base change of `f` along
  `hU.fromSpec : Spec Γ(S, U) ⟶ S` is projective. Over `U` the relative `Proj` is
  `Proj (⨁ n, Γ(Aₙ, U))` (`main`'s `CommMon.isPullback_relativeProjCover`, transported along
  `U ≅ Spec Γ(S, U)`), and the base change of the closed immersion `X ⟶ Proj_S(A)` is a closed
  immersion into it.
- **`Proj` of a graded algebra generated in degree one is projective over its coefficient ring**
  (`isProjective_toSpecCoeff`, split 15): for a graded `R`-algebra of finite type, generated over
  `𝒜 0` by `𝒜 1`, with `𝒜 0` finite over `R`, `Proj.toSpecCoeff 𝒜` is projective. It is the
  identity case `φ = id` of `exists_isClosedImmersion_proj_symmetricAlgebra`, followed by
  `IsProjectiveOver.isProjective` for `Proj (Sym_R (𝒜 1))`.
- Pasting with the affine base change of the twentieth session gives base change along every
  `Spec R ⟶ Spec Γ(S, U) ⟶ S` (`isProjective_pullback_snd_spec_map_fromSpec`), and over an
  affine base along every morphism `Spec R ⟶ S` (`isProjective_pullback_snd_of_isAffine`).
- Verified: `lake build` green and `lookahead-check` ok. `#lint` (`docBlame`, `unusedArguments`,
  `simpNF`, `checkType`, `synTaut`, `unusedHavesSuffices`) passes on `TauCeti` over the import
  closure of `Morphisms/ProjectiveOver.lean`. No `sorry` anywhere on the branch.
- Rubric audit:
  - reuse: no new `Proj` or pullback machinery; the chart square is `main`'s
    `isPullback_relativeProjCover` moved along `IsPullback.of_iso`, the pasting is
    `pullbackLeftPullbackSndIso`, and the factorisation over an affine base is
    `Spec.map_preimage`;
  - proof-quality: the lift into the chart is typed with target `Proj (⨁ n, Γ(Aₙ, U))` (with a
    comment), since instance search does not see through `A.relativeProjCover.X ⟨U, hU⟩`; this
    avoids supplying the composite instances by hand;
  - documentation: the module docstrings of `Morphisms/ProjectiveOver.lean` and
    `Morphisms/Projective.lean` now describe the base change to affine opens.

## Changes in the twentieth session (2026-11-04, 18:30 UTC)

- `main` moved to `52f9d081237` and is merged in with no conflicts. None of its 30 new commits
  touches a file of this branch or adds a declaration of it. The supplier PR #27145 is still not
  consumed, so there are still no stubs.
- **The converse comparison is proved: a scheme over `Spec R` is projective over `R` in the sense
  of `main`'s `Scheme.IsProjectiveOver` if and only if `X ⟶ Spec R` is projective**
  (`AlgebraicGeometry.Scheme.isProjectiveOver_of_isProjective` and
  `AlgebraicGeometry.Scheme.isProjectiveOver_iff_isProjective`, in
  `Morphisms/ProjectiveOver.lean`, new final split 15). This closes the earlier remaining item
  "`IsProjective (X ↘ Spec R) → X.IsProjectiveOver R`", along the plan recorded last session:
  - new generic graded-algebra file `RingTheory/GradedAlgebra/DegreeOne.lean` (new split 13):
    `TauCeti.GradedAlgebra.finite_grade_one` (`𝒜 1` is finite over `R` when `A` is of finite type
    and `𝒜 0` finite over `R`), `TauCeti.GradedAlgebra.mem_closure_grade_one` (if `𝒜 1` generates
    `A` over `𝒜 0`, every homogeneous element of positive degree is a sum of products of degree-one
    elements), and their helpers `exists_mem_grade_of_mem_closure` and `mem_span_inter_grade_one`;
  - `TauCeti.AlgebraicGeometry.exists_isClosedImmersion_proj_symmetricAlgebra`: for a graded
    `S`-algebra generated over `𝒜 0` by a finite `𝒜 1` and a finite ring map `φ : R →+* S`,
    `Proj 𝒜` is a closed subscheme of `Proj (Sym_R 𝒜 1)` over `Spec φ`, through the graded map
    `Sym_R (𝒜 1) → Sym_S (𝒜 1) → A` (`mapₛₗ`, then `gradedLift`), surjective in positive degrees;
  - the comparison itself, through `main`'s chart `Proj (⨁ n, Γ(Aₙ, ⊤)) ≅ Proj_S(A)` over an
    affine base (`CommMon.isIso_relativeProjCover_f_top`) and `R ≅ Γ(Spec R, ⊤)`.
- **Projectivity over an affine base is stable under affine base change**
  (`TauCeti.AlgebraicGeometry.isProjective_pullback_snd_spec_map` for `Spec φ`, `φ : R ⟶ S`, and
  `isProjective_pullback_snd_spec_map_algebraMap` for an `R`-algebra `S`, split 15). The closed
  immersion `X ⟶ Proj (Sym_R M)` base changes, by pasting with `main`'s cartesian square
  `Proj.isPullback_symmetricAlgebra_baseChange`, to a closed immersion of `X ×_R Spec S` into
  `Proj (Sym_S (S ⊗[R] M))`. This is the affine-base case of the remaining base-change item.
- The plan gains two splits: the old final split 13 becomes split 14 without
  `Morphisms/ProjectiveOver.lean`, which moves to the new final split 15 (so that no split exceeds
  about 600 lines), and the generic degree-one lemmas are the independent split 13. Split 15 also
  adds the closing paragraph of the module docstring of `Morphisms/Projective.lean` that points to
  the comparison.
- Verified: `lake build` green and `lookahead-check` ok. `#lint` (`docBlame`, `unusedArguments`,
  `simpNF`, `checkType`, `synTaut`, `unusedHavesSuffices`) passes on `TauCeti.AlgebraicGeometry`
  and `TauCeti.RingTheory` over the import closure of the changed modules. No `sorry` anywhere on
  the branch.
- Rubric audit:
  - generality: the embedding lemma first asked for a surjective `φ`; it now takes any finite
    `φ` (`RingHom.Finite`), which is all the proof uses. The graded-algebra lemmas are stated over
    commutative semirings;
  - reuse: the closed immersion comes from `main`'s `Proj.isClosedImmersion_map_of_grade_subset_range`
    and the base change from `Proj.isPullback_symmetricAlgebra_baseChange`, with no new `Proj`
    machinery;
  - proof-quality: the comparison first ran as one long proof that timed out; the algebraic part
    is now the standalone lemma `exists_isClosedImmersion_proj_symmetricAlgebra`. Where the chart
    `A.relativeProjCover.X ⟨⊤, _⟩` hides its `Proj` type from instance search and `rw`, the
    closed-immersion instance and the associativity step are supplied explicitly, with a comment.

## Changes in the nineteenth session (2026-11-04, 15:00 UTC)

- `main` moved to `5f78b5307b9` and is merged in with no conflicts. None of its new commits
  touches a file of this branch or adds a declaration of it. The supplier PR #27145 is still open
  and still not consumed, so there are still no stubs.
- **The sections of `Sym F` over an affine open are the symmetric algebra of the sections**
  (`TauCeti.AlgebraicGeometry.gradedSymmetricAlgebraSectionsEquiv`, an `AlgEquiv`
  `Sym Γ(F, U) ≃ₐ[Γ(X, U)] ⨁ n, Γ(Symⁿ F, U)` with `_ι`, `_mem` and `_symm_mem`, in `Adjunction.lean`,
  split 7). The section-level extension was already known to be surjective; it is now also
  injective (`sectionsLift_injective_of`, private): its degree-`n` part is the bijection
  `Symⁿ Γ(F, U) ≅ Γ(Symⁿ F, U)` of `main`'s `symmetricPowerSectionsIso` followed by the degree-`n`
  component of the sheaf-level extension, and the degree-`n` parts span `Sym Γ(F, U)`
  (`iSup_homogeneousSubmodule_eq_top`). `adjoin_gradedSectionsGrading_one_gradedSymmetricAlgebra`
  is now a corollary, and the private `adjoin_gradedSectionsGrading_one_eq_top_of` is gone.
  `finiteType_sections_gradedSymmetricAlgebra` shrinks from 25 lines to 8: the sections are
  `Sym` of the finite module `Γ(F, U)`.
- **Over an affine base, the relative `Proj` is the `Proj` of the global sections**
  (`CommMon.isIso_relativeProjCover_f_top`, an instance, in `main`'s `RelativeProj/Basic.lean`,
  split 7): the chart over `⊤` is the base change of the isomorphism `⊤ ⟶ X`.
- **`ℙ(F)` over an affine scheme is `Proj (Sym Γ(F, X))`** (`RelativeProj/SymmetricAlgebra.lean`,
  split 7): `gradedSymmetricAlgebraSectionsGradedHom` and its inverse,
  `projGradedSectionsGradingIso` (`Proj (⨁ n, Γ(Symⁿ F, U)) ≅ Proj (Sym Γ(F, U))` over
  `Spec Γ(X, U)`, `projGradedSectionsGradingIso_hom_toSpecCoeff`), and
  `relativeProjGradedSymmetricAlgebraIso` (`ℙ(F) ≅ Proj (Sym Γ(F, X))` for `X` affine) with
  `relativeProjGradedSymmetricAlgebraIso_inv_relativeProjToBase` (it lies over `X`).
- **Over an affine base, `Proj (Sym Γ(F, S)) ⟶ S` is projective** for `F` of finite type
  (`isProjective_toSpecCoeff_comp_fromSpec`, an instance, final split 13).
- **The sheaf associated with a finite module is of finite type**
  (`TauCeti.AlgebraicGeometry.isFiniteType_tilde`, an instance, in `main`'s
  `Modules/FinitePresentation.lean`, new split 12). `main` only had the finitely presented case.
  The generators of Mathlib's `presentationTilde` are finite when the module is; they are moved to
  local generators on the trivial cover through `Presentation.quasicoherentData`.
- **A scheme projective over a ring in the sense of `main`'s `Scheme.IsProjectiveOver` is
  projective over its spectrum** (`AlgebraicGeometry.Scheme.IsProjectiveOver.isProjective`, an
  instance like `main`'s `IsProjectiveOver.isProper`, in the new file
  `Morphisms/ProjectiveOver.lean`, final split 13). The identification `M ≅ Γ(M~, ⊤)`,
  semilinear over `R ≅ Γ(Spec R, ⊤)` (`tildeToOpenₛₗ M ⊤` and its inverse `tildeToOpenTopInvₛₗ`),
  induces `projSymmetricAlgebraTildeIso : Proj (Sym Γ(M~, ⊤)) ≅ Proj (Sym_R M)` through
  `SymmetricAlgebra.mapₛₗ`, lying over `Spec R`
  (`projSymmetricAlgebraTildeIso_hom_projToSpec`); the left side is `ℙ(M~)` over the affine
  base. This connects the branch's `IsProjective` to the affine-base notion that `main`'s curve
  files use.
- The private `symmetricToOpenSemilinear` of `main`'s `Modules/SymmetricPower/Affine.lean` is now
  the public `tildeToOpenₛₗ` (with `tildeToOpenₛₗ_apply`), so the new file reuses it instead of a
  copy.
- Verified: `lake build` green and `lookahead-check` ok. No `sorry` anywhere on the branch.
- Rubric audit:
  - reuse: the finite-type proof now goes through Tau Ceti's `SymmetricAlgebra.instFiniteType`
    instead of an ad hoc span argument, and the generation-in-degree-one theorem is derived from
    the equivalence rather than proved separately;
  - reuse: `tildeToOpenₛₗ` is exposed rather than duplicated;
  - the module system hides `Proj.mapIso`, so `projGradedSectionsGradingIso_hom_toSpecCoeff`
    rewrites with `Proj.mapIso_hom` stated for the concrete isomorphism (a `rw` of the generic
    lemma fails, since the sections module is typed through `PresheafOfModulesOfCommRing`).

## Changes in the eighteenth session (2026-11-04, 12:00 UTC)

- `main` moved to `00deee4410c` and is merged in with no conflicts; its only new commit changes
  `scripts/` (CI dependency prefill). The supplier PR #27145 is still open and still not
  consumed, so there are still no stubs.
- **Closed immersions, in particular isomorphisms and identities, are projective**
  (`TauCeti.AlgebraicGeometry.isProjective_of_isClosedImmersion`, an instance, in
  `Blowup/Projective.lean`, final split 12). The blowup along the unit ideal sheaf `⊤` is
  projective (`isProjective_blowupToBase`, `⊤` is of finite type) and an isomorphism (`main`'s
  `isIso_blowupToBase_iff` with `isEffectiveCartier_top`), so `f = (f ≫ (Bl_⊤ S ⟶ S)⁻¹) ≫
  (Bl_⊤ S ⟶ S)` is a closed immersion followed by a projective morphism. The module docstring of
  `Morphisms/Projective.lean` points to it, since it cannot live there (the blowup file imports
  that file).
- Found this session, and added to "Remains": `main` has an affine-base notion
  `AlgebraicGeometry.Scheme.IsProjectiveOver R X` (`ProjectiveSpectrum/ProjectiveOver.lean`: a
  closed subscheme over `R` of `Proj (Sym_R M)` for a finite `R`-module `M`), used by
  `Curves/Category.lean`. The port should connect it to `IsProjective (X ↘ Spec R)`.
- Verified: `lake build` green and `lookahead-check` ok. No `sorry` anywhere on the branch.
- Rubric audit:
  - placement: the instance goes to `Blowup/Projective.lean`, where both the blowup and
    `IsProjective` are available, with a pointer from `Morphisms/Projective.lean`;
  - reuse: it is derived from the existing blowup results rather than by computing
    `Proj_S (𝒪_S[t])` directly.

## Changes in the seventeenth session (2026-11-04, 11:10 UTC)

- `main` is unchanged at `7ed979dc2ea`; the supplier PR #27145 is still open and still not
  consumed, so there are still no stubs.
- **Relative ampleness composes after twisting (Stacks, Tag 0C4K)**, the composition input named
  in last session's "Remains". New file `LineBundle/RelativelyAmple/Comp.lean` (split 10):
  - `LineBundleClass.IsRelativelyAmple.exists_isAmple_mul_pullback_pow`: if `a` is relatively
    ample for `f : X ⟶ Y` and `b` is ample on `Y`, then `a · f* bⁿ` is ample on `X` for all
    `n ≥ N`. For `x ∈ X`, choose `s ∈ Γ(Y, M)`, `[M] = bᵈ`, with `Y_s ∋ f x` affine, and a section
    `t` over `U = f⁻¹ Y_s` of a bundle of class `aᵉ` with `X_t ∋ x` affine. Then
    `(f* s)^{⊗c} ⊗ t` extends to a global `ξ` (`InvertibleSheaf.exists_map_eq_tmul_sectionPow`,
    split 8), `X_{f* s ⊗ ξ} = X_t`, and `(f* s)^{⊗k} ⊗ (f* s ⊗ ξ)^{⊗d}` with `k = e n − d c` is a
    section of class `(a · f* bⁿ)^{e d}` vanishing nowhere exactly on `X_t`, for every `n ≥ d c`.
    Finitely many `X_t` cover `X`.
  - `LineBundleClass.IsRelativelyAmple.exists_isRelativelyAmple_comp_mul_pullback_pow`: over a
    quasi-compact base `S`, relative ampleness of `a` for `f` and of `b` for `g : Y ⟶ S` gives
    relative ampleness of `a · f* bⁿ` for `f ≫ g` for all large `n` (finite affine cover of `S`,
    the absolute case over each piece, and locality on the base).
- `IsProjective.exists_isRelativelyAmple_comp` (final split, `Morphisms/Projective.lean`): over a
  quasi-compact base, a composite of projective morphisms carries a relatively ample class.
- Deduplication: the transport of a section of a line bundle on an open subscheme `U` to a section
  of `L` over `U` with the image nonvanishing locus, which was inline in
  `IsAmple.of_iSup_basicOpen_eq_top`, is now the lemma
  `InvertibleSheaf.exists_nonvanishingLocus_eq_image` in `Ample.lean` (split 5); that proof and
  the new 0C4K proof both use it, and the proof of `of_iSup_basicOpen_eq_top` is shorter. The
  small lemma `InvertibleSheaf.nonvanishingLocus_le_nonvanishingLocus_sectionPow`
  (`X_s ⊆ X_{s^{⊗n}}`, also for `n = 0`) goes to `Extension.lean` (split 8).
- Splits: the new split 10 carries `Comp.lean`; intersection numbers are split 11 and the final
  split is 12.
- Verified: `lake build` green (62972 jobs) and `lookahead-check` ok. No `sorry` anywhere on the
  branch.
- Rubric audit:
  - naming: inside `namespace LineBundleClass`, the theorem names `IsRelativelyAmple.…` make bare
    `pullback` and `mk` resolve to `IsRelativelyAmple.pullback`/`.mk`, so the statements use
    `LineBundleClass.pullback` and `LineBundleClass.mk` explicitly;
  - duplication: the section transport is factored out rather than copied (see above);
  - placement: the composition result gets its own file under `LineBundle/RelativelyAmple/`
    rather than growing `RelativelyAmple.lean`, so that it is its own split.

## Changes in the sixteenth session (2026-11-04, 10:20 UTC)

- `main` is unchanged at `7ed979dc2ea`; the supplier PR #27145 is still not consumed, so there are
  still no stubs.
- **Extending sections from nonvanishing loci (Stacks 01PW), the blocker named last session.**
  New file `LineBundle/Extension.lean` (split 8). It needs a section-level tensor product, which
  is now on the branch:
  - `TauCeti.SheafOfModules.tmul` (site level, `Sheaf/TensorProduct/Basic.lean`): the
    sheafified pure tensor of two sections, with `tmul_map` (restriction);
  - `InvertibleSheaf.tmul` (`NonvanishingLocus.lean`): the same for sections of line bundles, with
    linearity (`smul_tmul`, `tmul_smul`, `tmul_sub`, `tmul_zero`) and `nonvanishingLocus_tmul`.
    The branch's `Scheme.Modules.exists_nonvanishingLocus_tensorProduct_eq_inf` and
    `InvertibleSheaf.exists_nonvanishingLocus_tensorProduct` are replaced by the named
    `Scheme.Modules.nonvanishingLocus_tmul` and `InvertibleSheaf.nonvanishingLocus_tmul`, and their
    four users in `Ample.lean` now use `InvertibleSheaf.tmul` directly. To type these sections,
    `InvertibleSheaf.tensorProduct` on `main` gets `@[expose]`.
  - `InvertibleSheaf.sectionPow s n`: the tensor powers `s^{⊗n} ∈ Γ(L^{⊗n}, U)`, compatible with
    restriction and with `(r • s)^{⊗n} = rⁿ • s^{⊗n}`.
  - `InvertibleSheaf.exists_tmul_sectionPow_eq_zero`: on a quasi-compact `U`, a section of a line
    bundle vanishing on `X_s` is killed by `s^{⊗n}` for large `n`.
  - `InvertibleSheaf.exists_map_eq_tmul_sectionPow`: on a quasi-compact quasi-separated `U`, for
    every section `y` of a line bundle over `X_s`, some `s^{⊗b} ⊗ s^{⊗a} ⊗ y` extends to `U`.
  Both reduce on affine trivializing opens `V` (where `s = r • e` and `X_s ∩ V = D(r)`) to `main`'s
  function-case lemmas `Scheme.Modules.exists_pow_smul_eq_zero_of_isCompact` and
  `Scheme.Modules.exists_pow_smul_eq_map`, and glue with the sheaf property.
- **Ample line bundles have a basis of affine nonvanishing loci**
  (`LineBundleClass.IsAmple.exists_isAffineOpen_nonvanishingLocus_le`), and hence **ampleness pulls
  back along immersions from quasi-compact schemes** (`IsAmple.pullback_of_isImmersion`: closed
  immersion into `coborderRange` followed by the open inclusion), in particular along
  quasi-compact open immersions. **Relative ampleness pulls back along quasi-compact immersions of
  the source** (`IsRelativelyAmple.pullback_of_isImmersion`). This closes the first item of last
  session's "Remains".
- Splits: the new split 8 carries `Extension.lean` and the two `Ample.lean` theorems; relative
  ampleness is now split 9 (after 8 as well), intersection numbers split 10, and the final split 11.
- Verified: `lake build` green and `lookahead-check` ok (see below). No `sorry` anywhere on the
  branch.
- Rubric audit:
  - duplication: the existential lemmas about tensor products of sections are removed in favour of
    the named `tmul` and its `nonvanishingLocus_tmul`, rather than kept beside them;
  - API: `sectionPow` follows `InvertibleSheaf.tensorPow` (`s^{⊗(n+1)} = s^{⊗n} ⊗ s`) so its type
    is the tensor power itself, without transport;
  - imports: `Extension.lean` imports `Modules/Localization.lean` and `Algebra/Group/Action/Pow.lean`
    only privately, since they are used only in proofs.

## Changes in the fifteenth session (2026-11-04, 09:45 UTC)

- `main` is unchanged at `7ed979dc2ea`, so there is nothing new to merge. The supplier PR #27145
  is still not consumed, so there are still no stubs.
- **Every line bundle on a quasi-affine scheme is ample and globally generated.**
  `InvertibleSheaf.exists_isAffineOpen_nonvanishingLocus_of_isQuasiAffine`: on a quasi-affine
  `X`, every point lies in an affine nonvanishing locus of a global section of `L` itself. A local
  generator of `L` near `x`, restricted to an affine basic open `X_r ∋ x` of a global function,
  extends to a global section `t` after multiplication by a power of `r`
  (`main`'s `Scheme.Modules.isLocalizedModule_basicOpenRestrict_of_qcqs`), and `r • t` vanishes
  nowhere exactly on `X_r`. Corollaries: `InvertibleSheaf.isGloballyGenerated_of_isQuasiAffine`
  and `LineBundleClass.isAmple_of_isQuasiAffine` (every class). The latter subsumes `main`'s
  `isAmple_one` and `isAmple_of_pow_eq_one`, which are removed (they had no other users), and it
  now gives the reverse direction of `main`'s `isAmple_one_iff`, whose proof shrinks.
- **Products of ample classes are ample** (`LineBundleClass.IsAmple.mul`), and likewise for
  relative ampleness (`IsRelativelyAmple.mul`). The sections are moved to a common power, as in
  `IsAmple.pullback_mul_pullback`.
- **Relative ampleness over a quasi-affine base is ampleness.** `IsRelativelyAmple.isAmple` and
  `isRelativelyAmple_iff_isAmple` now assume `[S.IsQuasiAffine]` instead of `[IsAffine S]`. The
  affine basic opens `S_r` cover `S`; their preimages are the basic opens of the pulled-back
  functions, so `IsAmple.of_iSup_basicOpen_eq_top` applies.
- **Relative ampleness for quasi-affine morphisms and composition with them.**
  `LineBundleClass.isRelativelyAmple_of_isQuasiAffine`: for `f` quasi-compact with quasi-affine
  preimages of affine opens, every class is relatively ample; `isRelativelyAmple_of_isAffineHom`
  is the affine case. They replace the branch's `isRelativelyAmple_one` and
  `isRelativelyAmple_of_pow_eq_one` (special cases, now removed).
  `IsRelativelyAmple.comp_of_isQuasiAffine`: relative ampleness for `f` gives it for `f ≫ g` when
  `g` is quasi-compact with quasi-affine preimages of affine opens. `IsRelativelyAmple.comp`
  (affine `g`) is now its corollary.
- **Degree on components of powers** (`LineBundleClass.intersectionNumber_pow`,
  `intersectionNumber_zpow` in `main`'s `IntersectionNumber/Basic.lean`): `(aⁿ · C) = n (a · C)`
  on a regular proper integral curve. This is the new split 9; the final split is renumbered 10.
- Checked this session: the target's "Cartier divisors, pullback, degree on components" clause.
  `main` has Cartier divisors and their line bundles (`CartierDivisor/Sheaf.lean`,
  `Scheme.CartierDivisor.toLineBundleClassHom`), pullback of line bundles and classes
  (`InvertibleSheaf.pullback`, `LineBundleClass.pullback`), and the degree on a component as an
  intersection number with its additivity (`intersectionNumber_mul`, `intersectionNumber_inv`,
  `intersectionNumberHom`). With this session's power formula and the branch's tensor powers, the
  clause needs nothing further from this target; positivity of degrees belongs to the separate
  Layer 2 ampleness-criterion item.
- Verified: `lake build` green (62968 jobs), `lookahead-check` ok, and `#lint` (`docBlame`,
  `unusedArguments`, `simpNF`, `checkType`, `synTaut`, `unusedHavesSuffices`) passes on the
  import closure of `RelativelyAmple.lean` and `IntersectionNumber/Basic.lean`. No `sorry`
  anywhere on the branch.
- Rubric audit:
  - duplication: the special cases `isAmple_one`, `isAmple_of_pow_eq_one`,
    `isRelativelyAmple_one` and `isRelativelyAmple_of_pow_eq_one` are removed rather than kept
    beside their generalizations, and `IsRelativelyAmple.comp` is derived from the quasi-affine
    version instead of repeating its proof;
  - generality: the base of `IsRelativelyAmple.isAmple` was affine; it is now quasi-affine, which
    is what the composition lemma needs;
  - naming: the two `InvertibleSheaf` lemmas sit in an `InvertibleSheaf` namespace block instead
    of a `_root_`-qualified name over 100 characters.

## Changes in the fourteenth session (2026-11-04, 08:40 UTC)

- `main` moved to `7ed979dc2ea` and is merged in with no conflicts. None of its new commits
  touches a file of this branch or adds a declaration of it. The supplier PR #27145 is still not
  consumed, so there are still no stubs.
- **The closure model is on `main`.** `TauCeti.Model.exists_isClosedImmersion_isProper`
  (`Curves/StableReduction/Model/Projective.lean`) constructs, from a closed immersion of `C`
  into a projective space over `K`, a proper model of `C` that is a closed subscheme of
  `ℙ^{n-1}_R`, by scheme-theoretic closure. The earlier remaining item "the scheme-theoretic
  closure of `C ↪ ℙ^N_K` in `ℙ^N_R` as a proper model" is therefore removed: this target does
  not need to supply it.
- **Relative ampleness descends along separated morphisms**
  (`LineBundleClass.IsRelativelyAmple.of_comp`: if `a` is relatively ample for `f ≫ g` and `g` is
  separated, then `a` is relatively ample for `f`). Over an affine `W` of the base of `g`, the
  class is ample on `f⁻¹ (g⁻¹ W)` and `g⁻¹ W` is a separated scheme, so `main`'s
  `IsAmple.isRelativelyAmple` applies to `f ∣_ g⁻¹ W`. Locality on the base
  (`isRelativelyAmple_of_iSup_eq_top`) finishes the proof. With `IsRelativelyAmple.comp`, this
  gives `isRelativelyAmple_comp_iff` for affine `g`.
- **Exterior products of ample classes are ample over a separated base**
  (`LineBundleClass.IsAmple.pullback_mul_pullback`, stated for any pullback square `P = X ×_S Y`
  with projections `q₁`, `q₂`: `q₁* a · q₂* b` is ample). The sections of `aⁿ` and `bᵐ` are moved
  to the common power `aⁿᵐ`, `bⁿᵐ` (`InvertibleSheaf.exists_nonvanishingLocus_eq_of_mk_eq_pow`),
  pulled back (`nonvanishingLocus_pullbackSections`) and tensored
  (`exists_nonvanishingLocus_tensorProduct`). The nonvanishing locus `X_s ×_S Y_t` is affine by
  the new `AlgebraicGeometry.IsAffineOpen.preimage_inf_preimage_of_isPullback`, in the new file
  `Pullback/Affine.lean`. Mathlib only proves that this open is quasi-compact
  (`IsAffineOpen.isCompact_pullback_inf`).
- **Exterior products of relatively ample classes are relatively ample**
  (`LineBundleClass.IsRelativelyAmple.pullback_fst_mul_pullback_snd`: for `a` relatively ample
  for `f` and `b` for `g`, `pr₁* a · pr₂* b` is relatively ample for `X ×_S Y ⟶ S`). Over an
  affine `V`, the preimage of `V` is the fibre product of `f⁻¹ V` and `g⁻¹ V` over `V`. The
  square comes from `IsPullback.of_right`, like the one in `IsRelativelyAmple.pullback_snd`. This
  is the ampleness input of the Segre construction, which the remaining item "projectivity is
  stable under composition and base change" needs.
- Verified: `lake build` green, `lookahead-check` ok, and `#lint` (`docBlame`,
  `unusedArguments`, `simpNF`, `checkType`, `synTaut`, `unusedHavesSuffices`) passes on the
  import closure of `RelativelyAmple.lean`. No `sorry` anywhere on the branch.
- Rubric audit:
  - placement: the affine-open lemma about fibre products needs no line bundles, so it moved out
    of `LineBundle/Ample.lean` into the new `Pullback/Affine.lean`, next to `Pullback/Carrier.lean`;
  - generality: the absolute product lemma first assumed an affine base. It now assumes only a
    separated base, since a morphism from an affine scheme to a separated scheme is affine;
  - proof quality: the class computation uses one `simp only [← pullbackHom_apply, map_pow]`
    instead of a ten-step `rw` chain. The commutativity of the restricted square is
    `simp only [Category.assoc, morphismRestrict_ι]` followed by `reassoc_of%` rewrites, not a
    chain of `Category.assoc` rewrites.

## Changes in the thirteenth session (2026-11-04, 06:40 UTC)

- `main` moved to `81820d6b555` and is merged in with no conflicts. None of its 56 new commits
  touches a file of this branch or adds a declaration of it. The supplier PR #27145 is still open
  and still not consumed, so there are still no stubs.
- **A scheme carrying an ample line bundle is separated** (`LineBundleClass.IsAmple.isSeparated`).
  This closes the first part of the earlier remaining item "ampleness also implies
  separatedness". It needs two new results:
  - `AlgebraicGeometry.Scheme.IsSeparated.of_isAffineOpen` (in `main`'s
    `Morphisms/Separated.lean`): a scheme is separated if it has an affine open cover `Uᵢ` whose
    intersections `Uᵢ ∩ Uⱼ` are affine with functions generated by those on `Uᵢ` and `Uⱼ`. The
    proof is `main`'s `IsSeparated.of_openCover` for `X ⟶ ⊤_ Scheme`, where each
    `Uᵢ ∩ Uⱼ ⟶ Uᵢ × Uⱼ` is a morphism of affine schemes that is surjective on functions.
  - `Scheme.Modules.sup_range_map_nonvanishingLocus_inf_eq_top` (in `NonvanishingLocus.lean`):
    for sections `s`, `t` of one invertible sheaf with `X_s` affine, the functions on
    `X_s ∩ X_t` are generated by those on `X_s` and `X_t`. On `X_s`, `t = g • s`, so the overlap
    is the basic open set `D(g)` of the affine `X_s`. The inverse of `g` there is the coefficient
    `h` of `s = h • t` on `X_t`.

  The sections of the definition have different powers `aⁿ`. They are moved into one line bundle
  of class `aᴺ`, with `N` the product of the finitely many `n` needed to cover `X`. The new lemma
  `InvertibleSheaf.exists_nonvanishingLocus_eq_of_mk_eq_pow` does this: it is the tensor-power
  argument formerly inlined in `IsAmple.pow`, so `IsAmple.pow` now calls it.
  `IsAmple.quasiSeparatedSpace` is removed, since separatedness gives it by instance. Its one
  caller, `IsAmple.of_iSup_basicOpen_eq_top`, now uses `isSeparated`.
- **A morphism carrying a relatively ample class is separated**
  (`LineBundleClass.IsRelativelyAmple.isSeparated`). Over an affine `V`, `f⁻¹ V` is a separated
  scheme, and separatedness is local on the base. Here, unlike for `QuasiCompact`, instance
  search does find `IsZariskiLocalAtTarget @IsSeparated`.
- **Relative ampleness is stable under base change** (`LineBundleClass.IsRelativelyAmple.pullback_snd`:
  for any `g : S' ⟶ S`, the pullback of `a` along `pullback.fst f g` is relatively ample for
  `pullback.snd f g`). This closes the base-change part of the earlier remaining item. The proof
  needs no extension of sections. The affine opens `V'` of `S'` with `g(V')` inside an affine
  open `V` of `S` cover `S'`, and relative ampleness is local on the base
  (`isRelativelyAmple_of_iSup_eq_top`). Over such a `V'`, relative ampleness is ampleness
  (`isRelativelyAmple_iff_isAmple`). The map from the preimage of `V'` to `X` factors through
  `f⁻¹ V` by a base change of the affine morphism `V' ⟶ V`. The pullback square comes from
  `IsPullback.of_right` and the two restriction squares. So ampleness on `f⁻¹ V` pulls back
  along it (`IsAmple.pullback`).
- Split 4 had grown to about 500 lines. The separatedness material and the basic-open-cover
  criterion that now depends on it form the new split 5. The later splits are renumbered:
  `Proj` is now 6, `Sym` 7, relative ampleness 8, and the final split 9.
- Verified: `lake build` green (62854 jobs), `lookahead-check` ok, and `#lint` (`docBlame`,
  `unusedArguments`, `simpNF`, `checkType`, `synTaut`, `unusedHavesSuffices`) passes on the
  import closure of `RelativelyAmple.lean`. No `sorry` anywhere on the branch.
- Rubric audit:
  - each new `change` carries a comment;
  - in the overlap lemma, a brittle 20-step `rw` chain is replaced by two restricted equations
    normalized by one `simp only`;
  - the range argument for the chart map `V' ⟶ V` now mirrors the one for `f'⁻¹ V' ⟶ f⁻¹ V`
    instead of a five-lemma set-range rewrite;
  - the definitional reassembly in `Scheme.IsSeparated.of_isAffineOpen` is documented.

## Changes in the twelfth session (2026-11-04, 05:20 UTC)

- `main` is unchanged at `6c781b0a734`, so there is nothing new to merge.
- **A relatively very ample line bundle for a quasi-compact morphism is relatively ample**
  (`InvertibleSheaf.IsRelativelyVeryAmple.isRelativelyAmple`). This closes the first remaining
  item of the eleventh session: the immersion into `Proj_S(A)` no longer needs to be closed. The
  proof needs no extension of sections from nonvanishing loci, because on `Proj` the relevant
  sections are already global:
  - `Proj.nonvanishingLocus_toTwistingSheaf` now covers every degree: for `r` of degree `d`, the
    global section `r / 1` of `𝒪(d)` vanishes nowhere exactly on `D₊(r)`. It replaces the
    degree-one statement, which had no other callers.
  - `Proj.exists_mem_basicOpen_le`: when the degree-one standard opens cover `Proj A`, every
    point of an open `U` lies in some `D₊(g) ⊆ U` with `g` homogeneous of positive degree. Take
    `D₊(f · aₖ)` for a basic open `D₊(a) ⊆ U`, a component `aₖ` of `a`, and `f` of degree one.
  - `Proj.isAmple_pullback_twistingSheaf_one`: `𝒪(1)` pulls back to an ample line bundle along
    every immersion `j : Z ⟶ Proj A` from a quasi-compact `Z`. The pullback of `g / 1` vanishes
    nowhere exactly on `j⁻¹ D₊(g)`. That open is affine, because `j` is the closed immersion
    `j.liftCoborder` followed by the inclusion of `j.coborderRange ⊇ D₊(g)`.
    `Proj.isAmple_twistingSheaf_one` is now its case `j = 𝟙`.
  - In `Morphisms/Projective.lean`, over an affine `V` the restriction `i ∣_ π⁻¹ V`, followed by the
    chart isomorphism, is an immersion of the quasi-compact `f⁻¹ V` into
    `Proj (⨁ n, Γ(Aₙ, V))`. `LineBundleClass.isRelativelyAmple_relativeProjTwistingSheafOne` is
    now a one-line corollary, so its chart argument is not duplicated.
- With `IsRelativelyVeryAmple.pullback`, it follows that for every immersion `j` with `j ≫ f`
  quasi-compact, the pullback of a relatively very ample bundle is relatively ample.
- **Relative ampleness is local on the base** (`LineBundleClass.isRelativelyAmple_of_iSup_eq_top`
  and the iff `isRelativelyAmple_iff_of_iSup_eq_top`). This closes the earlier remaining item
  "converse of `IsRelativelyAmple.restrict`". It rests on three new results in `main`'s
  `LineBundle/Ample.lean`:
  - `IsAmple.quasiSeparatedSpace`: a scheme with an ample line bundle is quasi-separated. Two
    affine nonvanishing loci meet in `X_s ∩ X_t`, the nonvanishing locus of `t` on the affine
    `X_s`, which is affine.
  - `Scheme.quasiSeparatedSpace_of_iSup_basicOpen_eq_top`: a cover by quasi-separated basic opens
    of global functions makes a scheme quasi-separated.
  - `IsAmple.of_iSup_basicOpen_eq_top`: on a quasi-compact scheme, ampleness can be checked on a
    cover by basic opens `X_{rᵢ}` of global functions. A section `s` over `X_{rᵢ}` extends to a
    global `t` after multiplication by a power of `rᵢ`, by `main`'s
    `Scheme.Modules.isLocalizedModule_basicOpenRestrict_of_qcqs`. Then `rᵢ • t` vanishes nowhere
    exactly on `X_s`. Sections on the open subscheme `X_{rᵢ}` are moved to sections of `L` over
    `X_{rᵢ}` with `Scheme.Modules.nonvanishingLocus_restrictAppIso_inv`. The eleventh session had
    deleted that lemma as unused; it is restored in `LineBundle/NonvanishingLocus.lean`.

  For the relative statement over an affine `V`, `f⁻¹ V` is covered by the basic opens of the
  pullbacks of the functions `g` on `V` with `D(g)` inside some `Uᵢ`. These basic opens are
  `f⁻¹ D(g)`. They are quasi-compact, being ample, so `f⁻¹ V` is quasi-compact; this also gives
  quasi-compactness of `f`. Note for the port: in the pinned Mathlib, instance search does not
  find `IsZariskiLocalAtTarget @QuasiCompact` or `HasAffineProperty @QuasiSeparated _`. Mathlib
  declares those instances under a `backward.isDefEq.respectTransparency` option. So the proof
  argues with compact sets directly, through `quasiCompact_iff_forall_isAffineOpen`.
- **File split.** `LineBundle/RelativelyAmple.lean` had grown to 573 lines and is split.
  Relative ampleness alone stays in `LineBundle/RelativelyAmple.lean` (338 lines; it needs no
  `Proj`). Relative very ampleness, projective morphisms and projective bundles move to the new
  `Morphisms/Projective.lean` (276 lines), next to the other morphism properties.
  `Blowup/Projective.lean` now imports it. The split plan grows to eight splits.
- Verified: `lake build` green (62718 jobs), `lookahead-check` ok, and the environment linters
  (`simpNF`, `unusedArguments`, `docBlame`, `checkType`, `synTaut`, `unusedHavesSuffices`,
  `impossibleInstance`, `nonClassInstance`, `simpComm`, `structureInType`, `deprecatedNoSince`)
  pass on every changed module. No `sorry` anywhere on the branch.
- Rubric audit:
  - the degree-one nonvanishing lemma is generalized in place rather than duplicated;
  - the relative `Proj` ampleness theorem is derived instead of re-proved;
  - the one explicit `@`-application, which supplies an `IsImmersion` instance that instance
    search does not find through the chart type, carries a comment.

## Changes in the eleventh session (2026-11-04, 04:35 UTC)

- `main` moved to `6c781b0a734` and is merged in with no conflicts. Nothing it added replaces a
  declaration of this branch. The supplier PR #27145 is still open and still not consumed.
- Correction to earlier notes: `main` already has a pullback-of-sections API
  (`Scheme.Hom.pullbackSections`, `pullbackSectionsLE`, in `Modules/Pullback/Sections.lean`) and the
  fibre identification `Scheme.Modules.residueFieldPullbackSectionsEquiv`
  (`Modules/Pullback/ResidueField.lean`). This session uses them.
- **Nonvanishing loci pull back along every morphism**
  (`Scheme.Modules.nonvanishingLocus_pullbackSections`: for `g : Y ⟶ X`, the locus of
  `g.pullbackSections M U s` is `g ⁻¹ᵁ X_s`). The proof goes through fibres:
  - `mem_nonvanishingLocus_iff_pullbackSectionsLE_ne_zero`: `x ∈ X_s` exactly when the pullback of
    `s` to `Spec κ(x)` is nonzero. This uses the new pure-algebra lemma
    `TauCeti.IsLocalRing.span_singleton_eq_top_iff_one_tmul_ne_zero` in
    `RingTheory/LocalRing/Module.lean`.
  - `Spec κ(y) ⟶ Y ⟶ X` factors through `Spec κ(g y)`, and pulling back along
    `Spec κ(y) ⟶ Spec κ(g y)` is injective (`Scheme.Modules.injective_pullbackSections_SpecMap`,
    added to `Modules/Pullback/ResidueField.lean`: faithful flatness over a field).
- **Ampleness pulls back along every affine morphism**, closed immersions included. On `main`'s
  `Ample.lean`, `IsAmple.pullback_of_isOpenImmersion` is replaced by `IsAmple.pullback`, which
  takes only `[IsAffineHom e]`. In the same way `IsRelativelyAmple.pullback_of_isOpenImmersion` is
  replaced by `IsRelativelyAmple.pullback`. All callers are updated and the old names are gone.
  The open-immersion helper `nonvanishingLocus_restrictAppIso_inv` (an earlier addition of this
  branch) had no other use, so it is removed.
- **Projective morphisms carry a relatively ample line bundle.**
  `IsProjective.exists_isRelativelyVeryAmple_isRelativelyAmple` replaces
  `IsProjective.exists_isRelativelyVeryAmple`: the pullback of `𝒪(1)` along the closed immersion
  is relatively very ample and relatively ample. This closes the earlier remaining item
  "for `f` projective, the pullback of `𝒪(1)` is relatively ample".
- **A relatively ample class is ample on every fibre** (`IsRelativelyAmple.isAmple_fiber`). This
  needs the new instances `TauCeti.isAffineHom_fromSpecResidueField` and
  `TauCeti.isAffineHom_fiberι`, added to `main`'s `AlgebraicGeometry/Fibers.lean` (split 7).
- Verified: `lake build` green (62716 jobs) and `lookahead-check` ok. No `sorry` anywhere on the
  branch. Rubric audit:
  - the injectivity lemma is public and lives in `Modules/Pullback/ResidueField.lean`, not as a
    private helper (under-exposure);
  - a private restatement of `InvertibleSheaf.isQuasicoherent_obj` is replaced by that instance
    (duplication);
  - the `change` and the one `erw` now carry comments.

## Changes in the tenth session (2026-11-04, 02:30 UTC)

- `main` moved to `8e29268de79` and is merged in with no conflicts. Nothing it added replaces a
  declaration of this branch. It did add `Scheme.Modules.symmetricPowerSectionsIso`
  (`Modules/SymmetricPower/Sections.lean`): on an affine `U`, `Symⁿ Γ(F, U) ≅ Γ(Symⁿ F, U)`.
  This closes the earlier remaining item "`ℙ(ℰ)` is projective".
- **`Sym F` is generated in degree one on affine sections**
  (`adjoin_gradedSectionsGrading_one_gradedSymmetricAlgebra`). It is added to `main`'s
  `Modules/Quasicoherent/GradedAlgebra/SymmetricAlgebra/Adjunction.lean`, because the proof uses
  that file's private section-level lift `Sym Γ(F, U) → ⨁ n, Γ(Aₙ, U)`. That lift is surjective
  on an affine `U` when every degree of the sheaf-level lift is an isomorphism, which holds for
  the lift of `F ≅ Sym¹ F`, the identity of `Sym F`. The degree-`n` part of the section-level
  lift is the sheaf-level lift composed with `symmetricPowerSectionsIso`.
- **Generation in degree one from generation over `Γ(X, U)`**
  (`CommMon.isGeneratedInDegreeOne_of_adjoin_eq_top`, split 1). It is used for both `Sym F` and
  the Rees algebra.
- **Projective bundles.** The new file `RelativeProj/SymmetricAlgebra.lean` (split 6) proves
  `isGeneratedInDegreeOne_gradedSymmetricAlgebra`. For `F` of finite type it also proves
  `finiteType_sections_gradedSymmetricAlgebra`, plus `finite_sections_gradedSymmetricAlgebra_zero`
  and `isProper_relativeProjToBase_gradedSymmetricAlgebra`. In `RelativelyAmple.lean`:
  `ℙ(F) ⟶ S` is projective (the instance `isProjective_relativeProjToBase_gradedSymmetricAlgebra`).
  `𝒪(1)` on it is relatively very ample, and relatively ample for `F` of finite type.
- **Blowups are projective.** The new file `Blowup/Projective.lean` proves that the Rees algebra
  of an ideal sheaf is generated in degree one. So the blowup along an ideal sheaf of finite type
  is projective (`isProjective_blowupToBase`, Stacks 02NS), and its `𝒪(1)` is relatively ample.
  The two inline bullets of `main`'s `isProper_blowupToBase` become the named lemmas
  `finiteType_sections_reesAlgebra` and `finite_sections_reesAlgebra_zero`, so they are not
  duplicated.
- Verified: `lake build` green (62714 jobs) and `lookahead-check` ok. No `sorry` anywhere on the
  branch. Rubric audit: renamed the blowup ampleness theorem after its statement and wrapped
  lines over 100 characters.
- The splits are renumbered. The new split 6 is the projective-bundle file. The old split 6 is
  now split 7: it still carries `RelativelyAmple.lean` and completes the target, and it also takes
  `Blowup/Projective.lean` and the `Blowup/IdealSheaf.lean` refactor.

## Changes in the ninth session (2026-11-04, 01:35 UTC)

- `main` is unchanged at `333c9e49143`, so there is nothing new to merge.
- **Nonvanishing loci of tensor products.** `Scheme.Modules.exists_nonvanishingLocus_tensorProduct_eq_inf`:
  for sections `s`, `t` of invertible `M`, `N` over `U`, the sheafified pure tensor `s ⊗ t` is a
  section of `M ⊗ N` with `X_{s ⊗ t} = X_s ∩ X_t`. The proof uses `main`'s stalk comparison
  `SheafOfModules.tensorStalkEquiv` and the rank-one stalks. `InvertibleSheaf.exists_nonvanishingLocus_tensorProduct`
  restates it for `InvertibleSheaf.tensorProduct`. Both are stated existentially on purpose:
  `main`'s lax monoidal sections functor `Scheme.Modules.sectionsFunctor` already has a tensor map
  `μ`, and the sheafified pure tensor agrees with it only through the unexposed
  `SheafOfModules.tensorUnderlyingIso`. A new named section would duplicate `μ`, and stating the
  theorem for `μ` needs a bridge lemma `main` lacks.
- **On an affine open, nonvanishing loci are affine** (`IsAffineOpen.nonvanishingLocus`, via
  Mathlib's `isAffineOpen_of_isAffineOpen_basicOpen`).
- **Ampleness is stable under positive powers** (`LineBundleClass.IsAmple.pow`,
  `isAmple_pow_iff`). This closes the earlier remaining item "`a` relatively ample ⇒ `aⁿ`
  relatively ample" (`IsRelativelyAmple.pow`, `isRelativelyAmple_pow_iff`). With it,
  `InvertibleSheaf.isRelativelyAmple_of_tensorPow` became the iff `isRelativelyAmple_tensorPow_iff`;
  the old one-directional name is removed.
- **Ample times globally generated is ample** (`IsAmple.mul_mk_of_isGloballyGenerated`), and the
  same holds for relative ampleness (`IsRelativelyAmple.mul_mk_of_isGloballyGenerated`).
- **`𝒪(1)` is ample on a quasi-compact `Proj`.** The new file
  `ProjectiveSpectrum/TwistingSheaf/Ample.lean` proves that `X_{r/1} = D₊(r)` for `r` of degree
  one (`Proj.nonvanishingLocus_toTwistingSheaf`, when the degree-one standard opens cover). It
  derives `Proj.isAmple_twistingSheaf_one`, and `Proj.isAmple_twistingSheaf` for `𝒪(n)`, `n > 0`.
- **`𝒪(1)` is relatively ample on a quasi-compact relative `Proj`**
  (`LineBundleClass.isRelativelyAmple_relativeProjTwistingSheafOne`). Over an affine `V`, the
  chart `Proj (⨁ n, Γ(Aₙ, V))` is the preimage of `V` (`relativeProjToBase_preimage`), and
  `𝒪(1)` restricts to the chart's `𝒪(1)` (`restrictRelativeProjTwistingSheafIso`). This is the
  identity case of "relatively very ample + quasi-compact ⇒ relatively ample". If `A` is of
  finite type with `A₀` finite, the structure morphism is proper by `main`'s
  `isProper_relativeProjToBase`, so the hypothesis holds.
- Split 4 now carries the ampleness API of the seventh and ninth sessions. The Proj result is
  the new split 5. The relative file is split 6 and still completes the target.
- Kernel-time note for the port. In `isRelativelyAmple_relativeProjTwistingSheafOne`, do not
  ascribe the chart map the type `Proj (A.gradedSectionsGrading V) ⟶ A.relativeProj`. That
  ascription makes the kernel unfold the glued cover and takes about 35 s. Leaving its type as
  `A.relativeProjCover.f U` takes about 2 s.
- Verified: `lake build` green, `lookahead-check` ok, and `#lint in TauCeti` over the import
  closure of `RelativelyAmple.lean` passes all 15 linters. `scripts/lint-style.sh` needs `uvx`,
  which this sandbox lacks. Instead I checked the changed files by grep: no combining marks, no
  trailing whitespace.

## Changes in the eighth session (2026-11-04, 01:15 UTC)

- `main` is unchanged at `333c9e49143`, so there is nothing new to merge.
- **Over an affine base, relative ampleness is ampleness** (`LineBundleClass.isRelativelyAmple_iff_isAmple`).
  This closes the remaining item "over an affine base, ampleness ⇒ relative ampleness". The
  earlier note expected Stacks' extension of sections from `X_s`, but the argument is short. For
  `V` an affine open of a separated base, `V ⟶ S` is an affine morphism. Its base change, the
  inclusion of `f⁻¹ V`, is then an affine open immersion. Ampleness pulls back along such a map
  (split 4). So `LineBundleClass.IsAmple.isRelativelyAmple` holds more generally: if `S` is
  separated and `f` is quasi-compact, an ample class is relatively ample for `f`.
- **Relative ampleness is preserved by pullback along affine open immersions**
  (`IsRelativelyAmple.pullback_of_isOpenImmersion`). `isRelativelyAmple_pullback_iff_of_isIso`
  is now a two-line corollary of it, replacing the earlier direct proof.
- **Relative ampleness is preserved by composition with an affine morphism**
  (`IsRelativelyAmple.comp`), **and it restricts to opens of the base**
  (`IsRelativelyAmple.restrict`: `a ∣_{f⁻¹ U}` is relatively ample for `f ∣_ U`). The second is
  one direction of locality on the base.
- All of this is in `RelativelyAmple.lean` (now the last split).

## Changes in the seventh session (2026-11-04, 00:50 UTC)

- `main` is unchanged at `333c9e49143`, so there is nothing new to merge.
- **The nonvanishing locus of a section pulled back along an open immersion is the preimage.**
  This proves remaining item (b) below for open immersions. The new theorem
  `Scheme.Modules.nonvanishingLocus_restrictAppIso_inv` sits at the end of `main`'s
  `LineBundle/NonvanishingLocus.lean`. The proof works on sections, using
  `le_nonvanishingLocus_iff`, and needs no stalk comparison.
- **Ampleness is preserved by pullback along affine open immersions.**
  `LineBundleClass.IsAmple.pullback_of_isOpenImmersion` and
  `isAmple_pullback_iff_of_isIso` are added to `main`'s `LineBundle/Ample.lean`, which now imports
  `LineBundle/Functoriality.lean`.
- **Over an affine base, relative ampleness implies ampleness**
  (`LineBundleClass.IsRelativelyAmple.isAmple`). **Relative ampleness is invariant under
  isomorphisms of the source over the base** (`isRelativelyAmple_pullback_iff_of_isIso`). Both are
  in `RelativelyAmple.lean`.
- The new material is part of split 4.

## Changes in the sixth session

- The stubs are replaced by `main`'s declarations, and `main` is merged in at `333c9e49143`.
- **Relative ampleness now follows the Stacks Project definition (Tag 01VH).** `main` now has
  absolute ampleness (`LineBundleClass.IsAmple`, #25214). The earlier stand-in definition was
  `InvertibleSheaf.IsRelativelyAmple`, meaning "some positive tensor power is relatively very
  ample". It is replaced by `LineBundleClass.IsRelativelyAmple a f`: `f` is quasi-compact, and
  the pullback of `a` to `f⁻¹ V` is ample for every affine open `V ⊆ S`. Ampleness lives on
  line-bundle classes, and this definition follows that convention. AdicSpacesPartIII
  (README ~l. 3672) expects exactly this definition: it compares it with `IsAmple` over
  `Spec A`. The stand-in's API (`of_tensorPow`, `of_iso`, `pullback`, `isSeparated` and
  `IsRelativelyVeryAmple.isRelativelyAmple`) is removed with it. For the Stacks definition those
  results are real theorems, and they remain to be proved (see below).
- **Relative very ampleness no longer asks for `A₁` of finite type.** This matches Stacks
  Definition 29.38.1, where `ℰ` is only quasi-coherent. `isRelativelyVeryAmple_relativeProjTwistingSheaf`
  therefore loses its `[(A.X 1).IsFiniteType]` argument.
- **Projective morphisms now require `A` of finite type and `A₀` finite**, instead of `A₁` of
  finite type. This is the hypothesis of `main`'s `isProper_relativeProjToBase`. With it, the new
  instance `IsProjective.isProper` proves that projective morphisms are proper. It replaces the
  `IsProjective.isSeparated` instance, since separatedness now follows from properness. The
  definition is still equivalent to Stacks' `ℙ(ℰ)` definition (`ℰ` of finite type): `Sym ℰ`
  satisfies these hypotheses, and conversely `A₁` is finite over `A₀`, hence over `𝒪_S`. The
  reason is that the degree-one components of a finite set of homogeneous algebra generators
  span `A₁` over `A₀`. In addition `Proj_S A` is closed in `ℙ(A₁)`, because the charts
  `A_(f)` only see `A₊`.
- I removed the Stacks tags I could not verify offline (01VM, 01W8, 01WC). Only 01VH is used,
  because the roadmap quotes it.
- Placement: adding `LineBundle/GlobalGeneration/` next to `LineBundle/GlobalGeneration.lean`
  would leave flat siblings. So split 3 moves `main`'s `GlobalGeneration.lean` to
  `GlobalGeneration/Basic.lean` and updates its three importers (`LineBundle/LocalRing.lean`,
  `WeilDivisor/Scheme/GlobalGeneration.lean` and the new files).

## Splits

1. **Name the generated-in-degree-one condition** (after: none). This is a refactor that touches
   only `main` code.
   - File: `TauCeti/AlgebraicGeometry/RelativeProj/TwistingSheaf.lean` (+48/−4).
   - Declarations: `CategoryTheory.CommMon.IsGeneratedInDegreeOne`, `CommMon.isGeneratedInDegreeOne_iff`,
     `CommMon.isGeneratedInDegreeOne_of_adjoin_eq_top` (generation over `Γ(X, U)` suffices), and
     `CommMon.isInvertible_relativeProjTwistingSheaf` restated with the new predicate.
   - Roadmap line: `Roadmap: SchemeAndStackFoundations` (§0.3 defines "generated in degree one").
   - Subject: `refactor(AlgebraicGeometry/RelativeProj): name the generated-in-degree-one condition`
2. **Tensor powers of line bundles** (after: none).
   - File: `TauCeti/AlgebraicGeometry/LineBundle/Power.lean` (112 lines, new).
   - Declarations: `InvertibleSheaf.tensorPow`, `tensorPow_zero`, `tensorPow_succ`,
     `LineBundleClass.mk_tensorPow`, `InvertibleSheaf.nonempty_tensorPow_obj_iso`,
     `nonempty_tensorPow_add_iso`, `nonempty_tensorPow_tensorPow_iso`,
     `nonempty_pullback_tensorPow_iso` (all in `TauCeti.AlgebraicGeometry`).
   - Subject: `feat(AlgebraicGeometry/LineBundle): tensor powers of line bundles`
3. **Global generation of trivial bundles, pullbacks, tensor products and tensor powers**
   (after: 2).
   - Files: `TauCeti/CategoryTheory/Monoidal/Closed/Epi.lean` (51 lines, new);
     `TauCeti/AlgebraicGeometry/LineBundle/GlobalGeneration/Pullback.lean` (71, new);
     `TauCeti/AlgebraicGeometry/LineBundle/GlobalGeneration/TensorProduct.lean` (79, new); the move
     `LineBundle/GlobalGeneration.lean` → `LineBundle/GlobalGeneration/Basic.lean` (275, unchanged)
     with its importers `LineBundle/LocalRing.lean` and `WeilDivisor/Scheme/GlobalGeneration.lean`.
   - Declarations: `TauCeti.MonoidalClosed.epi_whiskerRight`, `TauCeti.MonoidalClosed.epi_tensorHom`;
     `InvertibleSheaf.isGloballyGenerated_trivial`, `InvertibleSheaf.IsGloballyGenerated.pullback`,
     `IsGloballyGenerated.tensorProduct`, `IsGloballyGenerated.tensorPow`.
     `CategoryTheory.MonoidalClosed.mono_pre_app` on `main` inlines the argument of
     `epi_whiskerRight`. Switching it over is a separate refactor PR after this split.
   - Subject: `feat(AlgebraicGeometry/LineBundle): global generation of trivial bundles, pullbacks, tensor products and tensor powers`
4. **Pulling back nonvanishing loci, and stability of ampleness** (after: 2, 3). It changes only
   `main` files (about 470 lines):
   - `Algebra/Category/ModuleCat/Sheaf/TensorProduct/Basic.lean`: +29, the site-level pure tensor
     of sections `TauCeti.SheafOfModules.tmul` and `SheafOfModules.tmul_map` (restriction).
   - `LineBundle/TensorProduct.lean`: `@[expose]` on `InvertibleSheaf.tensorProduct`, so that
     sections of `(L.tensorProduct K).obj` are seen to be sections of the sheaf tensor product.
   - `LineBundle/NonvanishingLocus.lean`: the part of this branch's +299/−2 other than
     `sup_range_map_nonvanishingLocus_inf_eq_top` (split 5). It now imports
     `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
     `Algebra/Category/ModuleCat/Sheaf/TensorProduct/Stalk.lean`, `LineBundle/TensorProduct.lean`,
     `Modules/Pullback/ResidueField.lean` and `RingTheory/LocalRing/Module.lean`.
   - `LineBundle/Ample.lean`: everything up to `isAmple_pullback_iff_of_isIso`. It now imports
     `LineBundle/Functoriality.lean` and `LineBundle/GlobalGeneration/TensorProduct.lean` (split 3).
   - `Modules/Pullback/ResidueField.lean`: +29.
   - `RingTheory/LocalRing/Module.lean`: +21.

   Declarations:
   - `TauCeti.IsLocalRing.span_singleton_eq_top_iff_one_tmul_ne_zero` (`Module.lean`).
   - `Scheme.Modules.injective_pullbackSections_SpecMap` (`ResidueField.lean`).
   - In `NonvanishingLocus.lean`: `AlgebraicGeometry.IsAffineOpen.nonvanishingLocus`,
     `Scheme.Modules.nonvanishingLocus_restrictAppIso_inv`,
     `Scheme.Modules.mem_nonvanishingLocus_iff_pullbackSectionsLE_ne_zero`,
     `Scheme.Modules.nonvanishingLocus_pullbackSections`,
     `Scheme.Modules.nonvanishingLocus_tmul` (`X_{s ⊗ t} = X_s ∩ X_t`), and in namespace
     `TauCeti.AlgebraicGeometry.InvertibleSheaf` the tensor product of sections of line bundles
     `tmul` with `tmul_map`, `smul_tmul`, `tmul_smul`, `tmul_sub`, `tmul_zero` and
     `nonvanishingLocus_tmul`.
   - In `Ample.lean` (namespace `TauCeti.AlgebraicGeometry.LineBundleClass`):
     `InvertibleSheaf.exists_nonvanishingLocus_eq_of_mk_eq_pow`, `IsAmple.pow`,
     `isAmple_pow_iff` (simp), `IsAmple.mul_mk_of_isGloballyGenerated`, `IsAmple.mul`,
     `IsAmple.pullback`
     (`[IsAffineHom e]`) and `isAmple_pullback_iff_of_isIso`.
   - Subject: `feat(AlgebraicGeometry/LineBundle): nonvanishing loci pull back; ampleness under affine pullback, powers and globally generated twists`
5. **Schemes with an ample line bundle are separated; ampleness on basic-open covers, of
   exterior products and on quasi-affine schemes** (after: 4):
   - `Morphisms/Separated.lean` (+59): `AlgebraicGeometry.Scheme.IsSeparated.of_isAffineOpen`.
   - `LineBundle/NonvanishingLocus.lean` (+56):
     `Scheme.Modules.sup_range_map_nonvanishingLocus_inf_eq_top`.
   - `TauCeti/AlgebraicGeometry/Pullback/Affine.lean` (56 lines, new):
     `AlgebraicGeometry.IsAffineOpen.preimage_inf_preimage_of_isPullback`.
   - `LineBundle/Ample.lean` (the rest of its diff; it now also imports
     `Modules/Localization.lean`, `Morphisms/Separated.lean` and `Pullback/Affine.lean`):
     `IsAmple.isSeparated`, `AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_iSup_basicOpen_eq_top`,
     `InvertibleSheaf.exists_nonvanishingLocus_eq_image` (sections of a line bundle on an open
     subscheme `U` come from sections over `U`; used by the next lemma and by split 10),
     `IsAmple.of_iSup_basicOpen_eq_top`, `IsAmple.pullback_mul_pullback`,
     `InvertibleSheaf.exists_isAffineOpen_nonvanishingLocus_of_isQuasiAffine`,
     `InvertibleSheaf.isGloballyGenerated_of_isQuasiAffine` and `isAmple_of_isQuasiAffine`. It
     also reproves the reverse direction of `main`'s `isAmple_one_iff` by `isAmple_of_isQuasiAffine`
     (so the quasi-affine block moves before it) and deletes `main`'s `isAmple_one` and
     `isAmple_of_pow_eq_one`, which it subsumes and which have no other users. About 440 lines.
   - Subject: `feat(AlgebraicGeometry/LineBundle): schemes with an ample line bundle are separated; ampleness on basic-open covers and of exterior products`
6. **`𝒪(1)` pulls back to an ample line bundle along immersions from quasi-compact schemes**
   (after: 4).
   - File: `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/Ample.lean` (199 lines,
     new; imports `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, `LineBundle/Ample.lean` and
     `ProjectiveSpectrum/TwistingSheaf/TensorProduct.lean`).
   - Declarations (namespace `AlgebraicGeometry.Proj`, like the neighbouring twisting-sheaf
     files): `nonvanishingLocus_toTwistingSheaf` (every degree), `exists_mem_basicOpen_le`,
     `isAmple_pullback_twistingSheaf_one`, `isAmple_twistingSheaf_one`, `isAmple_twistingSheaf`.
   - Subject: `feat(AlgebraicGeometry/ProjectiveSpectrum): O(1) pulls back to an ample line bundle along immersions from quasi-compact schemes`
7. **The symmetric algebra is generated in degree one and its relative `Proj` is proper** (after: 1).
   - Files: `main`'s `Modules/Quasicoherent/GradedAlgebra/SymmetricAlgebra/Adjunction.lean`
     (+209; it now imports `Modules/SymmetricPower/Sections.lean` and
     `LinearAlgebra/SymmetricAlgebra/Homogeneous.lean`); `main`'s `RelativeProj/Basic.lean` (+12);
     `RelativeProj/SymmetricAlgebra.lean` (185 lines, new). About 400 lines.
   - Declarations: in `Adjunction.lean`, `gradedSymmetricAlgebraSectionsEquiv` with
     `gradedSymmetricAlgebraSectionsEquiv_ι`, `_mem`, `_symm_mem`, and
     `adjoin_gradedSectionsGrading_one_gradedSymmetricAlgebra` (with private helper lemmas); in
     `RelativeProj/Basic.lean`, the instance `CommMon.isIso_relativeProjCover_f_top`; in
     `RelativeProj/SymmetricAlgebra.lean`, `isGeneratedInDegreeOne_gradedSymmetricAlgebra`,
     `finiteType_sections_gradedSymmetricAlgebra`, `finite_sections_gradedSymmetricAlgebra_zero`,
     `isProper_relativeProjToBase_gradedSymmetricAlgebra`, `gradedSymmetricAlgebraSectionsGradedHom`,
     `gradedSymmetricAlgebraSectionsGradedHomInv`, `projGradedSectionsGradingIso`,
     `projGradedSectionsGradingIso_hom_toSpecCoeff`, `relativeProjGradedSymmetricAlgebraIso`,
     `relativeProjGradedSymmetricAlgebraIso_inv_relativeProjToBase`.
   - Roadmap line: `Roadmap: SchemeAndStackFoundations` (§0.3 relative `Proj`).
   - Subject: `feat(AlgebraicGeometry/RelativeProj): the symmetric algebra is generated in degree one and its relative Proj is proper`
8. **Sections over nonvanishing loci extend; ampleness pulls back along immersions**
   (after: 2, 4, 5).
   - Files: `TauCeti/AlgebraicGeometry/LineBundle/Extension.lean` (326 lines, new; imports
     `LineBundle/NonvanishingLocus.lean`, `LineBundle/Power.lean`, and privately
     `Modules/Localization.lean` and `Algebra/Group/Action/Pow.lean`); `LineBundle/Ample.lean`
     (+75; it now also imports `Mathlib.AlgebraicGeometry.Morphisms.Immersion` and
     `LineBundle/Extension.lean`).
   - Declarations in `Extension.lean` (namespace `TauCeti.AlgebraicGeometry.InvertibleSheaf`):
     `oneSection`, `oneSection_map`, `nonvanishingLocus_oneSection`; the tensor powers of sections
     `sectionPow` with `sectionPow_zero`, `sectionPow_succ`, `sectionPow_map`, `sectionPow_smul`,
     `nonvanishingLocus_sectionPow_succ`, `nonvanishingLocus_sectionPow_of_le`,
     `nonvanishingLocus_le_nonvanishingLocus_sectionPow`; the two halves of
     Stacks 01PW for line bundles on a quasi-compact (quasi-separated) open,
     `exists_tmul_sectionPow_eq_zero` (sections vanishing on `X_s` are killed by `s^{⊗n}`) and
     `exists_map_eq_tmul_sectionPow` (sections over `X_s` extend after multiplication by
     `s^{⊗n}`), with two private lemmas.
   - Declarations in `Ample.lean`: `LineBundleClass.IsAmple.exists_isAffineOpen_nonvanishingLocus_le`
     (the affine nonvanishing loci form a basis) and `LineBundleClass.IsAmple.pullback_of_isImmersion`
     (pullback along an immersion from a quasi-compact scheme).
   - Subject: `feat(AlgebraicGeometry/LineBundle): sections over nonvanishing loci extend; ampleness pulls back along immersions`
9. **Relatively ample line bundles** (after: 2, 3, 4, 5, 8).
   - Files: `TauCeti/AlgebraicGeometry/LineBundle/RelativelyAmple.lean` (544 lines, new; imports
     `Fibers.lean` and `LineBundle/Ample.lean`); `main`'s `AlgebraicGeometry/Fibers.lean` (+27:
     the instances `TauCeti.isAffineHom_fromSpecResidueField` and `TauCeti.isAffineHom_fiberι`).
   - Declarations (namespace `TauCeti.AlgebraicGeometry.LineBundleClass` unless noted):
     `IsRelativelyAmple` (Stacks 01VH), `IsRelativelyAmple.of_pow`, `IsRelativelyAmple.pow`,
     `isRelativelyAmple_pow_iff` (simp), `IsRelativelyAmple.mul_mk_of_isGloballyGenerated`,
     `IsRelativelyAmple.mul`, `IsRelativelyAmple.isAmple` (over a quasi-affine base),
     `IsAmple.isRelativelyAmple` (over a
     separated base, for quasi-compact `f`), `isRelativelyAmple_iff_isAmple`,
     `IsRelativelyAmple.pullback` (along affine morphisms),
     `IsRelativelyAmple.pullback_of_isImmersion` (along quasi-compact immersions, from split 8),
     `IsRelativelyAmple.isAmple_fiber`,
     `isRelativelyAmple_pullback_iff_of_isIso`, `IsRelativelyAmple.restrict`,
     `IsRelativelyAmple.comp_of_isQuasiAffine` and `IsRelativelyAmple.comp` (with a quasi-affine,
     resp. affine, morphism), `isRelativelyAmple_of_iSup_eq_top` and
     `isRelativelyAmple_iff_of_iSup_eq_top` (locality on the base), `IsRelativelyAmple.of_comp`
     (along a separated morphism), `isRelativelyAmple_comp_iff` (affine morphisms),
     `IsRelativelyAmple.isSeparated`, `IsRelativelyAmple.pullback_snd` (base change),
     `IsRelativelyAmple.pullback_fst_mul_pullback_snd` (exterior products),
     `isRelativelyAmple_of_isQuasiAffine`, `isRelativelyAmple_one_iff`,
     `isRelativelyAmple_of_isAffineHom`, and
     `InvertibleSheaf.isRelativelyAmple_tensorPow_iff`.
   - Roadmap line: `Roadmap: StableReduction`.
   - Subject: `feat(AlgebraicGeometry/LineBundle): relatively ample line bundles`
10. **Relative ampleness composes after twisting by a large power** (after: 2, 3, 4, 5, 8, 9).
   - File: `TauCeti/AlgebraicGeometry/LineBundle/RelativelyAmple/Comp.lean` (177 lines, new;
     imports `LineBundle/RelativelyAmple.lean`).
   - Declarations (namespace `TauCeti.AlgebraicGeometry.LineBundleClass`):
     `IsRelativelyAmple.exists_isAmple_mul_pullback_pow` (`a` relatively ample for `f : X ⟶ Y`,
     `b` ample on `Y` ⇒ `a · f* bⁿ` ample for `n ≫ 0`) and
     `IsRelativelyAmple.exists_isRelativelyAmple_comp_mul_pullback_pow` (Stacks 0C4K over a
     quasi-compact base).
   - Roadmap line: `Roadmap: StableReduction`.
   - Subject: `feat(AlgebraicGeometry/LineBundle): relative ampleness composes after twisting by a large power`
11. **Intersection numbers of powers** (after: none). A small addition to `main` only.
   - File: `main`'s `TauCeti/AlgebraicGeometry/IntersectionNumber/Basic.lean` (+27/−1).
   - Declarations: `TauCeti.AlgebraicGeometry.LineBundleClass.intersectionNumber_pow` and
     `intersectionNumber_zpow` (both simp): `(aⁿ · C) = n (a · C)` on a regular proper integral
     curve.
   - Subject: `feat(AlgebraicGeometry/IntersectionNumber): intersection numbers of powers`
12. **The sheaf associated with a finite module is of finite type** (after: none).
    - Files: `main`'s `Modules/FinitePresentation.lean` (+24; it now imports
      `Algebra/Category/ModuleCat/Sheaf/FiniteType.lean`).
    - Declarations: the instance `TauCeti.AlgebraicGeometry.isFiniteType_tilde`.
    - Roadmap line: `Roadmap: none` (general sheaf infrastructure).
    - Subject: `feat(AlgebraicGeometry/Modules): the sheaf associated with a finite module is of finite type`
13. **Finiteness and generation of the degree-one part of a graded algebra** (after: none).
    - File: `TauCeti/RingTheory/GradedAlgebra/DegreeOne.lean` (159 lines, new; imports `main`'s
      `RingTheory/GradedAlgebra/FiniteType.lean`).
    - Declarations (namespace `TauCeti.GradedAlgebra`): `exists_mem_grade_of_mem_closure`,
      `mem_span_inter_grade_one`, `finite_grade_one`, `mem_closure_grade_one`.
    - Roadmap line: `Roadmap: StableReduction` (input of the comparison in split 17).
    - Subject: `feat(RingTheory/GradedAlgebra): finiteness and generation of the degree-one part of a graded algebra`
14. **Relatively very ample line bundles, projective morphisms, projective bundles and blowups**
    (after: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12). It imports splits 1, 6, 7 and 10, and
    through them 2, 3, 4, 5, 8 and 9; splits 11 and 12 are ordered before it conservatively.
    It carries the target's main exported definitions and theorems (`IsRelativelyVeryAmple`,
    `IsProjective` and their API).
    - Files (about 460 lines):
      - `TauCeti/AlgebraicGeometry/Morphisms/Projective.lean` (309 lines in this split, new; imports
        `LineBundle/RelativelyAmple/Comp.lean`);
      - `TauCeti/AlgebraicGeometry/Blowup/Projective.lean` (130 lines, new);
      - `main`'s `Blowup/IdealSheaf.lean` (+24/−12: the two inline bullets of
        `isProper_blowupToBase` become `finiteType_sections_reesAlgebra` and
        `finite_sections_reesAlgebra_zero`).
    - Declarations in `Morphisms/Projective.lean`: `CommMon.relativeProjTwistingSheafOne`;
      `InvertibleSheaf.IsRelativelyVeryAmple`, `IsRelativelyVeryAmple.of_iso`,
      `isRelativelyVeryAmple_relativeProjTwistingSheaf`, `IsRelativelyVeryAmple.pullback`,
      `IsRelativelyVeryAmple.isSeparated`, `IsRelativelyVeryAmple.isRelativelyAmple` (for
      quasi-compact `f`); `LineBundleClass.isRelativelyAmple_relativeProjTwistingSheafOne`;
      `IsProjective` (class), `isProjective_relativeProjToBase`, the instance `IsProjective (j ≫ f)`
      for a closed immersion `j`, `IsProjective.exists_isRelativelyVeryAmple_isRelativelyAmple`,
      `IsProjective.exists_isRelativelyAmple_comp` (over a quasi-compact base), the
      instance `IsProjective.isProper`; projective bundles:
      `InvertibleSheaf.isRelativelyVeryAmple_relativeProjTwistingSheaf_gradedSymmetricAlgebra`,
      `LineBundleClass.isRelativelyAmple_relativeProjTwistingSheafOne_gradedSymmetricAlgebra`, and
      the instance `isProjective_relativeProjToBase_gradedSymmetricAlgebra`; over an affine base, the
      instance `isProjective_toSpecCoeff_comp_fromSpec` (`Proj (Sym Γ(F, S)) ⟶ S`).
    - Declarations in `Blowup/Projective.lean` (namespace `AlgebraicGeometry.Scheme.IdealSheafData`,
      like its neighbours): `adjoin_gradedSectionsGrading_one_reesAlgebra`,
      `isGeneratedInDegreeOne_reesAlgebra`, `isProjective_blowupToBase` (Stacks 02NS),
      `isRelativelyVeryAmple_relativeProjTwistingSheaf_reesAlgebra` and
      `isRelativelyAmple_relativeProjTwistingSheafOne_reesAlgebra`; in namespace
      `TauCeti.AlgebraicGeometry` the instance `isProjective_of_isClosedImmersion` (closed
      immersions, in particular isomorphisms, are projective, via the blowup along `⊤`).
    - Subject: `feat(AlgebraicGeometry/Morphisms): relatively very ample line bundles, projective morphisms, projective bundles and blowups`

15. **Recognising the glued scheme of a relative gluing datum** (after: none). Generic gluing
    infrastructure, the first step of the remaining general base change of projective morphisms.
    - File: `TauCeti/AlgebraicGeometry/RelativeGluing.lean` (103 lines, new; imports only Mathlib).
    - Declarations (namespace `AlgebraicGeometry.Scheme.Cover.RelativeGluingData`, extending
      Mathlib's): `desc_comp_eq_toBase`, `isIso_desc_of_isPullback`, `isoOfIsPullback`,
      `ι_isoOfIsPullback_hom`, `isoOfIsPullback_hom_comp`.
    - Roadmap line: `Roadmap: StableReduction`.
    - Subject: `feat(AlgebraicGeometry/RelativeGluing): recognise the glued scheme of a relative gluing datum`

16. **Pullback of graded sections, and `Proj` of them as a base change over affine opens**
    (after: none). Imports only `main`. The affine-local step of the general base change of
    projective morphisms.
    - Files: `TauCeti/AlgebraicGeometry/Modules/Pullback/Monoidal/Sections.lean` (77 lines, new)
      and `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/GradedAlgebra/PullbackSections.lean`
      (about 390 lines, new).
    - Declarations: `AlgebraicGeometry.Scheme.Hom.δ_app_pullbackSections_μ` and
      `Scheme.Hom.pullbackObjUnitIso_hom_app_pullbackSections` (pulled-back sections and the
      monoidal structure of pullback); in namespace
      `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra`: `pullbackHomogeneousSections` (with
      `_apply`, `_gAlgebra_toFun`, `_gOne`, `_gMul`), `pullbackGradedSections` (with `_of`,
      `_algebraMap`), `pullbackGradedSectionsGradedHom` (with `_apply`), `pullbackGradedSectionsLE`
      (with `_of`, `_algebraMap`), `pullbackGradedSectionsLEGradedHom` (with `_apply`),
      `irrelevant_le_map_pullbackGradedSectionsLEGradedHom` and
      `isPullback_proj_map_pullbackGradedSectionsLEGradedHom`; then
      `restrictGradedSections_comp_pullbackGradedSectionsLE`,
      `pullbackGradedSectionsLE_comp_restrictGradedSections`,
      `span_range_pullbackGradedSectionsLE`, `adjoin_gradedSectionsGrading_pullback_eq_top`,
      `finiteType_pullback_sections` and `finite_pullback_sections_zero`. The file is now 520
      lines, so the split is about 600 lines; if a reviewer asks, the last four declarations can
      move to split 17.
    - Roadmap line: `Roadmap: StableReduction`.
    - Subject: `feat(AlgebraicGeometry/Modules): pull back graded sections, and Proj of them as a base change over affine opens`

17. **Charts of the base change of a relative `Proj` over small affine opens; finiteness and
    generation in degree one of the pulled-back algebra** (after: 1, 16). Step 1 of the general
    base change of projective morphisms, and step 3.
    - Files: `TauCeti/AlgebraicGeometry/RelativeProj/Pullback.lean` (382 lines, new;
      imports split 16's `PullbackSections.lean` and `main`'s `RelativeProj/TwistingSheaf.lean`,
      where split 1 names `IsGeneratedInDegreeOne`); `TauCeti/RingTheory/Localization/Closure.lean`
      (77 lines, new; imports only Mathlib); `main`'s `RelativeProj/Basic.lean` (+14: the lemma
      below and a docstring line); `main`'s `Modules/GradedAlgebra/Localization.lean` (+102, now
      importing `Mathlib.RingTheory.RingHom.FiniteType` and `RingTheory/Localization/Closure.lean`).
      About 580 lines in all.
    - Declarations: in `Closure.lean`, `TauCeti.IsLocalization.exists_mul_eq_algebraMap_of_mem_closure`
      and `TauCeti.IsLocalization.exists_mul_mem_of_mem_closure`;
      `CategoryTheory.CommMon.isPullback_relativeProjCover_fromSpec` (in
      `Basic.lean`); in namespace `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra`:
      `projPullbackToRelativeProj` (with `_relativeProjToBase`),
      `isPullback_projPullbackToRelativeProj`, `projPullbackToPullbackRelativeProj` (with `_fst`,
      `_snd`), `isPullback_projPullbackToPullbackRelativeProj`,
      `proj_map_restrict_projPullbackToRelativeProj`, `projPullbackToRelativeProj_basicOpen`, the
      private `proj_map_restrict_projPullbackToRelativeProj_eq`,
      `isOpenImmersion_proj_map_restrictGradedSections`, `exists_basicOpen_le_preimage_basicOpen` and
      `exists_proj_map_restrictGradedSections_eq`, `projPullbackToRelativeProj_eq`, the instance
      `isOpenImmersion_projPullbackToPullbackRelativeProj`,
      `exists_projPullbackToPullbackRelativeProj_eq`, the
      private `span_setOf_basicOpen_le_preimage_eq_top`,
      `finiteType_pullback_sections_of_isAffineOpen`, `finite_pullback_sections_zero_of_isAffineOpen`,
      `isGeneratedInDegreeOne_pullback`;
      in `Localization.lean`, `CategoryTheory.CommMon.finiteType_gradedSections_of_span_eq_top`, the
      private `exists_pow_mul_of_eq_restrictGradedSections` and
      `CategoryTheory.CommMon.adjoin_gradedSectionsGrading_eq_top_of_span_eq_top`. If a reviewer
      asks, `Closure.lean` and the two `Localization.lean` locality lemmas can be split off as a
      preliminary PR after nothing.
    - Roadmap line: `Roadmap: StableReduction`.
    - Subject: `feat(AlgebraicGeometry/RelativeProj): charts of the base change of a relative Proj over small affine opens, and the pulled-back algebra stays of finite type and generated in degree one`

18. **The relative `Proj` commutes with base change** (after: 1, 15, 16, 17). It imports split 15's
    `RelativeGluing.lean` and split 17's `RelativeProj/Pullback.lean` (which needs 1 and 16).
    - Files: `TauCeti/AlgebraicGeometry/RelativeProj/BaseChange.lean` (225 lines, new), and a
      one-sentence pointer to it in the module docstring of split 17's `RelativeProj/Pullback.lean`
      (if split 17 has merged, this is a +3/−3 edit of that file).
    - Declarations: `TauCeti.AlgebraicGeometry.AffineZariskiSiteOver`,
      `AffineZariskiSiteOver.inclusion`, `directedCoverOver` and its `LocallyDirected` instance;
      in `GradedQuasicoherentAlgebra`: `relativeProjGluingDataOver`,
      `relativeProjGluingDataOverToRelativeProj`, `relativeProjGluingDataOverIso`,
      `relativeProjGluingDataOverIso_hom_comp`, `relativeProjGluingDataOverToPullback`,
      `isPullback_relativeProjGluingDataOverToPullback`, `relativeProjPullbackIso`,
      `relativeProjPullbackIso_hom_snd`, `relativeProjCover_f_relativeProjPullbackIso_hom` and
      `isPullback_relativeProjPullback`.
    - Subject: `feat(AlgebraicGeometry/RelativeProj): the relative Proj commutes with base change`
19. **Functoriality of the relative `Proj`** (after: none). It needs only `main`.
    - File: `TauCeti/AlgebraicGeometry/RelativeProj/Functor.lean` (247 lines, new; imports `main`'s
      `RelativeProj/Basic.lean` and `ProjectiveSpectrum/ClosedImmersion.lean`).
    - Declarations (all `CategoryTheory.CommMon.*`): `gradedSectionsGradedHom` (with `_apply`),
      `gradedSectionsGradedHom_comp_restrictGradedSectionsGradedHom`,
      `gradedSectionsGrading_subset_range_gradedSectionsGradedHom`, `IrrelevantLeMap`,
      `irrelevantLeMap_of_surjective`, `relativeProjMap`, `relativeProjCover_f_relativeProjMap`,
      `relativeProjMap_relativeProjToBase`, `relativeProjMap_id`, `relativeProjMap_comp`,
      `isPullback_relativeProjMap`, `isClosedImmersion_relativeProjMap`; private
      `relativeProjGluingDataMap` and `proj_map_gradedSectionsGradedHom_comp`.
    - Roadmap line: `Roadmap: StableReduction` (Layer 2, relative `Proj` and projective morphisms).
    - Subject: `feat(AlgebraicGeometry/RelativeProj): functoriality of the relative Proj`
20. **Closed immersions of relative `Proj`s from maps surjective in degree one** (after: 1, 7, 13,
    19). It imports split 19's `Functor.lean`, split 7's `RelativeProj/SymmetricAlgebra.lean`
    (`isGeneratedInDegreeOne_gradedSymmetricAlgebra`, which also needs split 1's
    `IsGeneratedInDegreeOne`) and split 13's `RingTheory/GradedAlgebra/DegreeOne.lean`.
    - File: `TauCeti/AlgebraicGeometry/RelativeProj/ClosedImmersion.lean` (221 lines, new).
    - Declarations: `CategoryTheory.CommMon.surjective_app_of_isGeneratedInDegreeOne`,
      `CommMon.irrelevantLeMap_of_isGeneratedInDegreeOne`,
      `CommMon.isClosedImmersion_relativeProjMap_of_isGeneratedInDegreeOne`; in
      `TauCeti.AlgebraicGeometry`: the instances
      `GradedQuasicoherentAlgebra.isIso_counit_app_hom_hom_hom_one` and
      `epi_gradedSymmetricAlgebra_map_hom_hom_hom_one`, and
      `GradedQuasicoherentAlgebra.isClosedImmersion_relativeProjMap_counit`,
      `isClosedImmersion_relativeProjMap_gradedSymmetricAlgebra_map`; private
      `gradedSectionsMap_apply_apply` and `isIso_eqToHom`.
    - Subject: `feat(AlgebraicGeometry/RelativeProj): closed immersions of relative Proj from maps surjective in degree one`
21. **Projective schemes over a ring are the projective morphisms to its spectrum; projective
    morphisms are stable under base change** (after: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
    15, 16, 17, 18, 19, 20). It imports splits 12, 13, 14 and 18, and through them every split
    up to 18; it is listed after all of them, including 19 and 20, so that it is the last split
    to merge and the one that completes the branch's current part of the target. (It was split 19
    before the twenty-seventh session.)
    - Files: `TauCeti/AlgebraicGeometry/Morphisms/ProjectiveOver.lean` (362 lines, new; imports
      split 18's `RelativeProj/BaseChange.lean`, `Morphisms/Projective.lean`,
      `ProjectiveSpectrum/ProjectiveOver.lean`, `ProjectiveSpectrum/ClosedImmersion.lean` and
      `RingTheory/GradedAlgebra/DegreeOne.lean`); `main`'s `Modules/SymmetricPower/Affine.lean`
      (+16/−9: the private `symmetricToOpenSemilinear` becomes the public `tildeToOpenₛₗ` with
      `tildeToOpenₛₗ_apply`, moved here from the old split 13); and the closing paragraph of the
      module docstring of `Morphisms/Projective.lean` (+5), which points to this file.
    - Declarations in `Morphisms/ProjectiveOver.lean`: `tildeToOpenTopInvₛₗ` (with `_apply`),
      `symmetricAlgebraTildeGradedHom`, `symmetricAlgebraTildeGradedHomInv`,
      `projSymmetricAlgebraTildeIso`, `projSymmetricAlgebraTildeIso_hom_projToSpec`, and
      the instance `AlgebraicGeometry.Scheme.IsProjectiveOver.isProjective`,
      `exists_isClosedImmersion_proj_symmetricAlgebra`,
      `AlgebraicGeometry.Scheme.isProjectiveOver_of_isProjective`,
      `isProjective_toSpecCoeff`, `isProjective_relativeProjToBase_pullback`, the instances
      `isProjective_pullback_snd`, `isProjective_pullback_fst`, `respectsIso_isProjective` and
      `isStableUnderBaseChange_isProjective`, and
      `AlgebraicGeometry.Scheme.isProjectiveOver_iff_isProjective`.
    - Subject: `feat(AlgebraicGeometry/Morphisms): projective schemes over a ring are the projective morphisms to its spectrum, and projective morphisms are stable under base change`

## What is proved and what remains

Proved, with no stubs:
- Tensor powers of line bundles, with their classes, exponent laws and pullbacks.
- Global generation of `𝒪_X`, and of pullbacks, tensor products and tensor powers of globally
  generated line bundles.
- Nonvanishing loci: `X_{s ⊗ t} = X_s ∩ X_t`, affineness on affine opens, the fibre criterion,
  and preimages along every morphism.
- Ampleness: stable under pullback along affine morphisms (closed immersions included), so it is
  invariant under isomorphism. It is also stable under positive powers (in both directions) and
  under multiplication by globally generated line bundles.
- `𝒪(1)`, and every `𝒪(n)` with `n > 0`, is ample on a quasi-compact `Proj` whose degree-one
  standard opens cover it.
- Relatively very ample line bundles: `𝒪(1)` is relatively very ample on `Proj_S A`. Relative
  very ampleness is stable under isomorphism and under pullback along immersions, and it forces
  separatedness. For a quasi-compact morphism, a relatively very ample line bundle is relatively
  ample.
- `𝒪(1)` pulls back to an ample line bundle along every immersion from a quasi-compact scheme
  into a `Proj` whose degree-one standard opens cover it.
- Every line bundle on a quasi-affine scheme is ample and globally generated. Products of ample
  classes are ample.
- Relative ampleness in the Stacks sense. It is equivalent for `a` and `aⁿ`, `n > 0`, and stable
  under products and under multiplication by globally generated bundles. The trivial class is
  relatively ample exactly for quasi-affine morphisms, and then every class is; in particular
  every class is relatively ample for an affine morphism. Over a quasi-affine base it is
  ampleness; over a separated base, ampleness implies it for quasi-compact morphisms. It is
  preserved by pullback along affine morphisms of the source, closed immersions included, so it
  is invariant under isomorphisms of the source over the base. It is preserved by composition
  with quasi-affine morphisms, it is local on the base, and it is stable under arbitrary base
  change. A relatively ample class is ample on every fibre, and a morphism carrying one is
  separated. Relative ampleness for `f ≫ g` gives it for `f` when `g` is separated.
- Exterior products: over a separated base, `pr₁* a · pr₂* b` is ample on `X ×_S Y` for ample `a`
  and `b`; for relatively ample `a` and `b` it is relatively ample for `X ×_S Y ⟶ S`.
- A scheme with an ample line bundle is separated, by a new criterion: a scheme with an affine
  open cover whose pairwise intersections are affine, with functions generated by those on the
  two pieces, is separated. On a quasi-compact scheme, ampleness can be checked on a cover by
  basic opens of global functions.
- `𝒪(1)` is relatively ample on a quasi-compact relative `Proj` generated in degree one.
- Intersection numbers of powers: `(aⁿ · C) = n (a · C)` on a regular proper integral curve.
- Tensor products and tensor powers of sections of line bundles, and both halves of Stacks 01PW
  for line bundles: on a quasi-compact quasi-separated open, sections vanishing on `X_s` are
  killed by powers of `s`, and sections over `X_s` extend after multiplication by a power of `s`.
- Composition of relative ampleness (Stacks 0C4K): if `a` is relatively ample for `f : X ⟶ Y`
  and `b` is ample on `Y`, then `a · f* bⁿ` is ample for all large `n`; over a quasi-compact
  base, relative ampleness for `f` and `g` gives it for `f ≫ g` after such a twist.
- Ample line bundles have a basis of affine nonvanishing loci; ampleness pulls back along
  immersions from quasi-compact schemes, and relative ampleness along quasi-compact immersions of
  the source.
- Projective morphisms are closed under precomposition with closed immersions and are
  **proper**. Closed immersions, in particular isomorphisms, are projective. They carry a line bundle, the pullback of `𝒪(1)`, that is relatively very ample and
  relatively ample.
- `Sym F` is generated in degree one for every quasicoherent `F`; over an affine open its sections
  are the symmetric algebra of the sections of `F`, and over an affine base `ℙ(F)` is
  `Proj (Sym Γ(F, S))`, which is therefore projective over `S` for `F` of finite type. A scheme
  projective over a ring in the sense of `main`'s `Scheme.IsProjectiveOver` is projective over its
  spectrum, and the sheaf associated with a finite module is of finite type. For `F` of finite type, the
  projective bundle `ℙ(F) = Proj_S(Sym F) ⟶ S` is projective (hence proper), and its `𝒪(1)` is
  relatively very ample and relatively ample. A closed immersion into `ℙ(F)` over `S` is
  therefore projective: this is the Stacks definition of projective morphisms.
- The Rees algebra of an ideal sheaf is generated in degree one. The blowup along an ideal sheaf
  of finite type is projective, and its `𝒪(1)` is relatively ample.
- A scheme over `Spec R` is projective over `R` in the sense of `main`'s `Scheme.IsProjectiveOver`
  (a closed subscheme over `R` of `Proj (Sym_R M)`, `M` finite) if and only if `X ⟶ Spec R` is
  projective. A graded algebra generated in degree one by a finite degree-one part has its `Proj`
  embedded as a closed subscheme of `Proj (Sym_R M)`, and it is projective over its coefficient
  ring.
- For every `g : S' ⟶ S` and every graded quasicoherent algebra `A` on `S` generated in degree
  one, of finite type and with finite degree-zero part, `g^* A` has the same three properties, so
  `Proj_{S'}(g^* A) ⟶ S'` is projective.
- The relative `Proj` commutes with base change: `Proj_{S'}(g^* A) ≅ Proj_S(A) ×_S S'` over `S'`
  for every graded quasicoherent algebra `A` on `S` and every `g : S' ⟶ S` (split 18). Hence
  **projective morphisms are stable under arbitrary base change** (split 21,
  `isProjective_pullback_snd`, `isProjective_pullback_fst`, and the `MorphismProperty` instances
  `respectsIso_isProjective` and `isStableUnderBaseChange_isProjective`).
- The relative `Proj` is functorial in morphisms of graded algebras satisfying the irrelevant-ideal
  condition, compatibly with the charts (split 19); a morphism surjective on affine sections in
  positive degrees, in particular one into an algebra generated in degree one that is surjective
  in degree one, induces a closed immersion. Hence `Proj_X(A)` is a closed subscheme of
  `ℙ(A₁)` for `A` generated in degree one, and an epimorphism `F ⟶ E` of quasicoherent sheaves
  gives a closed immersion `ℙ(E) ⟶ ℙ(F)` (split 20).

Remains for the target:
- Stability of projectivity under composition (Stacks 01WD-type, over a quasi-compact base). Base
  change is done (split 21), and so is the ampleness input (Stacks 0C4K, split 10:
  `IsProjective.exists_isRelativelyAmple_comp`). The planned route to a closed immersion of `X`
  into a relative `Proj` over `Z`, for projective `f : X ⟶ Y` (through `Proj_Y(B)`) and
  `g : Y ⟶ Z` (through `Proj_Z(A)`), each step a closed immersion over `Z`:
  `X ↪ Proj_Y(B) ↪ ℙ(B₁)` (**done**, split 20) `≅ ℙ(B₁ ⊗ 𝒪(n))` `↪ ℙ(g^* G)` (**done once the
  surjection exists**, split 20) `≅ ℙ_Z(G) ×_Z Y` `↪ ℙ_Z(G) ×_Z ℙ_Z(A₁)` `↪ ℙ_Z(G ⊗ A₁)`.
  What is missing:
  1. twist invariance `ℙ(E ⊗ L) ≅ ℙ(E)` over `Y` for an invertible `L`, compatible with `𝒪(1)`;
  2. relative global generation: for `E` of finite type on `Y` and `n` large, a quasicoherent `G`
     of finite type on `Z` with an epimorphism `g^* G ⟶ E ⊗ 𝒪(n)` (needs `g_*` of quasicoherent
     sheaves and finite-type approximation on the quasi-compact `Z`);
  3. `g^* (Sym G) ≅ Sym (g^* G)`, so that split 18's `relativeProjPullbackIso` identifies
     `ℙ_Y(g^* G)` with `ℙ_Z(G) ×_Z Y`;
  4. the Segre embedding `ℙ_Z(G) ×_Z ℙ_Z(H) ↪ ℙ_Z(G ⊗ H)`.
  The alternative route through Stacks 01VU/01VS (the relative `Proj` of the section algebra
  `⊕ₙ f_* Lⁿ`) needs `f_*` and a relative Veronese step and is not easier.
Not needed from this target (checked in the fifteenth session):
- Cartier divisors and degree on components. `main` already has the basic API: Cartier divisors,
  their sheaves `𝒪(D)` and the map to line-bundle classes (`CartierDivisor/Sheaf.lean`,
  `Scheme.CartierDivisor.toLineBundleClassHom` in `CartierDivisor/Picard.lean`), the Euler-characteristic
  degree (`LineBundle/Degree.lean`), and the degree on a component as an intersection number
  (`LineBundleClass.intersectionNumber`, `IntersectionNumber/Basic.lean`, used for components in
  `Curves/StableMaps/Degree.lean`), with its additivity and, from this branch, its value on
  powers. The relation to ampleness, the ampleness criterion by positive degree on components,
  is a separate Layer 2 item.
