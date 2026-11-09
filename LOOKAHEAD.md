<!--tauceti-lookahead:v1 {"area":"StableReduction","slug":"relative-ampleness","main":"34069c9ec88c7680bc8d3cbe55907d3354ac9102","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"refactor(AlgebraicGeometry/RelativeProj): name the generated-in-degree-one condition"},{"n":2,"after":[],"title":"feat(AlgebraicGeometry/LineBundle): tensor powers of line bundles"},{"n":3,"after":[2],"title":"feat(AlgebraicGeometry/LineBundle): global generation of trivial bundles, pullbacks, tensor products and tensor powers"},{"n":4,"after":[2,3],"title":"feat(AlgebraicGeometry/LineBundle): nonvanishing loci pull back; ampleness under affine pullback, powers and globally generated twists"},{"n":5,"after":[4],"title":"feat(AlgebraicGeometry/LineBundle): schemes with an ample line bundle are separated; ampleness on basic-open covers and of exterior products"},{"n":6,"after":[4],"title":"feat(AlgebraicGeometry/ProjectiveSpectrum): O(1) pulls back to an ample line bundle along immersions from quasi-compact schemes"},{"n":7,"after":[1],"title":"feat(AlgebraicGeometry/RelativeProj): the symmetric algebra is generated in degree one and its relative Proj is proper"},{"n":8,"after":[2,4,5],"title":"feat(AlgebraicGeometry/LineBundle): sections over nonvanishing loci extend; ampleness pulls back along immersions"},{"n":9,"after":[2,3,4,5,8],"title":"feat(AlgebraicGeometry/LineBundle): relatively ample line bundles"},{"n":10,"after":[2,3,4,5,8,9],"title":"feat(AlgebraicGeometry/LineBundle): relative ampleness composes after twisting by a large power"},{"n":11,"after":[],"title":"feat(AlgebraicGeometry/IntersectionNumber): intersection numbers of powers"},{"n":12,"after":[],"title":"feat(AlgebraicGeometry/Modules): the sheaf associated with a finite module is of finite type"},{"n":13,"after":[],"title":"feat(RingTheory/GradedAlgebra): finiteness and generation of the degree-one part of a graded algebra"},{"n":14,"after":[1,2,3,4,5,6,7,8,9,10,11,12],"title":"feat(AlgebraicGeometry/Morphisms): relatively very ample line bundles, projective morphisms, projective bundles and blowups"},{"n":15,"after":[],"title":"feat(AlgebraicGeometry/RelativeGluing): recognise the glued scheme of a relative gluing datum"},{"n":16,"after":[],"title":"feat(AlgebraicGeometry/Modules): pull back graded sections, and Proj of them as a base change over affine opens"},{"n":17,"after":[1,16],"title":"feat(AlgebraicGeometry/RelativeProj): charts of the base change of a relative Proj over small affine opens, and the pulled-back algebra stays of finite type and generated in degree one"},{"n":18,"after":[1,15,16,17],"title":"feat(AlgebraicGeometry/RelativeProj): the relative Proj commutes with base change"},{"n":19,"after":[],"title":"feat(AlgebraicGeometry/RelativeProj): isomorphisms of relative Proj"},{"n":20,"after":[1,7,13,19],"title":"feat(AlgebraicGeometry/RelativeProj): closed immersions of relative Proj from maps surjective in degree one"},{"n":21,"after":[],"title":"feat(AlgebraicGeometry/Modules): pullback of the graded symmetric algebra"},{"n":22,"after":[1,7,13,15,16,17,18,19,20,21],"title":"feat(AlgebraicGeometry/RelativeProj): base change of projective bundles"},{"n":23,"after":[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22],"title":"feat(AlgebraicGeometry/Morphisms): projective schemes over a ring are the projective morphisms to its spectrum, and projective morphisms are stable under base change"},{"n":24,"after":[2,3,4,5,8,9],"title":"feat(AlgebraicGeometry/LineBundle): global generation after sufficiently positive ample twisting"},{"n":25,"after":[2,7,13,19,20,22],"title":"feat(AlgebraicGeometry/RelativeProj): projective bundles are invariant under invertible twists"},{"n":26,"after":[2,3,5,8,9,24],"title":"feat(AlgebraicGeometry/Modules): relative generation after ample twisting"},{"n":27,"after":[7,18,19,20,21,22],"title":"feat(AlgebraicGeometry/RelativeProj): the relative Segre closed immersion"},{"n":28,"after":[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27],"title":"feat(AlgebraicGeometry/Morphisms): composition of projective morphisms"}]}-->
# Lookahead: relative-ampleness (StableReduction, Layer 2)

Status: **partial**. Resumed tip `590673324fe4` and merged `main` at `34069c9ec88c7680bc8d3cbe55907d3354ac9102`.
The merge brought in 876 `main` commits without conflicts. Among them, supplier PR #29201
(`relative-proj-twisting-sheaf`: the graded map `A → p_* 𝒪(n)` and quasi-coherence of the
relative twisting sheaves) landed as `5102d79ffb5`. The branch consumes none of its new
declarations. The other `main` changes in neighbouring modules were checked for duplicates:
`main`'s new `Scheme.Modules.isFiniteType_of_finite_sections` (in
`Modules/Quasicoherent/FiniteType.lean`) concerns sections over affine opens, not the instance
`isFiniteType_tilde` of split 12, so split 12 is kept. No other branch declaration was superseded.
The target is StableReduction/README.md, Layer 2, the bullet beginning “Extend Tau Ceti's
invertible-sheaf API with tensor powers”. StableReduction/Suggested.lean has no pinned signature
for this target. No pull request or issue is opened by this branch.

## Supplier contracts and stubs

**No stubs are needed by the mathematics proved here.** The consumed portion of
`relative-proj-twisting-sheaf` has landed on `main`. There is no stub file and no proof uses a
placeholder. SchemeAndStackFoundations/Suggested.lean has no signature for this supplier:
searching for `twist`, `relativeProj` and `GeneratedInDegreeOne` finds only unrelated Frobenius
statements. The definitive contract is SchemeAndStackFoundations/README.md §0.3.

The original stubs were copied from supplier PR #22384; they are now replaced by these landed
forms, in `RelativeProj/TwistingSheaf.lean`:

- `CategoryTheory.CommMon.relativeProjTwistingSheaf (n : ℤ) : A.relativeProj.Modules`.
- `CategoryTheory.CommMon.isInvertible_relativeProjTwistingSheaf`, for every integer twist,
  assuming generation by degree one over degree zero. Split 1 names this exact condition
  `CategoryTheory.CommMon.IsGeneratedInDegreeOne`. It does not strengthen it to generation over
  the structure sheaf.

PR #29201, now merged on `main` as `5102d79ffb5`, adds quasi-coherence of the relative twisting
sheaves and the maps from the homogeneous components to their direct images, with the chart
formula and multiplicativity. None of those additional declarations is consumed here, so none
is stubbed. The multiplication and invertibility results already on `main` are used directly.
There is therefore no new stub signature, no discrepancy with Suggested.lean to reconcile, and
`suppliers` in the header is empty.

## Progress in the previous rounds (2026-11-08)

The two latest short rounds only merged `main` (the latest one at `34069c9ec88c`) and
re-verified the branch; they add no new mathematics. The progress below is from the round before them.

- Proved `InvertibleSheaf.exists_isGloballyGenerated_tensorPow_of_isAmple`:
  for any line bundle `K` and ample `L`, there exists `N` such that `L^n ⊗ K` is globally
  generated for **every** `n ≥ N`, over arbitrary schemes. No Noetherian hypothesis is used.
- Proved `LineBundleClass.IsRelativelyAmple.exists_locally_isGloballyGenerated_tensorPow`:
  over a quasi-compact base a single bound makes these twists globally generated over the
  preimage of an affine neighbourhood of every base point.
- Extracted the uniform-exponent affine-cover lemma
  `IsAmple.exists_pos_forall_exists_isAffineOpen_nonvanishingLocus` in `LineBundle/Ample.lean`
  and reused it in the separatedness proof. The generation proof handles every residue class
  of the exponent, rather than only sufficiently divisible powers.
- Reconciled the three merge conflicts. The branch now consumes `main`'s
  `Proj.twistingSheaf.nonvanishingLocus_toTwistingSheaf`, retaining its additional immersion
  pullback theorem. It retains the independent finite-degree-one and subsemiring-generation
  results alongside `main`'s degree-one algebra API.
- Removed the newly duplicated `Scheme.Hom.δ_app_pullbackSections_μ` and the whole now-redundant
  `Modules/Pullback/Monoidal/Sections.lean` module. The unused special-case
  `Proj.isAmple_twistingSheaf_one` also disappears in favour of `main`'s general positive-twist theorem.
  The duplicated relative-Proj functoriality implementation is also removed, and only the
  additional isomorphism API is placed in `main`'s `RelativeProj/Map.lean`.
  The duplicated affine-chart isomorphism instance is removed from `RelativeProj/Basic.lean`
  and the proof uses the declaration now on `main` in `RelativeProj/Affine.lean`.
  Graded pullback sections use `main`'s
  tensor equation. The axiom audit also detected a second copy of the graded-section pullback
  API: it has been removed in favour of `main`'s `GradedAlgebra/BaseChange.lean`. Only the
  generalization to arbitrary smaller affine opens remains in `PullbackSections.lean`.
- Factored denominator clearing in `Modules/GradedAlgebra/Localization.lean` into a private
  helper, fixing the elaboration timeout under the current pin without changing any limit.

## Review audit

Placement: the new projective-morphism modules are `Morphisms/Projective/Basic.lean` and
`Morphisms/Projective/Over.lean`; their common subject has its own directory. Importers are
updated, and neither obsolete flat path survives.

Reuse: searched Mathlib and Tau Ceti before the new declarations; no existing positive-twisting
line-bundle generation theorem was found. Removed the newly landed duplicates described
above. Proof quality: the uniform affine-cover construction is shared with separatedness;
local extension and finite-cover arguments reuse the existing APIs. Generality: the exported
absolute theorem has no Noetherian, projectivity, base, or finiteness hypothesis beyond
ampleness, and the relative theorem states its quasi-compact-base hypothesis. Correctness:
the conclusion is uniform for all large exponents, using finitely many residue classes, and
the relative conclusion promises generation over base neighbourhoods, not a finite-type
relative evaluation presentation. Documentation and scope: files describe their mathematical
content, cite Stacks/Hartshorne, and advance the positive-twisting input to projective embeddings.

## Verification

All required commands passed again after merging `main` at `34069c9ec88c`, on 2026-11-08:
`lake exe cache get`, `lake build` (70,906 jobs), and `/opt/round/lookahead-check`.
The combined import and axiom audit reports `lookahead-check: ok`; no stubs or extra axioms remain.

## Split plan

Each split is opened only after the listed prerequisites have merged. These are future PRs,
not a stack of simultaneous dependent PRs. Splits 1–24 contain the proved material; 25–28 are
explicitly **unproved planned work**. Only split 28 completes the target and it waits for every
other split. Each future PR uses `Roadmap: StableReduction`, except the supplier refactors 1
and 7 whose primary attribution is `Roadmap: SchemeAndStackFoundations`.

1. **Name the generated-in-degree-one condition** (after: none). This is a refactor that touches
   only `main` code.
   - File: `TauCeti/AlgebraicGeometry/RelativeProj/TwistingSheaf.lean` (+48/−4).
   - Declarations: `CategoryTheory.CommMon.IsGeneratedInDegreeOne`, `CommMon.isGeneratedInDegreeOne_iff`,
     `CommMon.isGeneratedInDegreeOne_of_adjoin_eq_top` (generation over `Γ(X, U)` suffices).
     The landed invertibility theorem retains its inline hypothesis.
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
   - `LineBundle/Ample.lean` (the rest of its diff, including the new uniform-exponent lemma; it now also imports
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
   - File: `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/Ample.lean` (existing
     on current `main`; about 70 added lines).
   - Declarations: `Proj.exists_mem_basicOpen_le`, `Proj.isAmple_pullback_twistingSheaf_one`
     (including its standard-open basis lemma). The nonvanishing-locus calculation and ampleness
     of positive twists now come from `main`; no obsolete theorem is retained.
   - Subject: `feat(AlgebraicGeometry/ProjectiveSpectrum): O(1) pulls back to an ample line bundle along immersions from quasi-compact schemes`
7. **The symmetric algebra is generated in degree one and its relative `Proj` is proper** (after: 1).
   - Files: `main`'s `Modules/Quasicoherent/GradedAlgebra/SymmetricAlgebra/Adjunction.lean`
     (+209; it now imports `Modules/SymmetricPower/Sections.lean` and
     `LinearAlgebra/SymmetricAlgebra/Homogeneous.lean`); `main`'s `RelativeProj/Basic.lean` (+12);
     `RelativeProj/SymmetricAlgebra.lean` (185 lines, new). About 400 lines.
   - Declarations: in `Adjunction.lean`, `gradedSymmetricAlgebraSectionsEquiv` with
     `gradedSymmetricAlgebraSectionsEquiv_ι`, `_mem`, `_symm_mem`, and
     `adjoin_gradedSectionsGrading_one_gradedSymmetricAlgebra` (with private helper lemmas); in
     `RelativeProj/Basic.lean` no duplicate of the affine-chart instance is added (it now lives
    in `main`'s `RelativeProj/Affine.lean`); in
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
      - `TauCeti/AlgebraicGeometry/Morphisms/Projective/Basic.lean` (309 lines in this split, new; imports
        `LineBundle/RelativelyAmple/Comp.lean`);
      - `TauCeti/AlgebraicGeometry/Blowup/Projective.lean` (130 lines, new);
      - `main`'s `Blowup/IdealSheaf.lean` (+24/−12: the two inline bullets of
        `isProper_blowupToBase` become `finiteType_sections_reesAlgebra` and
        `finite_sections_reesAlgebra_zero`).
    - Declarations in `Morphisms/Projective/Basic.lean`: `CommMon.relativeProjTwistingSheafOne`;
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
    - File: `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/GradedAlgebra/PullbackSections.lean`
      (385 lines, new), importing `main`'s `GradedAlgebra/BaseChange.lean`.
    - Declarations in namespace
      `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra`: `pullbackGradedSectionsLE`
      (with `_of`, `_algebraMap`), `pullbackGradedSectionsLEGradedHom` (with `_apply`),
      `irrelevant_le_map_pullbackGradedSectionsLEGradedHom` and
      `isPullback_proj_map_pullbackGradedSectionsLEGradedHom`; then
      `restrictGradedSections_comp_pullbackGradedSectionsLE`,
      `pullbackGradedSectionsLE_comp_restrictGradedSections`,
      `span_range_pullbackGradedSectionsLE`, `adjoin_gradedSectionsGrading_pullback_eq_top`,
      `finiteType_pullback_sections` and `finite_pullback_sections_zero`. The file was 520
      lines, within the intended size for a single topic.
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
19. **Isomorphisms of relative `Proj`s** (after: none).
    - File: `TauCeti/AlgebraicGeometry/RelativeProj/Map.lean` (existing on `main`, about 80 added
      lines). The former `RelativeProj/Functor.lean` is removed; it is not a forwarding module.
    - Declarations: `CommMon.IrrelevantLeMap` (the exact inline condition consumed by `main`'s
      map), `gradedSectionsGrading_subset_range_gradedSectionsGradedHom`,
      `irrelevantLeMap_of_surjective`, `irrelevantLeMap_of_isIso`, and
      `relativeProjIso` with its `_hom` and `_inv` equations.
    - Graded section maps, relative-Proj maps, functoriality, cartesian charts, and the
      closed-immersion theorem are all reused from `main`; none is duplicated.
    - Subject: `feat(AlgebraicGeometry/RelativeProj): isomorphisms of relative Proj`

20. **Closed immersions of relative `Proj`s from maps surjective in degree one** (after: 1, 7, 13,
    19). It imports split 19's `Map.lean`, split 7's `RelativeProj/SymmetricAlgebra.lean`
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
21. **Pullback of the graded symmetric algebra** (after: none). It needs only `main`.
    - File: `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/GradedAlgebra/SymmetricAlgebra/GradedPullback.lean`
      (361 lines, new; imports `main`'s `GradedAlgebra/Pullback.lean`,
      `GradedAlgebra/SymmetricAlgebra/Adjunction.lean` and `GradedAlgebra/SymmetricAlgebra/Pullback.lean`).
    - Declarations: `GradedQuasicoherentAlgebra.toQuasicoherentAlgebraPullbackIso` (the algebra
      isomorphism `⨁ₙ f^* Aₙ ≅ f^* (⨁ₙ Aₙ)`) with `ιTotal_toQuasicoherentAlgebraPullbackIso_hom`;
      `GradedQuasicoherentAlgebra.isIso_of_isIso_toQuasicoherentAlgebra_map` (the direct-sum functor
      reflects isomorphisms); `pullbackGradedSymmetricAlgebraIso` (`f^* (Sym F) ≅ Sym (f^* F)` as
      graded quasicoherent algebras) with `degreeOne_map_pullbackGradedSymmetricAlgebraIso_inv`.
    - Roadmap line: `Roadmap: StableReduction` (input to stability of projective morphisms under
      composition, Layer 2).
    - Subject: `feat(AlgebraicGeometry/Modules): pullback of the graded symmetric algebra`

22. **Base change of projective bundles** (after: 1, 7, 13, 15, 16, 17, 18, 19, 20, 21). It edits
    split 19's `Map.lean` and imports split 18's `RelativeProj/BaseChange.lean` (which needs 1,
    15, 16, 17), split 20's `RelativeProj/ClosedImmersion.lean` (which needs 1, 7, 13, 19) and
    split 21's `GradedPullback.lean`.
    - Files: `TauCeti/AlgebraicGeometry/RelativeProj/SymmetricAlgebra/Pullback.lean` (143 lines,
      new) and `TauCeti/AlgebraicGeometry/RelativeProj/Map.lean` (+40: the declarations below
      and one line of its module docstring; if split 19 has not merged when this is opened, wait
      for it).
    - Declarations: in `Map.lean`, `CategoryTheory.CommMon.irrelevantLeMap_of_isIso`,
      `CommMon.relativeProjIso`, `CommMon.relativeProjIso_hom`, `CommMon.relativeProjIso_inv`; in
      `TauCeti.AlgebraicGeometry`: `relativeProjGradedSymmetricAlgebraPullbackIso`,
      `relativeProjGradedSymmetricAlgebraPullbackIso_hom_snd` (with `_assoc`),
      `isPullback_relativeProjGradedSymmetricAlgebraPullback`,
      `exists_isClosedImmersion_relativeProjPullback_of_epi` and
      `GradedQuasicoherentAlgebra.exists_isClosedImmersion_relativeProjPullback_of_epi`.
    - Roadmap line: `Roadmap: StableReduction` (Layer 2, projective morphisms: input to their
      stability under composition).
    - Subject: `feat(AlgebraicGeometry/RelativeProj): base change of projective bundles`

23. **Projective schemes over a ring are the projective morphisms to its spectrum; projective
    morphisms are stable under base change** (after: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
    15, 16, 17, 18, 19, 20, 21, 22). This proves base change and the affine comparison;
    completion of the target is reserved for split 28.
    - Files: `TauCeti/AlgebraicGeometry/Morphisms/Projective/Over.lean` (362 lines, new; imports
      split 18's `RelativeProj/BaseChange.lean`, `Morphisms/Projective/Basic.lean`,
      `ProjectiveSpectrum/ProjectiveOver.lean`, `ProjectiveSpectrum/ClosedImmersion.lean` and
      `RingTheory/GradedAlgebra/DegreeOne.lean`); `main`'s `Modules/SymmetricPower/Affine.lean`
      (+16/−9: the private `symmetricToOpenSemilinear` becomes the public `tildeToOpenₛₗ` with
      `tildeToOpenₛₗ_apply`, moved here from the old split 13); and the closing paragraph of the
      module docstring of `Morphisms/Projective/Basic.lean` (+5), which points to this file.
    - Declarations in `Morphisms/Projective/Over.lean`: `tildeToOpenTopInvₛₗ` (with `_apply`),
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

24. **Global generation after ample twisting** (after: 2, 3, 4, 5, 8, 9; proved).
    - Files: `LineBundle/GlobalGeneration/Ample.lean` and
      `LineBundle/RelativelyAmple/GlobalGeneration.lean` (about 195 lines combined).
      The common-exponent cover lemma in `LineBundle/Ample.lean` is supplied by split 5.
    - Declarations: `InvertibleSheaf.exists_isGloballyGenerated_tensorPow_of_isAmple` and
      `LineBundleClass.IsRelativelyAmple.exists_locally_isGloballyGenerated_tensorPow`.
      The affine-cover generation argument is private to the absolute proof.
    - Subject: `feat(AlgebraicGeometry/LineBundle): global generation after sufficiently positive ample twisting`

25. **Twist invariance of projective bundles** (after: 2, 7, 13, 19, 20, 22; unproved).
    - Planned files: symmetric-power tensor comparison in
      `Modules/SymmetricPower/TensorProduct.lean`, graded twisting in
      `Modules/Quasicoherent/GradedAlgebra/Twist.lean`, and
      `RelativeProj/SymmetricAlgebra/Twist.lean`, split into 200–600-line prerequisite PRs
      if their eventual implementation requires it.
    - Planned declarations: the natural symmetric-power comparison for an invertible factor,
      and `ℙ(E ⊗ L) ≅ ℙ(E)` over the base, with the tautological-sheaf comparison.
    - Subject: `feat(AlgebraicGeometry/RelativeProj): projective bundles are invariant under invertible twists`

26. **Finite-type relative generation** (after: 2, 3, 5, 8, 9, 24; unproved).
    - Planned files: `Modules/GlobalGeneration/Ample.lean` and
      `LineBundle/RelativelyAmple/Generation.lean`.
    - Planned declarations: positive-twisting generation for arbitrary finite-type
      quasi-coherent modules, and the epimorphism `g^* G ⟶ E ⊗ L^n` for a finite-type
      quasi-coherent `G` on a quasi-compact base. Split 24 handles only invertible `E` and
      local generation; this split must prove the actual presentation.
    - Subject: `feat(AlgebraicGeometry/Modules): relative generation after ample twisting`

27. **Relative Segre embedding** (after: 7, 18, 19, 20, 21, 22; unproved).
    - Planned file: `RelativeProj/SymmetricAlgebra/Segre.lean` and its necessary graded-algebra
      prerequisites, in 200–600-line PR units.
    - Planned declaration: the closed immersion `ℙ(G) ×_Z ℙ(H) ↪ ℙ(G ⊗ H)` over `Z`.
    - Subject: `feat(AlgebraicGeometry/RelativeProj): the relative Segre closed immersion`

28. **Composition of projective morphisms; target completion** (after: **every split 1–27**;
    unproved, final).
    - Planned file: `Morphisms/Projective/Comp.lean`, beside `Projective/Basic.lean` and
      `Projective/Over.lean`. The latter two are already placed in the directory by splits
      14 and 23, with every importer updated and no forwarding modules.
    - Planned exports: `IsProjective.comp` over a quasi-compact base and the corresponding
      projective-composition API. Its proof combines twist invariance, finite-type relative
      generation, base change, and the Segre embedding. It imports the preceding positivity,
      intersection-power, and projective API, and is the only split claiming completion.
    - Subject: `feat(AlgebraicGeometry/Morphisms): composition of projective morphisms`

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
  **projective morphisms are stable under arbitrary base change** (split 23,
  `isProjective_pullback_snd`, `isProjective_pullback_fst`, and the `MorphismProperty` instances
  `respectsIso_isProjective` and `isStableUnderBaseChange_isProjective`).
- The relative `Proj` is functorial in morphisms of graded algebras satisfying the irrelevant-ideal
  condition, compatibly with the charts (split 19); a morphism surjective on affine sections in
  positive degrees, in particular one into an algebra generated in degree one that is surjective
  in degree one, induces a closed immersion. Hence `Proj_X(A)` is a closed subscheme of
  `ℙ(A₁)` for `A` generated in degree one, and an epimorphism `F ⟶ E` of quasicoherent sheaves
  gives a closed immersion `ℙ(E) ⟶ ℙ(F)` (split 20).
- The graded symmetric algebra commutes with pullback: `f^* (Sym F) ≅ Sym (f^* F)` as graded
  quasicoherent algebras, and the direct-sum algebra commutes with pullback (split 21).
- Isomorphisms of graded algebras induce isomorphisms of relative `Proj`s over the base, and the
  projective bundle commutes with base change: `ℙ_Y(g^* F) ≅ ℙ_X(F) ×_X Y` over `Y`. An
  epimorphism `g^* F ⟶ E`, or `g^* F ⟶ B₁` for `B` generated in degree one, gives a closed
  immersion of `ℙ_Y(E)`, resp. `Proj_Y(B)`, into `ℙ_X(F) ×_X Y` over `Y` (split 22).

Newly proved (split 24): every invertible sheaf becomes globally generated after all sufficiently
large ample twists; for relatively ample twists over a quasi-compact base a uniform exponent
works locally on the base.

Remains for the target:
- Stability of projectivity under composition (Stacks 01WD-type, over a quasi-compact base). Base
  change is done (split 23), and so is the ampleness input (Stacks 0C4K, split 10:
  `IsProjective.exists_isRelativelyAmple_comp`). The planned route to a closed immersion of `X`
  into a relative `Proj` over `Z`, for projective `f : X ⟶ Y` (through `Proj_Y(B)`) and
  `g : Y ⟶ Z` (through `Proj_Z(A)`), each step a closed immersion over `Z`:
  `X ↪ Proj_Y(B) ↪ ℙ(B₁)` (**done**, split 20) `≅ ℙ(B₁ ⊗ 𝒪(n))` `↪ ℙ(g^* G)` (**done once the
  surjection exists**, split 20) `≅ ℙ_Z(G) ×_Z Y` `↪ ℙ_Z(G) ×_Z ℙ_Z(A₁)` `↪ ℙ_Z(G ⊗ A₁)`.
  What is missing:
  1. twist invariance `ℙ(E ⊗ L) ≅ ℙ(E)` over `Y` for an invertible `L`, compatible with `𝒪(1)`;
  2. relative global generation: for `E` of finite type on `Y` and `n` large, a quasicoherent `G`
     of finite type on `Z` with an epimorphism `g^* G ⟶ E ⊗ 𝒪(n)` (the rank-one local generation
     case is done in split 24; arbitrary finite-type modules and
     the actual epimorphism remain). Current `main` already has qcqs quasi-coherent pushforward in
     `Modules/Quasicoherent/Pushforward/QuasiSeparated.lean`, finite-type submodules in
     `Modules/Quasicoherent/FiniteType.lean`, and finite-type extension in
     `Modules/Quasicoherent/Extension/FiniteType.lean`; reuse these instead of rebuilding them;
  3. ~~`ℙ_Y(g^* G) ≅ ℙ_Z(G) ×_Z Y`~~ **done** (split 22,
     `relativeProjGradedSymmetricAlgebraPullbackIso`; with
     `GradedQuasicoherentAlgebra.exists_isClosedImmersion_relativeProjPullback_of_epi`, an
     epimorphism `g^* G ⟶ B₁` already gives the closed immersion `Proj_Y(B) ↪ ℙ_Z(G) ×_Z Y` over
     `Y` for `B` generated in degree one, so once items 1 and 2 supply such an epimorphism for a
     twist of `B`, only the Segre step 4 is left);
  4. the Segre embedding `ℙ_Z(G) ×_Z ℙ_Z(H) ↪ ℙ_Z(G ⊗ H)`.
  The alternative route through Stacks 01VU/01VS (the relative `Proj` of the section algebra
  `⊕ₙ f_* Lⁿ`) still needs a relative Veronese construction and a reconstruction theorem;
  quasi-coherence of the needed qcqs pushforward itself is already on `main`.
Not needed from this target (checked in the fifteenth session):
- Cartier divisors and degree on components. `main` already has the basic API: Cartier divisors,
  their sheaves `𝒪(D)` and the map to line-bundle classes (`CartierDivisor/Sheaf.lean`,
  `Scheme.CartierDivisor.toLineBundleClassHom` in `CartierDivisor/Picard.lean`), the Euler-characteristic
  degree (`LineBundle/Degree.lean`), and the degree on a component as an intersection number
  (`LineBundleClass.intersectionNumber`, `IntersectionNumber/Basic.lean`, used for components in
  `Curves/StableMaps/Degree.lean`), with its additivity and, from this branch, its value on
  powers. The relation to ampleness, the ampleness criterion by positive degree on components,
  is a separate Layer 2 item.

## Split subjects at a glance

The dependency lists here are authoritative; the mathematical descriptions and file assignments
are above. Splits 25–28 have no proof files on this partial branch yet.

1. After none: `refactor(AlgebraicGeometry/RelativeProj): name the generated-in-degree-one condition`.
2. After none: `feat(AlgebraicGeometry/LineBundle): tensor powers of line bundles`.
3. After 2: `feat(AlgebraicGeometry/LineBundle): global generation of trivial bundles, pullbacks, tensor products and tensor powers`.
4. After 2, 3: `feat(AlgebraicGeometry/LineBundle): nonvanishing loci pull back; ampleness under affine pullback, powers and globally generated twists`.
5. After 4: `feat(AlgebraicGeometry/LineBundle): schemes with an ample line bundle are separated; ampleness on basic-open covers and of exterior products`.
6. After 4: `feat(AlgebraicGeometry/ProjectiveSpectrum): O(1) pulls back to an ample line bundle along immersions from quasi-compact schemes`.
7. After 1: `feat(AlgebraicGeometry/RelativeProj): the symmetric algebra is generated in degree one and its relative Proj is proper`.
8. After 2, 4, 5: `feat(AlgebraicGeometry/LineBundle): sections over nonvanishing loci extend; ampleness pulls back along immersions`.
9. After 2, 3, 4, 5, 8: `feat(AlgebraicGeometry/LineBundle): relatively ample line bundles`.
10. After 2, 3, 4, 5, 8, 9: `feat(AlgebraicGeometry/LineBundle): relative ampleness composes after twisting by a large power`.
11. After none: `feat(AlgebraicGeometry/IntersectionNumber): intersection numbers of powers`.
12. After none: `feat(AlgebraicGeometry/Modules): the sheaf associated with a finite module is of finite type`.
13. After none: `feat(RingTheory/GradedAlgebra): finiteness and generation of the degree-one part of a graded algebra`.
14. After 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12: `feat(AlgebraicGeometry/Morphisms): relatively very ample line bundles, projective morphisms, projective bundles and blowups`.
15. After none: `feat(AlgebraicGeometry/RelativeGluing): recognise the glued scheme of a relative gluing datum`.
16. After none: `feat(AlgebraicGeometry/Modules): pull back graded sections, and Proj of them as a base change over affine opens`.
17. After 1, 16: `feat(AlgebraicGeometry/RelativeProj): charts of the base change of a relative Proj over small affine opens, and the pulled-back algebra stays of finite type and generated in degree one`.
18. After 1, 15, 16, 17: `feat(AlgebraicGeometry/RelativeProj): the relative Proj commutes with base change`.
19. After none: `feat(AlgebraicGeometry/RelativeProj): isomorphisms of relative Proj`.
20. After 1, 7, 13, 19: `feat(AlgebraicGeometry/RelativeProj): closed immersions of relative Proj from maps surjective in degree one`.
21. After none: `feat(AlgebraicGeometry/Modules): pullback of the graded symmetric algebra`.
22. After 1, 7, 13, 15, 16, 17, 18, 19, 20, 21: `feat(AlgebraicGeometry/RelativeProj): base change of projective bundles`.
23. After 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22: `feat(AlgebraicGeometry/Morphisms): projective schemes over a ring are the projective morphisms to its spectrum, and projective morphisms are stable under base change`.
24. After 2, 3, 4, 5, 8, 9: `feat(AlgebraicGeometry/LineBundle): global generation after sufficiently positive ample twisting`.
25. After 2, 7, 13, 19, 20, 22: `feat(AlgebraicGeometry/RelativeProj): projective bundles are invariant under invertible twists`.
26. After 2, 3, 5, 8, 9, 24: `feat(AlgebraicGeometry/Modules): relative generation after ample twisting`.
27. After 7, 18, 19, 20, 21, 22: `feat(AlgebraicGeometry/RelativeProj): the relative Segre closed immersion`.
28. After 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27: `feat(AlgebraicGeometry/Morphisms): composition of projective morphisms`.

## File inventory

Line counts are for the final source files on this branch, relative to current `main`.
Removed paths have no forwarding modules.

| File | Lines |
| --- | ---: |
| `TauCeti/Algebra/Category/ModuleCat/Sheaf/TensorProduct/Basic.lean` | 172 |
| `TauCeti/AlgebraicGeometry/Blowup/IdealSheaf.lean` | 231 |
| `TauCeti/AlgebraicGeometry/Blowup/Projective.lean` | 130 |
| `TauCeti/AlgebraicGeometry/Fibers.lean` | 423 |
| `TauCeti/AlgebraicGeometry/IntersectionNumber/Basic.lean` | 446 |
| `TauCeti/AlgebraicGeometry/LineBundle/Ample.lean` | 610 |
| `TauCeti/AlgebraicGeometry/LineBundle/Extension.lean` | 326 |
| `TauCeti/AlgebraicGeometry/LineBundle/GlobalGeneration/Ample.lean` | 121 |
| `TauCeti/AlgebraicGeometry/LineBundle/GlobalGeneration/Basic.lean` | 275 |
| `TauCeti/AlgebraicGeometry/LineBundle/GlobalGeneration/Pullback.lean` | 71 |
| `TauCeti/AlgebraicGeometry/LineBundle/GlobalGeneration/TensorProduct.lean` | 79 |
| `TauCeti/AlgebraicGeometry/LineBundle/LocalRing.lean` | 130 |
| `TauCeti/AlgebraicGeometry/LineBundle/NonvanishingLocus.lean` | 647 |
| `TauCeti/AlgebraicGeometry/LineBundle/Power.lean` | 112 |
| `TauCeti/AlgebraicGeometry/LineBundle/RelativelyAmple.lean` | 543 |
| `TauCeti/AlgebraicGeometry/LineBundle/RelativelyAmple/Comp.lean` | 177 |
| `TauCeti/AlgebraicGeometry/LineBundle/RelativelyAmple/GlobalGeneration.lean` | 71 |
| `TauCeti/AlgebraicGeometry/LineBundle/TensorProduct.lean` | 265 |
| `TauCeti/AlgebraicGeometry/Modules/FinitePresentation.lean` | 406 |
| `TauCeti/AlgebraicGeometry/Modules/GradedAlgebra/Localization.lean` | 293 |
| `TauCeti/AlgebraicGeometry/Modules/Pullback/ResidueField.lean` | 292 |
| `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/GradedAlgebra/PullbackSections.lean` | 385 |
| `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/GradedAlgebra/SymmetricAlgebra/Adjunction.lean` | 607 |
| `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/GradedAlgebra/SymmetricAlgebra/GradedPullback.lean` | 361 |
| `TauCeti/AlgebraicGeometry/Modules/SymmetricPower/Affine.lean` | 570 |
| `TauCeti/AlgebraicGeometry/Morphisms/Projective/Basic.lean` | 312 |
| `TauCeti/AlgebraicGeometry/Morphisms/Projective/Over.lean` | 362 |
| `TauCeti/AlgebraicGeometry/Morphisms/Separated.lean` | 151 |
| `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/Ample.lean` | 198 |
| `TauCeti/AlgebraicGeometry/Pullback/Affine.lean` | 56 |
| `TauCeti/AlgebraicGeometry/RelativeGluing.lean` | 103 |
| `TauCeti/AlgebraicGeometry/RelativeProj/BaseChange.lean` | 225 |
| `TauCeti/AlgebraicGeometry/RelativeProj/Basic.lean` | 288 |
| `TauCeti/AlgebraicGeometry/RelativeProj/ClosedImmersion.lean` | 199 |
| `TauCeti/AlgebraicGeometry/RelativeProj/Map.lean` | 375 |
| `TauCeti/AlgebraicGeometry/RelativeProj/Pullback.lean` | 383 |
| `TauCeti/AlgebraicGeometry/RelativeProj/SymmetricAlgebra.lean` | 186 |
| `TauCeti/AlgebraicGeometry/RelativeProj/SymmetricAlgebra/Pullback.lean` | 143 |
| `TauCeti/AlgebraicGeometry/RelativeProj/TwistingSheaf.lean` | 236 |
| `TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/GlobalGeneration.lean` | 87 |
| `TauCeti/CategoryTheory/Monoidal/Closed/Epi.lean` | 51 |
| `TauCeti/RingTheory/GradedAlgebra/DegreeOne.lean` | 221 |
| `TauCeti/RingTheory/LocalRing/Module.lean` | 166 |
| `TauCeti/RingTheory/Localization/Closure.lean` | 77 |
| `LOOKAHEAD.md` | 722 |
