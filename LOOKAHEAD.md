<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"noetherian-approximation","main":"fa7523a49c12af26664417a956326c2608b7824f","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: separation, affineness and underlying space of limits of schemes with affine transition maps"},{"n":2,"after":[],"title":"feat: Noetherian approximation of affine schemes"},{"n":3,"after":[],"title":"feat: descent of morphisms and isomorphisms of finitely presented schemes along cofiltered limits"},{"n":4,"after":[3],"title":"feat: existence of cofiltered limits of schemes with affine transition maps"},{"n":5,"after":[],"title":"feat: descent of finitely presented affine schemes along cofiltered limits"},{"n":6,"after":[3,5],"title":"feat: closed immersions and finite morphisms are inherited from a finite stage"},{"n":7,"after":[3,6],"title":"feat: open immersions are inherited from a finite stage"},{"n":8,"after":[2,3,6],"title":"feat: smooth and étale morphisms are inherited from a finite stage"},{"n":9,"after":[3,6,7,8],"title":"feat: closed immersions, finite, smooth and étale morphisms over a member, and separatedness, are inherited from a finite stage"},{"n":10,"after":[],"title":"feat: gluing two schemes along an open subscheme"},{"n":11,"after":[1,3,5,6,7,10],"title":"feat: descent of schemes of finite presentation along cofiltered limits"},{"n":12,"after":[3,6,9],"title":"feat: finite-stage criteria for surjectivity and proper covers"},{"n":13,"after":[3,5,6,8,11],"title":"feat: flatness is inherited from a finite stage"},{"n":14,"after":[3,6,9,11,12],"title":"feat: properness is inherited from a finite stage"},{"n":15,"after":[],"title":"feat: quasi-compact opens of finite type over ℤ in an affine scheme come from a finitely generated subring"},{"n":16,"after":[15],"title":"feat: quasi-affine models of a quasi-compact open as opens of the spectrum of a fibre product"},{"n":17,"after":[],"title":"feat: global sections with affine basic opens descend along cofiltered limits of schemes"},{"n":18,"after":[],"title":"feat: the cofiltered category of finitely generated subrings along a system of rings"},{"n":19,"after":[16,18],"title":"feat: affine models of a scheme near a quasi-compact open"},{"n":20,"after":[10],"title":"feat: morphisms between gluings of two schemes along opens"},{"n":21,"after":[3,4,10,20],"title":"feat: cofiltered limits of schemes commute with gluing along opens"},{"n":22,"after":[2,3,4,10,15,16,17,18,19,20,21],"title":"feat: extending finite-presentation models across a quasi-compact open"},{"n":23,"after":[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22],"title":"feat: absolute Noetherian approximation of quasi-compact quasi-separated schemes"}]}-->
# Lookahead: `noetherian-approximation` (SchemeAndStackFoundations §0.9)

Status: **partial**. Resumed from `5146a1eb184c` and merged `origin/main` at
`fa7523a49c12af26664417a956326c2608b7824f` (CI/tooling changes only; no conflicts, no proof
changes needed). The pinned Mathlib still has no descent of flatness along filtered colimits of
rings, so splits 13–14 remain as planned.
`affine_transition_limits` and absolute `noetherian_approximation` are proved.
For `finite_presentation_limits`, object and morphism descent and six of the eight requested
properties are proved. General flatness and properness remain (splits 13–14).
This session adds finite-stage constructible-set criteria, full surjectivity descent, and three
properness descent criteria with explicit geometric hypotheses (split 12).

Session of 2026-11-08 (23:17 UTC): `origin/main` had not moved past `fa7523a49c12`; the branch was
rebuilt (`lake build` green) and `lookahead-check` passes, with no Lean changes. The pinned Mathlib
was searched again for split 13 ingredients. It has `Module.Flat.projective_of_finitePresentation`,
the equational criterion and the local-ring results of `RingTheory/LocalRing/Module.lean`.
It has no openness of the flat locus, no local flatness criterion for modules over a non-local
base or over an `R`-algebra `S`, and no descent of flatness along filtered colimits (Stacks 00R6,
via Algebra §10.128–10.168). Split 13 therefore still needs those ring-theoretic prerequisites as
their own PRs before `Limits/Flat.lean`. Split 14 still needs the Chow cover. Neither can be
replaced by a stub, because no listed supplier pins them.

The definitive target is SchemeAndStackFoundations/README.md §0.9. `Suggested.lean` pins no Lean
forms for `affine_transition_limits`, `noetherian_approximation`, `finite_presentation_limits`
or `qcoh_extension`; these are README-only specifications. This branch targets the three
limit/approximation clauses selected by the operator, not the other §0.9 applications.

## Stubbed declarations

None. No proved declaration consumes `qcoh-extension`, so there is no stub module and the
machine-readable supplier list is empty. The earlier branch had already removed its unused
stub: the absolute approximation proof uses finitely generated subrings of fibre products
(splits 15–22) rather than extending ideal sheaves. This session preserves that proof.

The supplier's §0.4 README section and the full diff of open PR #30873 were checked. The PR
provides `AlgebraicGeometry.Scheme.Modules.exists_isFinitePresentation_restrict_iso`,
`exists_isFinitePresentation_restrictFunctor_map_eq` and their affine/extension prerequisites.
None is imported or assumed here. Therefore there are no stub signatures or signature
differences to report, and no substitution is needed when the supplier lands.
The already-merged partial suppliers are left as on main.

## Splits

This is a port plan, not permission to open a stacked PR. Every PR is based on main after its
listed prerequisites merge; independent splits may run concurrently. Every description must
include the standalone attribution line `Roadmap: SchemeAndStackFoundations` and identify
README.md §0.9. Split 23 is held until all of 1–22 merge, carries the exported absolute
approximation theorem, and is the only split that completes the selected target. Splits 13–14
are unproved plans; their final sizes and any additional prerequisite subdivisions cannot be
fixed before those proofs exist. The already-proved small terminal split is kept separate so
that no earlier PR claims completion.

1. **feat: separation, affineness and underlying space of limits of schemes with affine
   transition maps** (after: none) — *proved*. File
   `TauCeti/AlgebraicGeometry/Limits/AffineTransition.lean` (198 lines), namespace
   `TauCeti.AlgebraicGeometry.Scheme`: `isSeparated_of_isLimit`, `quasiSeparatedSpace_of_isLimit`
   (the separatedness half of `affine_transition_limits`, 01YX + 01S7; quasi-compactness is
   Mathlib's `Scheme.compactSpace_of_isLimit`), `isAffine_of_isLimit`, `isQuasiAffine_of_isLimit`,
   `isAffine_iff_exists_of_isLimit`, `isQuasiAffine_iff_exists_of_isLimit` (with Mathlib's 01Z6/01Z5
   converses); and `|lim Xᵢ| = lim |Xᵢ|` (0CUF): `exists_π_app_eq_of_isLimit`,
   `specializes_of_isLimit`, `ext_of_isLimit`, `topologicalSpace_eq_iInf_induced_of_isLimit`, and the
   instance `preservesLimit_forgetToTop : PreservesLimit D Scheme.forgetToTop`.
2. **feat: Noetherian approximation of affine schemes** (after: none) — *proved*.
   File `TauCeti/AlgebraicGeometry/Limits/NoetherianApproximation.lean` (105 lines):
   `finsetAdjoinDiagram`, `finsetAdjoinCocone`, `isColimitFinsetAdjoinCocone`, the instance
   `Algebra.FinitePresentation ℤ ((finsetAdjoinDiagram A).obj s)`,
   `locallyOfFinitePresentation_terminal_from_Spec`, and
   `Scheme.exists_isLimit_finitePresentation_of_isAffine` (the affine case of 01ZA).
3. **feat: descent of morphisms and isomorphisms of finitely presented schemes along cofiltered
   limits** (after: none) — *proved*. Files:
   - `TauCeti/CategoryTheory/Limits/Shapes/Pullback/Cofiltered.lean` (123 lines):
     `CategoryTheory.Functor.pullbackOver`, `CategoryTheory.Limits.Cone.pullbackOver`,
     `CategoryTheory.Limits.IsLimit.pullbackOver` and their `_map_fst/_map_snd`,
     `_π_app_fst/_π_app_snd` lemmas;
   - `TauCeti/AlgebraicGeometry/Limits/BaseChange.lean` (50 lines in this split; 85 final): instances passing affine
     transition maps, quasi-compactness and quasi-separation to `D.pullbackOver r`;
   - `TauCeti/AlgebraicGeometry/Limits/FinitePresentation.lean` (230 lines):
     `exists_map_comp_eq_of_isLimit`, `exists_π_app_comp_eq_of_isLimit` (01ZC over `ℤ`),
     `exists_pullbackMap_comp_eq_of_isLimit` (01ZM, descent of morphisms),
     `pullbackMap_iff_of_pullbackMap_comp_eq` (the base change to the limit of a descended morphism
     is the original one up to the canonical isomorphisms `S ×_{Dⱼ} (Dⱼ ×_{Dᵢ} Z) ≅ S ×_{Dᵢ} Z`, so
     it has every isomorphism-invariant property the original has; added this session and used by
     splits 8 and 11, replacing a copy of the same argument in split 8),
     `exists_isIso_pullbackMap_of_isLimit` (081E, isomorphisms).
4. **feat: existence of cofiltered limits of schemes with affine transition maps** (after: 3) —
   *proved*. File `TauCeti/AlgebraicGeometry/Limits/Existence.lean` (307 lines):
   `hasLimit_of_isAffine` and the instance `hasLimit_of_isAffineHom : HasLimit D` (01YW). It needs
   split 3 only for `Pullback/Cofiltered.lean`.
5. **feat: descent of finitely presented affine schemes along cofiltered limits** (after: none) —
   *proved*. Files:
   - `TauCeti/CategoryTheory/Limits/ConcreteCategory/Filtered.lean` (51 lines):
     `TauCeti.CategoryTheory.Limits.Concrete.exists_subset_range_of_isColimit` (a finite subset of a
     filtered colimit in a concrete category whose forgetful functor preserves the colimit comes from
     one stage; `TauCeti.GrpCat.exists_subset_range_of_isColimit` on `main` is a special case and can
     be refactored onto it in a follow-up);
   - `TauCeti/Algebra/Category/Ring/FinitePresentation.lean` (69 lines):
     `TauCeti.CommRingCat.exists_isPushout_of_isColimit` (Stacks 00QO: a finitely presented ring map
     out of a filtered colimit is a pushout of a finitely presented one out of some stage, via
     Mathlib's `Algebra.Presentation.ModelOfHasCoeffs`);
   - `TauCeti/AlgebraicGeometry/Limits/AffineDescent.lean` (83 lines):
     `Scheme.exists_isPullback_of_isLimit_of_isAffine` (01ZM, object half, affine case: an affine
     scheme of finite presentation over a cofiltered limit of affine schemes is the base change of
     one over some member) and `Scheme.exists_isPullback_of_isLimit_of_isAffineOpen` (the same over
     the preimages of an affine open of a member, for any diagram with affine transition maps).
   About 200 lines.
6. **feat: closed immersions and finite morphisms are inherited from a finite stage** (after: 3, 5)
   — *proved*. Files:
   - `TauCeti/Algebra/Category/Ring/Pushout.lean` (73 lines): `TauCeti.CommRingCat.surjective_of_isPushout`,
     `TauCeti.CommRingCat.isIntegral_of_isPushout`;
   - `TauCeti/CategoryTheory/MorphismProperty/Limits.lean` (existing file, +18 lines):
     `CategoryTheory.MorphismProperty.pullback_fst_pullback_fst_iff`, `pullback_fst_of_comp_eq`;
   - `TauCeti/AlgebraicGeometry/Limits/AffineProperties.lean` (292 lines):
     `exists_forall_appTop_snd_mem` (the generator argument), the affine cases
     `exists_isClosedImmersion_pullback_fst_of_isLimit_of_isAffine`,
     `exists_isFinite_pullback_fst_of_isLimit_of_isAffine`, the reduction
     `exists_pullback_fst_of_isLimit_of_le_isAffineHom` (from affine `Y` to `Y` qcqs over the member,
     via Mathlib's 01Z6 `Scheme.exists_isAffine_of_isLimit` on `D.pullbackOver q`), and
     `exists_isClosedImmersion_pullback_fst_of_isLimit_of_forall_isAffine`,
     `exists_isFinite_pullback_fst_of_isLimit_of_forall_isAffine`;
   - `TauCeti/AlgebraicGeometry/Limits/ZariskiLocal.lean` (142 lines):
     `exists_pullback_fst_of_isLimit_of_isZariskiLocalAtTarget` (any property local at the target and
     stable under base change that is inherited over cofiltered limits of affine schemes is inherited
     over cofiltered limits of quasi-compact schemes with affine transition maps, via
     `AlgebraicGeometry.isLimitOpensCone` on a finite affine cover of the member; the structure
     morphism of `Y` carries a second property `Q` stable under base change, finite type here and
     finite presentation in split 8), and the final
     `exists_isClosedImmersion_pullback_fst_of_isLimit` (01ZP) and `exists_isFinite_pullback_fst_of_isLimit`
     (01ZO): for `Y` of finite type, quasi-compact and quasi-separated over `Sᵢ`, if
     `Y ×_{Sᵢ} S ⟶ S` is a closed immersion (finite), so is `Y ×_{Sᵢ} Sⱼ ⟶ Sⱼ` for some `j`.
   About 520 lines; may be opened as two PRs (affine case, then the two reductions) if reviewers ask.
7. **feat: open immersions are inherited from a finite stage** (after: 3, 6) — *proved* (inherited). Files:
   - `TauCeti/CategoryTheory/MorphismProperty/Limits.lean` (existing file, +17 lines; hence after
     split 6, which also extends it): `CategoryTheory.MorphismProperty.pullback_map_pullback_map_iff`
     (the base change of `g : X ⟶ Y` over `Z` along `f' ≫ f` versus along `f'` after `f`);
   - `TauCeti/AlgebraicGeometry/Limits/OpenImmersion.lean` (191 lines):
     `exists_preimage_pullbackMap_eq_of_isLimit` (01Z4 for the limit `X ×_{Dᵢ} S = lim X ×_{Dᵢ} Dⱼ`:
     quasi-compact opens descend) and `exists_isOpenImmersion_pullbackMap_of_isLimit` (0EUU: for
     `g : X ⟶ Y` over `Dᵢ`, `X` l.f.p. and quasi-compact, `Y` l.f.t. and qcqs over `Dᵢ`, if the base
     change of `g` to the limit is an open immersion, so is its base change to some `Dⱼ`). The proof
     descends the image of `g` (01Z4 + Mathlib's `exists_map_eq_top`) and applies split 3's 081E to
     the corestriction.
8. **feat: smooth and étale morphisms are inherited from a finite stage** (after: 2, 3, 6) —
   *proved*. File `TauCeti/AlgebraicGeometry/Limits/Smooth.lean` (287 lines; its descended-isomorphism step now
   uses split 3's `pullbackMap_iff_of_pullbackMap_comp_eq`):
   - `exists_pullback_fst_of_isLimit_of_isPullback`: for `P` stable under base change and `Y` of
     finite presentation, quasi-compact and quasi-separated over `Sᵢ`, if `Y ×_{Sᵢ} S ⟶ S` is the base
     change along some `S ⟶ T`, `T` locally of finite presentation over `ℤ`, of a morphism
     `V ⟶ T` with `P` (and of finite presentation, qcqs), then `Y ×_{Sᵢ} Sⱼ ⟶ Sⱼ` has `P` for
     some `j` (01ZC factors `S ⟶ T` through some `Sₖ`; the two models over `Sₖ` are isomorphic over
     some `Sⱼ` by split 3's 01ZM/081E);
   - `exists_pullback_fst_of_isLimit_of_ringEquiv`: the same over affine members, with the model
     given by `Γ(Y ×_{Sᵢ} S) ≃ Γ(S) ⊗[A₀] B₀` for a finitely generated subring `A₀` (uses split 2's
     `locallyOfFinitePresentation_terminal_from_Spec`);
   - `exists_smooth_pullback_fst_of_isLimit_of_isAffine`,
     `exists_etale_pullback_fst_of_isLimit_of_isAffine` (affine members and affine `Y`, from Mathlib's
     `Algebra.Smooth.exists_subalgebra_fg` and `Algebra.Etale.exists_subalgebra_fg`);
   - `exists_pullback_fst_of_isLimit_of_isZariskiLocalAtSource` (from affine `Y` to quasi-compact
     `Y`, over affine members, by a finite affine cover);
   - `exists_smooth_pullback_fst_of_isLimit` (0C0C) and `exists_etale_pullback_fst_of_isLimit`
     (07RP): over cofiltered limits of quasi-compact schemes with affine transition maps, via split
     6's `exists_pullback_fst_of_isLimit_of_isZariskiLocalAtTarget` with `Q` finite presentation.
9. **feat: closed immersions, finite, smooth and étale morphisms over a member, and separatedness, are inherited from a finite stage** (after: 3, 6, 7, 8) — *proved*. Files:
   - `TauCeti/CategoryTheory/MorphismProperty/Limits.lean` (existing file, +28 lines; hence after
     splits 6 and 7, which also extend it):
     `CategoryTheory.MorphismProperty.pullback_map_iff_pullback_fst_pullback_snd` (the base change of
     `g : X ⟶ Y` over `Z` along `f` is the base change of `g` along `T ×_Z Y ⟶ Y`) and
     `CategoryTheory.MorphismProperty.diagonal_pullback_fst_iff` (the diagonal of a base change of
     `q` is the base change of the diagonal of `q`);
   - `TauCeti/AlgebraicGeometry/Limits/Morphisms.lean` (140 lines final), together with
     35 added lines in `TauCeti/AlgebraicGeometry/Limits/BaseChange.lean`:
     `exists_pullbackMap_of_pullbackOver` (for a morphism `g : X ⟶ Y` over a member `Sᵢ`, the base
     changes of `g` to the limit and to the `Sⱼ` are the base changes of one morphism over the member
     `Sᵢ ×_{Sᵢ} Y` of the limit `Y ×_{Sᵢ} S = lim (Y ×_{Sᵢ} Sⱼ)` of split 3's
     `IsLimit.pullbackOver`, so the case `Y = Sᵢ` gives the general one);
     `exists_isClosedImmersion_pullbackMap_of_isLimit` (01ZP), `exists_isFinite_pullbackMap_of_isLimit`
     (01ZO), `exists_smooth_pullbackMap_of_isLimit` (0C0C), `exists_etale_pullbackMap_of_isLimit`
     (07RP): the morphism forms Stacks states and the README's `finite_presentation_limits` asks for
     ("properties ... of a morphism over `S`"), from the `pullback.fst` forms of splits 6 and 8
     (open immersions 0EUU and isomorphisms 081E are already in morphism form, splits 7 and 3); and
     `exists_isSeparated_pullback_fst_of_isLimit` (for `Y` qcqs over `Sᵢ`, separatedness of
     `Y ×_{Sᵢ} S ⟶ S` is inherited by some `Y ×_{Sᵢ} Sⱼ ⟶ Sⱼ`, by applying 01ZP to the diagonal;
     one ingredient of 081F). The generic reduction lives in `BaseChange.lean`;
     `Surjective.lean` therefore does not import the smooth/étale results. About 200 lines.
10. **feat: gluing two schemes along an open subscheme** (after: none) — *proved* (2026-11-05).
    File `TauCeti/AlgebraicGeometry/Gluing/Pushout.lean` (412 lines), namespace
    `TauCeti.AlgebraicGeometry.Scheme` (two lemmas in Mathlib's `AlgebraicGeometry.IsZariskiLocalAtSource`
    namespace, for dot notation): `isPushout_opens_of_sup_eq_top` (a scheme covered by opens `U`, `V`
    is the pushout of `U ⟵ U ⊓ V ⟶ V`), `isPushout_of_isPullback_of_opensRange_sup_eq_top`,
    `IsZariskiLocalAtSource.iff_of_opensRange_sup_eq_top`, `IsZariskiLocalAtSource.pushout_desc_iff`;
    for open immersions `f : W ⟶ U`, `g : W ⟶ V`: the instances `isOpenImmersion_span_map`,
    `HasPushout f g` (from Mathlib's colimits of locally directed diagrams of open immersions),
    `IsOpenImmersion (pushout.inl f g)`/`(pushout.inr f g)`, `CompactSpace`/`QuasiSeparatedSpace` of the
    pushout, and `opensRange_pushout_inl_sup_opensRange_pushout_inr`,
    `exists_eq_of_pushout_inl_eq_pushout_inr`, `isPullback_pushout`,
    `image_pushout_inl_inter_image_pushout_inr`, `mem_of_isPullback_homOfLE`,
    `preimage_opensRange_eq_of_isPullback`, `isPullback_of_isPullback_of_opensRange_sup_eq_top`
    (a commutative square whose target corner is covered by two opens is a pullback if it is one over
    the two opens and their intersection) and `isPullback_pushout_desc_of_isPullback` (base change
    commutes with gluing). Pure scheme theory, imports only Mathlib.
11. **feat: descent of schemes of finite presentation along cofiltered limits** (after: 1, 3, 5, 6, 7,
    10) — *proved* (2026-11-05). File `TauCeti/AlgebraicGeometry/Limits/Descent.lean` (305 lines):
    `isPullback_lift_of_isPullback` (a model over `Sᵢ` base changes to every later `Sⱼ`),
    `exists_isPullback_of_isLimit_of_le` (a quasi-compact open of a scheme with a model has a model,
    an open of the base-changed model; 01Z4), `exists_isPullback_of_isLimit_of_sup_eq_top` (the
    inductive step: descend the overlap, descend the inclusion `U ⊓ V ⟶ V` by split 3, make it an
    open immersion by split 7's 0EUU, glue by split 10),
    `exists_isPullback_of_isLimit_of_isAffineOpen_of_le` (base case, from split 5), and
    **`exists_isPullback_of_isLimit`**: for `S = lim Sᵢ` cofiltered with affine transition maps and
    every `Sᵢ` quasi-compact and quasi-separated, every `X ⟶ S` locally of finite presentation,
    quasi-compact and quasi-separated is `IsPullback a f p (c.π.app i)` for some `p : Y ⟶ Sᵢ` locally
    of finite presentation, quasi-compact and quasi-separated — the object half of 01ZM, completing
    the first clause of `finite_presentation_limits`. Split 1 supplies `quasiSeparatedSpace_of_isLimit`.
12. **feat: finite-stage criteria for surjectivity and proper covers** (after: 3, 6, 9)
    — *proved in this session*, 332 lines. All declarations are in
    `TauCeti.AlgebraicGeometry.Scheme`.
    - `TauCeti/AlgebraicGeometry/Limits/Constructible.lean` (109 lines):
      `exists_map_preimage_eq_empty_of_isConstructible`,
      `exists_map_preimage_subset_map_preimage_of_isConstructible`,
      `exists_map_preimage_eq_map_preimage_of_isConstructible`.
      Emptiness, inclusion and equality of constructible subsets of a qcqs member, after
      pullback to the limit, are detected at a finite stage. The proof uses the finite-union
      decomposition into differences of affine opens and Mathlib's open-inclusion criterion.
    - `TauCeti/AlgebraicGeometry/Limits/Surjective.lean` (67 lines):
      `exists_surjective_pullback_fst_of_isLimit`,
      `exists_surjective_pullbackMap_of_isLimit`. A quasi-compact locally finitely presented
      morphism that becomes surjective over the limit is surjective at a finite stage, by
      Chevalley's theorem and the constructible criterion. The first theorem needs qcqs only
      for the distinguished member; the second needs qcqs members and a qcqs target over it.
    - `TauCeti/AlgebraicGeometry/Limits/Proper.lean` (156 lines):
      `exists_isProper_pullback_fst_of_isLimit_of_isImmersion` proves properness descent for
      a quasi-compact scheme admitting an immersion into a proper scheme over a member;
      `exists_isProper_pullback_fst_of_isLimit_of_isProper_surjective` proves it when the
      source has a proper surjective cover admitting such an immersion;
      `exists_isProper_pullback_fst_of_isLimit_of_surjective` descends properness of a
      separated finitely presented model receiving, over the limit, a surjective morphism
      from the base change of a proper finitely presented model. This last theorem consumes
      both surjectivity descent and descent of morphisms. These are conditional criteria,
      not the unconditional properness clause of the target: the cover-existence step is
      still missing.
13. **feat: flatness is inherited from a finite stage** (after: 3, 5, 6, 8, 11)
    — *remaining*. Planned files: `TauCeti/RingTheory/Flat/FilteredColimit.lean` and
    `TauCeti/AlgebraicGeometry/Limits/Flat.lean`. First prove Stacks 10.168 (00R6/05LY):
    a finitely presented algebra over a filtered colimit that is flat comes from a flat
    algebra at a finite stage. Then add the affine and general scheme statements
    `exists_flat_pullback_fst_of_isLimit` and `exists_flat_pullbackMap_of_isLimit` (04AI),
    using the local-at-source and local-at-target reductions of splits 6 and 8.
    No Lean placeholder or extra hypothesis for the missing ring theorem is present.
    Aim for 200–600 lines per PR; the ring argument must be split further if it exceeds that.
14. **feat: properness is inherited from a finite stage** (after: 3, 6, 9, 11, 12)
    — *remaining*. Extend `TauCeti/AlgebraicGeometry/Limits/Proper.lean` with the unconditional
    `exists_isProper_pullback_fst_of_isLimit` and `exists_isProper_pullbackMap_of_isLimit`
    (081F). Split 12 now proves all steps after choosing a proper surjective cover that
    immerses into a proper ambient scheme. Construct that cover (the form of Chow's lemma
    used in Stacks 32.12.1/0202), without assuming or stubbing it, or find another proof of
    universal closedness. Neither pinned Mathlib nor main supplies its existence.
    No extra supplier is assumed. Avoid a dependency on final split 23: one possible route
    reduces to affine bases, uses splits 2 and 11 to descend to a Noetherian model, and proves
    Noetherian Chow there before spreading out the cover. The cover construction needs separate prerequisite PRs
    if it exceeds 600 lines; the final application of split 12 should stay within that size.
15. **feat: quasi-compact opens of finite type over ℤ in an affine scheme come from a finitely
    generated subring** (after: none) — *proved* (2026-11-05). File
    `TauCeti/AlgebraicGeometry/Limits/QuasiAffine.lean` (206 lines), namespace
    `TauCeti.AlgebraicGeometry`, imports only Mathlib:
    `finiteType_intCastRingHom_of_locallyOfFiniteType_terminal_from_Spec` (if `Spec R` is locally of
    finite type over the terminal scheme, `ℤ → R` is of finite type; the finite-type converse of
    split 2's `locallyOfFinitePresentation_terminal_from_Spec`),
    `exists_finset_isOpenImmersion_away_comp_SpecMap_val` (if `R_f` is of finite type over `ℤ`, a
    finite `s ∋ f` makes `R_f` the localization away from `f` of every subring `A ⊇ s`, so
    `Spec R_f ⟶ Spec R ⟶ Spec A` is an open immersion, whose image contains (in fact is) the
    basic open `D_A(f)`), and
    **`Scheme.exists_finset_isOpenImmersion_comp_SpecMap_val`** (Stacks 01Z7): for an open immersion
    `ι : W ⟶ Spec R` with `W` quasi-compact and locally of finite type over `ℤ`, there is a finite
    `s ⊆ R` such that `ι ≫ Spec.map A.val` is an open immersion for every subring `A ⊇ s`; with
    `A = ℤ[s]` this is the first clause of 01Z7, and cofinality of such `A` is its "moreover".
    It also takes a finite set `F₀ ⊆ R` with each `D(f)`, `f ∈ F₀`, inside the image of `W`, and
    makes the image of `W` in `Spec A` contain `D_A(f)` for every `f ∈ F₀` (added this session;
    split 16 uses it to compute the image of a model in `Spec A`). The
    proof covers `range ι` by finitely many `D(f)`, so injectivity of `W ⟶ Spec A` follows from
    `D_R(f)` being the preimage of `D_A(f)`, and it is locally an open immersion by
    `IsOpenImmersion.of_isLocalization`.
16. **feat: quasi-affine models of a quasi-compact open as opens of the spectrum of a fibre
    product** (after: 15) — *proved* (2026-11-05). Files:
    - `TauCeti/RingTheory/Localization/Away/Pullback.lean` (82 lines), namespace `TauCeti`:
      `isLocalization_away_eqLocus_of_bijective_awayMap` (for `f : R →+* C`, `h : A →+* C` and
      `x = (g, b)` in the fibre product `R ×_C A` = Mathlib's `RingHom.eqLocus` underlying
      `CommRingCat.pullbackCone f h`, if `R_g → C_{f g}` is bijective then `A_b` is the localization
      of `R ×_C A` away from `x`); pure commutative algebra, imports only Mathlib.
    - `TauCeti/AlgebraicGeometry/Limits/SpecFiberProduct.lean` (330 lines), namespace
      `TauCeti.AlgebraicGeometry.Scheme`, imports split 15's `Limits/QuasiAffine.lean`:
      `bijective_awayMap_presheaf_map_of_basicOpen_le` (for qc opens `V ≤ W`, `W` qs, and `D(r) ⊆ V`,
      the restriction `Γ(X, W)_r → Γ(X, V)_{r|V}` is bijective, by the qcqs lemma),
      `isLocalization_away_eqLocus_of_basicOpen_le` (the two combined),
      `isOpenImmersion_toSpecΓ_comp_SpecMap_pullbackCone_snd` (for `X` qcqs, `V ⊆ X` qc open,
      `h : Γ(Y, ⊤) ⟶ Γ(X, V)` with `Y` qcqs covered by affine `D(b k)`, `h (b k) = g k|_V`,
      `D(g k) ⊆ V`: `Y ⟶ Spec (Γ(X, ⊤) ×_{Γ(X, V)} Γ(Y, ⊤))` is an open immersion),
      `mem_range_toSpecΓ_comp_SpecMap_pullbackCone_snd` (added this session: the basic open of
      `(g, b)` in `Spec P` is the image of `D(b)`),
      `isPullback_toSpecΓ_comp_SpecMap` (for any ring `A` mapping compatibly to `Γ(X, ⊤)` and
      `Γ(Y, ⊤)` along which `Y` is open, with the `D(β (a k))` covering `Y` and `D(α (a k)) ⊆ V`,
      the preimage of `Y` in `X` is `V`: an `IsPullback` square with `φ : V ⟶ Y`),
      `opensRange_toSpecΓ_comp_SpecMap_eq_iSup` (added this session: if `Y ⟶ Spec A` is an open
      immersion, `Y` is covered by the `D(β (a k))` and each `D(a k)` lies in the image, then the
      image is `⨆ k, D(a k)`), and
      **`exists_finset_isPullback_toSpecΓ_comp_SpecMap`** (with `Y` also locally of finite type
      over `ℤ` and finitely many `b k`: a finite `s ⊆ P = Γ(X, ⊤) ×_{Γ(X, V)} Γ(Y, ⊤)` such that for
      every subring `A ⊇ s` of `P`, `Y` is open in `Spec A` with preimage `V` in `X`, **and its
      image is the union of the basic opens of the elements `(g k, b k)` of `A`**; split 15's
      01Z7 applied to `Y ⊆ Spec P`). This is the single-stage step of Stacks 01Z9. The image
      clause (added this session) is what makes split 22's transition maps affine: without it, the
      preimage of `Vⱼ ⊆ Spec C` in `Spec C'` contains `Vⱼ'` but need not equal it, and then the
      preimage of `Uⱼ` in `X_{j',C'}` is not `Uⱼ'`.
17. **feat: global sections with affine basic opens descend along cofiltered limits of schemes**
    (after: none) — *proved* (2026-11-05). File `TauCeti/AlgebraicGeometry/Limits/GlobalSections.lean`
    (96 lines), namespace `TauCeti.AlgebraicGeometry.Scheme`, imports only Mathlib:
    `exists_appTop_π_eq_and_isAffineOpen_basicOpen` (for `c` a limit of a cofiltered diagram of
    qcqs schemes with affine transition maps, a global section `r` of `c.pt` with `D(r)` affine is
    `(c.π.app i).appTop t` for some `t` on a member with `D(t)` affine) and
    `exists_appTop_π_eq_and_iSup_basicOpen_eq_top` (finitely many such `s k` with `D(s k)` covering
    `c.pt` come from one member, with affine `D(t k)` covering it). This supplies split 16's
    hypotheses `hb`, `hY` for a member of a cofiltered system of models of `V`.
18. **feat: the cofiltered category of finitely generated subrings along a system of rings**
    (after: none) — *proved* (inherited). File
    `TauCeti/Algebra/Category/Ring/FGSubringPair.lean` (199 lines), namespace
    `TauCeti.CommRingCat`, imports only Mathlib: for `F : Iᵒᵖ ⥤ CommRingCat` (one universe `u`) and
    finite `s j ⊆ F j`, the structure `FGSubringPair F s` of pairs `(idx, sub)` of an index and a
    finitely generated `ℤ`-subalgebra containing `s idx`; its `Category` instance (a morphism
    `(j', C') ⟶ (j, C)` is `f : j' ⟶ j` with `F.map f.op` mapping `C` into `C'`), `hom_ext`,
    `id_val`, `comp_val`; `ofMaps`, `ofMapsFst`, `ofMapsSnd` (a common refinement of two pairs);
    the instances `IsCofilteredOrEmpty`, `Nonempty` and `isCofiltered`; `ringHom` (the induced
    `C ⟶ C'`) with `ringHom_apply_coe`; the functor `ring : (FGSubringPair F s)ᵒᵖ ⥤ CommRingCat`
    with `ring_map`; `cocone` (a cocone on `F` induces one on `ring F s`) with
    `cocone_ι_app_apply`; and `isColimitCocone` (if every element of `t.pt` comes from some `F j`
    and every element of `F j` mapping to `0` vanishes in a later `F j'`, the induced cocone is a
    colimit). Item (a) of the earlier plan for the extension step (split 22).
19. **feat: affine models of a scheme near a quasi-compact open** (after: 16, 18) — *proved* (inherited). Files:
    - `TauCeti/AlgebraicGeometry/Limits/FiberProductSystem.lean` (162 lines), namespace
      `TauCeti.AlgebraicGeometry.Scheme`: for an open `V ⊆ X` and a cone
      `π : (Functor.const I).obj V ⟶ D`, `fiberProductCone π j` (Mathlib's `CommRingCat.pullbackCone`
      of `Γ(X, ⊤) → Γ(X, V) ← Γ(D j, ⊤)`), `fiberProductCone_condition`, `fiberProductMap` with
      `fiberProductMap_fst`/`_snd`, the functor `fiberProductSystem π : Iᵒᵖ ⥤ CommRingCat`,
      `fiberProductSnd` with `fiberProductSystem_map_fiberProductSnd`, `fiberProductCocone` (to
      `Γ(X, ⊤)` by first projections) with `fiberProductCocone_ι_app`, and
      **`isColimitFiberProductCocone`** (for `π` a limit of a cofiltered diagram of qcqs schemes with
      affine transition maps, `Γ(X, ⊤)` is the colimit of the finitely generated subrings of the
      `P j` containing `s j`; from Mathlib's `exists_appTop_π_eq_of_isLimit` and
      `exists_appTop_map_eq_zero_of_isLimit` through split 18's `isColimitCocone`) and
      **`isLimitSpecFiberProductCocone`** (`Spec Γ(X, ⊤)` is the cofiltered limit of their
      spectra). Item (b) of the earlier plan.
    - `TauCeti/AlgebraicGeometry/Limits/AffineModels.lean` (162 lines), same namespace, imports
      split 16's `SpecFiberProduct.lean`: `fiberProductElem` (the element `(g k, b j k)` of `P j`)
      with its `fst`/`snd` simp lemmas and `fiberProductMap_fiberProductElem`; `toSpecFGSubring`
      (`D j ⟶ Spec C`) with `toSpecFGSubring_naturality` (for `(j', C') ⟶ (j, C)`,
      `D j' ⟶ Spec C' ⟶ Spec C = D j' ⟶ D j ⟶ Spec C`); **`exists_finset_isPullback_fgSubringPair`**
      (finite `s j ∋ (g k, b j k)` such that for every pair `(j, C)`, `D j ⟶ Spec C` is an open
      immersion, `V` is its preimage in `X` (an `IsPullback`), and its image is
      `⨆ k, D((g k, b j k))`; split 16 at every `j`); and **`preimage_opensRange_fgSubringPair`**
      (with the `b j k` compatible with the transition maps, along `(j', C') ⟶ (j, C)` the preimage
      of the image of `D j` is the image of `D j'`).
    About 320 lines.
20. **feat: morphisms between gluings of two schemes along opens** (after: 10) — *proved* (inherited). File `TauCeti/AlgebraicGeometry/Gluing/PushoutMap.lean` (150 lines), namespace
    `TauCeti.AlgebraicGeometry.Scheme`, imports split 10's `Gluing/Pushout.lean`: for gluings
    `U ∪_W V` and `U' ∪_{W'} V'` along open immersions and `u : U' ⟶ U`, `v : V' ⟶ V` compatible
    with `w : W' ⟶ W`, `isPullback_pushout_inl_map` (if `W'` is the preimage of `W` in `V'`, the
    preimage of `U` under `pushout.map` is `U'`), `isPullback_pushout_inr_map` (symmetrically), and
    `pushout_map_of_isZariskiLocalAtTarget` (if `W'` is the preimage of `W` in both, every property
    local at the target passes from `u` and `v` to `pushout.map`); for a span `Uf ⟵ Vf ⟶ Sf` of
    functors `Λ ⥤ Scheme` with open-immersion components, `pushoutFunctor α β` (the gluings, with
    `pushout.map` on morphisms, by Mathlib's `pushout.map_id`/`map_comp`) with
    `pushout_inl_pushoutFunctor_map`/`_inr_` and `pushoutFunctor_map_of_isZariskiLocalAtTarget`
    (split 22 applies it to `IsAffineHom` for the transition maps of `(j, C) ↦ Uⱼ ∪_{Vⱼ} Spec C`).
21. **feat: cofiltered limits of schemes commute with gluing along opens** (after: 3, 4, 10, 20)
    — *proved* (inherited). About 230 lines. Files:
    - `TauCeti/CategoryTheory/Limits/Shapes/Pullback/Cofiltered.lean` (existing file from split 3,
      +32 lines): `CategoryTheory.Limits.IsLimit.isPullback_of_isPullback_naturality`. For a
      natural transformation `α : F ⟶ G` of cofiltered diagrams with pullback naturality squares
      and limit cones `cF`, `cG`, the square `cF.pt ⟶ F i`, `cF.pt ⟶ cG.pt`, `α i`, `cG.π i` is a
      pullback. The proof uses split 3's `IsLimit.pullbackOver` and Mathlib's `IsLimit.hom_isIso`.
    - `TauCeti/AlgebraicGeometry/Restrict.lean` (existing file on `main`, +15 lines):
      `CategoryTheory.IsPullback.opensRange_snd`, the range of the base change of an open immersion
      `f` along `g` is `g ⁻¹ᵁ f.opensRange`.
    - `TauCeti/AlgebraicGeometry/Limits/Pushout.lean` (new, 182 lines), namespace
      `TauCeti.AlgebraicGeometry.Scheme`, imports split 20's `Gluing/PushoutMap.lean`, split 4's
      `Limits/Existence.lean` and `Restrict.lean`. Declarations:
      - `pushoutFunctorCone`: for `X` covered by `U`, `W` and cones `U ⟶ Uf`, `W ⟶ Sf` compatible
        along `U ⊓ W ⟶ Vf`, the cone with point `X` on split 20's `pushoutFunctor α β`.
      - `ι_pushoutFunctorCone_π_app_left`/`_right` (simp, reassoc).
      - `pushoutFunctorInl`, `pushoutFunctorInr` (natural transformations `Uf ⟶ pushoutFunctor`,
        `Sf ⟶ pushoutFunctor`) and their open-immersion instances.
      - `isIso_of_isOpenImmersion_ι_comp`: `φ : X ⟶ L` is an iso if it is an open immersion on two
        opens whose images cover `L` and which are the preimages of their images.
      - **`isLimitPushoutFunctorCone`**: for a span of cofiltered diagrams along open immersions
        with pullback naturality squares and affine transition maps, with `U = lim Uf`,
        `W = lim Sf` and `U ⊓ W` the preimage of `Vf` on both sides, `X` is the limit of the
        gluings. The limit exists by split 4. Over the images of `Uf a₀` and `Sf a₀`, the
        comparison map is an open immersion by the first lemma above, with preimages `U` and `W`
        by split 10's `preimage_opensRange_eq_of_isPullback`.
22. **feat: extending finite-presentation models across a quasi-compact open** (after: 2, 3, 4,
    10, 15, 16, 17, 18, 19, 20, 21) — *proved* (inherited). About 310 lines. Files:
    - `TauCeti/Algebra/Category/Ring/FGSubringPair.lean` (existing file from split 18, +17 lines):
      `FGSubringPair.proj : FGSubringPair F s ⥤ I` (simps) and the instance `initial_proj`
      (initial when `I` is cofiltered).
    - `TauCeti/AlgebraicGeometry/Limits/ModelExtension.lean` (new, 301 lines), namespace
      `TauCeti.AlgebraicGeometry.Scheme`, imports splits 2, 17, 19 and 21. Declarations:
      - `isCompact_ι_preimage`: `U ∩ W` is quasi-compact in `W` when `U`, `W` are quasi-compact
        in a quasi-separated scheme.
      - `exists_finite_iSup_basicOpen_eq`: a quasi-compact open of an affine scheme is a finite
        union of basic opens.
      - `isPullback_opensDiagramι`: the naturality squares of Mathlib's `opensDiagramι` are
        pullbacks.
      - `exists_isLimit_pushout_fgSubringPair`: given models `Vf ⟶ Uf` of `U ∩ W` with compatible
        affine basic covers. Split 19 gives the pairs `(j, C)`, `Spec C` as the limit `W` (split 19's
        `isLimitSpecFiberProductCocone`) and the open immersions `Vⱼ ⟶ Spec C`. Then split 21's
        `isLimitPushoutFunctorCone` makes `Y` the limit of `Uⱼ ∪_{Vⱼ} Spec C`. These schemes are
        qcqs and of finite presentation over `ℤ` (split 10, split 2's
        `locallyOfFinitePresentation_terminal_from_Spec`), with affine transition maps (split 20).
      - **`exists_isLimit_finitePresentation_of_sup_eq_top`** (01ZA induction step): `Y` qcqs,
        `U ⊔ W = ⊤`, `W` affine, `U` a cofiltered limit of qcqs schemes of finite presentation over
        `ℤ` with affine transition maps; then so is `Y`. Mathlib's `exists_preimage_eq` descends
        `U ∩ W` to `V₀` at a stage `i₀`. Split 17 descends the restrictions of a finite basic
        cover of `U ∩ W ⊆ W` to a stage `j₁` over `i₀`, and the rest of the proof works over
        `Over j₁`.
23. **feat: absolute Noetherian approximation of quasi-compact quasi-separated schemes**
    (after: 1–22) — *proved* (inherited), except that it must wait for splits 13–14 to complete the
    target. File `TauCeti/AlgebraicGeometry/Limits/AbsoluteNoetherianApproximation.lean` (new,
    109 lines), namespace `TauCeti.AlgebraicGeometry.Scheme`. It has a private predicate
    `IsApproximable` with `of_iso`, `of_isAffine` (split 2) and `of_sup_eq_top` (split 22), and
    **`exists_isLimit_finitePresentation`** (`noetherian_approximation`, 01ZA): every qcqs scheme
    is the limit of a cofiltered diagram, with affine transition maps, of qcqs schemes of finite
    presentation over `ℤ`. The proof is a `Finset.induction_on` over a finite affine cover. This
    file depends only on splits 2 and 22 (and so on 21 and its prerequisites). It is the target's
    exported theorem, so it is listed after all of 1–22, splits 13–14 included, as the split that
    completes the target. Line count: 109, under the 200-line guideline. Since the split
    completes the target, it is not merged into split 22.

## What remains

Proved: affine-transition limits (existence, affine projections, topology, quasi-compactness,
separation); absolute Noetherian approximation (01ZA), with
`TauCeti.AlgebraicGeometry.Scheme.exists_isLimit_finitePresentation`; descent of finitely
presented schemes and morphisms (01ZM); finite-stage inheritance of isomorphisms, closed and
open immersions, finite, smooth and étale morphisms, and separatedness. Split 12 additionally
proves surjectivity descent and the properness criteria described above.

Still required for the selected target:

- **Flatness (04AI):** prove filtered-colimit descent for flat finitely presented algebras
  (00R6/05LY), then apply the existing two locality reductions and the morphism reduction.
- **Properness (081F):** supply a proper surjective cover of the separated model admitting an
  immersion into a proper ambient model (0202), then apply split 12. The existing conditional
  criteria do not establish that arbitrary finite-type separated schemes have these covers.
  In particular no theorem here assumes a cover and presents itself as unconditional descent.

The pinned Mathlib and main were searched for both missing inputs. Neither is available.
The qcoh-extension supplier does not provide either missing theorem, and no new supplier is
stubbed or silently assumed. Constructing the necessary geometry is future mathematical work,
not an author-round stub substitution.

## Audit and verification

The self-audit checked correctness, scope, reuse, generality, API, naming, placement,
documentation, proof quality and attribution. It caused these changes:

- Extracted `exists_pullbackMap_of_pullbackOver` unchanged from `Morphisms.lean` into its
  canonical home `BaseChange.lean`; this removes a smooth/étale dependency from surjectivity.
- Kept every properness hypothesis visible in theorem names and documentation; no general
  properness claim is made from an assumed Chow cover. Reused Mathlib's closed-immersion
  criterion, properness cancellation, Chevalley theorem and universal-closedness cancellation.
- Required qcqs only for the distinguished member in the constructible and structure-morphism
  surjectivity criteria. The empty scheme is covered by including the empty affine open in
  the basis. No nonempty-scheme hypothesis is introduced.
- Credited the Stacks proof in `Proper.lean` (081F) and the topological limit criterion in
  `Constructible.lean` (081A). Added no compatibility aliases or new definitions.

All eight new theorems are proved without stubs. The generic reduction is a relocation, with
one canonical declaration and all uses resolving through its new home. Verification on 2026-11-08 succeeded: `lake exe cache get` (9111 cached files),
`lake build` (70156 jobs), and `/opt/round/lookahead-check` (`lookahead-check: ok`).
No axioms outside the permitted set were found; there are no supplier placeholders.

## File inventory

These are all Lean files differing from main, with final whole-file line counts. Existing
files may have only small additions; the split descriptions give ownership of shared files.

| File | Lines |
| --- | ---: |
| `TauCeti/Algebra/Category/Ring/FGSubringPair.lean` | 216 |
| `TauCeti/Algebra/Category/Ring/FinitePresentation.lean` | 69 |
| `TauCeti/Algebra/Category/Ring/Pushout.lean` | 73 |
| `TauCeti/AlgebraicGeometry/Gluing/Pushout.lean` | 412 |
| `TauCeti/AlgebraicGeometry/Gluing/PushoutMap.lean` | 150 |
| `TauCeti/AlgebraicGeometry/Limits/AbsoluteNoetherianApproximation.lean` | 109 |
| `TauCeti/AlgebraicGeometry/Limits/AffineDescent.lean` | 83 |
| `TauCeti/AlgebraicGeometry/Limits/AffineModels.lean` | 162 |
| `TauCeti/AlgebraicGeometry/Limits/AffineProperties.lean` | 292 |
| `TauCeti/AlgebraicGeometry/Limits/AffineTransition.lean` | 198 |
| `TauCeti/AlgebraicGeometry/Limits/BaseChange.lean` | 85 |
| `TauCeti/AlgebraicGeometry/Limits/Constructible.lean` | 109 |
| `TauCeti/AlgebraicGeometry/Limits/Descent.lean` | 305 |
| `TauCeti/AlgebraicGeometry/Limits/Existence.lean` | 307 |
| `TauCeti/AlgebraicGeometry/Limits/FiberProductSystem.lean` | 162 |
| `TauCeti/AlgebraicGeometry/Limits/FinitePresentation.lean` | 230 |
| `TauCeti/AlgebraicGeometry/Limits/GlobalSections.lean` | 96 |
| `TauCeti/AlgebraicGeometry/Limits/ModelExtension.lean` | 301 |
| `TauCeti/AlgebraicGeometry/Limits/Morphisms.lean` | 140 |
| `TauCeti/AlgebraicGeometry/Limits/NoetherianApproximation.lean` | 105 |
| `TauCeti/AlgebraicGeometry/Limits/OpenImmersion.lean` | 191 |
| `TauCeti/AlgebraicGeometry/Limits/Proper.lean` | 156 |
| `TauCeti/AlgebraicGeometry/Limits/Pushout.lean` | 182 |
| `TauCeti/AlgebraicGeometry/Limits/QuasiAffine.lean` | 206 |
| `TauCeti/AlgebraicGeometry/Limits/Smooth.lean` | 287 |
| `TauCeti/AlgebraicGeometry/Limits/SpecFiberProduct.lean` | 330 |
| `TauCeti/AlgebraicGeometry/Limits/Surjective.lean` | 67 |
| `TauCeti/AlgebraicGeometry/Limits/ZariskiLocal.lean` | 142 |
| `TauCeti/AlgebraicGeometry/Restrict.lean` | 175 |
| `TauCeti/CategoryTheory/Limits/ConcreteCategory/Filtered.lean` | 51 |
| `TauCeti/CategoryTheory/Limits/Shapes/Pullback/Cofiltered.lean` | 155 |
| `TauCeti/CategoryTheory/MorphismProperty/Limits.lean` | 143 |
| `TauCeti/RingTheory/Localization/Away/Pullback.lean` | 82 |
| `LOOKAHEAD.md` | 508 |
