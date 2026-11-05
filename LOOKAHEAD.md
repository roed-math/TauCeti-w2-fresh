<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"noetherian-approximation","main":"85f3eb5579df5ca44ba8cd0921d614b41ab72174","status":"partial","suppliers":["qcoh-extension"],"splits":[{"n":1,"after":[],"title":"feat: separation, affineness and underlying space of limits of schemes with affine transition maps"},{"n":2,"after":[],"title":"feat: Noetherian approximation of affine schemes"},{"n":3,"after":[],"title":"feat: descent of morphisms and isomorphisms of finitely presented schemes along cofiltered limits"},{"n":4,"after":[3],"title":"feat: existence of cofiltered limits of schemes with affine transition maps"},{"n":5,"after":[],"title":"feat: descent of finitely presented affine schemes along cofiltered limits"},{"n":6,"after":[3,5],"title":"feat: closed immersions and finite morphisms are inherited from a finite stage"},{"n":7,"after":[3,6],"title":"feat: open immersions are inherited from a finite stage"},{"n":8,"after":[2,3,6],"title":"feat: smooth and étale morphisms are inherited from a finite stage"},{"n":9,"after":[3,6,7,8],"title":"feat: closed immersions, finite, smooth and étale morphisms over a member, and separatedness, are inherited from a finite stage"},{"n":10,"after":[],"title":"feat: gluing two schemes along an open subscheme"},{"n":11,"after":[1,3,5,6,7,10],"title":"feat: descent of schemes of finite presentation along cofiltered limits"},{"n":12,"after":[3,5,6,7,8,9,11],"title":"feat: flatness and properness are inherited from a finite stage"},{"n":13,"after":[],"title":"feat: quasi-compact opens of finite type over ℤ in an affine scheme come from a finitely generated subring"},{"n":14,"after":[1,2,3,4,5,6,7,10,11,13],"title":"feat: extending finite-presentation models across a quasi-compact open"},{"n":15,"after":[1,2,3,4,5,6,7,8,9,10,11,12,13,14],"title":"feat: absolute Noetherian approximation of quasi-compact quasi-separated schemes"}]}-->
# Lookahead: `noetherian-approximation` (SchemeAndStackFoundations §0.9)

Built on `main` at `85f3eb5579d` (merged in this session; no conflicts, and `main` still has
no declaration of the stubbed statement). Status: **partial**.

The roadmap pins no Lean forms for §0.9 in `Suggested.lean`; the target is specified by the
README only (`affine_transition_limits`, `noetherian_approximation`,
`finite_presentation_limits`).

## Stubbed declarations

### `qcoh-extension`: finite-type submodule extension (Stacks 01PF)

`Suggested.lean` pins no Lean signature for `qcoh_extension` (`grep qcoh Suggested.lean` is
empty); its README §0.4 states it in prose: "a finite-type quasi-coherent submodule of `j^*G` is
`j^*G'` for a finite-type quasi-coherent submodule `G' ⊆ G` (Lemma 28.23.2 (01PF))". Parts (1)
and (2) of 01PE have since landed on `main` (PR #22951) as
`AlgebraicGeometry.Scheme.Modules.exists_isQuasicoherent_restrict_iso` and
`AlgebraicGeometry.Scheme.Modules.exists_mono_restrict_iso_of_isQuasicoherent` in
`TauCeti/AlgebraicGeometry/Modules/Quasicoherent/Extension.lean`, so they are not stubbed. The
supplier's open PR #26972 ("finite type of sheaves of modules can be checked on an open cover")
adds `SheafOfModules.IsFiniteType.of_coversTop` and
`isFiniteType_of_isFiniteType_restrict(_affineOpens)`, prerequisites of 01PF, but not 01PF itself.
The stub follows main's form of 01PE part (2), adding the finite-type hypotheses and conclusion and
qcqs of `X` (which 01PF needs and the README states):

```lean
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_restrict_iso
    [QuasiCompact j] [CompactSpace X] [QuasiSeparatedSpace X] {G : X.Modules}
    [G.IsQuasicoherent] {F : U.Modules} [F.IsQuasicoherent] [F.IsFiniteType]
    (i : F ⟶ G.restrict j) [Mono i] :
    ∃ (G' : X.Modules) (_ : G'.IsQuasicoherent) (_ : G'.IsFiniteType) (i' : G' ⟶ G) (_ : Mono i')
      (e : G'.restrict j ≅ F), (Scheme.Modules.restrictFunctor j).map i' = e.hom ≫ i
```

(in `namespace TauCeti.AlgebraicGeometry` with `variable {U X : Scheme.{u}} (j : U ⟶ X)
[IsOpenImmersion j]`, as on `main`). Differences from main's
`exists_mono_restrict_iso_of_isQuasicoherent`: the added
`[CompactSpace X] [QuasiSeparatedSpace X] [F.IsFiniteType]` hypotheses and `G'.IsFiniteType`
conclusion (the content of 01PF); the "isomorphism over `V`" clause is dropped since no split
consumes it. No proved declaration on this branch uses the stub yet: it is consumed by split 14
(extending a finite-type quasi-coherent ideal sheaf, cutting out the closure of a
finite-presentation model over an open, from `U` to `X`).

Rechecked on 2026-11-04: the supplier's open PR is now #27979 ("feat: finite-type quasi-coherent
submodules on affine schemes"). Its diff adds the affine input of 01PF
(`AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_isIso_restrict` and its basic-open
cases, `isIso_of_mono_of_forall_isFiniteType_factors`, `isFiniteType_of_epi`, ...) in
`TauCeti/AlgebraicGeometry/Modules/Quasicoherent/FiniteType.lean`, but not 01PF itself; its
description says the induction (01PF, then 0G41/01PI) remains. So the stub is unchanged: it is
still the statement 01PF, which a later PR of the supplier will land. Rechecked on 2026-11-05:
#27979 is still open and `main` (`85f3eb5579d`) has no `exists_isFiniteType_mono_restrict_iso`;
stub unchanged.

## Splits

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
   - `TauCeti/AlgebraicGeometry/Limits/BaseChange.lean` (50 lines): instances passing affine
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
7. **feat: open immersions are inherited from a finite stage** (after: 3, 6) — *proved* (this
   session). Files:
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
   - `TauCeti/AlgebraicGeometry/Limits/Morphisms.lean` (167 lines):
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
     one ingredient of 081F). About 195 lines.
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
12. **feat: flatness and properness are inherited from a finite stage** (after: 3, 5, 6, 7, 8, 9, 11)
    — *remaining*. Flat (04AI): Mathlib has no descent of flatness along filtered colimits of rings,
    so this needs the ring theory of Stacks 10.168 (00R6/05LY: a flat finitely presented algebra over a
    filtered colimit is flat at a finite stage); then the affine case globalises by split 6's
    `exists_pullback_fst_of_isLimit_of_isZariskiLocalAtTarget` and split 8's
    `exists_pullback_fst_of_isLimit_of_isZariskiLocalAtSource`. Proper (081F): separatedness is split
    9, so universal closedness remains, which Stacks reaches through Chow's lemma. Morphism forms
    follow from split 9's `exists_pullbackMap_of_pullbackOver`. Likely two PRs.
13. **feat: quasi-compact opens of finite type over ℤ in an affine scheme come from a finitely
    generated subring** (after: none) — *proved* (2026-11-05). File
    `TauCeti/AlgebraicGeometry/Limits/QuasiAffine.lean` (183 lines), namespace
    `TauCeti.AlgebraicGeometry`, imports only Mathlib:
    `finiteType_intCastRingHom_of_locallyOfFiniteType_terminal_from_Spec` (if `Spec R` is locally of
    finite type over the terminal scheme, `ℤ → R` is of finite type; the finite-type converse of
    split 2's `locallyOfFinitePresentation_terminal_from_Spec`),
    `exists_finset_isOpenImmersion_away_comp_SpecMap_val` (if `R_f` is of finite type over `ℤ`, a
    finite `s ∋ f` makes `R_f` the localization away from `f` of every subring `A ⊇ s`, so
    `Spec R_f ⟶ Spec R ⟶ Spec A` is an open immersion), and
    **`Scheme.exists_finset_isOpenImmersion_comp_SpecMap_val`** (Stacks 01Z7): for an open immersion
    `ι : W ⟶ Spec R` with `W` quasi-compact and locally of finite type over `ℤ`, there is a finite
    `s ⊆ R` such that `ι ≫ Spec.map A.val` is an open immersion for every subring `A ⊇ s`; with
    `A = ℤ[s]` this is the first clause of 01Z7, and cofinality of such `A` is its "moreover". The
    proof covers `range ι` by finitely many `D(f)`, so injectivity of `W ⟶ Spec A` follows from
    `D_R(f)` being the preimage of `D_A(f)`, and it is locally an open immersion by
    `IsOpenImmersion.of_isLocalization`.
14. **feat: extending finite-presentation models across a quasi-compact open** (after: 1, 2, 3, 4, 5,
    6, 7, 10, 11, 13) — *remaining*. Stacks 01Z9, 07RN: given `X = U ∪ W`, `W = Spec R` affine, and
    `U` a cofiltered limit of f.p. `ℤ`-schemes `Uᵢ` with affine transition maps, produce the same for
    `X`. Split 10's gluing (`isPullback_pushout_desc_of_isPullback`, the pushout instances) and split
    11's `isPullback_lift_of_isPullback` / `exists_isPullback_of_isLimit_of_le` are the gluing and
    rebasing tools. A route sketched this session (not yet checked in Lean) that needs only split 13 and
    Mathlib, no stub: put
    `V = U ∩ W`; descend `V` to quasi-compact opens `Vⱼ ⊆ Uⱼ` (01Z4), quasi-affine for large `j`
    (Mathlib's `Scheme.exists_isQuasiAffine_of_isLimit`); cover `V` by `D_W(g_k)`, `g_k ∈ R`, and lift
    `g_k|_V` to `b_k ∈ Γ(Vⱼ)` (`Γ(V) = colim Γ(Vⱼ)`, Mathlib's `nonempty_isColimit_Γ_mapCocone`);
    then `Pⱼ = R ×_{Γ(V)} Aⱼ` for a f.g. `Aⱼ ⊆ Γ(Vⱼ)` from split 13 has `(Pⱼ)_{(g_k, b_k)} ≅ (Aⱼ)_{b_k}`,
    so `Vⱼ ↪ Spec Pⱼ` is open, split 13 again gives a f.g. `C ⊆ Pⱼ`, and `Xⱼ,C = Uⱼ ∪_{Vⱼ} Spec C`
    (split 10) has limit `X` (over pairs `(j, C)`) because `colim Pⱼ = R ×_{Γ(V)} Γ(V) = R` when the `Aⱼ` exhaust
    `Γ(V)`. The route planned in earlier sessions instead
    extends a finite-type quasi-coherent ideal sheaf across `U ⊆ X`, consuming the stub
    `exists_isFiniteType_mono_restrict_iso` (01PF, through Properties 28.22.13). New file
    `Limits/NoetherianApproximation/Extension.lean`.
15. **feat: absolute Noetherian approximation of quasi-compact quasi-separated schemes**
    (after: 1–14) — *remaining*. `noetherian_approximation` (01ZA) by induction on the number of
    affines in a cover, starting from split 2; completes the target.

## What remains

Proved: existence of cofiltered limits of schemes with affine transition maps (01YW) with the
separatedness/quasi-separatedness and (quasi-)affineness criteria and `|lim Xᵢ| = lim |Xᵢ|` (0CUF),
which with Mathlib's `Scheme.compactSpace_of_isLimit` and `isAffineHom_π_app` make up
`affine_transition_limits`; the affine case of absolute Noetherian approximation; for
`finite_presentation_limits`: descent of schemes of finite presentation (01ZM, both halves: objects
by split 11, morphisms by split 3), and inheritance from a finite stage of isomorphisms (081E),
closed immersions (01ZP), finite morphisms (01ZO), open immersions (0EUU), smooth morphisms (0C0C)
and étale morphisms (07RP), all in the morphism form, and of separatedness, over cofiltered limits
of quasi-compact quasi-separated schemes with affine transition maps, and the descent of
quasi-compact opens of base changes (01Z4); gluing of schemes along opens with base change
(split 10). Also proved: Stacks 01Z7 (split 13), the first lemma of absolute Noetherian approximation.
Remaining: the properties flat and proper in `finite_presentation_limits` (split 12;
for proper only universal closedness), the extension step across an open (split 14, 01Z9/07RN;
on the Stacks route the only consumer of the `qcoh-extension` stub), and the qcqs induction for
`noetherian_approximation` (01ZA; split 15).
