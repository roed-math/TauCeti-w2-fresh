<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"noetherian-approximation","main":"52f9d081237dadaf6d4eae13629281f7faa37d54","status":"partial","suppliers":["qcoh-extension"],"splits":[{"n":1,"after":[],"title":"feat: separation, affineness and underlying space of limits of schemes with affine transition maps"},{"n":2,"after":[],"title":"feat: Noetherian approximation of affine schemes"},{"n":3,"after":[],"title":"feat: descent of morphisms and isomorphisms of finitely presented schemes along cofiltered limits"},{"n":4,"after":[3],"title":"feat: existence of cofiltered limits of schemes with affine transition maps"},{"n":5,"after":[],"title":"feat: descent of finitely presented affine schemes along cofiltered limits"},{"n":6,"after":[3,5],"title":"feat: closed immersions and finite morphisms are inherited from a finite stage"},{"n":7,"after":[3,6],"title":"feat: open immersions are inherited from a finite stage"},{"n":8,"after":[3,5,6,7],"title":"feat: descent of finitely presented schemes and of flatness, smoothness and properness to a finite stage"},{"n":9,"after":[2,4,8],"title":"feat: extending finite-presentation models across a quasi-compact open"},{"n":10,"after":[1,2,3,4,5,6,7,8,9],"title":"feat: absolute Noetherian approximation of quasi-compact quasi-separated schemes"}]}-->
# Lookahead: `noetherian-approximation` (SchemeAndStackFoundations §0.9)

Built on `main` at `52f9d08123`. Status: **partial**.

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
consumes it. No proved declaration on this branch uses the stub yet: it is consumed by split 9
(extending a finite-type quasi-coherent ideal sheaf, cutting out the closure of a
finite-presentation model over an open, from `U` to `X`).

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
   - `TauCeti/AlgebraicGeometry/Limits/FinitePresentation.lean` (193 lines):
     `exists_map_comp_eq_of_isLimit`, `exists_π_app_comp_eq_of_isLimit` (01ZC over `ℤ`),
     `exists_pullbackMap_comp_eq_of_isLimit` (01ZM, descent of morphisms),
     `exists_isIso_pullbackMap_of_isLimit` (081E, isomorphisms).
4. **feat: existence of cofiltered limits of schemes with affine transition maps** (after: 3) —
   *proved*. File `TauCeti/AlgebraicGeometry/Limits/Existence.lean` (307 lines):
   `hasLimit_of_isAffine` and the instance `hasLimit_of_isAffineHom : HasLimit D` (01YW). It needs
   split 3 only for `Pullback/Cofiltered.lean`.
5. **feat: descent of finitely presented affine schemes along cofiltered limits** (after: none) —
   *proved* (this session). Files:
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
   — *proved* (this session). Files:
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
   - `TauCeti/AlgebraicGeometry/Limits/ZariskiLocal.lean` (136 lines):
     `exists_pullback_fst_of_isLimit_of_isZariskiLocalAtTarget` (any property local at the target and
     stable under base change that is inherited over cofiltered limits of affine schemes is inherited
     over cofiltered limits of quasi-compact schemes with affine transition maps, via
     `AlgebraicGeometry.isLimitOpensCone` on a finite affine cover of the member), and the final
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
8. **feat: descent of finitely presented schemes and of flatness, smoothness and properness to a
   finite stage** (after: 3, 5, 6, 7) — *remaining*. The object half of 01ZM in general (glue the
   affine-local models of split 5 over a finite affine cover: descend the pairwise intersections
   with split 7's `exists_preimage_pullbackMap_eq_of_isLimit`, the gluing isomorphisms and cocycle
   conditions with split 3, and glue two pieces at a time with Mathlib's pushouts of open
   immersions), and the properties flat (04AI), smooth (0C0C), étale (07RP), proper (081F); the
   latter can reuse split 6's `exists_pullback_fst_of_isLimit_of_isZariskiLocalAtTarget` for the
   reduction to affine members. Likely two or three PRs.
9. **feat: extending finite-presentation models across a quasi-compact open** (after: 2, 4, 8) —
   *remaining*. Stacks 01Z7, 01Z9, 07RN: given `X = U ∪ W`, `W` affine, and `U` a limit of f.p.
   `ℤ`-schemes, glue an f.p. model over `W`; consumes the stub
   `exists_isFiniteType_mono_restrict_iso` to extend the finite-type ideal sheaf. New file
   `Limits/NoetherianApproximation/Extension.lean`.
10. **feat: absolute Noetherian approximation of quasi-compact quasi-separated schemes**
    (after: 1–9) — *remaining*. `noetherian_approximation` (01ZA) by induction on the number of
    affines in a cover, starting from split 2; completes the target.

## What remains

Proved: existence of cofiltered limits of schemes with affine transition maps (01YW) with the
separatedness/quasi-separatedness and (quasi-)affineness criteria and `|lim Xᵢ| = lim |Xᵢ|` (0CUF),
which with Mathlib's `Scheme.compactSpace_of_isLimit` and `isAffineHom_π_app` make up
`affine_transition_limits`; the affine case of absolute Noetherian approximation; for
`finite_presentation_limits`: descent of morphisms (01ZM, morphism half), the affine and
affine-local cases of descent of finitely presented schemes (01ZM, object half), and inheritance
from a finite stage of isomorphisms (081E), closed immersions (01ZP), finite morphisms (01ZO) and
open immersions (0EUU) over cofiltered limits of quasi-compact quasi-separated schemes with affine
transition maps, and the descent of quasi-compact opens of base changes (01Z4). Remaining: the
general object half of 01ZM (gluing), the properties flat, smooth, étale and proper (split 8), the
extension step across an open (split 9, the only consumer of the `qcoh-extension` stub), and the
qcqs induction for `noetherian_approximation` (01Z7, 01Z9, 07RN, 01ZA; split 10).
