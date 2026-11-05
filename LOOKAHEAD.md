<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"is-thickening","main":"e8758b7b2f82b9b1c3f33b992ab8f499b510240f","status":"partial","suppliers":["equiv-sheaf-h"],"splits":[{"n":1,"after":[],"title":"feat: formally smooth and formally étale morphisms of schemes"},{"n":2,"after":[1],"title":"feat: formal smoothness of Spec.map and of affine space"},{"n":3,"after":[],"title":"feat: thickenings of order n + 2 factor through first-order thickenings"},{"n":4,"after":[1,2],"title":"feat: étale iff formally étale"},{"n":5,"after":[1,2],"title":"feat: lifts into affine space along a closed immersion form a torsor"},{"n":6,"after":[1,2,4],"title":"feat: the sheaf of lifts along a first-order thickening"},{"n":7,"after":[2],"title":"feat: lifts along a first-order thickening of an affine scheme form a torsor under derivations"},{"n":8,"after":[1,2,4,6,7],"title":"feat: sections of the sheaf of lifts over affine opens"},{"n":9,"after":[1,2,4,5,6,7,8],"title":"feat: the torsor of lifts does not depend on the affine chart"},{"n":10,"after":[],"title":"feat: differences of morphisms of schemes on sections"},{"n":11,"after":[1,2,4,6,7,8,10],"title":"feat: differences of sections of the sheaf of lifts"},{"n":12,"after":[],"title":"feat: the sheaf of derivations into the ideal of a thickening"},{"n":13,"after":[1,2,4,6,7,8,10,11,12],"title":"feat: the sheaf of derivations acts simply transitively on the sheaf of lifts"},{"n":14,"after":[1,2,4,6,7,8,10,11,12,13],"title":"feat: the torsor of lifts along a first-order thickening"},{"n":15,"after":[12],"title":"feat: the sheaf of derivations into the ideal of a thickening is a sheaf of modules"},{"n":16,"after":[],"title":"feat: derivations into a localized module"},{"n":17,"after":[1,2,4,6,7,8,10,11,12,13,14,15],"title":"feat: lifts along a first-order thickening when the sheaf of derivations has no H¹"},{"n":18,"after":[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17],"title":"feat: smooth iff formally smooth and the torsor of lifts"}]}-->

# Lookahead: SchemeAndStackFoundations §4.1 `is-thickening` (partial)

Roadmap: `SchemeAndStackFoundations/README.md`, Layer 4, §4.1 *Thickenings, formally smooth and
étale morphisms, the lifting criterion, torsors of lifts*. Built on `main` at
`e8758b7b2f82b9b1c3f33b992ab8f499b510240f`.

## Stubs: `equiv-sheaf-h`

`TauCeti/Lookahead/IsThickening/Stubs.lean` holds one declaration, consumed only by split 17
(`LiftSheaf/Cohomology.lean`).

* **`CategoryTheory.Sheaf.NonabelianH1.equivSheafH`** (§2.3, open PR #27237; carrier
  `Sheaf.NonabelianH1` merged as #22627).
  * `Suggested.lean` signature: **none**. `equivSheafH` is pinned only in the README prose of §2.3:
    "the comparison `equivSheafH`: for an abelian sheaf `G`, `NonabelianH1 J G ≃ Sheaf.H G 1`
    sending `mk P` to the class of the extension `0 → G → P̃ → ℤ → 0` built from `P`, compatible
    with `map`, `pullback` and `connecting`", and §2.4 uses it as `NonabelianH1 J (toGrpSheaf E.X₃)`
    for an abelian sheaf `E.X₃`. PR #27237 (*feat: connecting map of an extension of sheaves of
    groups*, the single new file `TauCeti/CategoryTheory/Sites/NonabelianCohomology/Connecting.lean`)
    does not contain it. Rechecked 2026-11-05 07:00 UTC against `main` `e8758b7b2f8`: #27237 and
    #22428 are both still open.
  * Stub as stated (in main's namespace `CategoryTheory.Sheaf.NonabelianH1` of `Torsor.lean`):

    ```lean
    noncomputable def equivSheafH (G : Sheaf J AddCommGrpCat.{w})
        [J.HasSheafCompose (AddCommGrpCat.toCommGrp.{w} ⋙ forget₂ CommGrpCat.{w} GrpCat.{w})]
        [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] :
        NonabelianH1 ((sheafCompose J
          (AddCommGrpCat.toCommGrp.{w} ⋙ forget₂ CommGrpCat.{w} GrpCat.{w})).obj G) ≃ G.H 1 :=
      sorry
    ```
  * Differences and reasons. (1) The README's `toGrpSheaf G` (the abelian sheaf seen as a sheaf
    of groups) is defined nowhere, neither in `Suggested.lean` nor in #27237, so the stub spells it
    out as `sheafCompose` along `AddCommGrpCat.toCommGrp ⋙ forget₂ CommGrpCat GrpCat` (an
    equivalence followed by a limit-preserving forgetful functor), the construction split 14 already
    uses for `liftDerivationGrpSheaf`. When the supplier lands with its own `toGrpSheaf`, the port
    rewrites `liftDerivationGrpSheaf` as `toGrpSheaf (liftDerivationSheaf f i a)` (or keeps it as an
    abbreviation of that). (2) The `HasSheafCompose`, `HasSheafify` and `HasExt` instance arguments
    are those `sheafCompose` and Mathlib's `Sheaf.H` need; on `Opens.grothendieckTopology T'` all
    are found by instance search. (3) The stub states only the bijection; the consumer uses nothing
    else (`Subsingleton (G.H 1)` transfers along it), so no API about its values (the class of
    `mk P`, compatibilities with `map`, `pullback`, `connecting`) is stubbed.

## What is proved (all sorry-free, `lake build` green)

The roadmap's Lean pins `Formal.IsThickening`, `Formal.FormallySmooth`, etc. under
`TauCetiRoadmap.SchemeAndStackFoundations.Formal`. The neighbouring code on `main` (#23574's
`TauCeti.AlgebraicGeometry.IsThickening` / `IsFirstOrderThickening`) does not use a `Formal`
namespace, so the new classes sit next to it as `TauCeti.AlgebraicGeometry.FormallySmooth` and
`TauCeti.AlgebraicGeometry.FormallyEtale`. Their fields are verbatim the pinned ones:

```lean
class FormallySmooth {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  exists_lift : ∀ {T T' : Scheme.{u}} [IsAffine T'] (i : T ⟶ T') [IsFirstOrderThickening i]
    (g : T ⟶ X) (h : T' ⟶ S), g ≫ f = i ≫ h → ∃ l : T' ⟶ X, i ≫ l = g ∧ l ≫ f = h
class FormallyEtale {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  existsUnique_lift : … → ∃! l : T' ⟶ X, i ≫ l = g ∧ l ≫ f = h
```

How this matches the roadmap API (README §4.1):

| Roadmap item | Status on this branch |
| --- | --- |
| `IsThickening`, `IsFirstOrderThickening`, `.isThickening`, `specMap_iff`, `.pullback`, `.isUniversalHomeomorphism` | already on `main` (#23574) |
| *IsThickening.homeomorph* | covered on `main` by `IsUniversalHomeomorphism.homeomorph i` through the instance `IsThickening.isUniversalHomeomorphism`; a second name would be a forbidden alias |
| *IsThickening.factor_firstOrder* | **proved**: `IsThickening.factor_firstOrder` (split 3) |
| `FormallySmooth`, `FormallyEtale` | **defined** (split 1) |
| `FormallyUnramified` (Mathlib's) | `formallyUnramified_iff_hom_ext` (split 4), the lifting form of Mathlib's `FormallyUnramified.hom_ext`/`of_hom_ext` |
| *formallySmooth_specMap_iff* | **proved** as `FormallySmooth.SpecMap_iff`, plus `FormallyEtale.SpecMap_iff` (split 2), following main's `IsThickening.SpecMap_iff` naming |
| `.comp`, `.pullback` | **proved** for both classes, plus `IsStableUnderBaseChange`, `IsMultiplicative`, `RespectsIso` (split 1) |
| *FormallyEtale.of_isOpenImmersion* | **proved** (split 1) |
| *formallyEtale_iff* | **proved** (split 4) |
| *FormallySmooth.iff_affineLocally* | ⇒ **proved** as `FormallySmooth.formallySmooth_appLE` (split 4); ⇐ remains (needs gluing, see below) |
| *FormallySmooth.of_smooth*, `smooth_iff_formallySmooth` | ⇐ (formally smooth + LFP ⇒ smooth) **proved** as `AlgebraicGeometry.Smooth.of_formallySmooth` (split 4); ⇒ **proved for affine `X`, `S`** as `FormallySmooth.of_smooth_of_isAffine`, **locally** as `exists_local_lift_of_smooth` (split 4), and **reduced to the quasi-coherence of `liftDerivationModule f i a`** by `exists_lift_of_isQuasicoherent` (split 17); the general ⇒ remains |
| `etale_iff_formallyEtale` | **proved** (split 4), together with the instance `FormallyEtale.of_etale` |
| `smooth_lifting_torsor` | affine local model **proved** (split 7): `Ideal.derivationToSquareZeroAddTorsor` (lifts of `A → B ⧸ I` to `B`, for `I ^ 2 = ⊥`, are a torsor under `Der_R(A, I)`), `Ideal.nonempty_liftOfQuotient`/`subsingleton_liftOfQuotient`, `liftStructEquivLiftOfQuotient` (the lifts in a square of affine schemes along a closed immersion `i` are the algebra lifts `Γ(X, ⊤) →ₐ[Γ(S, ⊤)] Γ(T', ⊤)` of `Γ(X, ⊤) → Γ(T', ⊤) ⧸ ker i.appTop`) and `liftStructAddTorsor` (along a first-order thickening `i` of an affine scheme, the lifts in a square with `X`, `S` affine form a torsor under `Der_{Γ(S, ⊤)}(Γ(X, ⊤), ker i.appTop)`); affine space case **proved**: instance `affineSpaceLiftAddTorsor` (split 5); étale uniqueness **proved** as instance `FormallyEtale.subsingleton_liftStruct` (split 5) and, sheaf-wise, as instance `subsingleton_liftSheaf` (split 6); the **sheaf of lifts** `liftSheaf` is **defined**, with `nonempty_liftSheaf_top_iff` (a lift exists iff the sheaf has a global section) and `liftSheaf_coversTop` (locally nonempty for smooth `f`) (split 6); its sections over an affine open `W` of `T'` are **read as lifts in affine squares** (`liftSheafObjEquivLiftStruct`), so that `liftStructAddTorsor` acts on them, compatibly with restriction to a smaller affine `W' ⊆ W` (`liftSheafObjEquivLiftStruct_map_vadd`/`_map_vsub`) and independently of the affine chart `U ⊆ X` (`liftSheafObjEquivLiftStruct_vsub_apply_homOfLE`) (split 8); the local torsors **do not depend on the affine chart** `U' ⊆ U` of `X`: derivations of `Γ(U)` and of `Γ(U')` into the ideal are identified by `Derivation.compAlgebraMapEquiv` (`Γ(U) → Γ(U')` is formally étale) and the two actions agree (`liftSheafObjEquivLiftStruct_vsub_homOfLE`, `_symm_vadd_homOfLE`, `_symm_vadd_eq_compAlgebraMapEquiv_symm`) (split 9); the **difference of two sections is described chart-free** by `Scheme.Hom.appLESub` (split 10), a derivation along the first-order thickening valued in the ideal sheaf that detects equality (`liftSheaf_ext_iff`, `liftSheaf_eq_of_appLESub_eq`) and equals the affine torsor's `-ᵥ` over every affine chart, so that two affine charts with non-affine intersection give the same derivation (`liftSheafObjEquivLiftStruct_vsub_apply_eq_appLESub`, `_vsub_apply_eq_of_map_eq`) (split 11); the **group sheaf** `Hom(a^* Ω_{X/S}, I)` is **defined chart-free** as the sheaf of abelian groups `liftDerivationSheaf f i a` on `T'` (families `Γ(X, U) →+ Γ(T', V)` that restrict, land in the ideal of `i`, kill `S` and satisfy the Leibniz rule along local lifts), with its sheaf property `liftDerivationPresheaf_isSheaf` (split 12); the **difference map** into it, `liftSheafSub l₁ l₂`, is **defined**, additive, vanishing exactly on the diagonal, injective in the first argument and compatible with restriction, and **surjective** (`exists_liftSheafSub_eq`): `liftDerivationSheaf` acts simply transitively on `liftSheaf` (split 13); and **packaged** as main's `Sheaf.Torsor`, `liftTorsor`, with **obstruction class** `liftObstruction` in `NonabelianH1` whose vanishing is equivalent to the existence of a lift (`liftObstruction_eq_one_iff`) (split 14); uniqueness for étale `f` is `subsingleton_liftSheaf` (split 6); the sheaf of derivations is a **sheaf of `𝒪_{T'}`-modules** `liftDerivationModule f i a` with underlying abelian sheaf `liftDerivationSheaf f i a` (split 15); through the stubbed `equivSheafH` the class vanishes when `Sheaf.H (liftDerivationSheaf f i a) 1` does, so **a lift exists when `T'` is affine and `liftDerivationModule f i a` is quasi-coherent** (`exists_lift_of_isQuasicoherent`, by main's Serre vanishing; split 17); the algebraic input for that quasi-coherence, **derivations into a localized module are the localized derivations** when `Ω[A⁄R]` is finitely presented, is proved (`LinearMap.isLocalizedModule_compDerRestrictScalars`, split 16); the quasi-coherence of `liftDerivationModule f i a` itself remains |
| checks *isFirstOrderThickening_dualNumber*, *_id*, `not_isFirstOrderThickening_cube`, `not_isThickening_origin` | already on `main` |
| checks *formallySmooth_affineSpace*, *formallyEtale_id*, `not_formallySmooth_closedPoint` | **proved**: instance `FormallySmooth.affineSpace`, an `example`, and `not_formallySmooth_origin` (split 2) |
| check `formallyUnramified_iff_mathlib` | **proved** as `formallyUnramified_iff_hom_ext` (split 4) |
| check `lifting_torsor_test_affine_space` | **proved** as an `example` in the examples file (split 5) |

`IsThickening.factor_firstOrder` reads "thickening of order `m`" as a closed immersion whose ideal
sheaf has vanishing `(m + 1)`-st power, so that order 1 is first order:

```lean
theorem IsThickening.factor_firstOrder (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ)
    (hi : i.ker ^ (n + 3) = ⊥) :
    ∃ (Y : Scheme.{u}) (j : Z ⟶ Y) (k : Y ⟶ X), j ≫ k = i ∧ IsClosedImmersion j ∧
      j.ker ^ (n + 2) = ⊥ ∧ IsFirstOrderThickening k
```

## Split plan

1. **`feat: formally smooth and formally étale morphisms of schemes`** — after: none.
   New file `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/Basic.lean` (226 lines):
   `FormallySmooth`, `FormallyEtale`, `FormallyEtale.formallySmooth`, `FormallyEtale.hom_ext`,
   `FormallyEtale.of_formallySmooth`, and for both classes `of_isIso`, `comp`, `of_isPullback`,
   `pullback_fst`, `pullback_snd`, `isStableUnderBaseChange`, `isStableUnderComposition`,
   `isMultiplicative`, `respectsIso`, plus `FormallyEtale.of_isOpenImmersion`.
2. **`feat: formal smoothness of Spec.map and of affine space`** — after: 1.
   `TauCeti/RingTheory/RingHom/Smooth.lean` (39 lines, `RingHom.FormallySmooth.exists_lift`),
   `TauCeti/RingTheory/RingHom/Unramified.lean` (35 lines, `RingHom.FormallyUnramified.ext`),
   additions to `TauCeti/AlgebraicGeometry/Morphisms/Thickening.lean`
   (`IsFirstOrderThickening.isNilpotent_ker`, `appTop_surjective`, `ker_appTop_sq_eq_bot`,
   `SpecMap_mk`; about 33 lines), `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/Affine.lean`
   (142 lines: `FormallySmooth.SpecMap_iff`, `FormallyEtale.SpecMap_iff`, instance
   `FormallySmooth.affineSpace`), and `TauCeti/Examples/AlgebraicGeometry/Morphisms/FormallySmooth.lean`
   (50 lines: `formallyEtale_id` and affine-space examples, `not_formallySmooth_origin`).
   About 300 lines.
3. **`feat: thickenings of order n + 2 factor through first-order thickenings`** — after: none.
   `IsThickening.factor_firstOrder` in `TauCeti/AlgebraicGeometry/Morphisms/Thickening.lean`
   (about 40 lines, with its docstring bullet). It is independent of splits 1, 2 and 4 and can be
   opened at once; it touches the same file as split 2, in a different place.
4. **`feat: étale iff formally étale`** — after: 1, 2.
   `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/Local.lean` (118 lines:
   `formallyUnramified_iff_hom_ext`, instance `FormallyEtale.formallyUnramified`,
   `formallyEtale_iff`, `FormallySmooth.formallySmooth_appLE`, `FormallyEtale.formallyEtale_appLE`)
   and `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/Criterion.lean` (204 lines:
   `AlgebraicGeometry.Smooth.of_formallySmooth`, `AlgebraicGeometry.Etale.of_formallyEtale`,
   instance `FormallyEtale.of_etale`, `etale_iff_formallyEtale`, `exists_affine_chart` (along a
   thickening `i : T ⟶ T'`, the affine opens `W ⊆ T'` with affine opens `U ⊆ X`, `V ⊆ S` such
   that `a (i⁻¹ W) ⊆ U`, `h W ⊆ V`, `f U ⊆ V` form a basis; added this round, and
   `exists_local_lift_of_smooth` now uses it instead of choosing the charts inline)). About 320
   lines.
5. **`feat: lifts into affine space along a closed immersion form a torsor`** — after: 1, 2.
   New file `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/Lifts.lean` (125 lines). Lifts are
   Mathlib's `CommSq.LiftStruct` (no new structure). Declarations: instances
   `FormallySmooth.hasLift` and `FormallyEtale.subsingleton_liftStruct` (existence and uniqueness
   of lifts in a square along an affine first-order thickening), `affineSpaceLift_appTop_appTop_coord`,
   `affineSpaceLift_ext`, the `VAdd`/`VSub` instances `affineSpaceLiftVAdd`/`affineSpaceLiftVSub` of `n → RingHom.ker i.appTop` on lifts into
   `𝔸(n; S)` with simp lemmas `affineSpaceLift_vadd_appTop_coord`, `affineSpaceLift_coe_vsub_apply`,
   instance `affineSpaceLift_hasLift`, and instance `affineSpaceLiftAddTorsor` (along a closed
   immersion into an affine scheme, the lifts form a torsor under `n`-tuples of global sections
   of the ideal sheaf). Plus the check `lifting_torsor_test_affine_space` as an `example` (for
   `𝔸(PUnit; S)`, i.e. `𝔸¹_S`, along a first-order thickening) in
   `TauCeti/Examples/AlgebraicGeometry/Morphisms/FormallySmooth.lean` (about 12 lines); the example
   is why this split needs split 2, as that file is split 2's. `Lifts.lean` itself needs only
   split 1.
6. **`feat: the sheaf of lifts along a first-order thickening`** — after: 1, 2, 4.
   New file `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/LiftSheaf/Basic.lean` (183 lines) and
   instance `IsFirstOrderThickening.morphismRestrict` (`i ∣_ U` is a first-order thickening; 7
   lines) in `TauCeti/AlgebraicGeometry/Morphisms/Thickening.lean`. Declarations: `liftPresheaf`
   (sections over `W`: the `l : W ⟶ X` with `i ∣_ W ≫ l = (i ⁻¹ᵁ W).ι ≫ a` and
   `l ≫ f = W.ι ≫ h`), `liftPresheaf_isSheaf` (gluing via `Scheme.Cover.glueMorphisms` over the
   cover of `⨆ U` by the `U j`), `liftSheaf`, `nonempty_liftSheaf_top_iff`, instance
   `subsingleton_liftSheaf` (formally unramified `f`), `exists_nonempty_liftSheaf_of_smooth`
   and `liftSheaf_coversTop` (smooth `f`: locally nonempty, in the form of the `coversTop` field
   of main's `CategoryTheory.Sheaf.Torsor`). It needs split 4 for `exists_local_lift_of_smooth`
   and split 2 for `IsFirstOrderThickening.isNilpotent_ker`. A reviewer may ask to export the
   private `iSupCover` (the open cover of `⨆ U` by the `U j`) to a general home; it is kept
   private as it only serves the gluing here.
   The split also carries the characteristic API of the (unexposed) sections:
   `liftSheafObjEquiv f i a h W` (the sections over `W` are the `l : W ⟶ X` with
   `i ∣_ W ≫ l = (i ⁻¹ᵁ W).ι ≫ a` and `l ≫ f = W.ι ≫ h`) and the simp lemma
   `coe_liftSheafObjEquiv_map` (restriction to `W' ⊆ W` is precomposition with `W' ⟶ W`).
   `LiftSheaf/Basic.lean` is now 201 lines.
7. **`feat: lifts along a first-order thickening of an affine scheme form a torsor under
   derivations`** — after: 2.
   New file `TauCeti/RingTheory/Derivation/ToSquareZero.lean` (174 lines), pure algebra next
   to Mathlib's `Mathlib/RingTheory/Derivation/ToSquareZero.lean`: `Ideal.coe_mul_coe_of_sq_eq_bot`,
   `Ideal.isTorsionBySet_self_of_sq_eq_bot`, `Ideal.moduleOfSqEqBot` (a square-zero ideal `I` of `B`
   is an `A`-module through a given `A → B ⧸ I`, via Mathlib's `Module.IsTorsionBySet.module`),
   `Ideal.coe_smul_of_sq_eq_bot`, `Ideal.isScalarTower_of_sq_eq_bot`, the abbreviation
   `Ideal.LiftOfQuotient I R A` (the lifts `A →ₐ[R] B` of `A →ₐ[R] B ⧸ I`, Mathlib's subtype),
   `Ideal.LiftOfQuotient.mk_apply`, `Ideal.derivationToSquareZeroAddTorsor` (for `I ^ 2 = ⊥` the
   lifts, when there is one, form a torsor under `Derivation R A I`; base-point free, unlike
   Mathlib's `derivationToSquareZeroEquivLift`, which needs an algebra structure `A → B`), its
   `_vadd_apply`/`_vsub_apply`, `Ideal.nonempty_liftOfQuotient` (formally smooth `A`) and
   `Ideal.subsingleton_liftOfQuotient` (formally unramified `A`). The module structure and the
   torsor are `def`s, not instances, because they depend on the proof `hI`.
   New file `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/AffineLifts.lean` (210 lines), the
   same on schemes: `quotientKerAppTopAlgebra i g` (the `Γ(X, ⊤)`-algebra structure on
   `Γ(T', ⊤) ⧸ ker i.appTop ≃ Γ(T, ⊤)` given by `g`, for a closed immersion `i` into an affine
   `T'`), `quotientKerAppTopAlgebra_algebraMap`, `quotientKerAppTopAlgebra_mk_eq_algebraMap_iff`,
   `isScalarTower_quotientKerAppTopAlgebra`, `liftStructEquivLiftOfQuotient` (for `X`, `S`
   affine, the `CommSq.LiftStruct`s of `g ≫ f = i ≫ h` are `Ideal.LiftOfQuotient (ker i.appTop)
   Γ(S, ⊤) Γ(X, ⊤)`, via `l ↦ l.appTop`) with simp lemma `_apply_apply`, `liftStructAddTorsor`
   (for `i` a first-order thickening and `sq.HasLift`, the lifts form a torsor under
   `Derivation Γ(S, ⊤) Γ(X, ⊤) (ker i.appTop)`, transported from
   `Ideal.derivationToSquareZeroAddTorsor`), `liftStructAddTorsor_vadd_l_appTop` and
   `liftStructAddTorsor_vsub_apply`. Plus, in main's `TauCeti/AlgebraicGeometry/AffineScheme.lean`
   (7 lines), the general `toSpecΓ_SpecMap_isoSpec_inv_appTop` (the morphism into an affine `X`
   given by `φ : Γ(X, ⊤) ⟶ Γ(Y, ⊤)` acts on global sections by `φ`), proved with main's
   `Scheme.isoSpec_inv_appTop`. Together: the affine local model of `smooth_lifting_torsor`
   (`Hom(g^* Ω_{X/S}, I) = Der_{Γ(S, ⊤)}(Γ(X, ⊤), I)` for affine `X`, `S`, `T'`). Needs split 2 for
   `IsFirstOrderThickening.ker_appTop_sq_eq_bot`.
   The same file also proves the torsor **natural in the thickening** (section `Naturality`, about
   140 lines): `kerAppTopLinearMap φ hψ hg` (along a map `(ψ, φ)` of first-order thickenings into
   affine schemes, `ψ ≫ i = i₂ ≫ φ`, with `ψ ≫ g = g₂`, `φ.appTop` restricts to a
   `Γ(X, ⊤)`-linear map `ker i.appTop →ₗ ker i₂.appTop` of the square-zero ideals) with simp lemma
   `coe_kerAppTopLinearMap_apply`, `liftStructAddTorsor_precomp_vsub_apply`,
   `liftStructAddTorsor_precomp_vsub` (`φ ≫ l₁ -ᵥ φ ≫ l₂` is `(kerAppTopLinearMap φ hψ hg).compDer
   (l₁ -ᵥ l₂)`) and `liftStructAddTorsor_precomp_vadd` (`φ ≫ (d +ᵥ l) = compDer d +ᵥ φ ≫ l`). The
   precomposition of lifts is the new general `CategoryTheory.CommSq.LiftStruct.precomp` (with its
   `@[simps]` lemma `precomp_l`) in the new file `TauCeti/CategoryTheory/CommSq.lean` (38 lines):
   along a map `(a, b)` of arrows `i' ⟶ i`, a lift `l` of `f ≫ p = i ≫ g` gives the lift `b ≫ l` of
   `f' ≫ p = i' ≫ g'`. This is the compatibility of the local torsors with restriction to smaller
   affine opens that the gluing step needs. (An earlier round's `SpecLifts.lean`, the same
   equivalence for the literal square of spectra `Spec (B ⧸ I) ⟶ Spec B`, is removed: unused, and
   subsumed by `liftStructEquivLiftOfQuotient`.) About 590 lines in all (`ToSquareZero.lean` 191,
   `AffineLifts.lean` 353, `CommSq.lean` 38, `AffineScheme.lean` 9); a reviewer may ask to move the
   `Naturality` section of `AffineLifts.lean` into a split of its own.
8. **`feat: sections of the sheaf of lifts over affine opens`** — after: 1, 2, 4, 6, 7.
   New file `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/LiftSheaf/Affine.lean` (259 lines).
   Declarations: `commSq_resLE` (the square `a ≫ f = i ≫ h` restricted over opens `W ⊆ T'`,
   `U ⊆ X`, `V ⊆ S` with `i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U`, `W ≤ h ⁻¹ᵁ V`, `U ≤ f ⁻¹ᵁ V`, via Mathlib's
   `Scheme.Hom.resLE`); `range_subset_of_liftSheaf` (for surjective `i`, every section over `W`
   lands in `U`); `liftSheafObjEquivLiftStruct` (for surjective `i`, the sections of
   `liftSheaf f i a h` over `W` are the `CommSq.LiftStruct`s of the restricted square) with
   `liftSheafObjEquivLiftStruct_apply_l_ι` (simp, reassoc) and
   `coe_liftSheafObjEquivLiftStruct_symm_apply` (simp); `liftSheafObjEquivLiftStruct_map`
   (restriction to `W' ⊆ W` is `CommSq.LiftStruct.precomp` along Mathlib's
   `morphismRestrict_homOfLE` and `Scheme.Hom.map_resLE`); `liftSheafObjEquivLiftStruct_apply_l_homOfLE`
   (the lift read in `U' ⊆ U`, followed by `U' ⟶ U`, is the lift read in `U`); and, for `i` a
   first-order thickening and `W`, `W'`, `U`, `U'`, `V`, `V'` affine,
   `liftSheafObjEquivLiftStruct_map_vadd`, `liftSheafObjEquivLiftStruct_map_vsub` (restriction of
   sections to `W' ⊆ W` is equivariant for the torsors `liftStructAddTorsor` along
   `kerAppTopLinearMap`) and `liftSheafObjEquivLiftStruct_vsub_apply_homOfLE` (the derivation by
   which two sections differ, read through `U`, is the one read through `U' ⊆ U` composed with
   `Γ(U, ⊤) ⟶ Γ(U', ⊤)`). These are the local torsors of the sheaf of lifts and their
   compatibilities, the input of the gluing step.
9. **`feat: the torsor of lifts does not depend on the affine chart`** — after: 1, 2, 4, 5, 6, 7, 8.
   New file `TauCeti/RingTheory/Derivation/FormallyEtale.lean` (78 lines), pure algebra:
   `Derivation.compAlgebraMap_bijective` (for `T` formally étale over `S` and a `T`-module `M`,
   restriction `Derivation R T M → Derivation R S M` along `S → T` is bijective, from Mathlib's
   `KaehlerDifferential.isBaseChange_of_formallyEtale`), the `T`-linear equivalence
   `Derivation.compAlgebraMapEquiv` with simp lemmas `_apply`, `compAlgebraMap_compAlgebraMapEquiv_symm`
   and `compAlgebraMapEquiv_symm_apply_algebraMap`. In split 7's
   `TauCeti/RingTheory/Derivation/ToSquareZero.lean` (17 lines): `Ideal.isScalarTower_moduleOfSqEqBot`
   (the module structures `moduleOfSqEqBot` along `A → A'` over `B ⧸ I` form a scalar tower).
   In main's `TauCeti/AlgebraicGeometry/Morphisms/Etale/Basic.lean` (12 lines):
   `formallyEtale_homOfLE_appTop` (`Γ(U, ⊤) ⟶ Γ(U', ⊤)` is formally étale for affine opens
   `U' ⊆ U`, from Mathlib's `HasRingHomProperty.appTop @Etale`).
   New file `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/LiftSheaf/Chart.lean` (227 lines):
   `isScalarTower_resLE_homOfLE`, `isScalarTower_quotientKerAppTopAlgebra_homOfLE` (the algebra
   structures `toAlgebra` of `resLE`/`homOfLE` and `quotientKerAppTopAlgebra` for `U` and `U'` are
   compatible), instance `hasLift_commSq_resLE` (for `f` smooth the restricted squares over affine
   `W`, `U`, `V` have lifts, via `FormallySmooth.of_smooth_of_isAffine` and split 5's
   `FormallySmooth.hasLift`; this is why the split needs split 5), and, for affine `W`, `U' ⊆ U`,
   `V`:
   `liftSheafObjEquivLiftStruct_vsub_homOfLE` (the difference of two sections read through `U` is
   the one read through `U'` restricted along `Γ(U) → Γ(U')`, as derivations),
   `liftSheafObjEquivLiftStruct_symm_vadd_homOfLE` (acting by `d : Der(Γ(U'), I)` through `U'` is
   acting by `d.compAlgebraMap Γ(U)` through `U`) and
   `liftSheafObjEquivLiftStruct_symm_vadd_eq_compAlgebraMapEquiv_symm` (acting by
   `d : Der(Γ(U), I)` through `U` is acting by its unique extension to `Γ(U')` through `U'`).
   About 330 lines. The base chart `V` is already harmless: the pointwise
   `liftSheafObjEquivLiftStruct_vsub_apply_homOfLE` (split 8) allows unrelated `V`, `V'`.
10. **`feat: differences of morphisms of schemes on sections`** — after: none.
   New file `TauCeti/AlgebraicGeometry/Scheme/AppLESub.lean` (187 lines), general, in Mathlib's
   namespace `AlgebraicGeometry.Scheme.Hom` so that dot notation `l₁.appLESub l₂ …` works: `appLESub
   l₁ l₂ U V e₁ e₂ : Γ(X, U) →+ Γ(Y, V)` (`x ↦ l₁.appLE U V e₁ x - l₂.appLE U V e₂ x`, body
   unexposed) with simp lemma `appLESub_apply` (proved by `(rfl)`), the twisted Leibniz rule
   `appLESub_mul`, `appLESub_one`, `appLESub_self` (simp), `appLESub_add_appLESub` (cocycle),
   `neg_appLESub`, restriction in `V` (`appLESub_map`) and in `U` (`map_appLESub`), precomposition
   `appLESub_comp`, `appLESub_appLE_eq_zero` (for `l₁ ≫ f = l₂ ≫ f` the difference kills `f.appLE W
   U e s`), `appLE_appLESub_eq_zero` (for `j ≫ l₁ = j ≫ l₂` the difference lies in the kernel of
   `j.appLE`), and, for `j` surjective, `apply_eq_of_comp_eq`, `preimage_eq_of_comp_eq` and
   `eq_iff_appLESub_eq_zero` (`l₁ = l₂` iff all differences vanish, via Mathlib's `Scheme.Hom.ext`),
   and `appLESub_mul_of_isFirstOrderThickening` (along a first-order thickening `j` with `j ≫ l₁ = j
   ≫ l₂`, the untwisted Leibniz rule `δ(xy) = l₁ x · δ y + l₁ y · δ x`). The last one needs, in
   main's `TauCeti/AlgebraicGeometry/Morphisms/Thickening.lean` (19 lines with its docstring bullet,
   plus the import of main's `TauCeti.AlgebraicGeometry.IdealSheaf.Module`),
   `IsFirstOrderThickening.mul_eq_zero_of_app_eq_zero` (along a first-order thickening `i`, two
   sections over any open, not only affine ones, with vanishing pullbacks have product zero; from
   main's `mem_ker_sections_iff`, `sections_eq_ideal` and Mathlib's `IdealSheafData.ideal_mul`).
   About 190 lines. Needs no other split, so it can be opened at once.
11. **`feat: differences of sections of the sheaf of lifts`** — after: 1, 2, 4, 6, 7, 8, 10.
   New file `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/LiftSheaf/Difference.lean` (161
   lines): for two sections of `liftSheaf f i a h` over `W`:
   `morphismRestrict_comp_liftSheafObjEquiv` and `liftSheafObjEquiv_comp` (they agree after `i ∣_ W`
   and after `f`), and for surjective `i` `liftSheaf_ext_iff` (two sections are equal iff their
   differences on every open `U` of `X` vanish), `liftSheaf_eq_of_appLESub_eq` (two sections that
   differ from a third one in the same way are equal: the uniqueness half of the gluing step), and
   over affine `W`, `U`, `V` `liftSheafObjEquivLiftStruct_vsub_apply_eq_appLESub` (the derivation
   `l₁ -ᵥ l₂` of `liftStructAddTorsor`, on `U.ι.appLE U ⊤ _ x`, is the chart-free difference on `x :
   Γ(X, U)`) and `liftSheafObjEquivLiftStruct_vsub_apply_eq_of_map_eq` (the derivations read through
   two affine charts `U₁`, `U₂` agree on sections `x₁`, `x₂` with the same restriction to `U₁ ⊓ U₂`,
   which need not be affine). This closes, at the level of differences, the comparison of two charts
   with non-affine intersection that the previous round listed as missing.
12. **`feat: the sheaf of derivations into the ideal of a thickening`** — after: none.
   New file `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/LiftSheaf/Derivation.lean` (357
   lines; imports only Mathlib, so it can be opened at once). For `f : X ⟶ S`, `i : T ⟶ T'`,
   `a : T ⟶ X`: `LiftDerivationIndex i a W` (the pairs `(U, V)`, `U` open in `X`, `V ⊆ W` open in
   `T'`, with `i ⁻¹ᵁ V ≤ a ⁻¹ᵁ U`) and `LiftDerivationIndex.shrink`; the Prop-structure
   `IsLiftDerivation f i a D` for a family `D p : Γ(X, U) →+ Γ(T', V)` (fields `map_apply` and
   `apply_map`: compatible with restriction in `V` and in `U`; `app_apply`: values in the ideal of
   `i`; `apply_appLE`: kills the sections of `S`; `map_mul`: the Leibniz rule
   `D (x * y) = z * D y + w * D x` for all `z`, `w` with `i^♯ z = a^♯ x`, `i^♯ w = a^♯ y`); the
   additive subgroup `liftDerivationSubgroup f i a W` of such families with `isLiftDerivation_coe`,
   `mem_liftDerivationSubgroup` and `liftDerivationSubgroup.ext`;
   the restriction `liftDerivationSubgroupRestrict` (simp lemma `_apply`); the presheaf of abelian
   groups `liftDerivationPresheaf f i a` on `T'` (simp lemma `liftDerivationPresheaf_map_apply`);
   `liftDerivationPresheaf_isSheaf` (gluing through the sheaf property of `𝒪_{T'}`, ideal
   condition through that of `𝒪_T`); and `liftDerivationSheaf f i a`. This is step (c) of the
   previous round's plan: the group sheaf `ℋ = Hom(a^* Ω_{X/S}, I)`, stated without `Ω_{X/S}`.
   The Leibniz rule quantifies over local lifts `z`, `w` of `a^♯ x`, `a^♯ y` to `T'` because over a
   non-affine `V` they need not exist; over affine `V` they do, and the families are indexed by
   all `V ⊆ W`, so nothing is lost. `liftDerivationPresheaf` carries `@[expose]` so that its
   `map_apply` simp lemma can be stated about the underlying subgroup. A reviewer may ask to
   export the private general helpers `map_map_apply` (two restrictions are one) and
   `app_map_apply` (`i^♯` commutes with restriction) to a general home; they are kept private as
   one-line uses of `Functor.map_comp` and `Scheme.Hom.naturality`.
13. **`feat: the sheaf of derivations acts simply transitively on the sheaf of lifts`** — after: 1,
   2, 4, 6, 7, 8, 10, 11, 12.
   New file `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/LiftSheaf/Sub.lean` (about 590
   lines; imports split 11's `Difference.lean` and split 12's `Derivation.lean`). For `i` a
   first-order thickening and sections `l₁`, `l₂` of `liftSheaf f i a h` over `W`:
   `preimage_ι_le_preimage_liftSheafObjEquiv` (for `i ⁻¹ᵁ V ≤ a ⁻¹ᵁ U`, a section maps `W ∩ V`
   into `U`; the local form of split 8's `range_subset_of_liftSheaf`) and its converse
   `preimage_ι_image_preimage_liftSheafObjEquiv_le`; the **difference map**
   `liftSheafSub l₁ l₂ : liftDerivationSubgroup f i a W` (on `(U, V)`, `Scheme.Hom.appLESub l₁ l₂ U
   (W.ι ⁻¹ᵁ V)` carried to `Γ(T', V)` by the inverse of the isomorphism `W.ι.app V`, Mathlib's
   `Scheme.Hom.isIso_app`; the `IsLiftDerivation` fields come from split 10's `appLESub` API, the
   Leibniz rule along arbitrary lifts from `appLESub_mul_of_isFirstOrderThickening` and
   `IsFirstOrderThickening.mul_eq_zero_of_app_eq_zero`), `ι_app_liftSheafSub_apply`,
   `liftSheafSub_apply_eq_iff`, `liftSheafSub_add_liftSheafSub`, `liftSheafSub_self`,
   `neg_liftSheafSub`, `liftSheafSub_eq_zero_iff`, `liftSheafSub_left_injective`,
   `liftSheafSub_map` (compatible with restriction); `liftDerivation_eq_zero_of_isAffineOpen`
   (when `a` lifts to `W`, a derivation over `W` vanishing on `Γ(X, U)` for one affine open
   `U ⊇ a (i ⁻¹ W)` vanishes: over a basic open `D(g) ⊆ U ∩ U''` every section is `x' / g ^ n`, and
   the Leibniz rule along the lifts given by the lift of `a`, where `g ^ n` lifts to a unit, kills
   it; Mathlib's `IsAffineOpen.isLocalization_basicOpen`, `RingedSpace.isUnit_res_basicOpen`,
   `TopCat.Presheaf.IsSheaf.section_ext`); and the **action**: `exists_liftSheafSub_eq_of_isAffine`
   (over an affine `W` in affine charts `U`, `V`, every derivation `D` over `W` is `liftSheafSub l l₀`
   for some `l`: the component of `D` on `(U, W)` is the private `chartDerivation`, a derivation of
   split 7's `liftStructAddTorsor` built from the instance-free lemmas `chartFun_add`,
   `chartFun_mul`, `chartFun_appTop_mul`, `appTop_chartFun`, `mk_chartLift`; `l` is `d +ᵥ L₀`, and
   `liftDerivation_eq_zero_of_isAffineOpen` reduces `liftSheafSub l l₀ = D` to the chart, where it
   is split 11's `liftSheafObjEquivLiftStruct_vsub_apply_eq_appLESub`) and `exists_liftSheafSub_eq`
   (on every open `W`: local solutions on the affine charts of split 4's `exists_affine_chart` agree
   on overlaps by `liftSheafSub_left_injective` and glue through the sheaf property of
   `liftSheaf`; equality of derivations is checked locally by split 12's
   `liftDerivationSubgroup.ext_of_le_iSup`). Split 12 also gains the public
   `mem_liftDerivationSubgroup`, `liftDerivationSubgroup.ext`,
   `liftDerivationSubgroupRestrict_restrict` and `liftDerivationSubgroup.ext_of_le_iSup` for this
   split. Private helpers: `ιAppIso`, `ι_app_ιAppIso_inv`, `ι_app_injective`, `ι_app_app`,
   `app_map_appLE`, `app_liftSheafSubHom`, `ι_appLE_top` (`U.ι.appLE U ⊤ _ = U.topIso.inv`),
   `appTop_eq_appLE`, `appLE_comp_appLE'`, `appLE_congr_hom`, `resLE_appTop` (`resLE_app_top` with
   `appTop`), `morphismRestrict_appTop_topIso_inv`, `map_homOfLE_injective`, `liftSheaf_map_map`,
   `chartLift`. Several are general facts about opens and restrictions (`Γ(Z, V) ≅ Γ(W, W ⁻¹ V)`
   for `V ⊆ W`, `ι_appLE_top`, `appLE_comp_appLE'`, `appLE_congr_hom`); a reviewer may ask to
   export them next to Mathlib's `Scheme.Hom.isIso_app` and `Scheme.Opens.topIso`. The file could
   also be cut in two at `section Action` (difference map, about 350 lines; action, about 240
   lines) once those helpers are public.
14. **`feat: the torsor of lifts along a first-order thickening`** — after: 1, 2, 4, 6, 7, 8, 10,
   11, 12, 13.
   New file `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/LiftSheaf/Torsor.lean` (about 155
   lines): an instance `AddCommGrpCat.toCommGrp.IsEquivalence` (Mathlib's
   `commGroupAddCommGroupEquivalence.inverse`, so that `sheafCompose` applies; general, a
   reviewer may ask to move it to Mathlib's `EquivalenceGroupAddGroup` file);
   `liftDerivationGrpSheaf f i a` (the sheaf of derivations through
   `AddCommGrpCat.toCommGrp ⋙ forget₂ CommGrpCat GrpCat`, `@[expose]`); `liftSMul w D l` (the unique
   section with difference `D` with `l`) with `liftSheafSub_liftSMul` and `liftSMul_map`;
   `liftMulAction w W` (the `MulAction` of `Multiplicative (liftDerivationSubgroup f i a W)`; an
   `abbrev`, as the class-valued definition must be instance-reducible), `liftSheafSub_smul`,
   `liftMulAction_bijective`; and **`liftTorsor w : Sheaf.Torsor (liftDerivationGrpSheaf f i a)`**
   for `f` smooth: main's `CategoryTheory.Sheaf.Torsor` with sheaf `liftSheaf f i a h`,
   `coversTop` split 6's `liftSheaf_coversTop`; its class **`liftObstruction w`** in main's
   `Sheaf.NonabelianH1 (liftDerivationGrpSheaf f i a)` with **`liftObstruction_eq_one_iff`** (the
   class vanishes iff `a` lifts along `i` over `S`; main's `NonabelianH1.mk_eq_one_iff` with split
   6's `nonempty_liftSheaf_top_iff`). Split 12's `liftDerivationSheaf` gains `@[expose]`
   here, because the torsor's `mulAction` field is stated on `liftDerivationGrpSheaf`'s sections,
   which must unfold to `Multiplicative (liftDerivationSubgroup f i a W)`. This is
   `smooth_lifting_torsor`'s torsor, with `Hom(a^* Ω_{X/S}, I)` in its chart-free form `ℋ`.
15. **`feat: the sheaf of derivations into the ideal of a thickening is a sheaf of modules`** —
   after: 12.
   New file `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/LiftSheaf/Module.lean` (114 lines;
   imports split 12's `Derivation.lean` and Mathlib's `AlgebraicGeometry.Modules.Sheaf`):
   `IsLiftDerivation.mul_left` (a derivation over `W` times a section `t` of `𝒪_{T'}` over `W`,
   `(U, V) ↦ t|_V * D U V`, is a derivation), the `SMul` and `Module Γ(T', W)` instances on
   `liftDerivationSubgroup f i a W` with simp lemma `liftDerivationSubgroup.smul_apply`,
   `liftDerivationSubgroupRestrict_smul` (restriction is semilinear),
   `liftDerivationModule f i a : T'.Modules` (via Mathlib's `PresheafOfModules.ofPresheaf`; body
   not exposed) and `liftDerivationModule_toSheaf` (its underlying abelian sheaf is
   `liftDerivationSheaf f i a`, by `(rfl)`).
16. **`feat: derivations into a localized module`** — after: none.
   New file `TauCeti/RingTheory/Derivation/IsLocalizedModule.lean` (125 lines), pure algebra, next
   to main's `TauCeti/RingTheory/Derivation/Localization.lean` (which localizes the *source*):
   for `A` an `R`-algebra, `B` an `A`-algebra and `M`, `M'` `B`-modules,
   `Derivation.baseChangeKaehler D : B ⊗[A] Ω[A⁄R] →ₗ[B] M` with `_tmul`, `_tmul_D` (simp),
   its converse `Derivation.ofBaseChangeKaehler` with `_apply` (simp),
   `LinearMap.compDerRestrictScalars R A ι : Derivation R A M →ₗ[B] Derivation R A M'`
   (post-composition with a `B`-linear `ι`) with `_apply` (simp), and the instance
   `LinearMap.isLocalizedModule_compDerRestrictScalars`: if `Ω[A⁄R]` is finitely presented (e.g.
   `A` smooth over `R`, Mathlib's instance in `RingTheory/Smooth/Basic.lean`) and `ι` is a
   localization at `S ⊆ B`, so is post-composition with `ι` (from Mathlib's
   `Module.FinitePresentation.exists_lift_of_isLocalizedModule` and
   `Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule` over `B ⊗[A] Ω[A⁄R]`). Needs no
   other split, so it can be opened at once. It is the algebraic input of the quasi-coherence of
   `liftDerivationModule` (split 18); a reviewer may ask for its consumer first, in which case it
   moves into split 18.
17. **`feat: lifts along a first-order thickening when the sheaf of derivations has no H¹`** —
   after: 1, 2, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15; **and the supplier `equiv-sheaf-h` landed**.
   New file `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/LiftSheaf/Cohomology.lean` (72
   lines; imports split 14's `Torsor.lean`, split 15's `Module.lean`, main's
   `Cohomology/Affine.lean` and, on this branch, the stub module):
   `liftObstruction_eq_one_of_subsingleton` (the obstruction class vanishes when
   `Sheaf.H (liftDerivationSheaf f i a) 1` does, through `equivSheafH`),
   `exists_lift_of_subsingleton` (then `a` lifts) and `exists_lift_of_isQuasicoherent` (`a` lifts
   when `T'` is affine and `liftDerivationModule f i a` is quasi-coherent, by main's
   `Scheme.Modules.subsingleton_cohomology_succ_of_isAffine`). At port time, swap the stub import
   for the supplier's module and `sheafCompose …` for its `toGrpSheaf`, if it has one.
18. **`feat: smooth iff formally smooth and the torsor of lifts`** — after: 1–17.
   **Not on this branch.** This is the only split that completes the target: the quasi-coherence
   of `liftDerivationModule f i a` for smooth `f`, and with it the general `smooth_lifting_torsor`
   (its obstruction class and its vanishing for affine `T'`), `FormallySmooth.of_smooth`,
   `smooth_iff_formallySmooth`, and the ⇐ half of `FormallySmooth.iff_affineLocally`. It will
   probably have to be cut further (the chart identification of `ℋ(W)`, the localization of the
   ideal sheaf, the assembly); each of those cuts goes before it.

Splits 1–16 depend on no unlanded supplier and could be opened against `main` as they stand,
each once the splits it needs have merged; split 17 also waits for `equiv-sheaf-h`. This round moved the sheaf-of-lifts files into the
directory `FormallySmooth/LiftSheaf/` (`Basic.lean` for split 6, `Affine.lean` for split 8,
`Chart.lean` for split 9), as the placement rubric asks of files sharing the leading component
`LiftSheaf`; splits 6 and 8 are opened directly at those paths.

## What remains

* **Smooth ⇒ formally smooth** (Stacks, Lemma 37.11.7 (02H6), via Lemmas 37.9.x and 37.11.10
  (0D0F)), and with it the ⇐ half of `FormallySmooth.iff_affineLocally`, `FormallySmooth.of_smooth`
  and `smooth_iff_formallySmooth` (the ⇐ half of the last is already `Smooth.of_formallySmooth`).
  Done on the branch: local lifts exist on small affine opens of `T'` (`exists_local_lift_of_smooth`,
  split 4); they are the sections of the sheaf `liftSheaf f i a h` on `T'` (split 6), which is
  locally nonempty (`liftSheaf_coversTop`) and has a global section exactly when a lift exists
  (`nonempty_liftSheaf_top_iff`); over an affine `W` inside affine charts `U ⊆ X`, `V ⊆ S` its
  sections form a torsor under `Der_{Γ(V)}(Γ(U), I(W))` (`liftStructAddTorsor` via
  `liftSheafObjEquivLiftStruct`, splits 7–8), compatibly with restriction to `W' ⊆ W` (split 8) and
  with shrinking the chart `U' ⊆ U` (split 9). Split 11 adds the chart-free description of the
  difference of two sections, `Scheme.Hom.appLESub l₁ l₂ U V` on every open `U` of `X`: a
  derivation along a first-order thickening, valued in the ideal sheaf, killing `S`, detecting
  equality of sections, equal to the affine torsor's `l₁ -ᵥ l₂` over every affine chart, and hence
  independent of the chart even when two charts meet in a non-affine open.
  What remains, in order:
  (c) **done in split 12**: the group sheaf `ℋ = Hom(a^* Ω_{X/S}, I)` on `T'` is
  `liftDerivationSheaf f i a`, defined chart-free as the families `D U V : Γ(X, U) →+ Γ(T', V)`
  (for `V ⊆ W` with `i ⁻¹ᵁ V ≤ a ⁻¹ᵁ U`, a lift-free condition) satisfying `IsLiftDerivation`
  (restriction in `U` and `V`, valued in the ideal, killing `S`, the Leibniz rule along local
  lifts of `a^♯ x`), with its sheaf property; and **done in split 13**: the difference map
  `liftSheafSub : liftSheaf × liftSheaf → liftDerivationSheaf`, `(l₁, l₂) ↦ appLESub l₁ l₂`
  read on every `V ⊆ W`, additive (`liftSheafSub_add_liftSheafSub`), vanishing exactly on the
  diagonal (`liftSheafSub_eq_zero_iff`), injective in the first argument
  (`liftSheafSub_left_injective`) and compatible with restriction (`liftSheafSub_map`);
  (d) **done in split 13**: surjectivity of `l ↦ liftSheafSub l l₀` (`exists_liftSheafSub_eq`,
  with the affine-chart case `exists_liftSheafSub_eq_of_isAffine`); together with
  `liftSheafSub_left_injective` the sheaf of derivations acts simply transitively on the sheaf of
  lifts, with no smoothness hypothesis;
  (e) **done in split 14**: `liftTorsor w : Sheaf.Torsor (liftDerivationGrpSheaf f i a)` for `f`
  smooth (`coversTop` is `liftSheaf_coversTop`, the action is `liftSMul`, `bijective` is (d)),
  and its class `liftObstruction w` with `liftObstruction_eq_one_iff`; so smooth ⇒ formally smooth
  is now exactly `liftObstruction w = 1` for affine `T'`. Main's `Torsor` takes a
  sheaf of `GrpCat`, so `liftDerivationGrpSheaf` goes through `Multiplicative` (Mathlib's
  `AddCommGrpCat.toCommGrp`, then `forget₂ CommGrpCat GrpCat`); the §2.3 supplier's `equivSheafH`
  will have to be stated for such a `G`;
  (f) **done in split 15**: `ℋ` is the sheaf of `𝒪_{T'}`-modules `liftDerivationModule f i a`
  (`t • D := (U, V) ↦ t|_V * D U V`);
  (g) **done in split 17, against the stub**: through `equivSheafH` the torsor's class vanishes
  when `H¹(T', ℋ) = 0`, so `a` lifts when `T'` is affine and `liftDerivationModule f i a` is
  quasi-coherent (`exists_lift_of_isQuasicoherent`, main's Serre vanishing
  `subsingleton_cohomology_succ_of_isAffine`);
  (h) **remaining: `liftDerivationModule f i a` is quasi-coherent** for `f` smooth (locally of
  finite presentation with `Ω` finitely presented suffices). The intended proof uses main's
  criterion `Scheme.Modules.isQuasicoherent_of_isLocalizedModule`
  (`TauCeti/AlgebraicGeometry/Modules/Localization.lean`): cover `T'` by the affine opens `W` of
  split 4's `exists_affine_chart` basis that are small enough for `a` to lift to `W`
  (`exists_local_lift_of_smooth`), each with affine charts `U ⊆ X`, `V ⊆ S`; then for every
  `g ∈ Γ(T', W)` show that restriction `ℋ(W) → ℋ(D(g))` is a localization at `g`. Steps:
  (h1) the **chart identification** `ℋ(W') ≃ₗ[Γ(T', W')] Der_{Γ(V)}(Γ(U), ker (i ∣_ W')^♯)` for
  affine `W' ⊆ W`, natural in restriction: the map is split 13's private `chartDerivation`
  (to be made public), injective by `liftDerivation_eq_zero_of_isAffineOpen` and surjective by
  the argument of `exists_liftSheafSub_eq_of_isAffine` (`D := liftSheafSub (d +ᵥ l₀) l₀`);
  (h2) the **ideal localizes**: `ker (i ∣_ W)^♯ → ker (i ∣_ D(g))^♯` is a localization at `g`
  (the ideal sheaf `i.ker` is quasi-coherent; Mathlib's `IdealSheafData` basic-open API), as
  modules over `B = Γ(T, i⁻¹ W)` (where the `Γ(U)`-module structure of split 7's
  `Ideal.moduleOfSqEqBot` factors) at `ḡ`;
  (h3) split 16's `isLocalizedModule_compDerRestrictScalars` (with `Ω[Γ(U)⁄Γ(V)]` finitely
  presented, as `Γ(V) → Γ(U)` is smooth) and Mathlib's `IsLocalizedModule.restrictScalars_powers`
  (from `B` back to `Γ(T', W)`) then give the localization of `ℋ`;
  (i) `FormallySmooth.of_smooth`: for affine `T'`, (h) and split 17 give the lift.
* **`smooth_lifting_torsor`** in general (its affine space case and the check
  `lifting_torsor_test_affine_space` are split 5): the torsor is `liftTorsor` and its obstruction
  class `liftObstruction`, vanishing iff a lift exists (split 14), and uniqueness for étale `f` is
  `FormallyEtale.of_etale` with `FormallyEtale.hom_ext`, and sheaf-wise `subsingleton_liftSheaf`.
  What remains is the triviality of the class for affine `T'` ((h) above; (f), (g) are done).
  Its image `equivSheafH _ (liftObstruction w)` in `H¹` is available through the stub, but in
  `H¹(T', ℋ)`, not `H¹(T, Hom(a^* Ω_{X/S}, I))`. Stating it with `Ω_{X/S}` needs StableReduction Layer 1's relative
  differentials, which is not a listed supplier of this target: `main` has
  `Scheme.relativeDifferentials` only for `X` over a ring `R`
  (`TauCeti/AlgebraicGeometry/Modules/Differentials/Basic.lean`). The chart-free `ℋ` of (c) is the
  form the torsor can take without it; its identification with `Hom(a^* Ω_{X/S}, I)` waits for
  that layer.
