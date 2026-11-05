<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"is-thickening","main":"85f3eb5579df5ca44ba8cd0921d614b41ab72174","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: formally smooth and formally étale morphisms of schemes"},{"n":2,"after":[1],"title":"feat: formal smoothness of Spec.map and of affine space"},{"n":3,"after":[],"title":"feat: thickenings of order n + 2 factor through first-order thickenings"},{"n":4,"after":[1,2],"title":"feat: étale iff formally étale"},{"n":5,"after":[1,2],"title":"feat: lifts into affine space along a closed immersion form a torsor"},{"n":6,"after":[1,2,4],"title":"feat: the sheaf of lifts along a first-order thickening"},{"n":7,"after":[2],"title":"feat: lifts along a first-order thickening of an affine scheme form a torsor under derivations"},{"n":8,"after":[1,2,4,6,7],"title":"feat: sections of the sheaf of lifts over affine opens"},{"n":9,"after":[1,2,3,4,5,6,7,8],"title":"feat: smooth iff formally smooth and the torsor of lifts"}]}-->

# Lookahead: SchemeAndStackFoundations §4.1 `is-thickening` (partial)

Roadmap: `SchemeAndStackFoundations/README.md`, Layer 4, §4.1 *Thickenings, formally smooth and
étale morphisms, the lifting criterion, torsors of lifts*. Built on `main` at
`85f3eb5579df5ca44ba8cd0921d614b41ab72174`.

## Stubs: none

Nothing proved on this branch consumes either listed supplier, so there is no
`TauCeti/Lookahead/IsThickening/Stubs.lean`.

* `is-universal-homeomorphism` (§0.23, open PR #22428). The class
  `TauCeti.AlgebraicGeometry.IsUniversalHomeomorphism` is already on `main`, in
  `TauCeti/AlgebraicGeometry/Morphisms/UniversalHomeomorphism.lean`. So is
  `IsThickening.isUniversalHomeomorphism` (from #23574, `Morphisms/Thickening.lean`), proved from
  main's own `isUniversalHomeomorphism_iff_isIntegralHom_universallyInjective_surjective`. PR #22428
  moves the module to `Morphisms/UniversalHomeomorphism/Basic.lean` and adds
  `IsUniversalHomeomorphism.of_isClosedImmersion_of_surjective`. When it lands, its port has to
  update the import in `Morphisms/Thickening.lean`; that is #22428's job, not this branch's. The
  branch uses only `IsUniversalHomeomorphism.isHomeomorph`, which is on `main`, in
  `Criterion.lean`: a thickening is a homeomorphism, so preimages of opens are open.
* `equiv-sheaf-h` (§2.3, open PR #27237; carrier `Sheaf.NonabelianH1` merged as #22627). It is
  needed only for `smooth_lifting_torsor` (the obstruction class in `H¹(T, Hom(a^* Ω_{X/S}, I))`)
  and for the gluing step of smooth ⇒ formally smooth. Neither is on this branch (see
  *What remains*), so nothing is stubbed. The next session should stub what that step consumes:
  `NonabelianH1`'s torsor-class API and `equivSheafH`, in the forms of #27237 and its follow-ups.
  (Rechecked 2026-11-05, twice, against `main` `85f3eb5579d`: both PRs still open, same scope; split 8 consumes neither. Earlier, rechecked 2026-11-04, three times: #22428 and #27237 are still open; #27237 is now *feat: connecting map of an extension of sheaves of
  groups*, a single new file `TauCeti/CategoryTheory/Sites/NonabelianCohomology/Connecting.lean`;
  the torsor carrier `TauCeti/CategoryTheory/Sites/NonabelianCohomology/Torsor.lean` is on
  `main`. Nothing on the branch consumes either. Split 6's `liftSheaf_coversTop` is stated in the
  exact form of the `coversTop` field of main's `CategoryTheory.Sheaf.Torsor`, so that once a
  group sheaf acts on `liftSheaf` it plugs in directly; it uses only `main`'s
  `Opens.grothendieckTopology`, not the torsor API itself.)

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
| *FormallySmooth.of_smooth*, `smooth_iff_formallySmooth` | ⇐ (formally smooth + LFP ⇒ smooth) **proved** as `AlgebraicGeometry.Smooth.of_formallySmooth` (split 4); ⇒ **proved for affine `X`, `S`** as `FormallySmooth.of_smooth_of_isAffine`, and **locally** as `exists_local_lift_of_smooth` (split 4); the general ⇒ remains |
| `etale_iff_formallyEtale` | **proved** (split 4), together with the instance `FormallyEtale.of_etale` |
| `smooth_lifting_torsor` | affine local model **proved** (split 7): `Ideal.derivationToSquareZeroAddTorsor` (lifts of `A → B ⧸ I` to `B`, for `I ^ 2 = ⊥`, are a torsor under `Der_R(A, I)`), `Ideal.nonempty_liftOfQuotient`/`subsingleton_liftOfQuotient`, `liftStructEquivLiftOfQuotient` (the lifts in a square of affine schemes along a closed immersion `i` are the algebra lifts `Γ(X, ⊤) →ₐ[Γ(S, ⊤)] Γ(T', ⊤)` of `Γ(X, ⊤) → Γ(T', ⊤) ⧸ ker i.appTop`) and `liftStructAddTorsor` (along a first-order thickening `i` of an affine scheme, the lifts in a square with `X`, `S` affine form a torsor under `Der_{Γ(S, ⊤)}(Γ(X, ⊤), ker i.appTop)`); affine space case **proved**: instance `affineSpaceLift_addTorsor` (split 5); étale uniqueness **proved** as instance `FormallyEtale.subsingleton_liftStruct` (split 5) and, sheaf-wise, as instance `subsingleton_liftSheaf` (split 6); the **sheaf of lifts** `liftSheaf` is **defined**, with `nonempty_liftSheaf_top_iff` (a lift exists iff the sheaf has a global section) and `liftSheaf_coversTop` (locally nonempty for smooth `f`) (split 6); its sections over an affine open `W` of `T'` are **read as lifts in affine squares** (`liftSheafObjEquivLiftStruct`), so that `liftStructAddTorsor` acts on them, compatibly with restriction to a smaller affine `W' ⊆ W` (`liftSheafObjEquivLiftStruct_map_vadd`/`_map_vsub`) and independently of the affine chart `U ⊆ X` (`liftSheafObjEquivLiftStruct_vsub_apply_homOfLE`) (split 8); the group sheaf `Hom(a^* Ω_{X/S}, I)`, its simply transitive action and the obstruction class remain |
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
   and `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/Criterion.lean` (184 lines:
   `AlgebraicGeometry.Smooth.of_formallySmooth`, `AlgebraicGeometry.Etale.of_formallyEtale`,
   instance `FormallyEtale.of_etale`, `etale_iff_formallyEtale`). About 300 lines.
5. **`feat: lifts into affine space along a closed immersion form a torsor`** — after: 1, 2.
   New file `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/Lifts.lean` (125 lines). Lifts are
   Mathlib's `CommSq.LiftStruct` (no new structure). Declarations: instances
   `FormallySmooth.hasLift` and `FormallyEtale.subsingleton_liftStruct` (existence and uniqueness
   of lifts in a square along an affine first-order thickening), `affineSpaceLift_appTop_appTop_coord`,
   `affineSpaceLift_ext`, the `VAdd`/`VSub` instances of `n → RingHom.ker i.appTop` on lifts into
   `𝔸(n; S)` with simp lemmas `affineSpaceLift_vadd_appTop_coord`, `affineSpaceLift_coe_vsub_apply`,
   instance `affineSpaceLift_hasLift`, and instance `affineSpaceLift_addTorsor` (along a closed
   immersion into an affine scheme, the lifts form a torsor under `n`-tuples of global sections
   of the ideal sheaf). Plus the check `lifting_torsor_test_affine_space` as an `example` (for
   `𝔸(PUnit; S)`, i.e. `𝔸¹_S`, along a first-order thickening) in
   `TauCeti/Examples/AlgebraicGeometry/Morphisms/FormallySmooth.lean` (about 12 lines); the example
   is why this split needs split 2, as that file is split 2's. `Lifts.lean` itself needs only
   split 1.
6. **`feat: the sheaf of lifts along a first-order thickening`** — after: 1, 2, 4.
   New file `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/LiftSheaf.lean` (183 lines) and
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
   `LiftSheaf.lean` is now 201 lines.
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
   affine opens that the gluing step needs. About 530 lines in all. (An earlier round's `SpecLifts.lean`, the same
   equivalence for the literal square of spectra `Spec (B ⧸ I) ⟶ Spec B`, is removed: unused, and
   subsumed by `liftStructEquivLiftOfQuotient`.) About 390 lines.
8. **`feat: sections of the sheaf of lifts over affine opens`** — after: 1, 2, 4, 6, 7.
   New file `TauCeti/AlgebraicGeometry/Morphisms/FormallySmooth/LiftSheafAffine.lean` (259 lines).
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
9. **`feat: smooth iff formally smooth and the torsor of lifts`** — after: 1, 2, 3, 4, 5, 6, 7, 8.
   **Not on this branch.** This is the only split that completes the target: the general
   `smooth_lifting_torsor`, `FormallySmooth.of_smooth`, `smooth_iff_formallySmooth`, and the ⇐ half
   of `FormallySmooth.iff_affineLocally`.

Splits 1–8 depend on no unlanded supplier and could be opened against `main` as they stand
(split 7 once split 2 has merged).

## What remains

* **Smooth ⇒ formally smooth** (Stacks, Lemma 37.11.7 (02H6), via Lemmas 37.9.x and 37.11.10
  (0D0F)). Done on the branch: local lifts exist on small affine opens of `T'`
  (`exists_local_lift_of_smooth`, split 4), and they are the sections of the sheaf
  `liftSheaf f i a h` on `T'` (split 6), which is locally nonempty (`liftSheaf_coversTop`) and has
  a global section exactly when a lift exists (`nonempty_liftSheaf_top_iff`). Unlike the étale case,
  local lifts are not unique, so they do not glue directly. What remains: the differences of two
  lifts form the sheaf `Hom_{O_T}(a^* Ω_{X/S}, I)`; define its action on `liftSheaf` (on an affine
  `W` whose lifts land in an affine `U ⊆ X` over an affine `V ⊆ S`, this is Mathlib's
  `derivationToSquareZeroEquivLift` for `Γ(V) → Γ(U)`, now the base-point-free torsor
  `Ideal.derivationToSquareZeroAddTorsor` of split 7, read on schemes as `liftStructAddTorsor`
  (split 7, any square of affine schemes); its compatibility with restriction to a smaller affine
  open `W' ⊆ W` of `T'` (any map of first-order thickenings into affine schemes) is now proved:
  `liftStructAddTorsor_precomp_vsub`/`_vadd` with `kerAppTopLinearMap` (split 7). Split 8 (this round) reads the sections of `liftSheaf f i a h` over an affine open
  `W` of `T'`, landing in an affine `U ⊆ X` over an affine `V ⊆ S`, as the lifts of the restricted
  square (`liftSheafObjEquivLiftStruct`), proves restriction to `W' ⊆ W` equivariant
  (`liftSheafObjEquivLiftStruct_map_vadd`/`_map_vsub`) and the difference derivation independent of
  the chart `U` up to restriction to `U' ⊆ U` (`liftSheafObjEquivLiftStruct_vsub_apply_homOfLE`).
  The next bricks: (c) the group sheaf itself, on `T'` (equivalently on `T`): over `W` the
  `Γ(S)`-derivations `g^{-1} O_X → I`, i.e. compatible families of derivations
  `Γ(X, U) → I(W ∩ a⁻¹ U)` over the affine opens `U ⊆ X` lying over affine opens of `S`; on an
  affine `W` inside a single chart `U`, its sections are `Der_{Γ(V)}(Γ(U), I(W))`, which needs that
  a derivation out of `Γ(U)` extends uniquely along the localizations `Γ(U) → Γ(U')` for basic
  opens `U' ⊆ U`, which is already on `main` (`Derivation.extendOfIsLocalization` with
  `_algebraMap`, and uniqueness `IsLocalization.eq_of_leibniz`, in
  `TauCeti/RingTheory/Derivation/Localization.lean`, checked 2026-11-05); (d) its action on
  `liftSheaf`, glued from `liftStructAddTorsor` via split 8; (e) package `liftSheaf` as a
  `CategoryTheory.Sheaf.Torsor` (`liftSheaf_coversTop` is its `coversTop` field). Then
  `H¹ = 0` for quasi-coherent sheaves on affine `T'` makes its class trivial, so it has a section
  (main's `NonabelianH1.mk_eq_one_iff`), and `nonempty_liftSheaf_top_iff` turns the section into
  the lift. The `H¹` comparison is §2.3 `equiv-sheaf-h` (`equivSheafH`); Serre vanishing is
  already on `main` (`subsingleton_cohomology_succ_of_isAffine` in
  `TauCeti/AlgebraicGeometry/Cohomology/Affine.lean`, rechecked 2026-11-04). The same argument gives the ⇐ half of
  `FormallySmooth.iff_affineLocally`, and with it `FormallySmooth.of_smooth` and
  `smooth_iff_formallySmooth` (the ⇐ half is already `Smooth.of_formallySmooth`).
* **`smooth_lifting_torsor`** in general (its affine space case and the check
  `lifting_torsor_test_affine_space` are split 5): the torsor under
  `Hom_{O_T}(a^* Ω_{X/S}, I)`, its obstruction class in `H¹(T, Hom(a^* Ω_{X/S}, I))`, triviality for
  affine `T'`, and uniqueness for étale `f`. Uniqueness for étale `f` is already
  `FormallyEtale.of_etale` with `FormallyEtale.hom_ext`. This needs StableReduction Layer 1's
  `Ω_{X/S}` and the §2.3 supplier (stub them from #27237 and its successors). Note that `main`
  has `Scheme.relativeDifferentials` only for `X` over a ring `R`
  (`TauCeti/AlgebraicGeometry/Modules/Differentials/Basic.lean`), not for a general `X ⟶ S`;
  the general `Ω_{X/S}` is StableReduction Layer 1, which is not a listed supplier of this
  target. Split 5's affine space torsor is the base case: `Hom(g^* Ω_{𝔸(n; S)/S}, I) ≅ I^n`.
