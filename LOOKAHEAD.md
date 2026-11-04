<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"is-thickening","main":"7ed979dc2eacd36a3962e1fdf3b481323fb3fb8b","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: formally smooth and formally étale morphisms of schemes"},{"n":2,"after":[1],"title":"feat: formal smoothness of Spec.map and of affine space"},{"n":3,"after":[],"title":"feat: thickenings of order n + 2 factor through first-order thickenings"},{"n":4,"after":[1,2],"title":"feat: étale iff formally étale"},{"n":5,"after":[1,2,3,4],"title":"feat: smooth iff formally smooth and the torsor of lifts"}]}-->

# Lookahead: SchemeAndStackFoundations §4.1 `is-thickening` (partial)

Roadmap: `SchemeAndStackFoundations/README.md`, Layer 4, §4.1 *Thickenings, formally smooth and
étale morphisms, the lifting criterion, torsors of lifts*. Built on `main` at
`7ed979dc2eacd36a3962e1fdf3b481323fb3fb8b`.

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
| *FormallySmooth.of_smooth*, `smooth_iff_formallySmooth` | ⇐ (formally smooth + LFP ⇒ smooth) **proved** as `AlgebraicGeometry.Smooth.of_formallySmooth` (split 4); ⇒ remains |
| `etale_iff_formallyEtale` | **proved** (split 4), together with the instance `FormallyEtale.of_etale` |
| `smooth_lifting_torsor` | remains |
| checks *isFirstOrderThickening_dualNumber*, *_id*, `not_isFirstOrderThickening_cube`, `not_isThickening_origin` | already on `main` |
| checks *formallySmooth_affineSpace*, *formallyEtale_id*, `not_formallySmooth_closedPoint` | **proved**: instance `FormallySmooth.affineSpace`, an `example`, and `not_formallySmooth_origin` (split 2) |
| check `formallyUnramified_iff_mathlib` | **proved** as `formallyUnramified_iff_hom_ext` (split 4) |
| check `lifting_torsor_test_affine_space` | remains (with `smooth_lifting_torsor`) |

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
   (`IsFirstOrderThickening.isNilpotent_ker`, `appTop_surjective`, `ker_appTop_mul_self`,
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
5. **`feat: smooth iff formally smooth and the torsor of lifts`** — after: 1, 2, 3, 4.
   **Not on this branch.** This is the only split that completes the target: `smooth_lifting_torsor`,
   `FormallySmooth.of_smooth`, `smooth_iff_formallySmooth`, the ⇐ half of
   `FormallySmooth.iff_affineLocally`, and the check `lifting_torsor_test_affine_space`.

Splits 1–4 depend on no unlanded supplier and could be opened against `main` as they stand.

## What remains

* **Smooth ⇒ formally smooth** (Stacks, Lemma 37.11.7 (02H6), via Lemmas 37.9.x and 37.11.10
  (0D0F)). Local lifts exist on small affine opens of `T'`: `Smooth` gives affine-locally
  `RingHom.Smooth`, hence `RingHom.FormallySmooth`, and then `FormallySmooth.SpecMap_iff` applies.
  The construction is the one in `Criterion.lean`'s `exists_local_lift`. Unlike the étale case,
  however, local lifts are not unique, so they do not glue directly. The differences of two lifts
  form the sheaf `Hom_{O_T}(a^* Ω_{X/S}, I)`, and the lifts form a torsor under it. Gluing needs
  that torsor, from §2.3 `equiv-sheaf-h` (`NonabelianH1`, `equivSheafH`), together with
  `H¹ = 0` for quasi-coherent sheaves on affine `T'`. The same argument gives the ⇐ half of
  `FormallySmooth.iff_affineLocally`, and with it `FormallySmooth.of_smooth` and
  `smooth_iff_formallySmooth` (the ⇐ half is already `Smooth.of_formallySmooth`).
* **`smooth_lifting_torsor`** and the check `lifting_torsor_test_affine_space`: the torsor under
  `Hom_{O_T}(a^* Ω_{X/S}, I)`, its obstruction class in `H¹(T, Hom(a^* Ω_{X/S}, I))`, triviality for
  affine `T'`, and uniqueness for étale `f`. Uniqueness for étale `f` is already
  `FormallyEtale.of_etale` with `FormallyEtale.hom_ext`. This needs StableReduction Layer 1's
  `Ω_{X/S}` and the §2.3 supplier (stub them from #27237 and its successors).
