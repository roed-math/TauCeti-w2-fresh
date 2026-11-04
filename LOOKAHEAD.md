<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"is-nisnevich-covering","main":"7ed979dc2eacd36a3962e1fdf3b481323fb3fb8b","status":"complete","suppliers":["ind-etale"],"splits":[{"n":1,"after":[],"title":"feat: Nisnevich coverings and the Nisnevich topology"},{"n":2,"after":[1],"title":"feat: the henselization criterion for Nisnevich coverings"}]}-->

# Lookahead: `is-nisnevich-covering` (SchemeAndStackFoundations §2.12)

Built on `main` at `7ed979dc2eacd36a3962e1fdf3b481323fb3fb8b`. The whole target is proved on this
branch: the definitions `IsNisnevichCovering`, `nisnevichPrecoverage`, `nisnevichTopology`,
`smallNisnevichTopology`, and the README API through `isNisnevichCovering_iff_henselization`
(`isNisnevichCovering_of_zariski`, `nisnevichPrecoverage_le_etalePrecoverage`,
`IsNisnevichCovering.pullback`/`.of_isPullback`, `.comp`,
`isNisnevichCovering_iff_henselization`), together with `zariskiTopology_le_nisnevichTopology`,
`nisnevichTopology_le_etaleTopology`, `nisnevichTopology_subcanonical`,
`mem_nisnevichTopology_iff` and `smallNisnevichTopology_le_smallEtaleTopology`. The only `sorry`
is the supplier stub below. Not done (outside this item): `smallNisnevich_comparison` needs the
§2.10 comparison morphisms, which are not on `main`.

## Stubbed declaration (supplier `ind-etale`, open PR #27212)

Almost all of the §0.13 `IndEtale` API (`IndEtale`, `of_etale`, `of_equiv`, `flat`,
`baseChange`, `of_isLocalization`, `Henselization.indEtale`) is already on `main` and is used
directly. The only missing piece consumed here is `IndEtale.comp`.

`Suggested.lean` pins no `IndEtale` declaration (the README §0.13 names `IndEtale.comp` in its
API list only), so the stub follows PR #27212's diff, which states it in
`TauCeti/RingTheory/Etale/IndEtale.lean` as:

```lean
theorem comp (T : Type u) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [IndEtale R S] [IndEtale S T] : IndEtale R T := by
```

inside `namespace TauCeti.Algebra.IndEtale` with
`variable {R S S' : Type u} [CommRing R] [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']`.

Stub, in `TauCeti/Lookahead/IsNisnevichCovering/Stubs.lean`:

```lean
namespace TauCeti.Algebra.IndEtale
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
theorem comp (T : Type u) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [IndEtale R S] [IndEtale S T] : IndEtale R T := by
  sorry
```

Differences: none in the statement (same name, namespace, binders and conclusion); the unused
`S'` variable of the PR's section is omitted. Porting: delete the stub module and replace the
import `TauCeti.Lookahead.IsNisnevichCovering.Stubs` in
`TauCeti/AlgebraicGeometry/Sites/Nisnevich/Henselization.lean` by
`TauCeti.RingTheory.Etale.IndEtale` (already imported transitively through
`TauCeti.RingTheory.Henselization.IndEtale`, so the import line can simply be dropped).

The only consumer is `indEtale_henselization` (the henselization `𝒪ʰ_{X,x}` is ind-étale over
`Γ(X, W)` for every affine open `W ∋ x`: it is the henselization of the localization
`𝒪_{X,x}` of `Γ(X, W)`), which records that `Spec 𝒪ʰ_{X,x} ⟶ X` is the pro-étale point of §0.13
used by the criterion. The criterion itself uses only `main`'s henselization API
(`Henselization.isLocalHom_algebraMap`, `Henselization.residueField_map_bijective`,
`HenselianLocalRing`) and `HenselianRing.comp_bijective_of_algebra`.

## Differences from the roadmap's pinned forms (`Suggested.lean`, §2.12)

- Namespace: the roadmap's `TauCetiRoadmap.SchemeAndStackFoundations.Nisnevich.*` becomes
  `TauCeti.AlgebraicGeometry.Scheme.*`, next to Mathlib's `Scheme.etaleTopology`,
  `Scheme.zariskiTopology`, `Scheme.smallEtaleTopology` and Tau Ceti's
  `TauCeti.AlgebraicGeometry.Scheme.AffineZariskiSite`; this also avoids the stutter
  `Nisnevich.nisnevichTopology`.
- `IsNisnevichCovering` is a `structure` with fields `etale` and `exists_isIso` (pinned: a `def`
  conjunction), the index type is `ι : Type*` (pinned: `Type u`), and the residue condition is
  `IsIso ((f i).residueFieldMap x)` (pinned: `Function.Bijective (…).hom`); these are equivalent
  (`ConcreteCategory.isIso_iff_bijective`), and `IsIso` is the form `main`'s residue-field API
  (`Scheme.Pullback.isIso_residueFieldMap_fst`, `Scheme.Hom.isIso_residueFieldMap_of_comp`)
  consumes. The README says "`κ(x) → κ(u)` an isomorphism".
- `nisnevichPrecoverage` is stated intrinsically on presieves (pinned: presieves equal to
  `ofArrows` of a `Type u`-indexed covering); `ofArrows_mem_nisnevichPrecoverage_iff` recovers the
  pinned description for every index universe.
- `nisnevichTopology` is an `abbrev` for `nisnevichPrecoverage.toGrothendieck`, as pinned.
- `isNisnevichCovering_iff_henselization`: the README states it "for a finite family over a
  Noetherian base: Nisnevich iff the base change to every `Spec O^h_{X,x}` has a section". The
  proved form needs neither hypothesis and states the section of the base change of one member as
  a lift `t : Spec 𝒪ʰ_{S,s} ⟶ X i` with `t ≫ f i = fromSpecHenselization S s` (a section of
  `pullback (f i) (fromSpecHenselization S s) ⟶ Spec 𝒪ʰ_{S,s}` is the same datum).
- `𝒪ʰ_{X,x}` is `Henselization.algebra (maximalIdeal (X.presheaf.stalk x))` (the §0.12/§0.13
  henselization of the local ring along its maximal ideal, on `main`), packaged as
  `Scheme.henselization X x`.
- The README check `test_not_covering_real_complex` (pinned as an `example`) and
  `test_covering_identity` are in `TauCeti/Examples/AlgebraicGeometry/Sites/Nisnevich.lean`.

## Split plan

### Split 1 — `feat: Nisnevich coverings and the Nisnevich topology` (after: none)

Needs nothing from the supplier; can be opened as soon as convenient.

Files:
- `TauCeti/AlgebraicGeometry/Sites/Nisnevich/Basic.lean` (238 lines)
- `TauCeti/Examples/AlgebraicGeometry/Sites/Nisnevich.lean` (48 lines)

Declarations: `IsNisnevichCovering` (with `etale`, `exists_isIso`),
`IsNisnevichCovering.exists_eq`, `IsNisnevichCovering.of_isPullback`,
`IsNisnevichCovering.pullback`, `IsNisnevichCovering.comp`, `isNisnevichCovering_of_isIso`,
`isNisnevichCovering_of_zariski`, `nisnevichPrecoverage`, `ofArrows_mem_nisnevichPrecoverage_iff`,
instances `HasIsos`/`IsStableUnderBaseChange`/`IsStableUnderComposition` for
`nisnevichPrecoverage`, `nisnevichPrecoverage_le_etalePrecoverage`,
`zariskiPrecoverage_le_nisnevichPrecoverage`, `nisnevichTopology`, `mem_nisnevichTopology_iff`,
`zariskiTopology_le_nisnevichTopology`, `nisnevichTopology_le_etaleTopology`,
`nisnevichTopology_subcanonical`, `smallNisnevichTopology`,
`smallNisnevichTopology_le_smallEtaleTopology`; examples: identity covering and the quadratic
field extension that is not a Nisnevich covering.

### Split 2 — `feat: the henselization criterion for Nisnevich coverings` (after: 1)

Needs split 1 and the supplier `ind-etale` (PR #27212, `IndEtale.comp`) on `main`. Completes the
target.

Files:
- `TauCeti/AlgebraicGeometry/Sites/Nisnevich/Henselization.lean` (218 lines; drop the stub import)

Declarations: `exists_lift_of_isIso_residueFieldMap` (morphisms from the spectrum of a henselian
local ring lift along étale maps through a point with unchanged residue field),
`isIso_residueFieldMap_of_lift` (the converse), `henselization`, `toHenselization`,
`fromSpecHenselization`, the `Algebra Γ(X, W) (henselization X x)` and `IsScalarTower` instances,
`indEtale_henselization`, and the exported `isNisnevichCovering_iff_henselization`.

If the supplier is delayed, split 2 can instead be opened without `indEtale_henselization` (and
its two instances), since the criterion does not depend on it.
