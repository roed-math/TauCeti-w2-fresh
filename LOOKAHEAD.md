<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"epsilon-fppf-etale","main":"afa08a3ed16fb167e35de371afb1eb03fbc5913a","status":"partial","suppliers":["is-nisnevich-covering"],"splits":[{"n":1,"after":[],"title":"feat: the comparison morphism from the big fppf site to the big étale site"},{"n":2,"after":[],"title":"feat: left Kan extension along a flat functor is exact without smallness assumptions"},{"n":3,"after":[1,2,4],"title":"feat: the comparison morphism from the big fppf site to the small étale site"},{"n":4,"after":[],"title":"feat: base change of the small étale site"},{"n":5,"after":[1,2,3,4],"title":"feat: pullback of cohomology along the comparison morphisms from the big fppf site"},{"n":6,"after":[1,2,3,4],"title":"feat: the comparison morphisms between the small Zariski, Nisnevich and étale sites"},{"n":7,"after":[1,2,3,4,5,6],"title":"feat: pullback of cohomology along the comparison morphisms between the small Zariski, Nisnevich and étale sites"}]}-->

# Lookahead: `epsilon-fppf-etale` (SchemeAndStackFoundations §2.10)

Built on `main` at `afa08a3ed16fb167e35de371afb1eb03fbc5913a`. **Status: partial.** All four
comparison morphisms of §2.10 are on this branch, each through its exact inverse-image functor and
its adjunction with the direct image: `epsilonFppfEtale X` (`ε⁻¹`), `aX X` (`a_X⁻¹ = π_X⁻¹ ⋙ ε⁻¹`,
with `piX X` the inverse image from the small to the big étale site), `etaleToNisnevich X` and
`nisnevichToZariski X`. Each sends constant sheaves to constant sheaves. `comparison_comp` is on the
branch for the composites (`sheafInverseImageTrans`, `aX` by definition, and
`nisnevichToZariskiCompEtaleToNisnevichIso`), and `comparison_baseChange` for all of them:
`ε` (`epsilonFppfEtaleBaseChangeIso`), `π_X` and `a_X` (`piXBaseChangeIso`, `aXBaseChangeIso`, new
this session), `etaleToNisnevich` (`etaleToNisnevichBaseChangeIso`) and `nisnevichToZariski`
(`nisnevichToZariskiBaseChangeIso`), the small-site ones through the base change functor
`Etale.pullback g : X.Etale ⥤ Y.Etale`. New this session as well: `π_X⁻¹` is fully faithful
(`fullyFaithfulPiX`), and the big-étale half of `aX_inverseImage_obj`, `piXObjIso`:
`π_X⁻¹ F (T) ≅ Γ(T_ét, h⁻¹ F)` for `h : T ⟶ X`. New in the third session: the pullback maps on
sheaf cohomology along every comparison morphism (`epsilonFppfEtaleH`, `piXH`, `aXH`,
`etaleToNisnevichH`, `nisnevichToZariskiH`, through `main`'s `CategoryTheory.Sheaf.H.pullback`),
which are the maps the remaining comparison theorems assert to be bijective; `comparison_comp` on
cohomology for `a_X` (`aXH_apply`: the pullback along `a_X` is the pullback along `π_X` followed by
the pullback along `ε`); and the degree-zero descriptions as restriction of global sections
(`equiv₀_piXH`, `equiv₀_nisnevichToZariskiH`). New in the fourth session: `comparison_comp` on
cohomology for the small sites (`map_etaleToNisnevichH_nisnevichToZariskiH`: the pullback from
the Zariski site to the Nisnevich site followed by the pullback to the étale site is the pullback
along the morphism of sites from the étale to the Zariski site, through the general naturality
`Sheaf.H.pullback_natTrans_apply` and the compatibility of the constant-sheaf comparisons
`constantSheafComp_nisnevichToZariskiCompEtaleToNisnevichIso_hom_app`), and the degree-zero
descriptions of the remaining sheafification-type comparisons (`equiv₀_epsilonFppfEtaleH`,
`equiv₀_etaleToNisnevichH`, from the general `Sheaf.H.equiv₀_pullback_sheafInverseImage`). The
roadmap checks `test_comparison_id` and
`test_aX_constant` (for `aX` itself) are in the examples file. Fifth session: merged `main` (`72cbdfb14e3d`) and re-verified; supplier PR #28094 is still open
at head `6c29c999512d`, unchanged, so the stubs are unchanged. Sixth session: merged `main` (`afa08a3ed16f`) without conflicts and re-verified; the three supplier PRs are still open at unchanged heads (#28094 at `6c29c999512d`, #29365 at `440cc53de2c4`, #27295 at `075b1bd4978d`), so the stubs are unchanged and nothing on the branch yet consumes `big-sheaf` or `qcoh-higher-direct-image-vanishing`. Seventh session (2026-11-06): `main` is still at `afa08a3ed16f` and the three supplier PRs are still open at the same heads, so nothing was merged and the stubs are unchanged; the branch was rebuilt and re-checked. Eighth session (2026-11-06): `main` and the three supplier
PR heads are unchanged; added `aXAdjunction_unit_app` (the unit of `a_X⁻¹ ⊣ a_{X,*}` as the
composite of the units of `π_X` and `ε`) and the degree-zero description of the pullback along
`a_X`, `equiv₀_aXH`. Ninth session (2026-11-06): `main` and the three supplier PR heads are
unchanged, so the stubs are unchanged. Added the reduction of `aX_inverseImage_obj` to fppf
descent: the inverse image does not change a sheaf for the finer topology
(`sheafInverseImageObjIsoOfIsSheaf`, `epsilonFppfEtaleObjIsoOfIsSheaf`), so the sections of
`a_X⁻¹ F` over `h : T ⟶ X` are `Γ(T_ét, h⁻¹ F)` as soon as `π_X⁻¹ F` is an fppf sheaf
(`aXObjIsoOfIsSheaf`); and the degree-zero case of the cohomology comparisons: the pullback in
degree zero along `J ≤ K` is bijective on `J`-sheaves that are `K`-sheaves
(`Sheaf.H.pullback_sheafInverseImage_zero_bijective`), hence `epsilonFppfEtaleH_zero_bijective`,
`etaleToNisnevichH_zero_bijective` and `aXH_zero_bijective` (on sheaves that are already sheaves
for the finer topology), and `piXH_zero_bijective` unconditionally, since `π_X⁻¹` is fully
faithful. Tenth session (2026-11-06): `main` (`afa08a3ed16f`) and the three supplier PR heads are
unchanged, so the stubs are unchanged. Added the degree-zero comparison along `ε` for fpqc sheaves,
`epsilonFppfEtaleH_zero_bijective_of_fpqc` (with `fppfTopology_over_le_fpqcTopology_over`), which
applies to `main`'s big-site sheaves `Ga` and `Gm` (checked in the examples file): the degree-zero
case of the étale/fppf half of `quasiCoherent_topology_comparison` for `O` and of
`smoothGroup_fppf_etale_comparison` for `𝔾_m`. Eleventh session (2026-11-06): `main`
(`afa08a3ed16f`) and the three supplier PR heads (#28094 `6c29c999512d`, #29365 `440cc53de2c4`,
#27295 `075b1bd4978d`) are unchanged, so the stubs are unchanged. Added the degree-zero comparison
from the small Nisnevich to the small étale site on étale sheaves,
`etaleToNisnevichH_zero_bijective_of_etale` (split 7), checked in the examples file on the
restriction of `main`'s `Ga` to the small étale site: the degree-zero case of the Nisnevich/étale
half of `quasiCoherent_topology_comparison` for `O`. The README's §2.10 targets `quasiCoherent_topology_comparison`, `aX_inverseImage_obj` and `smoothGroup_fppf_etale_comparison` have no pinned form in `Suggested.lean`. Not yet proved: the fppf half of
`aX_inverseImage_obj` (that `ε⁻¹` does not change `π_X⁻¹ F`), and the cohomology comparison
theorems; see the end.

## Stubbed declarations

All stubs are in `TauCeti/Lookahead/EpsilonFppfEtale/Stubs.lean`. They are the only `sorry`s on
the branch. All come from supplier `is-nisnevich-covering` (open PR #28094, module
`TauCeti.AlgebraicGeometry.Sites.Nisnevich.Basic`). The roadmap's `Suggested.lean` §2.12 pins
only `IsNisnevichCovering`, `nisnevichPrecoverage`, `nisnevichTopology`,
`zariskiTopology_le_nisnevichTopology` and `nisnevichTopology_le_etaleTopology`; the README's
§2.12 additionally pins `smallNisnevichTopology X` on `X.Etale`, *isNisnevichCovering_of_zariski*,
*IsNisnevichCovering.pullback* and `smallNisnevichTopology_le_smallEtale`. The stubs follow the PR's current diff (re-read this
session), which differs from the previous session's stubs in the namespace of the small-site
declarations (now `AlgebraicGeometry.Scheme`, previously `TauCeti.AlgebraicGeometry.Scheme`).

### `IsNisnevichCovering`

- `Suggested.lean` (verbatim):
  ```lean
  def IsNisnevichCovering {S : Scheme.{u}} {ι : Type u} {X : ι → Scheme.{u}}
      (f : ∀ i, X i ⟶ S) : Prop :=
    (∀ i, Etale (f i)) ∧ ∀ s : S, ∃ i, ∃ x : X i, f i x = s ∧
      Function.Bijective (Scheme.Hom.residueFieldMap (f i) x).hom
  ```
- PR #28094: `structure IsNisnevichCovering {ι : Type*} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S) :
  Prop` with fields `etale` and `exists_isIso`, in `namespace TauCeti.AlgebraicGeometry.Scheme`,
  `variable {S : Scheme.{u}}`.
- Stub: `def IsNisnevichCovering {ι : Type*} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S) : Prop :=
  sorry`, same namespace and variables.
- Differences: follows the PR (index type `Type*` instead of `Type u`, an isomorphism of residue
  fields instead of a bijective map, a `structure` instead of a conjunction). The stub is a `def`
  with body `sorry`, since a structure cannot be stubbed;
  the proofs never use its fields, only `isNisnevichCovering_of_zariski` and
  `ofArrows_mem_smallNisnevichTopology_iff`.

### `IsNisnevichCovering.of_isPullback`

- `Suggested.lean`: not pinned there (README §2.12 API: *IsNisnevichCovering.pullback*).
- PR #28094 (head `6c29c999512d`, namespace `TauCeti.AlgebraicGeometry.Scheme`, with
  `variable {ι : Type*} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}`) and stub (same statement, the
  variables written as binders):
  ```lean
  theorem IsNisnevichCovering.of_isPullback {ι : Type*} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
      (hf : IsNisnevichCovering f) {Y : Scheme.{u}} (g : Y ⟶ S)
      {P : ι → Scheme.{u}} (p₁ : ∀ i, P i ⟶ Y) (p₂ : ∀ i, P i ⟶ X i)
      (h : ∀ i, IsPullback (p₁ i) (p₂ i) g (f i)) : IsNisnevichCovering p₁
  ```
- Differences: none but the `sorry` proof. The PR proves the README's pinned
  `IsNisnevichCovering.pullback` (the case `P i = pullback g (f i)`) from this form; the proof here
  needs the general form, because the base change of a morphism of `X.Etale` along `g` is a
  pullback square only up to the canonical isomorphism (`Etale.isPullback_pullback_map_left`).

### `isNisnevichCovering_of_zariski`

- `Suggested.lean`: not pinned there (README §2.12 API: *isNisnevichCovering_of_zariski*).
- PR #28094 and stub (same statement, namespace `TauCeti.AlgebraicGeometry.Scheme`):
  ```lean
  theorem isNisnevichCovering_of_zariski {ι : Type*} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
      (hf : Presieve.ofArrows X f ∈ AlgebraicGeometry.Scheme.zariskiPrecoverage S) :
      IsNisnevichCovering f
  ```
- Differences: none but the `sorry` proof.

### `smallNisnevichTopology`

- `Suggested.lean`: not pinned there (README §2.12: "`smallNisnevichTopology X` on `X.Etale`").
- PR #28094 (namespace `AlgebraicGeometry.Scheme`):
  ```lean
  def smallNisnevichTopology (X : Scheme.{u}) : GrothendieckTopology X.Etale :=
    (Scheme.Etale.forget X).restrictedTopology (nisnevichTopology.over X)
  ```
- Stub: `noncomputable def smallNisnevichTopology (X : Scheme.{u}) : GrothendieckTopology X.Etale
  := sorry`, namespace `AlgebraicGeometry.Scheme`.
- Differences: body `sorry`, hence `noncomputable`. Swapping in the landed declaration only means
  deleting the stub.

### `ofArrows_mem_smallNisnevichTopology_iff`

- `Suggested.lean`: not pinned there (README §2.12 lists `mem_nisnevichTopology_iff`; the PR
  adds this small-site form).
- PR #28094 and stub (same statement, namespace `AlgebraicGeometry.Scheme`):
  ```lean
  theorem ofArrows_mem_smallNisnevichTopology_iff {X : Scheme.{u}} {W : X.Etale} {ι : Type*}
      {Z : ι → X.Etale} (f : ∀ i, Z i ⟶ W) :
      Sieve.ofArrows Z f ∈ X.smallNisnevichTopology W ↔
        IsNisnevichCovering (fun i ↦ (f i).left)
  ```
- Differences: none but the `sorry` proof.

### `smallNisnevichTopology_le_smallEtaleTopology`

- `Suggested.lean`: not pinned there (README §2.12: `smallNisnevichTopology_le_smallEtale`).
- PR #28094 and stub (namespace `AlgebraicGeometry.Scheme`):
  ```lean
  theorem smallNisnevichTopology_le_smallEtaleTopology (X : Scheme.{u}) :
      X.smallNisnevichTopology ≤ X.smallEtaleTopology
  ```
- Differences: the name follows the PR rather than the README's shortened `…_le_smallEtale`.

No other supplier is consumed by what is on the branch:

- `sheaf-h-pullback`'s `Sheaf.H.pullback` is already on `main`
  (`TauCeti/CategoryTheory/Sites/SheafCohomology/Pullback.lean`).
- `qcoh-higher-direct-image-vanishing` (#27295) and `big-sheaf` (open PR #29365; partial #27307) are needed only by the
  cohomology comparisons, which are not yet proved, so they are not stubbed.

## Splits

### Split 1: `feat: the comparison morphism from the big fppf site to the big étale site`

Needs first: none. It uses no supplier and can be opened on `main` now.

Roadmap attribution: `Roadmap: SchemeAndStackFoundations` (§2.10 `epsilonFppfEtale`,
`comparison_comp`, `comparison_baseChange`).

Files:

- `TauCeti/CategoryTheory/Sites/InverseImageOfLE.lean` (225 lines, new), namespace
  `CategoryTheory.GrothendieckTopology`. This is the general comparison for topologies `J ≤ K`
  on one category:
  - `sheafDirectImageOfLE` with `_obj_obj` and `_map_hom` (simp lemmas),
    `fullyFaithfulSheafDirectImageOfLE` and the `Full`/`Faithful` instances,
    `sheafDirectImageOfLE_comp`;
  - `sheafInverseImage J K A` (the `K`-sheafification of a `J`-sheaf) with `_obj` and `_map`
    (simp lemmas), and a `PreservesFiniteLimits` instance (exactness);
  - `sheafAdjunctionOfLE` (inverse image ⊣ direct image), the `IsRightAdjoint` instance and
    `preservesColimits_sheafInverseImage`;
  - `sheafInverseImageObjIsoOfIsSheaf` (a `J`-sheaf that is a `K`-sheaf is not changed by the
    inverse image: the counit of the adjunction);
  - `sheafInverseImageRefl` (comparing a topology with itself gives the identity) and
    `sheafInverseImageTrans` (composition coherence, the general form of `comparison_comp`);
  - `presheafToSheafCompSheafInverseImageIso` and `constantSheafCompSheafInverseImageIso`
    (constant sheaves go to constant sheaves), and
    `toSheafify_comp_presheafToSheafCompSheafInverseImageIso_inv_app_hom` (the comparison of
    sheafifications, precomposed with the `K`-sheafification map, is the `J`-sheafification map
    followed by the unit of the adjunction);
  - `sheafInverseImageCompSheafPushforwardContinuousIso` (base change along a functor that is
    continuous and cocontinuous, the general form of `comparison_baseChange` for big sites) and
    `sheafInverseImageCompSheafPullbackIso` (pullback along a functor continuous for both pairs
    of topologies, the general form of `comparison_baseChange` for small sites, as the conjugate
    of the equality of the direct images).
- `TauCeti/AlgebraicGeometry/Sites/Comparison.lean` (122 lines, new), namespace
  `AlgebraicGeometry.Scheme`:
  - `etalePrecoverage_le_fppfPrecoverage`, `etaleTopology_le_fppfTopology`,
    `etaleTopology_over_le_fppfTopology_over` and `fppfTopology_over_le_fpqcTopology_over`;
  - `epsilonFppfEtale X A` (the inverse image `ε⁻¹`) with `epsilonFppfEtale_obj`,
    `epsilonFppfEtaleObjIsoOfIsSheaf`, `epsilonFppfEtaleAdjunction`, the `IsLeftAdjoint` and `PreservesFiniteLimits` instances,
    `constantSheafCompEpsilonFppfEtaleIso`, and `epsilonFppfEtaleBaseChangeIso` (base change
    along `g : Y ⟶ X`, through `overMapPullback`). `epsilonFppfEtale`, its adjunction and
    `constantSheafCompEpsilonFppfEtaleIso` carry `@[expose]`: the cohomology file of split 5
    unfolds them to the general `sheafInverseImage` statements.

About 350 lines in total.

### Split 2: `feat: left Kan extension along a flat functor is exact without smallness assumptions`

Needs first: none. Uses no supplier. `Roadmap: SchemeAndStackFoundations` (prerequisite of §2.10
`aX` and `nisnevichToZariski`; general category theory).

Files:

- `TauCeti/CategoryTheory/Functor/Flat.lean` (91 lines, new), namespace `TauCeti.CategoryTheory`:
  `lanCompEvaluationIsoColim` (Mathlib's `lanEvaluationIsoColim` without smallness assumptions)
  and the instance `lan_preservesFiniteLimits_of_flat`: for `F : C ⥤ D` representably flat, with
  categories of costructured arrows `Small.{w}`, and a concrete category `E` (sections in
  `Type w`) with finite limits, colimits and forgetful functor preserving finite limits and filtered
  colimits of the size of those costructured-arrow categories, `F.op.lan` into `E`-valued
  presheaves preserves finite limits. Mathlib's version requires `C` and `D` small; `X.Opens ⥤
  X.Etale` has a large target and `X.Etale ⥤ Over X` a large source. It imports
  `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit` privately, which the module
  system requires for the filtered-colimit instance.

### Split 3: `feat: the comparison morphism from the big fppf site to the small étale site`

Needs first: splits 1, 2 and 4. Uses no supplier. `Roadmap: SchemeAndStackFoundations` (§2.10 `aX`,
`comparison_comp`, `comparison_baseChange`, the étale part of `aX_inverseImage_obj`).

Files:

- `TauCeti/CategoryTheory/Sites/ConstantSheaf.lean` (existing, +19 lines): the natural isomorphism
  `Functor.constantSheafCompSheafPullbackIso` (for `u` final) built from the existing pointwise
  `sheafPullbackConstantSheafIso` and its naturality, and the simp lemma
  `constantSheafCompSheafPullbackIso_inv_app` giving its components.
- `TauCeti/CategoryTheory/Sites/PullbackFullyFaithful.lean` (72 lines, new), namespace
  `CategoryTheory.Functor`: for `G` fully faithful, continuous and cocontinuous (with pointwise
  left and right Kan extensions along `G.op`), `sheafPullbackCompSheafPushforwardContinuousIso :
  G.sheafPullback ⋙ G.sheafPushforwardContinuous ≅ 𝟭` (restriction commutes with sheafification
  through Mathlib's `pushforwardContinuousSheafificationCompatibility`, and the left Kan extension
  along a fully faithful functor restricts back through `lanUnit`), `fullyFaithfulSheafPullback`
  and the `Full`/`Faithful` instances.
- `TauCeti/AlgebraicGeometry/Sites/SmallEtaleComparison.lean` (321 lines, new), namespace
  `AlgebraicGeometry.Scheme`: `coverPreserving_etaleForget`, the `RepresentablyFlat`, `Final`,
  `IsContinuous` and `IsCocontinuous` instances for `Etale.forget X`, `piX X A`
  (`Functor.sheafPullback` along `Etale.forget X`) with `piXAdjunction`, `IsLeftAdjoint`,
  `constantSheafCompPiXIso` and `constantSheafCompPiXIso_inv_app`; `aX X A := piX X A ⋙
  epsilonFppfEtale X A` with `aXAdjunction`, `aXAdjunction_unit_app`, `IsLeftAdjoint`, `constantSheafCompAXIso` and
  `constantSheafCompAXIso_inv_app`; `piX`, `piXAdjunction` and `aX` carry `@[expose]`, because the
  cohomology files must unfold them to apply the `Functor.sheafPullback` and composite-functor API
  (in particular `Sheaf.H.equiv₀_pullback_sheafPullback` and `Sheaf.H.pullback_comp_apply`); base change along `g : Y ⟶ X`:
  `piXDirectImageBaseChangeIso` (the direct images, from `Etale.pullbackCompForgetIso`),
  `piXBaseChangeIso` (its conjugate through `Over.mapPullbackAdj g`) and `aXBaseChangeIso`
  (composed with `epsilonFppfEtaleBaseChangeIso`); `piXObjIso` (`π_X⁻¹ F (T) ≅ Γ(T_ét, h⁻¹ F)`,
  from `piXBaseChangeIso h` at `𝟙 T` and the fully faithful restriction); `aXObjIsoOfIsSheaf`
  (`a_X⁻¹ F (T) ≅ Γ(T_ét, h⁻¹ F)` when `π_X⁻¹ F` is an fppf sheaf, through
  `epsilonFppfEtaleObjIsoOfIsSheaf`); `fullyFaithfulPiX` with
  `Full`/`Faithful` instances; and `PreservesFiniteLimits` instances: for `piX` with concrete
  coefficients with sections in `Type (u + 1)` (through split 2), in particular for
  `AddCommGrpCat.{u + 1}`, and for `aX` whenever `piX` is exact.

About 410 lines.

### Split 4: `feat: base change of the small étale site`

Needs first: none. Uses no supplier and can be opened on `main` now. `Roadmap:
SchemeAndStackFoundations` (prerequisite of §2.10 `comparison_baseChange` on the small sites).

Files:

- `TauCeti/AlgebraicGeometry/Sites/SmallEtaleBaseChange.lean` (118 lines, new), namespace
  `AlgebraicGeometry.Scheme`: `Etale.pullback g : X.Etale ⥤ Y.Etale` (`MorphismProperty.Over.pullback`
  with its two `@Etale` instances passed explicitly, since instance search does not find them) with
  `_obj_left`, `_obj_hom`, `_map_left` (simp lemmas), `Etale.isPullback_pullback_map_left`,
  `Etale.pullbackCompForgetIso`, the `PreservesFiniteLimits` and `RepresentablyFlat` instances,
  `coverPreserving_etalePullback` and the `IsContinuous` instance for the small étale topologies.
- `TauCeti/AlgebraicGeometry/Sites/OpensEtale.lean` (140 lines, new; moved here from the previous
  plan's last split, it uses no supplier), namespace `AlgebraicGeometry.Scheme`:
  `restrictEtaleFunctor X : X.Opens ⥤ X.Etale` with `_obj_hom`/`_map_left`,
  `restrictEtaleFunctor_hom_ext`, `Etale.liftOpens` and `Etale.liftOpens_ι`,
  `restrictEtaleFunctorLift`, `isTerminalRestrictEtaleFunctorObjTop` (the open subscheme `X` is
  terminal in `X.Etale`), `range_subset_of_hom_restrictEtaleFunctor_obj`, the `RepresentablyFlat`
  and `Final` instances, and `restrictEtaleFunctorCompEtalePullbackIso` (`U ×ₓ Y ≅ g ⁻¹ᵁ U`
  as schemes étale over `Y`, naturally in `U`).

About 260 lines.

### Split 5: `feat: pullback of cohomology along the comparison morphisms from the big fppf site`

Needs first: splits 1, 2, 3 and 4. Uses no supplier. `Roadmap: SchemeAndStackFoundations`
(§2.10: the cohomology maps of `quasiCoherent_topology_comparison`,
`etale_pullback_fppf_comparison` and `smoothGroup_fppf_etale_comparison`; uses §2.1's
`Sheaf.H.pullback`, already on `main`).

Files:

- `TauCeti/CategoryTheory/Sites/SheafCohomology/Pullback.lean` (existing on `main`, +90 lines; now
  also imports split 1's `InverseImageOfLE`): `Sheaf.H.pullback_natTrans_apply` (the pullback is
  natural in the exact functor: for `τ : pb ⟶ pb'`, the pullback along `pb'` with comparison
  `c ≫ τ ℤ` is the pullback along `pb` followed by `τ G`; three rewrites through Mathlib's
  `Ext.mapExactFunctor_comp_mk₀_natTransApp`) and `Sheaf.H.equiv₀_pullback_sheafInverseImage`
  (for `J ≤ K`, the pullback along the `K`-sheafification of `J`-sheaves is, in degree zero, the
  restriction of global sections along the unit of the adjunction; the analogue of `main`'s
  `equiv₀_pullback_sheafPullback`) and `Sheaf.H.pullback_sheafInverseImage_zero_bijective` (that
  pullback is bijective in degree zero on a `J`-sheaf that is a `K`-sheaf, the unit being an
  isomorphism there).
- `TauCeti/AlgebraicGeometry/Sites/CohomologyComparison.lean` (233 lines, new), namespace
  `AlgebraicGeometry.Scheme`: the `Additive` instances for `epsilonFppfEtale`, `piX` and `aX` on
  abelian sheaves; `epsilonFppfEtaleH X F n : Hⁿ((Sch/X)_ét, F) →+ Hⁿ((Sch/X)_fppf, ε⁻¹ F)`,
  `piXH X F n : Hⁿ(X_ét, F) →+ Hⁿ((Sch/X)_ét, π_X⁻¹ F)` and
  `aXH X F n : Hⁿ(X_ét, F) →+ Hⁿ((Sch/X)_fppf, a_X⁻¹ F)` (each `Sheaf.H.pullback` with the
  inverse of the constant-sheaf comparison); `equiv₀_piXH` (in degree zero, `piXH` is the
  restriction of global sections along the unit of `π_X⁻¹ ⊣ π_{X,*}`, from `main`'s
  `Sheaf.H.equiv₀_pullback_sheafPullback`); `aXH_apply` (`comparison_comp` on cohomology:
  `aXH = epsilonFppfEtaleH ∘ piXH`, from `Sheaf.H.pullback_comp_apply`); `equiv₀_epsilonFppfEtaleH`
  (in degree zero, `epsilonFppfEtaleH` is the restriction of global sections along the unit of
  `ε⁻¹ ⊣ ε_*`, at the terminal object `Over.mk (𝟙 X)`); `equiv₀_aXH` (in degree zero, `aXH` is the
  restriction of global sections along the unit of `a_X⁻¹ ⊣ a_{X,*}`); `piXH_zero_bijective`
  (`π_X⁻¹` is fully faithful), `epsilonFppfEtaleH_zero_bijective` (on étale sheaves that are fppf
  sheaves) and `aXH_zero_bijective` (when `π_X⁻¹ F` is an fppf sheaf): the degree-zero case of the
  comparison theorems; and `epsilonFppfEtaleH_zero_bijective_of_fpqc` (bijective on fpqc sheaves,
  such as `main`'s `Ga` and `Gm`, regarded as étale sheaves through `sheafDirectImageOfLE`). The coefficient universe
  is arbitrary, with `HasExt` and the exactness of `π_X⁻¹` as instance hypotheses (the latter an
  instance for `w = u + 1`).

About 325 lines.

### Split 6: `feat: the comparison morphisms between the small Zariski, Nisnevich and étale sites`

Needs first: splits 1, 2, 3 and 4, and supplier PR #28094 on `main`. It is the first split that
uses the supplier.

`Roadmap: SchemeAndStackFoundations` (§2.10 `etaleToNisnevich`, `nisnevichToZariski`,
`comparison_comp`, `comparison_baseChange`; §2.12 `smallNisnevich_comparison`).

Port steps: delete `TauCeti/Lookahead/EpsilonFppfEtale/Stubs.lean`, and in the Nisnevich files
`Comparison.lean` and `Zariski.lean` replace its import with
`public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Basic`.

Files:

- `TauCeti/AlgebraicGeometry/Sites/Nisnevich/Comparison.lean` (121 lines, new):
  `etaleToNisnevich X A` with `etaleToNisnevich_obj`, `etaleToNisnevichAdjunction`, the
  `IsLeftAdjoint` and `PreservesFiniteLimits` instances, `constantSheafCompEtaleToNisnevichIso`,
  `coverPreserving_etalePullback_smallNisnevichTopology` (base change preserves Nisnevich coverings,
  through the stubbed `IsNisnevichCovering.of_isPullback`) with its `IsContinuous` instance, and
  `etaleToNisnevichBaseChangeIso` (`comparison_baseChange`, through split 1's
  `sheafInverseImageCompSheafPullbackIso`). `etaleToNisnevich`, its adjunction and
  `constantSheafCompEtaleToNisnevichIso` carry `@[expose]`, because `Zariski.lean` and the
  cohomology file of split 7 unfold them to the general `sheafInverseImage` statements.
- `TauCeti/AlgebraicGeometry/Sites/Nisnevich/Zariski.lean` (283 lines, new):
  `coverPreserving_restrictEtaleFunctor` (Zariski coverings are Nisnevich coverings) and the
  `IsContinuous` instance, `coverPreserving_restrictEtaleFunctor_smallEtaleTopology` and its
  `IsContinuous` instance, `nisnevichToZariski X A` (`Functor.sheafPullback` along
  `restrictEtaleFunctor`) with `nisnevichToZariskiAdjunction`, `IsLeftAdjoint`,
  `constantSheafCompNisnevichToZariskiIso` with `constantSheafCompNisnevichToZariskiIso_inv_app`
  (`nisnevichToZariski` and its adjunction carry `@[expose]`, as for `piX`),
  `nisnevichToZariskiCompEtaleToNisnevichIso`
  (`comparison_comp`: Zariski→Nisnevich→étale is the pullback from Zariski to étale sheaves),
  `constantSheafComp_nisnevichToZariskiCompEtaleToNisnevichIso_hom_app` (the comparisons of
  constant sheaves compose along it to the comparison for the pullback from Zariski to étale
  sheaves; checked on the constant section over the terminal object, where each comparison is a
  unit of an adjunction), `nisnevichToZariskiBaseChangeIso` (`comparison_baseChange`:
  compatibility with the pullbacks along `Opens.map g.base` and `Etale.pullback g`, the conjugate
  of `restrictEtaleFunctorCompEtalePullbackIso`) and the `PreservesFiniteLimits` instance (through
  split 2).

About 405 lines.

### Split 7: `feat: pullback of cohomology along the comparison morphisms between the small Zariski, Nisnevich and étale sites`

Needs first: splits 1–6 (and so supplier PR #28094). This is the last split of the current plan:
it carries the cohomology statements and the roadmap checks file.

`Roadmap: SchemeAndStackFoundations` (§2.10: the cohomology maps of
`quasiCoherent_topology_comparison` on the small sites, and `comparison_comp` on cohomology).

Files:

- `TauCeti/AlgebraicGeometry/Sites/Nisnevich/Cohomology.lean` (195 lines, new): the `Additive`
  instances for `etaleToNisnevich` and `nisnevichToZariski` on abelian sheaves,
  `etaleToNisnevichH X F n : Hⁿ(X_Nis, F) →+ Hⁿ(X_ét, F^ét)` with `equiv₀_etaleToNisnevichH`,
  `etaleToNisnevichH_zero_bijective` (on Nisnevich sheaves that are étale sheaves) and its
  corollary `etaleToNisnevichH_zero_bijective_of_etale` (on étale sheaves regarded as Nisnevich
  sheaves), `nisnevichToZariskiH X F n : Hⁿ(X_Zar, F) →+ Hⁿ(X_Nis, F^Nis)` with
  `equiv₀_nisnevichToZariskiH` (degree zero: restriction of global sections, at the terminal
  objects `⊤` and `isTerminalRestrictEtaleFunctorObjTop`), the `IsLeftAdjoint`,
  `PreservesFiniteLimits` (from `nisnevichToZariskiCompEtaleToNisnevichIso`) and `Additive`
  instances for the pullback of abelian sheaves from the Zariski site to the small étale site, and
  `map_etaleToNisnevichH_nisnevichToZariskiH` (`comparison_comp` on cohomology: the composite of
  `nisnevichToZariskiH` and `etaleToNisnevichH`, transported along
  `nisnevichToZariskiCompEtaleToNisnevichIso`, is `Sheaf.H.pullback` along the morphism of sites
  from the étale to the Zariski site with its canonical constant-sheaf comparison).
- `TauCeti/Examples/AlgebraicGeometry/Sites/Comparison.lean` (157 lines, new): the roadmap checks
  `test_comparison_id` and `test_aX_constant` (`a_X⁻¹` of the constant sheaf `ℤ/2` is the constant
  fppf sheaf `ℤ/2`), the same for `ε⁻¹`, exactness of `ε⁻¹`, `a_X⁻¹` and `etaleToNisnevich` on
  abelian sheaves, base change of `ε⁻¹`, `a_X⁻¹` and `etaleToNisnevich` on abelian sheaves, and
  `piXObjIso` on abelian sheaves; on cohomology, `aXH_apply` for `AddCommGrpCat.{u + 1}` (all
  hypotheses but `HasExt` discharged), `piXH_zero_bijective` for `AddCommGrpCat.{u + 1}`, `epsilonFppfEtaleH_zero_bijective_of_fpqc` for
  `main`'s `Ga X` and `Gm X` (importing `TauCeti.AlgebraicGeometry.Sites.Big.StructureSheaf`),
  `etaleToNisnevichH_zero_bijective_of_etale` for the restriction of `Ga X` to the small étale
  site (through `(Etale.forget X).sheafPushforwardContinuous`), and
  `map_etaleToNisnevichH_nisnevichToZariskiH` for
  `AddCommGrpCat.{u}`.

About 320 lines.

## What remains (status `partial`)

Still unproved from §2.10:

1. **`aX_inverseImage_obj`** (`a_X⁻¹ F (T) = Γ(T_ét, h⁻¹ F)` for `h : T ⟶ X`, Stacks
   59.100.1–2). The big étale half is `piXObjIso` (`π_X⁻¹ F (T) ≅ Γ(T_ét, h⁻¹ F)`). What remains is
   that `π_X⁻¹ F` is already an fppf sheaf: given that, `aXObjIsoOfIsSheaf` is the full statement
   (and `aXH_zero_bijective` its degree-zero cohomological form). This is fppf
   descent for the sheaf `T ↦ Γ(T_ét, h⁻¹ F)`, which in the Stacks Project goes through descent of
   étale morphisms (or algebraic spaces) along fppf coverings; nothing in Mathlib or on `main`
   supplies it yet, and no listed supplier pins it.
2. *(Done.)* `comparison_baseChange` for `piX` and `aX` (second session); the cohomology maps
   along every comparison morphism, which the comparison theorems below assert to be bijective
   (third session, splits 5 and 7); `comparison_comp` on cohomology for the small sites and the
   degree-zero descriptions of all five cohomology maps (fourth session, splits 5–7), and of
   `aXH` (eighth session, split 5).
3. **`quasiCoherent_topology_comparison`** (`H^q(X_Zar, F) = H^q(X_ét, F^a) = H^q(X_fppf, F^a)`,
   Stacks 35.9.3). It needs `big-sheaf` (open PR #29365; partial #27307), `qcoh-higher-direct-image-vanishing` (#27295)
   and the cohomology maps of splits 5 and 7. It is the statement that `nisnevichToZariskiH`,
   `etaleToNisnevichH`, `piXH` and `epsilonFppfEtaleH` are bijective on `F^a`. In degree zero this
   is the sheaf property of `F^a` for the finer topologies (fpqc descent of quasi-coherent
   modules), through the `*_zero_bijective` lemmas, which reduce it to the sheaf property (done for
   `ε` on fpqc sheaves, hence on `F = O` through `main`'s `Ga`, in the tenth session, and for
   `etaleToNisnevich` on étale sheaves, hence on the restriction of `Ga`, in the eleventh); in higher degrees it needs the vanishing of Čech
   cohomology of `F^a` on affine fpqc coverings (Stacks 35.9.2) and the comparison of Čech and
   derived cohomology. A practical obstacle: `HasExt`
   for `Sheaf X.smallEtaleTopology AddCommGrpCat.{u}` and for the big fppf site currently times
   out in instance synthesis at the default heartbeats; the cohomology API on `main`
   (`TauCeti/CategoryTheory/Sites/SheafCohomology/`) takes `HasExt` as a hypothesis, so the
   comparison theorems can do the same.
4. **`etale_pullback_fppf_comparison`** (Stacks 59.100.5–8) and
   **`smoothGroup_fppf_etale_comparison`** (Česnavičius 2018, Proposition 2.3).
5. Checks `test_zariski_not_etale` and `test_fppf_not_etale_mu_p` (they need §2.9's `μ_n` and the
   cohomology comparisons).

The split plan above lists only what is proved. The final split, which will carry the exported
cohomology comparison theorems and complete the target, is not yet planned in detail; it will
need every split above, and the plan's last split will move to it.
