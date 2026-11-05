<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"epsilon-fppf-etale","main":"e8758b7b2f82b9b1c3f33b992ab8f499b510240f","status":"partial","suppliers":["is-nisnevich-covering"],"splits":[{"n":1,"after":[],"title":"feat: the comparison morphism from the big fppf site to the big étale site"},{"n":2,"after":[],"title":"feat: left Kan extension along a flat functor is exact without smallness assumptions"},{"n":3,"after":[1,2],"title":"feat: the comparison morphism from the big fppf site to the small étale site"},{"n":4,"after":[1,2,3],"title":"feat: the comparison morphisms between the small Zariski, Nisnevich and étale sites"}]}-->

# Lookahead: `epsilon-fppf-etale` (SchemeAndStackFoundations §2.10)

Built on `main` at `e8758b7b2f82b9b1c3f33b992ab8f499b510240f`. **Status: partial.** All four
comparison morphisms of §2.10 are on this branch, each through its exact inverse-image functor and
its adjunction with the direct image: `epsilonFppfEtale X` (`ε⁻¹`), `aX X` (`a_X⁻¹ = π_X⁻¹ ⋙ ε⁻¹`,
with `piX X` the inverse image from the small to the big étale site), `etaleToNisnevich X` and
`nisnevichToZariski X`. Each sends constant sheaves to constant sheaves. `comparison_comp` is on the
branch for the composites (`sheafInverseImageTrans`, `aX` by definition, and
`nisnevichToZariskiCompEtaleToNisnevichIso`), `comparison_baseChange` for `ε`. The roadmap checks
`test_comparison_id` and `test_aX_constant` (for `aX` itself) are in the examples file. Not yet
proved: `aX_inverseImage_obj`, `comparison_baseChange` on the small sites, and the cohomology
comparison theorems; see the end.

## Stubbed declarations

All stubs are in `TauCeti/Lookahead/EpsilonFppfEtale/Stubs.lean`. They are the only `sorry`s on
the branch. All come from supplier `is-nisnevich-covering` (open PR #28094, module
`TauCeti.AlgebraicGeometry.Sites.Nisnevich.Basic`). The roadmap's `Suggested.lean` §2.12 pins
only `IsNisnevichCovering`, `nisnevichPrecoverage`, `nisnevichTopology`,
`zariskiTopology_le_nisnevichTopology` and `nisnevichTopology_le_etaleTopology`; the README's
§2.12 additionally pins `smallNisnevichTopology X` on `X.Etale`, *isNisnevichCovering_of_zariski*
and `smallNisnevichTopology_le_smallEtale`. The stubs follow the PR's current diff (re-read this
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
- `qcoh-higher-direct-image-vanishing` (#27295) and `big-sheaf` (#27307) are needed only by the
  cohomology comparisons, which are not yet proved, so they are not stubbed.

## Splits

### Split 1: `feat: the comparison morphism from the big fppf site to the big étale site`

Needs first: none. It uses no supplier and can be opened on `main` now.

Roadmap attribution: `Roadmap: SchemeAndStackFoundations` (§2.10 `epsilonFppfEtale`,
`comparison_comp`, `comparison_baseChange`).

Files:

- `TauCeti/CategoryTheory/Sites/InverseImageOfLE.lean` (177 lines, new), namespace
  `CategoryTheory.GrothendieckTopology`. This is the general comparison for topologies `J ≤ K`
  on one category:
  - `sheafDirectImageOfLE` with `_obj_obj` and `_map_hom` (simp lemmas),
    `fullyFaithfulSheafDirectImageOfLE` and the `Full`/`Faithful` instances,
    `sheafDirectImageOfLE_comp`;
  - `sheafInverseImage J K A` (the `K`-sheafification of a `J`-sheaf) with `_obj` and `_map`
    (simp lemmas), and a `PreservesFiniteLimits` instance (exactness);
  - `sheafAdjunctionOfLE` (inverse image ⊣ direct image), the `IsRightAdjoint` instance and
    `preservesColimits_sheafInverseImage`;
  - `sheafInverseImageRefl` (comparing a topology with itself gives the identity) and
    `sheafInverseImageTrans` (composition coherence, the general form of `comparison_comp`);
  - `presheafToSheafCompSheafInverseImageIso` and `constantSheafCompSheafInverseImageIso`
    (constant sheaves go to constant sheaves);
  - `sheafInverseImageCompSheafPushforwardContinuousIso` (base change along a functor that is
    continuous and cocontinuous, the general form of `comparison_baseChange`).
- `TauCeti/AlgebraicGeometry/Sites/Comparison.lean` (110 lines, new), namespace
  `AlgebraicGeometry.Scheme`:
  - `etalePrecoverage_le_fppfPrecoverage`, `etaleTopology_le_fppfTopology` and
    `etaleTopology_over_le_fppfTopology_over`;
  - `epsilonFppfEtale X A` (the inverse image `ε⁻¹`) with `epsilonFppfEtale_obj`,
    `epsilonFppfEtaleAdjunction`, the `IsLeftAdjoint` and `PreservesFiniteLimits` instances,
    `constantSheafCompEpsilonFppfEtaleIso`, and `epsilonFppfEtaleBaseChangeIso` (base change
    along `g : Y ⟶ X`, through `overMapPullback`).

About 290 lines in total.

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

Needs first: splits 1 and 2. Uses no supplier. `Roadmap: SchemeAndStackFoundations` (§2.10 `aX`,
`comparison_comp`).

Files:

- `TauCeti/CategoryTheory/Sites/ConstantSheaf.lean` (existing, +9 lines): the natural isomorphism
  `Functor.constantSheafCompSheafPullbackIso` (for `u` final) built from the existing pointwise
  `sheafPullbackConstantSheafIso` and its naturality.
- `TauCeti/AlgebraicGeometry/Sites/SmallEtaleComparison.lean` (147 lines, new), namespace
  `AlgebraicGeometry.Scheme`: `coverPreserving_etaleForget`, the `RepresentablyFlat` and
  `IsContinuous` instances for `Etale.forget X`, `piX X A` (`Functor.sheafPullback` along
  `Etale.forget X`) with `piXAdjunction`, `IsLeftAdjoint` and `constantSheafCompPiXIso`;
  `aX X A := piX X A ⋙ epsilonFppfEtale X A` with `aXAdjunction`, `IsLeftAdjoint` and
  `constantSheafCompAXIso`; and `PreservesFiniteLimits` instances for `piX` and `aX` for concrete
  coefficients with sections in `Type (u + 1)` (through split 2).

About 160 lines.

### Split 4: `feat: the comparison morphisms between the small Zariski, Nisnevich and étale sites`

Needs first: splits 1, 2 and 3, and supplier PR #28094 on `main`. This is the last split of the
current plan and the only one that uses the supplier.

`Roadmap: SchemeAndStackFoundations` (§2.10 `etaleToNisnevich`, `nisnevichToZariski`,
`comparison_comp`; §2.12 `smallNisnevich_comparison`).

Port steps: delete `TauCeti/Lookahead/EpsilonFppfEtale/Stubs.lean`, and in both Nisnevich files
replace its import with `public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Basic`.

Files:

- `TauCeti/AlgebraicGeometry/Sites/OpensEtale.lean` (112 lines, new; uses no supplier, and could
  be opened earlier as its own PR if a reviewer prefers), namespace `AlgebraicGeometry.Scheme`:
  `restrictEtaleFunctor X : X.Opens ⥤ X.Etale` with `_obj_hom`/`_map_left`,
  `restrictEtaleFunctor_hom_ext`, `Etale.liftOpens` and `Etale.liftOpens_ι`,
  `restrictEtaleFunctorLift`, `range_subset_of_hom_restrictEtaleFunctor_obj` and the
  `RepresentablyFlat` instance.
- `TauCeti/AlgebraicGeometry/Sites/Nisnevich/Comparison.lean` (81 lines, new):
  `etaleToNisnevich X A` with `etaleToNisnevich_obj`, `etaleToNisnevichAdjunction`, the
  `IsLeftAdjoint` and `PreservesFiniteLimits` instances, and `constantSheafCompEtaleToNisnevichIso`.
- `TauCeti/AlgebraicGeometry/Sites/Nisnevich/Zariski.lean` (145 lines, new):
  `coverPreserving_restrictEtaleFunctor` (Zariski coverings are Nisnevich coverings) and the
  `IsContinuous` instance, `coverPreserving_restrictEtaleFunctor_smallEtaleTopology` and its
  `IsContinuous` instance, `nisnevichToZariski X A` (`Functor.sheafPullback` along
  `restrictEtaleFunctor`) with `nisnevichToZariskiAdjunction`, `IsLeftAdjoint`,
  `constantSheafCompNisnevichToZariskiIso`, `nisnevichToZariskiCompEtaleToNisnevichIso`
  (`comparison_comp`: Zariski→Nisnevich→étale is the pullback from Zariski to étale sheaves) and
  the `PreservesFiniteLimits` instance (through split 2).
- `TauCeti/Examples/AlgebraicGeometry/Sites/Comparison.lean` (70 lines, new): the roadmap checks
  `test_comparison_id` and `test_aX_constant` (`a_X⁻¹` of the constant sheaf `ℤ/2` is the constant
  fppf sheaf `ℤ/2`), the same for `ε⁻¹`, exactness of `ε⁻¹`, `a_X⁻¹` and `etaleToNisnevich` on
  abelian sheaves, and base change of `ε⁻¹` on abelian sheaves.

About 410 lines.

## What remains (status `partial`)

Still unproved from §2.10:

1. **`aX_inverseImage_obj`** (`a_X⁻¹ F (T) = Γ(T_ét, h⁻¹ F|_T)` for `h : T ⟶ X`, Stacks
   59.100.1–2). This needs the small étale pullback `h⁻¹ : Sh(X_ét) ⥤ Sh(T_ét)` (not on `main`
   or in Mathlib; it would be `Functor.sheafPullback` along `MorphismProperty.Over.pullback`
   `X.Etale ⥤ T.Etale`), the identification of `π_X⁻¹ F (T)` with `Γ(T_ét, h⁻¹F)` (the presheaf
   `T ↦ Γ(T_ét, h⁻¹F)` is already a big étale sheaf), and fppf descent for it (so that `ε⁻¹`
   does not change its values).
2. **`comparison_baseChange`** for `aX`, `piX`, `etaleToNisnevich` and `nisnevichToZariski`
   along `g : Y ⟶ X`, which needs the same small-site pullbacks. The `ε` case is
   `epsilonFppfEtaleBaseChangeIso`.
3. **`quasiCoherent_topology_comparison`** (`H^q(X_Zar, F) = H^q(X_ét, F^a) = H^q(X_fppf, F^a)`,
   Stacks 35.9.3). It needs `big-sheaf` (#27307), `qcoh-higher-direct-image-vanishing` (#27295)
   and `Sheaf.H.pullback` (on `main`) along `ε⁻¹` and `a_X⁻¹`. A practical obstacle: `HasExt`
   for `Sheaf X.smallEtaleTopology AddCommGrpCat.{u}` and for the big fppf site currently times
   out in instance synthesis at the default heartbeats.
4. **`etale_pullback_fppf_comparison`** (Stacks 59.100.5–8) and
   **`smoothGroup_fppf_etale_comparison`** (Česnavičius 2018, Proposition 2.3).
5. Checks `test_zariski_not_etale` and `test_fppf_not_etale_mu_p` (they need §2.9's `μ_n` and the
   cohomology comparisons).

The split plan above lists only what is proved. The final split, which will carry the exported
cohomology comparison theorems and complete the target, is not yet planned in detail; it will
need every split above, and the plan's last split will move to it.
