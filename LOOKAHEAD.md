<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"epsilon-fppf-etale","main":"85f3eb5579df5ca44ba8cd0921d614b41ab72174","status":"partial","suppliers":["is-nisnevich-covering"],"splits":[{"n":1,"after":[],"title":"feat: the comparison morphism from the big fppf site to the big étale site"},{"n":2,"after":[1],"title":"feat: the comparison morphism from the small étale site to the small Nisnevich site"}]}-->

# Lookahead: `epsilon-fppf-etale` (SchemeAndStackFoundations §2.10)

Built on `main` at `85f3eb5579df5ca44ba8cd0921d614b41ab72174`. **Status: partial.** Two of the
four comparison morphisms of §2.10 are on this branch: `epsilonFppfEtale X` and
`etaleToNisnevich X`. Each is given through its exact inverse-image functor, together with its
adjunction to the direct image, preservation of constant sheaves, identity and composition
coherence, and (for `ε`) base change along `Y ⟶ X`. The remaining items are listed at the end.

## Stubbed declarations

All stubs are in `TauCeti/Lookahead/EpsilonFppfEtale/Stubs.lean`. They are the only `sorry`s on
the branch.

### `smallNisnevichTopology` (supplier `is-nisnevich-covering`, open PR #28094)

- `Suggested.lean`: **not pinned there.** The roadmap's `Suggested.lean` §2.12 pins only
  `IsNisnevichCovering`, `nisnevichPrecoverage`, `nisnevichTopology`,
  `zariskiTopology_le_nisnevichTopology` and `nisnevichTopology_le_etaleTopology`. The README's
  §2.12 pins "`smallNisnevichTopology X` on `X.Etale`".
- PR #28094's diff (`TauCeti/AlgebraicGeometry/Sites/Nisnevich/Basic.lean`):
  ```lean
  def smallNisnevichTopology (X : Scheme.{u}) : GrothendieckTopology X.Etale :=
    (Scheme.Etale.forget X).restrictedTopology (nisnevichTopology.over X)
  ```
  in `namespace TauCeti.AlgebraicGeometry.Scheme`.
- Stub:
  ```lean
  noncomputable def smallNisnevichTopology (X : Scheme.{u}) : GrothendieckTopology X.Etale :=
    sorry
  ```
  in `namespace TauCeti.AlgebraicGeometry.Scheme`.
- Differences: the body is `sorry`, so the stub is marked `noncomputable`. The PR's `def` is
  computable. Swapping in the landed declaration only means deleting the stub. The proofs never
  use the body.

### `smallNisnevichTopology_le_smallEtaleTopology` (supplier `is-nisnevich-covering`, open PR #28094)

- `Suggested.lean`: **not pinned there.** The README's §2.12 lists it as
  `smallNisnevichTopology_le_smallEtale`.
- PR #28094's diff:
  ```lean
  theorem smallNisnevichTopology_le_smallEtaleTopology (X : Scheme.{u}) :
      smallNisnevichTopology X ≤ X.smallEtaleTopology := by
  ```
- Stub: the same statement, with the same name and namespace (`TauCeti.AlgebraicGeometry.Scheme`),
  proved by `sorry`.
- Differences: the name follows the PR (`…_le_smallEtaleTopology`) rather than the README's
  shortened `…_le_smallEtale`, since the PR is what will land.

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

### Split 2: `feat: the comparison morphism from the small étale site to the small Nisnevich site`

Needs first: split 1, and supplier PR #28094 on `main`.

Roadmap attribution: `Roadmap: SchemeAndStackFoundations` (§2.10 `etaleToNisnevich`; §2.12
`smallNisnevich_comparison`).

Port steps: delete `TauCeti/Lookahead/EpsilonFppfEtale/Stubs.lean`, and in
`Nisnevich/Comparison.lean` replace its import with
`public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Basic`.

Files:

- `TauCeti/AlgebraicGeometry/Sites/Nisnevich/Comparison.lean` (81 lines, new), namespace
  `AlgebraicGeometry.Scheme`: `etaleToNisnevich X A` with `etaleToNisnevich_obj`,
  `etaleToNisnevichAdjunction`, the `IsLeftAdjoint` and `PreservesFiniteLimits` instances, and
  `constantSheafCompEtaleToNisnevichIso`.
- `TauCeti/Examples/AlgebraicGeometry/Sites/Comparison.lean` (54 lines, new): the roadmap check
  `test_comparison_id` (comparing the small étale topology with itself gives the identity), the
  `ε`-analogue of `test_aX_constant` (`ε⁻¹` of the constant étale sheaf `ℤ/2` is the constant
  fppf sheaf `ℤ/2`), exactness of `ε⁻¹` and of `etaleToNisnevich` on abelian sheaves, and base
  change of `ε⁻¹` on abelian sheaves (`AddCommGrpCat.{u+1}`, where every instance is found
  automatically).

About 135 lines. This split is small, but it is the only one that depends on the supplier.

## What remains (status `partial`)

Still unproved from §2.10:

1. **`aX`** (`Sh((Sch/X)_fppf) → Sh(X_ét)`) and **`aX_inverseImage_obj`**
   (`a_X⁻¹ F (T) = Γ(T_ét, F|_T)`, Stacks 59.100.1–2). The inverse image should be
   `π_X⁻¹ ⋙ ε⁻¹`, where `π_X⁻¹` is `Functor.sheafPullback` along the inclusion `X.Etale ⥤ Over X`.
   Three things are missing:
   - continuity of the inclusion from `X.smallEtaleTopology` to `etaleTopology.over X`. Mathlib
     defines the small site as an induced topology of `overGrothendieckTopology @Etale X`, and a
     comparison with `etaleTopology.over X` is needed first;
   - representable flatness of the inclusion;
   - exactness of `π_X⁻¹`. Mathlib's `lan_preservesFiniteLimits_of_flat` requires both categories
     to be small, and `X.Etale` is not. The fix is to generalise it to a functor whose
     costructured-arrow categories are small enough for the coefficient category's filtered
     colimits.
2. **`nisnevichToZariski`** (`Sh(X_Nis) → Sh(X_Zar)`): `Functor.sheafPullback` along
   `X.Opens ⥤ X.Etale`. Here the comma categories are small, because `X.Opens` is. Continuity
   into `smallNisnevichTopology X` needs the supplier's definition of that topology, which the
   pinned API does not expose, so it can only be done once #28094 has landed.
3. **`comparison_comp`** for the composites that involve these two morphisms. The same-category
   case is `sheafInverseImageTrans`. **`comparison_baseChange`** for the small-site morphisms.
   The `ε` case is `epsilonFppfEtaleBaseChangeIso`.
4. **`quasiCoherent_topology_comparison`** (`H^q(X_Zar, F) = H^q(X_ét, F^a) = H^q(X_fppf, F^a)`,
   Stacks 35.9.3). It needs `big-sheaf` (#27307), `qcoh-higher-direct-image-vanishing` (#27295)
   and `Sheaf.H.pullback` (on `main`) along `ε⁻¹`, whose constant-sheaf comparison is
   `constantSheafCompEpsilonFppfEtaleIso`. A practical obstacle: `HasExt` for
   `Sheaf X.smallEtaleTopology AddCommGrpCat.{u}` and for the big fppf site currently times out
   in instance synthesis at the default heartbeats.
5. **`etale_pullback_fppf_comparison`** (Stacks 59.100.5–8) and
   **`smoothGroup_fppf_etale_comparison`** (Česnavičius 2018, Proposition 2.3).
6. Checks `test_aX_constant` (for `aX` itself), `test_zariski_not_etale` and
   `test_fppf_not_etale_mu_p`.

The final split, which carries the exported cohomology comparison theorems and completes the
target, is not yet planned in detail. It will need every split above.
