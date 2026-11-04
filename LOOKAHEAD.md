<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"cohomology-with-support","main":"333c9e49143de812ed1452b412193ee9c05501e7","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: degree zero of local cohomology is the power torsion"},{"n":2,"after":[],"title":"feat: cohomology with supports in the whole space is ordinary cohomology"},{"n":3,"after":[],"title":"feat: pullback of cohomology with supports"},{"n":4,"after":[1],"title":"feat: local cohomology vanishes below the depth and not in degree the depth"},{"n":5,"after":[1],"title":"feat: Noetherian local cohomology computes derived power torsion"},{"n":6,"after":[5],"title":"feat: flat base change of Noetherian local cohomology"},{"n":7,"after":[1,2,3,4,5,6],"title":"feat: geometric comparison of local cohomology and the section 2.7 checks"}]}-->

# Lookahead: `cohomology-with-support` (SchemeAndStackFoundations §2.7)

Built on `main` at `333c9e49143de812ed1452b412193ee9c05501e7`. Status: **partial**.

## Suppliers: both have landed, so no stub remains

Session 3 deleted `TauCeti/Lookahead/CohomologyWithSupport/Stubs.lean`. Nothing on the branch had
imported it, and `main` now carries every declaration it stubbed:

- `sheaf-h-pullback`: the stubbed `CategoryTheory.Sheaf.H.pullback pb c G n` and
  `pullback_naturality` landed **verbatim** (same binders, same argument order `pullback pb c G n`)
  in `TauCeti/CategoryTheory/Sites/SheafCohomology/Pullback.lean` via PR #22647 (merged by Bors).
  `main` also has `pullback_apply`, `addEquiv₀_pullback`, `pullback_id`, `pullback_comp_apply` and
  `equiv₀_pullback_sheafPullback`. The README pins
  "`Sheaf.H.pullback pb G n : G.H n →+ [pb.obj G].H n`" with `pb = u.sheafPullback`; what landed
  instead takes an arbitrary exact additive `pb` and an extra comparison map
  `c : ℤ_K ⟶ pb ℤ_J`. Still open (PR #27242, higher direct images along a morphism of sites) is the
  rest of that item, and nothing here consumes it.
- `qcoh-higher-direct-image-vanishing`: the pinned `Suggested.lean` statement

  ```lean
  theorem higherDirectImage_vanishing {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
      [QuasiSeparated f] [IsAffine S] :
      ∃ N : ℕ, ∀ (F : X.Modules) [F.IsQuasicoherent] (p : ℕ), N ≤ p →
        Subsingleton (Scheme.Modules.Cohomology F p) := by
    sorry
  ```

  landed with exactly this statement, under the name
  `AlgebraicGeometry.Scheme.Hom.exists_subsingleton_cohomology_of_isAffine`
  (`TauCeti/AlgebraicGeometry/Cohomology/QuasiSeparated.lean`, PR #22975, merged by Bors). The
  earlier stub `TauCeti.QCoh.higherDirectImage_vanishing` therefore had to go. Split 7 should use
  the landed name. PR #27295 (localization of quasi-coherent cohomology) is still open, and nothing
  here needs it.

## What is proved (no `sorry`, no stub)

### `TauCeti/Algebra/Homology/LocalCohomology/DegreeZero.lean` (174 lines, session 1)

This file proves the pinned `Supports.localCohomology_degreeZero`:

```lean
theorem localCohomology_degreeZero (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) :
    Nonempty ((localCohomology I 0).obj M ≃
      {m : M // ∃ n : ℕ, ∀ a ∈ I ^ n, a • m = 0})
```

as `TauCeti.Supports.localCohomology_degreeZero`. It goes through:

- `preservesFiniteLimits_linearYoneda_obj`;
- `extZeroIso : (Ext A (ModuleCat A) 0).flip.obj M ≅ (linearYoneda A _).obj M`;
- `homDiagram`, `localCohomologyZeroIso`, `evalOne` (with `evalOne_apply`), `evalOneCocone`,
  `localCohomologyZeroToModule`;
- `localCohomologyZeroToModule_injective`, `range_localCohomologyZeroToModule`;
- the helpers `quotient_linearMap_eq_zero`, `smul_apply_mk_one_eq_zero`,
  `desc_evalOneCocone_ι_apply`, `desc_evalOneCocone_injective`, `range_desc_evalOneCocone`.

### `TauCeti/Topology/Sheaves/SupportedCohomology/Univ.lean` (83 lines, session 2)

This file proves the `Z = X` half of `cohomologyWithSupport_univ`. The `Z = ∅` half is `main`'s
`CategoryTheory.Sheaf.subsingleton_supportedH_of_le_compl`. Declarations:

- `TauCeti.CategoryTheory.isZero_freeYonedaSheafFunctor_obj_bot`;
- instance `isIso_cokernel_π_complInclusion_top`;
- `supportedHTopEquiv : F.supportedH ⊤ W n ≃+ F.H' n W`;
- `supportedHTopEquiv_apply`, `toH'_complInclusion_top_bijective`.

### Session 3: local cohomology and depth

`TauCeti/Algebra/Homology/Ext/ProjectiveResolution.lean` gains 138 lines (now 274), in namespace
`TauCeti`:

- `ShortComplex.injective_homologyMap_moduleCat` and
  `HomologicalComplex.injective_homologyMap_moduleCat`: a morphism of complexes of modules is
  injective on homology once every cycle that maps to a boundary is a boundary.
- `Ext_map_comp_isoExt_hom`: `ProjectiveResolution.isoExt` is natural in the first argument.
  Given a chain map `P' ⟶ P` over `g : X' ⟶ X`, the map `((Ext k C n).map g.op).app Y` becomes
  the induced map on the cohomology of `Hom`-complexes.
- `injective_Ext_map_succ`: if precomposition `(Ext.mk₀ g).comp` is injective on the
  derived-category `Ext X Y (p + 1)`, then the projective-resolution `Ext` map along `g` is
  injective. The proof matches cocycles via `extMk_eq_zero_iff` and `mk₀_comp_extMk`.
- `isZero_Ext_succ_iff_subsingleton (X Y : C) (p : ℕ)`:
  `IsZero (((Ext k C (p + 1)).obj (op X)).obj Y) ↔ Subsingleton (Abelian.Ext X Y (p + 1))`.

Mathlib's projective-resolution `Ext` (the one `localCohomology` is built on) and its
derived-category `Ext` (the one `Ideal.depth` is built on) are both the cohomology of `Hom(P, Y)`.
These lemmas compare them in positive degrees, for both vanishing and injectivity.

`TauCeti/Algebra/Homology/LocalCohomology/Depth.lean` (208 lines, new), in namespace
`TauCeti.Supports`:

- `isZero_Ext_iff_subsingleton`: the vanishing comparison in all degrees for modules; degree `0`
  goes through `extZeroIso` and `Ext.homEquiv₀`.
- `isZero_localCohomology_of_subsingleton_ext`: `H^q_I(M) = 0` once every `Ext^q(A/Iⁿ, M)`
  vanishes.
- `subsingleton_ext_of_support_subset`: Rees' theorem in the form needed here. For `A`
  Noetherian, `M` finite, `I M ≠ M` and `q < depth_I M`, `Ext^q(N, M) = 0` for every finite `N`
  with `Supp N ⊆ V(I)`.
- `subsingleton_ext_quotient_pow_of_lt_depth`: `Ext^q(A/Iⁿ, M) = 0` for `q < depth_I M`. If
  `I M = M`, the annihilators are comaximal; otherwise the previous lemma applies.
- **`depth_localCohomology_vanishing`** (`@[stacks 0AVZ]`): for `[IsNoetherianRing A]`,
  `[Module.Finite A M]` and `(q : ℕ∞) < I.depth M`, `IsZero ((localCohomology I q).obj M)`.
- `injective_ext_precomp_quotient`: for `p + 1 ≤ depth_I M`, precomposition with
  `A ⧸ Iᵐ → A ⧸ I¹` is injective on `Ext^{p+1}(−, M)`. This uses the long exact sequence
  `Ext.contravariant_sequence_exact₃` of `0 → ker → A/Iᵐ → A/I → 0`, and the kernel is supported
  in `V(I)`.
- `injective_Ext_map_quotient`: the transition maps `Ext^d(A/I¹, M) → Ext^d(A/Iᵐ, M)` of the
  system defining `H^d_I(M)` are injective for `d ≤ depth_I M`. Degree `0` goes through the
  naturality of `extZeroIso`.
- **`depth_localCohomology_nonvanishing`** (`@[stacks 0BUW]`): for `[IsNoetherianRing A]`,
  `[Module.Finite A M]` and `d : ℕ` with `I.depth M = d`,
  `Nontrivial ((localCohomology I d).obj M)`. The group `Ext^d(A/I¹, M)` is nonzero by
  `ModuleCat.depth_eq_iff`, and it injects into the filtered colimit by
  `Concrete.colimit_rep_eq_zero`.
- **`depth_localCohomology_zero_guard`**: for `[Subsingleton M]` over any commutative ring,
  `I.depth M = ⊤ ∧ ∀ q, IsZero ((localCohomology I q).obj M)`. This is the README check of that
  name.

`Suggested.lean` pins neither depth statement. Both are stated from the README wording:
"`H^q_I(M) = 0` when `(q : ℕ∞) < depth_I M`" (as `IsZero` of the `ModuleCat` object) and
"`H^d_I(M) ≠ 0` only for `d : ℕ` with `depth_I M = d`" (as `Nontrivial`).

## What `main` already has (found in session 2)

`sectionsWithSupport` is `CategoryTheory.Sheaf.supportedSections F S W`
(`TauCeti/Topology/Sheaves/SupportedCohomology.lean`). `supportedSubsheaf` is
`supportedSectionsSheaf`. `cohomologyWithSupport` is `supportedH`, with `supportedHZeroEquiv` for
degree zero. `localCohomologySheaf` is `supportedHSheaf`, with `supportedHSheafZeroIso`. The long
exact sequence of `supports_localization_triangle` is `relativeH'.exact_toH'_cohomologyPresheaf_map`,
`exact_cohomologyPresheaf_map_δ` and `exact_δ_toH'`. Excision is `supportedHExcisionEquiv`.

## What remains

- `cohomologyWithSupport_pullback` (split 3): `Sheaf.H.pullback` is on `main`, so this can be
  written directly. It needs `pb` to carry the relative free sheaf `ℤ_{W, W ∖ S}` to its pullback.
- `rHZ_adjunction` and `localToGlobal`: derived-category statements; `main` has only the edge map
  `supportedHEdgeEquiv`.
- `localCohomology_colimit_ext_comparison` (split 5); `Supports.localCohomology_flat_baseChange`
  and flat excision (split 6).
- Split 7:
  - `localCohomology_module_comparison`, using
    `Scheme.Hom.exists_subsingleton_cohomology_of_isAffine`;
  - the scheme wrappers with the `O(X)`-module structure, thin wrappers of `main`'s topological API;
  - the checks `test_support_all` (from `supportedHTopEquiv` at `n = 1`), `test_support_empty`,
    `test_support_affine_line_origin`, `test_support_not_restriction`, `test_depth_dvr`,
    `localCohomology_module_comparison_nil_ideal` and `localCohomology_module_comparison_dvr`.

## Split plan

1. **feat: degree zero of local cohomology is the power torsion**. After: none.
   `TauCeti/Algebra/Homology/LocalCohomology/DegreeZero.lean` (done); the declarations listed
   above.
2. **feat: cohomology with supports in the whole space is ordinary cohomology**. After: none.
   `TauCeti/Topology/Sheaves/SupportedCohomology/Univ.lean` (done):
   `isZero_freeYonedaSheafFunctor_obj_bot`, `isIso_cokernel_π_complInclusion_top`,
   `supportedHTopEquiv`, `supportedHTopEquiv_apply`, `toH'_complInclusion_top_bijective`.
3. **feat: pullback of cohomology with supports**. After: none (not yet written).
   `cohomologyWithSupport_pullback` via `main`'s `Sheaf.H.pullback`.
4. **feat: local cohomology vanishes below the depth and not in degree the depth**. After: 1
   (done, about 345 lines). `TauCeti/Algebra/Homology/Ext/ProjectiveResolution.lean` (+138 lines):
   `ShortComplex.injective_homologyMap_moduleCat`,
   `HomologicalComplex.injective_homologyMap_moduleCat`, `Ext_map_comp_isoExt_hom`,
   `injective_Ext_map_succ`, `isZero_Ext_succ_iff_subsingleton`.
   `TauCeti/Algebra/Homology/LocalCohomology/Depth.lean` (208 lines): `isZero_Ext_iff_subsingleton`,
   `isZero_localCohomology_of_subsingleton_ext`, `subsingleton_ext_of_support_subset`,
   `subsingleton_ext_quotient_pow_of_lt_depth`, `depth_localCohomology_vanishing`,
   `injective_ext_precomp_quotient`, `injective_Ext_map_quotient`,
   `depth_localCohomology_nonvanishing`, `depth_localCohomology_zero_guard`.
5. **feat: Noetherian local cohomology computes derived power torsion**. After: 1 (not yet written).
   `localCohomology_colimit_ext_comparison`.
6. **feat: flat base change of Noetherian local cohomology**. After: 5 (not yet written).
   `Supports.localCohomology_flat_baseChange`, flat excision.
7. **feat: geometric comparison of local cohomology and the section 2.7 checks**. After: 1–6 (not
   yet written). `localCohomology_module_comparison`, the scheme wrappers and the remaining §2.7
   checks. This is the only split that completes the target.
