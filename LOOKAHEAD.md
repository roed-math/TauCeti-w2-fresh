<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"cohomology-with-support","main":"ab1c5af023f864980704684df6008c9288ab4fcf","status":"partial","suppliers":["sheaf-h-pullback","qcoh-higher-direct-image-vanishing"],"splits":[{"n":1,"after":[],"title":"feat: degree zero of local cohomology is the power torsion"},{"n":2,"after":[],"title":"feat: cohomology with supports in the whole space is ordinary cohomology"},{"n":3,"after":[],"title":"feat: pullback of cohomology with supports"},{"n":4,"after":[1],"title":"feat: Noetherian local cohomology computes derived power torsion"},{"n":5,"after":[4],"title":"feat: flat base change of Noetherian local cohomology"},{"n":6,"after":[1,2,3,4,5],"title":"feat: geometric comparison and depth vanishing for local cohomology"}]}-->

# Lookahead: `cohomology-with-support` (SchemeAndStackFoundations §2.7)

Built on `main` at `ab1c5af023f864980704684df6008c9288ab4fcf`. Status: **partial**.

## What is proved

`TauCeti/Algebra/Homology/LocalCohomology/DegreeZero.lean` (no `sorry`, no stub used) proves the
pinned target

```lean
theorem localCohomology_degreeZero (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) :
    Nonempty ((localCohomology I 0).obj M ≃
      {m : M // ∃ n : ℕ, ∀ a ∈ I ^ n, a • m = 0})
```

as `TauCeti.Supports.localCohomology_degreeZero`, via:

- `TauCeti.Supports.preservesFiniteLimits_linearYoneda_obj` (instance: `Hom(−, Y)` is left exact
  on any `R`-linear category);
- `TauCeti.Supports.extZeroIso : (Ext A (ModuleCat A) 0).flip.obj M ≅ (linearYoneda A _).obj M`
  (from `Functor.leftDerivedZeroIsoSelf`);
- `localCohomologyZeroIso : (localCohomology I 0).obj M ≅ colimit (homDiagram I M)`, where
  `homDiagram I M` is `n ↦ Hom(A ⧸ Iⁿ, M)`;
- `evalOne`, `evalOneCocone`, `localCohomologyZeroToModule` (evaluation at `1`), with
  `localCohomologyZeroToModule_injective` and `range_localCohomologyZeroToModule` (the image is the
  `I`-power torsion), plus the helpers `quotient_linearMap_eq_zero`, `smul_apply_mk_one_eq_zero`,
  `desc_evalOneCocone_ι_apply`, `desc_evalOneCocone_injective`, `range_desc_evalOneCocone`.

## Also proved (session 2)

`TauCeti/Topology/Sheaves/SupportedCohomology/Univ.lean` (no `sorry`, no stub used) proves the
`Z = X` half of the pinned `cohomologyWithSupport_univ` (the `Z = ∅` half is main's
`CategoryTheory.Sheaf.subsingleton_supportedH_of_le_compl`):

- `TauCeti.CategoryTheory.isZero_freeYonedaSheafFunctor_obj_bot`: `ℤ_∅ = 0`;
- instance `TauCeti.CategoryTheory.isIso_cokernel_π_complInclusion_top`: `ℤ_W ≅ ℤ_{W, W ∖ X}`;
- `TauCeti.CategoryTheory.supportedHTopEquiv : F.supportedH ⊤ W n ≃+ F.H' n W`, with
  `supportedHTopEquiv_apply` (it is `relativeH'.toH'`) and `toH'_complInclusion_top_bijective`.

## What `main` already has (found in session 2)

Most of the topological half of §2.7 landed on `main` under other names, so it is not re-proved:
`sectionsWithSupport` is `CategoryTheory.Sheaf.supportedSections F S W`
(`TauCeti/Topology/Sheaves/SupportedCohomology.lean`); `supportedSubsheaf` is
`supportedSectionsSheaf` (`TauCeti/Topology/Sheaves/LocalCohomology.lean`);
`cohomologyWithSupport` is `supportedH` (relative cohomology `Hⁿ(W, W ∖ S; F)`, with
`cohomologyWithSupport_zero` = `supportedHZeroEquiv`); `localCohomologySheaf` is
`supportedHSheaf` (with `supportedHSheafZeroIso`); the long exact sequence of
`supports_localization_triangle` is `relativeH'.exact_toH'_cohomologyPresheaf_map`,
`exact_cohomologyPresheaf_map_δ`, `exact_δ_toH'`; excision is `supportedHExcisionEquiv`.

## What remains

- `cohomologyWithSupport_pullback` (consumes the `Sheaf.H.pullback` stub; split 3);
- `rHZ_adjunction` and `localToGlobal` (derived-category statements; main has the edge map
  `supportedHEdgeEquiv` only);
- `localCohomology_colimit_ext_comparison` (split 4), `Supports.localCohomology_flat_baseChange`
  and flat excision (split 5);
- `localCohomology_module_comparison` (uses the `QCoh.higherDirectImage_vanishing` stub),
  `depth_localCohomology_vanishing`, `depth_localCohomology_nonvanishing`, and the checks
  `test_support_all` (from `supportedHTopEquiv` at `n = 1`), `test_support_empty`,
  `test_support_affine_line_origin`, `test_support_not_restriction`, `test_depth_dvr`,
  `localCohomology_module_comparison_nil_ideal`, `localCohomology_module_comparison_dvr`,
  `depth_localCohomology_zero_guard` (split 6). The scheme-level wrappers with the `O(X)`-module
  structure are not yet written; they should be thin wrappers of main's topological API.

## Stubbed declarations (`TauCeti/Lookahead/CohomologyWithSupport/Stubs.lean`)

### `sheaf-h-pullback` — `CategoryTheory.Sheaf.H.pullback`, `pullback_naturality`

`Suggested.lean` pins no Lean signature for this item (no `H.pullback` occurs in
`SchemeAndStackFoundations/Suggested.lean`); the README pins
"`Sheaf.H.pullback pb G n : G.H n →+ [pb.obj G].H n`". Source of the stub: PR #22647's diff,
`TauCeti/CategoryTheory/Sites/SheafCohomology/Pullback.lean`:

```lean
variable (pb : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}) [pb.Additive]
  [PreservesFiniteLimits pb] [PreservesFiniteColimits pb]
  (c : (constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ)) ⟶
    pb.obj ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))))
def pullback (G : Sheaf J AddCommGrpCat.{w}) (n : ℕ) : H G n →+ H (pb.obj G) n
lemma pullback_naturality {G₁ G₂ : Sheaf J AddCommGrpCat.{w}} (f : G₁ ⟶ G₂) {n : ℕ}
    (x : H G₁ n) :
    pullback pb c G₂ n (H.map f n x) = H.map (pb.map f) n (pullback pb c G₁ n x)
```

Stub as stated: identical binders and conclusions, in namespace `CategoryTheory.Sheaf.H` as in the
PR; `pullback` has body `sorry` and `pullback_naturality` is its stated API. Differences: (1) versus
the README, the PR (and the stub) takes the extra comparison map `c : ℤ_K ⟶ pb ℤ_J`, and `pb` is
an arbitrary exact additive functor rather than `u.sheafPullback`; the stub follows the PR because
that is what will land. (2) In the stub `c` is written as an explicit binder of `pullback` itself
rather than a section variable, because a `sorry` body does not mention `c` and Lean would
otherwise drop it from the signature; the resulting argument order `pullback pb c G n` matches the
PR.

### `qcoh-higher-direct-image-vanishing` — `TauCeti.QCoh.higherDirectImage_vanishing`

`Suggested.lean` (verbatim):

```lean
theorem higherDirectImage_vanishing {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] [IsAffine S] :
    ∃ N : ℕ, ∀ (F : X.Modules) [F.IsQuasicoherent] (p : ℕ), N ≤ p →
      Subsingleton (Scheme.Modules.Cohomology F p) := by
  sorry
```

Stub as stated (from PR #22975's diff, `TauCeti/AlgebraicGeometry/Cohomology/QuasiSeparated.lean`):
the same statement, in namespace `TauCeti.QCoh`, with `Cohomology` resolved to main's
`TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology` (opened as in the PR). No mathematical
difference; the only difference is the namespace prefix (`TauCetiRoadmap.SchemeAndStackFoundations`
becomes `TauCeti`) and that `Scheme.Modules.Cohomology` is main's Tau Ceti abbreviation.

## Split plan

1. **feat: degree zero of local cohomology is the power torsion** — after: none.
   `TauCeti/Algebra/Homology/LocalCohomology/DegreeZero.lean` (174 lines, done): the
   declarations listed under "What is proved". Uses no supplier.
2. **feat: cohomology with supports in the whole space is ordinary cohomology** — after: none.
   `TauCeti/Topology/Sheaves/SupportedCohomology/Univ.lean` (done):
   `isZero_freeYonedaSheafFunctor_obj_bot`, `isIso_cokernel_π_complInclusion_top`,
   `supportedHTopEquiv`, `supportedHTopEquiv_apply`, `toH'_complInclusion_top_bijective`.
   Uses no supplier.
3. **feat: pullback of cohomology with supports** — after: none (not yet written; needs
   `sheaf-h-pullback` landed). `cohomologyWithSupport_pullback` via `Sheaf.H.pullback`.
4. **feat: Noetherian local cohomology computes derived power torsion** — after: 1 (not yet
   written). `localCohomology_colimit_ext_comparison`.
5. **feat: flat base change of Noetherian local cohomology** — after: 4 (not yet written).
   `Supports.localCohomology_flat_baseChange`, flat excision.
6. **feat: geometric comparison and depth vanishing for local cohomology** — after: 1–5 (not yet
   written). `localCohomology_module_comparison` (needs `qcoh-higher-direct-image-vanishing`
   landed), `depth_localCohomology_vanishing`, `depth_localCohomology_nonvanishing`, the scheme
   wrappers and the §2.7 checks; the only split that completes the target.
