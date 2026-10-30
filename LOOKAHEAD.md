<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"cohomology-with-support","main":"ab1c5af023f864980704684df6008c9288ab4fcf","status":"partial","suppliers":["sheaf-h-pullback","qcoh-higher-direct-image-vanishing"],"splits":[{"n":1,"after":[],"title":"feat: degree zero of local cohomology is the power torsion"},{"n":2,"after":[],"title":"feat: sections with support and the supported subsheaf"},{"n":3,"after":[2],"title":"feat: cohomology with supports and local cohomology sheaves"},{"n":4,"after":[3],"title":"feat: localization triangle and excision for cohomology with supports"},{"n":5,"after":[1],"title":"feat: Noetherian local cohomology computes derived power torsion"},{"n":6,"after":[5],"title":"feat: flat base change of Noetherian local cohomology"},{"n":7,"after":[1,2,3,4,5,6],"title":"feat: geometric comparison and depth vanishing for local cohomology"}]}-->

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

## What remains

Everything else in README §2.7: `sectionsWithSupport Z hZ F`, `supportedSubsheaf Z F`,
`cohomologyWithSupport Z F q := R^q Γ_Z(X, −)`, `localCohomologySheaf Z F q := R^q H_Z(F)` and the
API `cohomologyWithSupport_zero`, `cohomologyWithSupport_univ` (with `test_support_all`,
`test_support_empty`), `rHZ_adjunction`, `localToGlobal`, `cohomologyWithSupport_pullback`
(consumes `Sheaf.H.pullback`); `supports_localization_triangle` and excision;
`localCohomology_colimit_ext_comparison`; `localCohomology_module_comparison` (uses
`QCoh.higherDirectImage_vanishing` for the affine/qcqs vanishing on `Spec A`); the pinned
`Supports.localCohomology_flat_baseChange`; `depth_localCohomology_vanishing`,
`depth_localCohomology_nonvanishing`; and the checks `test_support_affine_line_origin`,
`test_support_not_restriction`, `test_depth_dvr`, `localCohomology_module_comparison_nil_ideal`,
`localCohomology_module_comparison_dvr`, `depth_localCohomology_zero_guard`. None of the proved
part consumes a stub yet; the stubs record the supplier forms these remaining pieces will use.

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
   File `TauCeti/Algebra/Homology/LocalCohomology/DegreeZero.lean` (on this branch, 174 lines):
   `preservesFiniteLimits_linearYoneda_obj`, `extZeroIso`, `quotient_linearMap_eq_zero`,
   `smul_apply_mk_one_eq_zero`, `evalOne`, `evalOne_apply`, `homDiagram`,
   `localCohomologyZeroIso`, `evalOneCocone`, `localCohomologyZeroToModule`,
   `desc_evalOneCocone_ι_apply`, `desc_evalOneCocone_injective`, `range_desc_evalOneCocone`,
   `localCohomologyZeroToModule_injective`, `range_localCohomologyZeroToModule`,
   `localCohomology_degreeZero`. Uses no supplier.
2. **feat: sections with support and the supported subsheaf** — after: none (not yet written).
   `TauCeti/AlgebraicGeometry/Cohomology/Support/Basic.lean`: `sectionsWithSupport`,
   `supportedSubsheaf`, functoriality, the `Z = X` / `Z = ∅` cases.
3. **feat: cohomology with supports and local cohomology sheaves** — after: 2 (not yet written).
   `.../Support/Cohomology.lean`: `cohomologyWithSupport`, `localCohomologySheaf`,
   `cohomologyWithSupport_zero`, `cohomologyWithSupport_univ`, `test_support_all`,
   `test_support_empty`, `cohomologyWithSupport_pullback` (needs `sheaf-h-pullback` landed).
4. **feat: localization triangle and excision for cohomology with supports** — after: 3
   (not yet written). `supports_localization_triangle`, excision, `rHZ_adjunction`, `localToGlobal`.
5. **feat: Noetherian local cohomology computes derived power torsion** — after: 1 (not yet
   written). `localCohomology_colimit_ext_comparison`.
6. **feat: flat base change of Noetherian local cohomology** — after: 5 (not yet written).
   `Supports.localCohomology_flat_baseChange`, flat excision.
7. **feat: geometric comparison and depth vanishing for local cohomology** — after: 1–6 (not yet
   written). `localCohomology_module_comparison` (needs `qcoh-higher-direct-image-vanishing`
   landed), `depth_localCohomology_vanishing`, `depth_localCohomology_nonvanishing`, and the §2.7
   checks; this is the only split that completes the target.
