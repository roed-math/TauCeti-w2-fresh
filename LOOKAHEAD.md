<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"cohomology-with-support","main":"d2083f0f1dd2136d02467ba36efbbe1af612e89c","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: degree zero of local cohomology is power torsion"},{"n":2,"after":[],"title":"feat: scheme cohomology with supports and its full-support comparison"},{"n":3,"after":[2],"title":"feat: pullback of cohomology with supports"},{"n":4,"after":[1],"title":"feat: local cohomology detects depth"},{"n":5,"after":[4],"title":"feat: compare projective-resolution and derived-category Ext"},{"n":6,"after":[5],"title":"feat: degree-one local cohomology along a nonzerodivisor"},{"n":7,"after":[1,5],"title":"feat: the long exact sequence of native local cohomology"},{"n":8,"after":[7],"title":"feat: native local cohomology computes derived power torsion"},{"n":9,"after":[],"title":"feat: flat base change of Ext over a Noetherian ring"},{"n":10,"after":[7,9],"title":"feat: flat base change and excision for native local cohomology"},{"n":11,"after":[2],"title":"feat: affine cohomology with supports and the affine-line origin"},{"n":12,"after":[1,6,11],"title":"feat: local cohomology of a DVR and a non-Noetherian nil ideal"},{"n":13,"after":[2],"title":"feat: supported cohomology of the sheaf associated to a module"},{"n":14,"after":[7,8,13],"title":"feat: the comparison map from native to geometric local cohomology"},{"n":15,"after":[14],"title":"feat: native and geometric local cohomology agree over Noetherian rings"},{"n":16,"after":[2],"title":"feat: local cohomology sheaves of modules on a scheme"},{"n":17,"after":[16],"title":"feat: the derived supported-section adjunction for a closed subspace"},{"n":18,"after":[17],"title":"feat: the derived localization triangle and excision for supports"},{"n":19,"after":[3,10,15],"title":"feat: flat base change respects the geometric local-cohomology comparison"},{"n":20,"after":[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],"title":"feat: the local-to-global spectral sequence for cohomology with supports"}]}-->

# Lookahead: `cohomology-with-support` (SchemeAndStackFoundations §2.7)

Built on `main` at `d2083f0f1dd2136d02467ba36efbbe1af612e89c` (session 21).
Status: **partial**. Session 21 resumed `51a22c18210d`, merged `origin/main`, and
constructed the supported subsheaf and its right derived local cohomology sheaves
as genuine `𝒪_X`-modules. The current port plan has 20 splits; the sheaf construction belongs to split 16.
The historical session notes below retain the previous plan's numbering. Use the
current split plan, rather than those historical numbers, when preparing branches.

The object-level and degree-zero sheaf constructions are proved. The derived
adjunction, local-to-global spectral sequence, derived localization triangle and
compatibility of flat base change with the geometric comparison are still outstanding.
The new sheaves are on `X`, supported in `Z`; transport to the ringed closed subspace
`(Z, i⁻¹𝒪_X)` remains part of the derived adjunction work. They are not modules over
an arbitrarily chosen closed subscheme structure on `Z`.

## Suppliers: no stubbed declaration is consumed

Session 3 deleted `TauCeti/Lookahead/CohomologyWithSupport/Stubs.lean`. Nothing on the branch had
imported it, and `main` now carries every declaration it stubbed. This does not claim that
the entire supplier list items have landed:

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
  earlier stub `TauCeti.QCoh.higherDirectImage_vanishing` therefore had to go. Any split that needs it should
  use the landed name. PRs #27295 and #30322 are now closed without merging; the current source API,
  rather than those PRs, supplies the results used here.

The current open supplier PR #33170 was read with `gh pr diff 33170 --repo
TauCetiProject/TauCeti` (head `f84bdab7db39b98cda939113a43ecd2f3b070a6b`). Its diff
adds `Scheme.Hom.higherDirectImagePresheaf`, `higherDirectImagePresheafZeroIso`,
`higherDirectImagePresheafSheafificationIso`, and
`higherDirectImagePresheafToPresheafIso`, and refactors the existing higher-direct-image
sheafification comparison. It does not change or replace the pinned finite-bound
statement quoted above. This branch consumes none of those new declarations, so
there is no permitted or necessary stub to add. `suppliers` is therefore empty and
`Stubs.lean` remains deleted. No stub signatures or differences remain to report.

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

### `TauCeti/Topology/Sheaves/SupportedCohomology/Univ.lean` (94 lines, sessions 2 and 7)

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

### Session 4: degree-zero examples and the scheme wrapper

`TauCeti/Algebra/Homology/LocalCohomology/DegreeZero.lean` gains 25 lines (now 199):

- `isZero_localCohomology_zero_iff`: `IsZero ((localCohomology I 0).obj M)` iff every element of
  `M` killed by a power of `I` is zero;
- `isZero_localCohomology_zero_of_isSMulRegular`: `H⁰_I(M) = 0` once every `Iⁿ` contains an
  `M`-regular element.

`TauCeti/Examples/Algebra/Homology/LocalCohomology.lean` (170 lines, new), in namespace
`TauCeti.Supports`:

- `isZero_localCohomology_zero_self_of_ne_bot`: `H⁰_I(A) = 0` for a domain `A` and `I ≠ ⊥`;
  `isZero_localCohomology_zero_maximalIdeal`: `H⁰_m(R) = 0` for a DVR (the `H⁰` halves of
  `test_depth_dvr` and `localCohomology_module_comparison_dvr`);
- `NilIdealExample.relations k` (the ideal `(x_j^{j+2})` of `k[x₀, x₁, …]`),
  `NilIdealExample.CoordRing k` (the quotient `A`), `NilIdealExample.ideal k` (`I = (x₀, x₁, …)`),
  over any commutative ring `k` (nontrivial where needed);
- `mem_relations_iff` (monomial-ideal membership), `exists_X_pow_mul_notMem_relations`,
  `one_notMem_relations`, the `Nontrivial (CoordRing k)` instance,
  `exists_mem_pow_mul_ne_zero` (the README's fresh-variable argument: every nonzero class has a
  nonzero product with an element of `Iⁿ`), `ideal_le_nilradical`;
- `zeroLocus_ideal`: `V(I) = Spec A`; `not_isNoetherianRing`: `A` is not Noetherian (its
  nilradical is not nilpotent); `isZero_localCohomology_zero`: native `H⁰_I(A) = 0`.

  These are the native half of `localCohomology_module_comparison_nil_ideal`. The geometric half
  (`H⁰_{V(I)}(Spec A, 𝒪) = A ≠ 0`) follows from `V(I) = Spec A`, `sectionsWithSupport_top` and
  `cohomologyWithSupportZeroLinearEquiv` below, and goes in split 14.

`TauCeti/AlgebraicGeometry/Cohomology/Support.lean` (223 lines, new), in namespace
`TauCeti.AlgebraicGeometry.Scheme.Modules` (beside `Scheme.Modules.Cohomology`). This is the
README's `cohomologyWithSupport Z F q` with its `O(X)`-module structure, and
`sectionsWithSupport`, for a closed `Z : Closeds X` (main's `Closeds` convention rather than a
`Set` plus `IsClosed` proof):

- `cohomologyWithSupport Z M q` (abbrev for `supportedH Z ⊤ q` of the underlying abelian sheaf);
- `cohomologyWithSupportMap` with `_apply`, `_id`, `_comp`, `_zero`, `_add`;
- `cohomologyWithSupportAction`, instance `cohomologyWithSupportModule` (a `Γ(X, ⊤)`-module, via
  the scalar endomorphisms `globalSectionsSmul`, as `cohomologyModule` does for `Cohomology`),
  `smul_cohomologyWithSupport`;
- `cohomologyWithSupportMapLinear` with `_apply`;
- `sectionsWithSupport Z M : Submodule Γ(X, ⊤) Γ(M, ⊤)`, `mem_sectionsWithSupport_iff`,
  `sectionsWithSupport_top` (`@[simp]`: every global section is supported in `X`);
- `cohomologyWithSupportZeroLinearEquiv : H_Z⁰(X, M) ≃ₗ[Γ(X, ⊤)] Γ_Z(X, M)` with
  `coe_cohomologyWithSupportZeroLinearEquiv_apply` (README `cohomologyWithSupport_zero`);
- `cohomologyWithSupportTopEquiv : H_X^q(X, M) ≃+ H^q(X, M)` and instance
  `subsingleton_cohomologyWithSupport_bot` (README `cohomologyWithSupport_univ`; at `q = 1` these
  give `test_support_all` and `test_support_empty`).

`TauCeti/AlgebraicGeometry/Modules/GlobalSections.lean` gains (+11 lines)
`AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_app_top_apply`:
`(M.globalSectionsSmul r).app ⊤ s = r • s`, the general fact the submodule and the degree-zero
linearity need. It sits beside `globalSectionsSmul_naturality`. `Support.lean` takes about 150–200 s
to compile, comparable to `Cohomology/Module/Basic.lean` (120 s).

### Session 5: degree one on affine schemes and the affine line at the origin

`TauCeti/CategoryTheory/Sites/SheafCohomology/Relative.lean` (a `main` file) gains 18 lines:

- `CategoryTheory.Sheaf.relativeH'.oneAddEquivOfSubsingleton`: if `H¹(V, F) = 0`, the
  connecting map gives `H⁰(U, F) ⧸ range(H⁰(V, F) ⟶ H⁰(U, F)) ≃+ H¹(V, U; F)`; with
  `oneAddEquivOfSubsingleton_mk` (`@[simp]`).

`TauCeti/Topology/Sheaves/SupportedCohomology.lean` (a `main` file) gains 28 lines:

- `CategoryTheory.Sheaf.supportedHOneEquiv S W hW`: if `H¹(W, F) = 0`, then
  `F(W ∖ S) ⧸ range(F(W) ⟶ F(W ∖ S)) ≃+ H_S¹(W, F)`, through
  `TauCeti.CategoryTheory.cohomologyZeroSectionsEquiv`; with `supportedHOneEquiv_mk`.

`TauCeti/AlgebraicGeometry/Cohomology/Support/Affine.lean` (157 lines, new), in namespace
`TauCeti.AlgebraicGeometry.Scheme.Modules`, using `main`'s Serre vanishing
`AlgebraicGeometry.Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen`:

- `cohomologyWithSupportOneEquiv Z M` (`[IsAffine X]`, `[M.IsQuasicoherent]`):
  `M(X ∖ Z) ⧸ M(X) ≃+ H_Z^1(X, M)`, and `cohomologyWithSupportOneEquiv_mk`;
- `subsingleton_cohomologyWithSupport_add_two`: `H_Z^{n+2}(X, M) = 0` when `X` and `X ∖ Z` are
  affine, and `subsingleton_cohomologyWithSupport_basicOpen_add_two` for `Z = V(r)`;
- for the structure sheaf `SheafOfModules.unit X.ringCatSheaf` and `r : Γ(X, ⊤)`:
  `cohomologyWithSupportBasicOpenOneEquiv r :
  Γ(X, D(r)) ⧸ (algebraMap Γ(X, ⊤) Γ(X, D(r))).range ≃+ H_{V(r)}^1(X, 𝒪)` (that is,
  `Γ(X, ⊤)_r / Γ(X, ⊤)`, by Mathlib's `isLocalization_away_of_isAffine`) and
  `subsingleton_cohomologyWithSupport_basicOpen_zero` (`H_{V(r)}^0(X, 𝒪) = 0` for a
  nonzerodivisor `r`); private helpers `top_inf_compl_compl_basicOpen`,
  `basicOpenSectionsAddEquiv`, `basicOpenSectionsAddEquiv_algebraMap`.

`TauCeti/Examples/AlgebraicGeometry/Cohomology/Support.lean` (116 lines, new), in namespace
`TauCeti.AlgebraicGeometry.Scheme.Modules.AffineLineExample`: the README check
`test_support_affine_line_origin` for a field `k`, `X = Spec k[t]` and `Z = V(t)`:

- `coordinate k` (`t` as a global function), `coordinate_mem_nonZeroDivisors`;
- `subsingleton_cohomologyWithSupport_origin_zero`: `H⁰_Z(X, 𝒪) = 0`;
- `cohomologyWithSupportOriginOneEquiv`: `H¹_Z(X, 𝒪) ≃+ k[T;T⁻¹] ⧸ toLaurent.range`
  (`k[t, t⁻¹]/k[t]`, via `IsLocalization.ringEquivOfRingEquiv` and Mathlib's
  `LaurentPolynomial.isLocalization`);
- `subsingleton_cohomologyWithSupport_origin_add_two`: `H^{n+2}_Z(X, 𝒪) = 0`.

The README states the affine-line check with `Z = {0}`; the branch uses `Z = V(t)`, which is that
point. The `H⁰_Z = 0` half of `test_support_not_restriction` is
`subsingleton_cohomologyWithSupport_origin_zero`; session 7 adds the other half.

### Session 6: pullback of cohomology with supports (`cohomologyWithSupport_pullback`)

`Suggested.lean` does not pin `cohomologyWithSupport_pullback`; it is stated from the README's API
list, in the same shape as `main`'s `Sheaf.H.pullback`, `TopCat.Hom.cohomologyPullback` and
`Scheme.Hom.cohomologyPullback`.

`TauCeti/CategoryTheory/Sites/SheafCohomology/Relative/Pullback.lean` (new), for a continuous
functor `u : C ⥤ D` whose pushforward has a left adjoint `u^* = u.sheafPullback`:

- `TauCeti.CategoryTheory.freeYonedaSheafPullbackComparison u U : ℤ_{u U} ⟶ u^* ℤ_U` (the section
  of `u^* ℤ_U` over `u U` given by the unit), with
  `freeYonedaSheafSectionsEquiv_pullbackComparison`,
  `freeYonedaSheafSectionsEquiv_pullbackComparison_comp` (precomposition is the adjunct) and
  `freeYonedaSheafPullbackComparison_naturality` (natural in `U`);
- `relativeFreeYonedaSheafPullbackComparison u i : ℤ_{u V, u U} ⟶ u^* ℤ_{V, U}`, with
  `cokernel_π_relativeFreeYonedaSheafPullbackComparison` and
  `coe_relativeFreeYonedaSheafHomEquiv_pullbackComparison_comp`;
- for `u^*` left exact: `CategoryTheory.Sheaf.relativeH'.pullback u F i n :
  Hⁿ(V, U; F) →+ Hⁿ(u V, u U; u^* F)`, `pullback_apply`, `pullback_naturality` and
  `coe_zeroEquiv_pullback` (degree zero is the unit `F ⟶ u_* u^* F` on sections vanishing along
  `i`).

`TauCeti/Topology/Sheaves/SupportedCohomology/Pullback.lean` (new), for a continuous map
`f : X ⟶ Y`:

- `TopCat.Hom.supportedHPullback f F S W n : H_Sⁿ(W, F) →+ H_{f⁻¹ S}ⁿ(f⁻¹ W, f⁻¹ F)`;
- `supportedHPullback_naturality`, `coe_supportedHZeroEquiv_supportedHPullback`.

`TauCeti/AlgebraicGeometry/Cohomology/Support/Pullback.lean` (new), for a morphism of schemes
`g : Y ⟶ X`:

- `AlgebraicGeometry.Scheme.Hom.cohomologyWithSupportPullback g Z M q :
  H_Z^q(X, M) →+ H_{g⁻¹ Z}^q(Y, g^* M)` (the README's `cohomologyWithSupport_pullback`);
- `cohomologyWithSupportPullback_cohomologyWithSupportMap` (naturality),
  `cohomologyWithSupportPullback_smul` (semilinear along `g^♯`) and
  `coe_cohomologyWithSupportZeroLinearEquiv_cohomologyWithSupportPullback` (degree zero is
  `Scheme.Hom.pullbackSections`).

### Session 7: linearity of `cohomologyWithSupport_univ` and `test_support_not_restriction`

`TauCeti/CategoryTheory/Sites/SheafCohomology/FreeYoneda.lean` (a `main` file) gains 10 lines:

- `CategoryTheory.Sheaf.H'AddEquivExt_cohomologyPresheafFunctor_map_app`: the coefficient maps of
  Mathlib's cohomology presheaf are `Ext` postcomposition, transported along `H'AddEquivExt`.
  It is `rfl`, but only inside this module, because `H'AddEquivExt` and
  `freeYonedaSheafFunctor` are not exposed. (`SectionsQuotient.lean` notes that Mathlib has no
  such lemma.)

`TauCeti/Topology/Sheaves/SupportedCohomology/Univ.lean` gains
`TauCeti.CategoryTheory.supportedHTopEquiv_naturality`: `H_Xⁿ(W, F) ≃+ Hⁿ(W, F)` is natural in
`F`.

`TauCeti/AlgebraicGeometry/Cohomology/Support.lean` gains:

- `cohomologyWithSupportTopEquiv_naturality`, natural in the coefficient module;
- `cohomologyWithSupportTopLinearEquiv : H_X^q(X, M) ≃ₗ[Γ(X, ⊤)] H^q(X, M)`, with `_apply`.
  This is `cohomologyWithSupport_univ` for the `O(X)`-module structure the README asks for.

`TauCeti/Examples/AlgebraicGeometry/Cohomology/Support.lean` gains the rest of
`test_support_not_restriction`:

- `origin k : Spec k ⟶ Spec k[t]` (evaluation at `0`), an `IsClosedImmersion` instance, and
  `range_origin`: its image is `V(t)`, the `Z` used throughout the file;
- `isEmpty_cohomologyWithSupport_origin_zero_equiv`: `H⁰_Z(𝔸¹, 𝒪)` is not in bijection with
  `Γ(Spec k, ⊤)`. The closed subscheme `Z` has the nonzero ring of functions `k`, while
  `H⁰_Z = 0`.

### Session 8: the geometric side of the DVR and nil-ideal checks

`TauCeti/AlgebraicGeometry/Cohomology/Support/Affine.lean` gains (+27 lines, now 184)
`Scheme.Modules.cohomologyWithSupportSpecOneEquiv a L`: for `a : A` and any localization `L` of
`A` away from `a`, `H_{V(a)}^1(Spec A, 𝒪) ≃+ L ⧸ (algebraMap A L).range`. It composes
`cohomologyWithSupportBasicOpenOneEquiv` with `IsLocalization.ringEquivOfRingEquiv`. The affine-line
example now uses it (`cohomologyWithSupportOriginOneEquiv` is `cohomologyWithSupportSpecOneEquiv X
k[T;T⁻¹]`), which removes that file's private `basicOpenRingEquiv` and
`basicOpenRingEquiv_algebraMap` (the file shrinks from 151 to 127 lines).

The same file gains the `Γ(X, ⊤)`-linearity of degree one (+67 lines; the file is now 251 lines):

- `Scheme.Modules.cohomologyWithSupportOneEquiv_globalSectionsSmul`: for any quasi-coherent `M`,
  the class in `H_Z^1(X, M)` of `r · s` (`s` a section over `X ∖ Z`, acted on by the scalar
  endomorphism `globalSectionsSmul r`) is `r •` the class of `s`. The proof is the naturality of
  the connecting map in the coefficients: `relativeH'.δ_apply`,
  `H'AddEquivExt_cohomologyPresheafFunctor_map_app`, `cohomologyZeroSectionsEquiv_naturality_right`
  and `Ext.comp_assoc_of_third_deg_zero`. It is stated in `Affine.lean` rather than as a
  `supportedHOneEquiv` naturality lemma in `SupportedCohomology.lean`, to avoid recompiling that
  slow `main` file; the port may move it there.
- `Scheme.Modules.cohomologyWithSupportBasicOpenOneLinearEquiv r`:
  `Γ(X, D(r)) ⧸ LinearMap.range (Algebra.linearMap Γ(X, ⊤) Γ(X, D(r))) ≃ₗ[Γ(X, ⊤)]
  H_{V(r)}^1(X, 𝒪)`, the `O(X)`-linear form of `cohomologyWithSupportBasicOpenOneEquiv`, through
  the private `basicOpenSectionsAddEquiv_algebraMap_mul`. Its type is stated with
  `let 𝒪 : X.Modules := SheafOfModules.unit X.ringCatSheaf`, the pattern of `main`'s
  `trivialCohomologyBaseLinearEquiv`: written with `SheafOfModules.unit` directly, the
  `Γ(X, ⊤)`-module instance on `cohomologyWithSupport _ (SheafOfModules.unit _) 1` is not found.

`TauCeti/Algebra/Homology/LocalCohomology/Depth.lean` gains (+9 lines, now 217)
`TauCeti.Supports.isZero_localCohomology_succ_of_injective`: native `H^{q+1}_I(J) = 0` for an
injective module `J` (every `Ext^{q+1}(A/Iⁿ, J)` vanishes, via `Abelian.Ext.eq_zero_of_injective`
and `isZero_localCohomology_of_subsingleton_ext`). This is the effaceability that the comparison
of split 15 needs on the native side.

`TauCeti/Examples/AlgebraicGeometry/Cohomology/Support/Comparison.lean` (new), in namespace
`TauCeti.Supports`:

- `DiscreteValuationRingExample.uniformizerLocus ϖ` (the closed set `V(ϖ) ⊆ Spec R`, the
  complement of `D(ϖ)`), `coe_uniformizerLocus` (for a uniformizer it is `V(m)`, the closed point,
  so this is the README's `Z = V(m)`), `subsingleton_cohomologyWithSupport_zero` (for a domain and
  `ϖ ≠ 0`: `H⁰_{V(ϖ)}(Spec R, 𝒪) = 0`), `cohomologyWithSupportOneEquiv K hϖ :
  H¹_{V(ϖ)}(Spec R, 𝒪) ≃+ K ⧸ (algebraMap R K).range` (through `main`'s
  `TauCeti.isLocalizationAway_fractionRing`: `K` is `R` localized away from `ϖ`) and
  `subsingleton_cohomologyWithSupport_add_two`. These are the geometric halves of
  `test_depth_dvr`/`localCohomology_module_comparison_dvr`; once split 15 proves the comparison,
  they give the native `H¹_m(R) ≅ K/R` as well.
- `NilIdealExample.idealZeroLocus k` (`V(I)` as a closed subset of `Spec A`),
  `idealZeroLocus_eq_top`, `cohomologyWithSupportZeroEquiv : H⁰_{V(I)}(Spec A, 𝒪) ≃+ A`, the
  `Nontrivial` instance, and the README check **`localCohomology_module_comparison_nil_ideal`**
  (complete: `V(I) = Spec A`, geometric `H⁰` nontrivial, native `H⁰_I(A) = 0`, `A` not
  Noetherian).

`TauCeti/AlgebraicGeometry/Cohomology/Support.lean` gains (+18 lines, now 274)
`Scheme.Modules.cohomologyWithSupportZeroLinearEquivOfEqTop hZ M :
H_Z^0(X, M) ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤)` for `hZ : Z = ⊤`, with `_apply` (`@[simp]`), which the nil-ideal
example uses for `V(I) = Spec A`.

Pitfall: on `X = Spec (CommRingCat.of A)` the `Γ(X, ⊤)`-module instances on
`cohomologyWithSupport Z (SheafOfModules.unit _) 0` and `Γ(unit, ⊤)` are not found (the unit sheaf
is a `SheafOfModules`, not syntactically an `X.Modules`); bind the unit sheaf as
`let 𝒪 : X.Modules := SheafOfModules.unit _` first (as `cohomologyWithSupportZeroEquiv` does). The unit sheaf's
`IsQuasicoherent` instance needs `import TauCeti.AlgebraicGeometry.Modules.TensorProduct`.

### Session 9: the two `Ext`s compared, and native `H¹` along a nonzerodivisor

`TauCeti/Algebra/Homology/Ext/Comparison.lean` (new, 322 lines, split 5), in namespace `TauCeti`.
For a projective resolution `P` of `X`, Mathlib's derived-functor `Ext k C (p + 1)` (computed by
`ProjectiveResolution.isoExt`) and its derived-category `Abelian.Ext X Y (p + 1)` (computed by
`ProjectiveResolution.extMk`) are now identified `k`-linearly, naturally in **both** arguments.
This replaces the vanishing/injectivity-only bridges of split 4 as the tool for transporting
derived-category computations (including the derived-category long exact sequences in either
argument) to `localCohomology`:

- `HomologicalComplex.homologyMap_comp_homologyIsoSc'_hom` (naturality of `homologyIsoSc'`) and
  `ShortComplex.moduleCatHomologyIso_hom_homologyMap_inv_mk` (the map on `ker g ⧸ im f` sends the
  class of `z` to the class of `φ.τ₂ z`), general helpers;
- `homologyLinearEquivExt k P Y p`: the explicit `ker ⧸ im` cohomology of `Hom(P, Y)` in degree
  `p + 1` is `Abelian.Ext X Y (p + 1)`, `[f] ↦ P.extMk f`; `homologyLinearEquivExt_mk`;
- `extSuccIsoHomology k P Y p` (derived-functor `Ext` as that quotient), `extSuccClass k P Y p f hf`
  (the class of a cocycle), `extSuccClass_surjective`;
- **`extSuccLinearEquiv k P Y p`**: `((Ext k C (p+1)).obj (op X)).obj Y ≃ₗ[k] Abelian.Ext X Y (p+1)`,
  with `extSuccLinearEquiv_extSuccClass` and `extSuccLinearEquiv_symm_extMk`;
- `map_extSuccClass_of_comp_isoExt_hom`: a map of derived-functor `Ext` groups that `isoExt` turns
  into the map induced by a chain map `ψ` of `Hom`-complexes sends `[f]` to `[ψ f]`;
- first argument: `Ext_map_extSuccClass` (precomposition with a chain map over `g`) and
  **`extSuccLinearEquiv_Ext_map`** (the map induced by `g` is `(Ext.mk₀ g).comp`);
- second argument: `Ext_obj_map_comp_isoExt_hom` (`isoExt` is natural in `Y`, through Mathlib's
  `ProjectiveResolution.leftDerived_app_eq`), `Ext_obj_map_extSuccClass` (postcomposition) and
  **`extSuccLinearEquiv_Ext_obj_map`** (the map induced by `f` is `·.comp (Ext.mk₀ f)`).

`TauCeti/Algebra/Homology/LocalCohomology/Principal.lean` (new, 311 lines, split 6), in
namespace `TauCeti.Supports`. For a nonzerodivisor `a` of a commutative ring `A` and `L` the
localization away from `a`:

- `powShortComplex a n` (`A →(aⁿ) A → A ⧸ (a)ⁿ`), `mem_span_singleton_pow_iff`,
  `shortExact_powShortComplex`, `powExtClass ha n` (its class `eₙ ∈ Ext¹(A ⧸ (a)ⁿ, A)`),
  `comp_mk₀_lsmul` (through Mathlib's `ModuleCat.lsmul_eq_smul_id`);
- `exists_eq_smul_powExtClass` (every element is `r • eₙ`, from `contravariant_sequence_exact₃`
  and `Ext¹(A, A) = 0`), `smul_powExtClass_eq_zero_iff` (`r • eₙ = 0 ↔ r ∈ (a)ⁿ`, from
  `contravariant_sequence_exact₁` and `extClass_comp`), `mk₀_mapQ_comp_powExtClass` (transition
  maps send `eₙ` to `aᵐ⁻ⁿ • eₘ`, from `extClass_naturality`),
  `toSpanSingleton_powExtClass_surjective`, `derivedExtOneLinearEquiv ha n :
  A ⧸ (a)ⁿ ≃ₗ[A] Ext¹(A ⧸ (a)ⁿ, A)` with `_mk`;
- `invPowClass a L n` (`1 / aⁿ` in `L ⧸ A`), `smul_invPowClass`, `smul_invPowClass_eq_zero_iff`,
  `pow_sub_smul_invPowClass`, `extOneToQuotient ha L n` (the derived-functor
  `Ext¹(A ⧸ (a)ⁿ, A) → L ⧸ A`, `r • eₙ ↦ r / aⁿ`, through `extSuccLinearEquiv`),
  `extOneToQuotient_apply`, `extOneToQuotient_Ext_map` (compatibility with the system);
- **`localCohomologyOneLinearEquiv ha L : (localCohomology (Ideal.span {a}) 1).obj A ≃ₗ[A]
  L ⧸ LinearMap.range (Algebra.linearMap A L)`**: the native counterpart of
  `cohomologyWithSupportSpecOneEquiv` (`H¹_{V(a)}(Spec A, 𝒪) ≃+ L ⧸ A`). The colimit is computed
  with `Concrete.colimit_exists_rep`; injectivity holds stage by stage, since `r / aⁿ ∈ A` forces
  `r ∈ (aⁿ)` for a nonzerodivisor.

`TauCeti/Examples/AlgebraicGeometry/Cohomology/Support/Comparison.lean` (split 14) gains, in
`DiscreteValuationRingExample`:

- `localCohomologyOneMaximalIdealLinearEquiv K hϖ : H¹_m(R) ≃ₗ[R] K ⧸ R` (native; through
  `maximalIdeal R = (ϖ)` and main's `isLocalizationAway_fractionRing`);
- `localCohomologyOneAddEquivCohomologyWithSupport K hϖ`: native `H¹_m(R)` ≃+ geometric
  `H¹_{V(ϖ)}(Spec R, 𝒪)` (both are `K ⧸ R`);
- `isZero_localCohomology_zero_and_nonempty_one_linearEquiv`: `H⁰_m(R) = 0` and
  `H¹_m(R) ≅ K ⧸ R`, natively. This is the content of the README check `test_depth_dvr`, now
  complete; split 15 collects it under the check's name.

### Session 10: the long exact sequence of native local cohomology

Merged `main` at `52f9d081237d` (one docstring conflict in `ProjectiveResolution.lean`, where
`main` had added `hasProjectiveDimensionLT`; both texts are kept).

`TauCeti/CategoryTheory/Abelian/LeftDerived.lean` (a `main` file) gains 25 lines:
`CategoryTheory.NatTrans.leftDerived_zero_comp_fromLeftDerivedZero` (`@[reassoc]`): the
comparison `L₀F ⟶ F` is natural in the functor `F`. Mathlib has its naturality in the object
only.

`TauCeti/Algebra/Homology/LocalCohomology/DegreeZero.lean` gains 31 lines (now 230):
`extZeroIso_inv_app` (the inverse of `extZeroIso` is `fromLeftDerivedZero`; it must live here,
since `extZeroIso` is not exposed) and `extZeroIso_hom_naturality_right` (`Ext⁰(N, M) ≅ Hom(N, M)`
is natural in `M` as well as in `N`).

`TauCeti/Algebra/Category/ModuleCat/FilteredColimits.lean` (new, 139 lines), in namespace
`TauCeti.ModuleCat`, for a filtered diagram `D : J ⥤ ModuleCat R ⥤ ModuleCat R`:
`exists_colimit_ι_app_eq` (every element of `(colimit D).obj X` comes from a stage),
`exists_map_app_eq_zero` (zero in the colimit is zero at a later stage), **`exists_eq_of_stages`**
(maps induced stage by stage by natural maps are exact once every stage is),
**`comp_eq_zero_of_stages`** (they compose to zero once every stage does) and
**`injective_of_stages`**. These are generic, so they live beside
`TauCeti/Algebra/Category/ModuleCat/Colimits.lean` rather than in the local-cohomology file.

`TauCeti/Algebra/Homology/LocalCohomology/Exact.lean` (new, 396 lines), in namespace
`TauCeti.Supports`, for a short exact sequence `hS : S.ShortExact` of `A`-modules over any
commutative ring and every degree `n`:

- **`extLinearEquiv N Y n`**: the derived-functor `Extⁿ(N, Y)` is `A`-linearly the
  derived-category `Extⁿ(N, Y)` in **every** degree (degree `0` through `extZeroIso` and
  `Ext.linearEquiv₀`, positive degrees through session 9's `extSuccLinearEquiv`);
  `extLinearEquiv_zero_apply`, `extLinearEquiv_Ext_obj_map` (natural in `Y`) and
  `extLinearEquiv_Ext_map` (natural in `N`);
- stage level, through Mathlib's `Ext.covariant_sequence_exact₁/₂/₃` and
  `Ext.postcomp_mk₀_injective_of_mono`: `Ext_zero_map_f_injective`, `exists_Ext_map_f_eq`,
  `Ext_map_f_comp_map_g`; the connecting map **`extδ N hS n : Extⁿ(N, X₃) ⟶ Extⁿ⁺¹(N, X₁)`**
  (Yoneda product with `hS.extClass`), `extLinearEquiv_extδ`, `extδ_naturality` (natural in
  `N`), `exists_Ext_map_g_eq`, `exists_extδ_eq`, `Ext_map_g_comp_extδ`, `extδ_comp_Ext_map_f`;
- colimit level: `ι_app_localCohomology_map`, `localCohomologyDiagramδ` (the stages as a natural
  transformation along `A ⧸ Iⁿ`), **`localCohomologyδ I hS n : Hⁿ_I(X₃) ⟶ Hⁿ⁺¹_I(X₁)`**,
  `ι_app_localCohomologyδ`;
- exactness: **`localCohomology_zero_map_f_injective`** (`0 → H⁰_I(X₁) → H⁰_I(X₂)`),
  `exists_localCohomology_map_f_eq`, `exists_localCohomology_map_g_eq`,
  `exists_localCohomologyδ_eq` (elementwise), `localCohomology_map_f_comp_map_g`,
  `localCohomology_map_g_comp_localCohomologyδ`, `localCohomologyδ_comp_localCohomology_map_f`,
  and **`localCohomology_sequence_exact₂`, `localCohomology_sequence_exact₃`,
  `localCohomology_sequence_exact₁`** (`ShortComplex.Exact` at `Hⁿ_I(X₂)`, `Hⁿ_I(X₃)` and
  `Hⁿ⁺¹_I(X₁)`, named after Mathlib's `Ext.covariant_sequence_exact₁/₂/₃`).

So the native functors `H^•_I` form a `δ`-functor on `A`-modules, for every commutative ring. With
`isZero_localCohomology_succ_of_injective` (effaceability) and split 1 (`H⁰_I = Γ_I`) this is
everything split 8 needs on the native side.

### Session 11: local cohomology is derived power torsion (any commutative ring)

`TauCeti/Algebra/Homology/LocalCohomology/DerivedTorsion.lean` (new, about 530 lines, split 8), in
namespace `TauCeti.Supports`. It works over **every** commutative ring: the identification of the
native colimit-of-`Ext` functor with derived `I`-power torsion needs no Noetherian hypothesis
(Stacks 0954 computes `colim_k Ext^q(A ⧸ Iᵏ, M)` from an injective resolution of `M` and exactness
of filtered colimits). Noetherianity is needed only for the next step, derived torsion versus
`RΓ_{V(I)}` (Stacks 0955), which is not done yet. Declarations:

- `powerTorsion I M := ⨆ n, Submodule.torsionBySet A M (Iⁿ)`, `mem_powerTorsion_iff`,
  `map_mem_powerTorsion`;
- `powerTorsionFunctor I : ModuleCat A ⥤ ModuleCat A` (`Γ_I`, exposed), `powerTorsionFunctor_obj`,
  `coe_powerTorsionFunctor_map_apply`, its `Additive` instance and a `PreservesFiniteLimits`
  instance (left exactness, through Mathlib's `preservesFiniteLimits_iff_forall_exact_map_and_mono`);
- `localCohomologyZeroLinearEquiv I M : H⁰_I(M) ≃ₗ[A] Γ_I(M)` (from split 1's
  `localCohomologyZeroToModule`) and `coe_localCohomologyZeroLinearEquiv_apply`;
- for an injective resolution `R` of `M` (Mathlib's `InjectiveResolution.extMk` API in
  `Mathlib/CategoryTheory/Abelian/Injective/Ext.lean`): `torsionSc I R p` (the short complex of
  `Γ_I(R)` at `p + 1`), `TorsionHomology I R p` (its `ker ⧸ im`), `torsionCycle f hf` (the cycle
  `f(1)` of a cocycle `f : A ⧸ Iᵏ ⟶ R^{p+1}`), `coe_coe_torsionCycle`,
  `mk_torsionCycle_eq_zero_iff`, `quotientCocycles`, `quotientCocyclesToExt`,
  `quotientCocyclesToHomology`, `quotientCocyclesToExt_surjective`,
  `ker_quotientCocyclesToExt_le`, the stage map `extToTorsionHomology I R p k`
  (`Ext^{p+1}(A ⧸ Iᵏ, M) → H^{p+1}(Γ_I(R))`, `[f] ↦ [f(1)]`), `extToTorsionHomology_extMk`,
  `extToTorsionHomology_comp` (compatibility with the transition maps), the cocone
  `torsionHomologyCocone I R p` with `torsionHomologyCocone_ι_app_apply`;
- **`localCohomologySuccLinearEquivHomology I R p : H^{p+1}_I(M) ≃ₗ[A] TorsionHomology I R p`**
  (surjective since every element of `Γ_I(R^{p+1})` is killed by some `Iᵏ`; injective since a
  coboundary `f(1) = d z` with `Iⁿ z = 0` is a coboundary of `Hom(A ⧸ I^{max k n}, R)`), with
  `localCohomologySuccLinearEquivHomology_ι_extMk`;
- naturality at the level of resolutions: `torsionHomologyMap φ` (the map on `TorsionHomology`
  induced by a morphism `φ : InjectiveResolution.Hom R R' g`), `torsionHomologyMap_mk_torsionCycle`
  (through session 9's `ShortComplex.moduleCatHomologyIso_hom_homologyMap_inv_mk`) and
  **`localCohomologySuccLinearEquivHomology_naturality`** (through Mathlib's
  `InjectiveResolution.extMk_comp_mk₀` and split 7's `extLinearEquiv_Ext_obj_map`,
  `ι_app_localCohomology_map`, `ModuleCat.exists_colimit_ι_app_eq`);
- `torsionHomologyIsoRightDerived I R p : TorsionHomology I R p ≅ R^{p+1}Γ_I(M)` (through
  `moduleCatHomologyIso`, `homologyIsoSc'` and `InjectiveResolution.isoRightDerivedObj`) and
  `torsionHomologyMap_comp_torsionHomologyIsoRightDerived_hom` (through session 9's
  `homologyMap_comp_homologyIsoSc'_hom` and Mathlib's `isoRightDerivedObj_inv_naturality`);
- **`localCohomologySuccLinearEquiv I p M : H^{p+1}_I(M) ≃ₗ[A] R^{p+1}Γ_I(M)`**,
  `localCohomologySuccLinearEquiv_naturality`, and the natural isomorphism
  **`localCohomologySuccIsoRightDerived I p : localCohomology I (p + 1) ≅
  (powerTorsionFunctor I).rightDerived (p + 1)`**;
- degree zero: `localCohomologyZeroToModule_ι_app` (+27 lines in split 1's `DegreeZero.lean`,
  where the unexposed `localCohomologyZeroToModule` can be unfolded: on the image of a stage it
  evaluates the `Hom` at `1`) and `localCohomologyZeroLinearEquiv_naturality`;
- **`localCohomologyIsoRightDerived I q : localCohomology I q ≅
  (powerTorsionFunctor I).rightDerived q`**, the natural isomorphism in every degree (degree zero
  through `localCohomologyZeroLinearEquiv` and `rightDerivedZeroIsoSelf`).

This is the first half of `localCohomology_colimit_ext_comparison`, proved without the
Noetherian hypothesis.

### Session 12: flat base change of `Ext` and of Noetherian local cohomology

The pinned `Supports.localCohomology_flat_baseChange` is now proved, and so is flat excision. It
needs neither split 8 nor the Noetherian hypothesis on `B`.

`TauCeti/Algebra/Category/ModuleCat/Ext/FlatBaseChange.lean` (new, 283 lines, split 9), in
namespace `TauCeti.ModuleCat`. Let `B` be a flat `A`-algebra, with `F = extendScalars (algebraMap A B)`:

- instance `PreservesFiniteLimits F` for `[Module.Flat A B]`, from Mathlib's
  `preservesFiniteLimits_extendScalars_of_flat`; so Mathlib's `Ext.mapExactFunctor F` applies;
- `mapExactFunctor_smul`: `(r • x)_B = algebraMap A B r • x_B`, through `Ext.smul_eq_comp_mk₀`
  and `main`'s `TauCeti.ModuleCat.extendScalars_map_smul_id`;
- `extToRestrictScalars B N M q` (the `A`-linear map `Ext_A^q(N, M) → Ext_B^q(F N, F M)`) and
  **`extBaseChange B N M q : F (Ext_A^q(N, M)) ⟶ Ext_B^q(F N, F M)`** (its adjoint, a morphism of
  `B`-modules), `extBaseChange_one_tmul`;
- `extendScalars_map_precomp_comp_extBaseChange` and its elementwise form
  `extBaseChange_extendScalars_map_precomp`: compatibility with precomposition by an `Ext` class;
- `bijective_extBaseChange_zero` (for finitely presented `N`, via
  `Module.FinitePresentation.isBaseChange_map`, `IsBaseChange.iff_of_equiv_comm` and `main`'s
  `ModuleCat.isIso_extendRestrictScalarsAdj_homEquiv_symm_of_isBaseChange`);
- `bijective_extBaseChange_succ` (for `A` Noetherian: dimension shifting along
  `0 → ker π → A^n → N → 0`, with `Ext.contravariant_sequence_exact₁/₃` on both sides,
  `Ext.mapExactFunctor_extClass` and `Adjunction.map_projective`);
- **`bijective_extBaseChange`**, instance `isIso_extBaseChange`, and
  **`extBaseChangeLinearEquiv B N M q : B ⊗[A] Ext_A^q(N, M) ≃ₗ[B] Ext_B^q(F N, F M)`** with
  `extBaseChangeLinearEquiv_tmul` (`@[simp]`).

`TauCeti/Algebra/Homology/LocalCohomology/FlatBaseChange.lean` (new, 244 lines, split 10), in
namespace `TauCeti.Supports`, for `[IsNoetherianRing A] [Module.Flat A B]`:

- `extendScalarsQuotientIso B J J' h : F (A ⧸ J) ≅ B ⧸ J'` for `h : J.map (algebraMap A B) = J'`
  (through Mathlib's `Algebra.TensorProduct.quotIdealMapEquivTensorQuot` and `main`'s
  `ModuleCat.extendScalarsAlgebraMapIso`), `extendScalarsQuotientIso_hom_one_tmul`, and naturality
  `extendScalars_map_mapQ_comp_extendScalarsQuotientIso`;
- `extQuotientBaseChangeLinearEquiv B J J' h M q : B ⊗[A] Ext_A^q(A ⧸ J, M) ≃ₗ[B]
  Ext_B^q(B ⧸ J', B ⊗[A] M)` for the derived-functor `Ext` of the definition of
  `localCohomology` (through split 7's `extLinearEquiv`, split 9 and `main`'s
  `extLinearEquivOfIso`), `extLinearEquiv_extQuotientBaseChangeLinearEquiv_one_tmul`, and
  naturality `extQuotientBaseChangeLinearEquiv_one_tmul_Ext_map`;
- `localCohomologyDiagramBaseChangeIso B I q M`: the natural isomorphism between `F` applied to
  the diagram `n ↦ Ext_A^q(A ⧸ Iⁿ, M)` and the diagram `n ↦ Ext_B^q(B ⧸ (I B)ⁿ, B ⊗[A] M)`
  (`Ideal.map_pow`);
- **`localCohomologyBaseChangeIso B I q M : B ⊗[A] H^q_I(M) ≅ H^q_{IB}(B ⊗[A] M)`**
  (`colimitObjIsoColimitCompEvaluation`, `preservesColimitIso` of the left adjoint `F`,
  `HasColimit.isoOfNatIso`);
- **`localCohomology_flat_baseChange`** (`Suggested.lean`'s statement, minus the unused
  `[IsNoetherianRing B]`; see below);
- `exists_pow_smul_localCohomology_eq_zero`: every element of `H^q_I(M)` is killed by a power of
  `I` (the stage `Ext^q(A ⧸ Iⁿ, M)` is killed by `Iⁿ`, by `main`'s
  `Ext.smul_eq_zero_of_mem_annihilator_left` and `Ideal.annihilator_quotient`), for any
  commutative ring;
- **`localCohomology_flat_excision`** (the README's flat excision, Stacks, Lemma 47.9.7): if
  moreover `Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) _` (that is,
  `A ⧸ I → B ⧸ I B`) is bijective, then
  `Nonempty ((localCohomology I q).obj M ≅ (restrictScalars (algebraMap A B)).obj
  ((localCohomology (I.map (algebraMap A B)) q).obj (of B (B ⊗[A] M))))`, an isomorphism of
  `A`-modules. `Suggested.lean` does not pin it, so the statement follows the README wording and
  the shape of `localCohomology_flat_baseChange`.

`TauCeti/RingTheory/Flat/PowerTorsion.lean` (new, 196 lines, split 10), in namespace
`TauCeti`, the module theory behind flat excision. Let `B` be a flat `A`-algebra with
`A ⧸ I → B ⧸ I B` bijective:

- `bijective_rTensor_mkₐ_of_smul_eq_zero`: if `I` kills `N`, then `C ⊗[A] N → (C ⧸ J) ⊗[A] N`
  is bijective for any `A`-algebra `C` and ideal `J ≤ I C` (right exactness, `rTensor_exact`);
- `bijective_one_tmul_of_smul_eq_zero`: `N → B ⊗[A] N` is bijective when `I` kills `N`;
- `bijective_one_tmul_of_pow_smul_eq_zero`: the same when `I^k` kills `N`, by induction on `k`
  along `0 → I N → N → N ⧸ I N → 0` (flatness and an elementwise five lemma);
- `bijective_one_tmul_of_forall_exists_pow_smul_eq_zero`: the same for `I`-power-torsion `N`,
  as the union of the `Submodule.torsionBySet A N (I ^ k)`.

Port notes (rubric audit): the instance `PreservesFiniteLimits (extendScalars (algebraMap A B))`
for flat `B` and `Supports.extendScalarsQuotientIso` (`B ⊗[A] (A ⧸ J) ≅ B ⧸ J'`) are general.
The port may move them to `TauCeti/Algebra/Category/ModuleCat/ChangeOfRings.lean` (as
`ModuleCat.extendScalarsQuotientIso`), at the price of new imports there. The branch keeps them
in the new files so as not to rebuild that widely imported `main` file. The new files use plain
`public section` (no `@[expose]`). Consumers go through `extBaseChange_one_tmul`,
`extBaseChangeLinearEquiv_tmul`, `extendScalarsQuotientIso_hom_one_tmul` (all `@[simp]`) and
`extLinearEquiv_extQuotientBaseChangeLinearEquiv_one_tmul`.

`Suggested.lean` pins

```lean
theorem localCohomology_flat_baseChange (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B]
    (I : Ideal A) (M : ModuleCat.{u} A) (q : ℕ) :
    Nonempty ((B ⊗[A] (localCohomology I q).obj M) ≃ₗ[B]
      (localCohomology (I.map (algebraMap A B)) q).obj (ModuleCat.of B (B ⊗[A] M))) := by
  sorry
```

The branch states exactly this, without `[IsNoetherianRing B]`. The proof never uses that
hypothesis, so dropping it gives a strictly stronger theorem. The pinned form is the special case.
The README also asks that the isomorphism be "compatibly with the geometric comparison", which can
only be stated once split 15's `localCohomology_module_comparison` exists.

### Session 13: the comparison map to cohomology with supports on `Spec A`

`main` (still `85f3eb5579d`) now has two inputs that sessions 8–12 listed as missing:
`TauCeti.AlgebraicGeometry.isFlasque_tilde_of_injective` (Hartshorne III.3.4: `J^~` is flasque for
an injective module `J` over a Noetherian ring,
`TauCeti/AlgebraicGeometry/Modules/Quasicoherent/Flasque.lean`) and the flasque vanishing and
dimension-shifting lemmas `CategoryTheory.Sheaf.relativeH'.subsingleton_succ_of_isFlasque` and
`extClass_postcomp_bijective_of_isFlasque` (`TauCeti/Topology/Sheaves/SupportedCohomology.lean`).
Mathlib also has the `I`-power torsion as `Ideal.primaryComponent`.

**Refactor (split 8).** The branch's `TauCeti.Supports.powerTorsion I M` had literally the same
definition as Mathlib's `Ideal.primaryComponent M I` (`⨆ n, torsionBySet A M (I ^ n)`), so it is
deleted. `DerivedTorsion.lean` now uses `I.primaryComponent M` throughout,
`mem_powerTorsion_iff` became `TauCeti.Supports.mem_primaryComponent_iff`, and
`map_mem_powerTorsion` became Mathlib's `Ideal.primaryComponent_map_mem`. The functor keeps the
name `powerTorsionFunctor`. Nothing else on the branch used the deleted names.

`TauCeti/AlgebraicGeometry/Cohomology/Support/Tilde.lean` (new, 227 lines, split 15), in namespace
`TauCeti.AlgebraicGeometry.Scheme.Modules`, for `R : CommRingCat`:

- `zeroLocusCloseds I : Closeds (Spec R)` (`@[expose]`), `coe_zeroLocusCloseds`, and
  `compl_zeroLocusCloseds_span G : V(span G)ᶜ = ⨆ g ∈ G, D(g)` for a finset `G`;
- `toOpen_eq_zero_iff`: `m ∈ M` vanishes as a section of `M^~` over `⋃_{g ∈ G} D(g)` iff a power
  of every `g` kills `m` (sheaf locality via `TopCat.Presheaf.IsSheaf.section_ext`);
- **`mem_sectionsWithSupport_tilde_iff`**: for finitely generated `I`, `s ∈ Γ_{V(I)}(Spec R, M^~)`
  iff `(tilde.isoTop M).inv s ∈ I.primaryComponent M` (Stacks 0A6T in degree zero);
- **`primaryComponentLinearEquivSectionsWithSupport`**:
  `Γ_I(M) ≃ₗ[R] (sectionsWithSupport (zeroLocusCloseds I) (tilde M)).restrictScalars R`;
- instance **`subsingleton_cohomologyWithSupport_tilde_succ`**: `H^{n+1}_Z(Spec R, J^~) = 0` for
  `J` injective over a Noetherian ring and any closed `Z`;
- `shortExact_map_tilde_toSheaf`, the connecting map **`cohomologyWithSupportTildeδ Z hS n`**
  (`H^n_Z(S.X₃^~) →+ H^{n+1}_Z(S.X₁^~)`, Yoneda product with the extension class of the sheafified
  sequence) with `cohomologyWithSupportTildeδ_apply`, and the dimension shifts
  **`bijective_cohomologyWithSupportTildeδ_succ`** and
  **`surjective_cohomologyWithSupportTildeδ_zero`** for `S.X₂` injective over a Noetherian ring.

`TauCeti/AlgebraicGeometry/Cohomology/Support/LocalCohomology.lean` (new, 314 lines, split 16), same
namespace, for a finitely generated ideal `I` (`hI : I.FG`):

- `one_mem_primaryComponent_quotient_pow`, and **`quotientPowOne hI k`**: the global section `1` of
  `(R ⧸ Iᵏ)^~`, supported in `V(I)`, as a morphism out of the relative free sheaf
  `ℤ_{Spec R, Spec R ∖ V(I)} ⟶ (tilde.functor R ⋙ toSheaf (Spec R)).obj (R ⧸ Iᵏ)`;
  `quotientPowOne_comp_map` (compatibility with `R ⧸ Iᵏ' ⟶ R ⧸ Iᵏ`);
- **`extToCohomologyWithSupport hI k M q`**: the stage `Ext^q_R(R ⧸ Iᵏ, M) →+ H^q_{V(I)}(Spec R, M^~)`,
  `x ↦ mk₀ (quotientPowOne hI k) ⬝ (x.mapExactFunctor (tilde.functor R ⋙ toSheaf _))`, with
  `extToCohomologyWithSupport_apply`, `extToCohomologyWithSupport_mk₀_comp` (transition maps),
  `extToCohomologyWithSupport_comp_mk₀` (naturality in `M`) and
  `extToCohomologyWithSupport_comp_extClass` (connecting maps, via `Ext.mapExactFunctor_extClass`
  and associativity of the Yoneda product);
- `localCohomologyStages`, `localCohomologyStagesCocone`, and **the comparison map
  `localCohomologyToCohomologyWithSupport hI q M : H^q_I(M) →+ H^q_{V(I)}(Spec R, M^~)`**, out of the
  colimit computed in abelian groups (`forget₂` preserves filtered colimits), with
  `localCohomologyToCohomologyWithSupport_ι_app` (stage formula),
  **`localCohomologyToCohomologyWithSupport_naturality`** (natural in `M`, against
  `cohomologyWithSupportMap _ (tilde.map f) q`) and **`localCohomologyToCohomologyWithSupport_δ`**
  (intertwines the native `Supports.localCohomologyδ` with `cohomologyWithSupportTildeδ`);
- degree zero: `coe_cohomologyWithSupportZeroLinearEquiv_extToCohomologyWithSupport_mk₀` (the
  stage sends `f : R ⧸ Iᵏ ⟶ M` to the section `tilde.isoTop M (f 1)`),
  `coe_cohomologyWithSupportZeroLinearEquiv_localCohomologyToCohomologyWithSupport` (under
  `H⁰_Z ≃ Γ_Z` it is `x ↦ tilde.isoTop M (localCohomologyZeroLinearEquiv I M x)`), and
  **`bijective_localCohomologyToCohomologyWithSupport_zero`**: bijective in degree zero for every
  finitely generated `I`, over any commutative ring.

Port notes (rubric audit): `one_mem_primaryComponent_quotient_pow` mentions only Mathlib types,
so the port should move it to `TauCeti/Algebra/Module/Torsion/PrimaryComponent.lean` (namespace
`Ideal`). Likewise `zeroLocusCloseds`, `coe_zeroLocusCloseds` and `compl_zeroLocusCloseds_span`
could move next to `PrimeSpectrum.zeroLocus` if a fitting `TauCeti/` file exists. The branch keeps
them in the new files so as not to rebuild those widely imported files. `zeroLocusCloseds` is not
exposed: `coe_zeroLocusCloseds` is proved by `(rfl)`.

Gotchas met in this session (for the next one): `Γ(tilde M, ⊤)` and
`(modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op ⊤)` are defeq but not syntactically equal,
so `rw` with a `sectionsWithSupport` membership on an element produced by `tilde.toOpen` or
`tilde.isoTop` fails (instance mismatch). Go through `.trans` with `mem_sectionsWithSupport_iff`
and `Sheaf.mem_supportedSections_iff`. `sectionsWithSupport`, `cohomologyWithSupportMap` and
`cohomologyWithSupportTildeδ` are not exposed, so in other modules use their `_apply` lemmas through
`Eq.trans`, not `rfl` or `rw`. State morphisms into the sheafified modules as
`(tilde.functor R ⋙ toSheaf (Spec R)).obj N`, the form `Ext.mapExactFunctor` produces, not as
`(toSheaf _).obj (tilde N)`. Otherwise `rw` with `Ext.comp_assoc*` fails.

### Session 14: the Noetherian geometric comparison (`localCohomology_module_comparison`)

Session 14 merged `main` (`e8758b7b2f8`, CI-only changes) and proved steps 2 and 3 of the
geometric comparison listed under "What remains" in session 13. Over a Noetherian ring the
comparison map is now bijective in every degree and `R`-linear, and the README's
`localCohomology_module_comparison` is proved.

`TauCeti/Algebra/Homology/LocalCohomology/Exact.lean` (+15 lines, split 7):

- `Supports.localCohomology_map_smul_id`: `(localCohomology I q).map (a • 𝟙 X) x = a • x`, stage
  by stage through `extLinearEquiv_Ext_obj_map` and Mathlib's `Ext.smul_eq_comp_mk₀`.

`TauCeti/AlgebraicGeometry/Cohomology/Support/Tilde.lean` (+34 lines, now 261, split 15):

- `tilde_map_smul_id`: `tilde.map (r • 𝟙 M) = (tilde M).globalSectionsSmul ((ΓSpecIso R).inv r)`,
  through the injectivity of `tilde.adjunction.homEquiv` (the unit is `tilde.isoTop`), Mathlib's
  `tilde.toOpen_map_app` and `smul_Spec_def`, and `main`'s `globalSectionsSmul_app`;
- `exists_cohomologyWithSupportMap_tilde_eq`: exactness of the geometric long exact sequence at
  `H^n_Z(Spec R, S.X₃^~)`, from Mathlib's `Ext.covariant_sequence_exact₃`.

`TauCeti/AlgebraicGeometry/Cohomology/Support/LocalCohomology.lean` (+36 lines, now 350, split 16):

- `localCohomologyToCohomologyWithSupport_smul`: `Φ (r • x) = (ΓSpecIso R).inv r • Φ x`
  (naturality applied to `r • 𝟙 M`, plus the two lemmas above);
- `localCohomologyToCohomologyWithSupportHom hI q M`: `Φ` as a morphism of `R`-modules
  `H^q_I(M) ⟶ (restrictScalars (ΓSpecIso R).inv.hom).obj (of Γ(Spec R, ⊤) H^q_{V(I)}(Spec R, M^~))`,
  with `localCohomologyToCohomologyWithSupportHom_apply` (`@[simp]`).

`TauCeti/AlgebraicGeometry/Cohomology/Support/Comparison.lean` (new, 163 lines, split 17), same
namespace:

- **`bijective_localCohomologyToCohomologyWithSupport`** (`[IsNoetherianRing R]`, `hI : I.FG`):
  bijective in every degree, by induction on `q` simultaneously for all `M`, along
  `0 ⟶ M ⟶ Injective.under M ⟶ cokernel ⟶ 0`. For `q + 2` both connecting maps are bijective
  (`isZero_localCohomology_succ_of_injective`, `exists_localCohomologyδ_eq`,
  `exists_localCohomology_map_g_eq`, `bijective_cohomologyWithSupportTildeδ_succ`). For `q = 1`,
  surjectivity uses `surjective_cohomologyWithSupportTildeδ_zero`, and injectivity uses
  `exists_cohomologyWithSupportMap_tilde_eq`, degree zero for `J` and `N`, naturality and
  `localCohomology_map_g_comp_localCohomologyδ`;
- **`localCohomologyIsoCohomologyWithSupport I q M`**: the `R`-linear isomorphism
  `H^q_I(M) ≅ (restrictScalars (ΓSpecIso R).inv.hom).obj (of Γ(Spec R, ⊤) H^q_{V(I)}(Spec R, M^~))`,
  with `localCohomologyIsoCohomologyWithSupport_hom_apply` (`@[simp]`);
- **`localCohomology_module_comparison`** (README name): there are `R`-linear isomorphisms
  `e M` for all `M`, natural in `M` (against `cohomologyWithSupportMap _ (tilde.map f) q`);
- **`rightDerivedPowerTorsionIsoCohomologyWithSupport I q M`**:
  `R^q Γ_I(M) ≅ H^q_{V(I)}(Spec R, M^~)`, composing session 11's
  `localCohomologyIsoRightDerived` with the above. This is the second, Noetherian half of
  `localCohomology_colimit_ext_comparison` ("identify derived torsion with `RΓ_{V(I)}`", Stacks
  0955), in degree `q` on `Spec A`.

`Suggested.lean` does not pin `localCohomology_module_comparison`. The statement follows the README
("the natural `A`-linear isomorphism `H^q_Z(X,F) ≅ (localCohomology I q).obj M`"). `R` acts on
cohomology with supports through `Γ(Spec R, ⊤)` (`main`'s `cohomologyWithSupportModule`), so the
`R`-linear structure is `ModuleCat.restrictScalars (ΓSpecIso R).inv.hom`, the same device as
`localCohomology_flat_excision`. The isomorphism goes from local cohomology to cohomology with
supports. That is the direction of the comparison map. The README writes it the other way round.

Port notes (rubric audit): `tilde_map_smul_id` mentions no cohomology, so the port may move it next
to `main`'s `TauCeti/AlgebraicGeometry/Modules/Tilde/Basic.lean` (at the price of importing
`Modules/GlobalSections.lean` there). `localCohomologyToCohomologyWithSupportHom` is not exposed.
Use its `_apply` lemma. The degree-one injectivity argument uses only the elementwise exactness
lemmas, not a five lemma, because the two long exact sequences live in different categories
(`ModuleCat R` and abelian groups).

### Session 15: the collected §2.7 checks (split 18, started)

Session 15 found `main` unchanged (`e8758b7b2f8`) and wrote the checks file of split 18.

`TauCeti/Examples/AlgebraicGeometry/Cohomology/Support/Checks.lean` (new, 144 lines, namespace
`TauCeti.Supports`):

- `test_support_all X M q`: `Nonempty (H^q_X(X, M) ≃ₗ[Γ(X, ⊤)] H^q(X, M))`, in every degree
  (the README asks for `q = 1`), from `cohomologyWithSupportTopLinearEquiv`;
- `test_support_empty`: `Subsingleton (H^q_∅(X, M))`;
- `test_support_affine_line_origin`: `H⁰_{V(t)}(𝔸¹_k, 𝒪) = 0` and
  `H¹_{V(t)}(𝔸¹_k, 𝒪) ≃+ k[T;T⁻¹] ⧸ k[X]`;
- `test_support_not_restriction`: the origin is the image of `Spec k ⟶ 𝔸¹_k`, `Γ(Spec k, ⊤)` is
  nontrivial, and `H⁰_{V(t)}(𝔸¹_k, 𝒪) = 0`;
- `test_depth_dvr`: `H⁰_m(R) = 0` and `H¹_m(R) ≃ₗ[R] K ⧸ R` (native functors, split 14);
- `DiscreteValuationRingExample.nonempty_localCohomology_iso_cohomologyWithSupport`: for a DVR
  and a uniformizer `ϖ`, an `R`-linear isomorphism `H^q_m(R) ≅ H^q_{V(ϖ)}(Spec R, 𝒪)` (through
  `restrictScalars (ΓSpecIso R).inv.hom`) in every degree, from split 17's
  `localCohomologyIsoCohomologyWithSupport` (`V(m) = V(ϖ)`, and Mathlib's `tildeSelf` is
  `Iso.refl`, so `R^~` is the structure sheaf by definition);
- **`localCohomology_module_comparison_dvr`**: `H⁰_m(R) = 0` and `H¹_m(R) ≃ₗ[R] K ⧸ R`, derived
  from the general comparison and the geometric computations (not from the native computation).

`TauCeti/AlgebraicGeometry/Cohomology/Support/Affine.lean` (+43 lines, now 292, split 13; only the
examples import this file, so the port may also move it to split 18):

- `cohomologyWithSupportSpecOneLinearEquiv a L`: the `A`-linear form
  `restrictScalars (ΓSpecIso A).inv.hom (H¹_{V(a)}(Spec A, 𝒪)) ≃ₗ[A] L ⧸ range (Algebra.linearMap A L)`
  of `cohomologyWithSupportSpecOneEquiv`, from the `Γ`-linearity of
  `cohomologyWithSupportBasicOpenOneLinearEquiv` and `IsLocalization.ringEquivOfRingEquiv_eq`.

`localCohomology_module_comparison_nil_ideal` (split 14) and `depth_localCohomology_zero_guard`
(split 4) already carry their README names, so the checks file only points to them.

Rubric audit (session 15): a scratch `#lint in TauCeti` over the import closure of `Checks.lean`
found one simpNF failure, in split 6. `derivedExtOneLinearEquiv_mk` (`Principal.lean`) had
`Submodule.Quotient.mk r` on its left-hand side, which simp rewrites to `Ideal.Quotient.mk`. It is
now stated with `Ideal.Quotient.mk (Ideal.span {a} ^ n) r`, and the lint is clean. The DVR helper
lives in `DiscreteValuationRingExample`, because it is specific to that example.

## What `main` already has (found in session 2)

`sectionsWithSupport` is `CategoryTheory.Sheaf.supportedSections F S W`
(`TauCeti/Topology/Sheaves/SupportedCohomology.lean`). `supportedSubsheaf` is
`supportedSectionsSheaf`. `cohomologyWithSupport` is `supportedH`, with `supportedHZeroEquiv` for
degree zero. `localCohomologySheaf` is `supportedHSheaf`, with `supportedHSheafZeroIso`. The long
exact sequence of `supports_localization_triangle` is `relativeH'.exact_toH'_cohomologyPresheaf_map`,
`exact_cohomologyPresheaf_map_δ` and `exact_δ_toH'`. Excision is `supportedHExcisionEquiv`.

### Session 16: the long exact sequence of cohomology with supports and its pullback

Session 16 merged `main` (no new commits since `e8758b7b2f8`) and closed the item "compatibility
of `cohomologyWithSupport_pullback` with the connecting maps" from "What remains".

`TauCeti/CategoryTheory/Sites/SheafCohomology/Relative/Pullback.lean` (+12 lines, split 3):

- `CategoryTheory.Sheaf.relativeH'.pullback_comp_extClass`: for a short exact sequence `T` of
  abelian sheaves, `pullback u T.X₁ i n₁ (x ⬝ [T]) = pullback u T.X₃ i n₀ x ⬝ [u^* T]`
  (`Ext.mapExactFunctor_comp`, `Ext.mapExactFunctor_extClass`, associativity), the relative
  analogue of `main`'s `Sheaf.H.pullback_δ`.

`TauCeti/Topology/Sheaves/SupportedCohomology/Pullback.lean` (+17 lines, split 3):

- `TopCat.Hom.supportedHPullback_comp_extClass`: the same for `f.supportedHPullback`.

`TauCeti/AlgebraicGeometry/Cohomology/Support.lean` (+79 lines, now 353, split 12), namespace
`TauCeti.AlgebraicGeometry.Scheme.Modules`:

- **`cohomologyWithSupportδ Z hS n₀ n₁ h : H_Z^{n₀}(X, S.X₃) →+ H_Z^{n₁}(X, S.X₁)`** for a short
  exact sequence `S` of `X.Modules` (Yoneda product with the class of the underlying short exact
  sequence of abelian sheaves), with `cohomologyWithSupportδ_eq` and `cohomologyWithSupportδ_apply`;
- exactness of the long exact sequence: `exact_cohomologyWithSupportMap_cohomologyWithSupportMap`,
  `exact_cohomologyWithSupportMap_cohomologyWithSupportδ`,
  `exact_cohomologyWithSupportδ_cohomologyWithSupportMap` (Mathlib's
  `Ext.covariant_sequence_exact₁'`/`₂'`/`₃'`);
- `cohomologyWithSupportδ_naturality` (in morphisms of short exact sequences, via
  `ShortComplex.ShortExact.extClass_naturality`) and `cohomologyWithSupportδ_smul` (linearity over
  `Γ(X, ⊤)`, naturality along multiplication by `r`).

`TauCeti/AlgebraicGeometry/Cohomology/Support/Pullback.lean` (+42 lines, now 164, split 12):

- **`Scheme.Hom.cohomologyWithSupportPullback_cohomologyWithSupportδ`**: for `S` short exact with
  `S.map (pullback g)` short exact (e.g. `g` flat and `S.X₁`, `S.X₂` quasi-coherent, `main`'s
  `shortExact_map_pullback_of_flat`), `g^*` intertwines the two connecting maps. It mirrors `main`'s
  `cohomologyPullback_cohomologyδ`: the comparison `g⁻¹ ⟶ g^*` is a morphism of short exact
  sequences, and `extClass_naturality` moves it past the extension class.

Refactor (rubric audit, reuse): the general connecting map replaces the tilde-specific one of
session 13. `Support/Tilde.lean` (now 238 lines) drops `shortExact_map_tilde_toSheaf`,
`cohomologyWithSupportTildeδ`, `cohomologyWithSupportTildeδ_apply` and
`exists_cohomologyWithSupportMap_tilde_eq`. It gains `shortExact_map_tilde : (S.map (tilde.functor
R)).ShortExact`, and the dimension shifts are restated as `bijective_cohomologyWithSupportδ_tilde_succ`
and `surjective_cohomologyWithSupportδ_tilde_zero` about
`cohomologyWithSupportδ Z (shortExact_map_tilde hS)`. `Support/LocalCohomology.lean`
(`extToCohomologyWithSupport_comp_extClass`, `localCohomologyToCohomologyWithSupport_δ`) and
`Support/Comparison.lean` (the degree-one injectivity now uses
`exact_cohomologyWithSupportMap_cohomologyWithSupportδ`) follow. Session-13/14 notes above that
name the deleted declarations describe the state before this refactor.

Gotchas (session 16): `rw` with `Ext.comp_assoc_of_*_deg_zero` or with the `_apply` lemmas fails
when `x : cohomologyWithSupport Z M q` (stated through `SheafOfModules.toSheaf X.ringCatSheaf`)
meets terms stated through `toSheaf X` or `(S.map (toSheaf X)).Xᵢ`: the motive is not type-correct
at instances transparency. State each step as a `have` with explicit arguments and chain them
with `Eq.trans`/`congrArg`. In the same way, give `hS.map_of_exact F` an explicit `F`, including
its topologies. Otherwise elaboration postpones it and fails with a universe or type mismatch.
`cohomologyWithSupportδ` is not exposed, so other modules rewrite with `cohomologyWithSupportδ_eq`
before applying a lemma stated through `Ext.postcomp`.

### Session 17: refresh on `main`

Session 17 merged `main` at `d0b6fe9d754` (infrastructure commits only, nothing under `TauCeti/`),
rebuilt the whole branch and reran `lookahead-check`. No declaration changed. Each item left under
"What remains" needs more than one session: the `𝒪_X`-module structure on `localCohomologySheaf`
needs the action of `𝒪_X(W)` on `H_Z^q(W, M|_W)` compatibly with restriction, and
`rHZ_adjunction`/`localToGlobal` need a derived-category `RΓ_Z`, which `main` does not have.

### Session 18: the affine-line check is linear

Session 18 merged `main` at `b3b0334ab92` (infrastructure commits only, nothing under `TauCeti/`).

`TauCeti/Examples/AlgebraicGeometry/Cohomology/Support.lean` (split 13): the additive
`AffineLineExample.cohomologyWithSupportOriginOneEquiv` is replaced by
**`cohomologyWithSupportOriginOneLinearEquiv`**, `H¹_{V(t)}(𝔸¹_k, 𝒪) ≃ₗ[k[t]] k[t, t⁻¹] ⧸ k[t]`
(with `k[t]` acting through `ΓSpecIso`), a direct instance of session 15's
`cohomologyWithSupportSpecOneLinearEquiv`. The check `test_support_affine_line_origin`
(`Checks.lean`, split 18) now states the `k[t]`-linear isomorphism instead of an `AddEquiv`.

### Session 19: refresh on `main`, and the plan for what remains

Session 19 resumed the branch at `2e303f92c4d`; `origin/main` was still `b3b0334ab92`, so the merge
was a no-op. It rebuilt the whole branch and reran `lookahead-check`; no declaration changed. Each
remaining item was scoped against `main` and is larger than one session:

- **Flat base change compatibly with the geometric comparison.** For `g = Spec.map (algebraMap A B)`,
  the statement is that `localCohomologyIsoCohomologyWithSupport` for `B` composed with
  `localCohomologyBaseChangeIso` agrees with `cohomologyWithSupportPullback g` (with
  `g⁻¹ V(I) = V(IB)`) after `B ⊗_A −` on the source. Stage by stage this needs: an isomorphism
  `g^* (M^~) ≅ (B ⊗_A M)^~` compatible with the pullback of the sections `1` of `(A ⧸ Iᵏ)^~`
  (`quotientPowOne`), and the identity `Ext.mapExactFunctor (tilde ⋙ toSheaf)` intertwining
  `extBaseChangeLinearEquiv` with `cohomologyWithSupportPullback`. The second needs `g^*` to be
  exact on the quasi-coherent sheaves involved (`main`'s `shortExact_map_pullback_of_flat` gives it on
  short exact sequences, not as an exact functor), so the stage comparison must be done through a
  projective resolution of `A ⧸ Iᵏ`, as in `Support/Comparison.lean`.
- **`localCohomologySheaf` as an `𝒪_X`-module.** The abelian sheaf is `main`'s
  `Sheaf.supportedHSheaf` of the underlying abelian sheaf, and a bare renaming of it would add
  nothing. The `𝒪_X(W)`-action on `H_Z^q(W, M)` comes from `cohomologyWithSupportModule` on the open
  subscheme `W` applied to `M|_W` (with `Γ(W, ⊤) ≅ 𝒪_X(W)`). The missing ingredient is the
  restriction isomorphism `H_Z^q(W, M) ≃+ H_{Z ∩ W}^q(W, M|_W)` of supported cohomology along an open
  immersion, natural in `W`; `main` has excision (`supportedHExcisionEquiv`) and pullback
  (`supportedHPullback`, split 3) but not this isomorphism. After it, the presheaf of
  `𝒪_X`-modules is assembled as `supportedModuleHPresheaf` is, and sheafified in `X.Modules`.
- **`rHZ_adjunction` and `localToGlobal`** need `RΓ_Z` and `RH_Z` as functors on `D(X)`; `main`
  has no derived pushforward along a closed immersion, so both wait on that infrastructure.

### Session 20: refresh on `main`, which now has module-valued supported cohomology

Session 20 merged `main` at `cd908f3e94a` (many commits under `TauCeti/`; the merge had no
conflicts, and no branch import was renamed or deleted). It rebuilt the whole library and reran
`lookahead-check`. The only fix: `main` renamed `isLocalizationAway_fractionRing` to
`Irreducible.isLocalizationAway_fractionRing`, so splits 14 and 18 now call
`hϖ.isLocalizationAway_fractionRing`. No declaration on the branch changed, and none of the branch's names
(`supportedHOneEquiv`, `oneAddEquivOfSubsingleton`, `supportedHTopEquiv`, `supportedHPullback`,
`extBaseChangeLinearEquiv`, `localCohomologyIsoRightDerived`, ...) now exists on `main`.

On `main` now (partly new since session 19), and relevant to what remains:

- `TauCeti/Topology/Sheaves/SupportedCohomology/{Module,Sections,Composition,LongExactSequence}.lean`:
  the `R`-linear `supportedModuleH`, its presheaf `supportedModuleHPresheaf`, the sheaf of
  supported submodules `supportedSubmoduleSheaf`, and the coefficient long exact sequence
  `supportedModuleHPresheafδ` for sheaves of `R`-modules.
- `TauCeti/Topology/Sheaves/LocalCohomology/{Module,LongExactSequence}.lean`: the sheafified `supportedModuleHSheaf S n`
  (a sheaf of `R`-modules for a constant ring `R`), `supportedModuleHSheafZeroIso`,
  `supportedModuleHSheafδ` and its exactness, and flasque vanishing.

These give `localCohomologySheaf` over a constant ring, not yet over `𝒪_X`. The next session
should build the scheme wrapper on `supportedModuleHSheaf` where the ring is constant, and on
the restriction isomorphism along open immersions (see session 19) for the `𝒪_X`-action. Split 12's
`cohomologyWithSupportδ` should also be compared with `main`'s `supportedModuleHPresheafδ`
at `W = ⊤`, and rebuilt on it if the two agree, so that it does not duplicate `main` (reuse rubric).

### Session 21: scheme-module local cohomology sheaves

`TauCeti/AlgebraicGeometry/Cohomology/Support/Sheaf.lean` constructs the sheaf
of sections supported in `Z` using Mathlib's `PresheafOfModules.Submodule`.
The local scalar action comes directly from the semilinearity of restriction in
`M`, so it does not require local functions to extend to global functions.
Its underlying abelian sheaf is `Sheaf.supportedSectionsSheaf`, naturally in `M`;
this existing API supplies left exactness, instead of another elementwise proof.

Public declarations:

- `supportedSubsheaf`, `supportedSubsheafι`, its complement
  restriction formula, and the monomorphism instance;
- `supportedSubsheafGlobalSectionsLinearEquiv`, with its section formula;
- `supportedSubsheafLift` with its inclusion identity (the universal factorization);
- `supportedSubsheafFunctor`, its object formula and natural inclusion
  `supportedSubsheafFunctorι` with its component formula,
  additivity, `supportedSubsheafFunctorForgetIso` and finite-limit preservation;
- `isZero_stalk_supportedSubsheaf_of_notMem`;
- `localCohomologySheaf Z M q`, defined as the actual right derived functor
  `(supportedSubsheafFunctor Z).rightDerived q` in `X.Modules`;
- `localCohomologySheafZeroIso`, `localCohomologySheafZeroSectionsLinearEquiv`,
  `localCohomologySheafZeroCohomologyWithSupportLinearEquiv`;
- `isZero_stalk_localCohomologySheaf_of_notMem`, proved using exactness of stalks
  applied to a supported injective-resolution complex;
- `isZero_localCohomologySheaf_succ_of_injective`.

Merge repairs preserve both filtered-colimit APIs in
`Algebra/Category/ModuleCat/FilteredColimits.lean`, without redeclaring a universe.
The branch's `Sheaf.H'AddEquivExt_cohomologyPresheafFunctor_map_app` is superseded by
`main`'s `Sheaf.cohomologyPresheafFunctor_map_app_apply`: the former is deleted and
both branch consumers use the latter. No compatibility alias remains.

Rubric audit: reused Mathlib's submodule presheaf and right derived functor rather
than adding carriers; reused the abelian supported-section sheaf for the sheaf
condition and exactness; supplied the inclusion/lift API and natural forgetful
comparison; kept the coefficient-map implementation and its helper lemma private, exposed the
functor object formula and natural inclusion, and documented the on-`X`
convention. The status remains partial because object-level right derived functors
do not supply the missing derived-category adjunction or spectral sequence.

## What remains

- `cohomologyWithSupport_pullback` is done (session 6, splits 3 and 12), including its
  compatibility with the connecting maps (session 16).
- `rHZ_adjunction` and `localToGlobal`: derived-category statements; `main` has only the edge map
  `supportedHEdgeEquiv`. Include the all-degree comparison between the relative-Ext
  groups `cohomologyWithSupport` and the right derived functor of global supported
  sections on scheme modules, with its scalar action. The new degree-zero
  comparison alone does not establish that all-degree identification.
- `localCohomology_colimit_ext_comparison`: done in every degree. Session 11 proved
  `localCohomologyIsoRightDerived I q : localCohomology I q ≅ (powerTorsionFunctor I).rightDerived q`
  (split 8, any commutative ring), and session 14 identified derived torsion with cohomology with
  supports on `Spec A` (`rightDerivedPowerTorsionIsoCohomologyWithSupport`, split 17). Only the
  derived-category (`RΓ_{V(I)}` as an object of `D(A)`) form is not stated; `main` has no
  derived-category `RΓ_Z` yet.
- **The geometric comparison** `localCohomology_module_comparison` (Stacks 0A6T) is done (session
  14, split 17): bijectivity in every degree, `R`-linearity, the natural isomorphism.
  `Supports.localCohomology_flat_baseChange` and flat excision `localCohomology_flat_excision`
  are done (session 12, splits 9 and 10). What remains of that README sentence is the clause
  "compatibly with the geometric comparison": the comparison isomorphisms for `A` and for `B`
  should intertwine `localCohomologyBaseChangeIso` with the flat pullback along
  `Spec B → Spec A`.
- `localCohomologySheaf Z F q` as an `𝒪_X`-module on `X` is done in session 21.
  Remaining: identify its underlying abelian sheaf in every degree with
  `Sheaf.supportedHSheaf` (only degree zero is currently compared), and transport
  it to the ringed closed subspace for `rHZ_adjunction`.
- `Γ(X, ⊤)`-linearity is done for the structure sheaf on `V(r)`
  (`cohomologyWithSupportBasicOpenOneLinearEquiv`) and, as a compatibility lemma, for any
  quasi-coherent `M` (`cohomologyWithSupportOneEquiv_globalSectionsSmul`). Session 15 added the
  `A`-linear `cohomologyWithSupportSpecOneLinearEquiv` on `Spec A`, so the DVR comparison check
  is `R`-linear. Session 18 made the affine-line identification `k[t]`-linear; session 9's DVR `AddEquiv` is
  still additive (its `R`-linear form is `test_depth_dvr`).
- Final split 20. Done in session 15: every README check (`Checks.lean`, see session 15),
  including `localCohomology_module_comparison_dvr` through the general comparison. Remaining:
  - (optional) check that the comparison isomorphism itself matches the two degree-one
    computations along a nonzerodivisor (`localCohomologyOneLinearEquiv` and
    `cohomologyWithSupportSpecOneLinearEquiv`), not only that both sides are `K ⧸ R`;
  - the clause "compatibly with the geometric comparison" of `localCohomology_flat_baseChange`;
  - the all-degree sheaf comparison, `rHZ_adjunction` and `localToGlobal`;
  - `supports_localization_triangle` as an actual distinguished triangle on derived
    categories (the existing group-level long exact sequence is not this triangle),
    with scheme-level excision and its compatibility with the derived functors.

## Current split plan

This plan replaces the historical split numbering in the session notes. It folds
the former 94-line full-support prerequisite into the scheme supported-cohomology
construction, moves all DegreeZero.lean additions together with their left-derived
prerequisite, and groups the native and geometric examples. The unproved derived
work is assigned separate topics; it is not hidden in a large final wrapper PR.
Line budgets for unproved files are planning estimates, not claims of completion.

Every PR description must contain `Roadmap: SchemeAndStackFoundations` as a
standalone line and cite `SchemeAndStackFoundations/README.md`, §2.7. For each split,
wait for all listed prerequisites to merge into main, then rebase and include only
that split. Independent splits may be opened concurrently. No PR is opened in this round.

1. **feat: degree zero of local cohomology is power torsion**. Must merge first: none.
   Files: `TauCeti/Algebra/Homology/LocalCohomology/DegreeZero.lean`, `TauCeti/CategoryTheory/Abelian/LeftDerived.lean`.
   Declarations and scope: The Ext-zero/Hom comparison, evaluation at one, the power-torsion equivalence and its characteristic API; naturality of the zeroth left-derived comparison. About 280 lines.
2. **feat: scheme cohomology with supports and its full-support comparison**. Must merge first: none.
   Files: `TauCeti/Topology/Sheaves/SupportedCohomology/Univ.lean`, `TauCeti/AlgebraicGeometry/Cohomology/Support.lean`, `TauCeti/AlgebraicGeometry/Modules/GlobalSections.lean`.
   Declarations and scope: The full-support equivalence, the global scalar section formula, sectionsWithSupport, cohomologyWithSupport, coefficient maps and connecting maps, and their linearity. About 466 lines; only the added lemma of GlobalSections.lean.
3. **feat: pullback of cohomology with supports**. Must merge first: 2.
   Files: `TauCeti/CategoryTheory/Sites/SheafCohomology/Relative/Pullback.lean`, `TauCeti/Topology/Sheaves/SupportedCohomology/Pullback.lean`, `TauCeti/AlgebraicGeometry/Cohomology/Support/Pullback.lean`.
   Declarations and scope: Free-Yoneda comparison, relative pullback, topological and scheme pullback, naturality, semilinearity and compatibility with connecting maps. About 483 lines.
4. **feat: local cohomology detects depth**. Must merge first: 1.
   Files: `TauCeti/Algebra/Homology/Ext/ProjectiveResolution.lean`, `TauCeti/Algebra/Homology/LocalCohomology/Depth.lean`.
   Declarations and scope: The added projective-resolution vanishing/injectivity comparison, vanishing below depth and nonvanishing in the finite depth degree, including the zero-module guard. About 355 added lines.
5. **feat: compare projective-resolution and derived-category Ext**. Must merge first: 4.
   Files: `TauCeti/Algebra/Homology/Ext/Comparison.lean`.
   Declarations and scope: The positive-degree Ext comparison with its coefficient, first-argument and connecting-map API. 322 lines.
6. **feat: degree-one local cohomology along a nonzerodivisor**. Must merge first: 5.
   Files: `TauCeti/Algebra/Homology/LocalCohomology/Principal.lean`.
   Declarations and scope: The principal-ideal Ext computation, passage to the colimit and localCohomologyOneLinearEquiv. 313 lines.
7. **feat: the long exact sequence of native local cohomology**. Must merge first: 1, 5.
   Files: `TauCeti/Algebra/Category/ModuleCat/FilteredColimits.lean`, `TauCeti/Algebra/Homology/LocalCohomology/Exact.lean`.
   Declarations and scope: Stage representation, vanishing and exactness for filtered colimits; extLinearEquiv, localCohomologyδ and the exact sequence. About 534 added lines; preserve main's universe-general forgetful instance.
8. **feat: native local cohomology computes derived power torsion**. Must merge first: 7.
   Files: `TauCeti/Algebra/Homology/LocalCohomology/DerivedTorsion.lean`.
   Declarations and scope: powerTorsionFunctor, its degree-zero comparison, universal delta-functor comparison, and localCohomologyIsoRightDerived. 524 lines.
9. **feat: flat base change of Ext over a Noetherian ring**. Must merge first: none.
   Files: `TauCeti/Algebra/Category/ModuleCat/Ext/FlatBaseChange.lean`.
   Declarations and scope: The finite-free resolution comparison and extBaseChangeLinearEquiv. 283 lines.
10. **feat: flat base change and excision for native local cohomology**. Must merge first: 7, 9.
   Files: `TauCeti/RingTheory/Flat/PowerTorsion.lean`, `TauCeti/Algebra/Homology/LocalCohomology/FlatBaseChange.lean`.
   Declarations and scope: Flat base change of power torsion, localCohomologyBaseChangeIso, localCohomology_flat_baseChange and localCohomology_flat_excision. 440 lines.
11. **feat: affine cohomology with supports and the affine-line origin**. Must merge first: 2.
   Files: `TauCeti/CategoryTheory/Sites/SheafCohomology/Relative.lean`, `TauCeti/Topology/Sheaves/SupportedCohomology.lean`, `TauCeti/AlgebraicGeometry/Cohomology/Support/Affine.lean`, `TauCeti/Examples/AlgebraicGeometry/Cohomology/Support.lean`.
   Declarations and scope: oneAddEquivOfSubsingleton, supportedHOneEquiv, the affine degree-one quotient, principal-complement vanishing, and the linear Laurent-polynomial computation. About 469 added lines.
12. **feat: local cohomology of a DVR and a non-Noetherian nil ideal**. Must merge first: 1, 6, 11.
   Files: `TauCeti/Examples/Algebra/Homology/LocalCohomology.lean`, `TauCeti/Examples/AlgebraicGeometry/Cohomology/Support/Comparison.lean`.
   Declarations and scope: The fresh-variable nil-ideal construction, native degree-zero vanishing, geometric nonvanishing and failure of non-Noetherian comparison; the DVR computation K/R. 351 lines.
13. **feat: supported cohomology of the sheaf associated to a module**. Must merge first: 2.
   Files: `TauCeti/AlgebraicGeometry/Cohomology/Support/Tilde.lean`.
   Declarations and scope: zeroLocusCloseds, associated-module supported sections, the geometric supported-cohomology functor and dimension shifting on injectives. 238 lines.
14. **feat: the comparison map from native to geometric local cohomology**. Must merge first: 7, 8, 13.
   Files: `TauCeti/AlgebraicGeometry/Cohomology/Support/LocalCohomology.lean`.
   Declarations and scope: The stage maps from Ext, localCohomologyToCohomologyWithSupport, naturality, compatibility with connecting maps, linearity, and degree-zero bijectivity. 351 lines.
15. **feat: native and geometric local cohomology agree over Noetherian rings**. Must merge first: 14.
   Files: `TauCeti/AlgebraicGeometry/Cohomology/Support/Comparison.lean`.
   Declarations and scope: All-degree bijectivity, localCohomologyIsoCohomologyWithSupport, localCohomology_module_comparison, and rightDerivedPowerTorsionIsoCohomologyWithSupport. 167 lines; this is the small, single-topic comparison step.
16. **feat: local cohomology sheaves of modules on a scheme**. Must merge first: 2.
   Files: `TauCeti/AlgebraicGeometry/Cohomology/Support/Sheaf.lean`.
   Declarations and scope: All session-21 declarations: the supported subsheaf, inclusion and universal lift, the left exact functor, localCohomologySheaf, degree zero, injective acyclicity and support of every stalk. 267 lines currently. Still add the all-degree comparison with the abelian supportedHSheaf; budget the completed split at about 300–600 lines.
17. **feat: the derived supported-section adjunction for a closed subspace**. Must merge first: 16.
   Files: `TauCeti/AlgebraicGeometry/Cohomology/Support/Derived.lean`.
   Declarations and scope: UNPROVED: transport to the ringed closed subspace (Z, i⁻¹𝒪_X), construct RH_Z and derive rHZ_adjunction on the derived categories specified in the README, with degreewise comparison to localCohomologySheaf. A bounded-below intermediate construction alone does not complete this split. Planned 300–600 lines; prerequisite work, never assume the adjunction as data.
18. **feat: the derived localization triangle and excision for supports**. Must merge first: 17.
   Files: `TauCeti/AlgebraicGeometry/Cohomology/Support/Localization.lean`.
   Declarations and scope: UNPROVED: supports_localization_triangle as an actual distinguished triangle, its comparison with the existing long exact sequence, and the open-neighbourhood excision isomorphism. Planned 200–600 lines.
19. **feat: flat base change respects the geometric local-cohomology comparison**. Must merge first: 3, 10, 15.
   Files: `TauCeti/AlgebraicGeometry/Cohomology/Support/BaseChange.lean`.
   Declarations and scope: UNPROVED: the compatibility square between localCohomologyBaseChangeIso, the geometric comparison for A and B, and scheme pullback along Spec B → Spec A. Planned 200–600 lines.
20. **feat: the local-to-global spectral sequence for cohomology with supports**. Must merge first: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19.
   Files: `TauCeti/AlgebraicGeometry/Cohomology/Support/LocalToGlobal.lean`, `TauCeti/Examples/AlgebraicGeometry/Cohomology/Support/Checks.lean`.
   Declarations and scope: PARTIAL: the 148-line Checks.lean exists. UNPROVED: construct and prove the convergent spectral sequence localToGlobal, with its boundedness hypotheses, edge maps and naturality, and finish the integration checks of the preceding splits. Planned 300–600 lines. This last split exports localToGlobal and is the only split completing the whole target.

## Current Lean file inventory

Counts are full source-file lengths, including unchanged portions of modified main files.

| File | Lines |
| --- | ---: |
| `TauCeti/Algebra/Category/ModuleCat/Ext/FlatBaseChange.lean` | 283 |
| `TauCeti/Algebra/Category/ModuleCat/FilteredColimits.lean` | 165 |
| `TauCeti/Algebra/Homology/Ext/Comparison.lean` | 322 |
| `TauCeti/Algebra/Homology/Ext/ProjectiveResolution.lean` | 291 |
| `TauCeti/Algebra/Homology/LocalCohomology/DegreeZero.lean` | 257 |
| `TauCeti/Algebra/Homology/LocalCohomology/Depth.lean` | 217 |
| `TauCeti/Algebra/Homology/LocalCohomology/DerivedTorsion.lean` | 524 |
| `TauCeti/Algebra/Homology/LocalCohomology/Exact.lean` | 411 |
| `TauCeti/Algebra/Homology/LocalCohomology/FlatBaseChange.lean` | 244 |
| `TauCeti/Algebra/Homology/LocalCohomology/Principal.lean` | 313 |
| `TauCeti/AlgebraicGeometry/Cohomology/Support.lean` | 361 |
| `TauCeti/AlgebraicGeometry/Cohomology/Support/Affine.lean` | 292 |
| `TauCeti/AlgebraicGeometry/Cohomology/Support/Comparison.lean` | 167 |
| `TauCeti/AlgebraicGeometry/Cohomology/Support/LocalCohomology.lean` | 351 |
| `TauCeti/AlgebraicGeometry/Cohomology/Support/Pullback.lean` | 164 |
| `TauCeti/AlgebraicGeometry/Cohomology/Support/Sheaf.lean` | 267 |
| `TauCeti/AlgebraicGeometry/Cohomology/Support/Tilde.lean` | 238 |
| `TauCeti/AlgebraicGeometry/Modules/GlobalSections.lean` | 462 |
| `TauCeti/CategoryTheory/Abelian/LeftDerived.lean` | 305 |
| `TauCeti/CategoryTheory/Sites/SheafCohomology/Relative.lean` | 508 |
| `TauCeti/CategoryTheory/Sites/SheafCohomology/Relative/Pullback.lean` | 213 |
| `TauCeti/Examples/Algebra/Homology/LocalCohomology.lean` | 170 |
| `TauCeti/Examples/AlgebraicGeometry/Cohomology/Support.lean` | 131 |
| `TauCeti/Examples/AlgebraicGeometry/Cohomology/Support/Checks.lean` | 148 |
| `TauCeti/Examples/AlgebraicGeometry/Cohomology/Support/Comparison.lean` | 181 |
| `TauCeti/RingTheory/Flat/PowerTorsion.lean` | 196 |
| `TauCeti/Topology/Sheaves/SupportedCohomology.lean` | 613 |
| `TauCeti/Topology/Sheaves/SupportedCohomology/Pullback.lean` | 106 |
| `TauCeti/Topology/Sheaves/SupportedCohomology/Univ.lean` | 94 |
