<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"cohomology-with-support","main":"6c781b0a7341d9d794cf474258f824f4fa65faa2","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: degree zero of local cohomology is the power torsion"},{"n":2,"after":[],"title":"feat: cohomology with supports in the whole space is ordinary cohomology"},{"n":3,"after":[],"title":"feat: pullback of cohomology with supports"},{"n":4,"after":[1],"title":"feat: local cohomology vanishes below the depth and not in degree the depth"},{"n":5,"after":[1],"title":"feat: Noetherian local cohomology computes derived power torsion"},{"n":6,"after":[5],"title":"feat: flat base change of Noetherian local cohomology"},{"n":7,"after":[1],"title":"feat: degree-zero local cohomology of a DVR and of a non-Noetherian nil ideal"},{"n":8,"after":[2,3],"title":"feat: cohomology with supports of a sheaf of modules on a scheme"},{"n":9,"after":[8],"title":"feat: cohomology with supports on affine schemes and at the origin of the affine line"},{"n":10,"after":[7,9],"title":"feat: cohomology with supports in the DVR and nil-ideal local cohomology examples"},{"n":11,"after":[1,2,3,4,5,6,7,8,9,10],"title":"feat: geometric comparison of local cohomology and the section 2.7 checks"}]}-->

# Lookahead: `cohomology-with-support` (SchemeAndStackFoundations §2.7)

Built on `main` at `6c781b0a7341d9d794cf474258f824f4fa65faa2`. Status: **partial**.

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
  earlier stub `TauCeti.QCoh.higherDirectImage_vanishing` therefore had to go. Split 10 should use
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
  `cohomologyWithSupportZeroLinearEquiv` below, and goes in split 10.

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
of split 11 needs on the native side.

`TauCeti/Examples/AlgebraicGeometry/Cohomology/Support/Comparison.lean` (new), in namespace
`TauCeti.Supports`:

- `DiscreteValuationRingExample.uniformizerLocus ϖ` (the closed set `V(ϖ) ⊆ Spec R`, the
  complement of `D(ϖ)`), `coe_uniformizerLocus` (for a uniformizer it is `V(m)`, the closed point,
  so this is the README's `Z = V(m)`), `subsingleton_cohomologyWithSupport_zero` (for a domain and
  `ϖ ≠ 0`: `H⁰_{V(ϖ)}(Spec R, 𝒪) = 0`), `cohomologyWithSupportOneEquiv K hϖ :
  H¹_{V(ϖ)}(Spec R, 𝒪) ≃+ K ⧸ (algebraMap R K).range` (through `main`'s
  `TauCeti.isLocalizationAway_fractionRing`: `K` is `R` localized away from `ϖ`) and
  `subsingleton_cohomologyWithSupport_add_two`. These are the geometric halves of
  `test_depth_dvr`/`localCohomology_module_comparison_dvr`; once split 11 proves the comparison,
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

## What `main` already has (found in session 2)

`sectionsWithSupport` is `CategoryTheory.Sheaf.supportedSections F S W`
(`TauCeti/Topology/Sheaves/SupportedCohomology.lean`). `supportedSubsheaf` is
`supportedSectionsSheaf`. `cohomologyWithSupport` is `supportedH`, with `supportedHZeroEquiv` for
degree zero. `localCohomologySheaf` is `supportedHSheaf`, with `supportedHSheafZeroIso`. The long
exact sequence of `supports_localization_triangle` is `relativeH'.exact_toH'_cohomologyPresheaf_map`,
`exact_cohomologyPresheaf_map_δ` and `exact_δ_toH'`. Excision is `supportedHExcisionEquiv`.

## What remains

- `cohomologyWithSupport_pullback` is done (session 6, splits 3 and 8). Its compatibility with the
  connecting maps of short exact sequences is not stated yet.
- `rHZ_adjunction` and `localToGlobal`: derived-category statements; `main` has only the edge map
  `supportedHEdgeEquiv`.
- `localCohomology_colimit_ext_comparison` (split 5); `Supports.localCohomology_flat_baseChange`
  and flat excision (split 6). The native side's effaceability
  (`isZero_localCohomology_succ_of_injective`) is done; the geometric side needs that `J~` is
  flasque for an injective module `J` over a Noetherian ring (Hartshorne III.3.4), and both sides
  need a long exact sequence in `M` (for the native functor, a comparison of Mathlib's
  projective-resolution `Ext` with the derived-category `Ext` that is natural in both arguments,
  which only exists on the branch for vanishing and injectivity).
- `localCohomologySheaf Z F q` as a sheaf of `𝒪_X`-modules: `main` has the abelian
  `supportedHSheaf` and the `R`-linear `supportedModuleHPresheaf`, but no scheme wrapper yet.
- The native `H¹_m(R) ≅ K/R` of `test_depth_dvr`. Its geometric counterpart is done (session 8,
  split 10); once `localCohomology_module_comparison` is proved, the native one follows from it.
- `Γ(X, ⊤)`-linearity is done for the structure sheaf on `V(r)`
  (`cohomologyWithSupportBasicOpenOneLinearEquiv`) and, as a compatibility lemma, for any
  quasi-coherent `M` (`cohomologyWithSupportOneEquiv_globalSectionsSmul`). The affine-line and
  DVR examples still state their degree-one identifications additively.
- Split 11:
  - `localCohomology_module_comparison`, using
    `Scheme.Hom.exists_subsingleton_cohomology_of_isAffine`;
  - the checks `test_support_all` and `test_support_empty` (one line each, from
    `cohomologyWithSupportTopEquiv` and `subsingleton_cohomologyWithSupport_bot`),
    `test_support_affine_line_origin` and `test_support_not_restriction` (both proved in split 9;
    split 11 only collects them), `test_depth_dvr` (the native `H¹_m(R) ≅ K/R` half is still
    open), `localCohomology_module_comparison_nil_ideal` (complete in split 10; split 11 only
    collects it) and `localCohomology_module_comparison_dvr` (the geometric half is in split 10).

## Split plan

1. **feat: degree zero of local cohomology is the power torsion**. After: none.
   `TauCeti/Algebra/Homology/LocalCohomology/DegreeZero.lean` (done); the declarations listed
   above.
2. **feat: cohomology with supports in the whole space is ordinary cohomology**. After: none.
   `TauCeti/Topology/Sheaves/SupportedCohomology/Univ.lean` (done):
   `isZero_freeYonedaSheafFunctor_obj_bot`, `isIso_cokernel_π_complInclusion_top`,
   `supportedHTopEquiv`, `supportedHTopEquiv_apply`, `supportedHTopEquiv_naturality`,
   `toH'_complInclusion_top_bijective`; plus (session 7, +10 lines)
   `Sheaf.H'AddEquivExt_cohomologyPresheafFunctor_map_app` in
   `TauCeti/CategoryTheory/Sites/SheafCohomology/FreeYoneda.lean`.
3. **feat: pullback of cohomology with supports**. After: none (done, about 290 lines).
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Relative/Pullback.lean` and
   `TauCeti/Topology/Sheaves/SupportedCohomology/Pullback.lean`; the declarations listed under
   session 6 (all but the scheme wrapper).
4. **feat: local cohomology vanishes below the depth and not in degree the depth**. After: 1
   (done, about 345 lines). `TauCeti/Algebra/Homology/Ext/ProjectiveResolution.lean` (+138 lines):
   `ShortComplex.injective_homologyMap_moduleCat`,
   `HomologicalComplex.injective_homologyMap_moduleCat`, `Ext_map_comp_isoExt_hom`,
   `injective_Ext_map_succ`, `isZero_Ext_succ_iff_subsingleton`.
   `TauCeti/Algebra/Homology/LocalCohomology/Depth.lean` (208 lines): `isZero_Ext_iff_subsingleton`,
   `isZero_localCohomology_of_subsingleton_ext`, `subsingleton_ext_of_support_subset`,
   `subsingleton_ext_quotient_pow_of_lt_depth`, `depth_localCohomology_vanishing`,
   `injective_ext_precomp_quotient`, `injective_Ext_map_quotient`,
   `depth_localCohomology_nonvanishing`, `depth_localCohomology_zero_guard`, and (session 8, +9
   lines) `isZero_localCohomology_succ_of_injective`.
5. **feat: Noetherian local cohomology computes derived power torsion**. After: 1 (not yet written).
   `localCohomology_colimit_ext_comparison`.
6. **feat: flat base change of Noetherian local cohomology**. After: 5 (not yet written).
   `Supports.localCohomology_flat_baseChange`, flat excision.
7. **feat: degree-zero local cohomology of a DVR and of a non-Noetherian nil ideal**. After: 1
   (done, 170 lines). `TauCeti/Examples/Algebra/Homology/LocalCohomology.lean`:
   `isZero_localCohomology_zero_self_of_ne_bot`, `isZero_localCohomology_zero_maximalIdeal`, and
   in `NilIdealExample`: `relations`, `CoordRing`, `ideal`, `mem_relations_iff`,
   `exists_X_pow_mul_notMem_relations`, `one_notMem_relations`, the `Nontrivial` instance,
   `exists_mem_pow_mul_ne_zero`, `ideal_le_nilradical`, `zeroLocus_ideal`,
   `not_isNoetherianRing`, `isZero_localCohomology_zero`. (Split 1 carries the 25-line
   `isZero_localCohomology_zero_iff` and `isZero_localCohomology_zero_of_isSMulRegular` that
   this uses.)
8. **feat: cohomology with supports of a sheaf of modules on a scheme**. After: 2, 3 (done, about
   380 lines). `TauCeti/AlgebraicGeometry/Cohomology/Support.lean` (256 lines, including
   session 7's `cohomologyWithSupportTopEquiv_naturality` and
   `cohomologyWithSupportTopLinearEquiv`) plus
   `globalSectionsSmul_app_top_apply` in `TauCeti/AlgebraicGeometry/Modules/GlobalSections.lean`;
   the declarations listed under session 4. Also
   `TauCeti/AlgebraicGeometry/Cohomology/Support/Pullback.lean` (122 lines, session 6):
   `cohomologyWithSupportPullback` and its three lemmas. Session 8 adds (+18 lines)
   `cohomologyWithSupportZeroLinearEquivOfEqTop` and its `_apply` to `Support.lean`.
9. **feat: cohomology with supports on affine schemes and at the origin of the affine line**.
   After: 8 (done, about 350 lines). `oneAddEquivOfSubsingleton` (+18 lines in
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Relative.lean`), `supportedHOneEquiv` (+28 lines
   in `TauCeti/Topology/Sheaves/SupportedCohomology.lean`),
   `TauCeti/AlgebraicGeometry/Cohomology/Support/Affine.lean` (157 lines) and
   `TauCeti/Examples/AlgebraicGeometry/Cohomology/Support.lean` (151 lines); the
   declarations listed under sessions 5 and 7 (`origin`, `range_origin`,
   `isEmpty_cohomologyWithSupport_origin_zero_equiv`). Session 8 adds to `Affine.lean` (now 251
   lines) `cohomologyWithSupportOneEquiv_globalSectionsSmul`,
   `cohomologyWithSupportBasicOpenOneLinearEquiv` and `cohomologyWithSupportSpecOneEquiv`, and
   shrinks the example file to 127 lines; the split is now about 425 lines.
10. **feat: cohomology with supports in the DVR and nil-ideal local cohomology examples**. After:
   7, 9 (done, 145 lines). `TauCeti/Examples/AlgebraicGeometry/Cohomology/Support/Comparison.lean`:
   `DiscreteValuationRingExample.uniformizerLocus`, `subsingleton_cohomologyWithSupport_add_two`,
   `subsingleton_cohomologyWithSupport_zero`, `coe_uniformizerLocus`,
   `cohomologyWithSupportOneEquiv`; `NilIdealExample.idealZeroLocus`, `idealZeroLocus_eq_top`,
   `cohomologyWithSupportZeroEquiv`, the `Nontrivial` instance and
   `localCohomology_module_comparison_nil_ideal`.
11. **feat: geometric comparison of local cohomology and the section 2.7 checks**. After: 1–10 (not
   yet written). `localCohomology_module_comparison`, the remaining scheme wrappers and the
   remaining §2.7 checks. This is the only split that completes the target.
