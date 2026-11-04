<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"projective-space-cohomology","main":"52f9d081237dadaf6d4eae13629281f7faa37d54","status":"complete","suppliers":["qcoh-higher-direct-image-vanishing"],"splits":[{"n":1,"after":[],"title":"feat: the top cohomology of the twisting sheaves on projective space"},{"n":2,"after":[1],"title":"feat: the top cohomology of the twisting sheaves on projective space is linear over the base ring"},{"n":3,"after":[1,2],"title":"feat: the cohomology of the twisting sheaves on projective space in every degree"}]}-->
# Lookahead: `projective-space-cohomology` (SchemeAndStackFoundations, Layer 2, §2.6)

Target (README §2.6): "Prove `projectiveSpace_cohomology`: `H^q(ℙ^n_A, O(d))` for every `q`, `d`
and ring `A`: `Sym^d` in degree `0`, the dual module in degree `n`, zero otherwise (Stacks,
Lemmas 30.8.1–30.8.3 (01XS))". `Suggested.lean` pins no form for this theorem; the README sentence
is the whole contract.

Built on `main` at `52f9d081237` (the branch merges `origin/main`). **Status: complete**, no
`sorry` outside the (empty) stub module.

## The exported theorem

`TauCeti/AlgebraicGeometry/Cohomology/ProjectiveSpace/Basic.lean`:

```lean
theorem TauCeti.SymmetricAlgebra.projectiveSpace_cohomology {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R M) {n : ℕ} (hn : n ≠ 0) (hκ : Fintype.card κ = n + 1) (q : ℕ) (d : ℤ) :
    (q = 0 → ∀ j : ℕ, d = j →
      Nonempty (Cohomology (Proj.twistingSheaf 𝒜 d) q ≃ₗ[R] 𝒜 j)) ∧
    (q = n → ∀ j : ℕ, d = -((j + (n + 1) : ℕ) : ℤ) →
      Nonempty (Cohomology (Proj.twistingSheaf 𝒜 d) q ≃ₗ[R] Module.Dual R (𝒜 j))) ∧
    ((q = 0 → d < 0) → (q = n → -((n + 1 : ℕ) : ℤ) < d) →
      Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 d) q))
```

for `ℙⁿ_R = Proj (Sym M)`, `M` free on `b`, `𝒜 = homogeneousSubmodule R M` (so `𝒜 j = Sym^j M`),
over any commutative ring `R`, for every `q : ℕ` and `d : ℤ`, all as `R`-modules. The explicit
isomorphisms are `TauCeti.SymmetricAlgebra.cohomologyZeroTwistingSheafLinearEquiv` (on `main`) and
`TauCeti.SymmetricAlgebra.cohomologyTopTwistingSheafLinearEquiv` (this branch).

Scope note: `n ≥ 1` (`hn`). For `ℙ⁰_R = Spec R` degrees `0` and `n` coincide; `main`'s `H⁰`
computation needs `Nontrivial κ`, and the top-degree computation needs two charts. The port may
add the trivial `n = 0` case if a reviewer asks, but CanonicalModelsAndGonality only consumes
`n ≥ 1`.

## Stubs

`TauCeti/Lookahead/ProjectiveSpaceCohomology/Stubs.lean` states **no declaration**; the port should
delete it. The target consumes nothing from its listed supplier `qcoh-higher-direct-image-vanishing`:

* `Suggested.lean` pins, for that supplier, only
  ```
  theorem higherDirectImage_vanishing {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
      [QuasiSeparated f] [IsAffine S] :
      ∃ N : ℕ, ∀ (F : X.Modules) [F.IsQuasicoherent] (p : ℕ), N ≤ p →
        Subsingleton (Scheme.Modules.Cohomology F p) := by
    sorry
  ```
  whose content for projective space (vanishing above the dimension, with the explicit bound) is
  already on `main` as `Module.Basis.subsingleton_cohomology_proj_of_card_le`, which the exported
  theorem uses; the uniform qcqs bound itself is also on `main`
  (`exists_subsingleton_cohomology_of_isAffine`).
* Open PR #27295 (rechecked 2026-11-04: still open, same files) adds `Hⁿ(U ∩ D(g), M) = Hⁿ(U, M)_g`,
  the `Γ(X, ⊤)`-module structure on `cohomologyOn`, Mayer–Vietoris `δ` naturality and a five lemma
  for `IsLocalizedModule`. None is needed: the computation goes through Leray's theorem for the
  standard affine cover, which is on `main`.

## What this branch adds

* `HigherCohomology.lean` (existing, 754 → 778 lines): the Laurent-polynomial model of the Čech
  complex of the standard cover is made public so that the top-degree file can use it:
  `negSupport`, `chartExponents`, `numeratorExponent`, `coordProd`, `chartSection`,
  `exponentBound`, `chartSectionHom`, `chartSectionsHom`, `chartFunctor`, `laurentPresheaf`,
  `sectionsPresheaf`, `laurentToSections`, `negSupportProj`, `laurentCech` and their lemmas
  `mem_negSupport`, `chartExponents_mono`, `degree_numeratorExponent(_eq_toNat)`, `coordProd_mem`,
  `basicOpen_le_basicOpen_pow`, `le_exponentBound`, `chartSectionHom_apply`,
  `chartSectionsHom_eq_sum`, `isAffineOpen_inf_chartFunctor_obj_singleton`,
  `iSup_chartFunctor_obj_singleton`, `isIso_cechComplexFunctor_map_laurentToSections`,
  `sum_negSupportProj`, `homologyMap_negSupportProj_of_notMem` (all previously `private`; the
  remaining helpers stay `private`). Factored out of the existing private
  `subsingleton_cohomology_twistingSheaf_aux` (which now uses them):
  `nonempty_pi_chartFunctor_obj_hom` and `cohomologyIsoHomologyLaurentCech` (Leray's comparison
  `H^q(𝒪(m)) ≅ H^q(Laurent Čech complex)`). The definitions the new file unfolds carry
  `@[expose]` (the eleven defs above other than `coordProd`, `sectionsPresheaf`, `laurentCech`,
  plus `cohomologyIsoHomologyLaurentCech`); the section itself is not exposed.
* `TopCohomology.lean` (new, 832 lines): the top degree.
  - Determinants of tuples of coordinates (`coordMatrix`, `det_coordMatrix_of_not_surjective`,
    `det_coordMatrix_self`, `det_coordMatrix_comp`, `sum_det_coordMatrix` — Laplace expansion of a
    singular matrix), `dupAt` and its faces, `ofDual_pi_eq_univ_iff`.
  - `topExponents`, `topPart`, `fromTop`, `evalTop`, `topCochain` (`a ↦ det(a) ℓ`), with
    `d_comp_evalTop`, `topCochain_comp_d`, `topCochain_comp_evalTop`; `topComponent`,
    `sum_topComponent` (cocycle condition), `topComponent_comp_swap`, `topComponent_comp_perm`,
    `topComponent_eq_det_smul` (a top cocycle is alternating); `homologyMap_negSupportProj_univ_top`,
    `toSingleTop`, `fromSingleTop`, `homologyLaurentCechTopIso`.
  - Linearity: `baseFunction`, `chartSectionHom_smul`, `chartSectionsHom_smul`, `laurentSmul`,
    `sectionsSmul`, `laurentSmul_comp_laurentToSections`, `topSmul`,
    `homologyMap_laurentSmul_comp_homologyLaurentCechTopIso_hom`,
    `cohomologyMap_comp_cohomologyIsoHomologyLaurentCech_hom`, and `cohomologyTopLinearEquivAux`,
    whose `map_smul'` follows `Cohomology/Cech/Linear.lean` (`ConcreteCategory.congr_hom` of the
    morphism identity, then `Scheme.Modules.base_smul_cohomology`/`cohomology_smul`).
  - `negExponentEquiv`, `topLaurentLinearEquivDual` (`x^{-P-1} ↦` dual basis vector of `x^P`).
  - Public: `TauCeti.SymmetricAlgebra.cohomologyTopTwistingSheafLinearEquiv (b) (hκ : card κ = n + 2) (j) :
    Cohomology (Proj.twistingSheaf 𝒜 (-((j + (n + 2) : ℕ) : ℤ))) (n + 1) ≃ₗ[R] Module.Dual R (𝒜 j)`,
    for `κ` in any universe (reindexed through `ULift (Fin (n + 2))`). All other declarations of
    the file are `private`.
* `Basic.lean` (new, 80 lines): `projectiveSpace_cohomology`, assembled from `main`'s
  `cohomologyZeroTwistingSheafLinearEquiv`, `subsingleton_cohomology_zero_twistingSheaf_of_neg`,
  `Module.Basis.subsingleton_cohomology_twistingSheaf_of_lt_card`,
  `Module.Basis.subsingleton_cohomology_twistingSheaf_of_neg_card_lt`,
  `Module.Basis.subsingleton_cohomology_proj_of_card_le` and the new top-degree equivalence.

## Split plan

Roadmap attribution for each split: `Roadmap: SchemeAndStackFoundations`.

1. *feat: the top cohomology of the twisting sheaves on projective space* (after: none).
   Files: `ProjectiveSpace/HigherCohomology.lean` (the de-privatisation and the factored
   `cohomologyIsoHomologyLaurentCech`, ~+60/−40), new `ProjectiveSpace/TopCohomology.lean` without
   the linearity material (~620 lines: Determinant, top-degree Čech computation, Dual), exporting
   the additive version `cohomologyTopTwistingSheafAddEquiv : … ≃+ Module.Dual R (𝒜 j)` (built
   from `(cohomologyIsoHomologyLaurentCech b m (n + 1) ≪≫ homologyLaurentCechTopIso m e)
   .addCommGroupIsoToAddEquiv` and `topLaurentLinearEquivDual`).
2. *feat: the top cohomology of the twisting sheaves on projective space is linear over the base
   ring* (after: 1). File: `ProjectiveSpace/TopCohomology.lean` (~+220): the section
   "Linearity over the base ring on the standard charts", `laurentSmul`, `sectionsSmul`,
   `laurentSmul_comp_laurentToSections`, `topSmul` and its three compatibility lemmas,
   `cohomologyMap_comp_cohomologyIsoHomologyLaurentCech_hom`, `cohomologyTopLinearEquivAux`;
   replaces split 1's `cohomologyTopTwistingSheafAddEquiv` by
   `cohomologyTopTwistingSheafLinearEquiv` (no alias kept). Imports
   `TwistingSheaf.GlobalSections` and `Cohomology.Module.Base`.
3. *feat: the cohomology of the twisting sheaves on projective space in every degree*
   (after: 1, 2). New file `ProjectiveSpace/Basic.lean` (80 lines) with the exported theorem
   `projectiveSpace_cohomology`; the only split that completes the target.

## Review notes for the port

* The Laurent-model API made public in `HigherCohomology.lean` is consumed only by
  `TopCohomology.lean`. If a reviewer objects to the `@[expose]` defs, the replacement is a set
  of characteristic lemmas (`laurentPresheaf_obj`, `laurentPresheaf_map_apply`,
  `mem_chartExponents_iff`, `chartSectionHom_of_notMem`, a `chartSection` evaluation lemma,
  `cohomologyIsoHomologyLaurentCech_hom`); the top-degree proofs currently use the defeqs.
* `projectiveSpace_cohomology` is a `∧`-bundle of the per-case results; it is the roadmap's named
  target, so it is kept as the single exported statement.
