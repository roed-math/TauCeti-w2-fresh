<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"projective-space-cohomology","main":"7ed979dc2eacd36a3962e1fdf3b481323fb3fb8b","status":"partial","suppliers":["qcoh-higher-direct-image-vanishing"],"splits":[{"n":1,"after":[],"title":"feat: the top cohomology of the twisting sheaves on projective space"},{"n":2,"after":[1],"title":"feat: the top cohomology of the twisting sheaves on projective space is linear over the base ring"},{"n":3,"after":[1,2],"title":"feat: the cohomology of the twisting sheaves on projective space in every degree"}]}-->
# Lookahead: `projective-space-cohomology` (SchemeAndStackFoundations, Layer 2, §2.6)

Target: `projectiveSpace_cohomology`: `Hᵠ(ℙⁿ_A, 𝒪(d))` for every `q`, `d` and ring `A`: `Sym^d` in
degree `0`, the dual module in degree `n`, zero otherwise (Stacks, Lemmas 30.8.1–30.8.3 (01XS)).
`Suggested.lean` pins no form for this theorem; the README sentence above is the whole contract.

Built on `main` at `7ed979dc2ea`.

## What `main` already has

Every case except the top degree is already on `main`, over any commutative ring and for
`ℙⁿ_R = Proj (Sym M)` with `M` free on a finite basis `b`:

* `H⁰(𝒪(j)) ≃ₗ[R] A_j` for `j : ℕ` (`TauCeti.SymmetricAlgebra.cohomologyZeroTwistingSheafLinearEquiv`)
  and `H⁰(𝒪(d)) = 0` for `d < 0` (`subsingleton_cohomology_zero_twistingSheaf_of_neg`);
* `Hᵠ = 0` for `0 < q < n` (`Module.Basis.subsingleton_cohomology_twistingSheaf_of_lt_card`) and for
  `q > 0`, `d > -n - 1` (`Module.Basis.subsingleton_cohomology_twistingSheaf_of_neg_card_lt`);
* `Hᵠ = 0` for `q > n` (`Module.Basis.subsingleton_cohomology_proj_of_card_le`).

## Stubs

`TauCeti/Lookahead/ProjectiveSpaceCohomology/Stubs.lean` states **no declaration**. The target
consumes nothing from its listed supplier `qcoh-higher-direct-image-vanishing`:

* `Suggested.lean` pins, for that supplier, only
  ```
  theorem higherDirectImage_vanishing {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
      [QuasiSeparated f] [IsAffine S] :
      ∃ N : ℕ, ∀ (F : X.Modules) [F.IsQuasicoherent] (p : ℕ), N ≤ p →
        Subsingleton (Scheme.Modules.Cohomology F p) := by
    sorry
  ```
  whose content for projective space (vanishing above the dimension, with the explicit bound) is
  already on `main` as `Module.Basis.subsingleton_cohomology_proj_of_card_le`; the uniform
  qcqs bound itself is also on `main` (`exists_subsingleton_cohomology_of_isAffine`, #22975).
* Open PR #27295 (partial, same slug) adds `Hⁿ(U ∩ D(g), M) = Hⁿ(U, M)_g`, the `Γ(X, ⊤)`-module
  structure on `cohomologyOn`, Mayer–Vietoris `δ` naturality and a five lemma for
  `IsLocalizedModule`. None of these is needed: the computation goes through Leray's theorem
  for the standard affine cover, which is on `main`.

So the stub module only carries the required header, `set_option warningAsError false` and a
docstring recording this. The port should simply delete it.

## What this branch proves

All in `TauCeti/AlgebraicGeometry/Cohomology/ProjectiveSpace/HigherCohomology.lean` (an existing
file, now 1355 lines; the in-build limit for existing files is 1500), no `sorry`:

* `Module.Basis.cohomologyTwistingSheafTopAddEquiv (b : Module.Basis κ R M) [Fintype κ]
  (hκ : Fintype.card κ = n + 2) (j : ℕ) :
  Cohomology (Proj.twistingSheaf 𝒜 (-((j + (n + 2) : ℕ) : ℤ))) (n + 1) ≃+ Module.Dual R (𝒜 j)`:
  the top cohomology of `𝒪(-j - n - 2)` on `ℙⁿ⁺¹_R` is the dual of the forms of degree `j`, as
  abelian groups, over any commutative ring, for `κ` in any universe.

Private supporting declarations (same file):

* determinants of tuples of coordinates (`coordMatrix`, `det_coordMatrix_of_not_surjective`,
  `det_coordMatrix_self`, `det_coordMatrix_comp`, `sum_det_coordMatrix` — Laplace expansion of a
  singular matrix), and the index map `dupAt` repeating an entry two places apart, with its faces;
* `topExponents`, `topPart`, `fromTop`: Laurent polynomials with all exponents negative;
* `evalTop`, `topCochain` and `d_comp_evalTop`, `topCochain_comp_d`, `topCochain_comp_evalTop`:
  the cocycle `a ↦ det(a) ℓ` and evaluation at a fixed enumeration `e` of the coordinates;
* `topComponent`, `sum_topComponent` (the cocycle condition), `topComponent_comp_swap`,
  `topComponent_comp_perm` (via `Equiv.Perm.mclosure_swap_castSucc_succ`),
  `topComponent_eq_det_smul`: a top cocycle is alternating;
* `homologyMap_negSupportProj_univ_top`, `homologyLaurentCechTopIso`: the top Čech cohomology of
  the Laurent presheaf is the group of Laurent polynomials with all exponents negative;
* `cohomologyIsoHomologyLaurentCech` (factored out of the existing
  `subsingleton_cohomology_twistingSheaf_aux`, which now uses it, together with
  `nonempty_pi_chartFunctor_obj_hom`), `cohomologyTopAddEquivAux`, `cohomologyTopAddEquivDual`;
* `negExponentEquiv`, `topLaurentLinearEquivDual`: `x^{-P-1} ↦` dual basis vector of `x^P`,
  `R`-linear.

## What remains (status `partial`)

1. **`R`-linearity of the top isomorphism.** `topLaurentLinearEquivDual` is already `R`-linear;
   what remains is that `Φ := cohomologyIsoHomologyLaurentCech b m (n + 1) ≪≫
   homologyLaurentCechTopIso m e` commutes with the action of `c : R`. All the categorical
   content of this was proved in this session but is **not on the branch** (the file would exceed
   its 1500-line limit while the last step is missing); the proven code is reproduced in the
   appendix below. It establishes, with no `sorry`:
   * `chartSectionsHom_smul`: `chartSectionsHom b m S (c • f) = baseFunction c _ • chartSectionsHom b m S f`
     (from `Proj.twistingSheaf.smul_apply`, `TauCeti.SymmetricAlgebra.val_baseRingToGlobalSections_apply`);
   * `laurentSmul_comp_laurentToSections`: multiplication by `c` on Laurent polynomials is
     intertwined with `globalSectionsSmul (baseRingToGlobalSections R _ c)` on sections;
   * `homologyMap_laurentSmul_comp_homologyLaurentCechTopIso_hom`: the top iso intertwines it with
     `topSmul m c` on Laurent polynomials with negative exponents;
   * `cohomologyMap_comp_cohomologyIsoHomologyLaurentCech_hom`: Leray's comparison intertwines
     `(cohomologyFunctor _ q).map (globalSectionsSmul …)` with it.
   The missing step is element-level: from the morphism identity
   `Φ.inv ≫ (cohomologyFunctor _ (n+1)).map σ = topSmul m c ≫ Φ.inv`, conclude
   `Φ.inv (c • y) = c • Φ.inv y` via `base_smul_cohomology`/`cohomology_smul`. Both
   `ConcreteCategory.congr_hom key y` and the `comp_apply` route time out at `whnf` here, because
   unifying `ToType ((cohomologyFunctor X q).obj F)` with `Cohomology F q` unfolds `Shrink` /
   `equivShrink`. The fix is probably to state the morphism identity with the objects written as
   `AddCommGrpCat.of (Cohomology F q)` (as `Cohomology/Cech/Linear.lean` does with `change`), or to
   go through `homologyCechComplexLinearEquiv` of `Cohomology/Cech/Linear.lean` with the Laurent
   presheaf upgraded to a presheaf of `R`-modules. Result:
   `Module.Basis.cohomologyTwistingSheafTopLinearEquiv : … ≃ₗ[R] Module.Dual R (𝒜 j)`. To make room,
   split the top-degree section into its own file, de-privatising the Laurent-presheaf API it uses.
2. **The packaged theorem `projectiveSpace_cohomology`**, combining the `≃ₗ[R]` of item 1 with the
   `main` results listed above into one statement for every `q : ℕ` and `d : ℤ` on
   `ℙⁿ⁺¹_R` (`Fintype.card κ = n + 2`): `H⁰(𝒪(j)) ≃ₗ[R] A_j` for `d = j ≥ 0`,
   `Hⁿ⁺¹(𝒪(-j - n - 2)) ≃ₗ[R] (A_j)^∨`, and `Subsingleton` in all other cases.

## Split plan

1. *feat: the top cohomology of the twisting sheaves on projective space* (after: none). File:
   `TauCeti/AlgebraicGeometry/Cohomology/ProjectiveSpace/HigherCohomology.lean` (+~590 lines).
   Adds everything listed under "What this branch proves", including
   `Module.Basis.cohomologyTwistingSheafTopAddEquiv`.
2. *feat: the top cohomology of the twisting sheaves on projective space is linear over the base
   ring* (after: 1). Moves the top-degree section to a new `ProjectiveSpace/TopCohomology.lean`
   (the Laurent-presheaf API of `HigherCohomology.lean` made public), adds the appendix lemmas and
   the last step of item 1 of "What remains", replacing `cohomologyTwistingSheafTopAddEquiv` by
   `cohomologyTwistingSheafTopLinearEquiv` (~300 lines).
3. *feat: the cohomology of the twisting sheaves on projective space in every degree* (after: 1, 2).
   New file `TauCeti/AlgebraicGeometry/Cohomology/ProjectiveSpace/Basic.lean` (~100 lines) with the
   exported theorem `projectiveSpace_cohomology` (item 2 of "What remains"); the only split that
   completes the target.

Roadmap attribution for each split: `Roadmap: SchemeAndStackFoundations`.

## Appendix: proven linearity lemmas (not on the branch)

These compiled, without `sorry`, inside `HigherCohomology.lean` at the positions noted
(they use its private Laurent-presheaf API and need
`import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.GlobalSections`). The four
blocks go, in order: at the end of `section Chart`; in `section Cech` after
`isIso_cechComplexFunctor_map_laurentToSections`; at the end of `section Cech`; and before
`subsingleton_cohomology_twistingSheaf_aux`.

```lean
/-! ### Linearity over the base ring -/

/-- The global function `c` of `Proj (Sym M)` given by an element of the base ring, restricted to
an open `U`. -/
private abbrev baseFunction (c : R) (U : (Proj 𝒜).Opens) : Γ(Proj 𝒜, U) :=
  (Proj 𝒜).presheaf.map U.leTop.op
    (AlgebraicGeometry.Scheme.Modules.baseRingToGlobalSections R (Proj 𝒜) c)

private lemma val_baseFunction_apply (c : R) {U : (Proj 𝒜).Opens} (x : U) :
    ((baseFunction c U).1 x).val =
      Localization.mk (algebraMap R (_root_.SymmetricAlgebra R M) c) 1 :=
  val_baseRingToGlobalSections_apply c ⟨x.1, trivial⟩

private lemma chartSectionHom_smul (S : Finset κ) (e : κ → ℤ) (c r : R) :
    chartSectionHom b m S e (c * r) =
      baseFunction (M := M) c (Proj.basicOpen 𝒜 (coordProd b S)) • chartSectionHom b m S e r := by
  by_cases he : e ∈ chartExponents m S
  · rw [chartSectionHom_apply b he (fun i _ ↦ le_exponentBound e i),
      chartSectionHom_apply b he (fun i _ ↦ le_exponentBound e i)]
    refine Proj.twistingSheaf.ext fun x ↦ Eq.trans ?_ (Proj.twistingSheaf.smul_apply _ _ x).symm
    refine (Proj.twistingSheaf.const_apply _ _ _ _ _ _ x).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (val_baseFunction_apply (M := M) c x).symm
        (Proj.twistingSheaf.const_apply _ _ _ _ _ _ x).symm))
    rw [Localization.mk_mul, mul_smul, Algebra.smul_def c]
    congr 1
    exact Subtype.ext (one_mul _).symm
  · simp [chartSectionHom, he]

private lemma chartSectionsHom_smul (S : Finset κ) (c : R)
    (f : Finsupp.supported R R (chartExponents m S)) :
    chartSectionsHom b m S (c • f) = baseFunction (M := M) c (Proj.basicOpen 𝒜 (coordProd b S)) • chartSectionsHom b m S f := by
  rw [chartSectionsHom_eq_sum, chartSectionsHom_eq_sum]
  change ((c • f.1).sum fun e r ↦ chartSectionHom b m S e r) =
    baseFunction (M := M) c (Proj.basicOpen 𝒜 (coordProd b S)) • (f.1.sum fun e r ↦ chartSectionHom b m S e r)
  rw [Finsupp.sum_smul_index' (fun e ↦ map_zero _), Finsupp.smul_sum]
  exact Finset.sum_congr rfl fun e _ ↦ chartSectionHom_smul b S e c _


-- ----

/-- Multiplication by an element of the base ring on the Laurent polynomials. -/
private def laurentSmul (c : R) :
    laurentPresheaf (R := R) (κ := κ) m ⟶ laurentPresheaf (R := R) (κ := κ) m where
  app _ := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom _ c)
  naturality X Y g := by
    have h : (c • LinearMap.id).comp (Submodule.inclusion (Finsupp.supported_mono (M := R)
        (R := R) (chartExponents_mono (m := m) (leOfHom g.unop)))) =
        (Submodule.inclusion (Finsupp.supported_mono (chartExponents_mono (leOfHom g.unop)))).comp
          (c • LinearMap.id) := by
      rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id]
    exact AddCommGrpCat.hom_ext (congrArg LinearMap.toAddMonoidHom h)

/-- Multiplication by an element of the base ring on the sections of `𝒪(m)`. -/
private abbrev sectionsSmul (c : R) :
    sectionsPresheaf (R := R) (M := M) m ⟶ sectionsPresheaf (R := R) (M := M) m :=
  ((SheafOfModules.toSheaf (Proj 𝒜).ringCatSheaf).map ((Proj.twistingSheaf 𝒜 m).globalSectionsSmul
    (AlgebraicGeometry.Scheme.Modules.baseRingToGlobalSections R (Proj 𝒜) c))).hom

omit [Fintype κ] [DecidableEq κ] in
private lemma sectionsSmul_app_apply (c : R) (U : (Proj 𝒜).Opens)
    (s : Γ(Proj.twistingSheaf 𝒜 m, U)) :
    (sectionsSmul (R := R) (M := M) m c).app (Opposite.op U) s = baseFunction (M := M) c U • s := by
  refine Eq.trans ?_ ((Proj.twistingSheaf 𝒜 m).smul_apply (baseFunction (M := M) c U) s)
  rw [← AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_app]
  rfl

/-- The identification of Laurent polynomials with sections of `𝒪(m)` is linear over the base
ring. -/
private lemma laurentSmul_comp_laurentToSections (c : R) :
    laurentSmul (R := R) (κ := κ) m c ≫ laurentToSections b m =
      laurentToSections b m ≫ Functor.whiskerLeft (chartFunctor b).op (sectionsSmul m c) := by
  ext S f
  exact (chartSectionsHom_smul b (ofDual S.unop) c f).trans
    (sectionsSmul_app_apply m c _ _).symm


-- ----

/-- Multiplication by an element of the base ring on the Laurent polynomials with all exponents
negative. -/
private abbrev topSmul (c : R) :
    AddCommGrpCat.of (Finsupp.supported R R (topExponents (κ := κ) m)) ⟶
      AddCommGrpCat.of (Finsupp.supported R R (topExponents (κ := κ) m)) :=
  AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom _ c)

private lemma laurentSmul_app_comp_topPartHom (c : R) (X : ((Finset κ)ᵒᵈ)ᵒᵖ) :
    (laurentSmul (R := R) m c).app X ≫ topPartHom (R := R) m (ofDual X.unop) =
      topPartHom (R := R) m (ofDual X.unop) ≫ topSmul m c :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ (topPart m _).map_smul c x)

private lemma cechComplexFunctor_map_laurentSmul_comp_evalTop (c : R) :
    ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (laurentSmul (R := R) m c)).f (n + 1) ≫ evalTop m e = evalTop m e ≫ topSmul m c := by
  unfold evalTop
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (cechComplexFunctor_map_f_π _ _ _ _ ⇑e)).trans ?_)
  exact (Category.assoc _ _ _).trans ((congrArg _ (laurentSmul_app_comp_topPartHom m c _)).trans
    (Category.assoc _ _ _).symm)

private lemma cechComplexFunctor_map_laurentSmul_comp_toSingleTop (c : R) :
    (cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (laurentSmul (R := R) m c) ≫ toSingleTop m e =
      toSingleTop m e ≫ (HomologicalComplex.single AddCommGrpCat.{u} (ComplexShape.up ℕ)
        (n + 1)).map (topSmul m c) := by
  ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, toSingleTop,
    HomologicalComplex.mkHomToSingle_f, HomologicalComplex.single_map_f_self,
    Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
    cechComplexFunctor_map_laurentSmul_comp_evalTop, Category.assoc]

private lemma homologyMap_laurentSmul_comp_homologyLaurentCechTopIso_hom (c : R) :
    HomologicalComplex.homologyMap ((cechComplexFunctor fun i : κ ↦
        (toDual {i} : (Finset κ)ᵒᵈ)).map (laurentSmul (R := R) m c)) (n + 1) ≫
        (homologyLaurentCechTopIso m e).hom =
      (homologyLaurentCechTopIso m e).hom ≫ topSmul m c := by
  simp only [homologyLaurentCechTopIso]
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    cechComplexFunctor_map_laurentSmul_comp_toSingleTop, HomologicalComplex.homologyMap_comp,
    Category.assoc, HomologicalComplex.singleObjHomologySelfIso_hom_naturality, Category.assoc]


-- ----
open Limits OrderDual TauCeti.CategoryTheory TauCeti.AlgebraicGeometry.Scheme.Modules in
/-- Leray's comparison for `𝒪(m)` carries multiplication by an element of the base ring to
multiplication of the Laurent polynomials. -/
private lemma cohomologyMap_comp_cohomologyIsoHomologyLaurentCech_hom [Fintype κ] [DecidableEq κ]
    (m : ℤ) (q : ℕ) (c : R) :
    (cohomologyFunctor (Proj 𝒜) q).map ((Proj.twistingSheaf 𝒜 m).globalSectionsSmul
        (AlgebraicGeometry.Scheme.Modules.baseRingToGlobalSections R (Proj 𝒜) c)) ≫
        (cohomologyIsoHomologyLaurentCech b m q).hom =
      (cohomologyIsoHomologyLaurentCech b m q).hom ≫ HomologicalComplex.homologyMap
        ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
          (laurentSmul (R := R) m c)) q := by
  have := isIso_cechComplexFunctor_map_laurentToSections b m
  have h1 := AlgebraicGeometry.Scheme.Modules.homologyMap_comp_homologyCechComplexIsoCohomology_hom
    (fun i : κ ↦ (chartFunctor b).obj (toDual {i}))
    (isAffineOpen_inf_chartFunctor_obj_singleton b) (iSup_chartFunctor_obj_singleton b)
    ((Proj.twistingSheaf 𝒜 m).globalSectionsSmul
      (AlgebraicGeometry.Scheme.Modules.baseRingToGlobalSections R (Proj 𝒜) c)) q
  have hA : (cohomologyFunctor (Proj 𝒜) q).map ((Proj.twistingSheaf 𝒜 m).globalSectionsSmul
        (AlgebraicGeometry.Scheme.Modules.baseRingToGlobalSections R (Proj 𝒜) c)) ≫
        (AlgebraicGeometry.Scheme.Modules.homologyCechComplexIsoCohomology
          (fun i : κ ↦ (chartFunctor b).obj (toDual {i}))
          (isAffineOpen_inf_chartFunctor_obj_singleton b) (iSup_chartFunctor_obj_singleton b)
          (Proj.twistingSheaf 𝒜 m) q).inv =
      (AlgebraicGeometry.Scheme.Modules.homologyCechComplexIsoCohomology
          (fun i : κ ↦ (chartFunctor b).obj (toDual {i}))
          (isAffineOpen_inf_chartFunctor_obj_singleton b) (iSup_chartFunctor_obj_singleton b)
          (Proj.twistingSheaf 𝒜 m) q).inv ≫
        HomologicalComplex.homologyMap ((cechComplexFunctor fun i : κ ↦
          (chartFunctor b).obj (toDual {i})).map (sectionsSmul (M := M) m c)) q :=
    (Iso.comp_inv_eq _).2 (((Category.assoc _ _ _).trans (congrArg _ h1)).trans
      (Iso.inv_hom_id_assoc _ _)).symm
  have hS := (((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map_comp _ _).symm.trans
      ((congrArg (cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (laurentSmul_comp_laurentToSections b m c)).trans
        ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map_comp _ _)))
  have hC : (cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (Functor.whiskerLeft (chartFunctor b).op (sectionsSmul m c)) ≫
        inv ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
          (laurentToSections b m)) =
      inv ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
          (laurentToSections b m)) ≫
        (cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
          (laurentSmul (R := R) m c) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← hS, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hB := (HomologicalComplex.homologyMap_comp _ _ q).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · q)
      (cechComplexFunctor_map_comp_cechComplexCompIso_hom (chartFunctor b)
        (fun i : κ ↦ toDual {i}) (sectionsPresheaf (R := R) (M := M) m)
        (nonempty_pi_chartFunctor_obj_hom b) (sectionsSmul (M := M) m c))).trans (HomologicalComplex.homologyMap_comp _ _ q))
  have hC' := (HomologicalComplex.homologyMap_comp _ _ q).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · q) hC).trans
      (HomologicalComplex.homologyMap_comp _ _ q))
  simp only [cohomologyIsoHomologyLaurentCech, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyMapIso_inv, asIso_inv,
    Category.assoc]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hA).trans ((Category.assoc _ _ _).trans
    (congrArg _ ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hB).trans
      ((Category.assoc _ _ _).trans (congrArg _ hC')))))))
```
