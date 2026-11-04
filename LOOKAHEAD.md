<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"relative-proj-base-change","main":"7ed979dc2eacd36a3962e1fdf3b481323fb3fb8b","status":"partial","suppliers":["relative-proj-twisting-sheaf"],"splits":[{"n":1,"after":[],"title":"feat: pullback of graded quasicoherent algebras"},{"n":2,"after":[1],"title":"feat: pullback of sections of a graded quasicoherent algebra as a graded ring map"},{"n":3,"after":[2],"title":"feat: affine base change of the graded sections of a pulled-back graded algebra"},{"n":4,"after":[3],"title":"feat: the relative Proj of a pulled-back graded algebra is the base change"},{"n":5,"after":[],"title":"feat: lift into a glued module from a covering family of charts"},{"n":6,"after":[4,5],"title":"feat: compare the twisting sheaves of the relative Proj of a pulled-back graded algebra"},{"n":7,"after":[],"title":"feat: base change of the sections of twisting sheaves over standard opens"},{"n":8,"after":[7],"title":"feat: twisting sheaves pull back along base changes of graded rings"},{"n":9,"after":[1,2,3,4,5,6,7,8],"title":"feat: base change of the relative Proj, compatibly with O(n)"}]}-->

# Lookahead: `relative-proj-base-change` (SchemeAndStackFoundations, Layer 0, §0.3)

Target (README §0.3): *Prove `relativeProj_baseChange`: formation of `relativeProj` commutes with
arbitrary base change `g : S' → S`, with degree-zero part `g^* A_0`, compatibly with `O(n)`
(Stacks, Lemma 27.16.10 (01O3)).* The README states that the relative Proj and its comparisons are
specified in the README only; `Suggested.lean` pins only `Proj.isPullback_baseChange`, which is
already on `main` (`AlgebraicGeometry.Proj.isPullback_baseChange`,
`Proj.isPullback_map_of_isBaseChange` in `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/BaseChange.lean`).

Built on `main` at `7ed979dc2eacd36a3962e1fdf3b481323fb3fb8b` (merged into the branch on
2026-11-04). Status: **partial** — splits 1–8 proved, sorry-free; split 9 is partly written, and
everything it still needs is mathematically settled (see *What remains*: two declarations whose
elaborated proofs hit kernel deterministic timeouts, plus the export).

## Stubs

`TauCeti/Lookahead/RelativeProjBaseChange/Stubs.lean` states **no declaration**.

The supplier `relative-proj-twisting-sheaf` has already landed, on `main`, everything the target
consumes: the relative Proj (`CategoryTheory.CommMon.relativeProj`, #19831), its twisting sheaves
`𝒪(n)` (`CategoryTheory.CommMon.relativeProjTwistingSheaf`, #22384) with their chart
identification `restrictRelativeProjTwistingSheafIso` / `ModulesGlueData.restrictGluedHom`, and
invertibility in degree one (#23564). The open supplier PR #27145 adds the multiplication
`CategoryTheory.CommMon.relativeProjTwistingSheafMul` and
`relativeProjTwistingSheafTensorProductIso`; the README milestone still owes the graded map
`A → ⊕_{n ≥ 0} (relativeProj.toBase)_* O(n)` (Stacks 01NR), which no PR or `Suggested.lean` pins.
None of these is consumed: "compatibly with `O(n)`" is proved as the isomorphism
`h^* 𝒪_A(n) ≅ 𝒪_{g^* A}(n)` for every `n ∈ ℤ`. If a reviewer reads the target as also requiring
compatibility with the multiplication maps, the next session should stub
`relativeProjTwistingSheafMul` and its two characterising lemmas from PR #27145's diff
(`TauCeti/AlgebraicGeometry/RelativeProj/TwistingSheaf/TensorProduct.lean`) verbatim in the stub
file. No `Suggested.lean` signature exists for any of them (relative Proj is README-only).

**Overlap with open PR #27468** (another author, not a supplier): it adds
`AlgebraicGeometry.Proj.pullbackTwistingSheafMap` (same definition as split 8's, same name on
purpose), `Scheme.Modules.Hom.bijective_app_of_le` and `Scheme.Modules.Hom.isIso_of_bijective_app`
(same statements as split 8's additions to `Modules/AffineRestriction.lean`), and proves the
isomorphism only for algebras generated in degree one. If #27468 lands first, split 8 must delete
its copies of these four declarations and reuse #27468's, keeping
`pullbackTwistingSheafMap_eq`, the degreewise base-change criterion and the two `isIso_…` theorems
(which drop the degree-one assumption).

## Splits

1. **`feat: pullback of graded quasicoherent algebras`** — after: none.
   File `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/GradedAlgebra/Pullback.lean` (230 lines).
   Adds, in `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra`: `pullbackMul`, `pullbackOne`,
   `pullbackOne_mul`, `pullbackMul_one`, `pullbackMul_assoc`, `pullbackMul_comm`, `pullback`
   (`g^* A`, `@[expose]` so that its components are definitionally `g^* Aₙ`), `pullback_obj_X`
   (degree `n` part is `g^* Aₙ`; in particular degree zero is `g^* A₀`), `mul_pullback`,
   `one_pullback`. The laws are transported along the strong symmetric monoidal pullback
   `ι ⋙ Scheme.Modules.pullback g` with `GradedObject.*_of_laxMonoidal`.
2. **`feat: pullback of sections of a graded quasicoherent algebra as a graded ring map`** — after: 1.
   File `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/GradedAlgebra/PullbackSections.lean`
   (310 lines). Adds `AlgebraicGeometry.Scheme.Hom.δ_app_pullbackSections`,
   `Scheme.Hom.δ_app_pullbackSectionsLE`, `Scheme.Hom.η_app_pullbackSectionsLE` (pullback of
   sections vs. the oplax comparisons of pullback), and in `GradedQuasicoherentAlgebra`:
   `pullbackSectionsLE_gAlgebraToFun`, `pullbackSectionsLE_gOne`, `pullbackSectionsLE_gMul`,
   `pullbackGradedSections` (`⨁ Γ(Aₙ, U) →+* ⨁ Γ(g^* Aₙ, V)` for `V ≤ g⁻¹ U`),
   `pullbackGradedSections_of`, `pullbackGradedSections_algebraMap` (over `g.appLE U V`),
   `restrictGradedSections_comp_pullbackGradedSections`,
   `pullbackGradedSections_comp_restrictGradedSections` (compatibility with restriction on both
   sides, the input for gluing in split 4), `pullbackGradedSectionsGradedHom` (+ `_toRingHom`,
   `_apply`).
3. **`feat: affine base change of the graded sections of a pulled-back graded algebra`** — after: 2.
   *Written this session.* Files:
   - `TauCeti/AlgebraicGeometry/Modules/Pullback/BaseChange.lean` (existing file, +109 lines, now
     639): `AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackSectionsLE` — for affine opens `U` of
     `X` and `V ≤ g⁻¹ U` of `Y`, `pullbackSectionsLE` exhibits `Γ(V, g^* M)` as the base change
     `Γ(Y, V) ⊗[Γ(X, U)] Γ(U, M)` along `g.appLE U V hV` (the `Γ(X, U)`-module structure and the
     linear map are caller parameters, in the style of `isBaseChange_pullbackSections`), with
     private helpers `fromSpec_comp_preimage_eq_top`, `fromSpec_comp_preimage_le`,
     `bijective_fromSpec_pullbackSectionsLE`. Proof: compare with `pullbackSectionsEquiv` for
     `hV.fromSpec ≫ g`, whose preimage of `U` is the whole chart, through the file's private
     `chartPullback_unit` (which is why it lives in this file) and `pullbackSectionsLE_comp_hom`.
     This part needs neither split 1 nor 2 and could be opened on its own if a reviewer asks
     for it.
   - `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/GradedAlgebra/PullbackBaseChange.lean`
     (new, 155 lines), in `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra`:
     `algebraPullbackGradedSections` (the `Γ(Y, U)`-algebra structure on `⨁ Γ(g^* Aₙ, V)` through
     `g.appLE`), `pullbackGradedSectionsGradedHom_algebraMap`,
     `isScalarTower_pullbackGradedSections`, `isBaseChange_pullbackGradedSections` (degreewise via
     Mathlib's `IsBaseChange.directSum`), `irrelevant_le_map_pullbackGradedSectionsGradedHom`, and
     `isPullback_proj_pullbackGradedSections`: the square
     `Proj (⨁ Γ(g^* Aₙ, V)) ⟶ Proj (⨁ Γ(Aₙ, U))` over `Spec Γ(X, V) ⟶ Spec Γ(Y, U)` is cartesian
     (via `Proj.isPullback_map_of_isBaseChange`).
4. **`feat: the relative Proj of a pulled-back graded algebra is the base change`** — after: 3.
   *Proved.* Files:
   - `TauCeti/AlgebraicGeometry/RelativeProj/Basic.lean` (existing file, +12 lines):
     `CategoryTheory.CommMon.isPullback_relativeProjCover_fromSpec` (the chart square of
     `isPullback_relativeProjCover` restated along `U.2.fromSpec : Spec Γ(X, U) ⟶ X`).
   - `TauCeti/AlgebraicGeometry/RelativeProj/BaseChange.lean` (new, 291 lines), in
     `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra`:
     `restrictGradedSectionsGradedHom_comp_pullbackGradedSectionsGradedHom`,
     `pullbackGradedSectionsGradedHom_comp_restrictGradedSectionsGradedHom`,
     `relativeProjGluingData_functor_map_comp_proj_map`,
     `proj_map_comp_relativeProjGluingData_functor_map`,
     `relativeProjGluingData_functor_map_comp_proj_map_comp_relativeProjCover_f` (all
     `@[reassoc]` where morphisms are composed), `relativeProjPullbackCover` (the open cover of
     `Proj_X(g^* A)` by its charts over the pairs `(V, U)` of affine opens with `V ≤ g⁻¹ U`, via
     `Cover.mkOfCovers`) with its `Preorder` index and `LocallyDirected` instances (directedness:
     shrink the common chart given by the relative `Proj` of `g^* A` to a basic open lying over a
     common basic open of the two `U`s, by `exists_basicOpen_le_affine_inter` and
     `IsAffineOpen.exists_basicOpen_le`), `relativeProjPullbackHom : Proj_X(g^* A) ⟶ Proj_Y(A)`
     (by `glueMorphismsOfLocallyDirected`), `relativeProjCover_f_relativeProjPullbackHom`,
     `relativeProjPullbackHom_relativeProjToBase` (it lies over `g`), and
     `isPullback_relativeProjPullbackHom`: `IsPullback (g^* A).relativeProjToBase
     (relativeProjPullbackHom g A) g A.relativeProjToBase`, by `Scheme.isPullback_of_openCover`
     over the cover of `X` by `Spec Γ(X, V)` for the same pairs, pasting the chart squares with
     `isPullback_proj_pullbackGradedSections`. Uses no stub.
5. **`feat: lift into a glued module from a covering family of charts`** — after: none.
   *Written this session.* File `TauCeti/AlgebraicGeometry/Modules/Gluing.lean` (existing file,
   +217 lines, now 585). Adds, in `TauCeti.ModulesGlueData`:
   `eq_of_transition_app_eq_of_le_cover` (sections of `(ιⱼ)_* Mⱼ` over any open are determined by
   their transitions along a downward closed set of indices whose images cover the image of
   `F j`), `eq_of_transition_app_eq_of_cover`, `exists_transition_app_eq_of_cover` (a compatible
   family over a downward closed covering set `J'` extends to every index), `extendOfCover`,
   `extendOfCover_transition`, `extendOfCover_of_mem`, `extendOfCover_comp_transition`,
   `liftOfCover` (a morphism into the glued module from compatible morphisms
   `M ⟶ (ιₖ)_* Mₖ`, `k ∈ J'`) and `liftOfCover_π`, with private helpers
   `exists_transition_app_eq_hom`, `extendApp` (+ `_zero`, `_add`, `_smul`, `_map`,
   `transition_app_extendApp`). Purely about gluing data; independent of splits 1–4. Needed
   because a morphism out of `h^* 𝒪(n)` is only available on the charts over affine opens `V`
   lying over a single affine open of the base.
6. **`feat: compare the twisting sheaves of the relative Proj of a pulled-back graded algebra`** —
   after: 4, 5. *Written this session.* Files:
   - `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/Functor.lean` (existing file,
     +16 lines): `AlgebraicGeometry.Proj.twistingSheafMap_app_apply_res_of_eq_comp` (the
     composition law of `twistingSheafMap` for sections restricted to opens only propositionally
     equal to preimages; it must live in this file, where `twistingSheaf.comap` unfolds).
   - `TauCeti/AlgebraicGeometry/RelativeProj/BaseChangeTwistingSheaf.lean` (new, 306 lines), in
     `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra`: `relativeProjTwistingSheafChartHom`
     (`𝒪_A(n) ⟶ h_* (ι_V)_* 𝒪(n)` over `V ≤ g⁻¹ U`, from the projection of the glued sheaf and
     `Proj.twistingSheafMap` of the pullback of sections), `_app_apply`, `_eq_of_le` (change of `U`
     to a basic open), `_comp_transition` (change of `V`), `relativeProjTwistingSheafChartHom_eq`
     (independence of `U`, via `eq_of_transition_app_eq_of_le_cover` over the charts lying over
     common basic opens), `pullbackRelativeProjTwistingSheafChartHom` (+ `_eq`,
     `_comp_transition`), `exists_mem_opensRange_relativeProjCover_f`,
     `relativeProjPullbackTwistingSheafHom : h^* 𝒪_A(n) ⟶ 𝒪_{g^* A}(n)` (by `liftOfCover`) and
     `relativeProjPullbackTwistingSheafHom_π` (its value on charts). Uses no stub.
     Elaboration notes for the port: pass `pushforwardComp`/`pushforwardCongr` arguments
     explicitly, state sections of `h_* M` over `W` as `let`s over `h⁻¹ W` before handing them to
     gluing lemmas, chain with `Eq.trans`/`congrArg` instead of `rw` on sections, and give the
     implicit opens of `twistingSheafMap_app_apply_res_of_eq_comp` by name; otherwise `whnf`
     times out. The file takes several minutes to elaborate.
7. **`feat: base change of the sections of twisting sheaves over standard opens`** — after: none.
   *Written this session.* File
   `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/BaseChange.lean` (new, 349 lines).
   Adds `AlgebraicGeometry.Proj.twistingSheaf.isBaseChange_comap_basicOpen`: for a graded ring
   homomorphism `f : 𝒜 →+*ᵍ ℬ` over `R → S` which is a base change in every degree (components
   `φ j : 𝒜ⱼ →ₗ[R] ℬⱼ` with `IsBaseChange S (φ j)`), and `a ∈ 𝒜_d`, `d > 0`, pulling back sections
   `Γ(D₊(a), 𝒪(n)) → Γ(D₊(f a), 𝒪(n))` is a base change along `Γ(D₊(a), 𝒪) → Γ(D₊(f a), 𝒪)`, for
   every `n ∈ ℤ` (the module structure, algebra and linear map are caller parameters, as in
   `Scheme.Hom.isBaseChange_pullbackSectionsLE`). Private helpers: `fracPow`, `fracPowHom`, `coeff`,
   `frac0`, `theta` (the elements `∑ s ⊗ r / aᵏ`), `mulPow`, `mulRight`, `exists_eq_theta` (common
   denominators), `theta_mulPow`, `liftBaseChange_theta`, `coe_liftBaseChange_mulPow`, … The proof
   is the degree-`n` analogue of `HomogeneousLocalization.Away.baseChangeEquiv`, via
   `exists_eq_const_basicOpen` and `const_eq_zero_iff`; it needs no degree-one generation.
8. **`feat: twisting sheaves pull back along base changes of graded rings`** — after: 7.
   *Written this session.* Files:
   - `TauCeti/AlgebraicGeometry/Modules/AffineRestriction.lean` (existing, +69 lines):
     `Scheme.Modules.Hom.bijective_app_of_le` and `Scheme.Modules.Hom.isIso_of_bijective_app`
     (isomorphisms of quasi-coherent modules are detected on an affine open cover).
   - `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/PullbackBaseChange.lean` (new,
     239 lines): `Proj.pullbackTwistingSheafMap` (`(Proj.map f)^* 𝒪(n) ⟶ 𝒪(n)`, adjoint to
     `twistingSheafMap`), `pullbackTwistingSheafMap_eq`,
     `pullbackTwistingSheafMap_app_pullbackSectionsLE`,
     `bijective_pullbackTwistingSheafMap_app_basicOpen`,
     `isIso_pullbackTwistingSheafMap_of_forall_isBaseChange` (degreewise base change) and
     `isIso_pullbackTwistingSheafMap_of_isBaseChange` (the hypotheses of
     `Proj.isPullback_map_of_isBaseChange`; private `componentLinearMap` and
     `isBaseChange_componentLinearMap` derive the degreewise statement from it).
9. **`feat: base change of the relative Proj, compatibly with O(n)`** — after: 1–8. The only split
   that completes the target. Files:
   - `TauCeti/AlgebraicGeometry/Modules/Gluing.lean` (+7 lines, written):
     `TauCeti.ModulesGlueData.restrictGluedHom_eq` (the definition is not exposed).
   - `TauCeti/AlgebraicGeometry/Modules/Restriction/Cover.lean` (new, 64 lines, written):
     `Scheme.Modules.Hom.isIso_of_isIso_restrictFunctor_map` (isomorphisms of modules are local on
     a jointly surjective family of open immersions, e.g. the charts of a glued scheme).
   - `TauCeti/CategoryTheory/Adjunction/HomEquiv.lean` (new, 63 lines, written):
     `Adjunction.comp_homEquiv_symm_comp_map`, `Adjunction.isIso_homEquiv_symm_comp_hom_app`.
   - `TauCeti/AlgebraicGeometry/RelativeProj/BaseChangeTwistingSheafIso.lean` (new, 134 lines so
     far): written and checked: `GradedQuasicoherentAlgebra.isIso_pullbackTwistingSheafMap_pullbackGradedSectionsGradedHom`
     (the chart comparison of twisting sheaves is an isomorphism), private
     `chartPushforwardIso` (`Proj.map ≫ ι_U = ι_V ≫ h` on pushforwards),
     `relativeProjTwistingSheafChartHom_eq_comp`, `isIso_homEquiv_symm_π_comp_map`. Still to add:
     `isIso_restrictFunctor_map_relativeProjPullbackTwistingSheafHom`, the instance
     `isIso_relativeProjPullbackTwistingSheafHom`, `relativeProjPullbackTwistingSheafIso` (+ `_hom`)
     and the export `GradedQuasicoherentAlgebra.relativeProj_baseChange` (`@[stacks 01O3]`).
   Expected size once finished: about 400 lines.

## What is proved and what remains

Proved (sorry-free, building on `main`): `g^* A` with degree-zero part `g^* A₀` (split 1); graded
maps of sections (2); affine base change of sections and the cartesian chart squares (3); the
cartesian square `isPullback_relativeProjPullbackHom` (4); gluing into a glued module (5); the
comparison `relativeProjPullbackTwistingSheafHom g A n : h^* 𝒪_A(n) ⟶ 𝒪_{g^* A}(n)` (6); the
degree-`n` affine base change of sections of twisting sheaves (7); the isomorphism
`(Proj.map f)^* 𝒪(n) ≅ 𝒪(n)` for any base change of graded rings, in all degrees and without
degree-one generation (8); and, in split 9, the isomorphism on the charts and the invertibility of
the transpose of the chart comparison along `ι_U` then `Proj.map`.

Remains (split 9 only): deduce that `relativeProjPullbackTwistingSheafHom` is an isomorphism and
export. The argument is complete and elaborates; only the kernel check of the last two lemmas
timed out (`(kernel) deterministic timeout`, each run about 9 minutes). The attempted code, which
the elaborator accepts:

```lean
/-- The transpose of the chart comparison, along `h` and then the chart `ι_V`, is an
isomorphism. -/
private theorem isIso_homEquiv_symm_relativeProjTwistingSheafChartHom {V : X.AffineZariskiSite}
    {U : Y.AffineZariskiSite} (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    IsIso (((Scheme.Modules.restrictAdjunction
      ((pullback g A).obj.relativeProjCover.f V)).homEquiv _ _).symm
        (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProjPullbackHom g A)).homEquiv
          _ _).symm (A.relativeProjTwistingSheafChartHom g n hV))) := by
  have hfin := Adjunction.isIso_homEquiv_symm_comp_hom_app
    ((Scheme.Modules.pullbackPushforwardAdjunction (relativeProjPullbackHom g A)).comp
      (Scheme.Modules.restrictAdjunction ((pullback g A).obj.relativeProjCover.f V)))
    ((Scheme.Modules.restrictAdjunction (A.obj.relativeProjCover.f U)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction _)) (chartPushforwardIso hV) _
    (hχ := isIso_homEquiv_symm_π_comp_map g A n hV)
  simp only [Adjunction.comp_homEquiv, Equiv.symm_trans_apply] at hfin
  rw [relativeProjTwistingSheafChartHom_eq_comp]
  exact hfin

/-- Over the chart of an affine open `V ≤ g⁻¹ U`, the comparison of twisting sheaves
`h^* 𝒪_A(n) ⟶ 𝒪_{g^* A}(n)` restricts to an isomorphism. -/
theorem isIso_restrictFunctor_map_relativeProjPullbackTwistingSheafHom {V : X.AffineZariskiSite}
    {U : Y.AffineZariskiSite} (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    IsIso ((Scheme.Modules.restrictFunctor ((pullback g A).obj.relativeProjCover.f V)).map
      (relativeProjPullbackTwistingSheafHom g A n)) := by
  let D' := (pullback g A).obj.relativeProjTwistingSheafGlueData n
  have hD' : IsIso (D'.restrictGluedHom V) :=
    D'.isIso_restrictGluedHom ((pullback g A).obj.bijective_relativeProjTwistingSheafGlueData_map_app
      n) V
  -- the restriction followed by the chart identification is the transpose of the chart comparison
  have h₁ : (Scheme.Modules.restrictFunctor ((pullback g A).obj.relativeProjCover.f V)).map
        (relativeProjPullbackTwistingSheafHom g A n) ≫ D'.restrictGluedHom V =
      ((Scheme.Modules.restrictAdjunction ((pullback g A).obj.relativeProjCover.f V)).homEquiv
        _ _).symm (((Scheme.Modules.pullbackPushforwardAdjunction _).homEquiv _ _).symm
          (A.relativeProjTwistingSheafChartHom g n hV)) := by
    rw [D'.restrictGluedHom_eq]
    exact (Adjunction.homEquiv_naturality_left_symm _ _ _).symm.trans (congrArg _
      (relativeProjPullbackTwistingSheafHom_π g A n hV))
  have : IsIso ((Scheme.Modules.restrictFunctor ((pullback g A).obj.relativeProjCover.f V)).map
      (relativeProjPullbackTwistingSheafHom g A n) ≫ D'.restrictGluedHom V) := by
    rw [h₁]
    exact isIso_homEquiv_symm_relativeProjTwistingSheafChartHom g A n hV
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (D'.restrictGluedHom V) hD' this

/-- **The twisting sheaves of a relative `Proj` are compatible with base change**: for the
projection `h : Proj_X(g^* A) ⟶ Proj_Y(A)`, the comparison `h^* 𝒪_A(n) ⟶ 𝒪_{g^* A}(n)` is an
isomorphism, for every `n ∈ ℤ`. It is so on every chart of `Proj_X(g^* A)` over an affine open
`V ≤ g⁻¹ U`, where it is the comparison of the twisting sheaves of the charts. -/
instance isIso_relativeProjPullbackTwistingSheafHom :
    IsIso (relativeProjPullbackTwistingSheafHom g A n) :=
  Scheme.Modules.Hom.isIso_of_isIso_restrictFunctor_map _
    (ι := {V : X.AffineZariskiSite // ∃ U : Y.AffineZariskiSite, V.toOpens ≤ g ⁻¹ᵁ U.toOpens})
    (fun V ↦ (pullback g A).obj.relativeProjCover.f V.1)
    (fun x ↦ (exists_mem_opensRange_relativeProjCover_f g A x).elim fun V ⟨hV, hx⟩ ↦ ⟨⟨V, hV⟩, hx⟩)
    fun ⟨_, _, hV⟩ ↦ isIso_restrictFunctor_map_relativeProjPullbackTwistingSheafHom g A n hV

/-- The isomorphism `h^* 𝒪_A(n) ≅ 𝒪_{g^* A}(n)` of twisting sheaves along the projection
`h : Proj_X(g^* A) ⟶ Proj_Y(A)` of the base change of a relative `Proj`. -/
noncomputable def relativeProjPullbackTwistingSheafIso :
    (Scheme.Modules.pullback (relativeProjPullbackHom g A)).obj
        (A.obj.relativeProjTwistingSheaf n) ≅
      (pullback g A).obj.relativeProjTwistingSheaf n :=
  asIso (relativeProjPullbackTwistingSheafHom g A n)
```

followed by

```lean
/-- The isomorphism `relativeProjPullbackTwistingSheafIso` is the comparison of twisting sheaves. -/
@[simp]
theorem relativeProjPullbackTwistingSheafIso_hom :
    (relativeProjPullbackTwistingSheafIso g A n).hom = relativeProjPullbackTwistingSheafHom g A n :=
  (rfl)

/-- **Base change of the relative `Proj`.** For a morphism of schemes `g : X ⟶ Y` and a graded
quasicoherent algebra `A` on `Y`, the relative `Proj` of the pulled-back graded algebra `g^* A`,
whose homogeneous components, in particular its degree-zero part, are the pullbacks `g^* Aₖ`, is
the base change of the relative `Proj` of `A` along `g`, through the projection
`h = relativeProjPullbackHom g A`; and `h` pulls the twisting sheaves `𝒪_A(n)` back to the twisting
sheaves `𝒪_{g^* A}(n)` (`relativeProjPullbackTwistingSheafIso`), for every `n ∈ ℤ`. -/
@[stacks 01O3]
theorem relativeProj_baseChange :
    IsPullback (pullback g A).obj.relativeProjToBase (relativeProjPullbackHom g A) g
        A.obj.relativeProjToBase ∧
      (∀ k, (pullback g A).obj.X k = (Scheme.Modules.pullback g).obj (A.obj.X k)) ∧
      ∀ n : ℤ, IsIso (relativeProjPullbackTwistingSheafHom g A n) :=
  ⟨isPullback_relativeProjPullbackHom g A, pullback_obj_X g A, fun _ ↦ inferInstance⟩
```

and the export

```lean
@[stacks 01O3]
theorem relativeProj_baseChange :
    IsPullback (pullback g A).obj.relativeProjToBase (relativeProjPullbackHom g A) g
        A.obj.relativeProjToBase ∧
      (∀ k, (pullback g A).obj.X k = (Scheme.Modules.pullback g).obj (A.obj.X k)) ∧
      ∀ n : ℤ, IsIso (relativeProjPullbackTwistingSheafHom g A n) :=
  ⟨isPullback_relativeProjPullbackHom g A, pullback_obj_X g A, fun _ ↦ inferInstance⟩
```

Suggestions for the kernel timeouts: the kernel is unfolding the glued objects (`D'.obj V`,
`colimit.ι F V` versus `relativeProjCover.f V`, `D.glued` versus `relativeProjTwistingSheaf n`) when
checking `exact hfin` (after `simp only … at hfin`) and the `rw [h₁]`/`IsIso.of_isIso_comp_right`
step. State every intermediate morphism with the same explicit objects as the goal (as
`isIso_homEquiv_symm_π_comp_map` does with `homEquiv D.glued (D.obj U)` and
`homEquiv (D.obj U) _`, which made it pass), use `(congrArg IsIso e).mpr` instead of `rw`/`simp at`,
and keep each declaration small: a single morphism-level `(rfl)` lemma for
`relativeProjTwistingSheafChartHom` itself also times out in the kernel, while the section-level
`relativeProjTwistingSheafChartHom_app_apply` passes, which is why
`relativeProjTwistingSheafChartHom_eq_comp` is proved on sections.

A second variant, stating the chart lemma directly for the composite adjunction
`(pullbackPushforwardAdjunction h).comp (restrictAdjunction ι_V)` (so that `exact` meets the
conclusion of `Adjunction.isIso_homEquiv_symm_comp_hom_app` without `simp at`), and deriving the
restriction statement through `(congrArg IsIso h₁).mpr` with
`rw [D'.restrictGluedHom_eq, Adjunction.comp_homEquiv, Equiv.symm_trans_apply]` in `h₁`, elaborates
too but still times out in the kernel on both declarations. The next attempt should first find which
defeq the kernel is unfolding (for instance by checking `h₁` and the `exact` separately as
standalone lemmas), and if needed add `@[expose]`-free characterising lemmas in
`RelativeProj/BaseChangeTwistingSheaf.lean` stated with the glue-data objects `D.glued`, `D.obj U`
rather than `relativeProjTwistingSheaf n` and `Proj.twistingSheaf …`.
