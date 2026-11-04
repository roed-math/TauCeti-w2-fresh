<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"relative-proj-base-change","main":"52f9d081237dadaf6d4eae13629281f7faa37d54","status":"partial","suppliers":["relative-proj-twisting-sheaf"],"splits":[{"n":1,"after":[],"title":"feat: pullback of sections of a graded quasicoherent algebra as a graded ring map"},{"n":2,"after":[1],"title":"feat: affine base change of the graded sections of a pulled-back graded algebra"},{"n":3,"after":[2],"title":"feat: the relative Proj of a pulled-back graded algebra is the base change"},{"n":4,"after":[],"title":"feat: lift into a glued module from a covering family of charts"},{"n":5,"after":[3,4],"title":"feat: compare the twisting sheaves of the relative Proj of a pulled-back graded algebra"},{"n":6,"after":[],"title":"feat: base change of the sections of twisting sheaves over standard opens"},{"n":7,"after":[6],"title":"feat: twisting sheaves pull back along base changes of graded rings"},{"n":8,"after":[1,2,3,4,5,6,7],"title":"feat: base change of the relative Proj, compatibly with O(n)"}]}-->

# Lookahead: `relative-proj-base-change` (SchemeAndStackFoundations, Layer 0, §0.3)

Target (README §0.3): *Prove `relativeProj_baseChange`: formation of `relativeProj` commutes with
arbitrary base change `g : S' → S`, with degree-zero part `g^* A_0`, compatibly with `O(n)`
(Stacks, Lemma 27.16.10 (01O3)).* The README states that the relative Proj and its comparisons are
specified in the README only; `Suggested.lean` pins only `Proj.isPullback_baseChange`, which is
already on `main` (`AlgebraicGeometry.Proj.isPullback_baseChange`,
`Proj.isPullback_map_of_isBaseChange` in `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/BaseChange.lean`).

Built on `main` at `52f9d081237dadaf6d4eae13629281f7faa37d54` (merged into the branch on 2026-11-04;
the merge needed no change to the branch's files).
Status: **partial** — splits 1–7 proved, sorry-free; split 8 has every input of its final step
proved and checked, and the abstract criterion that combines them, but the kernel times out on the
single application of that criterion (see *What remains*).

## Changes since the previous session (tip `e615e1f23491`)

No new Lean on the branch: `origin/main` was merged (clean) and the remaining kernel timeout of
split 8 was **located** by staged scratch experiments; see *What remains* for the diagnosis and the
fix that is half-way validated.

## Stubs

`TauCeti/Lookahead/RelativeProjBaseChange/Stubs.lean` states **no declaration**.

The supplier `relative-proj-twisting-sheaf` has already landed, on `main`, everything the target
consumes: the relative Proj (`CategoryTheory.CommMon.relativeProj`, #19831), its twisting sheaves
`𝒪(n)` (`CategoryTheory.CommMon.relativeProjTwistingSheaf`, #22384) with their chart
identification (`ModulesGlueData.restrictGluedHom`, `isIso_restrictGluedHom`), and invertibility
in degree one (#23564). The open supplier PR #27145 adds the multiplication
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
`AlgebraicGeometry.Proj.pullbackTwistingSheafMap` (same definition as split 7's, same name on
purpose), `Scheme.Modules.Hom.bijective_app_of_le` and `Scheme.Modules.Hom.isIso_of_bijective_app`
(same statements as split 7's additions to `Modules/AffineRestriction.lean`), and proves the
isomorphism only for algebras generated in degree one. If #27468 lands first, split 7 must delete
its copies of these four declarations and reuse #27468's, keeping
`pullbackTwistingSheafMap_eq`, the degreewise base-change criterion and the two `isIso_…` theorems
(which drop the degree-one assumption).

## Splits

1. **`feat: pullback of sections of a graded quasicoherent algebra as a graded ring map`** — after:
   none (builds on `main`'s `GradedQuasicoherentAlgebra.pullback`, #25225).
   File `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/GradedAlgebra/PullbackSections.lean`
   (348 lines). Adds `AlgebraicGeometry.Scheme.Hom.δ_app_pullbackSections`,
   `Scheme.Hom.δ_app_pullbackSectionsLE`, `Scheme.Hom.η_app_pullbackSectionsLE` (pullback of
   sections vs. the oplax comparisons of pullback), and in
   `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra`: `pullbackComponentSections` (+ `_apply`,
   `_gAlgebraToFun`, `_gOne`, `_gMul`), `pullbackGradedSections`
   (`⨁ Γ(Aₙ, U) →+* ⨁ Γ((g^* A)ₙ, V)` for `V ≤ g⁻¹ U`), `pullbackGradedSections_of`,
   `pullbackGradedSections_algebraMap` (over `g.appLE U V hV`),
   `restrictGradedSections_comp_pullbackGradedSections`,
   `pullbackGradedSections_comp_restrictGradedSections`, `pullbackGradedSectionsGradedHom`
   (+ `_toRingHom`, `_apply`).
2. **`feat: affine base change of the graded sections of a pulled-back graded algebra`** — after: 1.
   Files: `TauCeti/AlgebraicGeometry/Modules/Pullback/BaseChange.lean` (existing, +109 lines):
   `AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackSectionsLE` (for affine `U` and `V ≤ g⁻¹ U`,
   `Γ(V, g^* M) = Γ(Y, V) ⊗[Γ(X, U)] Γ(U, M)`), private helpers `fromSpec_comp_preimage_eq_top`,
   `fromSpec_comp_preimage_le`, `bijective_fromSpec_pullbackSectionsLE` (this part needs no
   other split and could be opened alone);
   `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/GradedAlgebra/PullbackBaseChange.lean` (new,
   171 lines): `algebraPullbackGradedSections`, `pullbackGradedSectionsGradedHom_algebraMap`,
   `isScalarTower_pullbackGradedSections`, private `isBaseChange_eqToHom_app_pullbackSectionsLE`,
   `isBaseChange_pullbackGradedSections`, `irrelevant_le_map_pullbackGradedSectionsGradedHom`,
   `isPullback_proj_pullbackGradedSections` (the chart squares are cartesian).
3. **`feat: the relative Proj of a pulled-back graded algebra is the base change`** — after: 2.
   Files: `TauCeti/AlgebraicGeometry/RelativeProj/Basic.lean` (existing, +12 lines):
   `CategoryTheory.CommMon.isPullback_relativeProjCover_fromSpec`;
   `TauCeti/AlgebraicGeometry/RelativeProj/BaseChange.lean` (new, 292 lines):
   `restrictGradedSectionsGradedHom_comp_pullbackGradedSectionsGradedHom`,
   `pullbackGradedSectionsGradedHom_comp_restrictGradedSectionsGradedHom`,
   `relativeProjGluingData_functor_map_comp_proj_map`,
   `proj_map_comp_relativeProjGluingData_functor_map`,
   `relativeProjGluingData_functor_map_comp_proj_map_comp_relativeProjCover_f`,
   `relativeProjPullbackCover` (+ `Preorder`/`LocallyDirected` instances),
   `relativeProjPullbackHom : Proj_X(g^* A) ⟶ Proj_Y(A)`,
   `relativeProjCover_f_relativeProjPullbackHom`, `relativeProjPullbackHom_relativeProjToBase`,
   `isPullback_relativeProjPullbackHom`.
4. **`feat: lift into a glued module from a covering family of charts`** — after: none.
   File `TauCeti/AlgebraicGeometry/Modules/Gluing.lean` (existing, +217 lines): in
   `TauCeti.ModulesGlueData`: `eq_of_transition_app_eq_of_le_cover`,
   `eq_of_transition_app_eq_of_cover`, `exists_transition_app_eq_of_cover`, `extendOfCover`
   (+ `_transition`, `_of_mem`, `_comp_transition`), `liftOfCover`, `liftOfCover_π`, private
   helpers `exists_transition_app_eq_hom`, `extendApp` (+ lemmas).
5. **`feat: compare the twisting sheaves of the relative Proj of a pulled-back graded algebra`** —
   after: 3, 4. Files: `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/Functor.lean`
   (existing, +16 lines): `AlgebraicGeometry.Proj.twistingSheafMap_app_apply_res_of_eq_comp`;
   `TauCeti/AlgebraicGeometry/RelativeProj/BaseChangeTwistingSheaf.lean` (new, 308 lines):
   `relativeProjTwistingSheafChartHom` (+ `_app_apply`, `_eq_of_le`, `_comp_transition`, `_eq`),
   `pullbackRelativeProjTwistingSheafChartHom` (+ `_eq`, `_comp_transition`),
   `exists_mem_opensRange_relativeProjCover_f`,
   `relativeProjPullbackTwistingSheafHom : h^* 𝒪_A(n) ⟶ 𝒪_{g^* A}(n)`,
   `relativeProjPullbackTwistingSheafHom_π`. The file elaborates in about 8.5 minutes; see the
   elaboration notes of the previous session (explicit `pushforwardComp`/`pushforwardCongr`
   arguments, `let`s over `h⁻¹ W`, `Eq.trans`/`congrArg` rather than `rw` on sections).
6. **`feat: base change of the sections of twisting sheaves over standard opens`** — after: none.
   File `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/BaseChange.lean` (new, 349
   lines): `AlgebraicGeometry.Proj.twistingSheaf.isBaseChange_comap_basicOpen` (degree-`n` analogue
   of `HomogeneousLocalization.Away.baseChangeEquiv`, no degree-one generation), private helpers.
7. **`feat: twisting sheaves pull back along base changes of graded rings`** — after: 6.
   Files: `TauCeti/AlgebraicGeometry/Modules/AffineRestriction.lean` (existing, +69 lines):
   `Scheme.Modules.Hom.bijective_app_of_le`, `Scheme.Modules.Hom.isIso_of_bijective_app`;
   `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/PullbackBaseChange.lean` (new, 239
   lines): `Proj.pullbackTwistingSheafMap`, `pullbackTwistingSheafMap_eq`,
   `pullbackTwistingSheafMap_app_pullbackSectionsLE`,
   `bijective_pullbackTwistingSheafMap_app_basicOpen`,
   `isIso_pullbackTwistingSheafMap_of_forall_isBaseChange`,
   `isIso_pullbackTwistingSheafMap_of_isBaseChange`.
8. **`feat: base change of the relative Proj, compatibly with O(n)`** — after: 1–7. The only split
   that completes the target. Files: `TauCeti/AlgebraicGeometry/Modules/Gluing.lean` (+7 lines):
   `TauCeti.ModulesGlueData.restrictGluedHom_eq`;
   `TauCeti/AlgebraicGeometry/Modules/Restriction/Cover.lean` (new, 64 lines):
   `Scheme.Modules.Hom.isIso_of_isIso_restrictFunctor_map`;
   `TauCeti/CategoryTheory/Adjunction/HomEquiv.lean` (new, 89 lines):
   `Adjunction.comp_homEquiv_symm_comp_map`, `Adjunction.isIso_homEquiv_symm_comp_hom_app`,
   `Adjunction.isIso_map_of_comp_eq_homEquiv_symm`;
   `TauCeti/AlgebraicGeometry/RelativeProj/BaseChangeTwistingSheafIso.lean` (new, 143 lines):
   `GradedQuasicoherentAlgebra.isIso_pullbackTwistingSheafMap_pullbackGradedSectionsGradedHom`,
   private `chartPushforwardIso`, `relativeProjTwistingSheafChartHom_eq_comp`,
   `isIso_homEquiv_symm_relativeProjTwistingSheafGlueData_π`,
   `isIso_homEquiv_symm_twistingSheafMap`, `relativeProjPullbackTwistingSheafHom_comp_π`; still to add:
   `isIso_restrictFunctor_map_relativeProjPullbackTwistingSheafHom`, the instance
   `isIso_relativeProjPullbackTwistingSheafHom`, `relativeProjPullbackTwistingSheafIso` (+ `_hom`)
   and the export `GradedQuasicoherentAlgebra.relativeProj_baseChange` (`@[stacks 01O3]`).

## What is proved and what remains

Proved (sorry-free, building on `main`): graded maps of sections into `(pullback g).obj A`
(split 1); affine base change of sections and the cartesian chart squares (2); the cartesian square
`isPullback_relativeProjPullbackHom` (3), whose degree-zero part is `g^* A₀` by `main`'s
`pullback_obj_obj_X`; gluing into a glued module (4); the comparison
`relativeProjPullbackTwistingSheafHom g A n : h^* 𝒪_A(n) ⟶ 𝒪_{g^* A}(n)` (5); the degree-`n`
affine base change of sections of twisting sheaves (6); the isomorphism `(Proj.map f)^* 𝒪(n) ≅ 𝒪(n)`
for any base change of graded rings, in all degrees, without degree-one generation (7); and, in
split 8, the abstract criterion `Adjunction.isIso_map_of_comp_eq_homEquiv_symm` together with
every concrete input it needs, each checked by the kernel:
`isIso_homEquiv_symm_relativeProjTwistingSheafGlueData_π` (for `A` over `U` and for `g^* A`
over `V`), `isIso_homEquiv_symm_twistingSheafMap` and the equation
`relativeProjPullbackTwistingSheafHom_comp_π`.

Remains (split 8 only): **one application**, then the export. The elaborator accepts

```lean
theorem isIso_restrictFunctor_map_relativeProjPullbackTwistingSheafHom {V : X.AffineZariskiSite}
    {U : Y.AffineZariskiSite} (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    IsIso ((Scheme.Modules.restrictFunctor (((pullback g).obj A).obj.relativeProjCover.f V)).map
      (relativeProjPullbackTwistingSheafHom g A n)) :=
  Adjunction.isIso_map_of_comp_eq_homEquiv_symm
    (Scheme.Modules.restrictAdjunction (A.obj.relativeProjCover.f U))
    (Scheme.Modules.pullbackPushforwardAdjunction (Proj.map (A.pullbackGradedSectionsGradedHom g hV)
      (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2)))
    (Scheme.Modules.pullbackPushforwardAdjunction (relativeProjPullbackHom g A))
    (Scheme.Modules.restrictAdjunction (((pullback g).obj A).obj.relativeProjCover.f V))
    (chartPushforwardIso hV) _ _ _ (relativeProjPullbackTwistingSheafHom g A n)
    (hπU := isIso_homEquiv_symm_relativeProjTwistingSheafGlueData_π n A U)
    (ht := isIso_homEquiv_symm_twistingSheafMap g A n hV)
    (hπV := isIso_homEquiv_symm_relativeProjTwistingSheafGlueData_π n ((pullback g).obj A) V)
    (relativeProjPullbackTwistingSheafHom_comp_π g A n hV)
```

but the kernel times out on it (`(kernel) deterministic timeout`, about 4–5 minutes).

**Diagnosis (session of 2026-11-04 evening).** Replacing the instance arguments one at a time by
`sorry` (scratch copies of the split-8 file, `set_option profiler true`): with `hπU` and `ht` real
and `hπV`, `h` sorried the kernel checks the application in about 1 s; adding the real `hπV` alone
makes it time out. The implicit `P` of the abstract lemma is fixed by `t`
(`Proj.twistingSheafMap … : _ ⟶ (Proj.map _)_* (Proj.twistingSheaf ℬ n)`), so `P` is spelled
`Proj.twistingSheaf (gradedSectionsGrading …) n`, while
`isIso_homEquiv_symm_relativeProjTwistingSheafGlueData_π` is stated with
`homEquiv D'.glued (D'.obj V)`. The kernel converts `D'.obj V ≡ Proj.twistingSheaf … n`
cheaply as bare objects or inside `Quiver.Hom`/`Eq` types (that is why `hπU`, whose `Q` is fixed
by `πU` itself, and the `D.obj U` in `ht` are fine), but **inside the second argument of
`(restrictAdjunction _).homEquiv`** (under `IsIso (DFunLike.coe …)`) the same conversion times out,
even for a generic graded algebra `B` (a lemma `IsIso (homEquiv D.glued (Proj.twistingSheaf …)).symm
(D.π W)` proved by `exact` of the `D.obj W` form times out too). Fixing `P := D'.obj V` instead
moves the cost to `h`: a restatement of `relativeProjPullbackTwistingSheafHom_comp_π` with
`(chartPushforwardIso hV).hom.app (D'.obj V)` and `homEquiv _ (Rv.obj (D'.obj V))` times out, while
the analogous restatement of `ht` with a `D'.obj V`-typed copy of `Proj.twistingSheafMap` passes
(80–140 s, too slow to keep). So every input must reach the application with `P` spelled exactly
as the other inputs spell it, and no `D'.obj V`/`Proj.twistingSheaf` conversion may happen under
`homEquiv`.

**Fix in progress.** A variant of the abstract lemma that takes `hP : P = P'`, `t : Q ⟶ Rm.obj P'`,
`πV : N ⟶ Rv.obj P` and `h : φ ≫ πV ≫ eqToHom (congrArg Rv.obj hP) = (adjH.homEquiv _ _).symm
((πU ≫ Ru.map t) ≫ e.hom.app P')`, proved by `subst hP; rw [eqToHom_refl, Category.comp_id] at h`
and the existing lemma, **passes the kernel instantly**:

```lean
theorem isIso_map_of_comp_eq_homEquiv_symm_of_eq {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] {Lu : C₁ ⥤ C₂} {Ru : C₂ ⥤ C₁} {Lm : C₂ ⥤ C₃} {Rm : C₃ ⥤ C₂}
    {Lh : C₁ ⥤ C₄} {Rh : C₄ ⥤ C₁} {Lv : C₄ ⥤ C₃} {Rv : C₃ ⥤ C₄} (adjU : Lu ⊣ Ru)
    (adjM : Lm ⊣ Rm) (adjH : Lh ⊣ Rh) (adjV : Lv ⊣ Rv) (e : Rm ⋙ Ru ≅ Rv ⋙ Rh) {M : C₁}
    {Q : C₂} {P P' : C₃} {N : C₄} (hP : P = P') (πU : M ⟶ Ru.obj Q) (t : Q ⟶ Rm.obj P')
    (πV : N ⟶ Rv.obj P) (φ : Lh.obj M ⟶ N) [hπU : IsIso ((adjU.homEquiv _ _).symm πU)]
    [ht : IsIso ((adjM.homEquiv _ _).symm t)] [hπV : IsIso ((adjV.homEquiv _ _).symm πV)]
    (h : φ ≫ πV ≫ eqToHom (congrArg Rv.obj hP) =
      (adjH.homEquiv _ _).symm ((πU ≫ Ru.map t) ≫ e.hom.app P')) :
    IsIso (Lv.map φ) := by
  subst hP
  rw [eqToHom_refl, Category.comp_id] at h
  exact isIso_map_of_comp_eq_homEquiv_symm adjU adjM adjH adjV e πU t πV φ h
```

It is to be applied with `hP := CommMon.relativeProjTwistingSheafGlueData_obj _ n V` (the `simps`
lemma `D'.obj V = Proj.twistingSheaf (gradedSectionsGrading V) n`), so that `hπV` keeps its
`D'.obj V` form and `ht`, `h` keep their `Proj.twistingSheaf` form. The input `h` is
`relativeProjPullbackTwistingSheafHom_comp_π` with `≫ eqToHom (congrArg (pushforward _).obj hP)`
appended to the left side; prove it by rewriting with
`show eqToHom (congrArg _ hP) = 𝟙 _ from eqToHom_refl _ _` and `Category.comp_id` (a plain
`rw [eqToHom_refl]` does not match). **This did not yet close the gap**: the application of the `_of_eq` variant still times out in
the kernel (about 5 minutes), whether `hP` is passed directly or as `(by exact …)` (elaborated
after `t`), and even with `h` stated with fully explicit objects
(`homEquiv (A.obj.relativeProjTwistingSheafGlueData n).glued ((pushforward ι_V).obj P')` and
`(chartPushforwardIso hV).hom.app P'`, `P' = Proj.twistingSheaf
(((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n`, which is also the spelling `t`
produces, since `pullbackGradedSectionsGradedHom : A.obj.gradedSectionsGrading U →+*ᵍ
((pullback g).obj A).obj.gradedSectionsGrading V`). So some other argument of that application is
expensive; the next session should profile it argument by argument exactly as above (replace
`hπU`, `ht`, `hπV`, `h` by `sorry` one at a time, in the `_of_eq` application, with `hP` real).
Also: proving the eqToHom form of `h` by `rw [eqToHom_refl]` (or
`rw [show eqToHom _ = 𝟙 _ from eqToHom_refl _ _]`, or `erw` after `rw [← h0]`) fails to find the
pattern; a working proof is still to be found (e.g. a general lemma
`f ≫ eqToHom p = f` for `p : X = X` applied with `exact`). Kernel
experiments: use `lean` with `LEAN_PATH` from `lake env printenv LEAN_PATH` directly (parallel
`lake env` calls contend for `.git/config` locks), and make the split-8 helpers temporarily
non-private so a small scratch module can import them (the split-8 file itself takes ~5 minutes).

After that, the rest is written and was accepted by the elaborator in the previous session:

```lean
instance isIso_relativeProjPullbackTwistingSheafHom :
    IsIso (relativeProjPullbackTwistingSheafHom g A n) :=
  Scheme.Modules.Hom.isIso_of_isIso_restrictFunctor_map _
    (ι := {V : X.AffineZariskiSite // ∃ U : Y.AffineZariskiSite, V.toOpens ≤ g ⁻¹ᵁ U.toOpens})
    (fun V ↦ ((pullback g).obj A).obj.relativeProjCover.f V.1)
    (fun x ↦ (exists_mem_opensRange_relativeProjCover_f g A x).elim fun V ⟨hV, hx⟩ ↦
      ⟨⟨V, hV⟩, hx⟩)
    fun ⟨_, _, hV⟩ ↦ isIso_restrictFunctor_map_relativeProjPullbackTwistingSheafHom g A n hV

noncomputable def relativeProjPullbackTwistingSheafIso :
    (Scheme.Modules.pullback (relativeProjPullbackHom g A)).obj
        (A.obj.relativeProjTwistingSheaf n) ≅
      ((pullback g).obj A).obj.relativeProjTwistingSheaf n :=
  asIso (relativeProjPullbackTwistingSheafHom g A n)

@[simp]
theorem relativeProjPullbackTwistingSheafIso_hom :
    (relativeProjPullbackTwistingSheafIso g A n).hom =
      relativeProjPullbackTwistingSheafHom g A n :=
  (rfl)

@[stacks 01O3]
theorem relativeProj_baseChange :
    IsPullback ((pullback g).obj A).obj.relativeProjToBase (relativeProjPullbackHom g A) g
        A.obj.relativeProjToBase ∧
      (∀ k, ((pullback g).obj A).obj.X k = (Scheme.Modules.pullback g).obj (A.obj.X k)) ∧
      ∀ n : ℤ, IsIso (relativeProjPullbackTwistingSheafHom g A n) :=
  ⟨isPullback_relativeProjPullbackHom g A, pullback_obj_obj_X g A, fun _ ↦ inferInstance⟩
```

(docstrings as in the `LOOKAHEAD.md` of the previous tip `7196e72258f2`; the instance needs
`public import TauCeti.AlgebraicGeometry.Modules.Restriction.Cover`). Expected size of the
finished split-8 file: about 250 lines.
