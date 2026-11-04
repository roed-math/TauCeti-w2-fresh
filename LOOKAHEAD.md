<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"relative-proj-base-change","main":"57ab0f657d7fb33d7c9425bf696bec3045b0fd75","status":"complete","suppliers":["relative-proj-twisting-sheaf"],"splits":[{"n":1,"after":[],"title":"feat: pullback of sections of a graded quasicoherent algebra as a graded ring map"},{"n":2,"after":[1],"title":"feat: affine base change of the graded sections of a pulled-back graded algebra"},{"n":3,"after":[2],"title":"feat: the relative Proj of a pulled-back graded algebra is the base change"},{"n":4,"after":[],"title":"feat: lift into a glued module from a covering family of charts"},{"n":5,"after":[3,4],"title":"feat: compare the twisting sheaves of the relative Proj of a pulled-back graded algebra"},{"n":6,"after":[],"title":"feat: base change of the sections of twisting sheaves over standard opens"},{"n":7,"after":[6],"title":"feat: twisting sheaves pull back along base changes of graded rings"},{"n":8,"after":[1,2,3,4,5,6,7],"title":"feat: base change of the relative Proj, compatibly with O(n)"}]}-->

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

## Changes since the previous session (tip `4a8386361159`)

`origin/main` (`57ab0f657d7`) was merged (clean; no stub had to give way). The kernel timeout of
split 8 is fixed and the target is now **complete**:

* A per-argument kernel diagnostic located the cost: the kernel converts `D.obj W` (a projection of
  the gluing datum of twisting sheaves) to `Proj.twistingSheaf (… W) n` cheaply as a bare object
  or inside a `Quiver.Hom` type, but not inside a transpose `(adj.homEquiv _ _).symm _`, where it
  unfolds the adjunction instead. The abstract lemma's implicit objects were previously fixed by
  unification, so its instance arguments disagreed with the supplied facts on exactly such
  objects.
* Every object of `Adjunction.isIso_map_of_comp_eq_homEquiv_symm` is now pinned to one spelling
  (the twisting sheaves `relativeProjTwistingSheaf n` and `Proj.twistingSheaf (…) n`), its
  hypothesis `h` names its composite's objects explicitly, and each input is stated with exactly
  those spellings. The one change of spelling under a transpose (the chart identification, stated
  on `main` with `D.glued` and `D.obj W`) goes through the new transport lemma
  `Adjunction.isIso_homEquiv_symm_of_eq`, which substitutes along `rfl` equalities of objects and
  takes the morphisms as `HEq` (proved by `HEq.rfl`), so the kernel only compares bare objects and
  `Quiver.Hom` types. (An `eqToHom` form of that hypothesis, proved by `erw [eqToHom_refl, …]`,
  timed out in the kernel; so did the old application.)
* With that, `isIso_restrictFunctor_map_relativeProjPullbackTwistingSheafHom`, the instance
  `isIso_relativeProjPullbackTwistingSheafHom`, `relativeProjPullbackTwistingSheafIso` (+ `_hom`)
  and the export `relativeProj_baseChange` (`@[stacks 01O3]`) are proved; the whole split-8 file
  elaborates and passes the kernel in about 6–14 minutes on a loaded machine (the old-spelling chart
  identification alone costs about 200 s of kernel time).

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
   `TauCeti/CategoryTheory/Adjunction/HomEquiv.lean` (new, 106 lines):
   `Adjunction.comp_homEquiv_symm_comp_map`, `Adjunction.isIso_homEquiv_symm_comp_hom_app`,
   `Adjunction.isIso_homEquiv_symm_of_eq`, `Adjunction.isIso_map_of_comp_eq_homEquiv_symm`;
   `TauCeti/AlgebraicGeometry/RelativeProj/BaseChangeTwistingSheafIso.lean` (new, 280 lines):
   `GradedQuasicoherentAlgebra.isIso_pullbackTwistingSheafMap_pullbackGradedSectionsGradedHom`,
   private `chartPushforwardIso`, `relativeProjTwistingSheafChartHom_eq_comp`,
   `isIso_homEquiv_symm_relativeProjTwistingSheafGlueData_π`, `isIso_homEquiv_symm_π_twistingSheaf`,
   `isIso_homEquiv_symm_twistingSheafMap`, `relativeProjPullbackTwistingSheafHom_comp_π`; public
   `isIso_restrictFunctor_map_relativeProjPullbackTwistingSheafHom`, the instance
   `isIso_relativeProjPullbackTwistingSheafHom`, `relativeProjPullbackTwistingSheafIso` (+ `_hom`)
   and the export `GradedQuasicoherentAlgebra.relativeProj_baseChange` (`@[stacks 01O3]`):
   the square `Proj_X(g^* A) → Proj_Y(A)` over `g` is cartesian, `(g^* A)ₖ = g^* Aₖ` for every
   `k` (degree zero included), and `h^* 𝒪_A(n) ⟶ 𝒪_{g^* A}(n)` is an isomorphism for every `n`.

## What is proved

Everything: the target is **complete** and sorry-free (the stub module is empty).
`TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.relativeProj_baseChange g A` states, for a
morphism of schemes `g : X ⟶ Y` and a graded quasicoherent algebra `A` on `Y`:

* `IsPullback ((pullback g).obj A).obj.relativeProjToBase (relativeProjPullbackHom g A) g
  A.obj.relativeProjToBase`: formation of `relativeProj` commutes with arbitrary base change;
* `∀ k, ((pullback g).obj A).obj.X k = (Scheme.Modules.pullback g).obj (A.obj.X k)`: the
  homogeneous components of the pulled-back algebra, in particular its degree-zero part `g^* A₀`;
* `∀ n : ℤ, IsIso (relativeProjPullbackTwistingSheafHom g A n)`: compatibility with `O(n)`. The
  isomorphism is `relativeProjPullbackTwistingSheafIso g A n : h^* 𝒪_A(n) ≅ 𝒪_{g^* A}(n)`.

No degree-one generation hypothesis is needed anywhere. Compatibility with the multiplication
maps `𝒪(m) ⊗ 𝒪(n) ⟶ 𝒪(m + n)` of the open supplier PR #27145 is not part of the statement; see
*Stubs* for how a later session would add it if review asks for it.
