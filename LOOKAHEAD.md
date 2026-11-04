<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"relative-proj-base-change","main":"6c781b0a7341d9d794cf474258f824f4fa65faa2","status":"partial","suppliers":["relative-proj-twisting-sheaf"],"splits":[{"n":1,"after":[],"title":"feat: pullback of graded quasicoherent algebras"},{"n":2,"after":[1],"title":"feat: pullback of sections of a graded quasicoherent algebra as a graded ring map"},{"n":3,"after":[2],"title":"feat: affine base change of the graded sections of a pulled-back graded algebra"},{"n":4,"after":[3],"title":"feat: the relative Proj of a pulled-back graded algebra is the base change"},{"n":5,"after":[],"title":"feat: lift into a glued module from a covering family of charts"},{"n":6,"after":[4,5],"title":"feat: compare the twisting sheaves of the relative Proj of a pulled-back graded algebra"},{"n":7,"after":[1,2,3,4,5,6],"title":"feat: base change of the relative Proj, compatibly with O(n)"}]}-->

# Lookahead: `relative-proj-base-change` (SchemeAndStackFoundations, Layer 0, §0.3)

Target (README §0.3): *Prove `relativeProj_baseChange`: formation of `relativeProj` commutes with
arbitrary base change `g : S' → S`, with degree-zero part `g^* A_0`, compatibly with `O(n)`
(Stacks, Lemma 27.16.10 (01O3)).* The README states that the relative Proj and its comparisons are
specified in the README only; `Suggested.lean` pins only `Proj.isPullback_baseChange`, which is
already on `main` (`AlgebraicGeometry.Proj.isPullback_baseChange`,
`Proj.isPullback_map_of_isBaseChange` in `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/BaseChange.lean`).

Built on `main` at `6c781b0a7341d9d794cf474258f824f4fa65faa2` (merged into the branch on 2026-11-04). Status: **partial**
(splits 1–6 proved, sorry-free; split 7 remains).

## Stubs

`TauCeti/Lookahead/RelativeProjBaseChange/Stubs.lean` states **no declaration**.

The supplier `relative-proj-twisting-sheaf` has already landed, on `main`, everything the target
needs from it so far: the relative Proj (`CategoryTheory.CommMon.relativeProj`, #19831), its
twisting sheaves `𝒪(n)` (`CategoryTheory.CommMon.relativeProjTwistingSheaf`, #22384) with their
chart identification `restrictRelativeProjTwistingSheafIso`, and invertibility in degree one
(#23564). The open supplier PR #27145 adds the multiplication of sections
`CategoryTheory.CommMon.relativeProjTwistingSheafMul` (with `π_app_relativeProjTwistingSheafMul`,
`res_relativeProjTwistingSheafMul`) and `relativeProjTwistingSheafTensorProductIso`; the README
milestone still owes the graded map `A → ⊕_{n ≥ 0} (relativeProj.toBase)_* O(n)` (Stacks 01NR),
which no PR or `Suggested.lean` pins yet. Splits 1–6 consume none of these, and neither does the
planned split 7 (the comparison of split 6 is an isomorphism, checked on charts, where the
twisting sheaves are those of `Proj` on `main`; the supplier's quasi-coherence of `𝒪(n)` on the
relative `Proj` is not needed, as the check runs on the charts `Proj (⨁ n, Γ(g^* Aₙ, V))`, where
`AlgebraicGeometry.Proj.isQuasicoherent_twistingSheaf` is on `main`). If the next session decides that "compatibly with `O(n)`"
must also include compatibility with the multiplication maps, it should stub
`relativeProjTwistingSheafMul` and its two characterising lemmas from PR #27145's diff
(`TauCeti/AlgebraicGeometry/RelativeProj/TwistingSheaf/TensorProduct.lean`), verbatim, in this file.
No `Suggested.lean` signature exists for any of them (relative Proj is README-only).

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
7. **`feat: base change of the relative Proj, compatibly with O(n)`** — after: 1, 2, 3, 4, 5, 6.
   *Not yet written.* Planned files: a degree-`n` companion of
   `TauCeti/RingTheory/GradedAlgebra/HomogeneousLocalization/BaseChange.lean` for the sections of
   twisting sheaves on standard opens, and `TauCeti/AlgebraicGeometry/RelativeProj/BaseChangeTwistingSheaf.lean`
   (or a sibling, if that file would pass 1000 lines) carrying the exported theorem
   `CategoryTheory.CommMon.relativeProj_baseChange` (`@[stacks 01O3]`).

## What is proved and what remains

Proved (sorry-free, building on `main`): the pulled-back graded algebra `g^* A` with degree-zero
part `g^* A₀` (split 1); the graded ring maps of sections along `g` (split 2); affine base change
of quasicoherent sections and of the graded sections, with the cartesian chart squares
`Proj (⨁ Γ(g^* Aₙ, V)) = Spec Γ(X, V) ×_{Spec Γ(Y, U)} Proj (⨁ Γ(Aₙ, U))` (split 3); the global
projection `relativeProjPullbackHom g A : Proj_X(g^* A) ⟶ Proj_Y(A)` over `g` and the cartesian
square `isPullback_relativeProjPullbackHom` (split 4) — i.e. formation of `relativeProj` commutes
with arbitrary base change, with degree-zero part `g^* A₀`.

Also proved (splits 5–6): gluing of morphisms into a glued module from a downward closed covering
family of charts, and the comparison morphism
`relativeProjPullbackTwistingSheafHom g A n : h^* 𝒪_A(n) ⟶ 𝒪_{g^* A}(n)` for the projection
`h = relativeProjPullbackHom g A`, identified on each chart over `V ≤ g⁻¹ U` with the adjoint of
`Proj.twistingSheafMap` of the pullback of sections (`relativeProjPullbackTwistingSheafHom_π`).

Remaining (split 7 only):
- *Degree-`n` base change on standard opens.* For a graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` over
  `R → S` exhibiting `B` as `S ⊗[R] A` (the hypotheses of `Proj.isPullback_map_of_isBaseChange`)
  and `a ∈ 𝒜 d`, `d > 0`: `Proj.twistingSheaf.comap f` from `Γ(D₊(a), 𝒪(n))` to `Γ(D₊(f a), 𝒪(n))`
  is a base change along `Γ(D₊(a), 𝒪) → Γ(D₊(f a), 𝒪)`. This is the degree-`n` analogue of
  `HomogeneousLocalization.Away.baseChangeEquiv` (degree zero, on `main`), via
  `Proj.twistingSheaf.exists_eq_const_basicOpen` and `const_eq_zero_iff`.
- *Proj-level isomorphism.* The adjoint `(Proj.map f)^* 𝒪(n) ⟶ 𝒪(n)` of `Proj.twistingSheafMap`
  is an isomorphism for such `f`. Both sides are quasi-coherent (`isQuasicoherent_twistingSheaf`;
  pullbacks of quasi-coherent modules), so this can be checked on the affine cover by the
  `D₊(f a)`, where pullback of sections is a base change (`Scheme.Hom.isBaseChange_pullbackSectionsLE`,
  split 3). Open PR #27468 (another author) adds `Proj.pullbackTwistingSheafMap` and an isomorphism
  criterion assuming degree-one generators, plus `Scheme.Modules.Hom.isIso_of_bijective_app`
  (isomorphisms of quasi-coherent modules are detected on an affine cover). If it lands first,
  reuse its comparison and criterion and drop the degree-one assumption with the lemma above.
- *Relative isomorphism.* `relativeProjPullbackTwistingSheafHom` is an isomorphism. This is local
  on the cover by the charts over `V ≤ g⁻¹ U`. There, by `relativeProjPullbackTwistingSheafHom_π`,
  `ModulesGlueData.restrictGluedIso` on both sides and `relativeProjCover_f_relativeProjPullbackHom`,
  it is the Proj-level isomorphism for the base change `isBaseChange_pullbackGradedSections`
  (split 3).
- *Export* `CategoryTheory.CommMon.relativeProj_baseChange` (`@[stacks 01O3]`), packaging
  `isPullback_relativeProjPullbackHom`, `pullback_obj_X` (degree-zero part `g^* A₀`) and
  `asIso (relativeProjPullbackTwistingSheafHom g A n)` for all `n : ℤ`.
