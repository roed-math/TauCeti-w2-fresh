<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"relative-proj-base-change","main":"11a5574886a7b084337236bb1f858406b483c6cc","status":"partial","suppliers":["relative-proj-twisting-sheaf"],"splits":[{"n":1,"after":[],"title":"feat: pullback of graded quasicoherent algebras"},{"n":2,"after":[1],"title":"feat: pullback of sections of a graded quasicoherent algebra as a graded ring map"},{"n":3,"after":[2],"title":"feat: affine base change of the graded sections of a pulled-back graded algebra"},{"n":4,"after":[3],"title":"feat: the relative Proj of a pulled-back graded algebra is the base change"},{"n":5,"after":[1,2,3,4],"title":"feat: base change of the relative Proj, compatibly with O(n)"}]}-->

# Lookahead: `relative-proj-base-change` (SchemeAndStackFoundations, Layer 0, §0.3)

Target (README §0.3): *Prove `relativeProj_baseChange`: formation of `relativeProj` commutes with
arbitrary base change `g : S' → S`, with degree-zero part `g^* A_0`, compatibly with `O(n)`
(Stacks, Lemma 27.16.10 (01O3)).* The README states that the relative Proj and its comparisons are
specified in the README only; `Suggested.lean` pins only `Proj.isPullback_baseChange`, which is
already on `main` (`AlgebraicGeometry.Proj.isPullback_baseChange`,
`Proj.isPullback_map_of_isBaseChange` in `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/BaseChange.lean`).

Built on `main` at `11a5574886a7b084337236bb1f858406b483c6cc` (merged into the branch this
session). Status: **partial** (splits 1, 2 and 3 proved, sorry-free; split 4 started; splits 4–5
remain).

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
which no PR or `Suggested.lean` pins yet. Splits 1–2 consume none of these. Split 3 and the
part of split 4 written so far consume none of them either. Neither does the
planned form of split 5 (the isomorphisms `g'^* 𝒪(n) ≅ 𝒪(n)`, built chartwise from
`Proj.twistingSheafMap` on `main`). If the next session decides that "compatibly with `O(n)`"
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
   *Started.* File `TauCeti/AlgebraicGeometry/RelativeProj/BaseChange.lean` (102 lines so far),
   in `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra`:
   `restrictGradedSectionsGradedHom_comp_pullbackGradedSectionsGradedHom`,
   `pullbackGradedSectionsGradedHom_comp_restrictGradedSectionsGradedHom` (graded-hom forms of
   split 2's restriction compatibilities), `relativeProjGluingData_functor_map_comp_proj_map` and
   `proj_map_comp_relativeProjGluingData_functor_map` (`@[reassoc]`: the chart morphisms
   `Proj.map (pullbackGradedSectionsGradedHom g hV)` commute with the transition maps of the
   gluing data of both relative `Proj`s — the naturality the cocone below needs).
   *Remaining:* the projection `relativeProj (g^* A) ⟶ relativeProj A` over `g` and its cartesian
   square. `relativeProj` is `colimit relativeProjGluingData.functor` (Mathlib's
   `RelativeGluingData.glued`), so the projection is a `colimit.desc`. Planned order:
   (i) when `g⁻¹ U = ⊤` for an affine `U` (e.g. `Y` affine, `U = ⊤`), the cocone is
   `Proj.map (pullbackGradedSectionsGradedHom g _) ≫ relativeProjCover.f ⟨U, hU⟩`, natural by
   `relativeProjGluingData_functor_map_comp_proj_map`; its square is cartesian by
   `Scheme.isPullback_of_openCover` over the affine cover of `X`, pasting
   `isPullback_relativeProjCover` (for `g^* A` at `V` and for `A` at `U`) with
   `isPullback_proj_pullbackGradedSections`. (ii) In general each chart `Proj (⨁ Γ(g^* Aₙ, V))`
   is covered by the charts of basic opens `D(f) ⊆ V` lying over affine opens `U` of `Y`; glue
   the maps of (i) with `Scheme.Cover.glueMorphisms` (agreement on overlaps by
   `proj_map_comp_relativeProjGluingData_functor_map`), check naturality in `V`, and conclude
   with `Scheme.isPullback_of_openCover` again. The file may need splitting at (i)/(ii) to stay
   within 600 lines.
5. **`feat: base change of the relative Proj, compatibly with O(n)`** — after: 1, 2, 3, 4.
   *Not yet written.* Planned file `TauCeti/AlgebraicGeometry/RelativeProj/BaseChangeTwistingSheaf.lean`
   carrying the exported theorem `CategoryTheory.CommMon.relativeProj_baseChange`
   (`@[stacks 01O3]`): `IsPullback` of the projection, the structure morphisms and `g`, with
   `relativeProj` of `(GradedQuasicoherentAlgebra.pullback g A).obj`, whose degree-zero part is
   `g^* A₀` by `pullback_obj_X`, and isomorphisms `(projection)^* 𝒪_A(n) ≅ 𝒪_{g^* A}(n)` for all
   `n : ℤ`, glued chartwise from the adjoints of `Proj.twistingSheafMap` (bijective on charts by
   base change) via `ModulesGlueData`.

## What is proved and what remains

Proved (sorry-free, building on `main`): the pulled-back graded algebra `g^* A` with degree-zero
part `g^* A₀` (split 1); the graded ring maps of sections along `g` (split 2); affine base change
of quasicoherent sections for any affine `V ≤ g⁻¹ U` and of the graded sections, and the cartesian
chart squares `Proj (⨁ Γ(g^* Aₙ, V)) = Spec Γ(X, V) ×_{Spec Γ(Y, U)} Proj (⨁ Γ(Aₙ, U))` (split 3);
compatibility of these chart maps with the transition maps of both relative `Proj`s (start of
split 4). Remaining: the global projection `relativeProj (g^* A) ⟶ relativeProj A` and its
cartesian square (rest of split 4, steps (i) and (ii) above), and the `𝒪(n)` comparison with the
exported `relativeProj_baseChange` (split 5).
