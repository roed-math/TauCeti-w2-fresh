<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"relative-proj-base-change","main":"333c9e49143de812ed1452b412193ee9c05501e7","status":"partial","suppliers":["relative-proj-twisting-sheaf"],"splits":[{"n":1,"after":[],"title":"feat: pullback of graded quasicoherent algebras"},{"n":2,"after":[1],"title":"feat: pullback of sections of a graded quasicoherent algebra as a graded ring map"},{"n":3,"after":[2],"title":"feat: affine base change of the graded sections of a pulled-back graded algebra"},{"n":4,"after":[3],"title":"feat: the relative Proj of a pulled-back graded algebra is the base change"},{"n":5,"after":[1,2,3,4],"title":"feat: base change of the relative Proj, compatibly with O(n)"}]}-->

# Lookahead: `relative-proj-base-change` (SchemeAndStackFoundations, Layer 0, §0.3)

Target (README §0.3): *Prove `relativeProj_baseChange`: formation of `relativeProj` commutes with
arbitrary base change `g : S' → S`, with degree-zero part `g^* A_0`, compatibly with `O(n)`
(Stacks, Lemma 27.16.10 (01O3)).* The README states that the relative Proj and its comparisons are
specified in the README only; `Suggested.lean` pins only `Proj.isPullback_baseChange`, which is
already on `main` (`AlgebraicGeometry.Proj.isPullback_baseChange`,
`Proj.isPullback_map_of_isBaseChange` in `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/BaseChange.lean`).

Built on `main` at `333c9e49143de812ed1452b412193ee9c05501e7`. Status: **partial** (splits 1 and 2
proved, sorry-free; splits 3–5 remain).

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
which no PR or `Suggested.lean` pins yet. Splits 1–2 consume none of these. Neither does the
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
   *Not yet written.* Planned file
   `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/GradedAlgebra/PullbackBaseChange.lean`:
   (a) a modest generalisation of `Scheme.Hom.pullbackSectionsEquiv` /
   `isBaseChange_pullbackSections` (`Modules/Pullback/BaseChange.lean`) from `V = g⁻¹ U` affine to
   any affine `V ≤ g⁻¹ U`, by applying it to `V.ι ≫ g` and identifying
   `(V.ι ≫ g)^* M` with `(g^* M)|_V` through `pullbackComp`, `restrictFunctorIsoPullback` and
   `pullbackSectionsLE_comp`; (b) the direct-sum version: for `U`, `V` affine,
   `pullbackGradedSections` exhibits `⨁ Γ(g^* Aₙ, V)` as `Γ(X, V) ⊗[Γ(Y, U)] ⨁ Γ(Aₙ, U)`
   (`IsBaseChange`, via `TensorProduct.directSumRight`); (c) the chart square:
   `Proj (⨁ Γ(g^* Aₙ, V)) ⟶ Proj (⨁ Γ(Aₙ, U))` is the pullback along
   `Spec Γ(X, V) ⟶ Spec Γ(Y, U)`, by `Proj.isPullback_map_of_isBaseChange`.
4. **`feat: the relative Proj of a pulled-back graded algebra is the base change`** — after: 3.
   *Not yet written.* Planned file `TauCeti/AlgebraicGeometry/RelativeProj/BaseChange.lean`:
   the projection `relativeProj (g^* A) ⟶ relativeProj A` over `g` and its cartesian square.
   Strategy: affine-target case first (every chart of `relativeProj (g^* A)` maps to the single
   chart `Proj A(S)` of an affine `S`, via `isPullback_relativeProjCover` at `U = ⊤` and split 3),
   then local on `S` over the cover by affine `U`, using `relativeProjToBase_preimage` and
   pasting of cartesian squares; the gluing data is Mathlib's `RelativeGluingData`.
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
part `g^* A₀` (split 1) and the graded ring maps of sections along `g` that the charts of the base
change are built from (split 2). Remaining: splits 3, 4, 5 as described above; in particular the
general affine `V ≤ g⁻¹ U` base change of quasicoherent sections, the global gluing of the
cartesian square, and the `𝒪(n)` comparison.
