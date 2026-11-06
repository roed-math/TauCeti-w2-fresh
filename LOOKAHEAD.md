<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"relative-proj-veronese","main":"385ec2ddd8ddf8cc779b78c176308cb9c6b55499","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: the Veronese subalgebra of a graded algebra"},{"n":2,"after":[1],"title":"feat: homogeneous localizations of a Veronese subalgebra"},{"n":3,"after":[2],"title":"feat: Proj of a Veronese subalgebra"},{"n":4,"after":[],"title":"feat: Veronese subalgebras of graded monoid objects"},{"n":5,"after":[1,4],"title":"feat: graded sections of the Veronese subalgebra of a graded quasi-coherent algebra"},{"n":6,"after":[3],"title":"feat: twisting sheaves of Proj of a Veronese subalgebra"},{"n":7,"after":[1,2,3,4,5,6],"title":"feat: relative Proj of a Veronese subalgebra"}]}-->

# Lookahead: `relative-proj-veronese` (SchemeAndStackFoundations, Layer 0, §0.3)

Target (README §0.3): prove `relativeProj_veronese`: for `d ≥ 1` the Veronese subalgebra
`A^{(d)} = ⊕_k A_{dk}`, which has the same degree-zero part `A_0`, satisfies
`relativeProj A^{(d)} ≅ relativeProj A` over `S`, with `O(n)` corresponding to `O(dn)`
(Stacks, Lemma 27.11.8 (0B5J), on affine charts).

Built on `main` at `385ec2ddd8d` (merged into the branch on 2026-11-06; `main` was unchanged at
the second session of 2026-11-06).

**Status: partial.** Splits 1 to 5 are proved on this branch, with no `sorry`: the
Veronese subalgebra and its functoriality in graded ring maps, its affine charts,
`Proj A^{(d)} ≅ Proj A` over `Spec 𝒜 0` and over `Spec R`, natural in graded ring maps, the
sheaf-level Veronese subalgebra `A^{(d)}` of a graded (commutative) monoid object, and the
identification of its graded sections over an open with the Veronese subalgebra of the graded
sections of `A`. Split 7 is started: the chart isomorphisms `Proj Γ(A^{(d)}, U) ≅ Proj Γ(A, U)`
and the compatibility of the section identification with restriction. The `O(n)`/`O(dn)`
comparison (split 6) and the rest of split 7 remain.

## Stubbed declarations

None, and this branch has no `TauCeti/Lookahead/` module.

The list names `relative-proj-twisting-sheaf` (open PR #29201) as the supplier. But the twisting
sheaves `O(n)` of a relative Proj are already on `main`:
`CategoryTheory.CommMon.relativeProjTwistingSheaf` in
`TauCeti/AlgebraicGeometry/RelativeProj/TwistingSheaf.lean`, landed by earlier partial PRs of that
supplier. Its invertibility in degree one is there too. PR #29201 adds the graded map
`A → ⊕ (relativeProj.toBase)_* O(n)` (`relativeProjToTwistingSheaf`) and the instance
`isQuasicoherent_relativeProjTwistingSheaf`. Neither appears in the README's statement of the
target ("`O(n)` corresponding to `O(dn)`" is an isomorphism of the `O(n)` that are already on
`main`), and nothing proved so far uses them, so nothing is stubbed. If split 7 states the
`O(n)` comparison in `QCoh` and so needs `isQuasicoherent_relativeProjTwistingSheaf`, then
split 7 has to wait for #29201 to land and should use the landed instance, which PR #29201's diff
states as:

```lean
instance _root_.CategoryTheory.CommMon.isQuasicoherent_relativeProjTwistingSheaf (n : ℤ) :
```

(that is, `(A.relativeProjTwistingSheaf n).IsQuasicoherent`). The roadmap's `Suggested.lean`
pins nothing for this supplier: the README says the relative Proj and its comparisons are
specified in the README only.

## Split plan

1. **`feat: the Veronese subalgebra of a graded algebra`**. After: none. *Done on this branch.*
   - File: `TauCeti/RingTheory/GradedAlgebra/VeroneseSubalgebra.lean` (203 lines).
   - Adds, in `TauCeti.GradedAlgebra`: `veronese 𝒜 d : Subalgebra R A` (the span of the
     `𝒜 (d k)`), `mem_veronese`, `mem_veronese_of_mem`, `veroneseGrading 𝒜 d : ℕ → Submodule R
     (veronese 𝒜 d)` (degree `k` part `𝒜 (d k)`), `mem_veroneseGrading`, `map_veroneseGrading`,
     `map_veroneseGrading_zero` (the degree-zero part is `𝒜 0`), the `SetLike.GradedMonoid`
     instance, `iSupIndep_veroneseGrading`, `iSup_veroneseGrading_eq_top`,
     `isInternal_veroneseGrading` (for `d ≠ 0`), `instGradedAlgebraVeroneseGrading` (for
     `[NeZero d]`), `coe_decompose_veroneseGrading` (the degree-`k` component is the
     degree-`d k` component in `A`), `veroneseGradingZeroEquiv : veroneseGrading 𝒜 d 0 ≃+* 𝒜 0`
     with `coe_veroneseGradingZeroEquiv`, and `veroneseMap d f : veroneseGrading 𝒜 d →+*ᵍ
     veroneseGrading ℬ d` (the restriction of a graded ring map `f : 𝒜 →+*ᵍ ℬ`) with
     `coe_veroneseMap_apply`.
2. **`feat: homogeneous localizations of a Veronese subalgebra`**. After: 1. *Done on this branch.*
   - File: `TauCeti/RingTheory/GradedAlgebra/HomogeneousLocalization/Veronese.lean` (223 lines).
   - Adds, in `TauCeti.GradedAlgebra`: `NumDenSameDeg.ofVeronese`, `veroneseLocalizationMap`
     with `veroneseLocalizationMap_mk`, `veroneseHomogeneousLocalizationFun` with its `val`
     lemma, `veroneseHomogeneousLocalizationMap` (the ring map from `A^{(d)}` localized at `P` in
     degree zero to `A` localized at `Q ⊇ P` in degree zero) with
     `val_veroneseHomogeneousLocalizationMap`, `powers_le_comap_val_powers`,
     `injective_veroneseHomogeneousLocalizationMap_powers`,
     `surjective_veroneseHomogeneousLocalizationMap_powers`, `awayVeroneseEquiv :
     Away (veroneseGrading 𝒜 d) f ≃+* Away 𝒜 f` for homogeneous `f ∈ A^{(d)}`, with
     `val_awayVeroneseEquiv`, `awayVeroneseEquiv_mk`, `awayVeroneseEquiv_awayMap` (compatibility
     with the transition maps `A_{(f)} → A_{(fg)}`) and `awayVeroneseEquiv_fromZeroRingHom`
     (compatibility with `𝒜 0`), and `awayVeroneseEquiv_awayMap_veroneseMap` (compatibility with
     the maps `Away.map` induced by a graded ring map). These are the affine charts of Stacks 0B5J.
3. **`feat: Proj of a Veronese subalgebra`**. After: 2. *Done on this branch.*
   - Files: `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/Veronese.lean` (303 lines, new) and
     `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean` (+6 lines).
   - Adds, in `AlgebraicGeometry.Proj`: `awayι_congr` (in `Basic.lean`: the chart `awayι` does
     not depend on the degree chosen for `f`), `iSup_basicOpen_veronese_eq_top` (the `D₊(g)`,
     `g ∈ A^{(d)}` homogeneous of positive degree, cover `Proj A`), the charts `veroneseChart :
     Spec A_{(g)} ⟶ Proj A^{(d)}` and `veroneseChartInv : Spec A^{(d)}_{(g)} ⟶ Proj A` with their
     `_congr` and overlap lemmas `SpecMap_awayMap_veroneseChart(Inv)` and
     `pullback_fst_veroneseChart(Inv)`, `veroneseAffineOpenCover`, the glued morphisms
     `toVeronese` and `fromVeronese` with `awayι_toVeronese` and `awayι_fromVeronese`,
     `veroneseIso : Proj (veroneseGrading 𝒜 d) ≅ Proj 𝒜`, and `veroneseIso_hom_toSpecZero` (it
     lies over `Spec 𝒜 0` under `veroneseGradingZeroEquiv`), `veroneseIso_hom_toSpecCoeff` (it lies
     over `Spec R`), and `map_veroneseMap_veroneseIso_hom` (naturality: for a graded ring map
     `f : 𝒜 →+*ᵍ ℬ`, `Proj.map (veroneseMap d f) ≫ (veroneseIso 𝒜 d).hom =
     (veroneseIso ℬ d).hom ≫ Proj.map f`). The last is what lets split 7 glue the chart
     isomorphisms along the restriction maps of the relative `Proj`.
   - The earlier plan built the morphism with `Proj.fromOfGlobalSections`. That does not apply,
     because elements of positive degree are not global sections of `Proj A`. Mathlib's
     `Proj.map` does not apply either: it needs a degree-preserving graded map, and
     `ℬ₊ ≤ 𝒜₊.map f` fails for `A^{(d)} → A`. The isomorphism is glued from the charts instead.
4. **`feat: Veronese subalgebras of graded monoid objects`**. After: none. *Done on this branch.*
   - File: `TauCeti/CategoryTheory/GradedObject/Veronese.lean` (195 lines).
   - Adds, in `CategoryTheory.Mon`: `eqToHom_whiskerRight_mul` and `whiskerLeft_eqToHom_mul`
     (homogeneous multiplication commutes with the transports identifying degrees), the
     homogeneous data `veroneseOne`, `veroneseMul` with their laws
     `veroneseOne_whiskerRight_veroneseMul`, `whiskerLeft_veroneseOne_veroneseMul`,
     `veroneseMul_assoc`, and `veronese A d : Mon (GradedObject ℕ C)` with components
     `A.X (d * k)` (assembled by `GradedObject.monObjOfHomogeneous`), with `veronese_X`,
     (`veroneseOne` and `veroneseMul` are `@[expose]`, so that split 5 can unfold them),
     `veronese_mul`, `veronese_one`. In `CategoryTheory.CommMon`: `veroneseMul_comm` and
     `veronese A d : CommMon (GradedObject ℕ C)`, with `veronese_toMon` and `veronese_X`. For
     `C = X.Modules` this is the Veronese subalgebra `A^{(d)}` of the graded algebra `A` that
     `relativeProj` takes; its components are those of `A`, so it is quasi-coherent when `A` is.
5. **`feat: graded sections of the Veronese subalgebra of a graded quasi-coherent algebra`**.
   After: 1, 4. *Done on this branch.*
   - File: `TauCeti/AlgebraicGeometry/Modules/GradedAlgebra/Veronese.lean` (253 lines).
   - Adds, in `CategoryTheory.CommMon`: the instance `isQuasicoherent_veronese_X`;
     `veroneseSectionsAlgHom : (⨁ k, Γ((A.veronese d).X k, U)) →ₐ[Γ(X, U)] ⨁ n, Γ(A.X n, U)`
     (degree `k` placed in degree `d k`, built with `DirectSum.toAlgebra`) with
     `veroneseSectionsAlgHom_of`, `veroneseSectionsAlgHom_apply_mul`,
     `veroneseSectionsAlgHom_apply_of_not_dvd`, `injective_veroneseSectionsAlgHom` (for `d ≠ 0`),
     `range_veroneseSectionsAlgHom` (the range is `veronese (A.gradedSectionsGrading U) d`),
     `veroneseSectionsEquiv : (⨁ k, Γ((A.veronese d).X k, U)) ≃ₐ[Γ(X, U)]
     veronese (A.gradedSectionsGrading U) d` with `coe_veroneseSectionsEquiv`,
     `veroneseSectionsEquiv_mem_veroneseGrading` and
     `map_veroneseSectionsEquiv_gradedSectionsGrading` (it carries
     `(A.veronese d).gradedSectionsGrading U k` onto `veroneseGrading _ d k`), and
     `veroneseSectionsAlgHom_restrictGradedSections` (naturality in restriction).
6. **`feat: twisting sheaves of Proj of a Veronese subalgebra`**. After: 3. *Remains.*
   - File: `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/Veronese.lean`.
   - Adds: `O_{Proj A^{(d)}}(n) ≅ (veroneseIso).hom^* O_{Proj A}(d n)`, using main's
     `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/*` on the charts of split 3. This
     is the module analogue of `awayVeroneseEquiv`: degree `n` of `M_{(g)}` over `A^{(d)}` is
     degree `d n` of `M_{(g)}` over `A`.
7. **`feat: relative Proj of a Veronese subalgebra`**. After: 1, 2, 3, 4, 5, 6. *Started.*
   Completes the target.
   - File: `TauCeti/AlgebraicGeometry/RelativeProj/Veronese.lean` (110 lines so far).
   - On the branch already, in `CategoryTheory.CommMon`: `veroneseSectionsGradedHom` and
     `veroneseSectionsGradedHomInv` (split 5's `veroneseSectionsEquiv` and its inverse as graded
     ring maps) with `veroneseSectionsGradedHomInv_apply`, `projVeroneseSectionsIso U :
     Proj ((A.veronese d).gradedSectionsGrading U) ≅ Proj (A.gradedSectionsGrading U)`
     (`Proj.mapIso` followed by `Proj.veroneseIso`), and
     `restrict_comp_veroneseSectionsGradedHomInv` (the inverse commutes with restriction, with
     `veroneseMap` of the restriction of `A` on the other side).
   - Still to add: `relativeProjFunctor_map_projVeroneseSectionsIso_hom` (naturality of
     `projVeroneseSectionsIso` along the transition maps of `relativeProjFunctor`), the natural
     isomorphism `relativeProjFunctorVeroneseIso` (`NatIso.ofComponents`), its compatibility with
     `relativeProjToSpec` (from `Proj.map_toSpecCoeff` and `Proj.veroneseIso_hom_toSpecCoeff`),
     and then `CommMon.relativeProjVeroneseIso :
     (A.veronese d).relativeProj ≅ A.relativeProj` over `X` (glued from split 3 over the affine
     opens, using `isPullback_relativeProjCover` and split 5's identification), and
     `relativeProjTwistingSheaf (A.veronese d) n` matching `relativeProjTwistingSheaf A (d * n)`
     under it (from split 6). If this is stated in `QCoh`, it consumes
     `isQuasicoherent_relativeProjTwistingSheaf` from PR #29201 (still open on 2026-11-06; see
     above).

## What is proved and what remains

Proved: for an `ℕ`-graded commutative `R`-algebra `A = ⨁ 𝒜 n` and `d ≠ 0`, the Veronese
subalgebra `⨁ₖ 𝒜 (d k)` is an `ℕ`-graded `R`-algebra with degree-zero part `𝒜 0`. For each
homogeneous `f` in it, `A^{(d)}_{(f)} ≃+* A_{(f)}`, compatibly with the transition maps and with
`𝒜 0`. As a consequence, `Proj.veroneseIso : Proj A^{(d)} ≅ Proj A` holds over `Spec 𝒜 0`. For a
commutative monoid object `A` in `ℕ`-graded objects of a braided monoidal category (in
particular a graded algebra of `O_X`-modules), `CommMon.veronese A d` is its Veronese subalgebra
`⨁ₖ A_{dk}`, with the unit and multiplications of `A`.

Also proved (split 5): over every open `U`, the graded sections `⨁ₖ Γ(A_{dk}, U)` of
`A^{(d)}` are `Γ(X, U)`-isomorphic to the Veronese subalgebra of `⨁ₙ Γ(Aₙ, U)`, degree by
degree and compatibly with restriction (`CommMon.veroneseSectionsEquiv`).

Also proved (split 7, started): the chart isomorphisms
`Proj (⨁ₖ Γ(A_{dk}, U)) ≅ Proj (⨁ₙ Γ(Aₙ, U))` (`CommMon.projVeroneseSectionsIso`), and the
compatibility of the section identification with restriction.

Remaining: split 6, and the rest of split 7 as listed above. The naturality square
`relativeProjFunctor_map_projVeroneseSectionsIso_hom` was written in this session. Its rewrite
chain is `← Category.assoc, ← Proj.map_comp, Proj.map_congr (restrict_comp_...), Proj.map_comp,
Category.assoc, Proj.map_veroneseMap_veroneseIso_hom`, and the needed irrelevant-ideal hypothesis
for `veroneseMap d (A.restrictGradedSectionsGradedHom _)` is transported from
`irrelevant_le_map_comp` through the two section isomorphisms with an explicit `Eq.subst` motive.
The statement times out (heartbeats) as soon as the goal is unfolded, whether by `change` or by
`dsimp only [relativeProjFunctor, projVeroneseSectionsIso, Iso.trans_hom, Proj.mapIso_hom]`,
before any rewrite happens. A `rw [Proj.mapIso_hom]`-style unfolding also fails, because the
graded sections over `(toOpensFunctor X).obj U` and over `U.toOpens` agree only up to defeq. The
next attempt should state the square for `Proj.map` of explicit graded maps over opens `V ≤ U`
first (no `AffineZariskiSite` and no `Iso`), then specialise. It also needs a
`Proj.mapIso`/`Proj.map` lemma for `projVeroneseSectionsIso_hom` stated with `Proj.map`, since
the `toSpecCoeff` compatibility timed out under the module system for the same reason. These are the twisting-sheaf comparison
`O(n)`/`O(dn)` on `Proj`, and the relative statement
`relativeProj_veronese`, glued from `Proj.veroneseIso` over affine opens of the base.
