<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"relative-proj-veronese","main":"7ac4960977499bb4976656e7658c457204e14c04","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: the Veronese subalgebra of a graded algebra"},{"n":2,"after":[1],"title":"feat: homogeneous localizations of a Veronese subalgebra"},{"n":3,"after":[2],"title":"feat: Proj of a Veronese subalgebra"},{"n":4,"after":[],"title":"feat: Veronese subalgebras of graded monoid objects"},{"n":5,"after":[1,4],"title":"feat: graded sections of the Veronese subalgebra of a graded quasi-coherent algebra"},{"n":6,"after":[1],"title":"feat: pulling back twisting sheaf sections along the Veronese contraction"},{"n":7,"after":[3,6],"title":"feat: twisting sheaves of Proj of a Veronese subalgebra"},{"n":8,"after":[1,2,3,4,5],"title":"feat: relative Proj of a Veronese subalgebra"},{"n":9,"after":[1,2,3,4,5,6,7,8],"title":"feat: twisting sheaves of the relative Proj of a Veronese subalgebra"}]}-->

# Lookahead: `relative-proj-veronese` (SchemeAndStackFoundations, Layer 0, §0.3)

Target (README §0.3): prove `relativeProj_veronese`: for `d ≥ 1` the Veronese subalgebra
`A^{(d)} = ⊕_k A_{dk}`, which has the same degree-zero part `A_0`, satisfies
`relativeProj A^{(d)} ≅ relativeProj A` over `S`, with `O(n)` corresponding to `O(dn)`
(Stacks, Lemma 27.11.8 (0B5J), on affine charts).

Built on `main` at `7ac49609774` (merged into the branch on 2026-11-06 at the eighth session;
the merge was clean and no new declaration on `main` duplicates one of this branch: `main`'s
`TauCeti/RingTheory/GradedAlgebra/Veronese.lean` is about generation of Veronese subrings, not the
subalgebra itself). PR #29201 was still open at the eighth session.

**Status: partial.** Splits 1 to 6 and 8 are proved on this branch, with no `sorry`: the
Veronese subalgebra and its functoriality in graded ring maps, its affine charts,
`Proj A^{(d)} ≅ Proj A` over `Spec 𝒜 0` and over `Spec R`, natural in graded ring maps, the
sheaf-level Veronese subalgebra `A^{(d)}` of a graded (commutative) monoid object, the
identification of its graded sections over an open with the Veronese subalgebra of the graded
sections of `A`, and **the isomorphism of relative `Proj`s
`CommMon.relativeProjVeroneseIso : Proj_X(A^{(d)}) ≅ Proj_X(A)` over `X`**, and (split 6) the
pullback of sections `Γ(U, O_{Proj A^{(d)}}(n)) → Γ(V, O_{Proj A}(dn))` along the contraction
`q ↦ q ∩ A^{(d)}`, bijective over every standard open `D₊(g)`. Split 7 is proved up to its last step: **the
isomorphism `Proj.twistingSheafVeroneseIso : 𝒪_{Proj A^{(d)}}(n) ≅ (toVeronese)_* 𝒪_{Proj A}(d n)`
of sheaves of modules on `Proj`**. What remains is the compatibility of that isomorphism with
`Proj.twistingSheafMap` (split 7, step 5) and split 9 on the relative `Proj`.

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
`main`), and nothing proved so far uses them, so nothing is stubbed. If split 9 states the
`O(n)` comparison in `QCoh` and so needs `isQuasicoherent_relativeProjTwistingSheaf`, then
split 9 has to wait for #29201 to land and should use the landed instance, which PR #29201's diff
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
   - Files: `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/Veronese.lean` (339 lines, new) and
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
     (veroneseIso ℬ d).hom ≫ Proj.map f`). The last is what lets split 8 glue the chart
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
6. **`feat: pulling back twisting sheaf sections along the Veronese contraction`**. After: 1.
   *Done on this branch.*
   - File: `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/Veronese.lean` (263 lines).
     It imports only split 1 and main's `TwistingSheaf/BasicOpen`, so it can open alongside
     splits 2 to 5.
   - Adds, in `AlgebraicGeometry.ProjectiveSpectrum`: `veroneseComapFun` and the continuous map
     `veroneseComap 𝒜 d : C(ProjectiveSpectrum 𝒜, ProjectiveSpectrum (veroneseGrading 𝒜 d))`,
     `q ↦ q ∩ A^{(d)}` (relevance: if `a ∈ 𝒜 i`, `i > 0`, then `a ^ d` lies in degree `i` of
     `A^{(d)}`), with `veroneseComap_asHomogeneousIdeal_toIdeal`. In `…TwistingSheaf`:
     `veroneseLocalizationsMap q : A^{(d)}_{q ∩ A^{(d)}} →+* A_q` with
     `veroneseLocalizationsMap_mk`, `comapVeroneseFun` and `isLocallyFraction_comapVeroneseFun`
     (a local fraction of degree `n` over `A^{(d)}` is one of degree `d n` over `A`). In
     `AlgebraicGeometry.Proj.twistingSheaf`: `comapVeronese hUV : Γ(U, 𝒪_{Proj A^{(d)}}(n)) →+
     Γ(V, 𝒪_{Proj A}(d n))` for `V ⊆ veroneseComap ⁻¹' U`, with `comapVeronese_apply`,
     `res_comapVeronese`, `comapVeronese_res`, `comapVeronese_const`, `comapVeronese_mul_apply`,
     `basicOpen_subset_preimage_veroneseComap`, and `bijective_comapVeronese_basicOpen` (for
     `g ∈ A^{(d)}` homogeneous of positive degree, the pullback over `D₊(g)` is bijective; proved
     from main's `exists_eq_const_basicOpen` and `const_eq_zero_iff` on both sides).
7. **`feat: twisting sheaves of Proj of a Veronese subalgebra`**. After: 3, 6. *Started.*
   - File: `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/VeroneseIso.lean`
     (currently 303 lines). It also imports main's `TauCeti/AlgebraicGeometry/Modules/Sheaf.lean`
     (for `Scheme.Modules.Hom.isIso_of_isBasis`).
   - Adds, in `AlgebraicGeometry.Proj`:
     1. *Done:* `toVeronese_apply` (the underlying map of `toVeronese 𝒜 d` is
        `ProjectiveSpectrum.veroneseComap 𝒜 d`; proved from split 3's
        `toVeronese_preimage_basicOpen`: both primes contain the same homogeneous elements of
        positive degree, and multiplying by a `g ∈ A^{(d)}` missed by both reduces every degree
        to a positive one), with `coe_toVeronese_preimage` (`toVeronese⁻¹ U` is
        `veroneseComap⁻¹ U`, which is the inclusion `comapVeronese` needs) and
        `veroneseComap_fromVeronese_apply`.
     2. *Done:* `awayToSection_comp_awayι_appLE` (Mathlib objects only: `awayToSection 𝒜 f ≫
        (awayι 𝒜 f _ _).appLE (D₊ f) ⊤ _ = (ΓSpecIso _).inv`) and
        `awayToSection_comp_toVeronese_appLE` (the analogue of Mathlib's
        `awayToSection_comp_appLE` for `toVeronese`: on sections over `D₊(g)`, `toVeronese` is
        `awayToSection ∘ awayVeroneseEquiv`). *Port note:* `awayToSection_comp_awayι_appLE` is a
        general fact about `Proj`; the port should move it to
        `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean` (split 3, which already edits
        that file) and let `chartSectionsEquiv_awayToSection` in
        `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/ProjectiveLine.lean`, whose `suffices`
        repeats the same argument for the coordinate charts, use it. It was left in this file this
        session only because editing `Basic.lean` rebuilds most of the library.
     3. *Done:* `isBasis_basicOpen_veronese` (the `D₊(g)`, `g ∈ A^{(d)}` homogeneous of positive
        degree, form a basis of `Proj A^{(d)}`: for `x ∈ D₊(f) ⊆ U`, take a homogeneous component
        of `f` not in `x` times a `g₀` with `fromVeronese x ∈ D₊(g₀)`), and
        `val_toVeronese_appLE_apply` (the analogue of main's `val_map_appLE_apply`:
        `(toVeronese 𝒜 d).appLE U V _ a` is pointwise `veroneseLocalizationsMap` of `a`), proved
        by restricting to such a `D₊(g)`, writing `a` there as `awayToSection c`, and applying
        step 2. Then `twistingSheaf.comapVeronese_smul` (linearity over `toVeronese`).
     4. *Done:* `twistingSheafVeroneseMap 𝒜 d n : twistingSheaf (veroneseGrading 𝒜 d) n ⟶
        (Scheme.Modules.pushforward (toVeronese 𝒜 d)).obj (twistingSheaf 𝒜 (d * n))` (given on
        sections by `comapVeronese` along `coe_toVeronese_preimage`, built like main's
        `twistingSheafMap`) with `twistingSheafVeroneseMap_app`, the instance
        `isIso_twistingSheafVeroneseMap` (from `bijective_comapVeronese_basicOpen` on the basis
        of step 3, through main's `Scheme.Modules.Hom.isIso_of_isBasis`), and
        `twistingSheafVeroneseIso` (its `asIso`).
     5. *Remains:* its compatibility with `Proj.twistingSheafMap` of `veroneseMap d f` versus
        `f`, using `map_veroneseMap_veroneseIso_hom` (split 3); split 9 needs it to glue.
8. **`feat: relative Proj of a Veronese subalgebra`**. After: 1, 2, 3, 4, 5. *Done on this branch.*
   - File: `TauCeti/AlgebraicGeometry/RelativeProj/Veronese.lean` (229 lines).
   - Adds, in `CategoryTheory.CommMon`: `veroneseSectionsGradedHom` and
     `veroneseSectionsGradedHomInv` (split 5's `veroneseSectionsEquiv` and its inverse as graded
     ring maps) with `veroneseSectionsGradedHomInv_apply`, `projVeroneseSectionsIso U :
     Proj ((A.veronese d).gradedSectionsGrading U) ≅ Proj (A.gradedSectionsGrading U)`
     (`Proj.mapIso` followed by `Proj.veroneseIso`) with `projVeroneseSectionsIso_hom` and
     `projVeroneseSectionsIso_hom_toSpecCoeff` (it lies over `Spec Γ(X, U)`),
     `restrict_comp_veroneseSectionsGradedHomInv` (the inverse commutes with restriction),
     `map_restrict_projVeroneseSectionsIso_hom` (naturality along restriction, stated for
     `Proj.map` of explicit graded maps over opens `V ≤ U`),
     `relativeProjFunctorVeroneseIso : (A.veronese d).relativeProjFunctor ≅ A.relativeProjFunctor`
     (`NatIso.ofComponents`), **`relativeProjVeroneseIso : (A.veronese d).relativeProj ≅
     A.relativeProj`** (`@[stacks 0B5J]`, `HasColimit.isoOfNatIso`),
     `relativeProjCover_f_relativeProjVeroneseIso_hom` (on charts it is `projVeroneseSectionsIso`)
     and `relativeProjVeroneseIso_hom_relativeProjToBase` (it lies over `X`).
9. **`feat: twisting sheaves of the relative Proj of a Veronese subalgebra`**. After: 1, 2, 3, 4,
   5, 6, 7, 8. *Remains.* Completes the target.
   - File: `TauCeti/AlgebraicGeometry/RelativeProj/TwistingSheaf/Veronese.lean`.
   - Adds, in `CategoryTheory.CommMon`: `relativeProjTwistingSheafVeroneseIso d n :
     (A.veronese d).relativeProjTwistingSheaf n ≅
       (A.relativeProjVeroneseIso d).hom^* (A.relativeProjTwistingSheaf (d * n))`, glued from
     split 7 over the charts. `relativeProjTwistingSheaf` is the glued module of
     `relativeProjTwistingSheafGlueData` (on `main`), so the isomorphism is a morphism of
     `ModulesGlueData` along `relativeProjFunctorVeroneseIso`, whose naturality is split 7's
     compatibility with `twistingSheafMap` plus `restrict_comp_veroneseSectionsGradedHomInv`.
     If stated in `QCoh`, it consumes `isQuasicoherent_relativeProjTwistingSheaf` from PR #29201
     (still open on 2026-11-06; see above).

## What is proved and what remains

Proved: for an `ℕ`-graded commutative `R`-algebra `A = ⨁ 𝒜 n` and `d ≠ 0`, the Veronese
subalgebra `⨁ₖ 𝒜 (d k)` is an `ℕ`-graded `R`-algebra with degree-zero part `𝒜 0`. For each
homogeneous `f` in it, `A^{(d)}_{(f)} ≃+* A_{(f)}`, compatibly with the transition maps and with
`𝒜 0`. As a consequence, `Proj.veroneseIso : Proj A^{(d)} ≅ Proj A` holds over `Spec 𝒜 0`,
naturally in graded ring maps. For a graded algebra `A` of `O_X`-modules with quasi-coherent
components, `CommMon.veronese A d` is its Veronese subalgebra `⨁ₖ A_{dk}`, its graded sections
over every open are the Veronese subalgebra of the graded sections of `A` (compatibly with
restriction), and `CommMon.relativeProjVeroneseIso : Proj_X(A^{(d)}) ≅ Proj_X(A)` holds over `X`
(`relativeProjVeroneseIso_hom_relativeProjToBase`).

Also proved (split 6): the contraction `q ↦ q ∩ A^{(d)}` is a continuous map
`Proj A → Proj A^{(d)}`, and pulling back local fractions along it gives maps
`Γ(U, O_{Proj A^{(d)}}(n)) → Γ(V, O_{Proj A}(dn))`, compatible with restriction, fractions and
products, and bijective over every standard open `D₊(g)`, `g ∈ A^{(d)}` homogeneous of positive
degree.

Also proved (split 7, steps 1 to 4): `Proj.toVeronese` is `veroneseComap` on points
(`toVeronese_apply`), `toVeronese⁻¹ D₊(a) = D₊(a)` (`toVeronese_preimage_basicOpen`, split 3),
on sections over `D₊(g)` it is `awayToSection ∘ awayVeroneseEquiv`
(`awayToSection_comp_toVeronese_appLE`), on all sections it is pointwise the map of localizations
(`val_toVeronese_appLE_apply`), and on `Proj` the twisting sheaves correspond:
`Proj.twistingSheafVeroneseIso 𝒜 d n : 𝒪_{Proj A^{(d)}}(n) ≅ (toVeronese)_* 𝒪_{Proj A}(d n)`.

Remaining: (a) split 7 step 5, the compatibility of `twistingSheafVeroneseMap` with
`Proj.twistingSheafMap` of `veroneseMap d f` versus `f` (on sections both are pullbacks of local
fractions, so it should reduce to `Localization.localRingHom` composition lemmas as in main's
`twistingSheafMap_comp`, plus `map_veroneseMap_veroneseIso_hom`); (b) split 9, gluing the chart
isomorphisms `twistingSheafVeroneseIso` of the `Proj (A.gradedSectionsGrading U)` along
`relativeProjFunctorVeroneseIso` into `relativeProjTwistingSheafVeroneseIso`, as listed above.

Lessons for the next session: (eighth session) the session only merged `main` and rebuilt;
for step 5, `twistingSheafMap` (main's `TwistingSheaf/Functor.lean`) is built from
`localizationsMap`, whose fibres are indexed by `Proj.map` of the point, so state the pointwise
identity `veroneseLocalizationsMap ∘ localizationsMap (veroneseMap d f) = localizationsMap f ∘
veroneseLocalizationsMap` on `Localization.mk` first (both sides are induced by the same ring map
`A^{(d)} → B`), then lift to sections with `twistingSheaf.ext` as in `twistingSheafMap_comp`.
(seventh session) in `val_toVeronese_appLE_apply`, `rw` with the
`ConcreteCategory.congr_hom` forms of `appLE_map`/`map_appLE` fails (motive not type correct);
chaining them through local `ev`/`res` evaluation lemmas with `Eq.trans` works, and the final
fraction identity closes by `exact` against `veroneseLocalizationsMap_mk`. Transport along
`toVeronese⁻¹ᵁ D₊(g) = D₊(g)` (propositional only) by a local `rintro _ rfl` lemma.
`/opt/round/lookahead-check` takes about 8 minutes; budget for it.

(sixth session) `rw` of `Scheme.Hom.appTop` and `rfl` closing
`appLE … ≫ appLE … = appLE … ≫ appTop …` time out at `whnf`; `congr 1` closes the latter, and
`awayι_toVeronese` is rewritten inside `appLE` through a local congruence lemma (`hcongr` in
`awayToSection_comp_toVeronese_appLE`), since the inclusion proof `appLE` carries blocks `rw`.

Earlier lessons:Earlier lessons: `rw` and `dsimp` on goals involving `Proj.map` of the section maps
time out (heartbeats) at `whnf`, as do `▸` and `rw … at` on the irrelevant-ideal hypotheses.
Term-mode chains of `Eq.trans`, `congrArg` and `Category.assoc` (as in
`map_restrict_projVeroneseSectionsIso_hom`) elaborate in seconds, and lemmas stated over
`X.Opens` specialise to `AffineZariskiSite` by `(toOpensFunctor X).map i` without unfolding.
In `TwistingSheaf/Veronese.lean`, `rw [comapVeronese_const]` fails ("motive is not type correct at
implicit transparency") on sections produced by `exists_eq_const_basicOpen`, whose `hU` proofs
mention `x.asHomogeneousIdeal` for points of `Proj`; use `(comapVeronese_const ..).trans` instead,
and state preimage inclusions as named lemmas (`basicOpen_subset_preimage_veroneseComap`) rather
than `fun _ hq ↦ hq`.
