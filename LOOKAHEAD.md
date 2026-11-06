<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"relative-proj-veronese","main":"afa08a3ed16fb167e35de371afb1eb03fbc5913a","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: the Veronese subalgebra of a graded algebra"},{"n":2,"after":[1],"title":"feat: homogeneous localizations of a Veronese subalgebra"},{"n":3,"after":[2],"title":"feat: Proj of a Veronese subalgebra"},{"n":4,"after":[1],"title":"feat: Veronese subalgebra of a graded quasi-coherent algebra"},{"n":5,"after":[3],"title":"feat: twisting sheaves of Proj of a Veronese subalgebra"},{"n":6,"after":[1,2,3,4,5],"title":"feat: relative Proj of a Veronese subalgebra"}]}-->

# Lookahead: `relative-proj-veronese` (SchemeAndStackFoundations, Layer 0, §0.3)

Target (README §0.3): prove `relativeProj_veronese`: for `d ≥ 1` the Veronese subalgebra
`A^{(d)} = ⊕_k A_{dk}`, which has the same degree-zero part `A_0`, satisfies
`relativeProj A^{(d)} ≅ relativeProj A` over `S`, with `O(n)` corresponding to `O(dn)`
(Stacks, Lemma 27.11.8 (0B5J), on affine charts).

Built on `main` at `afa08a3ed16fb167e35de371afb1eb03fbc5913a`.

**Status: partial.** Splits 1, 2 and 3 are proved on this branch, with no `sorry`: the Veronese
subalgebra, its affine charts, and `Proj A^{(d)} ≅ Proj A` over `Spec 𝒜 0`. The `O(n)`/`O(dn)`
comparison and the relative statement (splits 4 to 6) remain.

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
`main`), and nothing proved so far uses them, so nothing is stubbed. If split 6 states the
`O(n)` comparison in `QCoh` and so needs `isQuasicoherent_relativeProjTwistingSheaf`, then
split 6 has to wait for #29201 to land and should use the landed instance, which PR #29201's diff
states as:

```lean
instance _root_.CategoryTheory.CommMon.isQuasicoherent_relativeProjTwistingSheaf (n : ℤ) :
```

(that is, `(A.relativeProjTwistingSheaf n).IsQuasicoherent`). The roadmap's `Suggested.lean`
pins nothing for this supplier: the README says the relative Proj and its comparisons are
specified in the README only.

## Split plan

1. **`feat: the Veronese subalgebra of a graded algebra`**. After: none. *Done on this branch.*
   - File: `TauCeti/RingTheory/GradedAlgebra/VeroneseSubalgebra.lean` (177 lines).
   - Adds, in `TauCeti.GradedAlgebra`: `veronese 𝒜 d : Subalgebra R A` (the span of the
     `𝒜 (d k)`), `mem_veronese`, `mem_veronese_of_mem`, `veroneseGrading 𝒜 d : ℕ → Submodule R
     (veronese 𝒜 d)` (degree `k` part `𝒜 (d k)`), `mem_veroneseGrading`, `map_veroneseGrading`,
     `map_veroneseGrading_zero` (the degree-zero part is `𝒜 0`), the `SetLike.GradedMonoid`
     instance, `iSupIndep_veroneseGrading`, `iSup_veroneseGrading_eq_top`,
     `isInternal_veroneseGrading` (for `d ≠ 0`), `instGradedAlgebraVeroneseGrading` (for
     `[NeZero d]`), `coe_decompose_veroneseGrading` (the degree-`k` component is the
     degree-`d k` component in `A`), and `veroneseGradingZeroEquiv : veroneseGrading 𝒜 d 0 ≃+* 𝒜 0`
     with `coe_veroneseGradingZeroEquiv`.
2. **`feat: homogeneous localizations of a Veronese subalgebra`**. After: 1. *Done on this branch.*
   - File: `TauCeti/RingTheory/GradedAlgebra/HomogeneousLocalization/Veronese.lean` (210 lines).
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
     (compatibility with `𝒜 0`). These are the affine charts of Stacks 0B5J.
3. **`feat: Proj of a Veronese subalgebra`**. After: 2. *Done on this branch.*
   - Files: `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/Veronese.lean` (252 lines, new) and
     `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean` (+6 lines).
   - Adds, in `AlgebraicGeometry.Proj`: `awayι_congr` (in `Basic.lean`: the chart `awayι` does
     not depend on the degree chosen for `f`), `iSup_basicOpen_veronese_eq_top` (the `D₊(g)`,
     `g ∈ A^{(d)}` homogeneous of positive degree, cover `Proj A`), the charts `veroneseChart :
     Spec A_{(g)} ⟶ Proj A^{(d)}` and `veroneseChartInv : Spec A^{(d)}_{(g)} ⟶ Proj A` with their
     `_congr` and overlap lemmas `SpecMap_awayMap_veroneseChart(Inv)` and
     `pullback_fst_veroneseChart(Inv)`, `veroneseAffineOpenCover`, the glued morphisms
     `toVeronese` and `fromVeronese` with `awayι_toVeronese` and `awayι_fromVeronese`,
     `veroneseIso : Proj (veroneseGrading 𝒜 d) ≅ Proj 𝒜`, and `veroneseIso_hom_toSpecZero` (it
     lies over `Spec 𝒜 0` under `veroneseGradingZeroEquiv`).
   - The earlier plan built the morphism with `Proj.fromOfGlobalSections`. That does not apply,
     because elements of positive degree are not global sections of `Proj A`. Mathlib's
     `Proj.map` does not apply either: it needs a degree-preserving graded map, and
     `ℬ₊ ≤ 𝒜₊.map f` fails for `A^{(d)} → A`. The isomorphism is glued from the charts instead.
4. **`feat: Veronese subalgebra of a graded quasi-coherent algebra`**. After: 1. *Remains.*
   - File: `TauCeti/AlgebraicGeometry/Modules/GradedAlgebra/Veronese.lean`.
   - Adds: `CategoryTheory.CommMon.veronese A d : CommMon (GradedObject ℕ X.Modules)` with
     components `A.X (d * k)`, quasi-coherent when `A`'s are, and the identification of its
     graded sections over an affine open `U` with `veroneseGrading` of
     `A.gradedSectionsGrading U`, natural in restriction to basic opens.
5. **`feat: twisting sheaves of Proj of a Veronese subalgebra`**. After: 3. *Remains.*
   - File: `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/Veronese.lean`.
   - Adds: `O_{Proj A^{(d)}}(n) ≅ (veroneseIso).hom^* O_{Proj A}(d n)`, using main's
     `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/*` on the charts of split 3. This
     is the module analogue of `awayVeroneseEquiv`: degree `n` of `M_{(g)}` over `A^{(d)}` is
     degree `d n` of `M_{(g)}` over `A`.
6. **`feat: relative Proj of a Veronese subalgebra`**. After: 1, 2, 3, 4, 5. *Remains.*
   Completes the target.
   - File: `TauCeti/AlgebraicGeometry/RelativeProj/Veronese.lean`.
   - Adds: `CategoryTheory.CommMon.relativeProjVeroneseIso :
     (A.veronese d).relativeProj ≅ A.relativeProj` over `X` (glued from split 3 over the affine
     opens, using `isPullback_relativeProjCover` and split 4's identification), and
     `relativeProjTwistingSheaf (A.veronese d) n` matching `relativeProjTwistingSheaf A (d * n)`
     under it (from split 5). If this is stated in `QCoh`, it consumes
     `isQuasicoherent_relativeProjTwistingSheaf` from PR #29201 (see above).

## What is proved and what remains

Proved: for an `ℕ`-graded commutative `R`-algebra `A = ⨁ 𝒜 n` and `d ≠ 0`, the Veronese
subalgebra `⨁ₖ 𝒜 (d k)` is an `ℕ`-graded `R`-algebra with degree-zero part `𝒜 0`. For each
homogeneous `f` in it, `A^{(d)}_{(f)} ≃+* A_{(f)}`, compatibly with the transition maps and with
`𝒜 0`. As a consequence, `Proj.veroneseIso : Proj A^{(d)} ≅ Proj A` holds over `Spec 𝒜 0`.

Remaining: splits 4, 5 and 6 as described above. These are the Veronese subalgebra of a graded
quasi-coherent algebra, the twisting-sheaf comparison `O(n)`/`O(dn)` on `Proj`, and the relative
statement `relativeProj_veronese`, glued from `Proj.veroneseIso` over affine opens of the base.
