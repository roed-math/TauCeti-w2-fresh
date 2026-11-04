<!--tauceti-lookahead:v1 {"area":"StableReduction","slug":"relative-ampleness","main":"333c9e49143de812ed1452b412193ee9c05501e7","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"refactor(AlgebraicGeometry/RelativeProj): name the generated-in-degree-one condition"},{"n":2,"after":[],"title":"feat(AlgebraicGeometry/LineBundle): tensor powers of line bundles"},{"n":3,"after":[2],"title":"feat(AlgebraicGeometry/LineBundle): global generation of trivial bundles, pullbacks, tensor products and tensor powers"},{"n":4,"after":[1,2,3],"title":"feat(AlgebraicGeometry/LineBundle): relatively ample and very ample line bundles and projective morphisms"}]}-->
# Lookahead: `relative-ampleness` (StableReduction, Layer 2)

Built on `main` at `333c9e49143de812ed1452b412193ee9c05501e7`. Status: **partial**. Target text
(StableReduction README, Layer 2): "Extend Tau Ceti's invertible-sheaf API with tensor powers,
Cartier divisors, pullback, degree on components, global generation, and relative ampleness.
Build projective morphisms and relative `Proj` of a finitely generated graded quasi-coherent
algebra." The target has no pinned forms in `StableReduction/Suggested.lean`.

## Stubbed declarations: none left

Sixth session (2026-11-04, 00:05 UTC). The supplier `relative-proj-twisting-sheaf`
(SchemeAndStackFoundations §0.3) has landed the part this target consumes, in
`TauCeti/AlgebraicGeometry/RelativeProj/TwistingSheaf.lean` on `main`. The stub file
`TauCeti/Lookahead/RelativeAmpleness/Stubs.lean` is deleted and the proof now uses the landed
declarations. No `sorry` remains anywhere on the branch. The supplier's open PR #27145
(`O(m) ⊗ O(n) ≅ O(m + n)`) is not consumed, so it is not stubbed. `suppliers` in the header is
therefore empty. `SchemeAndStackFoundations/Suggested.lean` pins no Lean signature for this
supplier: grepping it for `twist`, `relativeProj` and `GeneratedInDegreeOne` finds only unrelated
Frobenius-twist declarations.

The earlier stubs and what replaced them:

1. `CategoryTheory.CommMon.relativeProjTwistingSheaf (n : ℤ) : A.relativeProj.Modules`. This is
   now on `main` with the same signature the stub had, which was copied from the earlier
   supplier PR #22384. It is used unchanged.
2. `CategoryTheory.CommMon.isInvertible_relativeProjTwistingSheaf_one (hA : A.IsGeneratedInDegreeOne) :
   isInvertible _ (A.relativeProjTwistingSheaf 1)` (stub). `main` landed the stronger
   ```
   theorem _root_.CategoryTheory.CommMon.isInvertible_relativeProjTwistingSheaf
       (h : ∀ U : X.Opens, IsAffineOpen U →
         Algebra.adjoin (A.gradedSectionsGrading U 0)
           (A.gradedSectionsGrading U 1 : Set (⨁ n, Γ(A.X n, U))) = ⊤)
       (n : ℤ) : AlgebraicGeometry.SheafOfModules.isInvertible A.relativeProj (A.relativeProjTwistingSheaf n)
   ```
   and the proof uses it at `n = 1`.
3. `CategoryTheory.CommMon.IsGeneratedInDegreeOne` (stub, a `sorry` predicate). `main` writes the
   condition inline, as the hypothesis `h` above. Split 1 names it: it adds the predicate
   `CommMon.IsGeneratedInDegreeOne A` with exactly that body, plus `isGeneratedInDegreeOne_iff`,
   and restates `isInvertible_relativeProjTwistingSheaf` with `(h : A.IsGeneratedInDegreeOne)`.
   That theorem has no other users on `main`.

## Changes this session

- The stubs are replaced by `main`'s declarations, and `main` is merged in at `333c9e49143`.
- **Relative ampleness now follows the Stacks Project definition (Tag 01VH).** `main` now has
  absolute ampleness (`LineBundleClass.IsAmple`, #25214). The earlier stand-in definition was
  `InvertibleSheaf.IsRelativelyAmple`, meaning "some positive tensor power is relatively very
  ample". It is replaced by `LineBundleClass.IsRelativelyAmple a f`: `f` is quasi-compact, and
  the pullback of `a` to `f⁻¹ V` is ample for every affine open `V ⊆ S`. Ampleness lives on
  line-bundle classes, and this definition follows that convention. AdicSpacesPartIII
  (README ~l. 3672) expects exactly this definition: it compares it with `IsAmple` over
  `Spec A`. The stand-in's API (`of_tensorPow`, `of_iso`, `pullback`, `isSeparated` and
  `IsRelativelyVeryAmple.isRelativelyAmple`) is removed with it. For the Stacks definition those
  results are real theorems, and they remain to be proved (see below).
- **Relative very ampleness no longer asks for `A₁` of finite type.** This matches Stacks
  Definition 29.38.1, where `ℰ` is only quasi-coherent. `isRelativelyVeryAmple_relativeProjTwistingSheaf`
  therefore loses its `[(A.X 1).IsFiniteType]` argument.
- **Projective morphisms now require `A` of finite type and `A₀` finite**, instead of `A₁` of
  finite type. This is the hypothesis of `main`'s `isProper_relativeProjToBase`. With it, the new
  instance `IsProjective.isProper` proves that projective morphisms are proper. It replaces the
  `IsProjective.isSeparated` instance, since separatedness now follows from properness. The
  definition is still equivalent to Stacks' `ℙ(ℰ)` definition (`ℰ` of finite type): `Sym ℰ`
  satisfies these hypotheses, and conversely `A₁` is finite over `A₀`, hence over `𝒪_S`. The
  reason is that the degree-one components of a finite set of homogeneous algebra generators
  span `A₁` over `A₀`. In addition `Proj_S A` is closed in `ℙ(A₁)`, because the charts
  `A_(f)` only see `A₊`.
- I removed the Stacks tags I could not verify offline (01VM, 01W8, 01WC). Only 01VH is used,
  because the roadmap quotes it.
- Placement: adding `LineBundle/GlobalGeneration/` next to `LineBundle/GlobalGeneration.lean`
  would leave flat siblings. So split 3 moves `main`'s `GlobalGeneration.lean` to
  `GlobalGeneration/Basic.lean` and updates its three importers (`LineBundle/LocalRing.lean`,
  `WeilDivisor/Scheme/GlobalGeneration.lean` and the new files).

## Splits

1. **Name the generated-in-degree-one condition** (after: none). This is a refactor that touches
   only `main` code.
   - File: `TauCeti/AlgebraicGeometry/RelativeProj/TwistingSheaf.lean` (+22/−4).
   - Declarations: `CategoryTheory.CommMon.IsGeneratedInDegreeOne`, `CommMon.isGeneratedInDegreeOne_iff`,
     and `CommMon.isInvertible_relativeProjTwistingSheaf` restated with the new predicate.
   - Roadmap line: `Roadmap: SchemeAndStackFoundations` (§0.3 defines "generated in degree one").
   - Subject: `refactor(AlgebraicGeometry/RelativeProj): name the generated-in-degree-one condition`
2. **Tensor powers of line bundles** (after: none).
   - File: `TauCeti/AlgebraicGeometry/LineBundle/Power.lean` (112 lines, new).
   - Declarations: `InvertibleSheaf.tensorPow`, `tensorPow_zero`, `tensorPow_succ`,
     `LineBundleClass.mk_tensorPow`, `InvertibleSheaf.nonempty_tensorPow_obj_iso`,
     `nonempty_tensorPow_add_iso`, `nonempty_tensorPow_tensorPow_iso`,
     `nonempty_pullback_tensorPow_iso` (all in `TauCeti.AlgebraicGeometry`).
   - Subject: `feat(AlgebraicGeometry/LineBundle): tensor powers of line bundles`
3. **Global generation of trivial bundles, pullbacks, tensor products and tensor powers**
   (after: 2).
   - Files: `TauCeti/CategoryTheory/Monoidal/Closed/Epi.lean` (51 lines, new);
     `TauCeti/AlgebraicGeometry/LineBundle/GlobalGeneration/Pullback.lean` (71, new);
     `TauCeti/AlgebraicGeometry/LineBundle/GlobalGeneration/TensorProduct.lean` (79, new); the move
     `LineBundle/GlobalGeneration.lean` → `LineBundle/GlobalGeneration/Basic.lean` (275, unchanged)
     with its importers `LineBundle/LocalRing.lean` and `WeilDivisor/Scheme/GlobalGeneration.lean`.
   - Declarations: `TauCeti.MonoidalClosed.epi_whiskerRight`, `TauCeti.MonoidalClosed.epi_tensorHom`;
     `InvertibleSheaf.isGloballyGenerated_trivial`, `InvertibleSheaf.IsGloballyGenerated.pullback`,
     `IsGloballyGenerated.tensorProduct`, `IsGloballyGenerated.tensorPow`.
     `CategoryTheory.MonoidalClosed.mono_pre_app` on `main` inlines the argument of
     `epi_whiskerRight`. Switching it over is a separate refactor PR after this split.
   - Subject: `feat(AlgebraicGeometry/LineBundle): global generation of trivial bundles, pullbacks, tensor products and tensor powers`
4. **Relatively ample and very ample line bundles and projective morphisms** (after: 1, 2, 3).
   It imports splits 1 and 2. It comes after split 3 so that it is the split that completes the
   target's global-generation and ampleness layer.
   - File: `TauCeti/AlgebraicGeometry/LineBundle/RelativelyAmple.lean` (225 lines, new).
   - Declarations: `CommMon.relativeProjTwistingSheafOne`; `InvertibleSheaf.IsRelativelyVeryAmple`,
     `IsRelativelyVeryAmple.of_iso`, `isRelativelyVeryAmple_relativeProjTwistingSheaf`,
     `IsRelativelyVeryAmple.pullback`, `IsRelativelyVeryAmple.isSeparated`;
     `LineBundleClass.IsRelativelyAmple` (Stacks 01VH), `IsRelativelyAmple.of_pow`,
     `LineBundleClass.isRelativelyAmple_one_iff` (the trivial class is relatively ample exactly
     for quasi-affine morphisms), `isRelativelyAmple_one` (affine morphisms),
     `isRelativelyAmple_of_pow_eq_one`, `InvertibleSheaf.isRelativelyAmple_of_tensorPow`;
     `IsProjective` (class), `isProjective_relativeProjToBase`, the instance `IsProjective (j ≫ f)`
     for a closed immersion `j`, `IsProjective.exists_isRelativelyVeryAmple`, and the instance
     `IsProjective.isProper`.
   - Subject: `feat(AlgebraicGeometry/LineBundle): relatively ample and very ample line bundles and projective morphisms`

## What is proved and what remains

Proved, with no stubs: tensor powers of line bundles, with their classes, exponent laws and
pullbacks. Global generation of `𝒪_X`, and of pullbacks, tensor products and tensor powers of
globally generated line bundles. Relatively very ample line bundles: `𝒪(1)` is relatively very
ample on `Proj_S A`, relative very ampleness is stable under isomorphism and under pullback along
immersions, and a relatively very ample bundle forces separatedness. Relative ampleness in the
Stacks sense: descent from positive powers, the trivial class and quasi-affine morphisms, affine
morphisms and torsion classes. Projective morphisms: they are closed under precomposition with
closed immersions, they carry a relatively very ample line bundle, and they are **proper**.

Remains for the target:
- **Relatively very ample + quasi-compact ⇒ relatively ample**, and so projective ⇒ the
  pullback of `𝒪(1)` is relatively ample. This needs four things. (a) A section of `𝒪(1)` on a
  chart `Proj R` for each `t ∈ R₁`, with nonvanishing locus `D₊(t)`. (b) The nonvanishing locus
  of a pulled-back section is the preimage of the original locus: `main` has no
  pullback-of-sections API for `Scheme.Modules.pullback`. (c) The restriction of the relative
  `Proj` and of `𝒪(1)` over an affine `V` (from `isPullback_relativeProjCover` and
  `restrictRelativeProjTwistingSheafIso`). (d) For non-closed immersions, the Stacks argument
  that extends sections from `X_s` after multiplying by powers of `s`.
- The converse "`a` relatively ample ⇒ `aⁿ` relatively ample". `IsAmple` on `main` lacks it too
  (`main` has only `IsAmple.of_pow`).
- Over an affine base, relative ampleness ⇔ ampleness. This needs ampleness transported along
  scheme isomorphisms and restricted to quasi-compact opens. Both need (b).
- Relative ampleness is stable under pullback along immersions, and implies separatedness.
- `ℙ(ℰ) = Proj_S(Sym ℰ)` is projective for `ℰ` of finite type. This needs `Sym ℰ` generated in
  degree one on affine sections: on an affine open, sections of `Symⁿ ℰ` are `Symⁿ` of sections.
- Stability of projectivity under composition and base change (Segre embedding and base change
  of the relative `Proj`).
- Cartier divisors and degree on components connected to these notions. Much of this is on
  `main` under `CartierDivisor/` and `LineBundle/Degree.lean`.
- The scheme-theoretic closure of `C ↪ ℙ^N_K` in `ℙ^N_R` as a proper model. Mathlib has no
  `ℙ^N`, and comparing the generic fibre needs the scheme-theoretic image to commute with flat
  base change.
