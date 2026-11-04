<!--tauceti-lookahead:v1 {"area":"StableReduction","slug":"relative-ampleness","main":"333c9e49143de812ed1452b412193ee9c05501e7","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"refactor(AlgebraicGeometry/RelativeProj): name the generated-in-degree-one condition"},{"n":2,"after":[],"title":"feat(AlgebraicGeometry/LineBundle): tensor powers of line bundles"},{"n":3,"after":[2],"title":"feat(AlgebraicGeometry/LineBundle): global generation of trivial bundles, pullbacks, tensor products and tensor powers"},{"n":4,"after":[2,3],"title":"feat(AlgebraicGeometry/LineBundle): ampleness under pullback by affine open immersions, powers, and products with globally generated bundles"},{"n":5,"after":[4],"title":"feat(AlgebraicGeometry/ProjectiveSpectrum): the twisting sheaf O(1) is ample on a quasi-compact Proj"},{"n":6,"after":[1,2,3,4,5],"title":"feat(AlgebraicGeometry/LineBundle): relatively ample and very ample line bundles and projective morphisms"}]}-->
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

## Changes in the ninth session (2026-11-04, 01:35 UTC)

- `main` is unchanged at `333c9e49143`, so there is nothing new to merge.
- **Nonvanishing loci of tensor products.** `Scheme.Modules.exists_nonvanishingLocus_tensorProduct_eq_inf`:
  for sections `s`, `t` of invertible `M`, `N` over `U`, the sheafified pure tensor `s ⊗ t` is a
  section of `M ⊗ N` with `X_{s ⊗ t} = X_s ∩ X_t`. The proof uses `main`'s stalk comparison
  `SheafOfModules.tensorStalkEquiv` and the rank-one stalks. `InvertibleSheaf.exists_nonvanishingLocus_tensorProduct`
  restates it for `InvertibleSheaf.tensorProduct`. Both are stated existentially on purpose:
  `main`'s lax monoidal sections functor `Scheme.Modules.sectionsFunctor` already has a tensor map
  `μ`, and the sheafified pure tensor agrees with it only through the unexposed
  `SheafOfModules.tensorUnderlyingIso`. A new named section would duplicate `μ`, and stating the
  theorem for `μ` needs a bridge lemma `main` lacks.
- **On an affine open, nonvanishing loci are affine** (`IsAffineOpen.nonvanishingLocus`, via
  Mathlib's `isAffineOpen_of_isAffineOpen_basicOpen`).
- **Ampleness is stable under positive powers** (`LineBundleClass.IsAmple.pow`,
  `isAmple_pow_iff`). This closes the earlier remaining item "`a` relatively ample ⇒ `aⁿ`
  relatively ample" (`IsRelativelyAmple.pow`, `isRelativelyAmple_pow_iff`). With it,
  `InvertibleSheaf.isRelativelyAmple_of_tensorPow` became the iff `isRelativelyAmple_tensorPow_iff`;
  the old one-directional name is removed.
- **Ample times globally generated is ample** (`IsAmple.mul_mk_of_isGloballyGenerated`), and the
  same holds for relative ampleness (`IsRelativelyAmple.mul_mk_of_isGloballyGenerated`).
- **`𝒪(1)` is ample on a quasi-compact `Proj`.** The new file
  `ProjectiveSpectrum/TwistingSheaf/Ample.lean` proves that `X_{r/1} = D₊(r)` for `r` of degree
  one (`Proj.nonvanishingLocus_toTwistingSheaf`, when the degree-one standard opens cover). It
  derives `Proj.isAmple_twistingSheaf_one`, and `Proj.isAmple_twistingSheaf` for `𝒪(n)`, `n > 0`.
- **`𝒪(1)` is relatively ample on a quasi-compact relative `Proj`**
  (`LineBundleClass.isRelativelyAmple_relativeProjTwistingSheafOne`). Over an affine `V`, the
  chart `Proj (⨁ n, Γ(Aₙ, V))` is the preimage of `V` (`relativeProjToBase_preimage`), and
  `𝒪(1)` restricts to the chart's `𝒪(1)` (`restrictRelativeProjTwistingSheafIso`). This is the
  identity case of "relatively very ample + quasi-compact ⇒ relatively ample". If `A` is of
  finite type with `A₀` finite, the structure morphism is proper by `main`'s
  `isProper_relativeProjToBase`, so the hypothesis holds.
- Split 4 now carries the ampleness API of the seventh and ninth sessions. The Proj result is
  the new split 5. The relative file is split 6 and still completes the target.
- Kernel-time note for the port. In `isRelativelyAmple_relativeProjTwistingSheafOne`, do not
  ascribe the chart map the type `Proj (A.gradedSectionsGrading V) ⟶ A.relativeProj`. That
  ascription makes the kernel unfold the glued cover and takes about 35 s. Leaving its type as
  `A.relativeProjCover.f U` takes about 2 s.
- Verified: `lake build` green, `lookahead-check` ok, and `#lint in TauCeti` over the import
  closure of `RelativelyAmple.lean` passes all 15 linters. `scripts/lint-style.sh` needs `uvx`,
  which this sandbox lacks. Instead I checked the changed files by grep: no combining marks, no
  trailing whitespace.

## Changes in the eighth session (2026-11-04, 01:15 UTC)

- `main` is unchanged at `333c9e49143`, so there is nothing new to merge.
- **Over an affine base, relative ampleness is ampleness** (`LineBundleClass.isRelativelyAmple_iff_isAmple`).
  This closes the remaining item "over an affine base, ampleness ⇒ relative ampleness". The
  earlier note expected Stacks' extension of sections from `X_s`, but the argument is short. For
  `V` an affine open of a separated base, `V ⟶ S` is an affine morphism. Its base change, the
  inclusion of `f⁻¹ V`, is then an affine open immersion. Ampleness pulls back along such a map
  (split 4). So `LineBundleClass.IsAmple.isRelativelyAmple` holds more generally: if `S` is
  separated and `f` is quasi-compact, an ample class is relatively ample for `f`.
- **Relative ampleness is preserved by pullback along affine open immersions**
  (`IsRelativelyAmple.pullback_of_isOpenImmersion`). `isRelativelyAmple_pullback_iff_of_isIso`
  is now a two-line corollary of it, replacing the earlier direct proof.
- **Relative ampleness is preserved by composition with an affine morphism**
  (`IsRelativelyAmple.comp`), **and it restricts to opens of the base**
  (`IsRelativelyAmple.restrict`: `a ∣_{f⁻¹ U}` is relatively ample for `f ∣_ U`). The second is
  one direction of locality on the base.
- All of this is in `RelativelyAmple.lean` (now the last split).

## Changes in the seventh session (2026-11-04, 00:50 UTC)

- `main` is unchanged at `333c9e49143`, so there is nothing new to merge.
- **The nonvanishing locus of a section pulled back along an open immersion is the preimage.**
  This proves remaining item (b) below for open immersions. The new theorem
  `Scheme.Modules.nonvanishingLocus_restrictAppIso_inv` sits at the end of `main`'s
  `LineBundle/NonvanishingLocus.lean`. The proof works on sections, using
  `le_nonvanishingLocus_iff`, and needs no stalk comparison.
- **Ampleness is preserved by pullback along affine open immersions.**
  `LineBundleClass.IsAmple.pullback_of_isOpenImmersion` and
  `isAmple_pullback_iff_of_isIso` are added to `main`'s `LineBundle/Ample.lean`, which now imports
  `LineBundle/Functoriality.lean`.
- **Over an affine base, relative ampleness implies ampleness**
  (`LineBundleClass.IsRelativelyAmple.isAmple`). **Relative ampleness is invariant under
  isomorphisms of the source over the base** (`isRelativelyAmple_pullback_iff_of_isIso`). Both are
  in `RelativelyAmple.lean`.
- The new material is part of split 4.

## Changes in the sixth session

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
4. **Stability of ampleness** (after: 2, 3). It changes only `main` files: +171/−2 in
   `LineBundle/NonvanishingLocus.lean` and +99/−2 in `LineBundle/Ample.lean` (about 270 lines).
   `Ample.lean` now imports `LineBundle/Functoriality.lean` and
   `LineBundle/GlobalGeneration/TensorProduct.lean` (split 3). `NonvanishingLocus.lean` now
   imports `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
   `Algebra/Category/ModuleCat/Sheaf/TensorProduct/Stalk.lean` and `LineBundle/TensorProduct.lean`.
   - Declarations in `NonvanishingLocus.lean`: `AlgebraicGeometry.IsAffineOpen.nonvanishingLocus`;
     `Scheme.Modules.nonvanishingLocus_restrictAppIso_inv` (the nonvanishing locus of
     `(M.restrictAppIso f U).inv s` is `f ⁻¹ᵁ M.nonvanishingLocus s` along an open immersion `f`);
     `Scheme.Modules.exists_nonvanishingLocus_tensorProduct_eq_inf`;
     `TauCeti.AlgebraicGeometry.InvertibleSheaf.exists_nonvanishingLocus_tensorProduct`.
   - Declarations in `Ample.lean` (namespace `TauCeti.AlgebraicGeometry.LineBundleClass`):
     `IsAmple.pullback_of_isOpenImmersion` (`[IsOpenImmersion e] [IsAffineHom e]`),
     `isAmple_pullback_iff_of_isIso`, `IsAmple.pow`, `isAmple_pow_iff` (simp),
     `IsAmple.mul_mk_of_isGloballyGenerated`.
   - Subject: `feat(AlgebraicGeometry/LineBundle): ampleness under pullback by affine open immersions, powers, and products with globally generated bundles`
5. **`𝒪(1)` is ample on a quasi-compact `Proj`** (after: 4).
   - File: `TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/Ample.lean` (111 lines,
     new; imports `LineBundle/Ample.lean` and `ProjectiveSpectrum/TwistingSheaf/TensorProduct.lean`).
   - Declarations (namespace `AlgebraicGeometry.Proj`, like the neighbouring twisting-sheaf
     files): `nonvanishingLocus_toTwistingSheaf`, `isAmple_twistingSheaf_one`,
     `isAmple_twistingSheaf`.
   - Subject: `feat(AlgebraicGeometry/ProjectiveSpectrum): the twisting sheaf O(1) is ample on a quasi-compact Proj`
6. **Relatively ample and very ample line bundles and projective morphisms** (after: 1, 2, 3, 4,
   5). It imports splits 1, 4 and 5, and through them 2 and 3. It is the only split that
   completes the target's relative-ampleness layer.
   - File: `TauCeti/AlgebraicGeometry/LineBundle/RelativelyAmple.lean` (399 lines, new).
   - Declarations: `CommMon.relativeProjTwistingSheafOne`; `InvertibleSheaf.IsRelativelyVeryAmple`,
     `IsRelativelyVeryAmple.of_iso`, `isRelativelyVeryAmple_relativeProjTwistingSheaf`,
     `IsRelativelyVeryAmple.pullback`, `IsRelativelyVeryAmple.isSeparated`;
     `LineBundleClass.IsRelativelyAmple` (Stacks 01VH), `IsRelativelyAmple.of_pow`,
     `IsRelativelyAmple.pow`, `isRelativelyAmple_pow_iff` (simp),
     `IsRelativelyAmple.mul_mk_of_isGloballyGenerated`, `IsRelativelyAmple.isAmple` (over an
     affine base), `IsAmple.isRelativelyAmple` (over a separated base, for quasi-compact `f`),
     `isRelativelyAmple_iff_isAmple` (over an affine base),
     `IsRelativelyAmple.pullback_of_isOpenImmersion`, `isRelativelyAmple_pullback_iff_of_isIso`,
     `IsRelativelyAmple.comp` (with an affine morphism), `IsRelativelyAmple.restrict` (to opens of
     the base), `LineBundleClass.isRelativelyAmple_one_iff` (the trivial class is relatively ample
     exactly for quasi-affine morphisms), `isRelativelyAmple_one` (affine morphisms),
     `isRelativelyAmple_of_pow_eq_one`, `InvertibleSheaf.isRelativelyAmple_tensorPow_iff`;
     `LineBundleClass.isRelativelyAmple_relativeProjTwistingSheafOne`; `IsProjective` (class),
     `isProjective_relativeProjToBase`, the instance `IsProjective (j ≫ f)` for a closed immersion
     `j`, `IsProjective.exists_isRelativelyVeryAmple`, and the instance `IsProjective.isProper`.
   - Subject: `feat(AlgebraicGeometry/LineBundle): relatively ample and very ample line bundles and projective morphisms`

## What is proved and what remains

Proved, with no stubs:
- Tensor powers of line bundles, with their classes, exponent laws and pullbacks.
- Global generation of `𝒪_X`, and of pullbacks, tensor products and tensor powers of globally
  generated line bundles.
- Nonvanishing loci: `X_{s ⊗ t} = X_s ∩ X_t`, affineness on affine opens, and preimages along
  open immersions.
- Ampleness: stable under pullback along affine open immersions (so invariant under
  isomorphism), under positive powers (in both directions), and under multiplication by globally
  generated line bundles.
- `𝒪(1)`, and every `𝒪(n)` with `n > 0`, is ample on a quasi-compact `Proj` whose degree-one
  standard opens cover it.
- Relatively very ample line bundles: `𝒪(1)` is relatively very ample on `Proj_S A`. Relative
  very ampleness is stable under isomorphism and under pullback along immersions, and it forces
  separatedness.
- Relative ampleness in the Stacks sense. It is equivalent for `a` and `aⁿ`, `n > 0`, and stable
  under multiplication by globally generated bundles. It characterizes quasi-affine morphisms for
  the trivial class, and it holds for affine morphisms and torsion classes. Over an affine base it
  is ampleness; over a separated base, ampleness implies it for quasi-compact morphisms. It is
  preserved by pullback along affine open immersions of the source, so it is invariant under
  isomorphisms of the source over the base. It is preserved by composition with affine
  morphisms and by restriction to opens of the base.
- `𝒪(1)` is relatively ample on a quasi-compact relative `Proj` generated in degree one.
- Projective morphisms are closed under precomposition with closed immersions, carry a relatively
  very ample line bundle, and are **proper**.

Remains for the target:
- **Relatively very ample + quasi-compact ⇒ relatively ample**, and so: for `f` projective, the
  pullback of `𝒪(1)` is relatively ample. The case `i = 𝟙` is now proved
  (`isRelativelyAmple_relativeProjTwistingSheafOne`). What is missing is ampleness pulled back
  along an immersion `i` that is not open. Two inputs are needed:
  - the nonvanishing locus of a section pulled back along `i` is `i⁻¹` of the original locus;
  - for non-closed immersions, the Stacks argument that extends sections from `X_s` after
    multiplying by powers of `s`.

  `main` lacks a pullback-of-sections API for `Scheme.Modules.pullback`. Two routes look viable:
  1. a section `s` as a morphism `𝒪 ⟶ L` (`SheafOfModules.freeHomEquiv`), pulled back with
     `Scheme.Modules.pullbackObjUnitIso`, as in `GlobalGeneration/Pullback.lean`; this needs the
     compatibility of the pullback with multiplication by regular functions;
  2. the residue-field criterion `mem_nonvanishingLocus_of_app_ne_zero` together with the adjunction
     `pullback ⊣ pushforward`.

  For a closed immersion, the preimage of an affine `D₊(t)` is affine, so the first input suffices.
- The converse of `IsRelativelyAmple.restrict`: relative ampleness can be checked on an open cover
  of the base. This needs ampleness on `f⁻¹ V` checked on the preimages of an affine open cover of
  `V`, which is the Stacks extension of sections from `X_s`.
- Relative ampleness is stable under pullback along immersions that are not open, and under base
  change. It also implies separatedness: ample ⇒ separated, by `X_s ∩ X_t = (X_s)_{t/s}` and a
  separatedness criterion via affine covers, which Mathlib lacks.
- `ℙ(ℰ) = Proj_S(Sym ℰ)` is projective for `ℰ` of finite type. This needs `Sym ℰ` generated in
  degree one on affine sections: on an affine open, sections of `Symⁿ ℰ` are `Symⁿ` of sections.
- Stability of projectivity under composition and base change (Segre embedding and base change
  of the relative `Proj`).
- Cartier divisors and degree on components connected to these notions. Much of this is on
  `main` under `CartierDivisor/` and `LineBundle/Degree.lean`.
- The scheme-theoretic closure of `C ↪ ℙ^N_K` in `ℙ^N_R` as a proper model. Mathlib has no
  `ℙ^N`, and comparing the generic fibre needs the scheme-theoretic image to commute with flat
  base change.
