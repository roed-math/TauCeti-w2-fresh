<!--tauceti-lookahead:v1 {"area":"ModularCurves","slug":"pole-sheaf","main":"57ab0f657d75f3bc2f06d2cb8db2fef3dbd33d39","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: the pole sheaves 𝒪(n[0]) of a Weierstrass model and their fibre degrees"},{"n":2,"after":[1],"title":"feat: the divisors n[0] and the pole sheaves 𝒪_E(n[0]) of an elliptic curve"},{"n":3,"after":[],"title":"refactor: share the restriction algebra of global functions on local sections"},{"n":4,"after":[3],"title":"feat: H¹ of a finite-type sheaf on a projective Weierstrass model is finitely generated"},{"n":5,"after":[1,4],"title":"feat: cohomology and base change for line bundles of positive fibre degree on a Weierstrass model"},{"n":6,"after":[4],"title":"feat: H⁰ of a finite-type sheaf on a projective Weierstrass model over a Noetherian ring is finitely generated"},{"n":7,"after":[5,6],"title":"feat: H⁰ of 𝒪(n[0]) on a Weierstrass model is projective of rank n"},{"n":8,"after":[2,5],"title":"feat: R¹π_*𝒪_E(n[0]) vanishes on an elliptic curve"},{"n":9,"after":[5],"title":"feat: finite local freeness from finite projective sections over an affine cover"},{"n":10,"after":[7,8,9],"title":"feat: π_*𝒪_E(n[0]) is locally free of rank n"},{"n":11,"after":[],"title":"feat: the base change morphism of a direct image of modules"},{"n":12,"after":[10,11],"title":"feat: π_*𝒪_E(n[0]) commutes with arbitrary base change"},{"n":13,"after":[12],"title":"feat: pushforwards of line bundles of positive fibre degree on an elliptic curve"},{"n":14,"after":[13],"title":"feat: degree-one line bundles and sections of an elliptic curve"},{"n":15,"after":[10],"title":"feat: the pole filtration of π_*𝒪_E(6[0]) and its Weierstrass relation"},{"n":16,"after":[15],"title":"feat: Weierstrass bases of the pole sheaves and their multiplication maps"},{"n":17,"after":[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],"title":"feat: the Weierstrass-presentation theorem for pointed genus-one curves"}]}-->

# Lookahead: `pole-sheaf` (ModularCurves, Layer 1C)

Built on `main` at `57ab0f657d75f3bc2f06d2cb8db2fef3dbd33d39`. Status: **partial**. Splits
1–12 are on this branch, fully proved, with no `sorry`. Splits 13–17 are the plan for the rest of
the target and are **not** on the branch.

History. The first round left tip `a1900430f893` with splits 1 and 2. The second round left tip
`3cb1a6114df7`, adding splits 3, 4 and 5. The third round added splits 6 and 7, so
`H⁰(projModel W, 𝒪(n[0]))` is projective of constant rank `n` over every ring. The fourth round
left tip `543397aab8a1`. The fifth round left tip `7bba41d2eebe`, adding splits 8, 9 and 10:
`R¹π_*ℒ_n = 0`, and `π_*ℒ_n` is locally free of rank `n`. The sixth round left tip `1ca2316d3bfa`.
It merged `main` and added split 11, the general base change morphism `f^* π_* ⟶ π'_* g'^*` of a commutative square
of schemes, with its value on sections and a criterion over affine opens for it to be an
isomorphism. The old split 11 (the base-change clause for `ℒ_n`) is now split 12, and the old
splits 12–16 are renumbered 13–17. The seventh round (this one) merged current `main` without
conflicts and added split 12: `π_*ℒ_n` commutes with arbitrary base change. (A proof of split 12
from an earlier session was lost before it was pushed; this is a fresh proof.) The seventh round
left tip `4784a0a14fc1`. The eighth round (this one) merged current `main` without conflicts and
proved the Weierstrass-model half of the positive-degree theorem (split 13). For any line bundle
`M` on `projModel W` of positive degree on every fibre, `H¹(M) = 0`, `H⁰(M)` is flat with formation
commuting with base change, and its fibres have dimension the fibre degree. Split 5 now proves this
in general, in the new file `Scheme/PositiveDegree.lean`, and derives the pole-sheaf statements
from it as corollaries, so the pole-sheaf proofs are not duplicated. Split 1's field-level
`dim H⁰(𝒪(n[0])) = n` moved into split 5, where it is now a corollary.

## Suppliers and stubs

**No stubs were needed, and the branch has no `TauCeti/Lookahead/` module.** The proved part
consumes neither supplier:

- `relative-cartier-divisor` (open PR #27087, the geometric-fibre criterion of 0A item 1;
  re-checked on 2026-11-04, still open and still unused by splits 1–12).
  `Suggested.lean` pins no declaration for it. Its §Finite flat group schemes says the carrier
  "is supplied once by the Jacobian Challenge", and the file "deliberately introduces no
  substitute". PR #27087 adds
  `Scheme.IdealSheafData.isRelativeEffectiveCartier_iff_forall_isEffectiveCartier_comap_fst_of_isAlgClosed`.
  The divisor `[0]` does not need it: a section of a smooth separated curve already cuts out a
  relative effective Cartier divisor, by
  `Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension` on `main`, and sums
  and base change are on `main` too. The fibre criterion first enters at split 14, where the
  zero divisor of the evaluation section must be shown relative effective Cartier on geometric
  fibres.
- `polarised-descent` (open PR #27128, descent of stable opens; re-checked on 2026-11-04, still
  open). `Suggested.lean` pins no
  declaration for it either. It first enters at split 14, for the fppf-descent compatibility of
  the degree-one divisor–section correspondence. It may also enter at split 17, if the
  presentation is descended rather than built Zariski-locally.

Neither supplier's statement was restated, so there are no differences to record.

## What is proved (splits 1–12)

### Split 1 — after: none

PR subject: `feat: the pole sheaves 𝒪(n[0]) of a Weierstrass model and their fibre degrees`

Files:
- `TauCeti/AlgebraicGeometry/EffectiveCartierDivisor/TensorProduct.lean` (extended, +38 lines).
  These are general facts about classes of ideal sheaves:
  - `TauCeti.AlgebraicGeometry.LineBundleClass.mk_toInvertibleSheaf_congr`: the class depends
    only on the ideal sheaf.
  - `TauCeti.AlgebraicGeometry.LineBundleClass.mk_toInvertibleSheaf_top`: the unit ideal sheaf
    has trivial class.
  - `TauCeti.AlgebraicGeometry.LineBundleClass.mk_toInvertibleSheaf_pow`: the class of `I ^ n` is
    the `n`-th power of the class of `I`.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Integral.lean` (extended, +7 lines):
  - `WeierstrassCurve.geometricallyIntegral_over_projModel`: the instance on
    `projModel W ↘ Spec R`. This follows the existing `isProper_over_projModel` pattern.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Divisor/PoleSheaf/Basic.lean` (new, 181 lines):
  - `WeierstrassCurve.poleSheaf W n`, the line bundle `𝒪(n[0])` on `projModel W` over any ring,
    with `poleSheaf_def`, `mk_poleSheaf_one`, `mk_poleSheaf` (`𝒪(n[0]) ≅ 𝒪([0])^{⊗n}`) and
    `mk_poleSheaf_add`.
  - `pullback_mk_poleSheaf_projModelBaseChange` and `nonempty_pullback_poleSheaf_iso`:
    compatibility with change of the coefficient ring, on classes and as sheaves.
  - Over a field `K`:
    - `genus_projModel`: `W.projModel.genus K = 1`.
    - `finrank_cohomology_one_trivial_projModel`: `dim H¹(𝒪) = 1`.
    - `eulerDegree_poleSheaf`: `deg 𝒪(n[0]) = n`.
  - `eulerDegree_pullback_poleSheaf`: over any ring, the pullback of `𝒪(n[0])` to the model over
    any field `K` receiving `R` has degree `n`. This is the fibre-degree hypothesis of split 5.

  The field-level Riemann–Roch statements (`H¹ = 0`, `dim H⁰ = n`) are in split 5, as instances of
  the positive-degree theorem.

### Split 2 — after: 1

PR subject: `feat: the divisors n[0] and the pole sheaves 𝒪_E(n[0]) of an elliptic curve`

File: `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/PoleSheaf.lean` (new, 280 lines).
Namespace `TauCeti.AlgebraicGeometry.EllipticCurveGeom`:
- The divisors:
  - `zeroDivisor E`, the divisor `[0]`, with `zeroDivisor_def`.
  - `zeroDivisor_pow_eq_pointsDivisor`: `n[0]` is the points divisor of `n` copies of `0`.
  - `isRelativeEffectiveCartier_zeroDivisor` and `isRelativeEffectiveCartier_zeroDivisor_pow`.
  - Instances `isFinite_zeroDivisor_pow`, `flat_zeroDivisor_pow` and
    `locallyOfFinitePresentation_zeroDivisor_pow`.
  - `finrank_zeroDivisor_pow`: rank `n`.
  - `zeroDivisor_comap_of_isPullback` and `zeroDivisor_pow_comap_of_isPullback`: base change.
  - `zeroDivisor_comap_toTotal` and `zeroDivisor_pow_comap_toTotal`: on a pointed Weierstrass
    chart, `n[0]` is the model's `zeroSectionDivisor ^ n`.
- The line bundles:
  - `poleSheaf E n`, the line bundle `ℒ_n = 𝒪_E(n[0])`, with `poleSheaf_def`,
    `mk_poleSheaf_one`, `mk_poleSheaf`, `mk_poleSheaf_zero` and `mk_poleSheaf_add`.
  - `pullback_mk_poleSheaf_toTotal`: on a chart, `ℒ_n` is `WeierstrassCurve.poleSheaf`.
  - `pullback_mk_poleSheaf_of_isPullback` and `pullback_mk_poleSheaf_baseChange`: base change.

These two splits carry the README's first sentence of 1C ("Construct the relative effective
Cartier divisor `[0]`, its multiples, and the line bundles `ℒ_n = 𝒪_E(n[0])`") and its
fibrewise inputs.

### Split 3 — after: none

PR subject: `refactor: share the restriction algebra of global functions on local sections`

A prerequisite refactor (no new mathematics), shipped on its own:
- `TauCeti/AlgebraicGeometry/Modules/Sections.lean` (+14 lines):
  `AlgebraicGeometry.Scheme.Modules.sectionsGlobalAlgebra` (the `Γ(X, ⊤)`-algebra structure on
  `Γ(X, U)` by restriction, meant as a local instance) and
  `isScalarTower_sectionsGlobalAlgebra`.
- `TauCeti/AlgebraicGeometry/Cohomology/ProjectiveLine/Basic.lean` (−14 lines): its private copies
  `sectionsAlgebra` and `isScalarTower_restrict` are deleted in favour of the shared ones.

### Split 4 — after: 3

PR subject: `feat: H¹ of a finite-type sheaf on a projective Weierstrass model is finitely generated`

This is the finiteness input of Grauert's theorem and of cohomology and base change in 1C, for
every Weierstrass curve over every ring.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/ProjModel.lean` (+7 lines):
  `WeierstrassCurve.projModelOver_def` (the body of `projModelOver` is not exposed).
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Chart.lean` (+38 lines):
  - `WeierstrassCurve.opensRange_chartι_one_sup_opensRange_chartι_two`: `D₊(Y)` and `D₊(Z)`
    cover the projective model (the equation puts `X³` in `(Y, Z)`).
  - `WeierstrassCurve.isAffineOpen_opensRange_chartι_one_inf_opensRange_chartι_two`: the
    overlap `D₊(YZ)` is affine.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Projective/Chart/Overlap.lean` (new, 171 lines),
  namespace `WeierstrassCurve.Projective`:
  - `exists_eq_chartRing_two`: the chart ring of `D₊(Z)` is spanned by `1, x, x²` over `R[y]`.
  - `awayMapOverlapY`, `awayMapOverlapZ`, `awayCoord`: restriction to the overlap and the
    affine coordinates `Xⱼ / Xᵢ`.
  - `awayMapOverlapY_mul_awayMapOverlapZ`: `(Z/Y)(Y/Z) = 1` on the overlap.
  - `isLocalization_awayMapOverlapZ`: `A_(YZ) = A_(Z)[(Y/Z)⁻¹]`.
  - private `chartRingTwoToOverlap`, the `R`-algebra map `ChartRing 2 → A_(YZ)`.
  - `exists_eq_overlap`: every function on the overlap is `(Z/Y)ᵏ (P₀(y) + x P₁(y) + x² P₂(y))`.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/FiniteCohomology.lean` (new, 277 lines):
  - `WeierstrassCurve.awayToSection_algebraMap`: constants on a chart `D₊(f)`.
  - `WeierstrassCurve.finite_sectionsQuotient`: the Čech quotient on the cover `D₊(Y), D₊(Z)` is
    finite over the global functions (`TauCeti.Algebra.finite_quotient_sup_of_mul_eq_one` with
    the algebra `Γ[Z/Y, Y/Z]`, over which the overlap sections are spanned by `xⁱ s`, `i < 3`).
  - `WeierstrassCurve.finite_cohomology_one`: `H¹(projModel W, M)` is a finite `R`-module for
    every quasi-coherent `M` of finite type, over any ring.

### Split 5 — after: 1, 4

PR subject: `feat: cohomology and base change for line bundles of positive fibre degree on a Weierstrass model`

- `TauCeti/AlgebraicGeometry/VectorBundle/Affine/Sections.lean` (new, 80 lines):
  - `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finite_projective_sections`: sections of a
    finite locally free sheaf over an affine open are finite projective over `Γ(X, U)`.
  - `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.flat_sectionsBase`: they are flat over `R`
    when `X` is flat over `R`.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Smooth.lean` (+8 lines):
  `WeierstrassCurve.smooth_over_projModel` (hence `Flat (projModel W ↘ Spec R)`).
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/BaseChange.lean` (+12 lines):
  `WeierstrassCurve.isPullback_projModelBaseChange_over`.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/PositiveDegree.lean` (new, 179 lines). This is the
  **positive-degree theorem on a Weierstrass model**. Let `M` be a line bundle on `projModel W`,
  for `W` elliptic over any ring `R`, such that for every prime `p` the pullback of `M` along
  `projModelBaseChange (algebraMap R κ(p))` has positive `eulerDegree κ(p)`. Then:
  - over a field, `subsingleton_cohomology_one_of_eulerDegree_pos` and
    `finrank_cohomology_zero_of_eulerDegree_pos` give `H¹ = 0` and `dim H⁰ = deg` (Riemann–Roch in
    genus one, via `InvertibleSheaf.subsingleton_cohomology_one_of_two_mul_genus_sub_two_lt_eulerDegree`
    and `finrank_cohomology_zero_eq_eulerDegree_add_one_sub_genus` on `main`);
  - `flat_sectionsBase`: sections of any line bundle over an affine open are `R`-flat;
  - `subsingleton_cohomology_one_of_forall_eulerDegree_pos`: `H¹(projModel W, M) = 0`;
  - `flat_cohomology_zero_of_forall_eulerDegree_pos`: `H⁰(projModel W, M)` is flat over `R`;
  - `bijective_cohomologyBaseChange_zero_of_forall_eulerDegree_pos`: `R' ⊗_R H⁰ ≅ H⁰` after any
    base change;
  - `finrank_fiber_cohomology_zero_of_forall_eulerDegree_pos`: `dim_{κ(p)} κ(p) ⊗_R H⁰(M)` is the
    fibre degree of `M` at `p`.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Divisor/PoleSheaf/Cohomology.lean` (new; 120 lines
  in this split). For `W` elliptic over any ring `R` and `n > 0`, these are corollaries of the
  positive-degree theorem through `eulerDegree_pullback_poleSheaf` (split 1):
  - `finrank_cohomology_zero_poleSheaf`: over a field, `dim H⁰(𝒪(n[0])) = n`.
  - `subsingleton_cohomology_one_poleSheaf`: `H¹(projModel W, 𝒪(n[0])) = 0`.
  - `flat_cohomology_zero_poleSheaf`: `H⁰(projModel W, 𝒪(n[0]))` is flat over `R`.
  - `bijective_cohomologyBaseChange_zero_poleSheaf`: `R' ⊗_R H⁰ ≅ H⁰` after any base change.
  - `finrank_fiber_cohomology_zero_poleSheaf`: `dim_{κ(p)} κ(p) ⊗_R H⁰ = n` at every prime.

### Split 6 — after: 4

PR subject: `feat: H⁰ of a finite-type sheaf on a projective Weierstrass model over a Noetherian ring is finitely generated`

This is the Noetherian finiteness input for Grauert's theorem. The proof follows the projective
line's (`TauCeti.AlgebraicGeometry.projectiveLine.finite_globalSections`).
- `TauCeti/AlgebraicGeometry/EllipticCurve/Projective/Chart/Overlap.lean` (+90 lines), namespace
  `WeierstrassCurve.Projective`:
  - `exists_eq_chartRing_one`: the chart ring of `D₊(Y)` is spanned by `1, x, x²` over `R[z]`,
    where `x = X/Y` and `z = Z/Y`.
  - `exists_eq_away_one` and `exists_eq_away_two`: the same decompositions on `A_(Y)` and `A_(Z)`,
    in the coordinates `awayCoord`.
  - private `chartRingToAway` and `chartRingToAway_chartPoint`.
- `TauCeti/AlgebraicGeometry/Modules/Sections.lean` (+17 lines):
  `AlgebraicGeometry.Scheme.Modules.map_mem_adjoin_singleton`. Through `sectionsGlobalAlgebra`,
  restriction maps `Γ(⊤)[t]` into `Γ(⊤)[t|_V]`.
- `TauCeti/AlgebraicGeometry/Cohomology/ProjectiveLine/Basic.lean` (+2/−24 lines): its private
  `sectionsRestrictionAlgHom` is deleted, and `map_mem_adjoin_overlapCoord` becomes a one-line
  application of `map_mem_adjoin_singleton`.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/FiniteCohomology.lean` (+58/−21 lines,
  314 lines in total):
  - `WeierstrassCurve.map_awayCoord_mul_map_awayCoord`: `(Z/Y)(Y/Z) = 1` on the overlap.
    `finite_sectionsQuotient` now uses it.
  - `WeierstrassCurve.surjective_baseRingToStructurePresheaf_app_top`: the global functions are
    the constants.
  - `WeierstrassCurve.finite_cohomology_of_finite`: finiteness over `Γ(⊤)` gives finiteness over
    `R`. `finite_cohomology_one` now uses these two lemmas instead of its inline copy.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/FiniteGlobalSections.lean` (new, 300 lines):
  - private helpers: `exists_eq_chart`, `exists_finite_span_eq_top`,
    `range_le_span_adjoin`, `isNoetherianRing_globalSections` and
    `fg_ker_sectionsRestrictionLinear`. Together they say that the sections over a chart are
    finite over `Γ[t]`, where `t` is the chart's affine coordinate, and that those vanishing on
    the overlap are `t`-power torsion.
  - `WeierstrassCurve.finite_globalSections`: `Γ(M, ⊤)` is finite over `Γ(⊤)` when `R` is
    Noetherian.
  - `WeierstrassCurve.finite_cohomology_zero`: `H⁰(projModel W, M)` is finite over a Noetherian
    `R`, for `M` quasi-coherent of finite type.

### Split 7 — after: 5, 6

PR subject: `feat: H⁰ of 𝒪(n[0]) on a Weierstrass model is projective of rank n`

`TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Divisor/PoleSheaf/Cohomology.lean` (+61 lines,
for `W` elliptic over any ring and `n > 0`; it imports split 6's `FiniteGlobalSections.lean`):
- private `finitePresentation_cohomology_zero_poleSheaf_of_map`: the case where `W` is the base
  change of `W₀` over a Noetherian `R₀`. It combines split 6 with split 5's base-change
  bijectivity and `nonempty_pullback_poleSheaf_iso`.
- `finitePresentation_cohomology_zero_poleSheaf`: `W` descends to the subring generated over `ℤ`
  by `a₁, …, a₆` and `Δ⁻¹`. That subring is of finite type over `ℤ`, hence Noetherian.
- `projective_cohomology_zero_poleSheaf`: flat and finitely presented, hence projective.
- `rankAtStalk_cohomology_zero_poleSheaf`: rank `n` at every prime, from split 5's fibre
  dimension.

### Split 8 — after: 2, 5

PR subject: `feat: R¹π_*𝒪_E(n[0]) vanishes on an elliptic curve`

- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/GlobalSections.lean` (+44/−30 lines, 145 in
  total). Steps of the existing proof of `isIso_structureMap_app` become public, because the new
  file needs them:
  - `PointedWeierstrassChart.isOpenImmersion_toTotal` (instance): `toTotal` is an open immersion.
  - `PointedWeierstrassChart.opensRange_toTotal`: its image is `π⁻¹(U)` for `U` the image of the
    base. `isIso_app_opensRange` now uses it.
  - `PointedWeierstrassAtlas.isBasis_range_opensRange_restrict`: the images of the restricted
    charts form a basis of `S`. `isIso_structureMap_app` is now three lines.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/PoleSheaf/DirectImage.lean` (new, 98
  lines), namespace `TauCeti.AlgebraicGeometry.EllipticCurveGeom`:
  - `nonempty_restrict_poleSheaf_iso`: on a chart, `ℒ_n` restricts along
    `modelIso.inv ≫ toTotal` to the model's `WeierstrassCurve.poleSheaf n`.
  - `subsingleton_cohomologyOn_one_poleSheaf`: `H¹(π⁻¹(U), ℒ_n) = 0` over a chart image `U`
    (via `Scheme.Modules.cohomologyOnOpensRangeIso` and split 5).
  - `isZero_higherDirectImage_one_poleSheaf`: **`R¹π_*ℒ_n = 0`** for `n > 0` (via
    `Scheme.Hom.isZero_higherDirectImage_succ_of_isBasis`).

### Split 9 — after: 5

PR subject: `feat: finite local freeness from finite projective sections over an affine cover`

`TauCeti/AlgebraicGeometry/VectorBundle/Affine/Sections.lean` (+67/−8 lines, 139 in total):
- `AlgebraicGeometry.Scheme.Modules.sectionsLinearEquivModuleSpecΓ`: `Γ(M, U)` is the module of
  global sections of the pullback to `Spec Γ(X, U)`. It is factored out of
  `finite_projective_sections`, which now uses it.
- `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rank_fromSpec_apply`: the rank at a point of
  an affine open `U` is `Module.rankAtStalk` of `Γ(E, U)`.
- `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pullback_fromSpec` and
  `isFiniteLocallyFree_of_finite_projective_sections`: a quasi-coherent sheaf with finite
  projective sections over an affine open cover is finite locally free. This is the converse of
  `finite_projective_sections`, via `fromTildeΓ` and `isFiniteLocallyFree_tilde_iff`.

### Split 10 — after: 7, 8, 9

PR subject: `feat: π_*𝒪_E(n[0]) is locally free of rank n`

- `TauCeti/Algebra/Module/Projective/RingEquiv.lean` (new, 72 lines):
  - `LinearMap.finite_of_surjective`: the image of a finite module under a surjective semilinear
    map is finite.
  - `LinearEquiv.rankAtStalk_eq`: along `e : M ≃ₛₗ[σ] N` with `σ` a ring isomorphism, the rank at
    `q` is the rank at `σ⁻¹(q)`. This is via `B ⊗[A] M ≃ₗ[B] N` and
    `Module.rankAtStalk_baseChange`.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/FiniteCohomology.lean` (+17/−10 lines):
  `WeierstrassCurve.bijective_baseRingToGlobalSections`. `surjective_baseRingToStructurePresheaf_app_top`
  is now derived from it.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Divisor/PoleSheaf/Cohomology.lean` (+28 lines,
  195 in total):
  `WeierstrassCurve.finite_projective_globalSections_poleSheaf`: `Γ(⊤, 𝒪(n[0]))` is finite
  projective of constant rank `n` over `Γ(projModel, ⊤)`. This transports split 7 along
  `R ≃+* Γ(projModel, ⊤)`.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/PoleSheaf/LocallyFree.lean` (new, 168
  lines), namespace `TauCeti.AlgebraicGeometry.EllipticCurveGeom`:
  - `finite_projective_sections_poleSheaf`: `Γ(π⁻¹(U), ℒ_n)` is finite projective of rank `n`
    over `Γ(E, π⁻¹(U))` for a chart image `U`.
  - `finite_projective_sections_pushforward_poleSheaf`: the same for `Γ(U, π_*ℒ_n)` over
    `Γ(S, U)`, through `isIso_app_opensRange`.
  - `isFiniteLocallyFree_pushforward_poleSheaf`: **`π_*ℒ_n` is finite locally free.**
  - `rank_pushforward_poleSheaf`: **it has rank `n` at every point.**

### Split 11 — after: none

PR subject: `feat: the base change morphism of a direct image of modules`

General infrastructure, independent of elliptic curves; it builds on `main` alone.
- `TauCeti/AlgebraicGeometry/Modules/Sheaf.lean` (+23/−2 lines):
  `AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_bijective_app_of_isBasis`, a morphism of
  `𝒪_X`-modules bijective on the sections over the opens of a basis is an isomorphism (via
  `TopCat.Sheaf.isIso_iff_isIso_basis`). It sits beside the file's epimorphism criterion
  `Hom.epi_of_surjective_on_affineOpens`.
- `TauCeti/AlgebraicGeometry/Modules/Pullback/Sections.lean` (+40 lines, 176 in total):
  - `AlgebraicGeometry.Scheme.Hom.restrictFunctorIsoPullback_hom_app_app_map`: along an open
    immersion `j`, `restrictFunctorIsoPullback` carries the restriction of `s` to `j (j⁻¹ U)` to
    `j.pullbackSections M U s`. This was a step inside the private `chartPullback_unit` of
    `Pullback/BaseChange.lean`, which now calls it.
  - `AlgebraicGeometry.Scheme.Hom.bijective_pullbackSections_of_isOpenImmersion`: hence pulling
    back sections over `U ≤ j.opensRange` is bijective. Split 12 uses it to identify the sections
    of `g^* ℒ_n` over `π'⁻¹ V` with those of its pullback to the open subscheme `π'⁻¹ V`.
- `TauCeti/AlgebraicGeometry/Modules/Pullback/BaseChange.lean` (+91/−64 lines, 557 in total).
  The private comparison behind `Scheme.Hom.pullbackSectionsEquiv` is generalised from the pair
  `(U, g⁻¹ U)` to any affine `V` with a ring map `φ : Γ(X, U) ⟶ Γ(Y, V)` compatible with `g` on
  spectra (private `chartPullbackIso`, `chartPullbackIso_unit`, `chartSectionsEquiv`,
  `chartSectionsEquiv_one_tmul`, `specMap_app_fromSpec`). `pullbackSectionsEquiv` and its two
  lemmas keep their statements and become instances of it. New:
  - `AlgebraicGeometry.Scheme.Hom.pullbackSectionsLEEquiv`: for affine opens `V ≤ g⁻¹ U`,
    `Γ(Y, V) ⊗_{Γ(X, U)} Γ(M, U) ≃ Γ(g^* M, V)` along `g.appLE U V`, for quasicoherent `M`.
  - `AlgebraicGeometry.Scheme.Hom.pullbackSectionsLEEquiv_one_tmul`: it sends `1 ⊗ s` to
    `g.pullbackSectionsLE M U V s`.
- `TauCeti/AlgebraicGeometry/Modules/Pushforward.lean` moves to
  `TauCeti/AlgebraicGeometry/Modules/Pushforward/Basic.lean` (no content change), because the
  new file below opens the `Modules/Pushforward/` directory; its three importers are updated.
- `TauCeti/AlgebraicGeometry/Modules/Pushforward/BaseChange.lean` (new, 212 lines), namespace
  `TauCeti.AlgebraicGeometry`:
  - `pushforwardBaseChange sq : pushforward π ⋙ pullback f ⟶ pullback g' ⋙ pushforward π'` for
    `sq : CommSq g' π' π f`: the mate (`mateEquiv` of the pullback–pushforward adjunctions of `g'`
    and `f`) of `π_* g'_* = (g' ≫ π)_* = (π' ≫ f)_* = f_* π'_*`.
  - `unit_comp_pushforward_map_pushforwardBaseChange_app`: its defining property against the
    unit of `f`.
  - `pushforwardBaseChange_app_pullbackSections` and
    `pushforwardBaseChange_app_pullbackSectionsLE`: on sections it sends `f^* s` to `g'^* s`
    (restricted to `π'⁻¹ V` for `V ≤ f⁻¹ U`).
  - `pushforwardBaseChange_app_pullbackSectionsLEEquiv_one_tmul`: over affine `V ≤ f⁻¹ U`, on
    `Γ(V) ⊗ Γ(U, π_* M)` it sends `1 ⊗ s` to `g'^* s`.
  - `isIso_pushforwardBaseChange_app_of_bijective`: **the reduction to affine opens.** If `π_* M`
    is quasicoherent and, for a basis of affine opens `V i ≤ f⁻¹ (U i)` with `U i` affine, some
    `Γ(V i)`-linear map `Φ i : Γ(V i) ⊗_{Γ(U i)} Γ(π⁻¹ (U i), M) → Γ(π'⁻¹ (V i), g'^* M)` with
    `Φ i (1 ⊗ s) = g'^* s` is bijective, then the base change morphism at `M` is an isomorphism.

### Split 12 — after: 10, 11

PR subject: `feat: π_*𝒪_E(n[0]) commutes with arbitrary base change`

- `TauCeti/RingTheory/TensorProduct/IsBaseChange/BijectiveAlgebraMap.lean` (new, 106 lines).
  Base change along bijective ring maps:
  - `IsBaseChange.of_bijective_algebraMap`: if `R → S` is bijective, every `S`-module is its own
    base change along it, through the identity.
  - `IsBaseChange.of_bijective_algebraMap_right`: a base change along `A → T` is one along
    `A → B` when `B → T` is bijective.
  - `IsBaseChange.restrictScalars_of_bijective`: a base change along `R → T` is one along
    `A → B` when `A → R`, `B → T` are bijective and the square of rings commutes.
  These are a new module rather than an extension of `TauCeti/RingTheory/TensorProduct/IsBaseChange.lean`
  only because that file has 1637 transitive importers; the port may append them there instead.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/PoleSheaf/BaseChange.lean` (new, 452
  lines), namespace `TauCeti.AlgebraicGeometry.EllipticCurveGeom`:
  - private, general: `bijective_pullbackSectionsLE` (pulling back sections along an open
    immersion between opens matching up is bijective), `bijective_appLE`, `appLE_eq_of_eq`. The
    port should consider making the first public in `Modules/Pullback/Sections.lean`, beside
    `Scheme.Hom.bijective_pullbackSections_of_isOpenImmersion` (kept here to avoid rebuilding its
    25 dependents, among them `Cohomology/FlatBaseChange.lean`).
  - private, in `PointedWeierstrassChart` for a chart pair `(k, c, h, hh)` over the base change
    square `hg`: `opensRange_modelIso_inv_toTotal`, `top_le_preimage_modelIso_inv_toTotal`,
    `opensRange_le_preimage_opensRange`, `preimage_le_preimage_preimage`,
    `modelMap_comp_modelIso_inv_toTotal`, the ring-map identities `appLE_comp_app_comp_appLE`
    and `app_comp_appLE`, `isPullback_modelMap_over` (main's `isPullback_modelMap` read over
    `Spec c.ring ← Spec k.ring` with the algebra `Spec.preimage`), `pullbackModelIso` (the
    identification of `g^*M` on the model of `k` with the pullback of `M|_c` along `modelMap`)
    and `pullbackModelIso_hom_app_pullbackSectionsLE` (its value on pulled-back sections).
  - private `exists_bijective_pullbackSectionsLE_poleSheaf`: over a chart pair, the
    `Γ(S', V)`-linear extension of `g^*` on sections of `ℒ_n` is bijective. This is
    `WeierstrassCurve.bijective_cohomologyBaseChange_zero_poleSheaf` (split 5) for the model
    square, transported along `H⁰ ≅ Γ(⊤)`, the model identification of `ℒ_n`
    (`nonempty_restrict_poleSheaf_iso`), the ring isomorphisms `Γ(S, U) ≅ c.ring` and
    `Γ(S', V) ≅ k.ring` (through `bijective_baseRingToGlobalSections`, split 10) and
    `IsBaseChange.restrictScalars_of_bijective`.
  - `isIso_pushforwardBaseChange_app_poleSheaf`: **for `n > 0` the base change morphism
    `f^* π_* ℒ_n ⟶ π'_* g^* ℒ_n` is an isomorphism**, by split 11's
    `isIso_pushforwardBaseChange_app_of_bijective` on the basis of images of chart bases of `E'`
    lying over a chart of `E` (`exists_chart_comp_baseMap` on `main`, restricted to affine opens).
  - `nonempty_pullback_pushforward_poleSheaf_iso`: **`f^* π_* ℒ_n ≅ π'_* ℒ'_n`** when `g`
    preserves the zero sections (with `pullback_mk_poleSheaf_of_isPullback`, split 2).

## What remains (splits 13–17, not on this branch)

13. **(after 12)** The positive-degree theorem on `E`: an invertible `M` on `E` of degree `d > 0`
    on every geometric fibre has `R¹π_*M = 0`, and `π_*M` is locally free of rank `d` and
    commutes with base change. The Weierstrass-model inputs `H¹ = 0`, flatness and base change of
    `H⁰`, and fibre dimension are **done for every such `M`** (split 5, `Scheme/PositiveDegree.lean`).
    What remains:
    - State the hypothesis on `E` with `main`'s fibre degree,
      `TauCeti.AlgebraicGeometry.relativePicardFiberDegree` (`PicardFunctor/PicZero/Basic.lean`),
      at geometric points. Transport it to split 5's residue-field hypothesis on each chart model.
      This uses the chart identification of the fibres and invariance of the degree under field
      extension and isomorphism (`LineBundleClass.eulerDegree_pullback_of_isIso` and
      `InvertibleSheaf.eulerDegree_eq_finrank_mul` on `main`).
    - Finite presentation of `H⁰(projModel W, M)` over a non-Noetherian `R`. Split 7 descends `W`
      to a finitely generated subring; for general `M` the line bundle must descend with it,
      which needs a spreading-out statement for line bundles that neither `main` nor 0E's pinned
      forms provide yet. A spreading-out-free alternative would also do.
    - Then generalise splits 8, 10 and 12 from `ℒ_n` to `M`. Their proofs use only the
      Weierstrass-model statements, which now hold for `M`.
14. **(after 13)** For `d = 1`: the evaluation section has a relative effective Cartier zero
    divisor of degree one, hence is the divisor of a unique section. Prove compatibility with
    base change and fppf descent. This needs `relative-cartier-divisor` and `polarised-descent`.
15. **(after 10)** The pole filtration of `π_*ℒ_n`: local splittings, the choice of `x` and `y`,
    the unique relation in pole order six, and the unit discriminant.
16. **(after 15)** The bases `1, x, y, x², xy, x³` after a pointed Weierstrass trivialisation, the
    multiplication maps, the relation equal to the Weierstrass equation, and their independence of
    the chosen pointed equation.
17. **(after 1–16; exported)** The Weierstrass-presentation theorem: a smooth proper genus-one
    curve with a section is Zariski-locally pointed-isomorphic to a projective Weierstrass model,
    producing a `PointedWeierstrassAtlas`. This split completes the target.

The previous plan's split "pointed isomorphisms of Weierstrass models are variable changes" is
dropped: `main` already has it, over affine bases
(`WeierstrassCurve.existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom`, in
`Scheme/VariableChange/Basic.lean`) and over arbitrary bases
(`WeierstrassCurve.existsUnique_hom_comp_eq_comp_projModelVariableChangeIso_hom`, in
`Scheme/VariableChange/OverScheme.lean`). The variable-change group and its action on the
coefficients are Mathlib's `WeierstrassCurve.VariableChange`. Split 16 should check what remains
of the README's action on `x`, `y` and the invariant differential before adding any of it.

## Verification

`lake exe cache get`, `lake build` (green, warnings as errors) and
`/opt/round/lookahead-check` all pass. Mathlib's default environment linters (including
`simpNF`, `unusedArguments`, `docBlame`, `synTaut`, `unusedHavesSuffices`,
`explicitVarsOfIff`) pass on the modules this round changed, run through
`scripts/LintEnvDriver.lean --only-listed`.
