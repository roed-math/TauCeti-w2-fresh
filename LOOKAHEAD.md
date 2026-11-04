<!--tauceti-lookahead:v1 {"area":"ModularCurves","slug":"pole-sheaf","main":"333c9e49143de812ed1452b412193ee9c05501e7","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: the pole sheaves 𝒪(n[0]) of a Weierstrass model and their cohomology over a field"},{"n":2,"after":[1],"title":"feat: the divisors n[0] and the pole sheaves 𝒪_E(n[0]) of an elliptic curve"},{"n":3,"after":[],"title":"refactor: share the restriction algebra of global functions on local sections"},{"n":4,"after":[3],"title":"feat: H¹ of a finite-type sheaf on a projective Weierstrass model is finitely generated"},{"n":5,"after":[1,4],"title":"feat: H¹ vanishing and base change for H⁰ of 𝒪(n[0]) on a Weierstrass model over a ring"},{"n":6,"after":[5],"title":"feat: H⁰ of 𝒪(n[0]) on a Weierstrass model is projective of rank n"},{"n":7,"after":[2,6],"title":"feat: π_*𝒪_E(n[0]) is locally free of rank n and commutes with base change"},{"n":8,"after":[7],"title":"feat: pushforwards of line bundles of positive fibre degree on an elliptic curve"},{"n":9,"after":[8],"title":"feat: degree-one line bundles and sections of an elliptic curve"},{"n":10,"after":[7],"title":"feat: the pole filtration of π_*𝒪_E(6[0]) and its Weierstrass relation"},{"n":11,"after":[10],"title":"feat: Weierstrass bases of the pole sheaves and their multiplication maps"},{"n":12,"after":[1,2,3,4,5,6,7,8,9,10,11],"title":"feat: the Weierstrass-presentation theorem for pointed genus-one curves"}]}-->

# Lookahead: `pole-sheaf` (ModularCurves, Layer 1C)

Built on `main` at `333c9e49143de812ed1452b412193ee9c05501e7`. Status: **partial**. Splits 1–5
are on this branch, fully proved, with no `sorry`. Splits 6–12 are the plan for the rest of the
target and are **not** on the branch.

This round continued the branch from tip `a1900430f893`, which held splits 1 and 2. It added
splits 3, 4 and 5, and moved `Divisor/PoleSheaf.lean` to `Divisor/PoleSheaf/Basic.lean`, because
the new `Divisor/PoleSheaf/Cohomology.lean` shares its leading component (placement rubric).

## Suppliers and stubs

**No stubs were needed, and the branch has no `TauCeti/Lookahead/` module.** The proved part
consumes neither supplier:

- `relative-cartier-divisor` (open PR #27087, the geometric-fibre criterion of 0A item 1).
  `Suggested.lean` pins no declaration for it. Its §Finite flat group schemes says the carrier
  "is supplied once by the Jacobian Challenge", and the file "deliberately introduces no
  substitute". PR #27087 adds
  `Scheme.IdealSheafData.isRelativeEffectiveCartier_iff_forall_isEffectiveCartier_comap_fst_of_isAlgClosed`.
  The divisor `[0]` does not need it: a section of a smooth separated curve already cuts out a
  relative effective Cartier divisor, by
  `Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension` on `main`, and sums
  and base change are on `main` too. The fibre criterion first enters at split 9, where the
  zero divisor of the evaluation section must be shown relative effective Cartier on geometric
  fibres.
- `polarised-descent` (open PR #27128, descent of stable opens). `Suggested.lean` pins no
  declaration for it either. It first enters at split 9, for the fppf-descent compatibility of
  the degree-one divisor–section correspondence. It may also enter at split 12, if the
  presentation is descended rather than built Zariski-locally.

Neither supplier's statement was restated, so there are no differences to record.

## What is proved (splits 1–5)

### Split 1 — after: none

PR subject: `feat: the pole sheaves 𝒪(n[0]) of a Weierstrass model and their cohomology over a field`

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
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Divisor/PoleSheaf/Basic.lean` (new, 190 lines):
  - `WeierstrassCurve.poleSheaf W n`, the line bundle `𝒪(n[0])` on `projModel W` over any ring,
    with `poleSheaf_def`, `mk_poleSheaf_one`, `mk_poleSheaf` (`𝒪(n[0]) ≅ 𝒪([0])^{⊗n}`) and
    `mk_poleSheaf_add`.
  - `pullback_mk_poleSheaf_projModelBaseChange` and `nonempty_pullback_poleSheaf_iso`:
    compatibility with change of the coefficient ring, on classes and as sheaves.
  - Over a field `K`:
    - `genus_projModel`: `W.projModel.genus K = 1`.
    - `finrank_cohomology_one_trivial_projModel`: `dim H¹(𝒪) = 1`.
    - `eulerDegree_poleSheaf`: `deg 𝒪(n[0]) = n`.
    - `finrank_cohomology_zero_poleSheaf`: `dim H⁰(𝒪(n[0])) = n` for `n > 0`.

  The field-level vanishing `H¹(𝒪(n[0])) = 0` is now a private step of split 5, whose public
  `subsingleton_cohomology_one_poleSheaf` holds over every ring and takes over its name.

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

PR subject: `feat: H¹ vanishing and base change for H⁰ of 𝒪(n[0]) on a Weierstrass model over a ring`

- `TauCeti/AlgebraicGeometry/VectorBundle/Affine/Sections.lean` (new, 80 lines):
  - `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finite_projective_sections`: sections of a
    finite locally free sheaf over an affine open are finite projective over `Γ(X, U)`.
  - `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.flat_sectionsBase`: they are flat over `R`
    when `X` is flat over `R`.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Smooth.lean` (+8 lines):
  `WeierstrassCurve.smooth_over_projModel` (hence `Flat (projModel W ↘ Spec R)`).
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/BaseChange.lean` (+12 lines):
  `WeierstrassCurve.isPullback_projModelBaseChange_over`.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Divisor/PoleSheaf/Cohomology.lean` (new, 158
  lines), for `W` elliptic over any ring `R` and `n > 0`:
  - `flat_sectionsBase_poleSheaf`: sections of `𝒪(n[0])` over affine opens are `R`-flat.
  - `subsingleton_cohomology_one_poleSheaf`: `H¹(projModel W, 𝒪(n[0])) = 0`.
  - `flat_cohomology_zero_poleSheaf`: `H⁰(projModel W, 𝒪(n[0]))` is flat over `R`.
  - `bijective_cohomologyBaseChange_zero_poleSheaf`: `R' ⊗_R H⁰ ≅ H⁰` after any base change.
  - `finrank_fiber_cohomology_zero_poleSheaf`: `dim_{κ(p)} κ(p) ⊗_R H⁰ = n` at every prime.

## What remains (splits 6–12, not on this branch)

6. **(after 5)** `H⁰(projModel W, 𝒪(n[0]))` is finitely presented, hence (flat) projective of
   rank `n` (`TauCeti.AlgebraicGeometry.projective_cohomology_zero_of_forall_isMaximal` or
   `Module.Flat.projective_of_finitePresentation`, rank from split 5's fibre dimension). Plan:
   - over a Noetherian ring, `H⁰` of a finite-type quasi-coherent sheaf on `projModel W` is
     finite, following `TauCeti.AlgebraicGeometry.projectiveLine.finite_globalSections`: use
     `TauCeti.Algebra.fg_inf_of_mul_eq_one` with the spans over `R[Z/Y]` and `R[Y/Z]` of the
     restrictions of `xⁱ s`, and a variant of
     `TauCeti.Algebra.fg_restrictScalars_of_forall_pow_smul_eq_zero` for a chart ring that is
     finite (not equal) over `R[t]`: `Overlap.lean`'s `exists_eq_chartRing_two`, and its analogue
     for `D₊(Y)`, give the finiteness;
   - over any ring, write `W = W₀.map ι` with `W₀` over the finitely generated `ℤ`-subalgebra
     `R₀` generated by the `aᵢ` and `Δ⁻¹`, and transport along split 5's
     `bijective_cohomologyBaseChange_zero_poleSheaf` with `isPullback_projModelBaseChange_over`
     and `nonempty_pullback_poleSheaf_iso`.
   An attempt this round (not kept) found two elaboration traps. Inside proofs about the charts,
   do not `set W' := W.toProjective`: `rw` then times out unifying the two spellings. Avoid `rw`
   and `▸` on goals of the form `a ∈ Submodule.span (Algebra.adjoin Γ(X, ⊤) {t}) s` with the
   local `sectionsGlobalAlgebra` instance; state the membership for a product `c * g` and prove
   it with `Submodule.smul_mem` at the subalgebra element directly. The chart decomposition for
   `D₊(Y)` (`x³ = (z + a₃z² − a₆z³) + x (a₁z − a₄z²) − x² a₂z` with `x = X/Y`, `z = Z/Y`) follows
   `exists_eq_chartRing_two` verbatim.
7. **(after 2, 6)** Globalise to `E/S`: `R¹π_*ℒ_n = 0`, `π_*ℒ_n` locally free of rank `n`, and
   arbitrary base change. The chart comparison `pullback_mk_poleSheaf_toTotal` (split 2) reduces
   this to splits 5–6 on an atlas.
8. **(after 7)** The positive-degree theorem: an invertible `M` of constant positive fibre degree
   `d` has `R¹π_*M = 0`, and `π_*M` is locally free of rank `d` and commutes with base change.
   `finite_cohomology_one` (split 4) applies to any finite-type `M` on a chart.
9. **(after 8)** For `d = 1`: the evaluation section has a relative effective Cartier zero divisor
   of degree one, hence is the divisor of a unique section. Prove compatibility with base change
   and fppf descent. This needs `relative-cartier-divisor` and `polarised-descent`.
10. **(after 7)** The pole filtration of `π_*ℒ_n`: local splittings, the choice of `x` and `y`,
    the unique relation in pole order six, and the unit discriminant.
11. **(after 10)** The bases `1, x, y, x², xy, x³` after a pointed Weierstrass trivialisation, the
    multiplication maps, the relation equal to the Weierstrass equation, and their independence of
    the chosen pointed equation.
12. **(after 1–11; exported)** The Weierstrass-presentation theorem: a smooth proper genus-one
    curve with a section is Zariski-locally pointed-isomorphic to a projective Weierstrass model,
    producing a `PointedWeierstrassAtlas`. This split completes the target.

The previous plan's split "pointed isomorphisms of Weierstrass models are variable changes" is
dropped: `main` already has it, over affine bases
(`WeierstrassCurve.existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom`, in
`Scheme/VariableChange/Basic.lean`) and over arbitrary bases
(`WeierstrassCurve.existsUnique_hom_comp_eq_comp_projModelVariableChangeIso_hom`, in
`Scheme/VariableChange/OverScheme.lean`). The variable-change group and its action on the
coefficients are Mathlib's `WeierstrassCurve.VariableChange`. Split 11 should check what remains
of the README's action on `x`, `y` and the invariant differential before adding any of it.

## Verification

`lake exe cache get`, `lake build` (green, warnings as errors) and
`/opt/round/lookahead-check` all pass.
