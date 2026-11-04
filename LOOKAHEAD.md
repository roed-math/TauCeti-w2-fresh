<!--tauceti-lookahead:v1 {"area":"ModularCurves","slug":"pole-sheaf","main":"333c9e49143de812ed1452b412193ee9c05501e7","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: the pole sheaves 𝒪(n[0]) of a Weierstrass model and their cohomology over a field"},{"n":2,"after":[1],"title":"feat: the divisors n[0] and the pole sheaves 𝒪_E(n[0]) of an elliptic curve"},{"n":3,"after":[1],"title":"feat: H¹ vanishing and locally free H⁰ of 𝒪(n[0]) on a Weierstrass model over a ring"},{"n":4,"after":[2,3],"title":"feat: π_*𝒪_E(n[0]) is locally free of rank n and commutes with base change"},{"n":5,"after":[4],"title":"feat: pushforwards of line bundles of positive fibre degree on an elliptic curve"},{"n":6,"after":[5],"title":"feat: degree-one line bundles and sections of an elliptic curve"},{"n":7,"after":[4],"title":"feat: the pole filtration of π_*𝒪_E(6[0]) and its Weierstrass relation"},{"n":8,"after":[7],"title":"feat: Weierstrass bases of the pole sheaves and their multiplication maps"},{"n":9,"after":[],"title":"feat: pointed isomorphisms of Weierstrass models are variable changes"},{"n":10,"after":[1,2,3,4,5,6,7,8,9],"title":"feat: the Weierstrass-presentation theorem for pointed genus-one curves"}]}-->

# Lookahead: `pole-sheaf` (ModularCurves, Layer 1C)

Built on `main` at `333c9e49143de812ed1452b412193ee9c05501e7`. Status: **partial**. Splits 1
and 2 are on this branch, fully proved, with no `sorry`. Splits 3–10 are the plan for the rest
of the target and are **not** on the branch.

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
  and base change are on `main` too. The fibre criterion first enters at split 6, where the
  zero divisor of the evaluation section must be shown relative effective Cartier on geometric
  fibres.
- `polarised-descent` (open PR #27128, descent of stable opens). `Suggested.lean` pins no
  declaration for it either. It first enters at split 6, for the fppf-descent compatibility of
  the degree-one divisor–section correspondence. It may also enter at split 10, if the
  presentation is descended rather than built Zariski-locally.

Neither supplier's statement was restated, so there are no differences to record.

## What is proved (splits 1–2)

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
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Divisor/PoleSheaf.lean` (new, 191 lines):
  - `WeierstrassCurve.poleSheaf W n`, the line bundle `𝒪(n[0])` on `projModel W` over any ring,
    with `poleSheaf_def`, `mk_poleSheaf_one`, `mk_poleSheaf` (`𝒪(n[0]) ≅ 𝒪([0])^{⊗n}`) and
    `mk_poleSheaf_add`.
  - `pullback_mk_poleSheaf_projModelBaseChange`: compatibility with change of the coefficient
    ring.
  - Over a field `K`:
    - `genus_projModel`: `W.projModel.genus K = 1`.
    - `finrank_cohomology_one_trivial_projModel`: `dim H¹(𝒪) = 1`.
    - `eulerDegree_poleSheaf`: `deg 𝒪(n[0]) = n`.
    - `subsingleton_cohomology_one_poleSheaf`: `H¹(𝒪(n[0])) = 0` for `n > 0`.
    - `finrank_cohomology_zero_poleSheaf`: `dim H⁰(𝒪(n[0])) = n` for `n > 0`.

  These are the fibrewise Riemann–Roch statements of 1C, obtained from `main`'s genus-one
  function-field theory and high-degree line-bundle cohomology.

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

## What remains (splits 3–10, not on this branch)

3. **(after 1)** For `W` elliptic over a ring `R`, on the two-affine cover `D₊(Y) ∪ D₊(Z)` of
   `projModel W`, whose intersection is affine:
   - prove `H¹(projModel W, 𝒪(n[0])) = 0` for `n > 0`;
   - prove `H⁰` is a finite projective `R`-module of rank `n`;
   - prove it commutes with every base change `R → R'`.

   The tools are `main`'s `TauCeti.AlgebraicGeometry.subsingleton_cohomology_one_iff_forall_isMaximal`,
   `projective_cohomology_zero_of_forall_isMaximal`,
   `bijective_cohomologyBaseChange_zero_of_subsingleton_cohomology_one` and
   `finrank_cohomology_zero_pullback_eq_finrank_fiber`, together with split 1's fibre
   statements, transported along `isPullback_projModelBaseChange`. Still needed:
   - the cover lemma;
   - flatness over `R` of the sections of `𝒪(n[0])` on the charts;
   - finiteness of `H¹` over `R`;
   - the identification of the chosen fibre `X ×_R κ(p)` with `projModel (W.map _)`, carrying
     `𝒪(n[0])` to `𝒪(n[0])` at sheaf level (split 1 gives it on classes).
4. **(after 2, 3)** Globalise to `E/S`: `R¹π_*ℒ_n = 0`, `π_*ℒ_n` locally free of rank `n`, and
   arbitrary base change. The chart comparison `pullback_mk_poleSheaf_toTotal` (split 2) reduces
   this to split 3 on an atlas.
5. **(after 4)** The positive-degree theorem: an invertible `M` of constant positive fibre degree
   `d` has `R¹π_*M = 0`, and `π_*M` is locally free of rank `d` and commutes with base change.
6. **(after 5)** For `d = 1`: the evaluation section has a relative effective Cartier zero divisor
   of degree one, hence is the divisor of a unique section. Prove compatibility with base change
   and fppf descent. This needs `relative-cartier-divisor` and `polarised-descent`.
7. **(after 4)** The pole filtration of `π_*ℒ_n`: local splittings, the choice of `x` and `y`,
   the unique relation in pole order six, and the unit discriminant.
8. **(after 7)** The bases `1, x, y, x², xy, x³` after a pointed Weierstrass trivialisation, the
   multiplication maps, and the relation equal to the Weierstrass equation.
9. **(after none)** The variable-change group acting on `x`, `y`, the coefficients and the
   invariant differential. The classification: every pointed isomorphism of projective
   Weierstrass models over a base is induced by a unique variable change, first over affine
   bases and then glued. Check first how much of
   `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/VariableChange/` already provides this.
10. **(after 1–9; exported)** The Weierstrass-presentation theorem: a smooth proper genus-one
    curve with a section is Zariski-locally pointed-isomorphic to a projective Weierstrass model,
    producing a `PointedWeierstrassAtlas`. This split completes the target.

## Verification

`lake exe cache get`, `lake build` (green, warnings as errors), and `#lint in TauCeti` over the
import closure (0 errors, 15 linters) all pass. `/opt/round/lookahead-check` also passes.
