<!--tauceti-lookahead:v1 {"area":"ModularCurves","slug":"pole-sheaf","main":"3a0189695d62134a412200ef4237d0bbb2e95d75","status":"partial","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: the pole sheaves 𝒪(n[0]) of a Weierstrass model and their fibre degrees"},{"n":2,"after":[1],"title":"feat: the divisors n[0] and the pole sheaves 𝒪_E(n[0]) of an elliptic curve"},{"n":3,"after":[],"title":"refactor: share the restriction algebra of global functions on local sections"},{"n":4,"after":[3],"title":"feat: H¹ of a finite-type sheaf on a projective Weierstrass model is finitely generated"},{"n":5,"after":[1,4],"title":"feat: cohomology and base change for line bundles of positive fibre degree on a Weierstrass model"},{"n":6,"after":[4],"title":"feat: H⁰ of a finite-type sheaf on a projective Weierstrass model over a Noetherian ring is finitely generated"},{"n":7,"after":[5,6],"title":"feat: H⁰ of 𝒪(n[0]) on a Weierstrass model is projective of rank n"},{"n":8,"after":[2,5],"title":"feat: R¹π_*M vanishes for line bundles of positive fibre degree on an elliptic curve"},{"n":9,"after":[5],"title":"feat: finite local freeness from finite projective sections over an affine cover"},{"n":10,"after":[7,8,9],"title":"feat: π_*𝒪_E(n[0]) is locally free of rank n"},{"n":11,"after":[],"title":"feat: a criterion for the base change morphism of a direct image on affine sections"},{"n":12,"after":[8,10,11],"title":"feat: π_*M commutes with arbitrary base change for line bundles of positive fibre degree"},{"n":13,"after":[],"title":"feat: the dual of a monomorphism of line bundles is a monomorphism"},{"n":14,"after":[2,10,13],"title":"feat: the pole filtration 𝒪(m[0]) ⊆ 𝒪(n[0]) of a Weierstrass model and of an elliptic curve"},{"n":15,"after":[10],"title":"feat: a fibrewise criterion for the cokernel of a map to a finite projective module to be projective"},{"n":16,"after":[13],"title":"feat: pullback preserves inclusions of effective Cartier divisors whose inverse images are effective Cartier"},{"n":17,"after":[7,10,14,15,16],"title":"feat: the quotients of the pole filtration of a Weierstrass model are projective of rank n - m"},{"n":18,"after":[10,17],"title":"feat: the pole filtration of π_*𝒪_E(n[0]) splits locally, with π_*ℒ_0 ≅ π_*ℒ_1"},{"n":19,"after":[13],"title":"feat: multiplication of the line bundles 𝒪(aD) ⊗ 𝒪(bD) ≅ 𝒪((a + b)D) of an effective Cartier divisor"},{"n":20,"after":[14,19],"title":"feat: the multiplication maps of the pole sheaves of a Weierstrass model and of an elliptic curve"},{"n":21,"after":[],"title":"feat: swapping nested evaluations in a symmetric monoidal category"},{"n":22,"after":[19,21],"title":"feat: the pole algebra ⨁ₙ 𝒪_X(nD) of an effective Cartier divisor"},{"n":23,"after":[20,22],"title":"feat: the pole algebras ⨁ₙ 𝒪(n[0]) of a Weierstrass model and of an elliptic curve"},{"n":24,"after":[20],"title":"feat: multiplication on the graded pieces of the pole filtrations of a Weierstrass model and of an elliptic curve"},{"n":25,"after":[18],"title":"feat: the cokernels of the pole filtration of π_*𝒪_E(n[0]) are locally free of rank n - m"},{"n":26,"after":[17,18],"title":"feat: sections of exact pole order of a Weierstrass model and of an elliptic curve, locally on the base"},{"n":27,"after":[7,9,12],"title":"feat: π_*M is locally free of rank d for line bundles of fibre degree d on an elliptic curve"},{"n":28,"after":[27],"title":"feat: degree-one line bundles and sections of an elliptic curve"},{"n":29,"after":[18,23,24,25,26],"title":"feat: local splittings of the pole filtration of π_*𝒪_E(6[0]) and its Weierstrass relation"},{"n":30,"after":[29],"title":"feat: Weierstrass bases of the pole sheaves and their multiplication maps"},{"n":31,"after":[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30],"title":"feat: the Weierstrass-presentation theorem for pointed genus-one curves"}]}-->

# Lookahead: `pole-sheaf` (ModularCurves, Layer 1C)

Built on `main` at `385ec2ddd8ddf8cc779b78c176308cb9c6b55499`. Status: **partial**. Splits
1–26 are on this branch, fully proved, with no `sorry`. Two of the three clauses of the
positive-degree theorem on `E` (`R¹π_*M = 0` and base change of `π_*M`) are also proved, inside
splits 8 and 12. Splits 27–31 are the plan for the rest of the target and are **not** on the
branch.

History. The first round left tip `a1900430f893` with splits 1 and 2. The second round left tip
`3cb1a6114df7`, adding splits 3, 4 and 5. The third round added splits 6 and 7, so
`H⁰(projModel W, 𝒪(n[0]))` is projective of constant rank `n` over every ring. The fourth round
left tip `543397aab8a1`. The fifth round left tip `7bba41d2eebe`, adding splits 8, 9 and 10:
`R¹π_*ℒ_n = 0`, and `π_*ℒ_n` is locally free of rank `n`. The sixth round left tip `1ca2316d3bfa`.
It merged `main` and added split 11, the general base change morphism `f^* π_* ⟶ π'_* g'^*` of a commutative square
of schemes, with its value on sections and a criterion over affine opens for it to be an
isomorphism. The old split 11 (the base-change clause for `ℒ_n`) is now split 12, and the old
splits 12–16 are renumbered 13–17. The seventh round merged current `main` without
conflicts and added split 12: `π_*ℒ_n` commutes with arbitrary base change. (A proof of split 12
from an earlier session was lost before it was pushed; this is a fresh proof.) The seventh round
left tip `4784a0a14fc1`. The eighth round merged current `main` without conflicts and
proved the Weierstrass-model half of the positive-degree theorem (split 13). For any line bundle
`M` on `projModel W` of positive degree on every fibre, `H¹(M) = 0`, `H⁰(M)` is flat with formation
commuting with base change, and its fibres have dimension the fibre degree. Split 5 now proves this
in general, in the new file `Scheme/PositiveDegree.lean`, and derives the pole-sheaf statements
from it as corollaries, so the pole-sheaf proofs are not duplicated. Split 1's field-level
`dim H⁰(𝒪(n[0])) = n` moved into split 5, where it is now a corollary. The eighth round left tip
`c9cccbd78344`.

The ninth round merged current `main`, which had meanwhile landed its own base change
morphism `AlgebraicGeometry.Scheme.Modules.pushforwardBaseChange` (#27117, flat base change), the
isomorphism criterion `Scheme.Modules.Hom.isIso_of_isBasis` and the base change of sections
`Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear`. These superseded most of the old split 11:
its `TauCeti.AlgebraicGeometry.pushforwardBaseChange` and lemmas, `Hom.isIso_of_bijective_app_of_isBasis`,
`Scheme.Hom.pullbackSectionsLEEquiv` and the generalisation of the private comparison in
`Pullback/BaseChange.lean` are all deleted in favour of `main`'s. What is left of split 11 is the
open-immersion lemmas and a general criterion extracted from `main`'s own flat base change proof
(see below), and split 12 now uses `main`'s API.

The ninth round left tip `61260164e388`. The tenth round (this one) merged current `main`
(`85f3eb5579df`) without conflicts. It then proved, for an
invertible sheaf `M` on `E` of positive degree on every geometric fibre, `R¹π_*M = 0` and that the
formation of `π_*M` commutes with arbitrary base change. The new files are
`Geom/PositiveDegree/DirectImage.lean` and `Geom/PositiveDegree/BaseChange.lean`. Split 12's file
moved to `Geom/PositiveDegree/BaseChange.lean` and now proves the general statement. The ℒ_n
statements of splits 8 and 12 became short corollaries, using the new fact that `ℒ_n` has degree
`n` on every fibre (`eulerDegree_pullback_snd_poleSheaf`). So they share their proofs with the
general statements instead of repeating them.

The tenth round left tip `a3e754886c41`. The eleventh round (this one) found `main` unchanged
(`85f3eb5579df`). It started the pole filtration, the first piece of the README's
"pole-filtration form of the construction", as two new splits 13 and 14. Split 13 is general:
an inclusion `J ⊆ I` of ideal sheaves is a monomorphism, and the dual of a monomorphism of line
bundles is a monomorphism. The proof uses only invertibility for the tensor product, so no local
computation is needed. Split 14 applies this to `𝒪(-n[0]) ⊆ 𝒪(-m[0])`. This gives the
inclusions `𝒪(m[0]) ⟶ 𝒪(n[0])` on a Weierstrass model and on `E`, and the monomorphisms
`π_*ℒ_m ⟶ π_*ℒ_n`. Over a field, it gives the dimension count of the filtration on `H⁰`: the
first step `H⁰(𝒪) ⟶ H⁰(𝒪([0]))` is bijective, and each later step has a one-dimensional
cokernel. The old splits 13–17 are renumbered 15–19.

The eleventh round left tip `c77307f19d38`. The twelfth round (this one) found `main` unchanged
(`85f3eb5579df`) and proved the next piece of the pole filtration over an arbitrary base, as four
new splits 15–18: for `0 < m ≤ n`, the image of `H⁰(𝒪(m[0]))` in `H⁰(𝒪(n[0]))` is a direct summand
with projective quotient of rank `n - m`, on a Weierstrass model over any ring and, over every chart
image `U`, for `Γ(U, π_*ℒ_m) ⊆ Γ(U, π_*ℒ_n)` on `E`. This settles the first bullet of the old
split 17 (now 25), except the `m = 0` case on `E` (see split 25 below). The route differs from the one the old plan sketched:
no specified isomorphism `g^*𝒪(n[0]) ≅ 𝒪(n[0])` is needed. It is enough that the pullback of the
inclusion along any base change is again a monomorphism, which holds because the divisors are
relative effective Cartier (split 16), and then the field statements apply to any monomorphism
(split 17 is stated for every `α : 𝒪(m[0]) ⟶ 𝒪(n[0])` whose fibres are monomorphisms; this is what
lets split 18 transport the inclusion of `E` along the bare `Nonempty` chart isomorphisms). The old
splits 15–19 are renumbered 19–23. Later in the round, the `m = 0` case was also proved on the
model (split 17): every section of `𝒪([0])` is constant over every ring, which replaces split
14's field-only version.

The twelfth round left tip `34752c48f0ac`. The thirteenth round (this one) merged current `main`
(`e8758b7b2f82`, whose only change was a CI workflow) without conflicts. It then closed the `m = 0` case of
the pole filtration on `E`, the first bullet of the old split 21 (now 25): `π_*ℒ_0 ⟶ π_*ℒ_1` is bijective
over every chart image and hence an isomorphism. As the old plan asked, the chain of equivalences
that split 18 used inline is now factored out first, as the semilinear equivalence
`PointedWeierstrassChart.modelCohomologyEquiv`, so the `m > 0` and `m = 0` cases share it. The image
computation `(modelIso.inv ≫ toTotal) ''ᵁ ⊤ = π⁻¹(U)`, which split 10 and split 18 each proved
inline, is now the lemma `PointedWeierstrassChart.image_top_modelIso_inv_toTotal` in split 8. The
round also proved the local splitting of the pole filtration (the second bullet of the old
split 21, now 25): over every chart image and for `0 < m ≤ n`, `Γ(U, π_*ℒ_m)` has a complement in
`Γ(U, π_*ℒ_n)`, from a new general lemma, a submodule with projective quotient is complemented.
These changes enlarge splits 8 and 18 and do not renumber any split.

The thirteenth round left tip `e7170dda8060`. The fourteenth round (this one) found `main`
unchanged (`e8758b7b2f82`) and both suppliers' PRs (#27087, #27128) still open. It built the
**multiplication maps between the pole sheaves**, the next ingredient of the pole-filtration
construction, as two new splits 19 and 20. Split 19 is general: for an effective Cartier divisor
`D` with ideal sheaf `I`, `main`'s multiplication `sheafMul : I^b ⊗ I^a ⟶ I^(a + b)` is an
isomorphism, and dualising it gives `𝒪(aD) ⊗ 𝒪(bD) ≅ 𝒪((a + b)D)`, characterised on local
sections by `(φ ψ)(t s) = φ(s) ψ(t)` and compatible with the inclusions `𝒪(aD) ⟶ 𝒪(a'D)`. Split 20
specialises it to `𝒪(n[0])` on a Weierstrass model and to `ℒ_n` on `E`, compatibly with the pole
filtration of split 14. The old splits 19–23 are renumbered 21–25.

The fourteenth round left tip `458c0088540e`. The fifteenth round (this one) found `main`
unchanged (`e8758b7b2f82`) and both suppliers' PRs (#27087, #27128) still open. It proved the
**algebra laws of the multiplication** of split 19, the first bullet of the old split 23 (now 25),
and assembled the graded commutative algebra `⨁ₙ 𝒪_X(nD)` of an effective Cartier divisor as a
`GradedQuasicoherentAlgebra` on `main`'s API, as two new splits 21 and 22. Split 21 is a general
lemma about symmetric monoidal categories (swapping two nested evaluations to the unit), which
commutativity needs. Split 22 proves unit, associativity and commutativity by evaluating against
the powers of `I` and reducing to the laws of the multiplication of ideal sheaves, which are
those of `𝒪_X`. The old splits 21–25 are renumbered 23–27.

The fifteenth round left tip `0d0714998dd6`. The sixteenth round (this one) merged current `main`
(`b3b0334ab920`, whose changes since `e8758b7b2f82` are CI workflow and configuration files only)
without conflicts. Both suppliers' PRs (#27087, #27128) are still open. It added split 23, the pole
algebras `⨁ₙ 𝒪(n[0])` of a Weierstrass model and `⨁ₙ ℒ_n` of an elliptic curve, which were the
first bullet of the old split 25. The old splits 23–27 are renumbered 24–28.

The sixteenth round left tip `62df7864bbfa`. The seventeenth round (this one) found `main`
unchanged (`b3b0334ab920`) and both suppliers' PRs (#27087, #27128) still open, so it merged
nothing. It attempted the first bullet of split 26, starting with the compatibility of the
multiplication with the pole filtration in the **second** factor (split 20 has only the first),
`ℒ_a ◁ (ℒ_b ⟶ ℒ_b') ≫ μ = μ ≫ (ℒ_(a+b) ⟶ ℒ_(a+b'))`, derived from the first-factor statement
`pre_sheafOfLE_whiskerRight_dualPowMulIso_hom` by moving it across `braiding_poleMul`. The
elaborated proof (cancel the braiding, `braiding_naturality_left`, then the commutativity on both
sides and transport of `pre (sheafOfLE _)` along `add_comm`) goes through, but the kernel check
of the resulting term hits a deterministic timeout, and the round ran out of time before it
could be restructured. Nothing from that attempt is on the branch. See split 26 for the hint.

The seventeenth round left tip `bc439800e8dc`. The eighteenth round (this one) merged current
`main` (`72cbdfb14e3d`) without conflicts. Meanwhile the suppliers' earlier partial PRs #27087 (the
geometric-fibre criterion) and #27128 (descent of stable opens) landed on `main`; their open
successors are #28759 and #28995. The branch still consumes neither. The round then proved the
compatibility of the multiplication with the pole filtration in the **second** factor, by the
first route the previous plan suggested: directly by `uncurry_injective`, mirroring the
first-factor proof. This avoids the kernel timeout of the seventeenth round's attempt through the
braiding. The new declarations are
`Scheme.IdealSheafData.IsEffectiveCartier.sheafOfLE_whiskerRight_powTensorIso_hom`,
`whiskerLeft_pre_sheafOfLE_dualPowMulIso_hom` and `whiskerLeft_dualPowMulIsoOfEq_hom` (split 19),
and `whiskerLeft_poleSheafMap_hom_poleSheafMulIso_hom` for `W` and for `E` (split 20). No split is
renumbered.

The eighteenth round left tip `71ce8a9d1c67`. The nineteenth round (this one) merged current
`main` (`afa08a3ed16f`) without conflicts. Its changes since `72cbdfb14e3d` touch none of the
modules this branch builds on (they are formal groups, `Spf`, analysis and topology files). Both
suppliers' successor PRs (#28759, #28995) are still open, and the branch still consumes neither,
so there are still no stubs. The round rebuilt the whole branch against the new `main` (green, warnings as
errors) and reran `lookahead-check`. It added no new declarations: the remaining splits 24–28 each
need more than the round's time, so it pushed the merged branch rather than leave an unfinished
proof. The next piece to attempt is the first bullet of split 26, the multiplication on the graded
pieces of the pole filtration.

The nineteenth round left tip `cc4fbb17db50`. The twentieth round (this one) found `main` unchanged
(`afa08a3ed16f`), so the merge was a no-op. Both suppliers' successor PRs (#28759, #28995) are
still open, and the branch still consumes neither, so there are still no stubs. The round rebuilt
the whole branch (green, warnings as errors) and reran `lookahead-check` (ok). Most of the round's
hour went to the full rebuild. The time left was too short to prove and rebuild a new piece
safely, so it added no declarations. The next piece is still the first bullet of split 26.

The twentieth round left tip `57939dc96751`. The twenty-first round (this one) again found `main`
unchanged (`afa08a3ed16f`), so the merge was a no-op, and both suppliers' successor PRs (#28759,
#28995) still open; the branch still consumes neither, so there are still no stubs. It rebuilt the
whole branch (green, warnings as errors) and reran `lookahead-check` (ok). It added no
declarations: the first bullet of split 26 needs that a product of sections of exact pole orders
`a` and `b` at `[0]` has exact pole order `a + b`, a local computation at the divisor on each
fibre, which does not fit in what the round had left after the rebuild. The next piece is still
the first bullet of split 26.

The twenty-first round left tip `4773669a55d5`. The twenty-second round (this one) again found
`main` unchanged (`afa08a3ed16f`), so the merge was a no-op, and both suppliers' successor PRs
(#28759, #28995) are still open. The branch still uses neither supplier, so there are still no stubs. The rebuild
replayed from a warm build directory and took about nine minutes (green, warnings as errors), and
`lookahead-check` passed. The round added no declarations. Its remaining half hour was too
short for the exact-pole-order computation that the first bullet of split 26 needs. A later round
that starts with a warm build should go straight to that piece.

The twenty-second round left tip `28a922814bb6`. The twenty-third round (this one) again found
`main` unchanged (`afa08a3ed16f`), so the merge was a no-op, and both suppliers' successor PRs
(#28759, #28995) still open; there are still no stubs. It proved the first bullet of the old split
26, on the Weierstrass model, by a formal route that avoids exact pole orders of sections. The
graded pieces are the cokernels `𝒪((n + 1)[0]) / 𝒪(n[0])` in `(projModel W).Modules`. Tensoring
there preserves cokernels, because the category is braided closed. Multiplying `𝒪((a + 1)[0])` by
the inclusion `𝒪(b[0]) ⟶ 𝒪((b + 1)[0])` factors through multiplying the inclusion
`𝒪(a[0]) ⟶ 𝒪((a + 1)[0])` by `𝒪((b + 1)[0])`, by the two compatibilities of split 20. So the
multiplication passes to the graded pieces and is an isomorphism there. The same proof gives the
statement for `ℒ_n` on `E`. The new split is 24, and the old splits 24–28 are renumbered 25–29.
`#lint in TauCeti` (15 linters) passes on the import closure of the three new modules, with 0
errors in 10105 declarations. It first found a `checkType` timeout on the equation lemma that
`simp [poleSheafGradedMulIso]` generated; the proof now uses `delta`, and the square of the
definition is a named lemma.

The twenty-third round left tip `082a8999c4ab`. The twenty-fourth round (this one) again found
`main` unchanged (`afa08a3ed16f`), so the merge was a no-op, and both suppliers' successor PRs
(#28759, #28995) still open; there are still no stubs. It extended split 24 by iterating the
graded multiplication: the `n`-th graded piece of the pole filtration is the `(n + 1)`-th tensor
power of the first one, the normal sheaf of `[0]`, on `W` and on `E`
(`poleSheafGradedPowIso`, built from `main`'s `TauCeti.tensorPow`). `#lint in TauCeti` (15 linters) passes on the import closure of both graded-multiplication modules, with 0 errors in 10111 declarations. This identifies the pieces
of pole orders two, three and six, where the leading terms of `x`, `y`, `x³` and `y²` live, with
the second, third and sixth powers of one line bundle on `[0]`. No split is renumbered.

The twenty-fourth round left tip `f887f3e423f7`. The twenty-fifth round (this one) merged current
`main` (`385ec2ddd8dd`, 481 files changed since `afa08a3ed16f`, with the same Lake pins) without
conflicts. Among its changes are `Cohomology/Basic.lean`, `Cohomology/QuasiSeparated.lean` and
`EllipticCurve/Weierstrass.lean`, which this branch builds on. `main` also renamed
`Modules/Quasicoherent/Extension.lean` to `Extension/Basic.lean`, but no module on this branch
imports it. Neither change supersedes a declaration of this branch. Both suppliers' successor PRs
(#28759, #28995) are still open, and the branch still uses neither, so there are still no stubs.
Most of the round went to the rebuild against the new `main` (green, warnings as errors), followed
by `lookahead-check` (ok), so it added no declarations. The next piece is still split 25 (finite
presentation of `H⁰(projModel W, M)` for general `M`) or the leading terms of split 27.

The twenty-fifth round left tip `d4dbdd28fb59`. The twenty-sixth round (this one) found `main`
unchanged (`385ec2ddd8dd`), so the merge was a no-op. Both suppliers' successor PRs (#28759,
#28995) are still open, and the branch still uses neither, so there are still no stubs. The round
started about forty minutes before its deadline. It rebuilt the whole branch from a warm build
directory (green, warnings as errors) and reran `lookahead-check` (ok). The time left was too
short to prove and check a new piece, so it added no declarations. The next piece is still split
25 (finite presentation of `H⁰(projModel W, M)` for general `M`) or the leading terms of split 27.

The twenty-sixth round left tip `a1d70b406c22`. The twenty-seventh round (this one) again found
`main` unchanged (`385ec2dd`), so the merge was a no-op. Both suppliers' successor PRs (#28759,
#28995) are still open, and the branch still uses neither, so there are still no stubs. It rebuilt
the whole branch from a warm build directory in about nine minutes (green, warnings as errors) and
reran `lookahead-check` (ok). The round started about forty-five minutes before its deadline, which
was too short to prove and check a new piece, so it added no declarations. The next piece is still
split 25 (finite presentation of `H⁰(projModel W, M)` for general `M`) or the leading terms of
split 27. A round with a full hour should start on one of them right after the warm rebuild.

The twenty-seventh round left tip `7ab866900b42`. The twenty-eighth round (this one) again found
`main` unchanged (`385ec2dd`), so the merge was a no-op. Both suppliers' successor PRs (#28759,
#28995) are still open, and the branch still uses neither, so there are still no stubs. After the
warm rebuild it did the reusable half of split 25: `Geom/PoleSheaf/LocallyFree.lean` (split 10)
now proves its chart-to-sheaf steps for an arbitrary `𝒪_E`-module `M`
(`finite_projective_sections_of_restrict_iso`,
`isFiniteLocallyFree_pushforward_of_finite_projective_sections`,
`rank_pushforward_of_finite_projective_sections`), and the `ℒ_n` statements are now corollaries.
The general lemmas replace `finite_projective_sections_pushforward_poleSheaf`. It also dropped two
manual quasi-coherence `have`s (in `LocallyFree.lean` and `Geom/PositiveDegree/BaseChange.lean`),
which `main`'s instance `InvertibleSheaf.isQuasicoherent_obj` now supplies. What remains of split 25
is only the finiteness of `H⁰(projModel W, M)` over a non-Noetherian base, described below.

The twenty-ninth round left tip `0cbbf51989ca`. The thirtieth round (this one) again found
`main` unchanged (`385ec2dd`), so the merge was a no-op. Both suppliers' successor PRs (#28759,
#28995) are still open, and the branch still uses neither, so there are still no stubs. It proved
the sheaf-level bullet of the old split 27, as the new split 25. For `0 < m ≤ n` the cokernel of
`π_*ℒ_m ⟶ π_*ℒ_n` is finite locally free of rank `n - m`. The missing input was the sections of a
cokernel over an affine open. The new general file `Modules/Quasicoherent/CokernelSections.lean`
supplies it, from left exactness of sections and `main`'s surjectivity on affine opens. The old
splits 25–29 are renumbered 26–30.

The thirtieth round left tip `53ab971ecd48`. The thirty-first round (this one) again found
`main` unchanged (`385ec2dd`), so the merge was a no-op. Both suppliers' successor PRs (#28759,
#28995) are still open, and the branch still uses neither, so there are still no stubs. It rebuilt
the whole branch from a warm build directory (green, warnings as errors, about eleven minutes) and
reran `lookahead-check` (ok). Only about twenty-five minutes were left after the rebuild, which was
too short to prove and check a new piece, so it added no declarations. The next piece is still
split 26 (finite presentation of `H⁰(projModel W, M)` for general `M`) or the choice of `x` and
`y` in split 28.

The thirty-first round left tip `9beab6be85e7`. The thirty-second round (this one) again found
`main` unchanged (`385ec2dd`), so the merge was a no-op. Both suppliers' successor PRs (#28759,
#28995) are still open, and the branch still uses neither, so there are still no stubs. After
starting the warm rebuild it added the new split 26, the local choice of the Weierstrass
coordinates: over a local ring, each step `H⁰(𝒪((n - 1)[0])) ⊆ H⁰(𝒪(n[0]))`, `n ≥ 2`, of the pole
filtration of a Weierstrass model has a free complement of rank one. The old splits 26–30 are
renumbered 27–31.

The thirty-second round left tip `88af4e2e89a4`. The thirty-third round (this one) merged current
`main` (`3a0189695d62`), whose only new commit since `385ec2dd` changes CI workflows, so no module of
this branch is affected. Both suppliers' successor PRs (#28759, #28995) are still open, and the
branch still uses neither, so there are still no stubs. While the warm rebuild ran, it added to
split 26 the algebra that spreads the local choice of `x` and `y` out to a neighbourhood:
`TauCeti.Module.exists_notMem_bijective_localizedModule_map_toSpanSingleton`. A finite projective
module of rank one at a prime `p` is free on one element after inverting some `g ∉ p`. It then
applied this on `E`, in the new `Geom/PoleSheaf/LocalCoordinates.lean`
(`exists_notMem_bijective_toSpanSingleton_mkQ_range_pushforward_poleSheafMap`). Over a chart image
and near any point of `S`, a section of `π_*ℒ_n`, `n ≥ 2`, freely generates the rank-one quotient by
`π_*ℒ_(n-1)`. This is the choice of `x` and `y` on `E` that the old split 29 needed. Split 26 now
also needs split 18.

## Suppliers and stubs

**No stubs were needed, and the branch has no `TauCeti/Lookahead/` module.** The proved part
consumes neither supplier:

- `relative-cartier-divisor` (its partial PR #27087, the geometric-fibre criterion of 0A
  item 1, landed on `main` before the eighteenth round; the open successor is PR #28759, the
  fibre criterion after base change; neither is used by splits 1–23).
  `Suggested.lean` pins no declaration for it. Its §Finite flat group schemes says the carrier
  "is supplied once by the Jacobian Challenge", and the file "deliberately introduces no
  substitute". PR #27087 adds
  `Scheme.IdealSheafData.isRelativeEffectiveCartier_iff_forall_isEffectiveCartier_comap_fst_of_isAlgClosed`.
  The divisor `[0]` does not need it: a section of a smooth separated curve already cuts out a
  relative effective Cartier divisor, by
  `Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension` on `main`, and sums
  and base change are on `main` too. Splits 16–18 need only that `m[0]` and `n[0]` pull back to
  effective Cartier divisors along base changes of the model, which `main`'s
  `zeroSectionDivisor_pow_map` and split 2 give. The fibre criterion first enters at split 28,
  where the zero divisor of the evaluation section must be shown relative effective Cartier on geometric
  fibres.
- `polarised-descent` (its partial PR #27128, descent of stable opens, landed on `main` before
  the eighteenth round; the open successor is PR #28995, descent of schemes affine over a
  descended scheme; neither is used by splits 1–24 and 26). `Suggested.lean` pins no
  declaration for it either. It first enters at split 28, for the fppf-descent compatibility of
  the degree-one divisor–section correspondence. It may also enter at split 31, if the
  presentation is descended rather than built Zariski-locally.

Neither supplier's statement was restated, so there are no differences to record.

## What is proved (splits 1–26)

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

PR subject: `feat: R¹π_*M vanishes for line bundles of positive fibre degree on an elliptic curve`

- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/GlobalSections.lean` (+51/−30 lines, 152 in
  total). Steps of the existing proof of `isIso_structureMap_app` become public, because the new
  files need them:
  - `PointedWeierstrassChart.isOpenImmersion_toTotal` (instance): `toTotal` is an open immersion.
  - `PointedWeierstrassChart.opensRange_toTotal`: its image is `π⁻¹(U)` for `U` the image of the
    base. `isIso_app_opensRange` now uses it.
  - `PointedWeierstrassAtlas.isBasis_range_opensRange_restrict`: the images of the restricted
    charts form a basis of `S`. `isIso_structureMap_app` is now three lines.
  - `PointedWeierstrassChart.image_top_modelIso_inv_toTotal`: the image of the model under
    `modelIso.inv ≫ toTotal` is `π⁻¹(U)`. Splits 10 and 18 use it.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/PositiveDegree/DirectImage.lean` (new, 216
  lines), namespace `TauCeti.AlgebraicGeometry`:
  - `PointedWeierstrassAtlas.exists_eq_specMap_comp_baseMap`: every point `Spec K ⟶ S` with
    values in a field factors as `Spec K ⟶ Spec R ≅ base ⟶ S` through a chart of an atlas.
  - `EllipticCurveGeom.eulerDegree_pullback_snd_specMap_comp`: over such a point, the degree of a
    line-bundle class on the fibre `Spec K ×_S E` is its degree on the Weierstrass model of the
    chart over `K`. This pastes `main`'s `PointedWeierstrassChart.isPullback_modelIso_inv_toTotal`
    with `WeierstrassCurve.isPullback_projModelBaseChange` and uses `main`'s
    `LineBundleClass.eulerDegree_pullback_of_isIso`.
  - `EllipticCurveGeom.exists_eulerDegree_pullback_projModelBaseChange_eq`: the degree of `M` on
    the fibre over a prime `p` of the model of a chart is the degree of `M` on the geometric fibre
    of `E` over a point `Spec Ω ⟶ S`, `Ω` an algebraic closure of `κ(p)`. This also uses `main`'s
    invariance of the degree under field extension, `LineBundleClass.eulerDegree_pullback`.
  - `EllipticCurveGeom.eulerDegree_pullback_projModelBaseChange_pos`: for `M` of positive degree on
    every geometric fibre, the restriction of `M` to the model of every chart satisfies split 5's
    hypothesis.
  - `EllipticCurveGeom.subsingleton_cohomologyOn_one_of_forall_eulerDegree_pos`:
    `H¹(π⁻¹(U), M) = 0` over a chart image `U` (via `Scheme.Modules.cohomologyOnOpensRangeIso`
    and split 5).
  - `EllipticCurveGeom.isZero_higherDirectImage_one_of_forall_eulerDegree_pos`: **`R¹π_*M = 0`
    for `M` of positive degree on every geometric fibre** (via
    `Scheme.Hom.isZero_higherDirectImage_succ_of_isBasis`). This is the first clause of the
    README's positive-degree theorem.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/PoleSheaf/DirectImage.lean` (new, 106
  lines), namespace `TauCeti.AlgebraicGeometry.EllipticCurveGeom`:
  - `pullback_mk_poleSheaf_modelIso_inv_toTotal` and `nonempty_restrict_poleSheaf_iso`: on a
    chart, `ℒ_n` restricts along `modelIso.inv ≫ toTotal` to the model's
    `WeierstrassCurve.poleSheaf n`.
  - `eulerDegree_pullback_snd_poleSheaf`: **`ℒ_n` has degree `n` on the fibre over every point
    `Spec K ⟶ S` with values in a field** (via `WeierstrassCurve.eulerDegree_pullback_poleSheaf`,
    split 1).
  - `isZero_higherDirectImage_one_poleSheaf`: **`R¹π_*ℒ_n = 0`** for `n > 0`, as a corollary of
    the general statement.

The hypothesis on `M` is stated directly, for every algebraically closed `Ω` and `ξ : Spec Ω ⟶ S`,
as `0 < LineBundleClass.eulerDegree Ω (LineBundleClass.pullback (pullback.snd ξ π) (.mk M))`, with
`Spec Ω ×_S E` over `Spec Ω` through `pullback.fst`. This is exactly the right-hand side of
`main`'s public `TauCeti.AlgebraicGeometry.relativePicardFiberDegree_mk`, which computes the fibre
degree of the relative Picard functor. It does not go through the Picard quotient: that would
require viewing `S` as the object `Over.mk (𝟙 S)`, whose fibre `pullback (ξ ≫ 𝟙 S) π` is a
different scheme. The README asks for degree `d > 0` on every geometric fibre; the statements here
only need positivity, so they are slightly more general.

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
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/PoleSheaf/LocallyFree.lean` (new, 258
  lines), namespace `TauCeti.AlgebraicGeometry.EllipticCurveGeom`. Since the twenty-eighth round the
  file proves the chart-to-sheaf steps for an arbitrary `𝒪_E`-module `M`, so that split 27 can reuse
  them, and derives the `ℒ_n` statements as corollaries:
  - `finite_projective_sections_of_restrict_iso`: if the restriction of `M` to the model of a chart
    is isomorphic to a module with finite projective global sections of constant rank `d`, then
    `Γ(π⁻¹(U), M)` is finite projective of rank `d` over `Γ(E, π⁻¹(U))` for the chart image `U`.
  - `finite_projective_sections_poleSheaf`: `Γ(π⁻¹(U), ℒ_n)` is finite projective of rank `n`
    over `Γ(E, π⁻¹(U))` for a chart image `U` (a corollary, through
    `nonempty_restrict_poleSheaf_iso`).
  - `finite_projective_sections_pushforward_of_finite_projective_sections` and
    `rankAtStalk_sections_pushforward_of_finite_projective_sections`: the same for `Γ(U, π_*M)`
    over `Γ(S, U)`, through `isIso_app_opensRange`. (They replace the former
    `finite_projective_sections_pushforward_poleSheaf`, which had no other user.)
  - `isFiniteLocallyFree_pushforward_of_finite_projective_sections` and
    `rank_pushforward_of_finite_projective_sections`: for quasi-coherent `M` with such sections over
    every chart preimage, `π_*M` is finite locally free (of rank `d`).
  - `isFiniteLocallyFree_pushforward_poleSheaf`: **`π_*ℒ_n` is finite locally free.**
  - `rank_pushforward_poleSheaf`: **it has rank `n` at every point.**

### Split 11 — after: none

PR subject: `feat: a criterion for the base change morphism of a direct image on affine sections`

General infrastructure, independent of elliptic curves; it builds on `main` alone.
- `TauCeti/AlgebraicGeometry/Modules/Pullback/Sections.lean` (+57/−22 lines, 201 in total):
  - `AlgebraicGeometry.Scheme.Hom.restrictFunctorIsoPullback_hom_app_app_map`: along an open
    immersion `j`, `restrictFunctorIsoPullback` carries the restriction of `s` to `j (j⁻¹ U)` to
    `j.pullbackSections M U s`.
  - `AlgebraicGeometry.Scheme.Hom.bijective_pullbackSections_of_isOpenImmersion`: hence pulling
    back sections over `U ≤ j.opensRange` is bijective. Split 12 uses it to identify the sections
    of `g^* ℒ_n` over `π'⁻¹ V` with those of its pullback to the open subscheme `π'⁻¹ V`.
  - `AlgebraicGeometry.Scheme.Hom.bijective_pullbackSectionsLE_of_isOpenImmersion`: the same
    from `U` to any open equal to `j⁻¹ U`. `main`'s `Scheme.Modules.bijective_pullbackSectionsLE_ι`
    is the special case `j = U.ι`, and its 25-line proof becomes a two-line application.
- `TauCeti/AlgebraicGeometry/Modules/Pullback/BaseChange.lean` (+1/−13 lines): the private
  `chartPullback_unit` calls `restrictFunctorIsoPullback_hom_app_app_map` instead of repeating its
  proof.
- `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/Pushforward/BaseChange.lean` (+70/−38 lines,
  169 in total):
  - `AlgebraicGeometry.Scheme.Modules.bijective_pushforwardBaseChange_app_app_of_isBaseChange`:
    for **any** commutative square `g' ≫ f = f' ≫ g` with `f_* M` quasi-coherent, and affine opens
    `W' ≤ g⁻¹ W`, the base change morphism is bijective on the sections over `W'` as soon as some
    `Γ(S, W)`-linear map `ψ` with `ψ s = g'^* s` exhibits `Γ(f'⁻¹ W', g'^* M)` as a base change of
    `Γ(f⁻¹ W, M)` along `Γ(S, W) → Γ(S', W')` (the algebra and module structures are parameters,
    with the algebra map required to be `g.appLE`). This is the first half of `main`'s proof of
    `bijective_pushforwardBaseChange_app_app` (flat base change), extracted.
  - `bijective_pushforwardBaseChange_app_app` keeps its statement and becomes an application of
    it, with `isBaseChange_pullbackSectionsLEBaseLinear_of_isQuasiSeparated`.

### Split 12 — after: 8, 10, 11

PR subject: `feat: π_*M commutes with arbitrary base change for line bundles of positive fibre degree`

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
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/PositiveDegree/BaseChange.lean` (new, 416
  lines; the former `Geom/PoleSheaf/BaseChange.lean`, generalised from `ℒ_n` to `M`), namespace
  `TauCeti.AlgebraicGeometry`:
  - private, general: `bijective_appLE`, the ring-level analogue of split 11's
    `bijective_pullbackSectionsLE_of_isOpenImmersion`. (The former private `appLE_eq_of_eq`
    duplicated `Scheme.Hom.congr_appLE` in `TauCeti/AlgebraicGeometry/Restrict.lean`, which is used
    instead.)
  - private, in `PointedWeierstrassChart` for a chart pair `(k, c, h, hh)` over the base change
    square `hg`: `opensRange_modelIso_inv_toTotal`, `top_le_preimage_modelIso_inv_toTotal`,
    `opensRange_le_preimage_opensRange`, `preimage_le_preimage_preimage`,
    `modelMap_comp_modelIso_inv_toTotal`, the ring-map identities `appLE_comp_app_comp_appLE`
    and `app_comp_appLE`, `isPullback_modelMap_over` (main's `isPullback_modelMap` read over
    `Spec c.ring ← Spec k.ring` with the algebra `Spec.preimage`), `pullbackModelIso` (the
    identification of `g^*M` on the model of `k` with the pullback of `M|_c` along `modelMap`)
    and `pullbackModelIso_hom_app_pullbackSectionsLE` (its value on pulled-back sections).
  - private `EllipticCurveGeom.bijective_pushforwardBaseChange_app_app_of_forall_eulerDegree_pos`:
    over a chart pair, the base change morphism of `π_*M` is bijective on the sections over `V`,
    by split 11's criterion: pulling back sections of `M` from `π⁻¹ U` to `π'⁻¹ V` is a base
    change. This is `WeierstrassCurve.bijective_cohomologyBaseChange_zero_of_forall_eulerDegree_pos`
    (split 5) for the model square, whose hypothesis is split 8's
    `eulerDegree_pullback_projModelBaseChange_pos`, transported along `H⁰ ≅ Γ(⊤)`, the ring
    isomorphisms `Γ(S, U) ≅ c.ring` and `Γ(S', V) ≅ k.ring` (through
    `bijective_baseRingToGlobalSections`, split 10) and `IsBaseChange.restrictScalars_of_bijective`.
  - `EllipticCurveGeom.isIso_pushforwardBaseChange_app_of_forall_eulerDegree_pos`: **for `M` of
    positive degree on every geometric fibre, the base change morphism `f^* π_* M ⟶ π'_* g^* M` is
    an isomorphism**, by `main`'s `Scheme.Modules.Hom.isIso_of_isBasis` on the basis of images of
    chart bases of `E'` lying over a chart of `E` (`exists_chart_comp_baseMap` on `main`,
    restricted to affine opens). This is the base change clause of the README's positive-degree
    theorem.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/PoleSheaf/BaseChange.lean` (new, 82 lines),
  namespace `TauCeti.AlgebraicGeometry.EllipticCurveGeom`:
  - `isIso_pushforwardBaseChange_app_poleSheaf`: for `n > 0`, **`f^* π_* ℒ_n ⟶ π'_* g^* ℒ_n` is an
    isomorphism**, as a corollary through `eulerDegree_pullback_snd_poleSheaf` (split 8).
  - `nonempty_pullback_pushforward_poleSheaf_iso`: **`f^* π_* ℒ_n ≅ π'_* ℒ'_n`** when `g`
    is compatible with the zero sections (via `pullback_mk_poleSheaf_of_isPullback`, split 2).

### Split 13 — after: none

PR subject: `feat: the dual of a monomorphism of line bundles is a monomorphism`

General infrastructure, independent of elliptic curves; it builds on `main` alone.
- `TauCeti/AlgebraicGeometry/IdealSheaf/Inclusion.lean` (new, 85 lines), namespace
  `AlgebraicGeometry.Scheme.IdealSheafData`, following `IdealSheaf/Module.lean`:
  - `sections_mono`: for `J ≤ I`, the sections of `J` over any open lie in `I`. This is checked
    on affine opens, where the sections are the recorded ideals.
  - `sheafOfLE`: the inclusion `J.sheaf ⟶ I.sheaf` (via `sheafLift`), with `sheafOfLE_sheafι`,
    the instance `mono_sheafOfLE`, `sheafOfLE_refl` and `sheafOfLE_comp`.
  These are a new module only to keep the rebuild small. The port may append them to
  `IdealSheaf/Module.lean` (212 lines) instead.
- `TauCeti/AlgebraicGeometry/LineBundle/Dual/Map.lean` (new, 150 lines), namespace
  `TauCeti.AlgebraicGeometry.InvertibleSheaf`:
  - `dual_obj_eq_ihom`: the underlying sheaf of `dual L` is `(ihom L.obj).obj (𝟙_ X.Modules)`.
    `dual` is not exposed, and `dual_obj` states this in `SheafOfModules`.
  - `dualMap f : dual L ⟶ dual K` for `f : K ⟶ L`, precomposition with `f`, with `dualMap_hom`,
    `dualMap_id` and `dualMap_comp`.
  - `mono_whiskerLeft_dual`: `L^∨ ⊗ -` preserves monomorphisms. It is `ihom L` up to the
    isomorphism `dualTensorIhom` on `main`, and `ihom L` is a right adjoint.
  - `mono_of_mono_whiskerLeft`: `L ⊗ -` reflects monomorphisms, since `L^∨ ⊗ L ≅ 𝒪_X`.
  - `mono_dualMap_hom` (instance): **the dual of a monomorphism of line bundles is a
    monomorphism**. `K ⊗ dualMap f` is `f ⊗ L^∨` up to the evaluation isomorphisms (Mathlib's
    `id_tensor_pre_app_comp_ev`).
- `TauCeti/AlgebraicGeometry/EffectiveCartierDivisor/Inclusion.lean` (new, 104 lines), namespace
  `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier`:
  - `toInvertibleSheafMap hI hJ h`: the inclusion `J ⟶ I` of invertible ideal sheaves, with
    `toInvertibleSheafMap_hom`, the instance `mono_toInvertibleSheafMap_hom`,
    `toInvertibleSheafMap_refl` and `toInvertibleSheafMap_comp`.
  - `dualMap hI hJ h`: its dual `𝒪(D') ⟶ 𝒪(D)`, with the instance `mono_dualMap_hom`,
    `dualMap_refl` and `dualMap_comp`.

### Split 14 — after: 2, 10, 13

PR subject: `feat: the pole filtration 𝒪(m[0]) ⊆ 𝒪(n[0]) of a Weierstrass model and of an elliptic curve`

- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Divisor/PoleSheaf/Filtration.lean` (new, 148
  lines), namespace `WeierstrassCurve`:
  - `zeroSectionDivisor_pow_le_pow`: `𝒪(-n[0]) ≤ 𝒪(-m[0])` for `m ≤ n`.
  - `poleSheafMap h : W.poleSheaf m ⟶ W.poleSheaf n`, with `poleSheafMap_def` (through
    `poleSheaf_def`; the body of `poleSheaf` stays unexposed), the instance
    `mono_poleSheafMap_hom`, `poleSheafMap_refl` and `poleSheafMap_comp`.
  - `injective_cohomologyMapBaseLinear_poleSheafMap`: `H⁰(𝒪(m[0])) ↪ H⁰(𝒪(n[0]))` over any ring
    (`main`'s `cohomologyMap_injective`).
  - Over a field `K`:
    - `finrank_cohomology_zero_trivial_projModel`: `dim H⁰(projModel W, 𝒪) = 1`, from
      `bijective_baseRingToGlobalSections` (split 10). It needs no ellipticity; the port may
      move it next to `finrank_cohomology_one_trivial_projModel` (split 1) if that file then
      imports `FiniteCohomology.lean`.
    - `finrank_cohomology_zero_poleSheaf_zero`: `dim H⁰(𝒪(0[0])) = 1`.
    - `finrank_quotient_range_cohomologyMapBaseLinear_poleSheafMap`: **the successive quotients
      `H⁰(𝒪((n+1)[0])) / H⁰(𝒪(n[0]))`, `n > 0`, are lines**. (Split 17's rank statement is the
      general form; the port may derive this one from it, or drop it, if a reviewer asks.)
  - The field-only `bijective_cohomologyMapBaseLinear_poleSheafMap_zero_one` of the eleventh
    round was deleted in the twelfth: split 17 proves it over every ring, under the same name.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/PoleSheaf/Filtration.lean` (new, 97
  lines), namespace `TauCeti.AlgebraicGeometry.EllipticCurveGeom`:
  - `zeroDivisor_pow_le_pow`, `poleSheafMap`, `poleSheafMap_def`, the instance
    `mono_poleSheafMap_hom`, `poleSheafMap_refl` and `poleSheafMap_comp` on `E`.
  - `mono_pushforward_map_poleSheafMap`: **the pole filtration `π_*ℒ_m ⟶ π_*ℒ_n` of
    `π_*ℒ_n`** is by monomorphisms.

### Split 15 — after: 10

PR subject: `feat: a fibrewise criterion for the cokernel of a map to a finite projective module to be projective`

General commutative algebra, independent of geometry.
- `TauCeti/RingTheory/Flat/Fiber.lean` (+82 lines, 222 in total; it imports
  `Mathlib.RingTheory.Spectrum.Prime.FreeLocus` in addition), section `Cokernel`, namespace
  `Module`:
  - `Module.Projective.quotient_range_of_injective_baseChange`: for `f : M →ₗ[R] N` with `M`
    finite and `N` finite projective, if `f.baseChange κ(p)` is injective for every maximal ideal
    `p`, then `N ⧸ range f` is projective. Over `R_p`, `N_p` is free and Mathlib's
    `Module.free_of_lTensor_residueField_injective` makes the localized cokernel free (the residue
    field of `R_p` is `κ(p)`, compared through `AlgebraTensorModule.cancelBaseChange`); then
    `flat_of_isLocalized_maximal` and finite presentation.
  - `Module.rankAtStalk_quotient_range_add`: if moreover `M` is projective and the condition holds
    at every prime, the rank of the cokernel plus the rank of `M` is the rank of `N`.
- `TauCeti/Algebra/Module/Projective/RingEquiv.lean` (split 10's file; +40 lines, 112 in total),
  section `QuotientRange`: for semilinear equivalences `eP`, `eQ` over a ring isomorphism with
  `eQ ∘ f = f' ∘ eP`,
  - `LinearEquiv.map_range_eq_range`: `eQ` carries `range f` onto `range f'`;
  - `LinearEquiv.projective_quotient_range`: projectivity of `Q ⧸ range f` transfers to
    `Q' ⧸ range f'`;
  - `LinearEquiv.rankAtStalk_quotient_range_eq`: so does the rank, at `σ⁻¹(q)`.

### Split 16 — after: 13

PR subject: `feat: pullback preserves inclusions of effective Cartier divisors whose inverse images are effective Cartier`

General infrastructure. Pullback is not left exact, but it preserves these inclusions.
- `TauCeti/AlgebraicGeometry/EffectiveCartierDivisor/Inclusion.lean` (split 13's file, +5 lines):
  `Scheme.IdealSheafData.IsEffectiveCartier.dualMap_def` (the body of `dualMap` is not exposed,
  and the new file must unfold it). The port should put this lemma into split 13 itself.
- `TauCeti/AlgebraicGeometry/EffectiveCartierDivisor/Inclusion/Pullback.lean` (new, 179 lines):
  - `TauCeti.AlgebraicGeometry.InvertibleSheaf.mono_whiskerLeft` and `mono_whiskerRight`:
    tensoring with a line bundle preserves monomorphisms (a line bundle is the dual of its dual,
    through `LineBundleClass.mk_eq_mk_iff`, and split 13's `mono_whiskerLeft_dual`).
  - `TauCeti.AlgebraicGeometry.InvertibleSheaf.mono_pullback_map_dualMap_hom`: if `g^* f` is a
    monomorphism for a morphism `f : K ⟶ L` of line bundles, so is `g^*` of `dualMap f`. The proof
    is split 13's, pushed through the oplax tensor comparisons `δ` of `pullback g`, which are
    isomorphisms on quasicoherent factors (`isIso_pullback_δ_of_isQuasicoherent` on `main`).
  - `Scheme.IdealSheafData.pullback_map_sheafOfLE_comp_pullbackSheafHom`: the pullback of the
    inclusion `J ⟶ I` is `J.comap g ⟶ I.comap g` up to `pullbackSheafHom` (on `main`).
  - `Scheme.IdealSheafData.IsEffectiveCartier.mono_pullback_map_sheafOfLE`,
    `mono_pullback_map_toInvertibleSheafMap_hom` and `mono_pullback_map_dualMap_hom`: when `J ≤ I`
    and their inverse images along `g` are effective Cartier, the pullbacks of `J ⟶ I` and of
    `𝒪(D') ⟶ 𝒪(D)` are monomorphisms (`isIso_pullbackSheafHom` on `main`).

### Split 17 — after: 7, 10, 14, 15, 16

PR subject: `feat: the quotients of the pole filtration of a Weierstrass model are projective of rank n - m`

- `TauCeti/AlgebraicGeometry/Modules/Pullback/UnitSections.lean` (new, 45 lines):
  `AlgebraicGeometry.Scheme.Hom.pullbackObjUnitIso_hom_app_pullbackSections`: pulling back a
  function `s` as a section of `𝒪_X` and identifying `g^*𝒪_X ≅ 𝒪_Y` gives `g^♯ s` (from
  `pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom` on `main`). A new module only to
  keep the rebuild small; the port should put it in `Modules/Pullback/Sections.lean`.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Divisor/PoleSheaf/FiltrationQuotient.lean` (new,
  321 lines), namespace `WeierstrassCurve`, for `W` elliptic over any ring `R`:
  - `mono_pullback_map_poleSheafMap_hom`: the pullback of `poleSheafMap h : 𝒪(m[0]) ⟶ 𝒪(n[0])`
    along `projModelBaseChange f` is a monomorphism, for every ring map `f` (split 16, with
    `zeroSectionDivisor_pow_map` on `main`).
  - `injective_baseChange_cohomologyMapBaseLinear_of_mono_pullback`: for any
    `α : (W.poleSheaf m).obj ⟶ (W.poleSheaf n).obj` whose pullback to the model over `R'` is a
    monomorphism, `R' ⊗ H⁰(α)` is injective as soon as the base change map of `H⁰(𝒪(m[0]))` is
    (naturality `cohomologyMapBaseLinear_comp_cohomologyBaseChange` on `main`, and
    `cohomologyMap_injective`). For `m > 0` that hypothesis is split 5's bijectivity.
  - For such `α` with monomorphic pullbacks to all fibres and `0 < m ≤ n`:
    `projective_quotient_range_cohomologyMapBaseLinear_of_mono_pullback` and
    `rankAtStalk_quotient_range_cohomologyMapBaseLinear_of_mono_pullback`: the quotient
    `H⁰(𝒪(n[0])) ⧸ H⁰(α)(H⁰(𝒪(m[0])))` is projective of rank `n - m` (split 15 with split 7).
  - The corollaries for `α = poleSheafMap h`:
    `injective_baseChange_cohomologyMapBaseLinear_poleSheafMap`,
    `projective_quotient_range_cohomologyMapBaseLinear_poleSheafMap` and
    `rankAtStalk_quotient_range_cohomologyMapBaseLinear_poleSheafMap`. With `n = m + 1` these say
    that the successive quotients of the pole filtration on `H⁰` are invertible `R`-modules.
  - The case `m = 0`, where split 5 does not apply (`𝒪(0[0])` has degree zero):
    - private `exists_basis_cohomology_poleSheaf_zero`: `H⁰(𝒪(0[0]))` is free on the class `s`
      of the section corresponding to the function `1` (through `unitHomEquivTop` on `main` and
      `bijective_baseRingToGlobalSections`), and the pullback of `s` to the model over any field
      is nonzero (it is the function `1`, by `pullbackObjUnitIso_hom_app_pullbackSections`).
    - `injective_cohomologyBaseChange_zero_poleSheaf_zero`: hence `K ⊗ H⁰(𝒪(0[0])) ⟶
      H⁰(g^*𝒪(0[0]))` is injective over every field `K`.
    - `bijective_cohomologyMapBaseLinear_of_mono_pullback_zero_one`: any `α : 𝒪(0[0]) ⟶ 𝒪([0])`
      with monomorphic pullbacks to the fibres is bijective on `H⁰` (the cokernel is projective of
      rank `1 - 1 = 0`; then Mathlib's `Module.bijective_of_surjective_of_rankAtStalk_eq`).
    - `bijective_cohomologyMapBaseLinear_poleSheafMap_zero_one`: **every section of `𝒪([0])` is
      constant, over any ring**, `H⁰(𝒪) ≅ H⁰(𝒪([0]))` (the row `n = 1: 1` of the README's table).
      This replaces split 14's field-only lemma of the same name.

### Split 18 — after: 10, 17

PR subject: `feat: the pole filtration of π_*𝒪_E(n[0]) splits locally, with π_*ℒ_0 ≅ π_*ℒ_1`

- `TauCeti/AlgebraicGeometry/Modules/AppLinear.lean` (new, 42 lines):
  `AlgebraicGeometry.Scheme.Modules.Hom.appLinear φ U : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U)` and
  `Hom.appLinear_apply`. `Hom.app` lands in abelian groups and `(φ.val.app (op U)).hom` is linear
  over a ring that is only defeq to `Γ(X, U)`, so the quotient of `Γ(N, U)` by its range has no
  `Γ(X, U)`-module instance; neither Mathlib nor `TauCeti/` has this map. It is a new module only
  to keep the rebuild small: the port should put it in `TauCeti/AlgebraicGeometry/Modules/Sheaf.lean`
  next to `sectionsLinearEquiv`.
- `TauCeti/Algebra/Module/Projective/Complement.lean` (new, 46 lines):
  `Submodule.exists_isCompl_of_projective_quotient`: a submodule with projective quotient has a
  complement (the kernel of `x ↦ x - s (x mod p)` for a section `s` of the quotient map, through
  Mathlib's `Module.projective_lifting_property` and `LinearMap.isCompl_of_proj`). Neither Mathlib
  nor `TauCeti/` has this statement.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/PoleSheaf/FiltrationQuotient.lean` (new,
  324 lines).
  - Namespace `TauCeti.AlgebraicGeometry.PointedWeierstrassChart`, for a chart `c` of any
    `π : X ⟶ S`, with `j = c.modelIso.inv ≫ c.toTotal`:
    - `modelRingEquiv : c.ring ≃+* Γ(X, j ''ᵁ ⊤)`, through `bijective_baseRingToGlobalSections`
      and `j.appIso ⊤`.
    - `modelCohomologyEquiv e : H⁰(N) ≃ₛₗ[modelRingEquiv] Γ(M, j ''ᵁ ⊤)`, for any
      `e : M.restrict j ≅ N` (`cohomologyZeroLinearEquiv`, then `sectionsLinearEquiv e ⊤`), with
      `modelCohomologyEquiv_apply`.
    - `modelCohomologyEquiv_cohomologyMapBaseLinear`: it carries `H⁰` of
      `e.inv ≫ (restrictFunctor j).map φ ≫ e'.hom` to `φ.appLinear (j ''ᵁ ⊤)`, for any
      `φ : M ⟶ M'`. This is the chain `e₀`, `e₁`, `e₂` that split 18's proof used inline in the
      twelfth round, now shared by the `m > 0` and `m = 0` cases. It is stated for any modules
      because neither case needs anything specific to pole sheaves.
  - Namespace `TauCeti.AlgebraicGeometry.EllipticCurveGeom`:
    - `mono_pullback_map_poleSheafMap_hom`: the pullback of `ℒ_m ⟶ ℒ_n` along any `φ : X ⟶ E`
      pulling `m[0]` and `n[0]` back to effective Cartier divisors is a monomorphism.
    - `zeroDivisor_pow_comap_modelIso_inv_toTotal`: on a chart, `n[0]` pulls back to the model's
      `zeroSectionDivisor ^ n`.
    - private `mono_pullback_map_chart`: the inclusion, transported to the model of a chart along
      any isomorphisms `ℒ_k|_{model} ≅ 𝒪(k[0])` (split 8's `nonempty_restrict_poleSheaf_iso`), has
      monomorphic pullbacks to all fibres (through `pullbackComp` and `restrictFunctorIsoPullback`).
      It holds for `m = 0` too.
    - private `projective_rankAtStalk_quotient_range_pushforward_poleSheafMap`, and its two halves
      `projective_quotient_range_pushforward_poleSheafMap` and
      `rankAtStalk_quotient_range_pushforward_poleSheafMap`: **over a chart image `U` and for
      `0 < m ≤ n`, `Γ(U, π_*ℒ_n) ⧸ Γ(U, π_*ℒ_m)` is a projective `Γ(S, U)`-module of rank
      `n - m`**. This is split 17 transported along `modelCohomologyEquiv`, then
      `image_top_modelIso_inv_toTotal` and `π.app U` (split 15's
      `LinearEquiv.projective_quotient_range`, as in split 10). Chart images cover `S`, so this is
      the Zariski-local splitting of the successive quotients of the pole filtration of `π_*ℒ_n`
      that the README asks for, stated on sections.
    - `exists_isCompl_range_pushforward_poleSheafMap`: **the pole filtration splits over every
      chart image**: for `0 < m ≤ n`, the image of `Γ(U, π_*ℒ_m)` in `Γ(U, π_*ℒ_n)` has a
      complement (by `Submodule.exists_isCompl_of_projective_quotient`). This is the README's
      "split the successive quotients" step, Zariski-locally on the base.
    - `bijective_app_pushforward_poleSheafMap_zero_one`: **over a chart image `U`,
      `Γ(U, π_*ℒ_0) ⟶ Γ(U, π_*ℒ_1)` is bijective**. This is split 17's
      `bijective_cohomologyMapBaseLinear_of_mono_pullback_zero_one` applied to the transported
      inclusion and carried along `modelCohomologyEquiv`.
    - `isIso_pushforward_map_poleSheafMap_zero_one` (instance): **`π_*ℒ_0 ⟶ π_*ℒ_1` is an
      isomorphism**, via `Hom.isIso_of_isBasis` on the restricted charts
      (`isBasis_range_opensRange_restrict`, split 8). So the first step of the pole filtration
      of `π_*ℒ_n` is an equality, the row `n = 1: 1` of the README's table, on `E`.

### Split 19 — after: 13

PR subject: `feat: multiplication of the line bundles 𝒪(aD) ⊗ 𝒪(bD) ≅ 𝒪((a + b)D) of an effective Cartier divisor`

Neither supplier is used. About 450 lines.

- `TauCeti/AlgebraicGeometry/LineBundle/Dual/Tensor.lean` (new, 104 lines; depends only on
  `main`), namespace `TauCeti.AlgebraicGeometry.InvertibleSheaf`:
  - `exactPairingIhomUnit L`: the internal-Hom dual `L^∨ = 𝓗om(L, 𝒪_X)` is a left dual of `L`
    (`main`'s `exactPairingOfIsIsoDualTensorIhom` with `isIso_dualTensorIhom_of_isLocallyFree`),
    with `exactPairingIhomUnit_evaluation`.
  - `ihomUnitTensorIso L K : (K ⊗ L)^∨ ≅ L^∨ ⊗ K^∨` (uniqueness of duals, `main`'s
    `TauCeti.ihomUnitIso`, applied to Mathlib's `ExactPairing.tensor`), and its evaluation formula
    `whiskerLeft_ihomUnitTensorIso_inv_comp_ev`.
- `TauCeti/AlgebraicGeometry/EffectiveCartierDivisor/TensorProduct.lean` (extended, +82 lines,
  section `SheafMul`): `main` has two multiplications of ideal sheaves, `sheafMul I J : I ⊗ J ⟶ I * J`
  in `X.Modules` (any `I`, `J`) and the isomorphism `tensorProductSheafIso I hJ` on the sheafified
  tensor product (`J` effective Cartier), but nothing relating them.
  - private `tensorProductSheafIso_hom_sheafι`: read through `tensorUnderlyingIso`,
    `tensorProductSheafIso` followed by `I * J ⟶ 𝒪_X` is `(ι_I ⊗ ι_J) ≫ λ` (checked on pure
    tensors of sections with `tensor_hom_ext`, `tensorProductSheafIso_hom_tmul` and
    `Scheme.leftUnitor_hom_app_μ_tmul`). The proof unfolds `sheafificationForgetAdjunction`, so
    the file gains `import all TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Monoidal`
    (commented at the import), and `public import TauCeti.AlgebraicGeometry.Modules.Algebra.Pushforward`.
  - `isIso_sheafMul I hJ`: hence `sheafMul I J` is that isomorphism (both are characterised by
    `sheafMul_sheafι`), so it is an isomorphism when `J` is effective Cartier;
    `sheafMulIso I hJ : I.sheaf ⊗ J.sheaf ≅ (I * J).sheaf` with `@[simp] sheafMulIso_hom`.
- `TauCeti/AlgebraicGeometry/IdealSheaf/Inclusion.lean` (split 13's file, +10 lines):
  `Scheme.IdealSheafData.eqToHom_sheafι` (`@[simp, reassoc]`; `simpNF` rejects a simp `_assoc` form): transport along an
  equality of ideal sheaves commutes with `sheafι`. (`IdealSheaf/ReesAlgebra.lean` on `main` has a
  private special case, `eqToHom_sheafιUnit`; the port may replace it.)
- `TauCeti/AlgebraicGeometry/EffectiveCartierDivisor/Multiplication.lean` (new, 257 lines),
  namespace `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier`, for `hI : I.IsEffectiveCartier`
  and `𝒪(nD) = 𝓗om(I^n, 𝒪_X)` written as `(ihom (I ^ n).sheaf).obj (𝟙_ _)`:
  - `powTensorIso hI a b : (I ^ b).sheaf ⊗ (I ^ a).sheaf ≅ (I ^ (a + b)).sheaf` (`sheafMulIso`), with
    `powTensorIso_hom_sheafι` and its naturality in the inclusions in each factor,
    `whiskerLeft_sheafOfLE_powTensorIso_hom` and `sheafOfLE_whiskerRight_powTensorIso_hom`.
  - `dualPowMulIso hI a b : 𝒪(aD) ⊗ 𝒪(bD) ≅ 𝒪((a + b)D)`, the dual of `powTensorIso` through
    `ihomUnitTensorIso`.
  - `whiskerLeft_dualPowMulIso_hom_comp_ev`: **`(φ ψ)(t s) = φ(s) ψ(t)`** for `t ∈ I^b`, `s ∈ I^a`.
  - `pre_sheafOfLE_whiskerRight_dualPowMulIso_hom`: **compatibility with the inclusions**
    `𝒪(aD) ⟶ 𝒪(a'D)` (precomposition with `I^a' ⊆ I^a`) for `a ≤ a'`, by `uncurry_injective` and
    the evaluation formula.
  - `whiskerLeft_pre_sheafOfLE_dualPowMulIso_hom`: the same in the second factor,
    `𝒪(bD) ⟶ 𝒪(b'D)` for `b ≤ b'`, by the same `uncurry_injective` argument (not through the
    braiding, whose kernel check times out).
  - `dualPowMulIsoOfEq hI hL a b`, `whiskerRight_dualPowMulIsoOfEq_hom` and
    `whiskerLeft_dualPowMulIsoOfEq_hom`: the same, transported
    to a family `L n` of modules with `hL : ∀ n, L n = 𝒪(nD)`. The pole sheaves on a Weierstrass
    model and on `E` are such families (their bodies are not exposed), so split 20 needs no
    `eqToHom` bookkeeping of its own.

### Split 20 — after: 14, 19

PR subject: `feat: the multiplication maps of the pole sheaves of a Weierstrass model and of an elliptic curve`

Neither supplier is used. About 230 lines.

- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Divisor/PoleSheaf/Multiplication.lean` (new,
  112 lines), namespace `WeierstrassCurve`:
  - `poleSheaf_obj`: `(W.poleSheaf n).obj = 𝓗om(𝒪(-n[0]), 𝒪)`.
  - `poleSheafMap_hom_eq`: the pole filtration map is precomposition with `𝒪(-n[0]) ⊆ 𝒪(-m[0])`.
  - `poleSheafMulIso a b : 𝒪(a[0]) ⊗ 𝒪(b[0]) ≅ 𝒪((a + b)[0])`.
  - `poleSheafMap_hom_whiskerRight_poleSheafMulIso_hom` and
    `whiskerLeft_poleSheafMap_hom_poleSheafMulIso_hom`: compatibility with the pole filtration in
    the first and in the second factor.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/PoleSheaf/Multiplication.lean` (new, 118
  lines), namespace `TauCeti.AlgebraicGeometry.EllipticCurveGeom`: the same five declarations for
  `ℒ_n = 𝒪_E(n[0])` on an elliptic curve `E` over any scheme.

### Split 21 — after: none

PR subject: `feat: swapping nested evaluations in a symmetric monoidal category`

Neither supplier is used. About 115 lines; depends only on Mathlib.

- `TauCeti/CategoryTheory/Monoidal/Braided/Evaluation.lean` (new, 114 lines), namespace `TauCeti`:
  - `whiskerLeft_whiskerLeft_comp_evaluate` (any monoidal category, `@[reassoc]`): a morphism on
    the outer factor commutes past an evaluation `f : A ⊗ B ⟶ 𝟙` of the inner factors;
  - in a symmetric monoidal category, `nestedEvaluation_eq_tensorHom`: the nested evaluation
    `(B ⊗ A) ⊗ (A' ⊗ B') ⟶ 𝟙`, `f : A ⊗ A' ⟶ 𝟙` inside and `g : B ⊗ B' ⟶ 𝟙` outside, is
    `g ⊗ f` after moving `B'` past `A ⊗ A'`;
  - `nestedEvaluation_braiding` (`@[reassoc]`): the braided structural identity relating the two
    rearrangements, proved by the hexagon expansions, cancelling inverse crossings by symmetry,
    and `monoidal`;
  - `braiding_tensorHom_braiding_comp_nestedEvaluation`: **braiding `B` past `A` and `A'` past `B'`
    exchanges the roles of `f` and `g` in the nested evaluation.** This is the shape of the
    evaluation formula of split 19 (`whiskerLeft_dualPowMulIso_hom_comp_ev`), so it is the
    commutativity input of split 22. The neighbouring `Braided/Basic.lean` on `main` holds the
    braided (not symmetric) moves of morphisms to the unit; the port may merge the two files.

### Split 22 — after: 19, 21

PR subject: `feat: the pole algebra ⨁ₙ 𝒪_X(nD) of an effective Cartier divisor`

Neither supplier is used. About 330 lines.

- `TauCeti/AlgebraicGeometry/EffectiveCartierDivisor/PoleAlgebra.lean` (new, 324 lines):
  - `Scheme.IdealSheafData.poleComponent I n := 𝓗om(Iⁿ, 𝒪_X)` (`abbrev`), the named family the
    graded algebra is built from.
  - namespace `Scheme.IdealSheafData.IsEffectiveCartier`, for `hI : I.IsEffectiveCartier`:
    - laws of the multiplication `powTensorIso hI a b : I^b ⊗ I^a ≅ I^(a + b)` of split 19:
      `whiskerLeft_powTensorIso_hom_comp_powTensorIso_hom`, its inverse form
      `powTensorIso_inv_whiskerLeft_powTensorIso_inv`, and `braiding_powTensorIso_hom`
      (`main`'s `IdealSheaf/ReesAlgebra.lean` proves the same laws privately for `reesMul`; the
      port may share them);
    - `poleMul hI a b : 𝒪_X(aD) ⊗ 𝒪_X(bD) ⟶ 𝒪_X((a + b)D)` (the `hom` of `dualPowMulIso`) and
      `poleOne : 𝒪_X ⟶ 𝒪_X(0D)` (the curried `I⁰ ⊗ 𝒪_X ≅ I⁰ ⊆ 𝒪_X`);
    - **the algebra laws** `poleOne_whiskerRight_poleMul`, `whiskerLeft_poleOne_poleMul`,
      `poleMul_assoc` and `braiding_poleMul`, each by `uncurry_injective`, the evaluation formula
      of split 19, and the corresponding law for ideal sheaves (commutativity also uses split 21);
    - `isQuasicoherent_poleComponent`, and **`poleAlgebra hI : GradedQuasicoherentAlgebra X`**, the
      graded commutative quasi-coherent algebra `⨁ₙ 𝒪_X(nD)` built with `main`'s
      `GradedQuasicoherentAlgebra.ofHomogeneous`, with `@[simp]` `poleAlgebra_obj_X`,
      `mul_poleAlgebra` and `one_poleAlgebra`. `main`'s `CommMon.gAlgebraSections` then gives the
      graded ring of sections `⨁ₙ Γ(U, 𝒪_X(nD))`.
  - Implementation notes (also in the module docstring): as for `main`'s `reesAlgebra`, the laws
    are stated with the named family `poleComponent` and the named `poleMul`; with
    `fun a b ↦ (dualPowMulIso hI a b).hom` the kernel times out checking `ofHomogeneous`. The
    inclusions `Iⁿ ⟶ 𝒪_X` are read through an opaque private `ιU` with target `𝟙_ X.Modules`. The
    module still takes about 95 s, most of it kernel checking of `poleMul_assoc` and one unit law.

### Split 23 — after: 20, 22

Subject: `feat: the pole algebras ⨁ₙ 𝒪(n[0]) of a Weierstrass model and of an elliptic curve`

Files (new):
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Divisor/PoleSheaf/PoleAlgebra.lean`
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/PoleSheaf/PoleAlgebra.lean`

Declarations:
- `WeierstrassCurve.poleAlgebra : GradedQuasicoherentAlgebra W.projModel`, the pole algebra of
  the effective Cartier divisor `[0]` (split 22's `IsEffectiveCartier.poleAlgebra`);
  `WeierstrassCurve.poleAlgebra_obj_X` (its components are the pole sheaves `𝒪(n[0])`),
  `WeierstrassCurve.mul_poleAlgebra` (its multiplication is split 20's `poleSheafMulIso`, up to
  the identifications of the components) and `WeierstrassCurve.one_poleAlgebra` (its unit).
- `TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleAlgebra : GradedQuasicoherentAlgebra E.carrier`,
  with `poleAlgebra_obj_X`, `mul_poleAlgebra` and `one_poleAlgebra`, the same for `ℒ_n` on `E`.

The pole sheaves are not definitionally the components `poleComponent` of split 22, so the
components are identified with them by the equalities `poleSheaf_obj` of split 20, as
`dualPowMulIsoOfEq` does for the multiplication. This was the first bullet of the old split 25.

The proofs need three unfolding lemmas, because under the module system the bodies of the
definitions they unfold are not exposed. Each was added in this round to the file of the split
that owns its definition, so it ships with that split: `IsEffectiveCartier.dualPowMulIsoOfEq_hom`
(split 19, `EffectiveCartierDivisor/Multiplication.lean`), `IsEffectiveCartier.poleMul_def` (split
22, `EffectiveCartierDivisor/PoleAlgebra.lean`), and `WeierstrassCurve.poleSheafMulIso_def` and
`EllipticCurveGeom.poleSheafMulIso_def` (split 20, the two `PoleSheaf/Multiplication.lean` files).

### Split 24 — after: 20

PR subject: `feat: multiplication on the graded pieces of the pole filtrations of a Weierstrass model and of an elliptic curve`

Neither supplier is used. About 350 lines.

- `TauCeti/CategoryTheory/Monoidal/Closed/Cokernels.lean` (new, 76 lines), namespace `TauCeti`,
  for a preadditive braided closed category with cokernels (tensoring on the right is a left
  adjoint by Mathlib's instance in `Monoidal/Closed/Braided.lean`):
  - `cokernel_whiskerLeft_eq_zero`: if `A ◁ g = h ≫ f ▷ B`, then `coker f ◁ g = 0`;
  - `cokernelTensorCokernelIso`: in that situation `coker f ⊗ coker g ≅ coker (f ▷ B)`, with
    `tensorHom_π_cokernelTensorCokernelIso_hom` (`@[reassoc (attr := simp)]`): it is induced by
    the projections.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Divisor/PoleSheaf/GradedMultiplication.lean`
  (new, 148 lines), namespace `WeierstrassCurve`:
  - `eqToHom_poleSheafMap_hom` and `poleSheafMap_hom_eqToHom` (`@[reassoc]`): transport of the
    pole filtration maps along equalities of indices;
  - `whiskerLeft_poleSheafMap_hom_succ`: the factorisation `𝒪((a + 1)[0]) ◁ (𝒪(b[0]) ⟶
    𝒪((b + 1)[0]))` through `(𝒪(a[0]) ⟶ 𝒪((a + 1)[0])) ▷ 𝒪((b + 1)[0])`;
  - `poleSheafMap_hom_whiskerRight_poleSheafMulIso_hom_eqToHom`: the square of the graded
    multiplication, with the indices normalised;
  - **`poleSheafGradedMulIso a b`**:
    `𝒪((a + 1)[0]) / 𝒪(a[0]) ⊗ 𝒪((b + 1)[0]) / 𝒪(b[0]) ≅ 𝒪((a + b + 2)[0]) / 𝒪((a + b + 1)[0])`;
  - `tensorHom_π_poleSheafGradedMulIso_hom` (`@[reassoc (attr := simp)]`): it is induced by
    `poleSheafMulIso (a + 1) (b + 1)`, so the class of a product is the product of the classes;
  - **`poleSheafGradedPowIso n`**: `(𝒪([0]) / 𝒪)^⊗(n + 1) ≅ 𝒪((n + 1)[0]) / 𝒪(n[0])`, by recursion
    on `n` through `poleSheafGradedMulIso n 0` and `TauCeti.tensorPowSuccIso`, with
    `poleSheafGradedPowIso_zero` and `poleSheafGradedPowIso_succ`.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/PoleSheaf/GradedMultiplication.lean` (new,
  144 lines), namespace `TauCeti.AlgebraicGeometry.EllipticCurveGeom`: the same nine declarations
  for `ℒ_n = 𝒪_E(n[0])` on an elliptic curve `E` over any scheme, from the `E`-side compatibilities
  of split 20.

### Split 25 — after: 18

PR subject: `feat: the cokernels of the pole filtration of π_*𝒪_E(n[0]) are locally free of rank n - m`

Neither supplier is used. About 180 lines.

- `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/CokernelSections.lean` (new, 78 lines),
  namespace `AlgebraicGeometry.Scheme.Modules`. This is general and builds on `main` alone. It is
  in this split because its only user is here:
  - `exact_app_of_shortExact`: sections over any open are left exact, because
    `SheafOfModules.evaluation` preserves finite limits.
  - `range_appLinear_eq_ker_appLinear_cokernel_π`: for a monomorphism `f : M ⟶ N`, the image of
    `Γ(M, U)` is the kernel of `Γ(N, U) ⟶ Γ(cokernel f, U)`.
  - `cokernelSectionsEquiv` and `cokernelSectionsEquiv_mk` (`@[simp]`): for `M` and `N`
    quasi-coherent and `U` affine, `Γ(N, U) ⧸ Γ(M, U) ≃ₗ[Γ(X, U)] Γ(cokernel f, U)`, induced by
    the projection. Surjectivity comes from `main`'s `Hom.app_surjective_of_epi_of_isAffineOpen`.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/PoleSheaf/FiltrationCokernel.lean` (new,
  103 lines), namespace `TauCeti.AlgebraicGeometry.EllipticCurveGeom`, for `0 < m ≤ n`:
  - `finite_projective_sections_cokernel_pushforward_poleSheafMap`: over a chart image `U`, the
    sections of `coker(π_*ℒ_m ⟶ π_*ℒ_n)` are finite projective of constant rank `n - m` over
    `Γ(S, U)`. They are split 18's quotient, through `cokernelSectionsEquiv`.
  - **`isFiniteLocallyFree_cokernel_pushforward_poleSheafMap`**: the cokernel is finite locally
    free.
  - **`rank_cokernel_pushforward_poleSheafMap`**: it has rank `n - m` at every point of `S`.

### Split 26 — after: 17, 18

PR subject: `feat: sections of exact pole order of a Weierstrass model and of an elliptic curve, locally on the base`

Neither supplier is used. About 270 lines, below the usual PR size; the port may fold it into split 29, its only consumer.

- `TauCeti/RingTheory/LocalRing/QuotientComplement.lean` (new, 131 lines), namespaces
  `TauCeti.IsLocalRing` and `TauCeti.Module`. General, on `main` alone:
  - `exists_isCompl_span_singleton_of_rankAtStalk_eq_one`: over a local ring, a submodule `N` of
    `M` with `M ⧸ N` finite flat of rank one at the closed point has a complement `R ∙ s` with
    `![s]` linearly independent.
  - `TauCeti.Module.exists_notMem_bijective_localizedModule_map_toSpanSingleton`: over any ring,
    a finite projective module of rank one at a prime `p` is free on one element `x` after
    inverting some `g ∉ p`: `LocalizedModule.map (.powers g) (LinearMap.toSpanSingleton R M x)`
    is bijective. This spreads the choice at a point out to a basic open neighbourhood, through
    Mathlib's `Module.FinitePresentation.exists_notMem_bijective`. (Added in the thirty-third
    round; the file is now 131 lines.)
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Divisor/PoleSheaf/LocalCoordinates.lean` (new, 63 lines),
  namespace `WeierstrassCurve`:
  - **`exists_isCompl_range_cohomologyMapBaseLinear_poleSheafMap`**: over a local ring and for
    `n ≥ 2`, the image of `H⁰(𝒪((n - 1)[0]))` in `H⁰(𝒪(n[0]))` has a complement spanned by one
    linearly independent section; for `n = 2, 3` these are the Weierstrass coordinates `x`, `y`.
- `TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/PoleSheaf/LocalCoordinates.lean` (new, 72
  lines, added in the thirty-third round), namespace `TauCeti.AlgebraicGeometry.EllipticCurveGeom`:
  - **`exists_notMem_bijective_toSpanSingleton_mkQ_range_pushforward_poleSheafMap`**: over the
    image `U` of a chart of `E`, for `n ≥ 2` and a prime `p` of `Γ(S, U)`, there are a section `s`
    of `π_*ℒ_n` over `U` and `g ∉ p` such that the class of `s` freely generates
    `Γ(U, π_*ℒ_n) ⧸ Γ(U, π_*ℒ_(n-1))` after inverting `g`. For `n = 2, 3` this is the choice of
    `x` and `y` near a point of `S`. It applies split 18's projectivity and rank one to the new
    algebraic lemma, so this split now needs split 18 as well.

## What remains (splits 27–31, not on this branch)

27. **(after 7, 9, 12)** The remaining clause of the positive-degree theorem on `E`: for an
    invertible `M` on `E` of degree `d > 0` on every geometric fibre, `π_*M` is locally free of
    rank `d`. The other two clauses were done in the tenth round, in splits 8
    (`isZero_higherDirectImage_one_of_forall_eulerDegree_pos`) and 12
    (`isIso_pushforwardBaseChange_app_of_forall_eulerDegree_pos`). They use the hypothesis in the
    direct form described under split 8, so no change to `main`'s Picard file is needed. The
    Weierstrass-model inputs are done for every such `M`: `H¹ = 0`, flatness and base change of `H⁰`,
    and fibre dimension equal to the fibre degree (split 5, `Scheme/PositiveDegree.lean`). The fibre
    degrees of `M` on chart models are geometric fibre degrees of `M`
    (`eulerDegree_pullback_projModelBaseChange_pos`, split 8). What remains:
    - Finite presentation of `H⁰(projModel W, M)` over a non-Noetherian `R`. Split 7 descends `W`
      to a finitely generated subring. For general `M` the line bundle must descend with it, which
      needs a spreading-out statement for line bundles that neither `main` nor 0E's pinned forms
      provide yet. `M` is given by finitely presented modules on the two standard affine charts,
      glued over their intersection, so it descends to a finitely generated subring. Building the
      descended sheaf by gluing modules is the missing piece. A spreading-out-free alternative would
      also do. (The obvious ones fail: `H⁰` is flat with finite-dimensional fibres, but over a
      non-Noetherian ring that does not make it finitely generated. Twisting by `ℒ_m` reduces
      finiteness for `M` to finiteness for `M(m[0])`, which is no easier.)
    - With that, `H⁰(projModel W, M)` is finite projective of constant rank the fibre degree, as
      split 7 shows for `ℒ_n`. The step from there to `π_*M` is done for every `M` (split 10, since
      the twenty-eighth round): apply `finite_projective_sections_of_restrict_iso` to
      `restrictFunctorIsoPullback`, then `rank_pushforward_of_finite_projective_sections`. The
      statements for `M` are then the analogues of `rank_pushforward_poleSheaf`, with `d` in place
      of `n`, and the `ℒ_n` statements become corollaries through `eulerDegree_pullback_snd_poleSheaf`,
      as splits 8 and 12 already are.
28. **(after 27)** For `d = 1`: the evaluation section has a relative effective Cartier zero
    divisor of degree one, hence is the divisor of a unique section. Prove compatibility with
    base change and fppf descent. This needs `relative-cartier-divisor` and `polarised-descent`.
29. **(after 18, 23, 24, 25, 26)** The rest of the pole filtration of `π_*ℒ_n`. Splits 14, 17 and 18 have
    the inclusions, their injectivity on `H⁰`, the dimension count over a field, and, over any ring
    and over every chart image of `E`, the projectivity of rank `n - m` of the quotients
    `H⁰(𝒪(n[0])) ⧸ H⁰(𝒪(m[0]))` for `0 < m ≤ n`. The case `m = 0` is done too: on `E`,
    `π_*ℒ_0 ⟶ π_*ℒ_1` is an isomorphism (split 18), and the filtration splits over every chart
    image (split 18). The multiplication maps `ℒ_a ⊗ ℒ_b ≅ ℒ_(a+b)`, compatible with the
    filtration in each factor, are split 20, and their algebra laws, with the graded commutative algebra
    `⨁ₙ 𝒪_X(nD)` of any effective Cartier divisor, are split 22, and its specialisation to `[0]`,
    the pole algebras `⨁ₙ 𝒪(n[0])` and `⨁ₙ ℒ_n` with components the pole sheaves, is split 23.
    What remains:
    - (Done in split 24: the multiplication on the graded pieces,
      `ℒ_(a+1)/ℒ_a ⊗ ℒ_(b+1)/ℒ_b ≅ ℒ_(a+b+2)/ℒ_(a+b+1)`, on `W` and on `E`.) It remains to read
      off the leading terms of `x², xy, x³, y²` from it, once `x` and `y` are chosen (third
      bullet). (Also done in split 24: the `n`-th graded piece is the `(n + 1)`-th tensor power of
      the first, `poleSheafGradedPowIso`.)
    - (Done in split 25: the sheaf-level form of split 18. For `0 < m ≤ n` the cokernel of
      `π_*ℒ_m ⟶ π_*ℒ_n` is finite locally free of rank `n - m`.)
    - The choice of `x` and `y` in the pieces of pole order 2 and 3, the unique relation in pole
      order six, and the unit discriminant. (Over a local base the choice is done in split 26:
      `exists_isCompl_range_cohomologyMapBaseLinear_poleSheafMap` gives `x` for `n = 2` and `y` for
      `n = 3` on a Weierstrass model. What remains is to transport it to `E` along the chart
      isomorphisms, as split 18 does for the complements, at a point of `S`, and to spread it out to
      a neighbourhood. Both are now done in split 26: on `E`, over a chart image and near any
      point of `S`, `exists_notMem_bijective_toSpanSingleton_mkQ_range_pushforward_poleSheafMap`
      gives `x` (`n = 2`) and `y` (`n = 3`), each freely generating its rank-one quotient after
      inverting some `g`. What remains of this bullet is the relation in pole order six and the
      unit discriminant, over the basic open `D(g)`.)
30. **(after 29)** The bases `1, x, y, x², xy, x³` after a pointed Weierstrass trivialisation, the
    multiplication maps (split 20) in these bases, the relation equal to the Weierstrass equation,
    and their independence of the chosen pointed equation.
31. **(after 1–30; exported)** The Weierstrass-presentation theorem: a smooth proper genus-one
    curve with a section is Zariski-locally pointed-isomorphic to a projective Weierstrass model,
    producing a `PointedWeierstrassAtlas`. This split completes the target.

The previous plan's split "pointed isomorphisms of Weierstrass models are variable changes" is
dropped: `main` already has it, over affine bases
(`WeierstrassCurve.existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom`, in
`Scheme/VariableChange/Basic.lean`) and over arbitrary bases
(`WeierstrassCurve.existsUnique_hom_comp_eq_comp_projModelVariableChangeIso_hom`, in
`Scheme/VariableChange/OverScheme.lean`). The variable-change group and its action on the
coefficients are Mathlib's `WeierstrassCurve.VariableChange`. Split 30 should check what remains
of the README's action on `x`, `y` and the invariant differential before adding any of it.

## Verification

`lake exe cache get`, `lake build` (green, warnings as errors; rerun in the nineteenth through twenty-fourth rounds on `afa08a3ed16f`, and in the twenty-fifth through twenty-ninth rounds on `385ec2ddd8dd`) and
`/opt/round/lookahead-check` all pass. In the twenty-eighth round, `#lint in TauCeti` (15 linters) passes, with 0 errors in
10314 declarations, on the import closure of `Geom/PoleSheaf/LocallyFree.lean` and
`Geom/PositiveDegree/BaseChange.lean`, run from a scratch file outside the repository. In the eighteenth round, the new proofs build with
warnings as errors; `#lint` was not rerun for lack of time. In the fifteenth round, `#lint in TauCeti` (15 linters)
passes, with 0 errors in 1588 declarations, on the import closure of the two new modules of
splits 21 and 22 (`PoleAlgebra.lean` imports `Braided/Evaluation.lean`), run from a scratch file
outside the repository. In the fourteenth round, `#lint in TauCeti` (15 linters)
passes, with 0 errors in 9793 declarations, on the import closure of the two new
`Multiplication.lean` files of split 20, run from a scratch file outside the repository. It first
found two `simpNF` failures, now fixed: `eqToHom_sheafι` carries `@[simp, reassoc]`, so its
`_assoc` form is not a simp lemma, and `exactPairingIhomUnit_evaluation` is not `@[simp]`. In the thirteenth round, `#lint in TauCeti` (15 linters) passes, with
0 errors, on the import closure of `Geom/PoleSheaf/FiltrationQuotient.lean`. In the twelfth round, `#lint in TauCeti` (15 linters)
passes, with 0 errors in 9913 declarations, on the import closure of the new modules of splits
15–18, run from a scratch file importing `Geom/PoleSheaf/FiltrationQuotient.lean` and
`RingTheory/Flat/Fiber.lean`. In the eleventh round, `#lint in TauCeti` (the same 15
linters) passes on the import closure of the five new modules of splits 13 and 14. It found
one `simpNF` failure: the generated `sheafOfLE_sheafι_assoc` was provable by `simp`. That
lemma is now `@[simp]` without `reassoc`. In the tenth round, Mathlib's default environment
linters (`#lint in TauCeti`,
15 linters including `simpNF`, `unusedArguments`, `docBlame` and `synTaut`) pass on the import
closure of the modules that round changed (`Geom/PositiveDegree/DirectImage.lean`,
`Geom/PositiveDegree/BaseChange.lean`, `Geom/PoleSheaf/DirectImage.lean`,
`Geom/PoleSheaf/BaseChange.lean` and `Geom/PoleSheaf/LocallyFree.lean`). They were run from a
scratch file because `uvx` is not available for `scripts/lint-env.sh`.

In the twenty-ninth round, `main` had not moved, so the branch is unchanged apart from this note. The round re-verified the build (a full `lake build`, 9 minutes) and `lookahead-check`. No new split was started: each of splits 25–29 needs a new construction (spreading out line bundles, the sheaf-level cokernel, or the choice of `x` and `y`), and none would fit in the time the round had left.

In the thirty-second round, the full `lake build` (warnings as errors) and `lookahead-check` pass,
and `#lint in TauCeti` (15 linters) passes, with 0 errors in 9314 declarations, on the import
closure of split 26's `LocalCoordinates.lean`, run from a scratch file outside the repository.

In the thirty-third round, the full `lake build` (warnings as errors) and `lookahead-check` pass.
`#lint in TauCeti` (15 linters) also passes, with 0 errors in 10414 declarations, on the import
closure of the new `Geom/PoleSheaf/LocalCoordinates.lean`, run from a scratch file outside the
repository.
