<!--tauceti-lookahead:v1 {"area":"ImaginaryQuadraticClassNumber","slug":"cm-tau","main":"385ec2ddd8ddf8cc779b78c176308cb9c6b55499","status":"partial","suppliers":["modular-function-field"],"splits":[{"n":1,"after":[],"title":"feat: the CM point τ_D and its multiplication matrices"},{"n":2,"after":[1],"title":"feat: units of the quadratic order as CM multiplication matrices"},{"n":3,"after":[1],"title":"feat: the reciprocity action of the CM multiplication matrices on level-N values"},{"n":4,"after":[1,2,3],"title":"feat: the CM reciprocity kernel is the image of the units, with ray degrees and conjugate norms"}]}-->

# Lookahead: `cm-tau` (ImaginaryQuadraticClassNumber, H3.1)

Built on `main` at `385ec2ddd8ddf8cc779b78c176308cb9c6b55499`. Status: **partial**.

## Stubbed declarations (supplier `modular-function-field`)

The supplier's roadmap `Suggested.lean` pins **no** declaration for `modular-function-field`
(the file pins only `cmTau`, which belongs to this target), and its open PR #29233
(`feat: the fixed field of SL(2, ℤ/Nℤ) on the function field of X(N)`) adds only the fixed-field
statements for the `SL(2, ℤ/Nℤ)` action that `main` already constructs
(`TauCeti.modularFunctionField`, `TauCeti.modularFunctionActionZMod`). What the remaining target
consumes from the supplier, and what neither `main` nor PR #29233 provides, is the README's
pinned (prose) item: "Construct the GL2(Z/N)/{±I} action: the SL2 part acts by fractional linear
maps and diag(1,d) acts on Fourier coefficients." It is stubbed in
`TauCeti/Lookahead/CmTau/Stubs.lean` as follows.

* `TauCeti.modularFunctionActionGL (N : ℕ) [NeZero N] :
  GL (Fin 2) (ZMod N) →* (modularFunctionField N ≃+* modularFunctionField N)ᵐᵒᵖ` (body `sorry`).
  Suggested.lean signature: none (no pinned Lean form). Source: README H3.1 prose. A right action,
  bundled into the opposite group like `TauCeti.modularFunctionActionZMod` on `main`.
* `TauCeti.coe_unop_modularFunctionActionGL_toGL (g : SL(2, ZMod N)) (F : modularFunctionField N) :
  ((unop (modularFunctionActionGL N (Matrix.SpecialLinearGroup.toGL g)) F : modularFunctionField N)
    : MeromorphicFunction _) = unop (modularFunctionActionZMod N g) F`.
  Suggested.lean signature: none. Source: README prose (the SL2 part acts by fractional linear
  maps), expressed through `main`'s `modularFunctionActionZMod`.
* `TauCeti.modularFunctionActionGL_neg_one : modularFunctionActionGL N (-1) = 1`.
  Suggested.lean signature: none. Source: README prose (the action is one of GL2(Z/N)/{±I}).

Not yet stubbed, because nothing proved so far consumes it: the README's clause that `diag(1, d)`
acts on Fourier coefficients through `ζ_N ↦ ζ_N^d`. The reciprocity split (3) will need it; its
statement is to be taken from the supplier's landed form (or a later Suggested.lean pin).

## What is proved (no `sorry`)

`TauCeti/NumberTheory/ClassNumberOne/CMPoint.lean` (237 lines), namespace `TauCeti`:

* `cmTau D hD : ℍ`, exactly the target's pinned `Suggested.lean` form
  (`i √|D| / 2` if `D % 4 = 0`, else `(3 + i √|D|) / 2`), with `cmTauCoe`, `coe_cmTau`,
  `im_cmTauCoe`, `im_cmTau`.
* `cmTauLinearCoeff D` (`B = 0` or `-3`), `cmTauConstCoeff D` (`C`), `cmTau_sq_add`
  (`τ_D² + B τ_D + C = 0`), `cmTauLinearCoeff_sq_sub_four_mul_cmTauConstCoeff` (`B² - 4C = D`).
* `cmMulMatrix B C s t = [[t - B s, -C s], [s, t]]` over any commutative ring, with
  `cmMulMatrix_mulVec` (`(τ, 1)` is an eigenvector with eigenvalue `t + s τ`),
  `det_cmMulMatrix` (determinant = norm form), `cmMulMatrix_mul` (multiplicativity),
  `cmMulMatrix_zero_one`, `cmMulMatrix_neg`, `map_cmMulMatrix` (reduction mod `N`),
  `four_mul_cmNormForm`.
* Units / exceptional kernels on the norm-form side: `cmNormForm_eq_one_iff_of_lt_neg_four`
  (only `(0, ±1)` once `D < -4`), `cmNormForm_eq_one_iff_neg_four` (four units),
  `cmNormForm_eq_one_iff_neg_three` (six units).

## What remains

1. Identify the pairs `(s, t)` with `t + s τ_D` a unit with the **actual** units of the order:
   transport through `TauCeti.QuadraticOrder.toSubalgebra D hD` (whose generator is
   `(D + √D)/2 = τ_D + (D + B)/2`) and its unit counts in
   `TauCeti/NumberTheory/QuadraticOrder/NormOne.lean`, then to `𝓞 K` for a field of
   discriminant `D` (the landed `card-units-of-is-totally-complex-of-discr`), giving the
   unit-image subgroup of `GL(2, ℤ/Nℤ)` and the exceptional kernels at `D = -3, -4`.
2. The reciprocity action: for `f ∈ F_N` finite at `τ_D`, the value `f(τ_D)` is sent by the Artin
   symbol of `t + s τ_D` to `(f ∘ M(s, t)⁻¹)(τ_D)` via `modularFunctionActionGL`
   (Shimura reciprocity). This needs the ray/ring class field and Artin-map interfaces of
   ClassFieldTheory (Layer 13 `rayClassField`), which are **not** among this list item's listed
   suppliers; the next session should confirm whether they are on `main` before attempting it.
3. Kernel = image of the actual units of `O_K`; the conductor/ray-degree formula
   `[K_(N) : H_K] = |(O_K/N)ˣ| / |image of O_Kˣ|`; and the norm-as-product-of-conjugates
   comparison for `N = 2, 3, 6, 8`.

## Split plan

1. **feat: the CM point τ_D and its multiplication matrices** — after: none.
   File `TauCeti/NumberTheory/ClassNumberOne/CMPoint.lean` (done on this branch); all
   declarations listed above.
2. **feat: units of the quadratic order as CM multiplication matrices** — after: 1.
   File `TauCeti/NumberTheory/ClassNumberOne/CMUnits.lean`: the bijection between the units of
   `QuadraticOrder.toSubalgebra D hD` (and of `𝓞 K`) and the norm-one pairs, the unit-image
   subgroup of `GL(2, ℤ/Nℤ)`, and its order `2`, `4`, `6`.
3. **feat: the reciprocity action of the CM multiplication matrices on level-N values** —
   after: 1. File `TauCeti/NumberTheory/ClassNumberOne/CMReciprocity.lean`, importing the
   supplier's `GL(2, ℤ/Nℤ)` action (stubbed here) and the ray class field interface.
4. **feat: the CM reciprocity kernel is the image of the units, with ray degrees and conjugate
   norms** — after: 1, 2, 3. File `TauCeti/NumberTheory/ClassNumberOne/CMRayClassField.lean`:
   the kernel theorem with the exceptional kernels at `D = -3, -4`, the conductor/ray-degree
   formula, and the norm-as-product-of-conjugates comparisons for levels `2, 3, 6, 8`. This is
   the split that completes the target.
