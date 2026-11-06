<!--tauceti-lookahead:v1 {"area":"ImaginaryQuadraticClassNumber","slug":"cm-tau","main":"3a0189695d62134a412200ef4237d0bbb2e95d75","status":"partial","suppliers":["modular-function-field"],"splits":[{"n":1,"after":[],"title":"feat: the CM point τ_D and its multiplication matrices"},{"n":2,"after":[1],"title":"feat: the units of the quadratic order as CM multiplication matrices of level N"},{"n":3,"after":[1],"title":"feat: the reciprocity action of the CM multiplication matrices on level-N values"},{"n":4,"after":[1,2,3],"title":"feat: the CM reciprocity kernel is the image of the units, with ray degrees and conjugate norms"}]}-->

# Lookahead: `cm-tau` (ImaginaryQuadraticClassNumber, H3.1)

Built on `main` at `3a0189695d62134a412200ef4237d0bbb2e95d75`. Status: **partial**.

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

`TauCeti/NumberTheory/ClassNumberOne/CMPoint.lean` (237 lines, split 1), namespace `TauCeti`:

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
* Units on the norm-form side: `cmNormForm_eq_one_iff_of_lt_neg_four`
  (only `(0, ±1)` once `D < -4`), `cmNormForm_eq_one_iff_neg_four` (four units),
  `cmNormForm_eq_one_iff_neg_three` (six units).
* This session: `cmTauLinearCoeff`, `cmTauConstCoeff`, `cmMulMatrix` are now `@[expose]` so
  that split 2 can compute with them under the module system.

`TauCeti/NumberTheory/ClassNumberOne/CMUnits.lean` (≈270 lines, split 2, new this session),
namespace `TauCeti`, no supplier needed:

* `cmTauShift D = (B + D)/2` with `two_mul_cmTauShift`: the generator `(D + √D)/2` of
  `QuadraticOrder.toSubalgebra D hD` is `τ_D + (B + D)/2`.
* `cmMulMatrix_shift_mul_self`: the multiplication matrix of that generator satisfies the
  defining relation `ω² = (D - D²)/4 + D ω` of the integral model.
* `cmMulMatrixHom D hD : toSubalgebra D hD →ₐ[ℤ] Matrix (Fin 2) (Fin 2) ℤ` (the regular
  representation on `(τ_D, 1)`, via `QuadraticAlgebra.lift`), with
  `cmMulMatrixHom_equivToSubalgebra` (`m + n ω ↦ cmMulMatrix B C n (m + n (B + D)/2)`),
  `cmMulMatrixHom_injective`, `det_cmMulMatrixHom_unit` (determinant `1` on units, `D < 0`).
* `cmUnitsToGL D hD N : (toSubalgebra D hD)ˣ →* GL (Fin 2) (ZMod N)` (units as level-`N`
  multiplication matrices), `coe_cmUnitsToGL`.
* `eq_zero_one_of_cmNormForm_eq_one` (a norm-one `(s, t) ≡ (0, 1) mod N`, `N ≥ 3`,
  `B² - 4C ≤ -3`, is `(0, 1)`), hence `cmUnitsToGL_injective` (`D < 0`, `N ≥ 3`) and
  **`card_range_cmUnitsToGL`**: the image of the units has order `6` at `D = -3`, `4` at
  `D = -4`, `2` otherwise — the exceptional kernels, not a quotient by `{±1}`;
  `cmUnitsToGL_two_neg_one` (at level `2`, `-1` is already trivial).
* The **actual** units of `O_K`: `ringOfIntegersEquivToSubalgebra` (`𝓞 ℚ(√D) ≃ₐ[ℤ]` the order,
  for fundamental `D`, from `QuadraticOrder.toSubalgebra_eq_integralClosure_iff`),
  `cmRingOfIntegersUnitsToGL`, `cmRingOfIntegersUnitsToGL_injective`,
  `card_range_cmRingOfIntegersUnitsToGL` (image order `= |O_Kˣ|`, which the landed
  `NumberField.Units.card_units_of_isTotallyComplex_of_discr` evaluates as `6, 4, 2`).

## What remains

1. (Split 3) The reciprocity action: for `f ∈ F_N` finite at `τ_D`, the Artin symbol of
   `t + s τ_D` sends `f(τ_D)` to `(f ∘ M(s, t)⁻¹)(τ_D)` through the supplier's
   `modularFunctionActionGL` (Shimura reciprocity), with the ClassFieldTheory arithmetic-Frobenius
   convention and the inverse it forces. This needs Layer 13 `rayClassField` / Artin-map
   interfaces of ClassFieldTheory and the CM main theorem over `H_K`; the next session must first
   check what of these is on `main` (they are not listed suppliers of this item). It also needs
   the `diag(1, d)`-on-Fourier-coefficients clause of the supplier, not yet stubbed.
2. (Split 4) Kernel of that action = `(cmRingOfIntegersUnitsToGL D hD hfund N).range` (split 2
   supplies this subgroup and its order); the conductor/ray-degree formula
   `[K_(N) : H_K] = |(O_K/N)ˣ| / |image of O_Kˣ|` (the residue-unit counts are on `main` in
   `TauCeti/NumberTheory/NumberField/Quadratic/ResidueUnits.lean`); the
   norm-as-product-of-conjugates comparison for `N = 2, 3, 6, 8`.
3. Not done in split 2 (optional polish): the comparison of `cmMulMatrixHom` with Mathlib's
   `Algebra.leftMulMatrix` on the basis `(τ_D, 1)` (it is the transpose), and the evaluation of
   an order element at the complex embedding `√D ↦ i √|D|` as `t + s τ_D`.

## Split plan

1. **feat: the CM point τ_D and its multiplication matrices** — after: none.
   File `TauCeti/NumberTheory/ClassNumberOne/CMPoint.lean` (done on this branch); all
   declarations listed above.
2. **feat: the units of the quadratic order as CM multiplication matrices of level N** —
   after: 1. File `TauCeti/NumberTheory/ClassNumberOne/CMUnits.lean` (done on this branch); all
   its declarations listed above. Does not import the stubs.
3. **feat: the reciprocity action of the CM multiplication matrices on level-N values** —
   after: 1. File `TauCeti/NumberTheory/ClassNumberOne/CMReciprocity.lean`, importing the
   supplier's `GL(2, ℤ/Nℤ)` action (stubbed here) and the ray class field interface.
4. **feat: the CM reciprocity kernel is the image of the units, with ray degrees and conjugate
   norms** — after: 1, 2, 3. File `TauCeti/NumberTheory/ClassNumberOne/CMRayClassField.lean`:
   the kernel theorem with the exceptional kernels at `D = -3, -4`, the conductor/ray-degree
   formula, and the norm-as-product-of-conjugates comparisons for levels `2, 3, 6, 8`. This is
   the split that completes the target.
