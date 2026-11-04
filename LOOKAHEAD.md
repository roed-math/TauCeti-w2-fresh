<!--tauceti-lookahead:v1 {"area":"ImaginaryQuadraticClassNumber","slug":"cm-lattice-dictionary","main":"5f78b5307b932e1e2ac7848dc7d4fedc6a52d6c1","status":"partial","suppliers":["weierstrass-uniformization"],"splits":[{"n":1,"after":[],"title":"feat: scalar maps between period lattices, their kernels, degrees and duals"},{"n":2,"after":[1],"title":"feat: the multiplier ring of a period lattice and its analytic endomorphisms"},{"n":3,"after":[2],"title":"feat: fractional ideals of imaginary quadratic orders as period lattices"},{"n":4,"after":[3],"title":"feat: ideal classes of an imaginary quadratic order and lattices with CM"},{"n":5,"after":[4],"title":"feat: the Picard group acts simply transitively on lattices with CM"}]}-->
# Lookahead: `cm-lattice-dictionary` (ImaginaryQuadraticClassNumber, H3.1)

Built on `main` at `5f78b5307b932e1e2ac7848dc7d4fedc6a52d6c1`. Status: **partial** (see the end).

Target (H3.1): "Prove that scalar maps between lattices correspond to algebraic isogenies, with
kernel/degree/dual comparisons to EllipticCurves, by the rational elliptic-function description in
wp and wp prime. Then, for every imaginary quadratic order, construct the oriented
ideal-lattice/complex elliptic-curve equivalence, endomorphism-order comparison, class-group action
and j-invariant classification."

## Stubbed supplier declarations (`weierstrass-uniformization`)

All stubs are in `TauCeti/Lookahead/CmLatticeDictionary/Stubs.lean`, in the root `PeriodPair`
namespace exactly as the supplier's neighbouring code on `main`
(`TauCeti/Analysis/SpecialFunctions/Elliptic/Uniformization.lean`) and the open supplier PR place
them. The roadmap's `ImaginaryQuadraticClassNumber/Suggested.lean` pins **no** declaration of
`weierstrass-uniformization` (it pins only H1/H2/H3.5/H3.6 forms), so every stub is taken from the
open supplier PR **#22646** (`feat: the addition theorem for ℘ and the group law of the Weierstrass
point map`, head `10bd9cc004e`), file `TauCeti/Analysis/SpecialFunctions/Elliptic/AdditionTheorem.lean`.
Surjectivity of the point map (`PeriodPair.weierstrassPoint_surjective`) and everything else used
is already on `main` (partials #21683, #22327 and later), so it is not stubbed.

1. `PeriodPair.weierstrassPoint_add`
   - `Suggested.lean`: none.
   - PR #22646: `@[simp] theorem weierstrassPoint_add (z w : ℂ) : L.weierstrassPoint (z + w) = L.weierstrassPoint z + L.weierstrassPoint w`
   - Stub: the same statement, `@[simp]`, body `sorry`. No difference.
2. `PeriodPair.weierstrassPointHom`
   - `Suggested.lean`: none.
   - PR #22646: `def weierstrassPointHom : ℂ →+ L.weierstrassCurve.toAffine.Point where toFun := L.weierstrassPoint ...`
   - Stub: `def weierstrassPointHom : ℂ →+ L.weierstrassCurve.toAffine.Point := sorry`. The body is
     `sorry`; the proof uses only the pinned API below (`_apply`, `ker_`), never the body.
3. `PeriodPair.weierstrassPointHom_apply`
   - `Suggested.lean`: none.
   - PR #22646: `@[simp] lemma weierstrassPointHom_apply (z : ℂ) : L.weierstrassPointHom z = L.weierstrassPoint z := (rfl)`
   - Stub: the same statement, `@[simp]`, body `sorry` (the PR's `(rfl)` would need the stub body).
4. `PeriodPair.ker_weierstrassPointHom`
   - `Suggested.lean`: none.
   - PR #22646: `lemma ker_weierstrassPointHom : L.weierstrassPointHom.ker = L.lattice.toAddSubgroup`
   - Stub: the same statement, body `sorry`. No difference.

The stub module imports only `TauCeti.Analysis.SpecialFunctions.Elliptic.Uniformization`; the PR's
module also imports `Mathlib.Analysis.Normed.Module.Connected`, which only its proofs need.

**Port:** replace `import TauCeti.Lookahead.CmLatticeDictionary.Stubs` in
`ScalarMap.lean` by `import TauCeti.Analysis.SpecialFunctions.Elliptic.AdditionTheorem` and delete
`TauCeti/Lookahead/`. Nothing else refers to the stub module.

## Split plan

All five splits need the supplier's PR #22646 on `main`. Each split builds on `main` plus the splits
before it.

### Split 1 — `feat: scalar maps between period lattices, their kernels, degrees and duals`
- Needs first: none (only the supplier).
- Files: new `TauCeti/Analysis/SpecialFunctions/Elliptic/ScalarMap.lean` (304 lines); adds
  `PeriodPair.intCast_mul_mem_lattice` and `PeriodPair.latticeBasis_repr_eq` to
  `TauCeti/Analysis/Complex/UpperHalfPlane/PeriodPair.lean`.
- Declarations (`PeriodPair` namespace): `weierstrassPointHom_surjective`,
  `mem_ker_weierstrassPointHom`, `pointHom_ext`, `scalarPointHom` (the homomorphism
  `E_Λ(ℂ) →+ E_Λ'(ℂ)`, `P_Λ(z) ↦ P_Λ'(α z)`, for `α Λ ⊆ Λ'`), `scalarPointHom_weierstrassPoint`,
  `scalarPointHom_one`, `scalarPointHom_comp`, `scalarPointHom_intCast` (`n : ℤ` gives `[n]`), `weierstrassPoint_mem_ker_scalarPointHom_iff`,
  `scalarPointHom_surjective`, `natCard_ker_scalarPointHom` (degree = `[Λ' : c Λ]`),
  `relIndex_lattice_smul_eq_natAbs` (degree = `|a f - b e|` for the integer matrix of `c`),
  `mul_sub_mul_ne_zero`, `relIndex_lattice_smul_ne_zero` (finite degree),
  `natCard_zsmul_eq_zero` (`#E_Λ(ℂ)[n] = n²`),
  `relIndex_div_mul_mem_lattice`, `scalarPointHom_comp_dual`, `scalarPointHom_dual_comp`
  (the dual of degree `n` composes to `[n]` on both sides); private helpers `kerParam`,
  `latticeBasis'`. The first three declarations (`weierstrassPointHom_surjective`,
  `mem_ker_weierstrassPointHom`, `pointHom_ext`) are general facts about the supplier's
  `weierstrassPointHom`; if the supplier lands them (or equivalents) in `AdditionTheorem.lean`, use
  those instead.

### Split 2 — `feat: the multiplier ring of a period lattice and its analytic endomorphisms`
- Needs first: 1.
- Files: new `TauCeti/Analysis/SpecialFunctions/Elliptic/Endomorphism.lean` (263 lines).
- Declarations (`PeriodPair`): `scalarPointHom_add`, `scalarPointHom_zero`,
  `scalarPointHom_eq_zero_iff`, `multiplierRing` (`{α | α Λ ⊆ Λ}` as a `Subring ℂ`),
  `mem_multiplierRing`, `multiplierRing_smul`, `endRingHom` (the ring homomorphism
  `multiplierRing →+* AddMonoid.End E_Λ(ℂ)`), `endRingHom_apply`, `endRingHom_weierstrassPoint`,
  `endRingHom_injective`, `sq_sub_trace_mul_add_norm_eq_zero` (`α² - t α + n = 0`,
  `t = 2 Re α`, `n = |α|²` integers), `isIntegral_of_mem_multiplierRing`,
  `exists_intCast_eq_of_im_eq_zero`, `multiplierRing_eq_bot_iff` (no CM iff all multipliers
  real), `natCard_ker_endRingHom` (degree of `[α]` is `|α|²`).

### Split 3 — `feat: fractional ideals of imaginary quadratic orders as period lattices`
- Needs first: 2.
- Files: new `TauCeti/NumberTheory/ComplexMultiplication/IdealLattice.lean` (287 lines); adds
  `PeriodPair.weierstrassCurve_j_eq_of_lattice_eq_smul` to
  `TauCeti/Analysis/SpecialFunctions/Elliptic/Uniformization.lean`.
- Declarations (`TauCeti.GlobalNumberFields.NumberFieldOrder`):
  `linearIndependent_real_of_span_rat_eq_top`, `exists_periodPair_lattice_eq` (`σ(I)` is a
  period lattice), `multiplierRing_eq_map` (endomorphism-order comparison: multiplier ring of
  `σ(I)` is `σ` of the multiplier ring of `I`), `multiplierRing_eq_map_of_isProper`,
  `multiplierRingEquiv` + `coe_multiplierRingEquiv`, `orderEndRingHom` +
  `orderEndRingHom_weierstrassPoint` + `orderEndRingHom_injective` (`O` acts faithfully on
  `E_I(ℂ)` and is all of its analytic endomorphisms), `lattice_smul_eq_image_spanSingleton_mul`,
  `jInvariant`, `jInvariant_eq`, `jInvariant_eq_of_homothetyCon`; and
  (`TauCeti.GlobalNumberFields.IdealClassMonoid`) `jInvariant`, `jInvariant_mk`,
  `exists_jInvariant_eq_j` (the `j`-invariant of an ideal class is a modular `j`-value).

### Split 4 — `feat: ideal classes of an imaginary quadratic order and lattices with CM`
- Needs first: 3.
- Files: new `TauCeti/NumberTheory/ComplexMultiplication/LatticeClass.lean` (200 lines); adds
  `PeriodPair.mem_lattice_smul_iff` to `TauCeti/Analysis/Complex/UpperHalfPlane/PeriodPair.lean`.
- Declarations (`TauCeti.GlobalNumberFields.NumberFieldOrder`):
  `exists_eq_spanSingleton_mul_of_lattice_eq_smul`, `mk_eq_mk_iff_exists_lattice_eq_smul`
  (ideal classes = homothety classes of their lattices), `exists_isProper_lattice_smul_eq`
  (every lattice with multiplier ring `σ(O)` is homothetic to `σ(I)` for a proper `I`); private
  helpers `mem_lattice_iff_of_coe_eq`, `exists_mem_notMem_span_one`, `span_one_pair_eq_top`.

### Split 5 — `feat: the Picard group acts simply transitively on lattices with CM`
- Needs first: 4.
- Files: new `TauCeti/NumberTheory/ComplexMultiplication/ClassGroupAction.lean` (248 lines).
- Declarations (`TauCeti.GlobalNumberFields.NumberFieldOrder`): `CMLattice` (period pairs with
  multiplier ring `σ(O)`), `CMLattice.homothety`, `CMClass` (their homothety classes),
  `CMClass.mk`, `CMClass.mk_surjective`, `CMClass.mk_eq_mk_iff`, `cmLatticeOfIsProper`,
  `coe_lattice_cmLatticeOfIsProper`, `cmClassEquiv` (`Pic O ≃ CMClass O σ`, `[I] ↦ [σ(I)]`),
  `cmClassEquiv_mkPic`, `picSMul`, `picSMul_cmClassEquiv`, `cmClassMulAction`, `picSMul_mk`
  (`[𝔞] · [σ(I)] = [σ(𝔞⁻¹ I)]`, Silverman's convention), `exists_picSMul_eq` (transitive),
  `picSMul_eq_self_iff` (free); private helpers `unitRep`, `ofUnit` and their lemmas. Uses
  `main`'s `isProperFractionalIdeal_iff_isUnit_of_finrank_eq_two` (proper = invertible in a
  quadratic order).

## What is proved and what remains (`partial`)

Proved (no `sorry` outside the stub file): the analytic half of the dictionary. Scalar maps between
lattices are group homomorphisms of the Weierstrass point groups with kernel `α⁻¹Λ'/Λ`, degree
`[Λ' : αΛ] = |det|` (finite), functoriality, `[n]`, and duals composing to `[deg]`; the multiplier
ring acts faithfully, consists of integers of imaginary quadratic orders with degree = norm, and is
`ℤ` exactly when there is no CM; for an imaginary quadratic order `O` with orientation `σ`, every
nonzero fractional ideal gives a period lattice whose multiplier ring is `σ` of the ideal's
multiplier ring (so `O` for proper ideals), ideal classes correspond bijectively to homothety
classes of lattices with multiplier ring `σ(O)`, `Pic O` acts simply transitively on these
classes (`[𝔞] · [σ(I)] = [σ(𝔞⁻¹ I)]`), and the `j`-invariant descends to ideal classes and is a
modular `j`-value.

Remains:
1. **Algebraic isogenies.** The rational description: for `α Λ ⊆ Λ'`, `℘_Λ'(α z)` and
   `℘'_Λ'(α z)` are rational functions of `℘_Λ(z), ℘'_Λ(z)` (even elliptic function with poles on
   `α⁻¹Λ'`, Liouville), giving a `TauCeti.Isogeny` / `TauCeti.Isogeny.Hom` of the Weierstrass
   curves whose point map is `scalarPointHom`; then compare its EllipticCurves degree, kernel and
   dual with `natCard_ker_scalarPointHom`, `scalarPointHom_comp_dual`, and identify the algebraic
   endomorphism ring with `multiplierRing` (so `End(E_I) ≅ O` algebraically).
2. **j-invariant classification.** The converse of `jInvariant_eq_of_homothetyCon`: equal
   `j`-invariants force homothetic lattices (hence equal ideal classes, via
   `mk_eq_mk_iff_exists_lattice_eq_smul`). This needs recovery of the lattice from `(g₂, g₃)`,
   i.e. the supplier's "period-lattice recovery for every complex elliptic curve", which no open
   supplier PR yet states.
3. **Class-group action by isogenies.** The action itself is split 5; what remains is its
   isogeny form: for integral invertible `𝔞`, the `𝔞`-isogeny `E_I → E_{𝔞⁻¹ I}` (the scalar map
   of `1`, from `σ(I) ⊆ σ(𝔞⁻¹ I)`) has kernel `E_I[𝔞]` and degree `N(𝔞) = [O : 𝔞]`, and its
   algebraic form after item 1.
4. The final split carrying the target's exported theorems would assemble 1–3 with splits 1–5.
