<!--tauceti-lookahead:v1 {"area":"ImaginaryQuadraticClassNumber","slug":"cm-lattice-dictionary","main":"e8758b7b2f82b9b1c3f33b992ab8f499b510240f","status":"partial","suppliers":["weierstrass-uniformization"],"splits":[{"n":1,"after":[],"title":"feat: scalar maps between period lattices, their kernels, degrees and duals"},{"n":2,"after":[1],"title":"feat: the multiplier ring of a period lattice and its analytic endomorphisms"},{"n":3,"after":[2],"title":"feat: fractional ideals of imaginary quadratic orders as period lattices"},{"n":4,"after":[3],"title":"feat: ideal classes of an imaginary quadratic order and lattices with CM"},{"n":5,"after":[4],"title":"feat: the Picard group acts simply transitively on lattices with CM"},{"n":6,"after":[],"title":"feat: the index of 𝔞 J in an invertible fractional ideal J is the index of 𝔞"},{"n":7,"after":[5,6],"title":"feat: the isogeny of an invertible integral ideal, its torsion kernel and its degree"},{"n":8,"after":[1],"title":"feat: Vélu's formulas for ℘ of a superlattice"},{"n":9,"after":[5],"title":"feat: the j-invariant classifies ideal classes and curves with complex multiplication"},{"n":10,"after":[1,2,3,4,5,6,7,8,9],"title":"feat: scalar maps between lattices are algebraic isogenies"}]}-->
# Lookahead: `cm-lattice-dictionary` (ImaginaryQuadraticClassNumber, H3.1)

Built on `main` at `e8758b7b2f82b9b1c3f33b992ab8f499b510240f`. Status: **partial** (see the end).
Split 10 is the planned final split and is **not yet written**; splits 1–9 are on the branch.

Target (H3.1): "Prove that scalar maps between lattices correspond to algebraic isogenies, with
kernel/degree/dual comparisons to EllipticCurves, by the rational elliptic-function description in
wp and wp prime. Then, for every imaginary quadratic order, construct the oriented
ideal-lattice/complex elliptic-curve equivalence, endomorphism-order comparison, class-group action
and j-invariant classification."

## Changes since the previous session (tip `64acec3e391`)

- The supplier PR #22646 (addition theorem, `weierstrassPointHom`, its kernel) **landed on `main`**
  (`TauCeti/Analysis/SpecialFunctions/Elliptic/AdditionTheorem.lean`). Its four stubs are deleted and
  `ScalarMap.lean` imports the landed module.
- The supplier's next PR **#28061** (`feat: complex uniformization ℂ/Λ ≃ E(ℂ) and the lattice of a
  complex elliptic curve`, head `15ddff1bbbb`) states `PeriodPair.weierstrassCurve_j_eq_iff` and
  `PeriodPair.weierstrassCurve_j_eq_of_lattice_eq_smul`. The previous branch proved both itself
  (split 7, `Elliptic/JInvariant.lean`, by a differential-equation argument, and an addition to
  `Uniformization.lean`). Keeping them would duplicate the supplier, so they are **removed** and
  stubbed from #28061 instead; the CM `j`-classification (now split 9) uses the stubs.
- New: `FractionalIdeal.relIndex_coeIdeal_mul_eq_index` (split 6) and the norm form of the degree of
  the `𝔞`-isogeny, `NumberFieldOrder.natCard_idealTorsion_eq_index` (split 7). This closes the old
  remaining item "degree of the `𝔞`-isogeny as a norm".
- New: Vélu's formulas and the rational description of `℘_{Λ'}`, `℘'_{Λ'}` in `℘_Λ`, `℘'_Λ`
  (split 8): the analytic half of remaining item 1.

## Stubbed supplier declarations (`weierstrass-uniformization`)

All stubs are in `TauCeti/Lookahead/CmLatticeDictionary/Stubs.lean`, in the root `PeriodPair`
namespace where the supplier and its neighbouring code on `main` put them. The roadmap's
`ImaginaryQuadraticClassNumber/Suggested.lean` pins **no** declaration of
`weierstrass-uniformization` (it pins only H1/H2/H3.5/H3.6 forms), so both stubs come from the open
supplier PR **#28061**'s diff.

1. `PeriodPair.weierstrassCurve_j_eq_of_lattice_eq_smul`
   - `Suggested.lean`: none.
   - PR #28061 (`Uniformization.lean`, section variables `{L L' : PeriodPair} {c : ℂˣ}`):
     `lemma weierstrassCurve_j_eq_of_lattice_eq_smul (h : L'.lattice = (c • L).lattice) : L'.weierstrassCurve.j = L.weierstrassCurve.j`
   - Stub: the same statement with the same implicit variables, body `sorry`. No difference.
2. `PeriodPair.weierstrassCurve_j_eq_iff`
   - `Suggested.lean`: none.
   - PR #28061 (`LatticeClassification.lean`, variables `{L L' : PeriodPair}`):
     `theorem weierstrassCurve_j_eq_iff : L.weierstrassCurve.j = L'.weierstrassCurve.j ↔ ∃ c : ℂˣ, L'.lattice = (c • L).lattice`
   - Stub: the same statement, body `sorry`. No difference.

The stub module imports only `TauCeti.Analysis.SpecialFunctions.Elliptic.AdditionTheorem`.

**Port:** in `IdealLattice.lean` replace `import TauCeti.Lookahead.CmLatticeDictionary.Stubs` by
`import TauCeti.Analysis.SpecialFunctions.Elliptic.Uniformization` (already imported transitively);
in `ComplexMultiplication/JInvariant.lean` replace it by
`import TauCeti.Analysis.SpecialFunctions.Elliptic.LatticeClassification`; delete
`TauCeti/Lookahead/`. Nothing else refers to the stub module. Splits 1, 2, 6 and 8 need no supplier
at all and can be opened now.

## Split plan

Each split builds on `main` plus the splits it lists as needed first.

### Split 1 — `feat: scalar maps between period lattices, their kernels, degrees and duals`
- Needs first: none (the supplier's #22646 is on `main`).
- Files: new `TauCeti/Analysis/SpecialFunctions/Elliptic/ScalarMap.lean` (304 lines); adds
  `PeriodPair.intCast_mul_mem_lattice` and `PeriodPair.latticeBasis_repr_eq` to
  `TauCeti/Analysis/Complex/UpperHalfPlane/PeriodPair.lean`.
- Declarations (`PeriodPair`): `weierstrassPointHom_surjective`, `mem_ker_weierstrassPointHom`,
  `pointHom_ext`, `scalarPointHom` (`E_Λ(ℂ) →+ E_Λ'(ℂ)`, `P_Λ(z) ↦ P_Λ'(α z)`, for `α Λ ⊆ Λ'`),
  `scalarPointHom_weierstrassPoint`, `scalarPointHom_one`, `scalarPointHom_comp`,
  `scalarPointHom_intCast`, `weierstrassPoint_mem_ker_scalarPointHom_iff`,
  `scalarPointHom_surjective`, `natCard_ker_scalarPointHom` (degree `[Λ' : c Λ]`),
  `relIndex_lattice_smul_eq_natAbs`, `mul_sub_mul_ne_zero`, `relIndex_lattice_smul_ne_zero`,
  `natCard_zsmul_eq_zero` (`#E_Λ(ℂ)[n] = n²`), `relIndex_div_mul_mem_lattice`,
  `scalarPointHom_comp_dual`, `scalarPointHom_dual_comp`; private `kerParam`, `latticeBasis'`.
  If #28061's `weierstrassPointEquiv` lands first, `weierstrassPointHom_surjective` may be restated
  through it.

### Split 2 — `feat: the multiplier ring of a period lattice and its analytic endomorphisms`
- Needs first: 1.
- Files: new `TauCeti/Analysis/SpecialFunctions/Elliptic/Endomorphism.lean` (263 lines).
- Declarations (`PeriodPair`): `scalarPointHom_add`, `scalarPointHom_zero`,
  `scalarPointHom_eq_zero_iff`, `multiplierRing`, `mem_multiplierRing`, `multiplierRing_smul`,
  `endRingHom`, `endRingHom_apply`, `endRingHom_weierstrassPoint`, `endRingHom_injective`,
  `sq_sub_trace_mul_add_norm_eq_zero`, `isIntegral_of_mem_multiplierRing`,
  `exists_intCast_eq_of_im_eq_zero`, `multiplierRing_eq_bot_iff`, `natCard_ker_endRingHom`.

### Split 3 — `feat: fractional ideals of imaginary quadratic orders as period lattices`
- Needs first: 2, and the supplier's `weierstrassCurve_j_eq_of_lattice_eq_smul` (#28061).
- Files: new `TauCeti/NumberTheory/ComplexMultiplication/IdealLattice.lean` (288 lines).
- Declarations (`TauCeti.GlobalNumberFields.NumberFieldOrder`):
  `linearIndependent_real_of_span_rat_eq_top`, `exists_periodPair_lattice_eq`,
  `multiplierRing_eq_map`, `multiplierRing_eq_map_of_isProper`, `multiplierRingEquiv`,
  `coe_multiplierRingEquiv`, `orderEndRingHom`, `orderEndRingHom_weierstrassPoint`,
  `orderEndRingHom_injective`, `lattice_smul_eq_image_spanSingleton_mul`, `jInvariant`,
  `jInvariant_eq`, `jInvariant_eq_of_homothetyCon`; (`IdealClassMonoid`) `jInvariant`,
  `jInvariant_mk`, `exists_jInvariant_eq_j`.

### Split 4 — `feat: ideal classes of an imaginary quadratic order and lattices with CM`
- Needs first: 3.
- Files: new `TauCeti/NumberTheory/ComplexMultiplication/LatticeClass.lean` (200 lines); adds
  `PeriodPair.mem_lattice_smul_iff` to `PeriodPair.lean`.
- Declarations: `exists_eq_spanSingleton_mul_of_lattice_eq_smul`,
  `mk_eq_mk_iff_exists_lattice_eq_smul`, `exists_isProper_lattice_smul_eq`; private helpers.

### Split 5 — `feat: the Picard group acts simply transitively on lattices with CM`
- Needs first: 4.
- Files: new `TauCeti/NumberTheory/ComplexMultiplication/ClassGroupAction.lean` (248 lines).
- Declarations: `CMLattice`, `CMLattice.homothety`, `CMClass`, `CMClass.mk`,
  `CMClass.mk_surjective`, `CMClass.mk_eq_mk_iff`, `cmLatticeOfIsProper`,
  `coe_lattice_cmLatticeOfIsProper`, `cmClassEquiv` (`Pic O ≃ CMClass O σ`), `cmClassEquiv_mkPic`,
  `picSMul`, `picSMul_cmClassEquiv`, `cmClassMulAction`, `picSMul_mk`, `exists_picSMul_eq`,
  `picSMul_eq_self_iff`; private `unitRep`, `ofUnit`.

### Split 6 — `feat: the index of 𝔞 J in an invertible fractional ideal J is the index of 𝔞`
- Needs first: none (general ring theory, no supplier).
- Files: new `TauCeti/RingTheory/FractionalIdeal/Index.lean` (98 lines).
- Declarations (`FractionalIdeal`): `toAddSubgroup_coeIdeal`, `toAddSubgroup_spanSingleton_mul`,
  `relIndex_coeIdeal_mul_eq_index` (`[J : 𝔞 J] = [R : 𝔞]` for invertible `J` and `𝔞` in finitely
  many maximal ideals; via `main`'s coprime representative
  `exists_coeIdeal_eq_spanSingleton_mul_and_sup_eq_top` and the second isomorphism theorem).
- Small: may instead be folded into split 7.

### Split 7 — `feat: the isogeny of an invertible integral ideal, its torsion kernel and its degree`
- Needs first: 5, 6.
- Files: new `TauCeti/NumberTheory/ComplexMultiplication/IdealIsogeny.lean` (249 lines); adds
  `NumberFieldOrder.exists_mkPic_eq_coeIdeal` to
  `TauCeti/NumberTheory/NumberField/Global/Orders/Picard.lean`.
- Declarations: `idealTorsion`, `weierstrassPoint_mem_idealTorsion_iff`,
  `mem_lattice_of_mul_eq_one`, `ker_scalarPointHom_one_eq_idealTorsion`, `natCard_idealTorsion`,
  `natCard_idealTorsion_eq_relIndex`, `natCard_idealTorsion_eq_index` (**new**: the degree of the
  `𝔞`-isogeny is the norm `[O : 𝔞]`), `exists_isogeny_picSMul`; private `toSubring`.

### Split 8 — `feat: Vélu's formulas for ℘ of a superlattice`
- Needs first: 1 (only for `relIndex_lattice_smul_ne_zero`); no supplier.
- Files: new `TauCeti/Analysis/SpecialFunctions/Elliptic/Superlattice.lean` (266 lines).
- Declarations (`PeriodPair`): `finite_quotient_of_le`, `hasSum_weierstrassP_of_le`
  (`℘_{Λ'}(z) = ∑_{t ∈ Λ'/Λ} (℘_Λ(z - t) - ℘_Λ(t))`), `hasSum_derivWeierstrassP_of_le`
  (`℘'_{Λ'}(z) = ∑_t ℘'_Λ(z - t)`), `lattice_le_lattice_inv_smul`, `hasSum_weierstrassP_mul`,
  `hasSum_derivWeierstrassP_mul` (the scalar-map forms, `℘_{Λ'}(α z) = α⁻² ∑ …`),
  `sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq` (`℘(z) = ℘(w)` forces `z ≡ ±w`),
  `weierstrassP_sub_eq`, `derivWeierstrassP_sub_eq`,
  `hasSum_weierstrassP_sub_weierstrassP_of_le`,
  `hasSum_derivWeierstrassP_sub_derivWeierstrassP_of_le` (the rational description off `Λ'`);
  private `hasSum_fiberwise`, `out_mem_lattice_iff`, `notMem_of_notMem_of_le`.

### Split 9 — `feat: the j-invariant classifies ideal classes and curves with complex multiplication`
- Needs first: 5, and the supplier's `weierstrassCurve_j_eq_iff` (#28061).
- Files: new `TauCeti/NumberTheory/ComplexMultiplication/JInvariant.lean` (120 lines).
- Declarations: `jInvariant_eq_jInvariant_iff`, `CMClass.jInvariant`, `CMClass.jInvariant_mk`,
  `CMClass.jInvariant_injective`, `injective_jInvariant_cmClassEquiv`;
  (`IdealClassMonoid`) `jInvariant_injective`.

### Split 10 (planned, not yet written) — `feat: scalar maps between lattices are algebraic isogenies`
- Needs first: 1–9.
- Content: see "Remains" below. It carries the target's exported comparison theorems and is the
  only split that completes the target.

## What is proved and what remains (`partial`)

Proved (no `sorry` outside the stub file): the whole analytic dictionary and its arithmetic.
Scalar maps `α Λ ⊆ Λ'` are homomorphisms of the Weierstrass point groups with kernel `α⁻¹Λ'/Λ`,
degree `[Λ' : αΛ] = |det|`, functoriality, `[n]` and duals composing to `[deg]`; the multiplier ring
acts faithfully, its elements are quadratic integers with degree = norm, and it is `ℤ` exactly
without CM. For an imaginary quadratic order `O` oriented by `σ`, nonzero fractional ideals give
lattices whose multiplier ring is `σ` of the ideal's (endomorphism-order comparison), ideal classes
correspond to homothety classes of lattices with CM by `O`, `Pic O` acts simply transitively,
the action is realized by the `𝔞`-isogenies `E_I → E_{𝔞⁻¹I}` with kernel `E_I[𝔞]` and degree
`[𝔞⁻¹I : I] = [O : 𝔞]`, and the `j`-invariant classifies ideal classes, CM lattices and `Pic O`.
Vélu's formulas express `℘_{Λ'}` and `℘'_{Λ'}` (hence `℘_{Λ'}(α z)`, `℘'_{Λ'}(α z)`) as explicit
rational functions of `℘_Λ(z)`, `℘'_Λ(z)`.

Remains (split 10): **the algebraic isogeny.** `main` already has the algebraic Vélu isogeny
`WeierstrassCurve.Affine.veluIsogeny W Φ : W → W / Φ` with `veluX = ∑_{Q ∈ Φ} (x ∘ τ_Q - x(Q))`,
`veluY = ∑_Q (y ∘ τ_Q - y(Q))`, degree `#Φ`, kernel `Φ` and the quotient universal property
(`TauCeti/AlgebraicGeometry/EllipticCurve/Isogeny/Velu/`). These are exactly split 8's analytic
formulas evaluated along `P_Λ` with `Φ = P_Λ(Λ'/Λ) = ker (scalarPointHom 1)`. The plan:
1. an evaluation injection: an element of the function field of `E_Λ` vanishing at `P_Λ(z)` for
   `z` in a nonempty open set is `0` (write it as `(a + b y)/d`; use `z ↦ -z` and that `℘` is open);
2. evaluate `veluX`, `veluY` at `P_Λ(z)` (translation by `Q = P_Λ(t)` is `z ↦ z + t`, by
   `weierstrassPoint_add`) and compare with `hasSum_weierstrassP_of_le` (the sum over `Φ` is the sum
   over `Λ'/Λ`; `∑ y(Q) = 0` by `Q ↦ -Q`), so `veluCurve E_Λ Φ = E_{Λ'}` by step 1 applied to the two
   Weierstrass equations;
3. compose with the variable change of `Λ' = α (α⁻¹Λ')` (#28061's `pointAddEquivOfLatticeEq`) to get
   an isogeny `E_Λ → E_{Λ'}` whose point map is `scalarPointHom α`; read off degree
   (`degree_veluIsogeny` vs `natCard_ker_scalarPointHom`), kernel and the dual from the universal
   property, and identify the algebraic endomorphism ring of `E_I` with `O` via `orderEndRingHom`.
