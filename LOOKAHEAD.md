<!--tauceti-lookahead:v1 {"area":"ImaginaryQuadraticClassNumber","slug":"cm-lattice-dictionary","main":"e8758b7b2f82b9b1c3f33b992ab8f499b510240f","status":"complete","suppliers":["weierstrass-uniformization"],"splits":[{"n":1,"after":[],"title":"feat: scalar maps between period lattices, their kernels, degrees and duals"},{"n":2,"after":[1],"title":"feat: the multiplier ring of a period lattice and its analytic endomorphisms"},{"n":3,"after":[2],"title":"feat: fractional ideals of imaginary quadratic orders as period lattices"},{"n":4,"after":[3],"title":"feat: ideal classes of an imaginary quadratic order and lattices with CM"},{"n":5,"after":[4],"title":"feat: the Picard group acts simply transitively on lattices with CM"},{"n":6,"after":[],"title":"feat: the index of 𝔞 J in an invertible fractional ideal J is the index of 𝔞"},{"n":7,"after":[5,6],"title":"feat: the isogeny of an invertible integral ideal, its torsion kernel and its degree"},{"n":8,"after":[1],"title":"feat: Vélu's formulas for ℘ of a superlattice"},{"n":9,"after":[5],"title":"feat: the j-invariant classifies ideal classes and curves with complex multiplication"},{"n":10,"after":[1,8],"title":"feat: Vélu's quotient of E_Λ by Λ'/Λ is E_Λ'"},{"n":11,"after":[2,10],"title":"feat: scalar maps between lattices are algebraic isogenies"},{"n":12,"after":[11],"title":"feat: every isogeny between curves of lattices is a scalar map"},{"n":13,"after":[1,2,3,4,5,6,7,8,9,10,11,12],"title":"feat: the algebraic curves with complex multiplication of an imaginary quadratic order"}]}-->
# Lookahead: `cm-lattice-dictionary` (ImaginaryQuadraticClassNumber, H3.1)

Built on `main` at `e8758b7b2f82b9b1c3f33b992ab8f499b510240f`. Status: **complete**. All thirteen
planned splits are on the branch, and split 13 is the final one. No `sorry` occurs outside the stub
file.

Target (H3.1): "Prove that scalar maps between lattices correspond to algebraic isogenies, with
kernel/degree/dual comparisons to EllipticCurves, by the rational elliptic-function description in
wp and wp prime. Then, for every imaginary quadratic order, construct the oriented
ideal-lattice/complex elliptic-curve equivalence, endomorphism-order comparison, class-group action
and j-invariant classification."

## Changes since the previous session (tip `f0d3009ab9a`)

- `main` is unchanged (`e8758b7b2f8`), and #28061 is still open at head `15ddff1b`, so every stub
  stays. One stub was added, `WeierstrassCurve.exists_variableChange_smul_weierstrassCurve_periodPair_eq`
  from #28061's `LatticeClassification.lean`.
- **The converse is proved**, so the target is complete. New **split 12**
  (`Elliptic/LatticeIsogeny.lean`) has three parts.
  - *Period-lattice recovery* (`PeriodPair.lattice_eq_of_weierstrassCurve_eq`, and the iff
    `PeriodPair.weierstrassCurve_eq_iff`). #28061 does not state it, so it is proved from the
    stubbed `j`-classification. If `E_{cΛ} = E_Λ`, then `g₂ (c⁴ - 1) = 0` and `g₃ (c⁶ - 1) = 0`.
    For `c ≠ ±1` this forces `c² + 1 = t c` with `t ∈ {0, ±1}`. The lattice `ℤ + ℤ c` is stable
    under `c` and `c⁻¹ = t - c`, and it has the same `j` (`0` or `1728`), so `Λ` is a multiple of
    it and `cΛ = Λ`.
  - *The kernel lattice*. The preimage `M` of `ker φ` is discrete (it lies in `(deg φ)⁻¹ Λ`, since
    `#ker φ = deg φ` over `ℂ`) and spans `ℂ`. It is therefore a period lattice, by the new general
    `PeriodPair.exists_lattice_eq` in `PeriodPair.lean`. Vélu's `isogenyOfLE (Λ ⊆ M)` has the same
    kernel as `φ`, so `main`'s `existsUnique_variableChangeIsogeny_comp_eq_of_ker_eq` writes `φ`
    as a change of variables `C` after it. Between short forms `C = (u, 0, 0, 0)`
    (`main`'s `VariableChange.{r,s,t}_eq_zero_of_isShortNF`), so `E_{Λ'} = E_{uM}`. Recovery then
    gives `Λ' = uM ⊇ uΛ`.
  - *Consequences*: `PeriodPair.exists_eq_scalarIsogeny` (every isogeny is `scalarIsogeny c h`),
    `PeriodPair.nonempty_isogeny_iff`, `PeriodPair.multiplierCMAction_surjective`, and
    `PeriodPair.multiplierRingEquivHom : multiplierRing ≃+* End(E_Λ)`.
- Split 11 also gains `PeriodPair.dual_scalarIsogeny`: the dual isogeny on `main`
  (`Isogeny.dual`) of `scalarIsogeny c` is `scalarIsogeny ([Λ' : cΛ] / c)`.
- The final split (now **13**, `AlgebraicCM.lean`) gains:
  - `cmAction_surjective`;
  - `cmRingEquiv : O ≃+* End(E_I)`, the full endomorphism-order comparison;
  - `exists_isProper_variableChange_smul_eq`. This is the missing half of the ideal/curve
    equivalence: an elliptic curve over `ℂ` whose endomorphisms are all given by a normalised
    action of `O` is `C • E_I` for a proper `I`. The proof conjugates through the stubbed
    uniformization `C • E_τ = E`, shows that the multiplier ring of `ℤτ + ℤ` is `σ(O)`, and
    applies split 4's `exists_isProper_lattice_smul_eq`.

## Changes in the session before (tip `a0b51905cfc`)

- `main` is unchanged (`e8758b7b2f8`); #28061 is still open, so both stubs stay.
- New **split 10** (`Elliptic/VeluIsogeny.lean`) supplies the algebraic half of the old remaining
  item. For `Λ ⊆ Λ'`, Vélu's quotient curve of `E_Λ` by `P_Λ(Λ')` is `E_{Λ'}`
  (`PeriodPair.veluCurve_latticePoints`), so Vélu's isogeny is an algebraic isogeny
  `isogenyOfLE : E_Λ → E_{Λ'}`. It has degree `[Λ' : Λ]`, kernel `P_Λ(Λ')`, and it preserves the
  invariant differential.
  The proof evaluates the function field of `E_Λ` at `(℘_Λ, ℘'_Λ/2)` in the field of germs
  along an ultrafilter at the punctured origin. The evaluation is injective because `℘_Λ` is
  transcendental there (pole at `0`). Translates by `P_Λ(t)` evaluate to `℘_Λ(z+t)`, `℘'_Λ(z+t)/2`
  by the addition theorem, and split 8's Vélu sums give `℘_{Λ'}`, `℘'_{Λ'}/2`.
- New **split 11** (`Elliptic/AlgebraicIsogeny.lean`): for every scalar map `cΛ ⊆ Λ'`, the
  algebraic isogeny `scalarIsogeny c h : E_Λ → E_{Λ'}`, which is `isogenyOfLE` for `Λ ⊆ c⁻¹Λ'`
  followed by a change of variables. It has the kernel of the analytic `scalarPointHom c h` and
  degree `[Λ' : cΛ]`, and it pulls `ω` back to `c ω`.
  A new general lemma, `Isogeny.eq_of_pullbackDifferential_invariantDifferential_eq` (in
  characteristic zero a morphism is determined by its `ω`-constant), then gives:
  `scalarIsogeny` is the unique isogeny scaling `ω` by `c`, it is injective in `c`, it is
  compatible with composition, `scalarIsogeny n = [n]`, and the dual pair
  `scalarIsogeny ([Λ' : cΛ]/c)` composes to `[n]` in both orders. Finally the
  multiplier ring acts on `E_Λ` by a normalised `CMAction` (`multiplierCMAction`).
- New final **split 12** (now split 13, `ComplexMultiplication/AlgebraicCM.lean`) covers, for proper `I` of an
  imaginary quadratic order `O`:
  - the normalised algebraic CM action `cmAction : CMAction O E_I`;
  - the algebraic `𝔞`-isogeny with kernel `E_I[𝔞]` and degree `[O : 𝔞]`;
  - `E_I ≅ E_J` over `ℂ` ⇔ `[I] = [J]`, via split 9 and Mathlib's `exists_variableChange_of_j_eq`.
- Supporting changes to files on `main`:
  - `TauCeti/Order/Filter/Germ.lean` gains `Filter.Germ.algebra_aeval_coe` and `Filter.Germ.coe_sum`
    (split 10; `main`'s `Filter.Germ.algebra` instance is used).
  - `Translation/Differential.lean` gains `D_translation_genericX` (split 10).
  - `Isogeny/InvariantDifferential.lean` gains `Hom.eq_of_pullbackDifferential_invariantDifferential_eq`
    and `eq_of_pullbackDifferential_invariantDifferential_eq` (split 11).
  - `PeriodPair.eventually_weierstrassP_ne` in `AdditionTheorem.lean` becomes public (split 10).

## Stubbed supplier declarations (`weierstrass-uniformization`)

All stubs are in `TauCeti/Lookahead/CmLatticeDictionary/Stubs.lean`. They sit in the root
`PeriodPair` and `WeierstrassCurve` namespaces, where the supplier and its neighbouring code on
`main` put them. The roadmap's `ImaginaryQuadraticClassNumber/Suggested.lean` pins **no**
declaration of `weierstrass-uniformization`: it pins only H1/H2/H3.5/H3.6 forms. So all three stubs
come from the diff of the open supplier PR **#28061**.

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
3. `WeierstrassCurve.exists_variableChange_smul_weierstrassCurve_periodPair_eq`
   - `Suggested.lean`: none.
   - PR #28061 (`LatticeClassification.lean`, `namespace WeierstrassCurve`, variables
     `(E : WeierstrassCurve ℂ) [E.IsElliptic]`):
     `theorem exists_variableChange_smul_weierstrassCurve_periodPair_eq : ∃ (τ : ℍ) (C : VariableChange ℂ), C • τ.periodPair.weierstrassCurve = E`
   - Stub: the same statement with the same variables. The stub writes `UpperHalfPlane` for `ℍ`,
     because the stub file does not open the `UpperHalfPlane` scope. Body `sorry`. Otherwise no
     difference.

The stub module imports only `TauCeti.Analysis.SpecialFunctions.Elliptic.AdditionTheorem`.

**Port:**
- In `IdealLattice.lean`, replace `import TauCeti.Lookahead.CmLatticeDictionary.Stubs` by
  `import TauCeti.Analysis.SpecialFunctions.Elliptic.Uniformization` (already imported
  transitively).
- In `ComplexMultiplication/JInvariant.lean` and in `Elliptic/LatticeIsogeny.lean` (a `public
  import`), replace it by `import TauCeti.Analysis.SpecialFunctions.Elliptic.LatticeClassification`.
- Delete `TauCeti/Lookahead/`. Nothing else refers to the stub module.
- `AlgebraicCM.lean` gets the third stub through `LatticeIsogeny`. Splits 1, 2, 6 and 8 need no supplier
at all and can be opened now.

## Split plan

Each split builds on `main` plus the splits it lists as needed first.

### Split 1 — `feat: scalar maps between period lattices, their kernels, degrees and duals`
- Needs first: none (the supplier's #22646 is on `main`).
- Files: new `TauCeti/Analysis/SpecialFunctions/Elliptic/ScalarMap.lean` (316 lines); adds
  `PeriodPair.intCast_mul_mem_lattice` and `PeriodPair.latticeBasis_repr_eq` to
  `TauCeti/Analysis/Complex/UpperHalfPlane/PeriodPair.lean`.
- Declarations (`PeriodPair`): `weierstrassPointHom_surjective`, `mem_ker_weierstrassPointHom`,
  `pointHom_ext`, `scalarPointHom` (`E_Λ(ℂ) →+ E_Λ'(ℂ)`, `P_Λ(z) ↦ P_Λ'(α z)`, for `α Λ ⊆ Λ'`),
  `scalarPointHom_weierstrassPoint`, `scalarPointHom_one`, `scalarPointHom_comp`,
  `scalarPointHom_intCast`, `weierstrassPoint_mem_ker_scalarPointHom_iff`,
  `scalarPointHom_surjective`, `natCard_ker_scalarPointHom` (degree `[Λ' : c Λ]`),
  `relIndex_lattice_smul_eq_natAbs`, `mul_sub_mul_ne_zero`, `relIndex_lattice_smul_ne_zero`,
  `natCard_zsmul_eq_zero` (`#E_Λ(ℂ)[n] = n²`), `relIndex_div_mul_mem_lattice`,
  `relIndex_div_ne_zero`, `mk0_relIndex_div_mul_mem_lattice`, `scalarPointHom_comp_dual`,
  `scalarPointHom_dual_comp`; private `kerParam`, `latticeBasis'`.
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

### Split 10 — `feat: Vélu's quotient of E_Λ by Λ'/Λ is E_Λ'`
- Needs first: 1 (`relIndex_lattice_smul_ne_zero`, via 8) and 8 (`hasSum_weierstrassP_of_le`,
  `hasSum_derivWeierstrassP_of_le`, `finite_quotient_of_le`); no supplier.
- Files: new `TauCeti/Analysis/SpecialFunctions/Elliptic/VeluIsogeny.lean` (413 lines). It also adds
  `Filter.Germ.algebra_aeval_coe` and `Filter.Germ.coe_sum` to `TauCeti/Order/Filter/Germ.lean`, and
  `WeierstrassCurve.Affine.D_translation_genericX` to
  `TauCeti/AlgebraicGeometry/EllipticCurve/Affine/FunctionField/Translation/Differential.lean`.
  It makes `PeriodPair.eventually_weierstrassP_ne` public in `Elliptic/AdditionTheorem.lean`.
- Declarations (`PeriodPair`): `xCoord_weierstrassPoint`, `yCoord_weierstrassPoint`,
  `latticePoints`, `mem_latticePoints`, `finite_latticePoints`, `veluCurve_latticePoints`,
  `isogenyOfLE`, `fieldPullback_isogenyOfLE_genericX`, `fieldPullback_isogenyOfLE_genericY`,
  `degree_isogenyOfLE`, `ker_isogenyOfLE`, `natCard_ker_isogenyOfLE`,
  `pullbackDifferential_isogenyOfLE`.
  Private helpers:
  - the germ field `Germs` and its ultrafilter;
  - the evaluations `evalCoord` and `evalFF`, their injectivity, and their values on `genericX`,
    `genericY` and translates;
  - `quotientToLatticePoints` (bijective) and the Vélu coordinate evaluations;
  - the cast lemmas `*_eqRec`.

### Split 11 — `feat: scalar maps between lattices are algebraic isogenies`
- Needs first: 2 (`multiplierRing`) and 10; through them 1 and 8.
- Files: new `TauCeti/Analysis/SpecialFunctions/Elliptic/AlgebraicIsogeny.lean` (287 lines); adds
  `TauCeti.Isogeny.Hom.eq_of_pullbackDifferential_invariantDifferential_eq` and
  `TauCeti.Isogeny.eq_of_pullbackDifferential_invariantDifferential_eq` to
  `TauCeti/AlgebraicGeometry/EllipticCurve/Isogeny/InvariantDifferential.lean`.
- Declarations (`PeriodPair`): `scalarIsogeny`, `ker_scalarIsogeny`,
  `pullbackDifferential_scalarIsogeny`, `degree_scalarIsogeny`,
  `degree_scalarIsogeny_eq_relIndex`, `eq_scalarIsogeny_iff`, `scalarIsogeny_inj`,
  `scalarIsogeny_comp`, `scalarIsogeny_intCast`, `scalarIsogeny_comp_dual`,
  `scalarIsogeny_dual_comp`, `dual_scalarIsogeny`,
  `multiplierCMAction`, `pullbackDifferential_multiplierCMAction`,
  `multiplierCMAction_apply_of_ne_zero`.
  Private: `mem_lattice_inv_smul_iff`, `variableChange_weierstrassCurve_inv_smul`,
  `ker_scalarIsogeny_eq`, `multiplierHom`, `pullbackDifferential_multiplierHom`.

### Split 12 — `feat: every isogeny between curves of lattices is a scalar map`
- Needs first: 11 (through it 1, 2, 8, 10), and the supplier's `weierstrassCurve_j_eq_iff`
  (#28061).
- Files: new `TauCeti/Analysis/SpecialFunctions/Elliptic/LatticeIsogeny.lean` (312 lines). It also
  adds `PeriodPair.exists_lattice_eq` (every discrete subgroup of `ℂ` spanning `ℂ` over `ℝ` is a
  period lattice) and `PeriodPair.lattice_smul_eq_self` to
  `TauCeti/Analysis/Complex/UpperHalfPlane/PeriodPair.lean`.
- Declarations (`PeriodPair`): `lattice_eq_of_weierstrassCurve_eq` (period-lattice recovery),
  `weierstrassCurve_eq_iff`, `exists_eq_scalarIsogeny`, `nonempty_isogeny_iff`,
  `multiplierCMAction_surjective`, `multiplierRingEquivHom`, `multiplierRingEquivHom_apply`.
  Private:
  - for recovery: `g₂_g₃_of_weierstrassCurve_smul_eq`, `weierstrassCurve_j_eq_of_g₂_g₃`,
    `exists_sq_add_one_eq_of_weierstrassCurve_smul_eq`, `unitLattice`, `unitLattice_mul_mem`,
    `lattice_smul_eq_of_weierstrassCurve_smul_eq`;
  - for the kernel lattice: `kerLattice`, `mem_kerLattice`, `lattice_le_kerLattice`,
    `degree_mul_mem_lattice`, `exists_lattice_ker`.

### Split 13 (final) — `feat: the algebraic curves with complex multiplication of an imaginary quadratic order`
- Needs first: 1–12. It imports split 12 (`LatticeIsogeny`, through it 11, 10, 8, 2, 1), split 7
  (`IdealIsogeny`, through it 3–6), split 9 (`JInvariant`) and split 4 (`LatticeClass`). It uses
  the supplier's `weierstrassCurve_j_eq_iff` through splits 9 and 12, and
  `exists_variableChange_smul_weierstrassCurve_periodPair_eq` directly.
- Files: new `TauCeti/NumberTheory/ComplexMultiplication/AlgebraicCM.lean` (258 lines).
- Declarations (`TauCeti.GlobalNumberFields.NumberFieldOrder`): `cmAction`, `cmAction_apply`,
  `pullbackDifferential_cmAction`, `cmAction_surjective`, `cmRingEquiv` (`O ≃+* End(E_I)`),
  `cmRingEquiv_apply`, `exists_isProper_variableChange_smul_eq` (every curve with a normalised
  CM by `O` through all its endomorphisms is some `E_I`), `ker_scalarIsogeny_one_eq_idealTorsion`,
  `degree_scalarIsogeny_one_eq_index`, `exists_scalarIsogeny_picSMul` (the algebraic form of
  split 7's `exists_isogeny_picSMul`, with degree `[O : 𝔞]`),
  `exists_variableChange_smul_eq_iff_mk_eq`.
- Private: `pullbackDifferential_conj`.
- The only split that completes the target. It carries the exported theorems: the
  endomorphism-order comparison (`cmRingEquiv`), the class-group action by algebraic isogenies,
  and both halves of the ideal-class/curve equivalence
  (`exists_variableChange_smul_eq_iff_mk_eq` and `exists_isProper_variableChange_smul_eq`).

## What is proved

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

Splits 10–13 add the algebraic side.
- *Scalar map ↦ isogeny.* Every scalar map `cΛ ⊆ Λ'` gives an algebraic isogeny
  `scalarIsogeny c h`. Its kernel is the analytic kernel, its degree is `[Λ' : cΛ]`, and it pulls
  `ω` back to `c ω`. It is the unique isogeny with that differential, injective in `c`, compatible
  with composition, equal to `[n]` for `c = n`. Its dual isogeny is the scalar map
  `[Λ' : cΛ] / c`.
- *Isogeny ↦ scalar map.* Every isogeny `E_Λ → E_{Λ'}` is `scalarIsogeny c h`. Equal Weierstrass
  curves have equal lattices.
- *Endomorphism order.* `End(E_Λ)` is the multiplier ring, and `End(E_I) ≅ O` by a normalised
  action.
- *Class group.* The class-group action is realised by algebraic `𝔞`-isogenies with kernel `E_I[𝔞]`
  and degree `N(𝔞)`.
- *Classification.* `E_I ≅ E_J` over `ℂ` exactly when `[I] = [J]`. Every elliptic curve over `ℂ`
  with a normalised CM by `O` through all of its endomorphisms is some `E_I`, with `I` proper.

Not done (optional, not required by the target): reading the algebraic point map
`Isogeny.toPointHom (scalarIsogeny c h)` through `equivBaseChangeSelf` as `scalarPointHom c h`.
