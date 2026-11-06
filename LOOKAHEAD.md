<!--tauceti-lookahead:v1 {"area":"ImaginaryQuadraticClassNumber","slug":"siegel-function","main":"eaaa3ce3cdadc72cf584dd7ab90a70d08ce55956","status":"partial","suppliers":["modular-function-field"],"splits":[{"n":1,"after":[],"title":"feat: finite products of Siegel functions and their SL₂(ℤ) transformation"},{"n":2,"after":[1],"title":"feat: the exact Siegel transformation on Γ(N) and the level-N congruence criterion"},{"n":3,"after":[1,2],"title":"feat: Siegel functions as level-N modular functions, cyclotomic action and integrality over ℤ[j]"}]}-->

# Lookahead: `siegel-function` (ImaginaryQuadraticClassNumber H3.2)

Built on `main` at `eaaa3ce3cda`. Status: **partial**.

## What `main` already has

Most of H3.2 landed earlier (the bors merge of #20811 and its predecessors, all under
`TauCeti/NumberTheory/ModularForms/SiegelFunction/`): the definition `siegelFunction` with the
roadmap's exact phases, locally uniform product convergence, holomorphicity, nonvanishing off `ℤ²`,
the q-order asymptotics, translation in `r` by `ℤ²`, the `SL₂(ℤ)` law with a twelfth root of unity
(`exists_siegelFunction_smul_eq_mul`), `g₀ g₁ g₂ = 2ζ₈`, `gammaTwo` with `gammaTwo ^ 3 = j`, the
leading term `q^(-1/3)` and `γ₂ = (g_i¹² + 16)/g_i⁴` for each `i`, the eta comparison and the
integrality of the level-2 Siegel functions over `ℤ[j]`.

## Stubbed declarations (`TauCeti/Lookahead/SiegelFunction/Stubs.lean`)

Neither is pinned in `ImaginaryQuadraticClassNumber/Suggested.lean`: that file pins no H3.1
declaration at all (its only modular-function items are `siegelHalf`, `gammaTwo`, `cmTau`). Both
stubs are therefore taken verbatim from the open supplier PR #29233's diff
(`TauCeti/NumberTheory/ModularForms/CongruenceSubgroups/FunctionField.lean`), with only the proof
replaced by `sorry`. Everything else they mention (`modularFunctionField`,
`modularFunctionActionZMod`, `Subgroup.compactifiedQuotientComap`,
`ModularGroup.jMeromorphicFunction`) is already on `main` and is not stubbed.

1. `TauCeti.fixedField_unop_range_modularFunctionActionZMod`
   - `Suggested.lean`: none.
   - Stub (= PR #29233):
     ```lean
     theorem fixedField_unop_range_modularFunctionActionZMod :
         IntermediateField.fixedField (modularFunctionActionZMod N).range.unop =
           (Subgroup.compactifiedQuotientComap
             (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R).fieldRange
     ```
   - Differences: none.
2. `TauCeti.modularFunctionField_inf_fixedField_eq_closure`
   - `Suggested.lean`: none.
   - Stub (= PR #29233):
     ```lean
     theorem modularFunctionField_inf_fixedField_eq_closure :
         modularFunctionField N ⊓
             (IntermediateField.fixedField (modularFunctionActionZMod N).range.unop).toSubfield =
           Subfield.closure (insert (Subgroup.compactifiedQuotientComap
               (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R ModularGroup.jMeromorphicFunction)
             (algebraMap ℂ _ '' Subfield.closure {z : ℂ | z ^ N = 1}))
     ```
   - Differences: none.

These are the supplier facts the remaining splits 2–3 consume (a Siegel product fixed by
`SL(2, ℤ/Nℤ)` lies in `ℚ(ζ_N)(j)`; integrality over `ℤ[j]`). No proved declaration on the branch
uses them yet.

## Splits

1. **feat: finite products of Siegel functions and their SL₂(ℤ) transformation** — after: none.
   On the branch, proved. File `TauCeti/NumberTheory/ModularForms/SiegelFunction/Product.lean`
   (new). Adds `siegelProduct`, `siegelProduct_def`, `siegelProduct_zero`, `siegelProduct_single`,
   `siegelProduct_neg`, `siegelProduct_add`, `siegelProduct_ne_zero`,
   `differentiableOn_siegelProduct`, `mdifferentiable_siegelProduct`,
   `exists_siegelProduct_smul_eq_mul`, `siegelProduct_smul_of_dvd_sum` (the roadmap's
   "inverse/product and finite-support exponent-family APIs"). Does not need the supplier.
2. **feat: the exact Siegel transformation on Γ(N) and the level-N congruence criterion** — after: 1.
   Not yet on the branch. File `SiegelFunction/Level.lean`: the explicit root of unity of
   `g_r ∘ γ` for `γ ∈ Γ(N)` and `r ∈ N⁻¹ℤ²` (Kubert–Lang K 1–K 3), the quadratic congruence
   criterion for `∏ g_r^{m(r)}` to be `Γ(N)`-invariant, and `g_r^{12N/gcd(6,N)}` invariant.
3. **feat: Siegel functions as level-N modular functions, cyclotomic action and integrality over
   ℤ[j]** — after: 1, 2. Not yet on the branch. Places the products of split 2 in
   `modularFunctionField N` (q-expansion with coefficients in `ℚ(ζ_N)`), proves the diagonal
   `diag(1, d)` cyclotomic action `g_r ↦ g_{(r₁, d r₂)}`, and integrality over `ℤ[j]` via the
   stubbed `modularFunctionField_inf_fixedField_eq_closure` (the characteristic polynomial over
   the `SL(2, ℤ/Nℤ)`-orbit). Carries the target's exported theorems; it is the split that completes
   the target.

## What remains

Splits 2 and 3 above: the exact `Γ(N)` transformation phases, the congruence criterion, the power
`12N/gcd(6,N)`, membership in `F_N`, the diagonal cyclotomic action and integrality over `ℤ[j]`
for general level (level 2 is on `main`). The round's time ran out before these were started.
