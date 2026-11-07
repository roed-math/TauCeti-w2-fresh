<!--tauceti-lookahead:v1 {"area":"ImaginaryQuadraticClassNumber","slug":"siegel-function","main":"57cfc63ad4ea735fa8532c4eb95647b2495c6384","status":"partial","suppliers":["modular-function-field"],"splits":[{"n":1,"after":[],"title":"feat: finite products of Siegel functions and their SL₂(ℤ) transformation"},{"n":2,"after":[1],"title":"feat: the exact Siegel transformation on Γ(N) and the level-N congruence criterion"},{"n":3,"after":[1,2],"title":"feat: Siegel functions as level-N modular functions, cyclotomic action and integrality over ℤ[j]"}]}-->

# Lookahead: `siegel-function` (ImaginaryQuadraticClassNumber H3.2)

Built on `main` at `57cfc63ad4e`. Status: **partial**.

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
   Proved on the branch; does not need the supplier. Files
   `TauCeti/NumberTheory/ModularForms/SiegelFunction/Level.lean` (new, imports
   `SiegelFunction.Product`, Mathlib's `CongruenceSubgroups` and `MoebiusAction`) and
   `TauCeti/NumberTheory/ModularForms/SiegelFunction/Transform.lean` (existing; adds
   `siegelFunction_neg`, `g_{-r} = -g_r`, the action of `S² = -1`, next to the `S` law).
   **Proved in full on the branch** (`Level.lean`, 515 lines):
   - translations: `siegelFunction_apply_add_natCast` (`g_r(τ + n) = e^{π i n/6} g_{(r₁, n r₁ + r₂)}(τ)`),
     `siegelFunction_apply_add_natCast_of_mul_eq` (exact `T^N` phase
     `e^{π i N/6} (-1)^a e^{π i a r₁}` when `N r₁ = a`),
     `siegelFunction_pow_apply_add_natCast_of_mul_eq`, and the lower-triangular counterparts
     `siegelFunction_apply_div_natCast_mul_add_one`,
     `siegelFunction_apply_div_natCast_mul_add_one_of_mul_eq`,
     `siegelFunction_pow_apply_div_natCast_mul_add_one_of_mul_eq` (private helper
     `translationPhase_pow_eq_one`);
   - the `T^N` / `L^N` halves of the product criterion (only one quadratic condition each):
     `siegelProduct_apply_add_natCast_of_dvd`, `siegelProduct_apply_div_natCast_mul_add_one_of_dvd`
     (private `prod_translationPhase_zpow_eq_one`);
   - **general `γ ∈ Γ(N)`** (round 7): the private `exists_siegelFunction_smul_eq_of_mem_Gamma`
     (writing `γ = 1 + N[[u, w], [v, z]]`, there is a twelfth root of unity `ε` depending only on
     `γ` with `g_r(γτ) = ε (-1)^{s₁s₂+s₁+s₂} e^{-π i (s₁ r₂ - s₂ r₁)} g_r(τ)`,
     `(s₁, s₂) = r γ - r = (a u + b v, a w + b z)`, plus the determinant relation
     `u + z + N(uz - vw) = 0`), the private `integralTranslationPhase_pow_eq_one`,
     **`siegelFunction_pow_smul_of_mem_Gamma`** (`g_r^{12N/gcd(6,N)}` is `Γ(N)`-invariant when
     `N r ∈ ℤ²`: the roadmap's "power 12N/gcd[6,N]"), the private
     `prod_congruencePhase_zpow_eq_one` (the parity bookkeeping, reduced to a `decide` over
     `ZMod 2` in the two cases `N` even / odd), and **`siegelProduct_smul_of_mem_Gamma`**, the full
     Kubert–Lang congruence criterion: `12 ∣ ∑ m(r)`, `gcd(2,N) N ∣ ∑ m(r) a_r²`,
     `gcd(2,N) N ∣ ∑ m(r) b_r²`, `N ∣ ∑ m(r) a_r b_r` imply `∏ g_r^{m(r)}` is `Γ(N)`-invariant.
   Split 2 is therefore complete; at the port, consider whether reviewers want the two
   `T^N` / `L^N` product statements kept (they need only one quadratic condition each, so they
   are not literally special cases of the general criterion).
3. **feat: Siegel functions as level-N modular functions, cyclotomic action and integrality over
   ℤ[j]** — after: 1, 2. Not yet on the branch. Places the products of split 2 in
   `modularFunctionField N` (q-expansion with coefficients in `ℚ(ζ_N)`), proves the diagonal
   `diag(1, d)` cyclotomic action `g_r ↦ g_{(r₁, d r₂)}`, and integrality over `ℤ[j]` via the
   stubbed `modularFunctionField_inf_fixedField_eq_closure` (the characteristic polynomial over
   the `SL(2, ℤ/Nℤ)`-orbit). Carries the target's exported theorems; it is the split that completes
   the target.

## What remains

Split 3 only: membership of the `Γ(N)`-invariant Siegel products of split 2 in
`modularFunctionField N` (meromorphy at the cusps from the q-order asymptotics on `main`, and the
q-expansion coefficients in `ℚ(ζ_N)`), the diagonal `diag(1, d)` cyclotomic action
`g_r ↦ g_{(r₁, d r₂)}`, and integrality over `ℤ[j]` for general level via the stubbed
`modularFunctionField_inf_fixedField_eq_closure`. Rounds 1–6 built splits 1–2 up to the
`T^N` / `L^N` halves of the criterion; round 7 (on `main` at `57cfc63ad4e`; supplier PR #29233
still open, so both stubs stay) proved the general `Γ(N)` phase, the power `12N/gcd(6,N)` on all
of `Γ(N)` and the full congruence criterion, completing split 2.
