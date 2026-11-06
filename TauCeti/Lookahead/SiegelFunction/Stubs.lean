/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField

set_option warningAsError false

/-!
# Lookahead stubs for `modular-function-field`

These are lookahead stubs for the supplier `modular-function-field`
(ImaginaryQuadraticClassNumber H3.1), stated as in its open pull request #29233, to be replaced by
the landed declarations. They are the fixed-field statements the level-`N` congruence criterion and
the integrality of Siegel products over `ℤ[j]` consume.
-/

public noncomputable section

open CongruenceSubgroup MulOpposite Subgroup.CompactifiedQuotient TauCeti.RiemannSurface
open scoped MatrixGroups Pointwise UpperHalfPlane

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-- **The fixed field of `SL(2, ℤ/Nℤ)`.** Lookahead stub of PR #29233. -/
theorem fixedField_unop_range_modularFunctionActionZMod :
    IntermediateField.fixedField (modularFunctionActionZMod N).range.unop =
      (Subgroup.compactifiedQuotientComap
        (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R).fieldRange := by
  sorry

/-- **The modular functions of level `N` fixed by `SL(2, ℤ/Nℤ)` are `ℚ(ζ_N)(j)`.** Lookahead
stub of PR #29233. -/
theorem modularFunctionField_inf_fixedField_eq_closure :
    modularFunctionField N ⊓
        (IntermediateField.fixedField (modularFunctionActionZMod N).range.unop).toSubfield =
      Subfield.closure (insert (Subgroup.compactifiedQuotientComap
          (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R ModularGroup.jMeromorphicFunction)
        (algebraMap ℂ _ '' Subfield.closure {z : ℂ | z ^ N = 1})) := by
  sorry

end TauCeti
