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

These are lookahead stubs for the supplier slug `modular-function-field`
(ImaginaryQuadraticClassNumber, H3.1), to be replaced by the landed declarations. `main` already
has the field `F_N` (`TauCeti.modularFunctionField`) and the right action of `SL(2, ℤ/Nℤ)`
(`TauCeti.modularFunctionActionZMod`). The supplier still owes the action of `GL(2, ℤ/Nℤ)` on
`F_N`, in which the `SL(2)` part acts by fractional linear maps and `diag(1, d)` acts on Fourier
coefficients; the reciprocity law of the target `cm-tau` lets the multiplication matrices act
through it. Only its existence as a right action extending the `SL(2)` action is stubbed here.
-/

public noncomputable section

open CongruenceSubgroup MulOpposite TauCeti.RiemannSurface
open scoped MatrixGroups

namespace TauCeti

variable (N : ℕ) [NeZero N]

/-- Lookahead stub: the right action of `GL(2, ℤ/Nℤ)` on `F_N`. -/
def modularFunctionActionGL :
    GL (Fin 2) (ZMod N) →* (modularFunctionField N ≃+* modularFunctionField N)ᵐᵒᵖ :=
  sorry

variable {N}

/-- Lookahead stub: on `SL(2, ℤ/Nℤ)` the action is the fractional linear action of
`TauCeti.modularFunctionActionZMod`. -/
theorem coe_unop_modularFunctionActionGL_toGL (g : SL(2, ZMod N))
    (F : modularFunctionField N) :
    ((unop (modularFunctionActionGL N (Matrix.SpecialLinearGroup.toGL g)) F :
        modularFunctionField N) : MeromorphicFunction _) =
      unop (modularFunctionActionZMod N g) F := by
  sorry

/-- Lookahead stub: `-1` acts trivially, so the action is one of `GL(2, ℤ/Nℤ) / {±1}`. -/
theorem modularFunctionActionGL_neg_one : modularFunctionActionGL N (-1) = 1 := by
  sorry

end TauCeti
