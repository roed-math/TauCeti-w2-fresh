/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

set_option warningAsError false

/-!
# Lookahead stubs for `qcoh-pushforward`

These are lookahead stubs for the supplier `qcoh-pushforward` (SchemeAndStackFoundations,
Layer 0, §0.4), stated as in its open pull request #21787
(`TauCeti/AlgebraicGeometry/Modules/Quasicoherent/Pushforward/QuasiSeparated.lean`). They are to
be replaced by the landed declarations.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (M : X.Modules) (f : X ⟶ Y)

/-- **Pushforward along a quasi-compact quasi-separated morphism preserves quasi-coherence.** -/
instance isQuasicoherent_pushforward [M.IsQuasicoherent] [QuasiCompact f] [QuasiSeparated f] :
    ((pushforward f).obj M).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.Scheme.Modules
