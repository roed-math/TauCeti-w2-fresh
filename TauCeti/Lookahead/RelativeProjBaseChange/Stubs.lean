/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf

set_option warningAsError false

/-!
# Lookahead stubs for `relative-proj-base-change`

Lookahead stubs for the supplier `relative-proj-twisting-sheaf` (SchemeAndStackFoundations,
Layer 0, §0.3), to be replaced by the landed declarations.

`relative-proj-base-change` consumes no declaration of the supplier: the relative `Proj`, its
twisting sheaves `𝒪(n)` and their chart identifications
(`CategoryTheory.CommMon.relativeProjTwistingSheaf`,
`CategoryTheory.CommMon.restrictRelativeProjTwistingSheafIso`) are already on `main`, and the
comparison `h^* 𝒪(n) ⟶ 𝒪(n)` is checked on the charts, where the twisting sheaves are those of
`Proj`. This module therefore states no stub.
-/
