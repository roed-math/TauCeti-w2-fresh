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

The parts of `relative-proj-base-change` proved so far (the pullback `g^* A` of a graded
quasicoherent algebra and the graded ring maps of sections along `g`) consume no declaration of
the supplier, and the twisting sheaves `𝒪(n)` of a relative `Proj` that the compatibility with
`𝒪(n)` will use are already on `main` (`CategoryTheory.CommMon.relativeProjTwistingSheaf`,
`CategoryTheory.CommMon.restrictRelativeProjTwistingSheafIso`). This module therefore states no
stub yet; a later session adds here whatever supplier declaration the remaining splits consume.
-/
