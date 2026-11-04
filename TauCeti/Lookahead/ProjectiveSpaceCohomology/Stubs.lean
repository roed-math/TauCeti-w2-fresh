/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

set_option warningAsError false

/-!
# Lookahead stubs for `projective-space-cohomology`

These would be lookahead stubs for the supplier `qcoh-higher-direct-image-vanishing`
(SchemeAndStackFoundations, §2.6), to be replaced by the landed declarations. The computation of
`Hᵠ(ℙⁿ_R, 𝒪(d))` consumes nothing from that supplier: the vanishing above the dimension, the
vanishing in the intermediate degrees, the zeroth cohomology and Leray's comparison for the
standard affine cover are already on `main`, and the top degree is computed here from the Čech
complex of the standard cover. This module therefore states no declaration.
-/
