/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.IndEtale

set_option warningAsError false

/-!
# Lookahead stubs for `ind-etale`

These are lookahead stubs for the supplier `ind-etale` (SchemeAndStackFoundations §0.13, open
pull request #27212), stated as that pull request states them. They are to be replaced by the
landed declarations.
-/

public section

universe u

namespace TauCeti.Algebra.IndEtale

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Ind-étale algebras are stable under composition: an ind-étale algebra over an ind-étale
`R`-algebra is ind-étale over `R` (Stacks, Tag 0BSI). -/
theorem comp (T : Type u) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [IndEtale R S] [IndEtale S T] : IndEtale R T := by
  sorry

end TauCeti.Algebra.IndEtale
