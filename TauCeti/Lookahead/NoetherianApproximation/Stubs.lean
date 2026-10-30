/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels

set_option warningAsError false

/-!
# Lookahead stubs for `qcoh-extension`

These are lookahead stubs for the supplier `qcoh-extension` (SchemeAndStackFoundations §0.4),
to be replaced by the landed declarations. Only the finite-type submodule extension of Stacks,
Lemma 28.23.2 (01PF), is stated: it extends finite-type quasi-coherent ideal sheaves from a
quasi-compact open of a quasi-compact quasi-separated scheme, which absolute Noetherian
approximation consumes.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **Extension of finite-type quasi-coherent submodules.** Along a quasi-compact open immersion
`j : U ⟶ X` into a quasi-compact quasi-separated scheme, a finite-type quasi-coherent submodule
`i : F ⟶ j^* G` of the restriction of a quasi-coherent `𝒪_X`-module `G` is the restriction of a
finite-type quasi-coherent submodule `i' : G' ⟶ G`. Stacks, Lemma 28.23.2 (01PF). -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_restrict_iso
    [QuasiCompact j] [CompactSpace X] [QuasiSeparatedSpace X] {G : X.Modules}
    [G.IsQuasicoherent] {F : U.Modules} [F.IsQuasicoherent] [F.IsFiniteType]
    (i : F ⟶ G.restrict j) [Mono i] :
    ∃ (G' : X.Modules) (_ : G'.IsQuasicoherent) (_ : G'.IsFiniteType) (i' : G' ⟶ G) (_ : Mono i')
      (e : G'.restrict j ≅ F), (Scheme.Modules.restrictFunctor j).map i' = e.hom ≫ i := by
  sorry

end TauCeti.AlgebraicGeometry
