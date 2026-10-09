/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Finite

set_option warningAsError false

/-!
# Lookahead stubs for `nonempty-tate-module`

These are lookahead stubs for the supplier `nonempty-tate-module` (LocalGaloisGroups, Layer 7
Step 3), to be replaced by the landed declarations. The structure is stated as in the open pull
request #13651 (`TauCeti/NumberTheory/Padics/MultiplicativeCompletion/LayerTateModule/Basic.lean`),
which renames the roadmap's `TateModule` to `LayerTateModule` because `TauCeti.TateModule` is
already the `p`-adic Tate module of an abelian group, and spells the augmentation ideal as the
kernel of `MonoidAlgebra.augmentation`.
-/

@[expose] public section

universe u

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (L : Type u) [Field L] (K : Type u) [Field K] [Algebra K L]

/-- **A Tate module of a layer** `L/K`: the properties of the module `Y = I_{G_K}/I_{G_L} I_{G_K}`
of NSW (5.6.5) that the integral decomposition in the proof of (7.4.1) consumes, without an
identification with that quotient. It is a finitely generated `ℤ_p[Gal(L/K)]`-module of
projective dimension at most one, together with an extension `0 → A(L) → Y → I_G → 0` of the
augmentation ideal `I_G` by the `p`-adic completion `A(L)` of `Lˣ`. -/
structure LayerTateModule where
  /-- The carrier `Y`. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) carrier]
  /-- The inclusion of `A(L)`. -/
  ι : Additive ↑(padicCompletionUnits p L) →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] carrier
  /-- The projection onto the augmentation ideal. -/
  π : carrier →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
    RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L))
  ι_injective : Function.Injective ι
  π_surjective : Function.Surjective π
  exact : LinearMap.ker π = LinearMap.range ι
  finite : Module.Finite (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) carrier
  /-- Projective dimension at most one: a quotient of a free module by a projective kernel. -/
  projdim : ∃ (n : ℕ) (f : (Fin n → MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) →ₗ[MonoidAlgebra ℤ_[p]
      (L ≃ₐ[K] L)] carrier),
    Function.Surjective f ∧ Module.Projective (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (LinearMap.ker f)

attribute [instance] LayerTateModule.addCommGroup LayerTateModule.module

end TauCeti
