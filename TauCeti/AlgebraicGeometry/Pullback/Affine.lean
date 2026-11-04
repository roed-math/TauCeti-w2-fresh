/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Affine opens of fibre products

Over a separated base `S`, a fibre product of affine schemes is affine, since a morphism from an
affine scheme to `S` is affine. So in a fibre product `P = X ×_S Y` over a separated `S`, the open
`U ×_S V` cut out by the preimages of affine opens `U` of `X` and `V` of `Y` is affine. Mathlib
proves the weaker statement that it is quasi-compact when `U` and `V` lie over an affine open of
a general base (`AlgebraicGeometry.IsAffineOpen.isCompact_pullback_inf`).

## Main results

* `AlgebraicGeometry.IsAffineOpen.preimage_inf_preimage_of_isPullback`: over a separated base, the
  preimages in a fibre product of affine opens of the factors meet in an affine open.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- Over a separated base `S`, the open `U ×_S V` of a fibre product `P = X ×_S Y`, cut out by the
preimages of affine opens `U` of `X` and `V` of `Y`, is affine: it is the image of the scheme
`U ×_S V` under an open immersion, and `U ×_S V` is affine because `U ⟶ S` is an affine morphism. -/
theorem IsAffineOpen.preimage_inf_preimage_of_isPullback {X Y S P : Scheme.{u}} [S.IsSeparated]
    {f : X ⟶ S} {g : Y ⟶ S} {q₁ : P ⟶ X} {q₂ : P ⟶ Y}
    (h : IsPullback q₁ q₂ f g) {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens}
    (hV : IsAffineOpen V) : IsAffineOpen (q₁ ⁻¹ᵁ U ⊓ q₂ ⁻¹ᵁ V) := by
  have : IsAffine U := hU
  have : IsAffine V := hV
  have : IsAffineHom (U.ι ≫ f) := IsAffineHom.of_comp _ (terminal.from S)
  have : IsAffine (pullback (U.ι ≫ f) (V.ι ≫ g)) := isAffine_of_isAffineHom (pullback.snd _ _)
  let p := pullback.map (U.ι ≫ f) (V.ι ≫ g) f g U.ι V.ι (𝟙 S) (by simp) (by simp)
  have hp : IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
    convert isAffineOpen_opensRange p
    ext1
    simp [p, Scheme.Pullback.range_map]
  -- Preimages under `h.isoPullback.hom ≫ pullback.fst f g = q₁` compose by definition.
  convert hp.preimage h.isoPullback.hom using 1
  rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_snd]

end AlgebraicGeometry
