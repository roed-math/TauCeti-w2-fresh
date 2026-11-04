/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import TauCeti.AlgebraicGeometry.Descent.AffineMorphism
import TauCeti.AlgebraicGeometry.Descent.MorphismProperty
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Effective descent of closed subschemes along affine faithfully flat morphisms

Let `f : X ⟶ Y` be an affine, flat and surjective morphism of schemes, for instance a finite étale
surjection. An ideal sheaf `J` on `X` whose inverse images along the two projections
`X ×_Y X ⇉ X` agree is the inverse image of an ideal sheaf on `Y`
(`AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_comap_fst_eq_comap_snd`). This is the
existence half of faithfully flat descent for closed subschemes; for `f` also locally of finite
presentation the descended ideal sheaf is unique by
`AlgebraicGeometry.Scheme.IdealSheafData.comap_injective_of_flat_of_surjective`.

The closed subscheme `Z` of `J` carries a descent datum relative to `f`
(`TauCeti.DescentDatum.ofIdealSheafData`): the action `X ×_Y Z ⟶ Z` is the first projection,
which lands in `Z` because the two inverse images of `J` agree. As `Z ⟶ X` is a monomorphism, the
axioms of a descent datum hold automatically. The descended scheme of this datum
(`TauCeti.DescentDatum.descended`) is a closed subscheme of `Y` whose base change along `f` is
`Z`, and its ideal sheaf is the required descent of `J`.

## Main definitions

* `TauCeti.DescentDatum.ofIdealSheafData`: the descent datum on the closed subscheme of an ideal
  sheaf with equal inverse images along the two projections.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_comap_fst_eq_comap_snd`: effective
  descent of ideal sheaves along an affine, flat and surjective morphism.
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_isPullback`: the same, for the two
  projections of any fibre square presenting `X ×_Y X`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII,
  Corollaire 1.9.
* The Stacks Project, Tag 023Y (descent of closed subschemes along fpqc coverings).
-/

public section

open CategoryTheory Limits AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The first projection `X ×_Y Z ⟶ X` from the base change of the closed subscheme `Z` of `J`
lands in `Z` when the inverse images of `J` along the two projections `X ×_Y X ⇉ X` agree. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι_le_ker_pullback_fst
    (J : X.IdealSheafData) (hJ : J.comap (pullback.fst f f) = J.comap (pullback.snd f f)) :
    J.subschemeι.ker ≤ (pullback.fst f (J.subschemeι ≫ f)).ker := by
  -- The first projection factors through `X ×_Y X`.
  let k : pullback f (J.subschemeι ≫ f) ⟶ pullback f f :=
    pullback.map _ _ _ _ (𝟙 X) J.subschemeι (𝟙 Y) (by simp) (by simp)
  have hk₁ : k ≫ pullback.fst f f = pullback.fst f (J.subschemeι ≫ f) := by simp [k]
  have hk₂ : k ≫ pullback.snd f f = pullback.snd f (J.subschemeι ≫ f) ≫ J.subschemeι := by
    simp [k]
  -- `k` lands in the closed subscheme of `J.comap (pullback.snd f f)`.
  have hsnd : J.comap (pullback.snd f f) ≤ k.ker := by
    rw [← le_map_iff_comap_le, map_ker, hk₂]
    exact J.ker_subschemeι.symm.le.trans (Scheme.Hom.le_ker_comp _ _)
  rw [ker_subschemeι, ← hk₁, ← map_ker]
  exact (le_map_comap _ _).trans (map_mono _ (hJ.le.trans hsnd))

/-- **The descent datum on a closed subscheme.** Let `J` be an ideal sheaf on `X` whose inverse
images along the two projections `X ×_Y X ⇉ X` agree. The closed subscheme `Z` of `J` carries the
descent datum relative to `f : X ⟶ Y` whose action `X ×_Y Z ⟶ Z` is the first projection. -/
noncomputable def DescentDatum.ofIdealSheafData (J : X.IdealSheafData)
    (hJ : J.comap (pullback.fst f f) = J.comap (pullback.snd f f)) :
    DescentDatum f (Over.mk J.subschemeι) where
  act := IsClosedImmersion.lift J.subschemeι (pullback.fst f (J.subschemeι ≫ f))
    (J.ker_subschemeι_le_ker_pullback_fst f hJ)
  act_hom := IsClosedImmersion.lift_fac _ _ _
  lift_act := by
    rw [← cancel_mono J.subschemeι]
    simp
  act_assoc := by
    rw [← cancel_mono J.subschemeι]
    simp

variable [IsAffineHom f] [Flat f] [Surjective f]

/-- **Effective descent of closed subschemes along affine faithfully flat morphisms.** Let
`f : X ⟶ Y` be affine, flat and surjective. An ideal sheaf `J` on `X` whose inverse images along
the two projections `X ×_Y X ⇉ X` agree is the inverse image along `f` of an ideal sheaf on `Y`. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_comap_fst_eq_comap_snd
    (J : X.IdealSheafData) (hJ : J.comap (pullback.fst f f) = J.comap (pullback.snd f f)) :
    ∃ I : Y.IdealSheafData, I.comap f = J := by
  let D := DescentDatum.ofIdealSheafData f J hJ
  have : IsAffineHom (Over.mk J.subschemeι).hom := inferInstanceAs (IsAffineHom J.subschemeι)
  have : IsClosedImmersion (Over.mk J.subschemeι).hom :=
    inferInstanceAs (IsClosedImmersion J.subschemeι)
  refine ⟨D.descended.hom.ker, ?_⟩
  rw [← ker_eq_comap_of_isPullback D.descended.hom D.isPullback_toDescended.flip]
  exact J.ker_subschemeι

/-- **Effective descent of closed subschemes, for any fibre square.** Let `f : X ⟶ Y` be affine,
flat and surjective, and let `p₁, p₂ : P ⟶ X` exhibit `P` as the fibre product `X ×_Y X`. An ideal
sheaf `J` on `X` with `J.comap p₁ = J.comap p₂` is the inverse image along `f` of an ideal sheaf
on `Y`. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_isPullback
    {P : Scheme.{u}} {p₁ p₂ : P ⟶ X} (h : IsPullback p₁ p₂ f f) (J : X.IdealSheafData)
    (hJ : J.comap p₁ = J.comap p₂) : ∃ I : Y.IdealSheafData, I.comap f = J :=
  J.exists_comap_eq_of_comap_fst_eq_comap_snd f (by
    rw [← h.isoPullback_inv_fst, ← h.isoPullback_inv_snd, comap_comp, comap_comp, hJ])

end TauCeti
