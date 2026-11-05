/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.Lookahead.ChowProperPushforward.Stubs

/-!
# Orders of vanishing along isomorphisms of local rings

Let `g : X ⟶ Y` be a dominant morphism of locally Noetherian integral schemes and `x ∈ X` a point
at which the stalk map `𝒪_{Y, g x} ⟶ 𝒪_{X, x}` is bijective. Then the order of vanishing of a
rational function `r` on `Y` at `g x` is the order of vanishing of its pullback `g^* r` at `x`
(`TauCeti.AlgebraicGeometry.ord_functionFieldMap_of_bijective`). This applies to the inclusion of
the generic fibre of a morphism, whose stalk maps are bijective.

The ring-theoretic input is that `Ring.ordFrac` is transported along an isomorphism of
one-dimensional Noetherian domains, compatibly with a homomorphism of their fraction fields
(`TauCeti.Ring.ordFrac_map_of_ringEquiv`).

## Main results

* `TauCeti.Ring.ordFrac_map_of_ringEquiv`: the order of vanishing of a fraction is invariant under
  an isomorphism of rings extended to their fraction fields.
* `TauCeti.AlgebraicGeometry.ord_functionFieldMap_of_bijective`: `ord_x (g^* r) = ord_{g x} r` when
  the stalk map of `g` at `x` is bijective.
-/

public section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace TauCeti

namespace Ring

variable {R R' K K' : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [Ring.KrullDimLE 1 R'] [Field K] [Field K']
  [Algebra R K] [IsFractionRing R K] [Algebra R' K'] [IsFractionRing R' K']

/-- **Orders of vanishing are invariant under isomorphisms.** Let `σ : R ≃+* R'` be an
isomorphism of Noetherian domains of dimension at most one, and `τ : K →+* K'` a homomorphism of
their fraction fields extending it. Then `ordFrac_{R'} (τ x) = ordFrac_R x` for every `x ∈ K`. -/
theorem ordFrac_map_of_ringEquiv (σ : R ≃+* R') (τ : K →+* K')
    (h : ∀ a, τ (algebraMap R K a) = algebraMap R' K' (σ a)) (x : K) :
    Ring.ordFrac R' (τ x) = Ring.ordFrac R x := by
  have key (a : R) :
      Ring.ordFrac R' (τ (algebraMap R K a)) = Ring.ordFrac R (algebraMap R K a) := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    have ha' : σ a ≠ 0 := (map_ne_zero_iff σ σ.injective).mpr ha
    rw [h, Ring.ordFrac_eq_ord R' ha', Ring.ordFrac_eq_ord R ha,
      Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero ha'),
      Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero ha), ord_ringEquiv]
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  rw [map_div₀, map_div₀, map_div₀, key, key]

end Ring

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
  [IsLocallyNoetherian Y]

/-- **Orders of vanishing along an isomorphism of local rings.** Let `g : X ⟶ Y` be a dominant
morphism of locally Noetherian integral schemes whose stalk map at `x` is bijective. Then for every
rational function `r` on `Y`, `ord_x (g^* r) = ord_{g x} r`. -/
theorem ord_functionFieldMap_of_bijective (g : X ⟶ Y) [IsDominant g] {x : X}
    (hx : Function.Bijective (g.stalkMap x)) (r : Y.functionField) :
    X.ord (g.functionFieldMap r) x = Y.ord r (g x) := by
  have hc : coheight (g x) = coheight x := by
    have h := ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hx)
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  by_cases h1 : coheight x = 1
  swap
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one h1,
      Scheme.ord_eq_zero_of_coheight_neq_one (hc ▸ h1)]
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one h1,
    Scheme.ord_eq_ordHom_of_coheight_eq_one (hc.trans h1)]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le h1.le
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk (g x)) := krullDimLE_of_coheight_le (hc.trans h1).le
  congr 2
  refine Ring.ordFrac_map_of_ringEquiv (RingEquiv.ofBijective _ hx) g.functionFieldMap.hom
    (fun a ↦ ?_) r
  -- Both sides are `a` specialized to the image of the generic point, then pulled back.
  simp only [RingHom.algebraMap_toAlgebra, RingEquiv.ofBijective_apply,
    Scheme.Hom.functionFieldMap_def, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]
  exact congrArg _ (TopCat.Presheaf.stalkSpecializes_comp_apply _ _ _ a)

end AlgebraicGeometry

end TauCeti
