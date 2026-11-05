/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization

/-!
# Local rings of the generic fibre

Let `f : X ⟶ Y` be a morphism to an integral scheme `Y` with generic point `η`. The generic fibre
`X_η = f.fiber η` has the local rings of `X`: the stalk maps of `f.fiberι η : X_η ⟶ X` are
bijective.

The morphism `Spec 𝒪_{X, x} ⟶ X` is flat, being a localization over an affine open
(`TauCeti.AlgebraicGeometry.flat_fromSpecStalk`), and at the generic point of an integral scheme
the residue map `𝒪_{Y, η} ⟶ κ(η)` is an isomorphism, so `Spec κ(η) ⟶ Y` is flat
(`TauCeti.AlgebraicGeometry.flat_fromSpecResidueField_genericPoint`). Hence its base change
`f.fiberι η` is flat, and its stalk maps are flat local homomorphisms of local rings, hence
injective. They are surjective since `f.fiberι η` is a preimmersion.

## Main results

* `TauCeti.AlgebraicGeometry.flat_fromSpecStalk`: `Spec 𝒪_{X, x} ⟶ X` is flat.
* `TauCeti.AlgebraicGeometry.flat_fromSpecResidueField_genericPoint`: the inclusion
  `Spec κ(η) ⟶ Y` of the generic point of an integral scheme is flat.
* `TauCeti.AlgebraicGeometry.bijective_stalkMap_fiberι_genericPoint`: the generic fibre has the
  local rings of the source.
* `TauCeti.AlgebraicGeometry.coheight_fiberι_genericPoint`: hence its points have the codimension
  of their images.
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry

/-- The canonical morphism `Spec 𝒪_{X, x} ⟶ X` is flat: over an affine open `U ∋ x` it is the
spectrum of the localization `Γ(X, U) ⟶ 𝒪_{X, x}`, followed by the open immersion of `U`. -/
instance flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  change Flat (Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec)
  have : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    rw [Flat.SpecMap_iff]
    let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact IsLocalization.flat _ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  infer_instance

/-- The inclusion `Spec κ(η) ⟶ Y` of the generic point of an integral scheme is flat: the residue
map from the function field `𝒪_{Y, η}` is an isomorphism, followed by the flat
`Spec 𝒪_{Y, η} ⟶ Y`. -/
instance flat_fromSpecResidueField_genericPoint (Y : Scheme.{u}) [IsIntegral Y] :
    Flat (Y.fromSpecResidueField (genericPoint Y)) := by
  have : IsIso (Y.residue (genericPoint Y)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(Y.residue (genericPoint Y)).hom.injective, Y.residue_surjective _⟩
  rw [Scheme.fromSpecResidueField]
  infer_instance

/-- **The generic fibre has the local rings of the source.** For a morphism `f : X ⟶ Y` to an
integral scheme with generic point `η`, the stalk maps of `f.fiberι η : f.fiber η ⟶ X` are
bijective: `f.fiberι η` is flat, as a base change of `Spec κ(η) ⟶ Y`, so its stalk maps are flat
local homomorphisms of local rings, hence injective, and it is a preimmersion. -/
theorem bijective_stalkMap_fiberι_genericPoint {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y)
    (x : f.fiber (genericPoint Y)) :
    Function.Bijective ((f.fiberι (genericPoint Y)).stalkMap x) := by
  refine ⟨?_, (f.fiberι (genericPoint Y)).stalkMap_surjective x⟩
  have : Flat (f.fiberι (genericPoint Y)) :=
    inferInstanceAs (Flat (Limits.pullback.fst f (Y.fromSpecResidueField (genericPoint Y))))
  let _ := ((f.fiberι (genericPoint Y)).stalkMap x).hom.toAlgebra
  have : Module.Flat _ _ := Flat.stalkMap (f.fiberι (genericPoint Y)) x
  have : IsLocalHom (algebraMap (X.presheaf.stalk (f.fiberι (genericPoint Y) x))
      ((f.fiber (genericPoint Y)).presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom ((f.fiberι (genericPoint Y)).stalkMap x).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := X.presheaf.stalk (f.fiberι (genericPoint Y) x))
    (B := (f.fiber (genericPoint Y)).presheaf.stalk x)
  exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (f.fiberι (genericPoint Y) x))
    ((f.fiber (genericPoint Y)).presheaf.stalk x)

/-- A point of the generic fibre has the codimension of its image: the two local rings are
isomorphic (`TauCeti.AlgebraicGeometry.bijective_stalkMap_fiberι_genericPoint`). -/
theorem coheight_fiberι_genericPoint {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y)
    (x : f.fiber (genericPoint Y)) :
    Order.coheight (f.fiberι (genericPoint Y) x) = Order.coheight x := by
  have h := ringKrullDim_eq_of_ringEquiv
    (RingEquiv.ofBijective _ (bijective_stalkMap_fiberι_genericPoint f x))
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

end TauCeti.AlgebraicGeometry
