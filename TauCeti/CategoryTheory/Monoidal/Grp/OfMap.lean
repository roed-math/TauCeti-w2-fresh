/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Mon

/-!
# Monoid and group axioms after a monoidal functor

Let `F : C ⥤ D` be a monoidal functor and let `X : C` carry candidate structure morphisms
`one : 𝟙_ C ⟶ X`, `mul : X ⊗ X ⟶ X` (and `inv : X ⟶ X`), not assumed to satisfy any axioms. This
file compares these data with group object structures on `F.obj X`, in both directions. The
monoid-only API lives in the imported `TauCeti.CategoryTheory.Monoidal.Mon`.
`TauCeti.groupLawAxiomPairs` collects the five group axioms as parallel arrow pairs for uniform
descent of their equalities.

* If the images of the data under `F` are the structure morphisms of a monoid (group) object
  `F.obj X`, then each axiom holds for the data on `X` after applying `F`
  (`CategoryTheory.Functor.map_one_mul` and its companions).
* Conversely, if each axiom holds for the data on `X` after applying `F`, the images of the data
  make `F.obj X` a monoid (group) object (`CategoryTheory.Functor.monObjObjOfMap`,
  `CategoryTheory.Functor.grpObjObjOfMap`). When the axioms already hold on `X` this is Mathlib's
  `CategoryTheory.Functor.monObjObj` (`CategoryTheory.Functor.grpObjObj`), whose construction and
  proofs these follow.
* A monoidal natural transformation `τ : F ⟶ G` is a homomorphism `F.obj X ⟶ G.obj X` between
  monoid objects whose structure morphisms are the images of the same data on `X`
  (`CategoryTheory.NatTrans.isMonHom_app`).

The first statement lets a faithful functor reflect the axioms
(`CategoryTheory.Functor.monObjOfFaithful`). Together, the statements move monoid and group
objects along functors which are not faithful, such as the base change functors from a member of a
cofiltered system of schemes to its limit: a group law over the limit is spread out to a member by
lifting its structure morphisms and then the equalities expressing its axioms.
-/

public section

namespace TauCeti

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

/-- The five group axioms as pairs of parallel arrows with common target `X`: left and right
unit, associativity, and left and right inverse. This presents the axioms as one finite family
so that equality descent applies uniformly despite their different source objects. -/
abbrev groupLawAxiomPairs {C : Type*} [Category* C] [CartesianMonoidalCategory C] (X : C)
    (one : 𝟙_ C ⟶ X) (mul : X ⊗ X ⟶ X) (inv : X ⟶ X) :
    Fin 5 → Σ A : C, (A ⟶ X) × (A ⟶ X) :=
  ![⟨_, one ▷ X ≫ mul, (λ_ X).hom⟩,
    ⟨_, X ◁ one ≫ mul, (ρ_ X).hom⟩,
    ⟨_, mul ▷ X ≫ mul, (α_ X X X).hom ≫ X ◁ mul ≫ mul⟩,
    ⟨_, lift inv (𝟙 X) ≫ mul, toUnit X ≫ one⟩,
    ⟨_, lift (𝟙 X) inv ≫ mul, toUnit X ≫ one⟩]

end TauCeti

namespace CategoryTheory.Functor

open MonoidalCategory MonObj OplaxMonoidal LaxMonoidal CartesianMonoidalCategory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section Cartesian

variable [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] (F : C ⥤ D)

section OplaxMonoidal

variable [F.OplaxMonoidal] {X : C} [GrpObj (F.obj X)] {one : 𝟙_ C ⟶ X} {mul : X ⊗ X ⟶ X}
  {inv : X ⟶ X}

/-- If `one`, `mul` and `inv` lift the structure morphisms of the group object `F.obj X`, then
the left inverse axiom holds for them after applying `F`. -/
theorem map_left_inv (h_one : F.map one = OplaxMonoidal.η F ≫ η[F.obj X])
    (h_mul : F.map mul = δ F X X ≫ μ[F.obj X]) (h_inv : F.map inv = ι[F.obj X]) :
    F.map (lift inv (𝟙 X) ≫ mul) = F.map (toUnit X ≫ one) := by
  simp [h_one, h_mul, h_inv, OplaxMonoidal.η_of_cartesianMonoidalCategory]

/-- If `one`, `mul` and `inv` lift the structure morphisms of the group object `F.obj X`, then
the right inverse axiom holds for them after applying `F`. -/
theorem map_right_inv (h_one : F.map one = OplaxMonoidal.η F ≫ η[F.obj X])
    (h_mul : F.map mul = δ F X X ≫ μ[F.obj X]) (h_inv : F.map inv = ι[F.obj X]) :
    F.map (lift (𝟙 X) inv ≫ mul) = F.map (toUnit X ≫ one) := by
  simp [h_one, h_mul, h_inv, OplaxMonoidal.η_of_cartesianMonoidalCategory]

end OplaxMonoidal

variable [F.Monoidal] {X : C} (one : 𝟙_ C ⟶ X) (mul : X ⊗ X ⟶ X) (inv : X ⟶ X)

/-- The group object structure on `F.obj X` given by the images of candidate structure morphisms
on `X` which satisfy the group axioms after applying `F`. -/
@[simps]
abbrev grpObjObjOfMap (h_one_mul : F.map (one ▷ X ≫ mul) = F.map (λ_ X).hom)
    (h_mul_one : F.map (X ◁ one ≫ mul) = F.map (ρ_ X).hom)
    (h_mul_assoc : F.map (mul ▷ X ≫ mul) = F.map ((α_ X X X).hom ≫ X ◁ mul ≫ mul))
    (h_left_inv : F.map (lift inv (𝟙 X) ≫ mul) = F.map (toUnit X ≫ one))
    (h_right_inv : F.map (lift (𝟙 X) inv ≫ mul) = F.map (toUnit X ≫ one)) :
    GrpObj (F.obj X) where
  __ := F.monObjObjOfMap one mul h_one_mul h_mul_one h_mul_assoc
  inv := F.map inv
  left_inv := by
    simp [← Functor.map_id, Functor.Monoidal.lift_μ_assoc,
      Functor.Monoidal.toUnit_ε_assoc, ← Functor.map_comp, h_left_inv]
  right_inv := by
    simp [← Functor.map_id, Functor.Monoidal.lift_μ_assoc,
      Functor.Monoidal.toUnit_ε_assoc, ← Functor.map_comp, h_right_inv]

end Cartesian

end CategoryTheory.Functor
