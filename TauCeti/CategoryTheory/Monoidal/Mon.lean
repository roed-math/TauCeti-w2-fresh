/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import TauCeti.CategoryTheory.Monoidal.Functor

/-!
# Monoid objects

This file provides general-purpose facts about monoid objects, their monomorphisms, and their
commutativity. It also compares candidate unit and multiplication morphisms with monoid structures
after a functor: `Functor.map_one_mul`, `Functor.map_mul_one` and `Functor.map_mul_assoc` reflect
the axioms, while `Functor.monObjObjOfMap` constructs the image structure following Mathlib's
`Functor.monObjObj`. `NatTrans.isMonHom_app` compares structures induced by the same data.

## Main declarations

* `CategoryTheory.Mon.mono_of_mono_hom`: monicity of an underlying morphism implies monicity of
  the morphism of monoid objects.
* `CategoryTheory.Mon.mono_of_mono_left`: the corresponding reflection for monoid objects in a
  slice category.
* `TauCeti.isCommMonObj_of_grp_iso`: commutativity of a group object is preserved by isomorphism.
* `TauCeti.isCommMonObj_of_mono`: a monoid subobject of a commutative monoid object is commutative.
* `TauCeti.monObj_eq_of_mono`: a monomorphism admits at most one compatible monoid structure.
* `TauCeti.commMon_eqToHom_hom_hom`: the underlying morphism of an `eqToHom` between commutative
  monoid objects is an `eqToHom`.
* `CategoryTheory.MonObj.isMonHom_one`: the unit of a monoid object is a monoid homomorphism
  from the trivial monoid on the tensor unit.
* `CategoryTheory.MonObj.isMonHom_mul`: the multiplication of a commutative monoid object is a
  monoid homomorphism.
* `CategoryTheory.MonObj.tensorHom_whisker_one_comp_mul`: a monoid homomorphism out of `M ⊗ N`
  is the product of its restrictions along `m ↦ m ⊗ 1` and `n ↦ 1 ⊗ n`.
* `CategoryTheory.MonObj.braiding_inv_whiskerRight_mul`: in a commutative monoid object, a
  scalar `f a` may multiply on either side.
* `CategoryTheory.Adjunction.isMonHom_homEquiv_iff`: along a monoidal adjunction `F ⊣ G`, the
  transpose `M ⟶ G N` of a morphism `F M ⟶ N` is a monoid homomorphism exactly when the
  morphism is compatible with the unit and multiplication of `M` transported by the oplax
  structure of `F`. This holds without the oplax structure of `F` being invertible.
-/

public section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Mon

universe u v

/-- A morphism of monoid objects is monic if its underlying morphism is monic. -/
instance (priority := 900) mono_of_mono_hom {C : Type u} [Category.{v} C]
    [MonoidalCategory C] {M N : Mon C} (f : M ⟶ N) [hf : Mono f.hom] : Mono f :=
  -- The forgetful functor maps `f` to `f.hom` by definition.
  (Mon.forget C).mono_of_mono_map hf

/-- A morphism of monoid objects over a base is monic if its underlying morphism is monic. -/
instance (priority := 900) mono_of_mono_left {C : Type u} [Category.{v} C] {X : C}
    [MonoidalCategory (Over X)] {M N : Mon (Over X)} (f : M ⟶ N)
    [Mono f.hom.left] : Mono f := by
  have := Over.mono_of_mono_left f.hom
  exact mono_of_mono_hom f

end CategoryTheory.Mon

namespace TauCeti

universe u v

/-- A monomorphism into a monoid object admits at most one compatible monoid structure. -/
theorem monObj_eq_of_mono
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {H G : C} [MonObj G] (i : H ⟶ G) [Mono i] (a b : MonObj H)
    (ha : @IsMonHom _ _ _ H G a inferInstance i)
    (hb : @IsMonHom _ _ _ H G b inferInstance i) : a = b := by
  apply MonObj.ext
  apply (cancel_mono i).1
  exact ha.mul_hom.trans hb.mul_hom.symm

/-- Commutativity of a group object is preserved under isomorphism. -/
theorem isCommMonObj_of_grp_iso
    {C : Type u} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {G H : Grp C} (e : G ≅ H) (hG : IsCommMonObj G.X) : IsCommMonObj H.X := by
  let _ := hG
  constructor
  apply (cancel_mono e.inv.hom.hom).1
  simp only [Category.assoc, IsMonHom.mul_hom]
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality]
  simp only [Category.assoc, IsCommMonObj.mul_comm]

/-- A subobject of a commutative monoid object is commutative whenever its inclusion is a
homomorphism. -/
theorem isCommMonObj_of_mono
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {A B : C} [MonObj A] [MonObj B] [IsCommMonObj B]
    (i : A ⟶ B) [Mono i] [IsMonHom i] : IsCommMonObj A where
  mul_comm := by
    apply (cancel_mono i).1
    simp [IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc]

/-- The morphism of underlying objects of an `eqToHom` between commutative monoid objects is an
`eqToHom`. -/
theorem commMon_eqToHom_hom_hom
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {A B : CommMon C} (h : A = B) (h' : A.X = B.X) :
    (eqToHom h).hom.hom = eqToHom h' := by
  subst h
  rw [eqToHom_refl, eqToHom_refl, CommMon.id_hom]

end TauCeti

namespace CategoryTheory.MonObj

open MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (M : C) [MonObj M]

/-- The unit `𝟙_ C ⟶ M` of a monoid object is a monoid homomorphism, for the trivial monoid
structure on the tensor unit. -/
instance isMonHom_one : IsMonHom η[M] where
  mul_hom := by
    rw [MonObj.mul_def, tensorHom_def', Category.assoc, one_mul, leftUnitor_naturality]

/-- The multiplication `M ⊗ M ⟶ M` of a commutative monoid object is a monoid homomorphism. -/
instance isMonHom_mul [BraidedCategory C] [IsCommMonObj M] : IsMonHom μ[M] where
  one_hom := by
    have h := IsMonHom.mul_hom η[M]
    simp only [MonObj.mul_def] at h
    rw [tensorObj.one_def, Category.assoc, ← h, Iso.inv_hom_id_assoc]
  mul_hom := by
    rw [tensorObj.mul_def, Category.assoc, mul_mul_mul_comm]

section TensorHom

variable {M N T : C} [MonObj T]

/-- Multiplying `f m` by `g 1` gives `f m`, for a monoid homomorphism `g`. -/
@[reassoc]
theorem whiskerLeft_one_tensorHom_mul [MonObj N] (f : M ⟶ T) (g : N ⟶ T) [IsMonHom g] :
    M ◁ η[N] ≫ (f ⊗ₘ g) ≫ μ[T] = (ρ_ M).hom ≫ f := by
  simp only [tensorHom_def', Category.assoc, ← whiskerLeft_comp_assoc, IsMonHom.one_hom]
  rw [whisker_exchange_assoc]
  simp

/-- Multiplying `f 1` by `g n` gives `g n`, for a monoid homomorphism `f`. -/
@[reassoc]
theorem whiskerRight_one_tensorHom_mul [MonObj M] (f : M ⟶ T) (g : N ⟶ T) [IsMonHom f] :
    η[M] ▷ N ≫ (f ⊗ₘ g) ≫ μ[T] = (λ_ N).hom ≫ g := by
  simp only [tensorHom_def, Category.assoc, ← comp_whiskerRight_assoc, IsMonHom.one_hom]
  rw [← whisker_exchange_assoc]
  simp

/-- In `M ⊗ N`, the product of `m ⊗ 1` and `1 ⊗ n` is `m ⊗ n`. -/
@[reassoc]
theorem whiskerLeft_one_tensorHom_whiskerRight_one_mul [BraidedCategory C] [MonObj M]
    [MonObj N] : (M ◁ η[N] ⊗ₘ η[M] ▷ N) ≫ μ[M ⊗ N] = (ρ_ M).hom ⊗ₘ (λ_ N).hom := by
  rw [tensorObj.mul_def, ← id_tensorHom, ← tensorHom_id, tensorμ_natural_assoc]
  simp only [tensorHom_comp_tensorHom, id_tensorHom, tensorHom_id, mul_one, one_mul, tensorμ,
    braiding_tensorUnit_left]
  monoidal

/-- A monoid homomorphism `h` out of `M ⊗ N` is the product of `m ↦ h (m ⊗ 1)` and
`n ↦ h (1 ⊗ n)`. -/
theorem tensorHom_whisker_one_comp_mul [BraidedCategory C] [MonObj M] [MonObj N]
    (h : M ⊗ N ⟶ T) [IsMonHom h] :
    ((((ρ_ M).inv ≫ M ◁ η[N]) ≫ h) ⊗ₘ (((λ_ N).inv ≫ η[M] ▷ N) ≫ h)) ≫ μ[T] = h := by
  rw [← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom, Category.assoc, Category.assoc,
    ← IsMonHom.mul_hom, whiskerLeft_one_tensorHom_whiskerRight_one_mul_assoc]
  simp

/-- Multiplying by `f a` on the left or on the right agrees in a commutative monoid object. -/
theorem braiding_inv_whiskerRight_mul [BraidedCategory C] {A B : C} [MonObj B] [IsCommMonObj B]
    (f : A ⟶ B) : (β_ A B).inv ≫ f ▷ B ≫ μ = B ◁ f ≫ μ := by
  rw [← BraidedCategory.braiding_inv_naturality_right_assoc, IsCommMonObj.mul_comm']

end TensorHom

end CategoryTheory.MonObj

namespace CategoryTheory.Adjunction

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped Obj

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.OplaxMonoidal] [G.LaxMonoidal]
  [adj.IsMonoidal]

/-- Along a monoidal adjunction `F ⊣ G`, the transpose `M ⟶ G N` of a morphism `φ : F M ⟶ N`
is a monoid homomorphism, for the monoid structure on `G N` induced by the lax monoidal functor
`G`, exactly when `φ` carries the image under `F` of the unit and the multiplication of `M` to
the unit and the multiplication of `N`, through the oplax comparisons of `F`. -/
theorem isMonHom_homEquiv_iff {M : C} {N : D} [MonObj M] [MonObj N] (φ : F.obj M ⟶ N) :
    IsMonHom (adj.homEquiv _ _ φ) ↔
      F.map η[M] ≫ φ = Functor.OplaxMonoidal.η F ≫ η[N] ∧
        F.map μ[M] ≫ φ = δ F M M ≫ (φ ⊗ₘ φ) ≫ μ[N] := by
  rw [← (adj.homEquiv _ _).injective.eq_iff, ← (adj.homEquiv _ _).injective.eq_iff,
    homEquiv_η_comp, homEquiv_δ_comp_tensorHom_comp, homEquiv_naturality_left,
    homEquiv_naturality_left]
  exact ⟨fun h ↦ ⟨h.one_hom, h.mul_hom⟩, fun h ↦ ⟨h.1, h.2⟩⟩

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

open MonoidalCategory MonObj OplaxMonoidal LaxMonoidal

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section Monoidal

variable [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)

section OplaxMonoidal

variable [F.OplaxMonoidal] {X : C} [MonObj (F.obj X)] {one : 𝟙_ C ⟶ X} {mul : X ⊗ X ⟶ X}

/-- If `one` and `mul` lift the unit and the multiplication of `F.obj X`, then the left unit
axiom holds for them after applying `F`. -/
theorem map_one_mul (h_one : F.map one = OplaxMonoidal.η F ≫ η[F.obj X])
    (h_mul : F.map mul = δ F X X ≫ μ[F.obj X]) :
    F.map (one ▷ X ≫ mul) = F.map (λ_ X).hom := by
  simp [h_one, h_mul, ← δ_natural_left_assoc]

/-- If `one` and `mul` lift the unit and the multiplication of `F.obj X`, then the right unit
axiom holds for them after applying `F`. -/
theorem map_mul_one (h_one : F.map one = OplaxMonoidal.η F ≫ η[F.obj X])
    (h_mul : F.map mul = δ F X X ≫ μ[F.obj X]) :
    F.map (X ◁ one ≫ mul) = F.map (ρ_ X).hom := by
  simp [h_one, h_mul, ← δ_natural_right_assoc]

/-- If `mul` lifts the multiplication of `F.obj X`, then the associativity axiom holds for it
after applying `F`. -/
theorem map_mul_assoc (h_mul : F.map mul = δ F X X ≫ μ[F.obj X]) :
    F.map (mul ▷ X ≫ mul) = F.map ((α_ X X X).hom ≫ X ◁ mul ≫ mul) := by
  simp [h_mul, ← δ_natural_left_assoc, ← δ_natural_right_assoc]

end OplaxMonoidal

variable [F.LaxMonoidal] {X : C} (one : 𝟙_ C ⟶ X) (mul : X ⊗ X ⟶ X)

/-- The monoid object structure on `F.obj X` given by the images `ε ≫ F.map one` and
`μ ≫ F.map mul` of candidate structure morphisms on `X` which satisfy the monoid axioms after
applying `F`. -/
@[simps]
abbrev monObjObjOfMap (h_one_mul : F.map (one ▷ X ≫ mul) = F.map (λ_ X).hom)
    (h_mul_one : F.map (X ◁ one ≫ mul) = F.map (ρ_ X).hom)
    (h_mul_assoc : F.map (mul ▷ X ≫ mul) = F.map ((α_ X X X).hom ≫ X ◁ mul ≫ mul)) :
    MonObj (F.obj X) where
  one := ε F ≫ F.map one
  mul := LaxMonoidal.μ F X X ≫ F.map mul
  one_mul := by
    simp [← F.map_comp, h_one_mul]
  mul_one := by
    simp [← F.map_comp, h_mul_one]
  mul_assoc := by
    simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc]
    rw [← F.map_comp, h_mul_assoc]
    simp

end Monoidal

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

open MonoidalCategory MonObj Functor.LaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] (τ : F ⟶ G) [τ.IsMonoidal] {X : C}
  [hF : MonObj (F.obj X)] [hG : MonObj (G.obj X)] {one : 𝟙_ C ⟶ X} {mul : X ⊗ X ⟶ X}

/-- A monoidal natural transformation `τ : F ⟶ G` is a homomorphism of monoid objects
`F.obj X ⟶ G.obj X` when the units and the multiplications of both are the images of the same
morphisms `one` and `mul` on `X`. -/
theorem isMonHom_app (hF_one : η[F.obj X] = ε F ≫ F.map one)
    (hF_mul : μ[F.obj X] = «μ» F X X ≫ F.map mul) (hG_one : η[G.obj X] = ε G ≫ G.map one)
    (hG_mul : μ[G.obj X] = «μ» G X X ≫ G.map mul) : IsMonHom (τ.app X) where
  one_hom := by rw [hF_one, hG_one, Category.assoc, τ.naturality, IsMonoidal.unit_assoc]
  mul_hom := by rw [hF_mul, hG_mul, Category.assoc, τ.naturality, IsMonoidal.tensor_assoc]

end CategoryTheory.NatTrans
