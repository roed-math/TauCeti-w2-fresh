/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.CategoryTheory.Monoidal.Grp.Basic
public import TauCeti.CategoryTheory.Comma.Over.Pullback
public import TauCeti.CategoryTheory.Monoidal.Grp.OfMap

/-!
# Group objects over a base

A morphism of group objects in a slice category is monic when its underlying morphism is monic,
by reflection through the faithful forgetful functors.

For a cone in a category with pullbacks, `CategoryTheory.Limits.Cone.exists_grpObj_of_map_axioms`
transports candidate group structure morphisms from an iterated base change to the direct one.
If their group axioms hold after base change to a later member, and their images at the cone point
already give a compatible group law, the resulting law remains compatible at the cone point.
This is the categorical reconstruction step in spreading out group schemes.
-/

public section

open CategoryTheory Limits MonoidalCategory MonObj CartesianMonoidalCategory
  Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped Obj

namespace CategoryTheory.Limits.Cone

attribute [local instance] Over.cartesianMonoidalCategory

universe v u v' u'

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {I : Type u'} [Category.{v'} I] {D : I ⥤ C}

/-- Let `Y = X ×_{Dᵢ} Dⱼ` carry candidate group structure morphisms, and let its base change to the
cone point carry a group law whose unit and multiplication are their base changes, such that the
identification with the base change of `X` is a homomorphism to a given group law. If the group
axioms hold for the candidates after base change along `h : k ⟶ j`, then their base changes are a
group law on `X ×_{Dᵢ} Dₖ` whose base change to the cone point is the given one. -/
theorem exists_grpObj_of_map_axioms (c : Cone D) {i j k : I} (X : Over (D.obj i))
    [GrpObj ((Over.pullback (c.π.app i)).obj X)] (g : j ⟶ i) (h : k ⟶ j)
    (one : 𝟙_ _ ⟶ (Over.pullback (D.map g)).obj X)
    (mul : (Over.pullback (D.map g)).obj X ⊗ (Over.pullback (D.map g)).obj X ⟶
      (Over.pullback (D.map g)).obj X)
    (inv : (Over.pullback (D.map g)).obj X ⟶ (Over.pullback (D.map g)).obj X)
    [T : GrpObj ((Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X))]
    (h_one : η[(Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X)] =
      ε _ ≫ (Over.pullback (c.π.app j)).map one)
    (h_mul : μ[(Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X)] =
      Functor.LaxMonoidal.μ _ _ _ ≫ (Over.pullback (c.π.app j)).map mul)
    [hT : IsMonHom (M := (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X))
      ((Over.pullbackCompIsoOfEq (c.w g)).hom.app X)]
    (h_axioms : ∀ n,
      (Over.pullback (D.map h)).map
          (TauCeti.groupLawAxiomPairs ((Over.pullback (D.map g)).obj X) one mul inv n).2.1 =
        (Over.pullback (D.map h)).map
          (TauCeti.groupLawAxiomPairs ((Over.pullback (D.map g)).obj X) one mul inv n).2.2) :
    ∃ (_ : GrpObj ((Over.pullback (D.map (h ≫ g))).obj X)),
      IsMonHom (M := (Over.pullback (c.π.app k)).obj ((Over.pullback (D.map (h ≫ g))).obj X))
        ((Over.pullbackCompIsoOfEq (c.w (h ≫ g))).hom.app X) := by
  -- The group law over `Dₖ`, on the iterated base change and transported to the direct one. The
  -- structures are restated on the objects written as images under composite functors, as which
  -- they occur in the sources of the comparison isomorphisms.
  let S : GrpObj ((Over.pullback (D.map h)).obj ((Over.pullback (D.map g)).obj X)) :=
    (Over.pullback (D.map h)).grpObjObjOfMap one mul inv (h_axioms 0) (h_axioms 1) (h_axioms 2)
      (h_axioms 3) (h_axioms 4)
  let S' : GrpObj ((Over.pullback (D.map g) ⋙ Over.pullback (D.map h)).obj X) := S
  let T' : GrpObj ((Over.pullback (D.map g) ⋙ Over.pullback (c.π.app j)).obj X) := T
  let C := Over.pullbackCompIsoOfEq (D.map_comp h g).symm
  let G : GrpObj ((Over.pullback (D.map (h ≫ g))).obj X) := .ofIso (C.app X)
  refine ⟨G, ?_⟩
  rw [Over.pullbackCompIsoOfEq_hom_app_eq (c.w h) (D.map_comp h g).symm (c.w g) (c.w (h ≫ g)) X]
  have : IsMonHom (M := (Over.pullback (D.map (h ≫ g))).obj X)
      (N := (Over.pullback (D.map g) ⋙ Over.pullback (D.map h)).obj X) (C.inv.app X) :=
    inferInstanceAs (IsMonHom (C.app X).inv)
  have : IsMonHom (M := (Over.pullback (D.map g) ⋙ Over.pullback (c.π.app j)).obj X)
      ((Over.pullbackCompIsoOfEq (c.w g)).hom.app X) := hT
  have : IsMonHom (M := (Over.pullback (c.π.app k)).obj
        ((Over.pullback (D.map g) ⋙ Over.pullback (D.map h)).obj X))
      (N := (Over.pullback (D.map g) ⋙ Over.pullback (c.π.app j)).obj X)
      ((Over.pullbackCompIsoOfEq (c.w h)).hom.app ((Over.pullback (D.map g)).obj X)) := by
    refine NatTrans.isMonHom_app (F := Over.pullback (D.map h) ⋙ Over.pullback (c.π.app k))
      (G := Over.pullback (c.π.app j)) (X := (Over.pullback (D.map g)).obj X)
      (hF := Functor.monObjObj (F := Over.pullback (c.π.app k))
        ((Over.pullback (D.map g) ⋙ Over.pullback (D.map h)).obj X)) (hG := T'.toMonObj)
      (one := one) (mul := mul) _ ?_ ?_ h_one h_mul
    · have hS : η[(Over.pullback (D.map h)).obj ((Over.pullback (D.map g)).obj X)] =
          ε _ ≫ (Over.pullback (D.map h)).map one := rfl
      simp [hS]
    · have hS : μ[(Over.pullback (D.map h)).obj ((Over.pullback (D.map g)).obj X)] =
          Functor.LaxMonoidal.μ _ _ _ ≫ (Over.pullback (D.map h)).map mul := rfl
      simp [hS]
  infer_instance

end CategoryTheory.Limits.Cone

namespace CategoryTheory.Grp

/-- A morphism of group objects over a base is monic if its underlying morphism is monic. -/
instance (priority := 900) mono_of_mono_left {C : Type u} [Category.{v} C] {X : C}
    [CartesianMonoidalCategory (Over X)] {G H : Grp (Over X)} (f : G ⟶ H)
    [Mono f.hom.hom.left] : Mono f :=
  -- Forgetting inverses maps `f` to `f.hom` by definition.
  (Grp.forget₂Mon _).mono_of_mono_map (Mon.mono_of_mono_left f.hom)

end CategoryTheory.Grp
