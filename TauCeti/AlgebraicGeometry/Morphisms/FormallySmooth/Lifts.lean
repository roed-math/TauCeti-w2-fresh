/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.Basic

/-!
# Lifts along thickenings

For `f : X ⟶ S`, a morphism `i : T ⟶ T'`, a morphism `g : T ⟶ X` and a morphism `h : T' ⟶ S`
with `g ≫ f = i ≫ h`, the lifts of `g` along `i` over `S` are the morphisms `l : T' ⟶ X` with
`i ≫ l = g` and `l ≫ f = h`, that is, Mathlib's `CommSq.LiftStruct` of the square. Formal
smoothness and formal étaleness say that along affine first-order thickenings there is at least
one, respectively exactly one, lift.

For affine space `𝔸(n; S) ⟶ S` the lifts are described by coordinates: when `i` is a closed
immersion into an affine scheme `T'` and `g ≫ 𝔸(n; S) ↘ S = i ≫ h`, the lifts of `g` form a
torsor under `n → Γ(T', I)`, where `I` is the ideal sheaf of `i`, acting by translation of the
coordinates. This is the affine space case of the torsor of lifts of Stacks, Lemma 37.9.5 (04FJ).

## Main results

* `TauCeti.AlgebraicGeometry.affineSpaceLift_addTorsor`: the lifts into `𝔸(n; S)` form a torsor
  under `n → RingHom.ker i.appTop`, the `n`-tuples of global sections of the ideal sheaf of `i`.
* `TauCeti.AlgebraicGeometry.FormallySmooth.hasLift`: along an affine first-order thickening, a
  square into a formally smooth morphism has a lift.
* `TauCeti.AlgebraicGeometry.FormallyEtale.subsingleton_liftStruct`: along an affine first-order
  thickening, a square into a formally étale morphism has at most one lift.

## References

* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ).
-/

public section

open CategoryTheory AlgebraicGeometry AffineSpace

universe u

namespace TauCeti.AlgebraicGeometry

variable {X S T T' : Scheme.{u}}

/-- Along an affine first-order thickening, a square into a formally smooth morphism has a
lift. -/
instance FormallySmooth.hasLift {f : X ⟶ S} [FormallySmooth f] {i : T ⟶ T'} [IsAffine T']
    [IsFirstOrderThickening i] {g : T ⟶ X} {h : T' ⟶ S} (sq : CommSq g i f h) : sq.HasLift :=
  let ⟨l, hl⟩ := FormallySmooth.exists_lift i g h sq.w
  ⟨⟨⟨l, hl.1, hl.2⟩⟩⟩

/-- Along an affine first-order thickening, a square into a formally étale morphism has at most
one lift. -/
instance FormallyEtale.subsingleton_liftStruct {f : X ⟶ S} [FormallyEtale f] {i : T ⟶ T'}
    [IsAffine T'] [IsFirstOrderThickening i] {g : T ⟶ X} {h : T' ⟶ S} (sq : CommSq g i f h) :
    Subsingleton sq.LiftStruct :=
  ⟨fun l₁ l₂ ↦ CommSq.LiftStruct.ext <| FormallyEtale.hom_ext f i
    (l₁.fac_left.trans l₂.fac_left.symm) (l₁.fac_right.trans l₂.fac_right.symm)⟩

variable {n : Type u} {i : T ⟶ T'} {g : T ⟶ 𝔸(n; S)} {h : T' ⟶ S} {sq : CommSq g i (𝔸(n; S) ↘ S) h}

/-- The coordinates of a lift into `𝔸(n; S)` reduce to those of `g`. -/
theorem affineSpaceLift_appTop_appTop_coord (l : sq.LiftStruct) (j : n) :
    i.appTop (l.l.appTop (coord S j)) = g.appTop (coord S j) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, l.fac_left]

/-- Two lifts into `𝔸(n; S)` with the same coordinates agree. -/
theorem affineSpaceLift_ext {l₁ l₂ : sq.LiftStruct}
    (e : ∀ j, l₁.l.appTop (coord S j) = l₂.l.appTop (coord S j)) : l₁ = l₂ :=
  CommSq.LiftStruct.ext <| hom_ext (by rw [l₁.fac_right, l₂.fac_right]) e

/-- Global sections of the ideal sheaf of `i` act on the lifts into `𝔸(n; S)` by translating
their coordinates. -/
noncomputable instance : VAdd (n → RingHom.ker i.appTop.hom) sq.LiftStruct where
  vadd v l :=
    { l := homOfVector h fun j ↦ v j + l.l.appTop (coord S j)
      fac_left := by
        refine hom_ext (by rw [Category.assoc, homOfVector_over, sq.w]) fun j ↦ ?_
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, homOfVector_appTop_coord, map_add,
          RingHom.mem_ker.1 (v j).2, zero_add, affineSpaceLift_appTop_appTop_coord]
      fac_right := homOfVector_over _ _ }

@[simp]
theorem affineSpaceLift_vadd_appTop_coord (v : n → RingHom.ker i.appTop.hom) (l : sq.LiftStruct)
    (j : n) : (v +ᵥ l).l.appTop (coord S j) = v j + l.l.appTop (coord S j) :=
  homOfVector_appTop_coord _ _ _

/-- The coordinates of two lifts into `𝔸(n; S)` differ by global sections of the ideal sheaf
of `i`. -/
noncomputable instance : VSub (n → RingHom.ker i.appTop.hom) sq.LiftStruct where
  vsub l₁ l₂ j := ⟨l₁.l.appTop (coord S j) - l₂.l.appTop (coord S j), by
    rw [RingHom.mem_ker, map_sub, affineSpaceLift_appTop_appTop_coord,
      affineSpaceLift_appTop_appTop_coord, sub_self]⟩

@[simp]
theorem affineSpaceLift_coe_vsub_apply (l₁ l₂ : sq.LiftStruct) (j : n) :
    ((l₁ -ᵥ l₂) j : Γ(T', ⊤)) = l₁.l.appTop (coord S j) - l₂.l.appTop (coord S j) :=
  (rfl)

/-- Along a closed immersion `i : T ⟶ T'` into an affine scheme, a square into `𝔸(n; S) ⟶ S`
has a lift: lift the coordinates of `g` along the surjection `i.appTop` on global sections. -/
instance affineSpaceLift_hasLift [IsAffine T'] [IsClosedImmersion i] : sq.HasLift := by
  choose v hv using fun j ↦ (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
    (g.appTop (coord S j))
  refine ⟨⟨⟨homOfVector h v, hom_ext (by rw [Category.assoc, homOfVector_over, sq.w])
    fun j ↦ ?_, homOfVector_over _ _⟩⟩⟩
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, homOfVector_appTop_coord, hv]

/-- Along a closed immersion `i : T ⟶ T'` into an affine scheme, the lifts in a square into
`𝔸(n; S) ⟶ S` form a torsor under `n`-tuples of global sections of the ideal sheaf of `i` (the
kernel of `i.appTop`), acting by translation of the coordinates. This is the affine space case of
Stacks, Lemma 37.9.5 (04FJ), where the torsor is under `Hom(g^* Ω_{𝔸(n; S)/S}, I) ≅ I^n`. -/
noncomputable instance affineSpaceLift_addTorsor [IsAffine T'] [IsClosedImmersion i] :
    AddTorsor (n → RingHom.ker i.appTop.hom) sq.LiftStruct where
  zero_vadd l := affineSpaceLift_ext fun j ↦ by simp
  add_vadd v₁ v₂ l := affineSpaceLift_ext fun j ↦ by simp [add_assoc]
  nonempty := (CommSq.HasLift.iff sq).1 inferInstance
  vsub_vadd' l₁ l₂ := affineSpaceLift_ext fun j ↦ by simp
  vadd_vsub' v l := funext fun j ↦ Subtype.ext <| by simp

end TauCeti.AlgebraicGeometry
