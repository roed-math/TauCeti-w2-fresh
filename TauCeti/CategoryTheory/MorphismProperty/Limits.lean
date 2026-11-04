/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Base changes of base changes

Let `P` be a property of morphisms stable under base change. If the base change
`pullback.snd f k` of `f` along `k` has `P`, then so does every further base change of `f` along a
morphism factoring through `k`: this file records the forms of this used when reducing a property
of morphisms of schemes to an affine base. Mathlib's `MorphismProperty.pullback_snd` is the case
where `f` itself has `P`.

## Main results

* `CategoryTheory.MorphismProperty.pullback_snd_comp`: `P (pullback.snd f k)` implies
  `P (pullback.snd f (e ≫ k))`; `pullback_snd_of_comp_eq` is the same for a morphism equal to
  `e ≫ k`.
* `CategoryTheory.MorphismProperty.pullback_snd_pullback_fst_comp`: the base change of `f` along
  `Y ×_S T ⟶ Y` passes its property to the base change along `Y ×_S T' ⟶ Y` for any `T' ⟶ T`.
* `CategoryTheory.MorphismProperty.pullback_snd_pullback_snd`: `P (pullback.snd f k)` implies
  `P (pullback.snd (pullback.snd f v) a)` whenever `a ≫ v` factors through `k`.
* `CategoryTheory.MorphismProperty.pullback_snd_comp_left`: if `P` is moreover stable under
  composition, `P e` and `P (pullback.snd f k)` imply `P (pullback.snd (e ≫ f) k)`.
* `CategoryTheory.MorphismProperty.pullback_fst_pullback_fst_iff`: for `P` closed under
  isomorphisms, `P (pullback.fst f' (pullback.fst f g)) ↔ P (pullback.fst (f' ≫ f) g)`;
  `pullback_fst_of_comp_eq` is the resulting inheritance along `e ≫ f`.
* `CategoryTheory.MorphismProperty.pullback_map_pullback_map_iff`: the same for the base change of
  a morphism `g` over `Z`, along `f'` after `f` and along `f' ≫ f`.
* `CategoryTheory.MorphismProperty.pullback_map_iff_pullback_fst_pullback_snd`: the base change of
  a morphism `g : X ⟶ Y` over `Z` along `f` is the base change of `g` along `T ×_Z Y ⟶ Y`.
* `CategoryTheory.MorphismProperty.diagonal_pullback_fst_iff`: the diagonal of a base change of
  `q` is the base change of the diagonal of `q`.
-/

public section

namespace CategoryTheory.MorphismProperty

open Limits

variable {C : Type*} [Category* C] [HasPullbacks C] {P : MorphismProperty C}
  [P.IsStableUnderBaseChange] {X Y W W' : C}

/-- A base change of `pullback.snd f k` along `e` is the base change of `f` along `e ≫ k`, so it
inherits every property stable under base change. -/
theorem pullback_snd_comp (f : X ⟶ Y) (k : W ⟶ Y) (e : W' ⟶ W) (h : P (pullback.snd f k)) :
    P (pullback.snd f (e ≫ k)) := by
  refine (P.cancel_left_of_respectsIso (pullbackLeftPullbackSndIso f k e).hom _).mp ?_
  simpa using P.pullback_snd _ e h

/-- A form of `pullback_snd_comp` for a morphism `a` known to factor as `e ≫ k`. Its conclusion
does not mention the composite, so it can be applied where rewriting with the factorisation inside
`pullback` is not possible. -/
theorem pullback_snd_of_comp_eq (f : X ⟶ Y) (k : W ⟶ Y) (e : W' ⟶ W) {a : W' ⟶ Y}
    (hfac : e ≫ k = a) (h : P (pullback.snd f k)) : P (pullback.snd f a) := by
  subst hfac
  exact pullback_snd_comp f k e h

/-- If the base change of `f` along `Y ×_S T ⟶ Y` has `P`, then so does its base change along
`Y ×_S T' ⟶ Y` for every `t : T' ⟶ T`, since the latter factors through the former. -/
theorem pullback_snd_pullback_fst_comp {S T T' : C} (f : X ⟶ Y) (g : Y ⟶ S) (r : T ⟶ S)
    (t : T' ⟶ T) (h : P (pullback.snd f (pullback.fst g r))) :
    P (pullback.snd f (pullback.fst g (t ≫ r))) :=
  pullback_snd_of_comp_eq f _ ((pullbackLeftPullbackSndIso g r t).inv ≫ pullback.fst _ _)
    (by simp) h

/-- If `a ≫ v` factors as `e ≫ k`, then the base change of `pullback.snd f v` along `a` inherits
from `pullback.snd f k` every property stable under base change. -/
theorem pullback_snd_pullback_snd {Y' T : C} (f : X ⟶ Y) (v : Y' ⟶ Y) (a : T ⟶ Y')
    (k : W ⟶ Y) (e : T ⟶ W) (hfac : a ≫ v = e ≫ k) (h : P (pullback.snd f k)) :
    P (pullback.snd (pullback.snd f v) a) := by
  have := pullback_snd_of_comp_eq f k e hfac.symm h
  refine (P.cancel_left_of_respectsIso (pullbackLeftPullbackSndIso f v a).inv _).mp ?_
  simpa using this

/-- For a property stable under base change and composition, precomposing `f` with a morphism
having the property keeps the property of `pullback.snd f k`. -/
theorem pullback_snd_comp_left [P.IsStableUnderComposition] {X' : C} (f : X ⟶ Y) (k : W ⟶ Y)
    (e : X' ⟶ X) (he : P e) (h : P (pullback.snd f k)) : P (pullback.snd (e ≫ f) k) := by
  refine (P.cancel_left_of_respectsIso (pullbackRightPullbackFstIso f k e).hom _).mp ?_
  simpa using P.comp_mem _ _ (P.pullback_snd _ _ he) h

omit [P.IsStableUnderBaseChange] in
/-- The base change of `g` along `f' ≫ f` is the base change along `f'` of its base change along
`f`, so the two have the same properties closed under isomorphisms. -/
theorem pullback_fst_pullback_fst_iff [P.RespectsIso] {Z : C} (f' : W ⟶ X) (f : X ⟶ Z)
    (g : Y ⟶ Z) {a : W ⟶ Z} (hfac : f' ≫ f = a) :
    P (pullback.fst f' (pullback.fst f g)) ↔ P (pullback.fst a g) := by
  subst hfac
  rw [← pullbackRightPullbackFstIso_hom_fst, P.cancel_left_of_respectsIso]

/-- A base change of `pullback.fst f g` along `e` is the base change of `g` along a morphism
`a = e ≫ f`, so it inherits every property stable under base change. -/
theorem pullback_fst_of_comp_eq {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (e : W ⟶ X) {a : W ⟶ Z}
    (hfac : e ≫ f = a) (h : P (pullback.fst f g)) : P (pullback.fst a g) :=
  (pullback_fst_pullback_fst_iff e f g hfac).mp (P.pullback_fst _ _ h)

omit [P.IsStableUnderBaseChange] in
/-- The base change of a morphism `g : X ⟶ Y` over `Z` along `f' ≫ f` is the base change along
`f'` of its base change along `f`, so the two have the same properties closed under
isomorphisms. -/
theorem pullback_map_pullback_map_iff [P.RespectsIso] {S T Z : C} (f' : T ⟶ S) (f : S ⟶ Z)
    {a : T ⟶ Z} (hfac : f' ≫ f = a) {p : X ⟶ Z} {q : Y ⟶ Z} (g : X ⟶ Y) (hg : g ≫ q = p) :
    P (pullback.map f' (pullback.fst f p) f' (pullback.fst f q) (𝟙 _)
        (pullback.map f p f q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])) (𝟙 _) (by simp)
        (by simp)) ↔
      P (pullback.map a p a q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])) := by
  subst hfac
  refine P.arrow_mk_iso_iff (Arrow.isoMk (pullbackRightPullbackFstIso f p f')
    (pullbackRightPullbackFstIso f q f') ?_)
  apply pullback.hom_ext <;> simp

omit [P.IsStableUnderBaseChange] in
/-- The base change along `f` of a morphism `g : X ⟶ Y` over `Z` is the base change of `g` along
the projection `T ×_Z Y ⟶ Y`, so the two have the same properties closed under isomorphisms. -/
theorem pullback_map_iff_pullback_fst_pullback_snd [P.RespectsIso] {T Z : C} (f : T ⟶ Z)
    {p : X ⟶ Z} {q : Y ⟶ Z} (g : X ⟶ Y) (hg : g ≫ q = p) :
    P (pullback.map f p f q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])) ↔
      P (pullback.fst (pullback.snd f q) g) := by
  subst hg
  refine P.arrow_mk_iso_iff (Arrow.isoMk (pullbackLeftPullbackSndIso f q g).symm (Iso.refl _) ?_)
  apply pullback.hom_ext <;> simp

omit [P.IsStableUnderBaseChange] in
/-- The diagonal of the base change `T ×_Z Y ⟶ T` of `q : Y ⟶ Z` along `f` is the base change along
`f` of the diagonal of `q`, so the two have the same properties closed under isomorphisms. -/
theorem diagonal_pullback_fst_iff [P.RespectsIso] {T Z : C} (f : T ⟶ Z) (q : Y ⟶ Z) :
    P.diagonal (pullback.fst f q) ↔
      P (pullback.map f q f (pullback.snd q q ≫ q) (𝟙 _) (pullback.diagonal q) (𝟙 _) (by simp)
        (by simp)) := by
  have : pullback.diagonal (pullback.fst f q) =
      pullback.map f q f (pullback.snd q q ≫ q) (𝟙 _) (pullback.diagonal q) (𝟙 _) (by simp)
        (by simp) ≫ (pullbackSymmetry _ _).hom ≫ (diagonalObjPullbackFstIso f q).inv := by
    ext <;> simp
  rw [diagonal_iff, this, P.cancel_right_of_respectsIso]

end CategoryTheory.MorphismProperty
