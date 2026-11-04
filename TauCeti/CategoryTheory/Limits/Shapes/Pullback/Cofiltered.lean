/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Base change of a cofiltered limit

Let `D : I ⥤ C` be a diagram in a category with pullbacks, `i : I`, and `r : Z ⟶ Dᵢ`. The members
`Dⱼ` over `i` base change along `r` to the diagram `D.pullbackOver r : Over i ⥤ C`,
`j ↦ Dⱼ ×_{Dᵢ} Z`, and a cone `c` over `D` base changes to the cone `c.pullbackOver r` with point
`c.pt ×_{Dᵢ} Z`. When `I` is cofiltered, the base change of a limit cone is a limit cone
(`CategoryTheory.Limits.IsLimit.pullbackOver`).

Up to the choice of pullbacks, `D.pullbackOver r` is the composite
`Over.post D ⋙ Over.pullback r ⋙ Over.forget Z`; it is stated with the objects
`pullback (D.map j.hom) r` so that the pullback projections apply to its members directly.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasPullbacks C] {I : Type*} [Category* I] (D : I ⥤ C) {i : I}
  {Z : C} (r : Z ⟶ D.obj i)

/-- The base change `j ↦ Dⱼ ×_{Dᵢ} Z` of the members of `D` over `i` along `r : Z ⟶ Dᵢ`. -/
noncomputable abbrev _root_.CategoryTheory.Functor.pullbackOver : Over i ⥤ C where
  obj j := pullback (D.map j.hom) r
  map {j k} f := pullback.map _ _ _ _ (D.map f.left) (𝟙 Z) (𝟙 _)
    (by simp [← D.map_comp]) (by simp)
  map_id j := by ext <;> simp
  map_comp f g := by ext <;> simp

@[reassoc]
lemma _root_.CategoryTheory.Functor.pullbackOver_map_fst {j k : Over i} (f : j ⟶ k) :
    (D.pullbackOver r).map f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ D.map f.left := by
  simp [Functor.pullbackOver]

@[reassoc]
lemma _root_.CategoryTheory.Functor.pullbackOver_map_snd {j k : Over i} (f : j ⟶ k) :
    (D.pullbackOver r).map f ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [Functor.pullbackOver]

variable {D}

/-- The base change `c.pt ×_{Dᵢ} Z` of a cone `c` over `D` along `r : Z ⟶ Dᵢ`. -/
noncomputable abbrev Cone.pullbackOver (c : Cone D) : Cone (D.pullbackOver r) where
  pt := pullback (c.π.app i) r
  π :=
    { app j := pullback.map _ _ _ _ (c.π.app j.left) (𝟙 Z) (𝟙 _) (by simp) (by simp)
      naturality j k f := by ext <;> simp [Functor.pullbackOver] }

@[reassoc]
lemma Cone.pullbackOver_π_app_fst (c : Cone D) (j : Over i) :
    (c.pullbackOver r).π.app j ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ c.π.app j.left := by
  simp [Cone.pullbackOver]

@[reassoc]
lemma Cone.pullbackOver_π_app_snd (c : Cone D) (j : Over i) :
    (c.pullbackOver r).π.app j ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [Cone.pullbackOver]

/-- The base change of a limit cone of a cofiltered diagram is a limit cone. -/
noncomputable def IsLimit.pullbackOver [IsCofilteredOrEmpty I] {c : Cone D}
    (hc : IsLimit c) : IsLimit (c.pullbackOver r) := by
  have hc' := Over.isLimitConePost i hc
  -- `Over.mk (𝟙 i)` is terminal in `Over i`, so every leg agrees with its leg to `Z`.
  let o : Over i := Over.mk (𝟙 i)
  have snd_eq (s : Cone (D.pullbackOver r)) (j : Over i) :
      s.π.app j ≫ pullback.snd _ _ = s.π.app o ≫ pullback.snd _ _ := by
    rw [← s.w (Over.homMk j.hom : j ⟶ o), Category.assoc, Functor.pullbackOver_map_snd]
  let s' (s : Cone (D.pullbackOver r)) : Cone (Over.post (X := i) D) :=
    { pt := Over.mk (s.π.app o ≫ pullback.snd _ _ ≫ r)
      π :=
        { app j := Over.homMk (s.π.app j ≫ pullback.fst _ _) (by
            dsimp
            rw [Category.assoc, pullback.condition, reassoc_of% snd_eq s j])
          naturality j k f := by
            ext
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Over.comp_left, Over.homMk_left]
            rw [← s.w f, Category.assoc, Functor.pullbackOver_map_fst, Category.assoc]
            rfl } }
  have hL (s : Cone (D.pullbackOver r)) (j : Over i) :
      (hc'.lift (s' s)).left ≫ c.π.app j.left = s.π.app j ≫ pullback.fst _ _ :=
    congr(($(hc'.fac (s' s) j)).left)
  exact
    { lift s := pullback.lift (f := c.π.app i) (g := r) (hc'.lift (s' s)).left
        (s.π.app o ≫ pullback.snd _ _)
        ((Over.w (hc'.lift (s' s))).trans (Category.assoc _ _ _).symm)
      fac s j := by
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst]
          erw [pullback.lift_fst_assoc]
          exact hL s j
        · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
          erw [pullback.lift_snd]
          exact (snd_eq s j).symm
      uniq s m hm := by
        apply pullback.hom_ext
        · have hm' : Over.homMk (m ≫ pullback.fst (c.π.app i) r) (by
              change (m ≫ pullback.fst _ _) ≫ c.π.app i = _
              simp [s', pullback.condition, ← hm o]) = hc'.lift (s' s) := by
            refine hc'.uniq (s' s) _ fun j ↦ ?_
            ext
            refine (Category.assoc _ _ _).trans ?_
            simp [s', ← hm j]
            rfl
          erw [pullback.lift_fst]
          exact congr(($hm').left)
        · simp [← hm o]
          rfl }

end CategoryTheory.Limits
