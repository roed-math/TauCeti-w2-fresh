/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Cofiltered
public import TauCeti.CategoryTheory.MorphismProperty.Limits

/-!
# Base change of a cofiltered diagram of schemes

Let `D : I ⥤ Scheme` be a diagram, `i : I`, and `r : Z ⟶ Dᵢ`. The base change
`D.pullbackOver r : Over i ⥤ Scheme`, `j ↦ Dⱼ ×_{Dᵢ} Z`, writes a scheme `Z` over a member `Dᵢ`
of `S = lim Dⱼ` as the cofiltered limit of the `Dⱼ ×_{Dᵢ} Z` (Stacks, Section 32.10 (01ZL)). This
file records that affine transition maps, quasi-compactness and quasi-separation of the members
pass to the base change, so that the descent results for such limits apply to it.

The reduction `exists_pullbackMap_of_pullbackOver` passes finite-stage inheritance of a property
from structure morphisms over a limit to arbitrary morphisms between schemes over a member.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

section BaseChange

variable {I : Type*} [Category* I] (D : I ⥤ Scheme.{u}) {i : I} {Z : Scheme.{u}}
  (r : Z ⟶ D.obj i)

instance [∀ {j k : I} (f : j ⟶ k), IsAffineHom (D.map f)] {j k : Over i} (f : j ⟶ k) :
    IsAffineHom ((D.pullbackOver r).map f) := by
  have s : IsPullback ((D.pullbackOver r).map f ≫ pullback.snd (D.map k.hom) r)
      (pullback.fst _ _) r (D.map f.left ≫ D.map k.hom) := by
    rw [Functor.pullbackOver_map_snd, ← D.map_comp, Over.w f]
    exact (IsPullback.of_hasPullback _ r).flip
  have sq := IsPullback.of_right s (D.pullbackOver_map_fst r f)
    (IsPullback.of_hasPullback _ r).flip
  exact MorphismProperty.of_isPullback sq.flip inferInstance

instance [∀ j, CompactSpace (D.obj j)] [QuasiCompact r] (j : Over i) :
    CompactSpace ((D.pullbackOver r).obj j) := by
  dsimp; infer_instance

instance [∀ j, QuasiSeparatedSpace (D.obj j)] [QuasiSeparated r] (j : Over i) :
    QuasiSeparatedSpace ((D.pullbackOver r).obj j) := by
  dsimp; exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)

end BaseChange

section Reduction

variable {I : Type*} [Category* I] {D : I ⥤ Scheme.{u}} (c : Cone D)

/-- Let `c` be a cone over `D`, and `g : X ⟶ Y` a morphism of schemes over a member `Dᵢ`. The base
changes of `g` to `c.pt` and to the members `Dⱼ` over `Dᵢ` are the base changes of the morphism
`X ×_Y (Dᵢ ×_{Dᵢ} Y) ⟶ Dᵢ ×_{Dᵢ} Y` to `c.pt ×_{Dᵢ} Y` and to the members `Dⱼ ×_{Dᵢ} Y` of
`D.pullbackOver q`. So if a property `P` closed under isomorphisms passes from the cone
`c.pullbackOver q` to a member for this morphism, it passes from `c` to some `Dⱼ` for `g`. -/
theorem exists_pullbackMap_of_pullbackOver (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {i : I} {X Y : Scheme.{u}} {p : X ⟶ D.obj i} {q : Y ⟶ D.obj i} (g : X ⟶ Y) (hg : g ≫ q = p)
    (H : P (pullback.fst ((c.pullbackOver q).π.app (Over.mk (𝟙 i)))
        (pullback.fst (pullback.snd (D.map (𝟙 i)) q) g)) →
      ∃ (k : Over i) (hk : k ⟶ Over.mk (𝟙 i)), P (pullback.fst ((D.pullbackOver q).map hk)
        (pullback.fst (pullback.snd (D.map (𝟙 i)) q) g)))
    (h : P (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg]))) :
    ∃ (j : I) (hji : j ⟶ i),
      P (pullback.map (D.map hji) p (D.map hji) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])) := by
  let r : pullback (D.map (𝟙 i)) q ⟶ Y := pullback.snd _ _
  obtain ⟨k, hk, hP⟩ := H <| (MorphismProperty.pullback_fst_pullback_fst_iff _ r g
    (Cone.pullbackOver_π_app_snd q c _)).mpr
      ((MorphismProperty.pullback_map_iff_pullback_fst_pullback_snd _ g hg).mp h)
  exact ⟨k.left, k.hom, (MorphismProperty.pullback_map_iff_pullback_fst_pullback_snd _ g hg).mpr
    ((MorphismProperty.pullback_fst_pullback_fst_iff _ r g (D.pullbackOver_map_snd q hk)).mp hP)⟩

end Reduction

end TauCeti.AlgebraicGeometry.Scheme
