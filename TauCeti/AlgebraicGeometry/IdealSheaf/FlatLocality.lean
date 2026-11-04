/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Ideal sheaves are determined by their pullbacks along fppf coverings

Let `f : X ⟶ Y` be a flat surjective morphism of schemes, locally of finite presentation, for
instance an étale surjection. Then every ideal sheaf `I` on `Y` is the pushforward of its inverse
image: `(I.comap f).map f = I`
(`AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_flat_of_surjective`). Hence taking inverse
images along `f` is injective on ideal sheaves
(`AlgebraicGeometry.Scheme.IdealSheafData.comap_injective_of_flat_of_surjective`), and it reflects
inclusions (`AlgebraicGeometry.Scheme.IdealSheafData.comap_le_comap_iff_of_flat_of_surjective`): a
closed subscheme of `Y` is determined by its base change along an fppf covering. This is the
uniqueness half of faithfully flat descent for closed subschemes.

The proof descends morphisms: the base change `X ×_Y Z ⟶ Z` of `f` to the closed subscheme `Z` of
`I` is again flat, surjective and locally of finite presentation, hence an effective epimorphism of
schemes, and the closed subscheme of `(I.comap f).map f` receives a morphism from `X ×_Y Z` which
is invariant under its kernel pair, so `Z` maps into that closed subscheme over `Y`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_flat_of_surjective`: the pushforward of
  the inverse image of `I` along an fppf covering is `I`.
* `AlgebraicGeometry.Scheme.IdealSheafData.comap_le_comap_iff_of_flat_of_surjective`: inverse
  image along an fppf covering reflects inclusions of ideal sheaves.
* `AlgebraicGeometry.Scheme.IdealSheafData.comap_injective_of_flat_of_surjective`: inverse image
  along an fppf covering is injective on ideal sheaves.

## References

* The Stacks Project, Tag 023Q (fpqc coverings are effective epimorphisms).
-/

public section

open CategoryTheory Limits AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [LocallyOfFinitePresentation f]

/-- **An ideal sheaf is the pushforward of its inverse image along an fppf covering.** For a flat
surjective morphism `f : X ⟶ Y`, locally of finite presentation, and an ideal sheaf `I` on `Y`,
`(I.comap f).map f = I`. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_flat_of_surjective
    (I : Y.IdealSheafData) : (I.comap f).map f = I := by
  refine le_antisymm ?_ (le_map_iff_comap_le.mpr le_rfl)
  let K := (I.comap f).map f
  let p := pullback.snd f I.subschemeι
  -- The base change of `X ×_Y Z` to the closed subscheme of `K`.
  let m : pullback f I.subschemeι ⟶ K.subscheme :=
    (I.comapIso f).inv ≫ subschemeMap (I.comap f) K f le_rfl
  have hm : m ≫ K.subschemeι = p ≫ I.subschemeι := by
    simp [m, p, pullback.condition]
  -- It descends along the effective epimorphism `p : X ×_Y Z ⟶ Z`.
  let k : I.subscheme ⟶ K.subscheme := EffectiveEpi.desc p m fun g₁ g₂ hg ↦ by
    rw [← cancel_mono K.subschemeι]
    simp only [Category.assoc, hm, reassoc_of% hg]
  have hk : k ≫ K.subschemeι = I.subschemeι := by
    rw [← cancel_epi p, ← Category.assoc, EffectiveEpi.fac, hm]
  calc K = K.subschemeι.ker := K.ker_subschemeι.symm
    _ ≤ (k ≫ K.subschemeι).ker := Scheme.Hom.le_ker_comp _ _
    _ = I := by rw [hk, ker_subschemeι]

/-- **Inclusions of ideal sheaves can be checked after an fppf covering.** For a flat surjective
morphism `f : X ⟶ Y`, locally of finite presentation, `I.comap f ≤ J.comap f` if and only if
`I ≤ J`. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.comap_le_comap_iff_of_flat_of_surjective
    {I J : Y.IdealSheafData} : I.comap f ≤ J.comap f ↔ I ≤ J := by
  refine ⟨fun h ↦ ?_, fun h ↦ comap_mono f h⟩
  rw [← map_comap_of_flat_of_surjective f I, ← map_comap_of_flat_of_surjective f J]
  exact map_mono f h

/-- **Ideal sheaves are determined by their inverse images along an fppf covering.** For a flat
surjective morphism `f : X ⟶ Y`, locally of finite presentation, two ideal sheaves on `Y` with the
same inverse image along `f` are equal. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.comap_injective_of_flat_of_surjective :
    Function.Injective fun I : Y.IdealSheafData ↦ I.comap f := fun I J h ↦ by
  exact le_antisymm ((comap_le_comap_iff_of_flat_of_surjective f).mp h.le)
    ((comap_le_comap_iff_of_flat_of_surjective f).mp h.ge)

end TauCeti
