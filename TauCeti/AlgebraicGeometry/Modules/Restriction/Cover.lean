/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Isomorphisms of modules are local on a covering family of open immersions

A morphism of `𝒪_X`-modules whose restrictions along a jointly surjective family of open
immersions `fᵢ : Yᵢ ⟶ X` are isomorphisms is an isomorphism
(`AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_isIso_restrictFunctor_map`). Unlike
`AlgebraicGeometry.Scheme.Modules.isIso_iff_of_isOpenCover`, the members of the cover need not be
open subschemes: they may be, for instance, the charts of a glued scheme.

The proof checks the isomorphism on the basis of opens contained in the image of some `fᵢ`, where
the sections of the restriction along `fᵢ` over `fᵢ⁻¹ W` are the sections over `fᵢ(fᵢ⁻¹ W) = W`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_isIso_restrictFunctor_map`: isomorphisms of
  `𝒪_X`-modules can be checked after restriction along a covering family of open immersions.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- **Isomorphisms of `𝒪_X`-modules are local on a covering family of open immersions**: a
morphism whose restrictions along open immersions `fᵢ : Yᵢ ⟶ X` covering `X` are isomorphisms is
an isomorphism. -/
theorem Hom.isIso_of_isIso_restrictFunctor_map {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    {ι : Type*} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hf : ∀ x, ∃ i, x ∈ (f i).opensRange) (h : ∀ i, IsIso ((restrictFunctor (f i)).map φ)) :
    IsIso φ := by
  -- the opens inside the image of some `fᵢ` form a basis, on whose members `φ` is an isomorphism
  let B : {W : X.Opens // ∃ i, W ≤ (f i).opensRange} → X.Opens := Subtype.val
  have hB : TopologicalSpace.Opens.IsBasis (Set.range B) := by
    refine TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {W x} hx ↦ ?_
    obtain ⟨i, hi⟩ := hf x
    exact ⟨W ⊓ (f i).opensRange, ⟨⟨_, i, inf_le_right⟩, rfl⟩, ⟨hx, hi⟩, inf_le_left⟩
  let ψ : (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X) ⟶ ⟨N.presheaf, N.isSheaf⟩ :=
    ObjectProperty.homMk φ.mapPresheaf
  have : IsIso ψ := TopCat.Sheaf.isIso_iff_isIso_basis hB fun ⟨W, i, hW⟩ ↦ by
    have e : (f i) ''ᵁ ((f i) ⁻¹ᵁ W) = W := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact inf_eq_right.2 hW
    -- sections of the restriction along `fᵢ` over `fᵢ⁻¹ W` are sections over `fᵢ(fᵢ⁻¹ W) = W`
    have : IsIso (φ.app ((f i) ''ᵁ ((f i) ⁻¹ᵁ W))) :=
      inferInstanceAs (IsIso (((restrictFunctor (f i)).map φ).app ((f i) ⁻¹ᵁ W)))
    rw [e] at this
    exact this
  refine Hom.isIso_iff_isIso_app.mpr fun V ↦ ?_
  exact NatIso.isIso_app_of_isIso ((TopCat.Sheaf.forget _ _).map ψ) (Opposite.op V)

end AlgebraicGeometry.Scheme.Modules
