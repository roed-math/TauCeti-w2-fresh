/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections

/-!
# Pulling back sections of the structure sheaf

For a morphism of schemes `g : Y ⟶ X`, the pullback `g^* 𝒪_X` is identified with `𝒪_Y` by
`Scheme.Modules.pullbackObjUnitIso`. Under this identification, pulling back a function
`s ∈ Γ(X, U)` as a section of `𝒪_X` gives the function `g^♯ s ∈ Γ(Y, g⁻¹ U)`
(`Scheme.Hom.pullbackObjUnitIso_hom_app_pullbackSections`).
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- Pulling back a function `s` on `U` as a section of `𝒪_X` and identifying `g^* 𝒪_X` with `𝒪_Y`
gives the function `g^♯ s` on `g⁻¹ U`. -/
theorem pullbackObjUnitIso_hom_app_pullbackSections (U : X.Opens) (s : Γ(X, U)) :
    (Scheme.Modules.pullbackObjUnitIso g).hom.app (g ⁻¹ᵁ U)
      (g.pullbackSections (𝟙_ X.Modules) U s) = g.app U s := by
  have h := Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom g
  rw [Adjunction.homEquiv_unit] at h
  -- Evaluate both sides of the transposed identification on `s`, a section of `𝒪_X` over `U`;
  -- the map `𝒪_X ⟶ g_* 𝒪_Y` acts on it by `g^♯`.
  have h' := congrArg (fun φ : 𝟙_ X.Modules ⟶ (Scheme.Modules.pushforward g).obj (𝟙_ Y.Modules) ↦
    Scheme.Modules.Hom.app φ U (s : Γ(𝟙_ X.Modules, U))) h
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at h'
  exact (congrArg _ (g.pullbackSections_apply (𝟙_ X.Modules) U s)).trans
    (h'.trans (SheafOfModules.unitToPushforwardObjUnit_val_app_apply g.toRingCatSheafHom
      (X := .op U) s))

end AlgebraicGeometry.Scheme.Hom
