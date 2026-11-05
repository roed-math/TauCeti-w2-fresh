/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections

/-!
# Pulled-back sections and the monoidal structure of pullback

For a morphism of schemes `g : Y ⟶ X`, pulling back sections over an open `U` of `X`
(`AlgebraicGeometry.Scheme.Hom.pullbackSections`) is compatible with the oplax monoidal
structure of pullback of modules:

* the tensor comparison `g^* (M ⊗ N) ⟶ g^* M ⊗ g^* N` sends the pullback of the section `x ⊗ y`
  of `M ⊗ N` to the section `g^* x ⊗ g^* y` (`Scheme.Hom.δ_app_pullbackSections_μ`);
* the identification `g^* 𝒪_X ≅ 𝒪_Y` sends the pullback of a function `r` to `g^* r`
  (`Scheme.Hom.pullbackObjUnitIso_hom_app_pullbackSections`).

Both follow from the compatibility of the pullback--pushforward adjunction with the monoidal
structures (Mathlib's `Adjunction.unit_app_tensor_comp_map_δ`), evaluated on sections. They show
that pulling back sections of an algebra is a ring homomorphism.
-/

public section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- Pulling back sections is compatible with tensor products: the tensor comparison
`g^* (M ⊗ N) ⟶ g^* M ⊗ g^* N` sends the pullback of the section `x ⊗ y` of `M ⊗ N` over `U` to
the section `g^* x ⊗ g^* y` over `g⁻¹ U`. -/
theorem δ_app_pullbackSections_μ (M N : X.Modules) (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)) :
    (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) M N).app (g ⁻¹ᵁ U)
        (g.pullbackSections (M ⊗ N) U
          (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) M N (x ⊗ₜ y))) =
      Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor (g ⁻¹ᵁ U)) _ _
        (g.pullbackSections M U x ⊗ₜ g.pullbackSections N U y) := by
  simp only [pullbackSections_apply]
  -- The adjunction unit is monoidal; evaluate this on the section `x ⊗ y` over `U`.
  have h := congr(($((Scheme.Modules.pullbackPushforwardAdjunction g).unit_app_tensor_comp_map_δ
    M N)).app U (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) M N (x ⊗ₜ y)))
  have hμ := congr($(Functor.LaxMonoidal.μ_natural (Scheme.Modules.sectionsFunctor U)
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N)) (x ⊗ₜ y))
  have hp := TauCeti.SheafOfModules.pushforward_μ_app_tmul.{u} g.toRingCatSheafHom
    ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N) (op U)
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U x)
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app U y)
  simp only [ConcreteCategory.comp_apply] at hμ
  -- `pullbackSections` is not exposed, so its unfolding equation is used as a rewrite.
  erw [pullbackSections_apply]
  erw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
  refine h.trans ?_
  erw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, ← hμ]
  exact hp

/-- Pulling back functions is compatible with the identification `g^* 𝒪_X ≅ 𝒪_Y`: it sends the
pullback of a function `r` over `U` to the function `g^* r` over `g⁻¹ U`. -/
theorem pullbackObjUnitIso_hom_app_pullbackSections (U : X.Opens) (r : Γ(X, U)) :
    (Scheme.Modules.pullbackObjUnitIso g).hom.app (g ⁻¹ᵁ U)
        (g.pullbackSections (𝟙_ X.Modules) U r) = g.app U r := by
  have h := congr(($(Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom
    g)).val.app (op U) r)
  rw [Adjunction.homEquiv_unit] at h
  -- `pullbackSections` is not exposed, so its unfolding equation is used as a rewrite.
  erw [pullbackSections_apply]
  exact h

end AlgebraicGeometry.Scheme.Hom
