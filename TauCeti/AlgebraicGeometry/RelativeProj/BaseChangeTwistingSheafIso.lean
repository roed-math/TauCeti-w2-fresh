/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.PullbackBaseChange
public import TauCeti.AlgebraicGeometry.RelativeProj.BaseChangeTwistingSheaf
public import TauCeti.CategoryTheory.Adjunction.HomEquiv

/-!
# Toward the base change of the relative `Proj`, compatibly with the twisting sheaves

Let `g : X ⟶ Y` be a morphism of schemes, `A` a graded quasicoherent algebra on `Y`, and
`h = relativeProjPullbackHom g A : Proj_X(g^* A) ⟶ Proj_Y(A)` the projection of the relative `Proj`
of the pulled-back graded algebra, which exhibits `Proj_X(g^* A)` as the base change of `Proj_Y(A)`
along `g` (`GradedQuasicoherentAlgebra.isPullback_relativeProjPullbackHom`).

For affine opens `U` of `Y` and `V ≤ g⁻¹ U` of `X`, the chart `Proj (⨁ n, Γ(g^* Aₙ, V))` maps to the
chart `Proj (⨁ n, Γ(Aₙ, U))` by `Proj.map` of the pullback of sections, a base change of graded
rings (`GradedQuasicoherentAlgebra.isBaseChange_pullbackGradedSections`), so the twisting sheaves of
the charts pull back to each other
(`GradedQuasicoherentAlgebra.isIso_pullbackTwistingSheafMap_pullbackGradedSectionsGradedHom`, from
`AlgebraicGeometry.Proj.isIso_pullbackTwistingSheafMap_of_isBaseChange`). The chart comparison
`relativeProjTwistingSheafChartHom` factors through the two factorizations
`ι_V ≫ h = Proj.map ≫ ι_U` of the pushforward, and its part through `ι_U` and `Proj.map` has an
invertible transpose.

## Main results

* `GradedQuasicoherentAlgebra.isIso_pullbackTwistingSheafMap_pullbackGradedSectionsGradedHom`:
  the comparison `(Proj.map)^* 𝒪(n) ⟶ 𝒪(n)` between the twisting sheaves of the charts is an
  isomorphism.

## References

* [The Stacks Project, Lemma 27.16.10](https://stacks.math.columbia.edu/tag/01O3)
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

namespace GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (A : GradedQuasicoherentAlgebra Y) {U : Y.Opens}
  {V : X.Opens} (hV : V ≤ g ⁻¹ᵁ U)

/-- **The twisting sheaves of the charts pull back.** For affine opens `U` of `Y` and `V ≤ g⁻¹ U`
of `X`, the comparison `(Proj.map)^* 𝒪(n) ⟶ 𝒪(n)` along
`Proj (⨁ n, Γ(g^* Aₙ, V)) ⟶ Proj (⨁ n, Γ(Aₙ, U))` is an isomorphism, for every `n ∈ ℤ`. -/
theorem isIso_pullbackTwistingSheafMap_pullbackGradedSectionsGradedHom (hU : IsAffineOpen U)
    (hV' : IsAffineOpen V) (n : ℤ) :
    IsIso (Proj.pullbackTwistingSheafMap (A.pullbackGradedSectionsGradedHom g hV)
      (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV hU hV') n) := by
  let := (g.appLE U V hV).hom.toAlgebra
  let := A.algebraPullbackGradedSections g hV
  have := A.isScalarTower_pullbackGradedSections g hV
  exact Proj.isIso_pullbackTwistingSheafMap_of_isBaseChange _ _ _
    (A.isBaseChange_pullbackGradedSections g hV hU hV') n

variable (n : ℤ)

variable {g A} in
/-- The two factorizations `ι_V ≫ h = Proj.map ≫ ι_U` of the pushforward from the chart of
`Proj_X(g^* A)` over `V ≤ g⁻¹ U` to `Proj_Y(A)`. -/
private noncomputable def chartPushforwardIso {V : X.AffineZariskiSite} {U : Y.AffineZariskiSite}
    (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    Scheme.Modules.pushforward (Proj.map (A.pullbackGradedSectionsGradedHom g hV)
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2)) ⋙
        Scheme.Modules.pushforward (A.obj.relativeProjCover.f U) ≅
      Scheme.Modules.pushforward ((pullback g A).obj.relativeProjCover.f V) ⋙
        Scheme.Modules.pushforward (relativeProjPullbackHom g A) :=
  Scheme.Modules.pushforwardComp _ _ ≪≫
    Scheme.Modules.pushforwardCongr (relativeProjCover_f_relativeProjPullbackHom g A V U hV).symm ≪≫
    (Scheme.Modules.pushforwardComp _ _).symm

/-- The chart comparison is the projection to the chart over `U` followed by the map of twisting
sheaves of the charts, transported along `chartPushforwardIso`. -/
private theorem relativeProjTwistingSheafChartHom_eq_comp {V : X.AffineZariskiSite}
    {U : Y.AffineZariskiSite} (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    A.relativeProjTwistingSheafChartHom g n hV =
      ((A.obj.relativeProjTwistingSheafGlueData n).π U ≫
        (Scheme.Modules.pushforward (A.obj.relativeProjCover.f U)).map
          (Proj.twistingSheafMap (A.pullbackGradedSectionsGradedHom g hV)
            (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2) n)) ≫
        (chartPushforwardIso hV).hom.app _ := by
  -- on sections, both sides restrict the image of the projection along an `eqToHom`
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ConcreteCategory.hom_ext _ _ fun s ↦ ?_
  exact (A.relativeProjTwistingSheafChartHom_app_apply g n hV W s).trans rfl

/-- The transpose of the projection of `𝒪_A(n)` to the chart over `U` followed by the map of
twisting sheaves of the charts, along `ι_U` and then `Proj.map`, is an isomorphism. -/
private theorem isIso_homEquiv_symm_π_comp_map {V : X.AffineZariskiSite}
    {U : Y.AffineZariskiSite} (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    IsIso ((((Scheme.Modules.restrictAdjunction (A.obj.relativeProjCover.f U)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction
        (Proj.map (A.pullbackGradedSectionsGradedHom g hV)
          (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2)))).homEquiv _ _).symm
      ((A.obj.relativeProjTwistingSheafGlueData n).π U ≫
        (Scheme.Modules.pushforward (A.obj.relativeProjCover.f U)).map
          (Proj.twistingSheafMap (A.pullbackGradedSectionsGradedHom g hV)
            (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2) n))) := by
  let D := A.obj.relativeProjTwistingSheafGlueData n
  have hU : IsIso (((Scheme.Modules.restrictAdjunction (A.obj.relativeProjCover.f U)).homEquiv
      D.glued (D.obj U)).symm (D.π U)) := by
    have := D.isIso_restrictGluedHom (A.obj.bijective_relativeProjTwistingSheafGlueData_map_app n) U
    rw [D.restrictGluedHom_eq] at this
    exact this
  have hP : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction
      (Proj.map (A.pullbackGradedSectionsGradedHom g hV)
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2))).homEquiv (D.obj U)
          _).symm (Proj.twistingSheafMap (A.pullbackGradedSectionsGradedHom g hV)
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2) n)) :=
    (congrArg IsIso (Proj.pullbackTwistingSheafMap_eq _ _ n)).mp
      (isIso_pullbackTwistingSheafMap_pullbackGradedSectionsGradedHom g A hV U.2 V.2 n)
  exact (congrArg IsIso (Adjunction.comp_homEquiv_symm_comp_map
    (Scheme.Modules.restrictAdjunction (A.obj.relativeProjCover.f U))
    (Scheme.Modules.pullbackPushforwardAdjunction (Proj.map (A.pullbackGradedSectionsGradedHom g hV)
      (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2))) (D.π U)
    (Proj.twistingSheafMap (A.pullbackGradedSectionsGradedHom g hV)
      (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2) n))).mpr
    (IsIso.comp_isIso' (Functor.map_isIso _ _) hP)

end GradedQuasicoherentAlgebra

end TauCeti.AlgebraicGeometry
