/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.PullbackBaseChange
public import TauCeti.AlgebraicGeometry.RelativeProj.BaseChangeTwistingSheaf
public import TauCeti.AlgebraicGeometry.Modules.Restriction.Cover
public import TauCeti.CategoryTheory.Adjunction.HomEquiv

/-!
# Base change of the relative `Proj`, compatibly with the twisting sheaves

Let `g : X ⟶ Y` be a morphism of schemes, `A` a graded quasicoherent algebra on `Y`, and
`h = relativeProjPullbackHom g A : Proj_X(g^* A) ⟶ Proj_Y(A)` the projection of the relative `Proj`
of the pulled-back graded algebra, which exhibits `Proj_X(g^* A)` as the base change of `Proj_Y(A)`
along `g` (`GradedQuasicoherentAlgebra.isPullback_relativeProjPullbackHom`). We show that the
comparison `h^* 𝒪_A(n) ⟶ 𝒪_{g^* A}(n)` of twisting sheaves is an isomorphism for every `n ∈ ℤ`.

For affine opens `U` of `Y` and `V ≤ g⁻¹ U` of `X`, the chart `Proj (⨁ n, Γ(g^* Aₙ, V))` maps to the
chart `Proj (⨁ n, Γ(Aₙ, U))` by `Proj.map` of the pullback of sections, a base change of graded
rings (`GradedQuasicoherentAlgebra.isBaseChange_pullbackGradedSections`), so the twisting sheaves of
the charts pull back to each other
(`GradedQuasicoherentAlgebra.isIso_pullbackTwistingSheafMap_pullbackGradedSectionsGradedHom`, from
`AlgebraicGeometry.Proj.isIso_pullbackTwistingSheafMap_of_isBaseChange`). The chart comparison
`relativeProjTwistingSheafChartHom` factors through the two factorizations
`ι_V ≫ h = Proj.map ≫ ι_U` of the pushforward, so the comparison is an isomorphism over each chart
(`CategoryTheory.Adjunction.isIso_map_of_comp_eq_homEquiv_symm`), and these charts cover
`Proj_X(g^* A)`.

## Main results

* `GradedQuasicoherentAlgebra.isIso_pullbackTwistingSheafMap_pullbackGradedSectionsGradedHom`:
  the comparison `(Proj.map)^* 𝒪(n) ⟶ 𝒪(n)` between the twisting sheaves of the charts is an
  isomorphism.
* `GradedQuasicoherentAlgebra.relativeProjPullbackTwistingSheafIso`: the isomorphism
  `h^* 𝒪_A(n) ≅ 𝒪_{g^* A}(n)`.
* `GradedQuasicoherentAlgebra.relativeProj_baseChange`: formation of the relative `Proj` commutes
  with base change, with homogeneous components `g^* Aₖ` (degree zero included), compatibly with
  the twisting sheaves `𝒪(n)`.

## Implementation notes

The inputs of `CategoryTheory.Adjunction.isIso_map_of_comp_eq_homEquiv_symm` are stated with the
twisting sheaves of the relative `Proj` and of the charts spelled out, and its implicit objects are
given explicitly: the kernel compares a projection of the gluing datum of twisting sheaves with the
twisting sheaf of a chart cheaply as objects, but not inside a transpose along an adjunction.

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
      Scheme.Modules.pushforward (((pullback g).obj A).obj.relativeProjCover.f V) ⋙
        Scheme.Modules.pushforward (relativeProjPullbackHom g A) :=
  Scheme.Modules.pushforwardComp _ _ ≪≫
    Scheme.Modules.pushforwardCongr (relativeProjCover_f_relativeProjPullbackHom g A V U hV).symm ≪≫
    (Scheme.Modules.pushforwardComp _ _).symm

/-- The chart comparison is the projection to the chart over `U` followed by the map of twisting
sheaves of the charts, transported along `chartPushforwardIso`. The objects are spelled as in
`Adjunction.isIso_map_of_comp_eq_homEquiv_symm`, with the twisting sheaves of the charts written
out. -/
private theorem relativeProjTwistingSheafChartHom_eq_comp {V : X.AffineZariskiSite}
    {U : Y.AffineZariskiSite} (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    A.relativeProjTwistingSheafChartHom g n hV =
      CategoryStruct.comp (X := A.obj.relativeProjTwistingSheaf n)
        (Y := (Scheme.Modules.pushforward (A.obj.relativeProjCover.f U)).obj
          ((Scheme.Modules.pushforward (Proj.map (A.pullbackGradedSectionsGradedHom g hV)
            (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2))).obj
              (Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n)))
        (Z := (Scheme.Modules.pushforward (relativeProjPullbackHom g A)).obj
          ((Scheme.Modules.pushforward (((pullback g).obj A).obj.relativeProjCover.f V)).obj
            (Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n)))
        (CategoryStruct.comp (X := A.obj.relativeProjTwistingSheaf n)
          (Y := (Scheme.Modules.pushforward (A.obj.relativeProjCover.f U)).obj
            (Proj.twistingSheaf (A.obj.gradedSectionsGrading U.toOpens) n))
          ((A.obj.relativeProjTwistingSheafGlueData n).π U)
          ((Scheme.Modules.pushforward (A.obj.relativeProjCover.f U)).map
            (Proj.twistingSheafMap (A.pullbackGradedSectionsGradedHom g hV)
              (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2) n)))
        ((chartPushforwardIso hV).hom.app
          (Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n)) := by
  -- on sections, both sides restrict the image of the projection along an `eqToHom`
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ConcreteCategory.hom_ext _ _ fun s ↦ ?_
  exact (A.relativeProjTwistingSheafChartHom_app_apply g n hV W s).trans rfl

/-- The transpose of the projection of the twisting sheaf `𝒪(n)` of a relative `Proj` to a chart,
along the restriction to that chart, is an isomorphism: it identifies the restriction of `𝒪(n)`
with the twisting sheaf of the chart. -/
private theorem isIso_homEquiv_symm_relativeProjTwistingSheafGlueData_π {Z : Scheme.{u}}
    (B : GradedQuasicoherentAlgebra Z) (W : Z.AffineZariskiSite) :
    IsIso (((Scheme.Modules.restrictAdjunction (B.obj.relativeProjCover.f W)).homEquiv
      (B.obj.relativeProjTwistingSheafGlueData n).glued
        ((B.obj.relativeProjTwistingSheafGlueData n).obj W)).symm
          ((B.obj.relativeProjTwistingSheafGlueData n).π W)) := by
  have := (B.obj.relativeProjTwistingSheafGlueData n).isIso_restrictGluedHom
    (B.obj.bijective_relativeProjTwistingSheafGlueData_map_app n) W
  rw [ModulesGlueData.restrictGluedHom_eq] at this
  exact this

/-- The transpose of the projection of `𝒪(n)` to a chart is an isomorphism, with the twisting sheaf
of the relative `Proj` and the twisting sheaf of the chart spelled out. -/
private theorem isIso_homEquiv_symm_π_twistingSheaf {Z : Scheme.{u}}
    (B : GradedQuasicoherentAlgebra Z) (W : Z.AffineZariskiSite) :
    IsIso (((Scheme.Modules.restrictAdjunction (B.obj.relativeProjCover.f W)).homEquiv
      (B.obj.relativeProjTwistingSheaf n)
        (Proj.twistingSheaf (B.obj.gradedSectionsGrading W.toOpens) n)).symm
          ((B.obj.relativeProjTwistingSheafGlueData n).π W)) :=
  -- transport along equalities of objects rather than unfolding the restriction adjunction
  Adjunction.isIso_homEquiv_symm_of_eq
    (Scheme.Modules.restrictAdjunction (B.obj.relativeProjCover.f W))
    (M := (B.obj.relativeProjTwistingSheafGlueData n).glued)
    (M' := B.obj.relativeProjTwistingSheaf n)
    (P := (B.obj.relativeProjTwistingSheafGlueData n).obj W)
    (P' := Proj.twistingSheaf (B.obj.gradedSectionsGrading W.toOpens) n) rfl rfl
    ((B.obj.relativeProjTwistingSheafGlueData n).π W)
    ((B.obj.relativeProjTwistingSheafGlueData n).π W) HEq.rfl
    (hχ := isIso_homEquiv_symm_relativeProjTwistingSheafGlueData_π n B W)

/-- The transpose of the map of twisting sheaves of the charts along `Proj.map` of the pullback
of sections is an isomorphism. -/
private theorem isIso_homEquiv_symm_twistingSheafMap {V : X.AffineZariskiSite}
    {U : Y.AffineZariskiSite} (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction
      (Proj.map (A.pullbackGradedSectionsGradedHom g hV)
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2))).homEquiv
          (Proj.twistingSheaf (A.obj.gradedSectionsGrading U.toOpens) n) _).symm
      (Proj.twistingSheafMap (A.pullbackGradedSectionsGradedHom g hV)
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2) n)) :=
  (congrArg IsIso (Proj.pullbackTwistingSheafMap_eq _ _ n)).mp
    (isIso_pullbackTwistingSheafMap_pullbackGradedSectionsGradedHom g A hV U.2 V.2 n)

/-- On the chart over `V ≤ g⁻¹ U`, the comparison of twisting sheaves is the transpose of the
projection to the chart over `U` followed by the map of twisting sheaves of the charts. -/
private theorem relativeProjPullbackTwistingSheafHom_comp_π {V : X.AffineZariskiSite}
    {U : Y.AffineZariskiSite} (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    CategoryStruct.comp
        (X := (Scheme.Modules.pullback (relativeProjPullbackHom g A)).obj
          (A.obj.relativeProjTwistingSheaf n))
        (Y := ((pullback g).obj A).obj.relativeProjTwistingSheaf n)
        (Z := (Scheme.Modules.pushforward (((pullback g).obj A).obj.relativeProjCover.f V)).obj
          (Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n))
        (relativeProjPullbackTwistingSheafHom g A n)
        ((((pullback g).obj A).obj.relativeProjTwistingSheafGlueData n).π V) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (relativeProjPullbackHom g A)).homEquiv
        (A.obj.relativeProjTwistingSheaf n)
          ((Scheme.Modules.pushforward (((pullback g).obj A).obj.relativeProjCover.f V)).obj
            (Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n))).symm
        (CategoryStruct.comp (X := A.obj.relativeProjTwistingSheaf n)
          (Y := (Scheme.Modules.pushforward (A.obj.relativeProjCover.f U)).obj
            ((Scheme.Modules.pushforward (Proj.map (A.pullbackGradedSectionsGradedHom g hV)
              (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2))).obj
                (Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n)))
          (Z := (Scheme.Modules.pushforward (relativeProjPullbackHom g A)).obj
            ((Scheme.Modules.pushforward (((pullback g).obj A).obj.relativeProjCover.f V)).obj
              (Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n)))
          (CategoryStruct.comp (X := A.obj.relativeProjTwistingSheaf n)
            (Y := (Scheme.Modules.pushforward (A.obj.relativeProjCover.f U)).obj
              (Proj.twistingSheaf (A.obj.gradedSectionsGrading U.toOpens) n))
            ((A.obj.relativeProjTwistingSheafGlueData n).π U)
            ((Scheme.Modules.pushforward (A.obj.relativeProjCover.f U)).map
              (Proj.twistingSheafMap (A.pullbackGradedSectionsGradedHom g hV)
                (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2) n)))
          ((chartPushforwardIso hV).hom.app
            (Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n))) :=
  (relativeProjPullbackTwistingSheafHom_π g A n hV).trans
    (congrArg _ (relativeProjTwistingSheafChartHom_eq_comp g A n hV))

/-- Over the chart of `Proj_X(g^* A)` above an affine open `V ≤ g⁻¹ U`, the comparison
`h^* 𝒪_A(n) ⟶ 𝒪_{g^* A}(n)` is an isomorphism: up to the identifications of the restrictions of
`𝒪(n)` with the twisting sheaves of the charts, it is the pullback of twisting sheaves along
`Proj.map` of the pullback of sections. All objects are spelled as the twisting sheaves of the
relative `Proj` and of the charts, so that the kernel compares the inputs syntactically. -/
theorem isIso_restrictFunctor_map_relativeProjPullbackTwistingSheafHom {V : X.AffineZariskiSite}
    {U : Y.AffineZariskiSite} (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    IsIso ((Scheme.Modules.restrictFunctor (((pullback g).obj A).obj.relativeProjCover.f V)).map
      (relativeProjPullbackTwistingSheafHom g A n)) :=
  Adjunction.isIso_map_of_comp_eq_homEquiv_symm
    (Scheme.Modules.restrictAdjunction (A.obj.relativeProjCover.f U))
    (Scheme.Modules.pullbackPushforwardAdjunction (Proj.map (A.pullbackGradedSectionsGradedHom g hV)
      (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2)))
    (Scheme.Modules.pullbackPushforwardAdjunction (relativeProjPullbackHom g A))
    (Scheme.Modules.restrictAdjunction (((pullback g).obj A).obj.relativeProjCover.f V))
    (chartPushforwardIso hV) (M := A.obj.relativeProjTwistingSheaf n)
    (Q := Proj.twistingSheaf (A.obj.gradedSectionsGrading U.toOpens) n)
    (P := Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n)
    (N := ((pullback g).obj A).obj.relativeProjTwistingSheaf n)
    ((A.obj.relativeProjTwistingSheafGlueData n).π U)
    (Proj.twistingSheafMap (A.pullbackGradedSectionsGradedHom g hV)
      (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2) n)
    ((((pullback g).obj A).obj.relativeProjTwistingSheafGlueData n).π V)
    (relativeProjPullbackTwistingSheafHom g A n)
    (hπU := isIso_homEquiv_symm_π_twistingSheaf n A U)
    (ht := isIso_homEquiv_symm_twistingSheafMap g A n hV)
    (hπV := isIso_homEquiv_symm_π_twistingSheaf n ((pullback g).obj A) V)
    (relativeProjPullbackTwistingSheafHom_comp_π g A n hV)

/-- **The comparison of twisting sheaves is an isomorphism**: `h^* 𝒪_A(n) ⟶ 𝒪_{g^* A}(n)` is an
isomorphism of `𝒪`-modules on `Proj_X(g^* A)`, for every `n ∈ ℤ`. It is checked on the charts over
the affine opens `V ≤ g⁻¹ U`, which cover `Proj_X(g^* A)`. -/
instance isIso_relativeProjPullbackTwistingSheafHom :
    IsIso (relativeProjPullbackTwistingSheafHom g A n) :=
  Scheme.Modules.Hom.isIso_of_isIso_restrictFunctor_map _
    (ι := {V : X.AffineZariskiSite // ∃ U : Y.AffineZariskiSite, V.toOpens ≤ g ⁻¹ᵁ U.toOpens})
    (fun V ↦ ((pullback g).obj A).obj.relativeProjCover.f V.1)
    (fun x ↦ (exists_mem_opensRange_relativeProjCover_f g A x).elim fun V ⟨hV, hx⟩ ↦
      ⟨⟨V, hV⟩, hx⟩)
    fun ⟨_, _, hV⟩ ↦ isIso_restrictFunctor_map_relativeProjPullbackTwistingSheafHom g A n hV

/-- **The twisting sheaves pull back along the base change of the relative `Proj`**: the
isomorphism `h^* 𝒪_A(n) ≅ 𝒪_{g^* A}(n)` on `Proj_X(g^* A)`, for every `n ∈ ℤ`. -/
noncomputable def relativeProjPullbackTwistingSheafIso :
    (Scheme.Modules.pullback (relativeProjPullbackHom g A)).obj
        (A.obj.relativeProjTwistingSheaf n) ≅
      ((pullback g).obj A).obj.relativeProjTwistingSheaf n :=
  asIso (relativeProjPullbackTwistingSheafHom g A n)

@[simp]
theorem relativeProjPullbackTwistingSheafIso_hom :
    (relativeProjPullbackTwistingSheafIso g A n).hom =
      relativeProjPullbackTwistingSheafHom g A n :=
  (rfl)

/-- **Formation of the relative `Proj` commutes with base change**, compatibly with the twisting
sheaves. For a morphism of schemes `g : X ⟶ Y` and a graded quasicoherent algebra `A` on `Y`, the
square formed by `h : Proj_X(g^* A) ⟶ Proj_Y(A)`, the structure morphisms and `g` is cartesian; the
homogeneous components of `g^* A`, its degree-zero part `g^* A₀` among them, are the pullbacks
`g^* Aₖ`; and the comparison `h^* 𝒪_A(n) ⟶ 𝒪_{g^* A}(n)` is an isomorphism for every `n ∈ ℤ`. -/
@[stacks 01O3]
theorem relativeProj_baseChange :
    IsPullback ((pullback g).obj A).obj.relativeProjToBase (relativeProjPullbackHom g A) g
        A.obj.relativeProjToBase ∧
      (∀ k, ((pullback g).obj A).obj.X k = (Scheme.Modules.pullback g).obj (A.obj.X k)) ∧
      ∀ n : ℤ, IsIso (relativeProjPullbackTwistingSheafHom g A n) :=
  ⟨isPullback_relativeProjPullbackHom g A, pullback_obj_obj_X g A, fun _ ↦ inferInstance⟩

end GradedQuasicoherentAlgebra

end TauCeti.AlgebraicGeometry
