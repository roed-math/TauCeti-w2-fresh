/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.PullbackBaseChange
public import TauCeti.AlgebraicGeometry.RelativeProj.Basic

/-!
# The charts of the relative `Proj` of a pulled-back graded algebra

Let `g : X ⟶ Y` be a morphism of schemes and `A` a graded quasicoherent algebra on `Y`. Over
affine opens `U` of `Y` and `V ≤ g⁻¹ U` of `X`, pullback of sections gives the morphism
`Proj (⨁ n, Γ(g^* Aₙ, V)) ⟶ Proj (⨁ n, Γ(Aₙ, U))` from a chart of the relative `Proj` of `g^* A`
to a chart of the relative `Proj` of `A`, which is a base change
(`GradedQuasicoherentAlgebra.isPullback_proj_pullbackGradedSections`). This file shows that these
morphisms commute with the transition maps of both relative `Proj`s, induced by restriction of
sections to basic opens. This is the naturality needed to assemble them into a morphism from the
relative `Proj` of `g^* A` to that of `A` over `g`.

## Main results

In the namespace `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra`:

* `relativeProjGluingData_functor_map_comp_proj_map`: compatibility with the transition maps of
  the relative `Proj` of `g^* A`;
* `proj_map_comp_relativeProjGluingData_functor_map`: compatibility with the transition maps of
  the relative `Proj` of `A`.

## References

* [The Stacks Project, Lemma 27.16.10](https://stacks.math.columbia.edu/tag/01O3)
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry Scheme.AffineZariskiSite

universe u

namespace GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (A : GradedQuasicoherentAlgebra Y)

/-- Restricting the pullback of sections of `A` from `V` to `V' ≤ V` is pulling them back to `V'`,
as graded ring homomorphisms. -/
theorem restrictGradedSectionsGradedHom_comp_pullbackGradedSectionsGradedHom {U : Y.Opens}
    {V V' : X.Opens} (hV : V ≤ g ⁻¹ᵁ U) (i : V' ⟶ V) :
    ((pullback g A).obj.restrictGradedSectionsGradedHom i).comp
        (A.pullbackGradedSectionsGradedHom g hV) =
      A.pullbackGradedSectionsGradedHom g ((leOfHom i).trans hV) :=
  GradedRingHom.ext fun x ↦ by
    simp [← A.restrictGradedSections_comp_pullbackGradedSections g hV i]

/-- Pulling back sections of `A` restricted from `U` to `U' ≤ U` is pulling them back from `U`,
as graded ring homomorphisms. -/
theorem pullbackGradedSectionsGradedHom_comp_restrictGradedSectionsGradedHom {U U' : Y.Opens}
    {V : X.Opens} (hV : V ≤ g ⁻¹ᵁ U) (j : U' ⟶ U) (hV' : V ≤ g ⁻¹ᵁ U') :
    (A.pullbackGradedSectionsGradedHom g hV').comp (A.obj.restrictGradedSectionsGradedHom j) =
      A.pullbackGradedSectionsGradedHom g hV :=
  GradedRingHom.ext fun x ↦ by
    simp [← A.pullbackGradedSections_comp_restrictGradedSections g hV j hV']

/-- The morphisms from the charts of the relative `Proj` of `g^* A` to the chart
`Proj (⨁ n, Γ(Aₙ, U))` commute with the transition maps of the relative `Proj` of `g^* A`. -/
@[reassoc]
theorem relativeProjGluingData_functor_map_comp_proj_map {U : Y.Opens} (hU : IsAffineOpen U)
    {V' V : X.AffineZariskiSite} (i : V' ⟶ V) (hV : V.toOpens ≤ g ⁻¹ᵁ U) :
    (pullback g A).obj.relativeProjGluingData.functor.map i ≫
        Proj.map (A.pullbackGradedSectionsGradedHom g hV)
          (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV hU V.2) =
      Proj.map (A.pullbackGradedSectionsGradedHom g ((leOfHom ((toOpensFunctor X).map i)).trans hV))
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g _ hU V'.2) := by
  rw [CommMon.relativeProjGluingData_functor_map]
  exact (Proj.map_comp ..).symm.trans (Proj.map_congr
    (A.restrictGradedSectionsGradedHom_comp_pullbackGradedSectionsGradedHom g hV _) _ _)

/-- The morphisms from a chart `Proj (⨁ n, Γ(g^* Aₙ, V))` of the relative `Proj` of `g^* A` to the
charts of the relative `Proj` of `A` commute with the transition maps of the relative `Proj`
of `A`. -/
@[reassoc]
theorem proj_map_comp_relativeProjGluingData_functor_map {U' U : Y.AffineZariskiSite} (j : U' ⟶ U)
    {V : X.Opens} (hV' : IsAffineOpen V) (hV : V ≤ g ⁻¹ᵁ U'.toOpens) :
    Proj.map (A.pullbackGradedSectionsGradedHom g hV)
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U'.2 hV') ≫
        A.obj.relativeProjGluingData.functor.map j =
      Proj.map (A.pullbackGradedSectionsGradedHom g
          (hV.trans fun _ hx ↦ leOfHom ((toOpensFunctor Y).map j) hx))
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g _ U.2 hV') := by
  rw [CommMon.relativeProjGluingData_functor_map]
  exact (Proj.map_comp ..).symm.trans (Proj.map_congr
    (A.pullbackGradedSectionsGradedHom_comp_restrictGradedSectionsGradedHom g _ _ hV) _ _)

end GradedQuasicoherentAlgebra

end TauCeti.AlgebraicGeometry
