/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import TauCeti.AlgebraicGeometry.Sites.Big.StructureSheaf
import TauCeti.AlgebraicGeometry.Sites.CohomologyComparison
import TauCeti.AlgebraicGeometry.Sites.Comparison
import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Cohomology
import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Comparison
import TauCeti.AlgebraicGeometry.Sites.SmallEtaleComparison

/-!
# Checks for the comparison morphisms between the topologies of a scheme

The comparison of the small étale topology with itself is the identity, the inverse image
`ε⁻¹` from big étale to big fppf abelian sheaves is exact, preserves the constant sheaf `ℤ/2`,
and commutes with base change, the inverse image from Nisnevich to étale abelian sheaves is exact
and commutes with base change, and the inverse image `a_X⁻¹` from small étale to big fppf
abelian sheaves is exact and preserves the constant sheaf `ℤ/2`. On cohomology, the pullback along
`a_X` is the pullback along `π_X` followed by the pullback along `ε`, the pullback along `ε` is
bijective in degree zero on `𝔾_a` and `𝔾_m`, the pullback from the small Nisnevich to the small
étale site is bijective in degree zero on the restriction of `𝔾_a`, and the pullbacks from the
Zariski site to the small Nisnevich and étale sites compose.
-/

open CategoryTheory Limits AlgebraicGeometry GrothendieckTopology Scheme

universe u

namespace TauCeti.Examples

-- The étale-to-étale comparison is the identity.
noncomputable example (X : Scheme.{u}) :
    sheafInverseImage X.smallEtaleTopology X.smallEtaleTopology AddCommGrpCat.{u} ≅ 𝟭 _ :=
  sheafInverseImageRefl _ _

-- `ε⁻¹` of the constant étale sheaf `ℤ/2` is the constant fppf sheaf `ℤ/2`.
noncomputable example (X : Scheme.{u}) :
    (epsilonFppfEtale X AddCommGrpCat.{u + 1}).obj
        ((constantSheaf _ _).obj (AddCommGrpCat.of (ULift (ZMod 2)))) ≅
      (constantSheaf _ _).obj (AddCommGrpCat.of (ULift (ZMod 2))) :=
  (constantSheafCompEpsilonFppfEtaleIso X AddCommGrpCat.{u + 1}).app _

-- `ε⁻¹` is exact on abelian sheaves.
example (X : Scheme.{u}) : PreservesFiniteLimits (epsilonFppfEtale X AddCommGrpCat.{u + 1}) :=
  inferInstance

-- `ε⁻¹` commutes with restriction along `Y ⟶ X` on abelian sheaves.
noncomputable example {X Y : Scheme.{u}} (g : Y ⟶ X) :
    epsilonFppfEtale X AddCommGrpCat.{u + 1} ⋙
        Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} g ≅
      Scheme.etaleTopology.overMapPullback AddCommGrpCat.{u + 1} g ⋙
        epsilonFppfEtale Y AddCommGrpCat.{u + 1} :=
  epsilonFppfEtaleBaseChangeIso X AddCommGrpCat.{u + 1} g

-- The inverse image from Nisnevich to étale abelian sheaves is exact.
example (X : Scheme.{u}) : PreservesFiniteLimits (etaleToNisnevich X AddCommGrpCat.{u}) :=
  inferInstance

-- The inverse image from Nisnevich to étale abelian sheaves commutes with base change along
-- `Y ⟶ X`.
noncomputable example {X Y : Scheme.{u}} (g : Y ⟶ X) :
    etaleToNisnevich X AddCommGrpCat.{u + 1} ⋙
        (Etale.pullback g).sheafPullback AddCommGrpCat.{u + 1} _ Y.smallEtaleTopology ≅
      (Etale.pullback g).sheafPullback AddCommGrpCat.{u + 1} _ Y.smallNisnevichTopology ⋙
        etaleToNisnevich Y AddCommGrpCat.{u + 1} :=
  etaleToNisnevichBaseChangeIso AddCommGrpCat.{u + 1} g

-- `test_aX_constant`: `a_X⁻¹` of the constant étale sheaf `ℤ/2` is the constant fppf sheaf `ℤ/2`.
noncomputable example (X : Scheme.{u}) :
    (aX X AddCommGrpCat.{u + 1}).obj
        ((constantSheaf _ _).obj (AddCommGrpCat.of (ULift (ZMod 2)))) ≅
      (constantSheaf _ _).obj (AddCommGrpCat.of (ULift (ZMod 2))) :=
  (constantSheafCompAXIso X AddCommGrpCat.{u + 1}).app _

-- `a_X⁻¹` is exact on abelian sheaves.
example (X : Scheme.{u}) : PreservesFiniteLimits (aX X AddCommGrpCat.{u + 1}) :=
  inferInstance

-- `a_X⁻¹` commutes with base change along `Y ⟶ X` on abelian sheaves.
noncomputable example {X Y : Scheme.{u}} (g : Y ⟶ X) :
    aX X AddCommGrpCat.{u + 1} ⋙ Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} g ≅
      (Etale.pullback g).sheafPullback AddCommGrpCat.{u + 1} _ Y.smallEtaleTopology ⋙
        aX Y AddCommGrpCat.{u + 1} :=
  aXBaseChangeIso g AddCommGrpCat.{u + 1}

-- The sections of `π_X⁻¹ F` over `h : T ⟶ X` are `Γ(T_ét, h⁻¹ F)`, for abelian sheaves `F`.
noncomputable example {X T : Scheme.{u}} (h : T ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((piX X AddCommGrpCat.{u + 1}).obj F).obj.obj (Opposite.op (Over.mk h)) ≅
      (((Etale.pullback h).sheafPullback AddCommGrpCat.{u + 1} _ T.smallEtaleTopology).obj
        F).obj.obj (Opposite.op (Etale.mk (𝟙 T))) :=
  piXObjIso h AddCommGrpCat.{u + 1} F

-- The pullback of cohomology `Hⁿ(X_ét, F) → Hⁿ((Sch/X)_fppf, a_X⁻¹ F)` along `a_X` is the
-- pullback along `π_X` followed by the pullback along `ε`.
example (X : Scheme.{u}) [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (x : F.H n) :
    aXH X F n x =
      epsilonFppfEtaleH X ((piX X AddCommGrpCat.{u + 1}).obj F) n (piXH X F n x) :=
  aXH_apply X F n x

-- In degree zero, the pullback of cohomology along `π_X` is bijective.
example (X : Scheme.{u}) [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective (piXH X F 0) :=
  piXH_zero_bijective X F

-- In degree zero, the pullback of cohomology along `ε` is bijective on `𝔾_a` and on `𝔾_m`.
example (X : Scheme.{u}) [HasSheafify (etaleTopology.over X) AddCommGrpCat.{u}]
    [HasSheafify (fppfTopology.over X) AddCommGrpCat.{u}]
    [HasExt.{u + 1} (Sheaf (etaleTopology.over X) AddCommGrpCat.{u})]
    [HasExt.{u + 1} (Sheaf (fppfTopology.over X) AddCommGrpCat.{u})] :
    Function.Bijective (epsilonFppfEtaleH X ((sheafDirectImageOfLE AddCommGrpCat.{u}
        ((etaleTopology_over_le_fppfTopology_over X).trans
          (fppfTopology_over_le_fpqcTopology_over X))).obj (Ga X)) 0) ∧
      Function.Bijective (epsilonFppfEtaleH X ((sheafDirectImageOfLE AddCommGrpCat.{u}
        ((etaleTopology_over_le_fppfTopology_over X).trans
          (fppfTopology_over_le_fpqcTopology_over X))).obj (Gm X)) 0) :=
  ⟨epsilonFppfEtaleH_zero_bijective_of_fpqc X (Ga X),
    epsilonFppfEtaleH_zero_bijective_of_fpqc X (Gm X)⟩

-- In degree zero, the pullback of cohomology from the small Nisnevich site to the small étale
-- site is bijective on the restriction of `𝔾_a` to the small étale site.
example (X : Scheme.{u}) [HasSheafify X.smallNisnevichTopology AddCommGrpCat.{u}]
    [HasExt.{u + 1} (Sheaf X.smallNisnevichTopology AddCommGrpCat.{u})]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    Function.Bijective (etaleToNisnevichH X ((sheafDirectImageOfLE AddCommGrpCat.{u}
      (smallNisnevichTopology_le_smallEtaleTopology X)).obj
        ((Etale.forget X).sheafPushforwardContinuous AddCommGrpCat.{u} X.smallEtaleTopology
          (etaleTopology.over X) |>.obj ((sheafDirectImageOfLE AddCommGrpCat.{u}
            ((etaleTopology_over_le_fppfTopology_over X).trans
              (fppfTopology_over_le_fpqcTopology_over X))).obj (Ga X)))) 0) :=
  etaleToNisnevichH_zero_bijective_of_etale X _

-- In degree zero, the pullback of cohomology from the Zariski site to the small Nisnevich site is
-- injective on the restriction of `𝔾_a` to the Zariski site.
example (X : Scheme.{u}) [HasSheafify X.smallNisnevichTopology AddCommGrpCat.{u}]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    [HasExt.{u + 1} (Sheaf X.smallNisnevichTopology AddCommGrpCat.{u})] :
    Function.Injective (nisnevichToZariskiH X
      ((X.restrictEtaleFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) X.smallNisnevichTopology).obj
        ((sheafDirectImageOfLE AddCommGrpCat.{u}
          (smallNisnevichTopology_le_smallEtaleTopology X)).obj
            ((Etale.forget X).sheafPushforwardContinuous AddCommGrpCat.{u} X.smallEtaleTopology
              (etaleTopology.over X) |>.obj ((sheafDirectImageOfLE AddCommGrpCat.{u}
                ((etaleTopology_over_le_fppfTopology_over X).trans
                  (fppfTopology_over_le_fpqcTopology_over X))).obj (Ga X))))) 0) :=
  nisnevichToZariskiH_zero_injective X
    ((sheafDirectImageOfLE AddCommGrpCat.{u}
      (smallNisnevichTopology_le_smallEtaleTopology X)).obj
        ((Etale.forget X).sheafPushforwardContinuous AddCommGrpCat.{u} X.smallEtaleTopology
          (etaleTopology.over X) |>.obj ((sheafDirectImageOfLE AddCommGrpCat.{u}
            ((etaleTopology_over_le_fppfTopology_over X).trans
              (fppfTopology_over_le_fpqcTopology_over X))).obj (Ga X))))

-- The pullback of cohomology from the Zariski site to the small Nisnevich site, followed by the
-- pullback to the small étale site, is the pullback from the Zariski site to the small étale site.
example (X : Scheme.{u}) [HasSheafify X.smallNisnevichTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf X.smallNisnevichTopology AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) (x : F.H n) :
    Sheaf.H.map ((nisnevichToZariskiCompEtaleToNisnevichIso X _).hom.app F) n
        (etaleToNisnevichH X _ n (nisnevichToZariskiH X F n x)) =
      Sheaf.H.pullback (X.restrictEtaleFunctor.sheafPullback AddCommGrpCat.{u} _
        X.smallEtaleTopology) (X.restrictEtaleFunctor.sheafPullbackConstantSheafIso
          AddCommGrpCat.{u} _ X.smallEtaleTopology (AddCommGrpCat.of (ULift ℤ))).inv F n x :=
  map_etaleToNisnevichH_nisnevichToZariskiH X F n x

end TauCeti.Examples
