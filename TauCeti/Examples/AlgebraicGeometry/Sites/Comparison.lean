/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import TauCeti.AlgebraicGeometry.Sites.Comparison
import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Comparison
import TauCeti.AlgebraicGeometry.Sites.SmallEtaleComparison

/-!
# Checks for the comparison morphisms between the topologies of a scheme

The comparison of the small étale topology with itself is the identity, the inverse image
`ε⁻¹` from big étale to big fppf abelian sheaves is exact, preserves the constant sheaf `ℤ/2`,
and commutes with base change, and the inverse image `a_X⁻¹` from small étale to big fppf
abelian sheaves is exact and preserves the constant sheaf `ℤ/2`.
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

-- `test_aX_constant`: `a_X⁻¹` of the constant étale sheaf `ℤ/2` is the constant fppf sheaf `ℤ/2`.
noncomputable example (X : Scheme.{u}) :
    (aX X AddCommGrpCat.{u + 1}).obj
        ((constantSheaf _ _).obj (AddCommGrpCat.of (ULift (ZMod 2)))) ≅
      (constantSheaf _ _).obj (AddCommGrpCat.of (ULift (ZMod 2))) :=
  (constantSheafCompAXIso X AddCommGrpCat.{u + 1}).app _

-- `a_X⁻¹` is exact on abelian sheaves.
example (X : Scheme.{u}) : PreservesFiniteLimits (aX X AddCommGrpCat.{u + 1}) :=
  have := hasColimitsOfSizeShrink.{u, u + 1, u + 1, 0} AddCommGrpCat.{u + 1}
  have := preservesFilteredColimitsOfSize_shrink.{u + 1, 0, u, u + 1}
    (forget AddCommGrpCat.{u + 1})
  inferInstance

end TauCeti.Examples
