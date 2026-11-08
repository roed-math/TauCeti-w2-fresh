/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Support.Sheaf.Basic
public import TauCeti.CategoryTheory.Abelian.RightDerived.Adapted
public import TauCeti.Topology.Sheaves.LocalCohomology.Derived
import TauCeti.AlgebraicGeometry.Cohomology.Flasque
import TauCeti.Topology.Sheaves.Flasque.Locality

/-!
# Forgetting scalars in derived supported sections

The underlying abelian sheaf of the right derived supported-subsheaf functor
agrees, in every degree and naturally in the coefficient module, with the right
derived supported-section functor on abelian sheaves. The comparison uses that
injective module sheaves are flasque; it does not require their underlying
abelian sheaves to be injective.

The sheafification of the presheaf of relative-Ext supported cohomology groups
therefore also computes the underlying abelian local cohomology sheaf in every
degree.

## References

* The Stacks Project, Cohomology of Sheaves, Sections 20.21 and 20.34.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X : Scheme.{u}} (Z : Closeds X)

/-- Forgetting scalars commutes with every right derived supported-section
functor, naturally in the module sheaf. -/
def localCohomologySheafForgetIso (q : ℕ) :
    (supportedSubsheafFunctor Z).rightDerived q ⋙ toSheaf X ≅
      toSheaf X ⋙ (Sheaf.supportedSectionsFunctor Z).rightDerived q :=
  rightDerivedCompIsoOfAdapted (supportedSubsheafFunctor Z) (toSheaf X) (toSheaf X)
    (Sheaf.supportedSectionsFunctor Z) (Sheaf.isFlasque X.toTopCat AddCommGrpCat.{u})
    (fun F hF ↦ by
      have := hF
      exact Sheaf.isFlasque_iff.2 (TauCeti.Topology.isFlasque_of_injective F))
    (fun S hS h₁ h₂ ↦ by
      have := Sheaf.isFlasque_iff.1 h₁
      have := Sheaf.isFlasque_iff.1 h₂
      exact Sheaf.isFlasque_iff.2 (TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS))
    (fun S hS h₁ _ ↦ by
      have := Sheaf.isFlasque_iff.1 h₁
      exact Sheaf.shortExact_map_supportedSectionsFunctor Z hS
        (Sheaf.isZero_supportedHSheaf_succ_of_isFlasque S.X₁ Z 0))
    (fun M hM ↦ by
      have := hM
      exact Sheaf.isFlasque_iff.2
        (inferInstanceAs (TopCat.Presheaf.IsFlasque M.presheaf)))
    (supportedSubsheafFunctorForgetIso Z) q

/-- The all-degree forgetful comparison commutes with coefficient maps. -/
@[reassoc]
lemma localCohomologySheafForgetIso_hom_naturality {M N : X.Modules} (f : M ⟶ N) (q : ℕ) :
    (toSheaf X).map (((supportedSubsheafFunctor Z).rightDerived q).map f) ≫
        (localCohomologySheafForgetIso Z q).hom.app N =
      (localCohomologySheafForgetIso Z q).hom.app M ≫
        ((Sheaf.supportedSectionsFunctor Z).rightDerived q).map ((toSheaf X).map f) :=
  (localCohomologySheafForgetIso Z q).hom.naturality f

/-- The underlying abelian local cohomology sheaf of a module agrees in every
degree with the sheafification of its supported relative-Ext cohomology presheaf. -/
def toSheafLocalCohomologySheafIso (M : X.Modules) (q : ℕ) :
    (toSheaf X).obj (localCohomologySheaf Z M q) ≅
      ((toSheaf X).obj M).supportedHSheaf Z q :=
  (localCohomologySheafForgetIso Z q).app M ≪≫
    rightDerivedSupportedSectionsIsoSheaf Z (injectiveResolution ((toSheaf X).obj M)) q

end

end TauCeti.AlgebraicGeometry.Scheme.Modules
