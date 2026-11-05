/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Comparison
public import TauCeti.CategoryTheory.Functor.Flat
public import TauCeti.CategoryTheory.Sites.ConstantSheaf

/-!
# The comparison morphisms from the big sites of a scheme to its small étale site

The inclusion `Scheme.Etale.forget X : X.Etale ⥤ Over X` of the small étale site of a scheme `X`
into its big étale site is continuous and representably flat, so it induces a morphism of topoi
`π_X : Sh((Sch/X)_ét) ⥤ Sh(X_ét)`, given here through its exact inverse image `piX X A`, the
étale sheafification of the left Kan extension of a sheaf on `X_ét`; it sends constant sheaves to
constant sheaves. Composing with the inverse
image `ε⁻¹ = epsilonFppfEtale X A` from the big étale site to the big fppf site gives the inverse
image `aX X A` of the morphism of topoi `a_X : Sh((Sch/X)_fppf) ⥤ Sh(X_ét)` (Stacks, Section 59.100
(0DDK)).

## Main declarations

* `AlgebraicGeometry.Scheme.coverPreserving_etaleForget`: étale coverings in `X.Etale` are étale
  coverings of schemes over `X`.
* `AlgebraicGeometry.Scheme.piX`, `piXAdjunction`: the inverse image of `π_X` and its adjunction
  with the direct image, which restricts a big étale sheaf to the small étale site.
* `AlgebraicGeometry.Scheme.aX`, `aXAdjunction`: the inverse image of `a_X` and its adjunction with
  the direct image.
* `AlgebraicGeometry.Scheme.constantSheafCompPiXIso`, `constantSheafCompAXIso`: `π_X⁻¹` and `a_X⁻¹`
  send constant sheaves to constant sheaves.

## References

* [Stacks Project, Section 59.100 (0DDK)](https://stacks.math.columbia.edu/tag/0DDK)
-/

public section

open CategoryTheory Limits GrothendieckTopology

universe w w' u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The inclusion of the small étale site of `X` into its big étale site sends étale coverings to
étale coverings. -/
theorem coverPreserving_etaleForget :
    CoverPreserving X.smallEtaleTopology (etaleTopology.over X) (Etale.forget X) := by
  have : MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Etale :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  exact @Functor.coverPreserving_restrictedTopology _ _ _ _ (Etale.forget X) (etaleTopology.over X)
    (locallyCoverDense_of_le X le_rfl) _ _

/-- The inclusion of the small étale site of `X` into its big étale site is representably flat,
since it preserves finite limits. -/
instance : RepresentablyFlat (Etale.forget X) :=
  flat_of_preservesFiniteLimits _

/-- The inclusion of the small étale site of `X` into its big étale site is continuous. -/
instance : (Etale.forget X).IsContinuous X.smallEtaleTopology (etaleTopology.over X) :=
  Functor.isContinuous_iff_coverPreserving.mpr (coverPreserving_etaleForget X)

section

variable (A : Type w) [Category.{w'} A]
  [∀ F : X.Etaleᵒᵖ ⥤ A, (Etale.forget X).op.HasLeftKanExtension F]

section Etale

variable [HasWeakSheafify (etaleTopology.over X) A]

/-- The inverse image of the morphism of topoi `π_X` from the big étale site to the small étale
site of `X`: the pullback of sheaves along the inclusion `X.Etale ⥤ Over X`. -/
noncomputable def piX : Sheaf X.smallEtaleTopology A ⥤ Sheaf (etaleTopology.over X) A :=
  (Etale.forget X).sheafPullback A _ _

/-- The inverse image `π_X⁻¹` is left adjoint to the direct image, which restricts a sheaf on the
big étale site to the small étale site. -/
noncomputable def piXAdjunction :
    piX X A ⊣ (Etale.forget X).sheafPushforwardContinuous A _ (etaleTopology.over X) :=
  (Etale.forget X).sheafAdjunctionContinuous A _ _

instance : (piX X A).IsLeftAdjoint :=
  (piXAdjunction X A).isLeftAdjoint

/-- The inverse image `π_X⁻¹` sends the constant sheaf on the small étale site to the constant
sheaf on the big étale site. -/
noncomputable def constantSheafCompPiXIso [HasWeakSheafify X.smallEtaleTopology A] :
    constantSheaf _ A ⋙ piX X A ≅ constantSheaf _ A :=
  have := final_of_representablyFlat (Etale.forget X)
  (Etale.forget X).constantSheafCompSheafPullbackIso A _ _

end Etale

variable [HasWeakSheafify (etaleTopology.over X) A] [HasWeakSheafify (fppfTopology.over X) A]

/-- The inverse image of the morphism of topoi `a_X` from the big fppf site to the small étale
site of `X`: the composite of `π_X⁻¹` and `ε⁻¹`. Stacks, Section 59.100 (0DDK). -/
noncomputable def aX : Sheaf X.smallEtaleTopology A ⥤ Sheaf (fppfTopology.over X) A :=
  piX X A ⋙ epsilonFppfEtale X A

/-- The inverse image `a_X⁻¹` is left adjoint to the direct image, which regards a sheaf on the big
fppf site as a sheaf on the big étale site and restricts it to the small étale site. -/
noncomputable def aXAdjunction :
    aX X A ⊣ sheafDirectImageOfLE A (etaleTopology_over_le_fppfTopology_over X) ⋙
      (Etale.forget X).sheafPushforwardContinuous A _ (etaleTopology.over X) :=
  (piXAdjunction X A).comp (epsilonFppfEtaleAdjunction X A)

instance : (aX X A).IsLeftAdjoint :=
  (aXAdjunction X A).isLeftAdjoint

/-- The inverse image `a_X⁻¹` sends the constant sheaf on the small étale site to the constant
sheaf on the big fppf site. -/
noncomputable def constantSheafCompAXIso [HasWeakSheafify X.smallEtaleTopology A] :
    constantSheaf _ A ⋙ aX X A ≅ constantSheaf _ A :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (constantSheafCompPiXIso X A) _ ≪≫
    constantSheafCompEpsilonFppfEtaleIso X A

end

section Exact

variable (A : Type w) [Category.{u + 1} A] {FA : A → A → Type*} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] [HasFiniteLimits A]
  [HasColimitsOfSize.{u, u + 1} A] [PreservesFiniteLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u + 1} (CategoryTheory.forget A)]
  [HasSheafify X.smallEtaleTopology A] [HasSheafify (etaleTopology.over X) A]

/-- The inverse image `π_X⁻¹` is exact. -/
instance : PreservesFiniteLimits (piX X A) := by
  dsimp only [piX]
  infer_instance

/-- The inverse image `a_X⁻¹` is exact. -/
instance [HasSheafify (fppfTopology.over X) A] : PreservesFiniteLimits (aX X A) := by
  dsimp only [aX]
  infer_instance

end Exact

end AlgebraicGeometry.Scheme
