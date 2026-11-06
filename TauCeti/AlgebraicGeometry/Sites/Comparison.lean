/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import TauCeti.CategoryTheory.Sites.InverseImageOfLE

/-!
# The comparison morphism from the big fppf site to the big étale site

The fppf topology on schemes is finer than the étale topology, so on the category of schemes over
a scheme `X` the identity functor induces a morphism of topoi
`ε : Sh((Sch/X)_fppf) ⥤ Sh((Sch/X)_ét)`. It is given here through its inverse image
`epsilonFppfEtale X A`, the fppf sheafification of an étale sheaf with values in `A`. The inverse
image is left adjoint to the direct image `ε_*`, which regards an fppf sheaf as an étale sheaf; it
is exact, it sends constant sheaves to constant sheaves, and it commutes with restriction along a
morphism `Y ⟶ X` (`epsilonFppfEtaleBaseChangeIso`).

## Main declarations

* `AlgebraicGeometry.Scheme.etaleTopology_le_fppfTopology`: étale coverings are fppf coverings.
* `AlgebraicGeometry.Scheme.epsilonFppfEtale`, `epsilonFppfEtaleAdjunction`: the inverse image
  of `ε` and its adjunction with the direct image.
* `AlgebraicGeometry.Scheme.epsilonFppfEtaleObjIsoOfIsSheaf`: `ε⁻¹` does not change an étale
  sheaf that is already an fppf sheaf.
* `AlgebraicGeometry.Scheme.constantSheafCompEpsilonFppfEtaleIso`: `ε⁻¹` of a constant sheaf is
  constant.
* `AlgebraicGeometry.Scheme.epsilonFppfEtaleBaseChangeIso`: compatibility of `ε⁻¹` with the
  morphisms of big sites induced by `Y ⟶ X`.

## References

* [Stacks Project, Section 59.100 (0DDK)](https://stacks.math.columbia.edu/tag/0DDK)
-/

public section

open CategoryTheory Limits GrothendieckTopology

universe w w' u

namespace AlgebraicGeometry.Scheme

/-- Every étale covering is an fppf covering: étale morphisms are flat and locally of finite
presentation. -/
theorem etalePrecoverage_le_fppfPrecoverage : etalePrecoverage.{u} ≤ fppfPrecoverage :=
  precoverage_mono fun _ _ _ _ ↦ ⟨inferInstance, inferInstance⟩

/-- The étale topology is coarser than the fppf topology. -/
theorem etaleTopology_le_fppfTopology : etaleTopology.{u} ≤ fppfTopology :=
  Precoverage.toGrothendieck_mono etalePrecoverage_le_fppfPrecoverage

variable (X : Scheme.{u}) (A : Type w) [Category.{w'} A]

section Fppf

/-- The étale topology on schemes over `X` is coarser than the fppf topology. -/
theorem etaleTopology_over_le_fppfTopology_over : etaleTopology.over X ≤ fppfTopology.over X :=
  fun _ _ hS ↦ etaleTopology_le_fppfTopology _ hS

variable [HasWeakSheafify (fppfTopology.over X) A]

/-- The inverse image `ε⁻¹` of the morphism of topoi `ε` from the big fppf site to the big étale
site over `X`: the fppf sheafification of an étale sheaf. Stacks, Section 59.100 (0DDK). -/
@[expose] noncomputable def epsilonFppfEtale :
    Sheaf (etaleTopology.over X) A ⥤
      Sheaf (fppfTopology.over X) A :=
  sheafInverseImage _ _ A

/-- The inverse image `ε⁻¹` of an étale sheaf is its fppf sheafification. -/
@[simp]
lemma epsilonFppfEtale_obj (F : Sheaf (etaleTopology.over X) A) :
    (epsilonFppfEtale X A).obj F = (presheafToSheaf _ A).obj F.obj :=
  (rfl)

/-- An étale sheaf that is already an fppf sheaf is not changed by the inverse image `ε⁻¹`. -/
noncomputable def epsilonFppfEtaleObjIsoOfIsSheaf (F : Sheaf (etaleTopology.over X) A)
    (hF : Presheaf.IsSheaf (fppfTopology.over X) F.obj) :
    (epsilonFppfEtale X A).obj F ≅ ⟨F.obj, hF⟩ :=
  sheafInverseImageObjIsoOfIsSheaf A (etaleTopology_over_le_fppfTopology_over X) F hF

/-- The inverse image `ε⁻¹` is left adjoint to the direct image `ε_*`, which regards an fppf
sheaf as an étale sheaf. -/
@[expose] noncomputable def epsilonFppfEtaleAdjunction :
    epsilonFppfEtale X A ⊣ sheafDirectImageOfLE A (etaleTopology_over_le_fppfTopology_over X) :=
  sheafAdjunctionOfLE A _

instance : (epsilonFppfEtale X A).IsLeftAdjoint :=
  (epsilonFppfEtaleAdjunction X A).isLeftAdjoint

/-- The inverse image `ε⁻¹` is exact. -/
instance [HasFiniteLimits A] [HasSheafify (fppfTopology.over X) A] :
    PreservesFiniteLimits (epsilonFppfEtale X A) := by
  dsimp only [epsilonFppfEtale]
  infer_instance

/-- The inverse image `ε⁻¹` sends the constant étale sheaf to the constant fppf sheaf. -/
@[expose] noncomputable def constantSheafCompEpsilonFppfEtaleIso
    [HasWeakSheafify (etaleTopology.over X) A] :
    constantSheaf _ A ⋙ epsilonFppfEtale X A ≅ constantSheaf _ A :=
  constantSheafCompSheafInverseImageIso A (etaleTopology_over_le_fppfTopology_over X)

/-- **The inverse image `ε⁻¹` commutes with base change**: for a morphism `g : Y ⟶ X`, restricting
an étale sheaf along `g` and then fppf-sheafifying it is restricting its fppf sheafification. -/
noncomputable def epsilonFppfEtaleBaseChangeIso {Y : Scheme.{u}} (g : Y ⟶ X)
    [HasWeakSheafify (fppfTopology.over Y) A]
    [∀ F : (Over Y)ᵒᵖ ⥤ A, (Over.map g).op.HasPointwiseRightKanExtension F] :
    epsilonFppfEtale X A ⋙ fppfTopology.overMapPullback A g ≅
      etaleTopology.overMapPullback A g ⋙ epsilonFppfEtale Y A :=
  sheafInverseImageCompSheafPushforwardContinuousIso A (Over.map g) _ _ _ _

end Fppf

end AlgebraicGeometry.Scheme
