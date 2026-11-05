/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.SmallEtaleBaseChange
public import TauCeti.CategoryTheory.Sites.InverseImageOfLE
public import TauCeti.Lookahead.EpsilonFppfEtale.Stubs

/-!
# The comparison morphism from the small étale site to the small Nisnevich site

On the category `X.Etale` of schemes étale over a scheme `X`, the small étale topology is finer
than the small Nisnevich topology, so the identity functor induces a morphism of topoi
`Sh(X_ét) ⥤ Sh(X_Nis)`. It is given here through its inverse image `etaleToNisnevich X A`, the
étale sheafification of a Nisnevich sheaf with values in `A`. The inverse image is left adjoint to
the direct image, which regards an étale sheaf as a Nisnevich sheaf; it is exact, it sends
constant sheaves to constant sheaves, and it commutes with the pullbacks of sheaves along the base
change functor `Etale.pullback g` of a morphism `g : Y ⟶ X`.

## Main declarations

* `AlgebraicGeometry.Scheme.etaleToNisnevich`: the inverse image from Nisnevich sheaves to étale
  sheaves.
* `AlgebraicGeometry.Scheme.etaleToNisnevichAdjunction`: its adjunction with the direct image.
* `AlgebraicGeometry.Scheme.constantSheafCompEtaleToNisnevichIso`: it sends constant sheaves to
  constant sheaves.
* `AlgebraicGeometry.Scheme.coverPreserving_etalePullback_smallNisnevichTopology`: base change
  preserves Nisnevich coverings.
* `AlgebraicGeometry.Scheme.etaleToNisnevichBaseChangeIso`: the inverse image commutes with base
  change.

## References

* F. Morel and V. Voevodsky, *𝔸¹-homotopy theory of schemes*, Publ. Math. IHÉS 90 (1999), §3.1.
-/

public section

open CategoryTheory Limits GrothendieckTopology

universe w w' u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (A : Type w) [Category.{w'} A]

variable [HasWeakSheafify X.smallEtaleTopology A]

/-- The inverse image of the morphism of topoi from the small étale site to the small Nisnevich
site of `X`: the étale sheafification of a Nisnevich sheaf. -/
noncomputable def etaleToNisnevich :
    Sheaf (smallNisnevichTopology X) A ⥤ Sheaf X.smallEtaleTopology A :=
  sheafInverseImage _ _ A

/-- The inverse image of a Nisnevich sheaf is its étale sheafification. -/
@[simp]
lemma etaleToNisnevich_obj (F : Sheaf (smallNisnevichTopology X) A) :
    (etaleToNisnevich X A).obj F = (presheafToSheaf _ A).obj F.obj :=
  (rfl)

/-- The inverse image from Nisnevich sheaves to étale sheaves is left adjoint to the direct image,
which regards an étale sheaf as a Nisnevich sheaf. -/
noncomputable def etaleToNisnevichAdjunction :
    etaleToNisnevich X A ⊣
      sheafDirectImageOfLE A (smallNisnevichTopology_le_smallEtaleTopology X) :=
  sheafAdjunctionOfLE A _

instance : (etaleToNisnevich X A).IsLeftAdjoint :=
  (etaleToNisnevichAdjunction X A).isLeftAdjoint

/-- The inverse image from Nisnevich sheaves to étale sheaves is exact. -/
instance [HasFiniteLimits A] [HasSheafify X.smallEtaleTopology A] :
    PreservesFiniteLimits (etaleToNisnevich X A) := by
  dsimp only [etaleToNisnevich]
  infer_instance

/-- The inverse image from Nisnevich sheaves to étale sheaves sends the constant Nisnevich sheaf
to the constant étale sheaf. -/
noncomputable def constantSheafCompEtaleToNisnevichIso
    [HasWeakSheafify (smallNisnevichTopology X) A] :
    constantSheaf _ A ⋙ etaleToNisnevich X A ≅ constantSheaf _ A :=
  constantSheafCompSheafInverseImageIso A (smallNisnevichTopology_le_smallEtaleTopology X)

section BaseChange

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X)

/-- Base change along `g : Y ⟶ X` sends Nisnevich coverings in `X.Etale` to Nisnevich coverings
in `Y.Etale`. -/
theorem coverPreserving_etalePullback_smallNisnevichTopology :
    CoverPreserving X.smallNisnevichTopology Y.smallNisnevichTopology (Etale.pullback g) where
  cover_preserve {W R} hR := by
    obtain ⟨ι, Z, f, rfl⟩ := R.exists_eq_ofArrows
    rw [ofArrows_mem_smallNisnevichTopology_iff] at hR
    rw [Sieve.functorPushforward_ofArrows, ofArrows_mem_smallNisnevichTopology_iff]
    exact hR.of_isPullback (pullback.fst W.hom g) _ _
      fun i ↦ Etale.isPullback_pullback_map_left g (f i)

instance : (Etale.pullback g).IsContinuous X.smallNisnevichTopology Y.smallNisnevichTopology :=
  Functor.isContinuous_iff_coverPreserving.mpr
    (coverPreserving_etalePullback_smallNisnevichTopology g)

/-- **The comparison from étale to Nisnevich sheaves commutes with base change**: for
`g : Y ⟶ X`, the inverse image from Nisnevich to étale sheaves followed by the pullback of étale
sheaves along `g` is the pullback of Nisnevich sheaves along `g` followed by the inverse image
from Nisnevich to étale sheaves. -/
noncomputable def etaleToNisnevichBaseChangeIso [HasWeakSheafify Y.smallEtaleTopology A]
    [HasWeakSheafify Y.smallNisnevichTopology A]
    [∀ F : X.Etaleᵒᵖ ⥤ A, (Etale.pullback g).op.HasLeftKanExtension F] :
    etaleToNisnevich X A ⋙ (Etale.pullback g).sheafPullback A _ Y.smallEtaleTopology ≅
      (Etale.pullback g).sheafPullback A _ Y.smallNisnevichTopology ⋙ etaleToNisnevich Y A :=
  sheafInverseImageCompSheafPullbackIso A (Etale.pullback g)
    (smallNisnevichTopology_le_smallEtaleTopology X)
    (smallNisnevichTopology_le_smallEtaleTopology Y)

end BaseChange

end AlgebraicGeometry.Scheme
