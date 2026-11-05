/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Spaces
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Comparison
public import TauCeti.AlgebraicGeometry.Sites.OpensEtale
public import TauCeti.CategoryTheory.Functor.Flat
public import TauCeti.CategoryTheory.Sites.ConstantSheaf
public import TauCeti.Lookahead.EpsilonFppfEtale.Stubs

/-!
# The comparison morphism from the small Nisnevich site to the Zariski site

Zariski coverings are Nisnevich coverings, so the representably flat functor
`X.restrictEtaleFunctor : X.Opens ⥤ X.Etale` taking an open subset to the corresponding open
subscheme is continuous for the Zariski topology on `X.Opens` and the small Nisnevich topology on
`X.Etale`. It therefore induces a
morphism of topoi `Sh(X_Nis) ⥤ Sh(X_Zar)`, given here through its inverse image
`nisnevichToZariski X A`. The inverse image is left adjoint to the direct image, which restricts a
Nisnevich sheaf to the open subschemes of `X`; it is exact and it sends constant sheaves to
constant sheaves.

## Main declarations

* `AlgebraicGeometry.Scheme.coverPreserving_restrictEtaleFunctor`: it sends Zariski coverings to
  Nisnevich coverings.
* `AlgebraicGeometry.Scheme.nisnevichToZariski`, `nisnevichToZariskiAdjunction`: the inverse
  image from Zariski sheaves to Nisnevich sheaves and its adjunction with the direct image.
* `AlgebraicGeometry.Scheme.constantSheafCompNisnevichToZariskiIso`: the inverse image sends
  constant sheaves to constant sheaves.
* `AlgebraicGeometry.Scheme.nisnevichToZariskiCompEtaleToNisnevichIso`: composing with the inverse
  image from Nisnevich to étale sheaves gives the pullback from Zariski to étale sheaves.

## References

* F. Morel and V. Voevodsky, *𝔸¹-homotopy theory of schemes*, Publ. Math. IHÉS 90 (1999), §3.1.
-/

public section

open CategoryTheory Limits TopologicalSpace TauCeti.AlgebraicGeometry.Scheme

universe w w' u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- **Zariski coverings are Nisnevich coverings**: the functor from open subsets of `X` to schemes
étale over `X` sends Zariski covering sieves to covering sieves of the small Nisnevich site. -/
theorem coverPreserving_restrictEtaleFunctor :
    CoverPreserving (Opens.grothendieckTopology X) X.smallNisnevichTopology
      X.restrictEtaleFunctor where
  cover_preserve {U S} hS := by
    let Z : (Σ V : X.Opens, {i : V ⟶ U // S i}) → X.Etale :=
      fun i ↦ X.restrictEtaleFunctor.obj i.1
    let f : ∀ i, Z i ⟶ X.restrictEtaleFunctor.obj U := fun i ↦ X.restrictEtaleFunctor.map i.2.1
    refine GrothendieckTopology.superset_covering _ ?_
      ((ofArrows_mem_smallNisnevichTopology_iff f).mpr ?_)
    · rintro W g ⟨_, h, _, ⟨i⟩, rfl⟩
      exact ⟨i.1, i.2.1, h, i.2.2, rfl⟩
    · refine isNisnevichCovering_of_zariski
        ((AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun x ↦ ?_, fun i ↦ ?_⟩)
      · obtain ⟨V, i, hi, hx⟩ := hS x.1 x.2
        exact ⟨⟨V, i, hi⟩, ⟨x.1, hx⟩, Subtype.ext (Scheme.homOfLE_apply i.le ⟨x.1, hx⟩)⟩
      · exact (inferInstance : IsOpenImmersion (X.homOfLE i.2.1.le))

/-- The functor from open subsets of `X` to schemes étale over `X` is continuous for the Zariski
and the small Nisnevich topologies. -/
instance : X.restrictEtaleFunctor.IsContinuous (Opens.grothendieckTopology X)
    X.smallNisnevichTopology :=
  Functor.isContinuous_iff_coverPreserving.mpr (coverPreserving_restrictEtaleFunctor X)

/-- Zariski coverings are étale coverings: the functor from open subsets of `X` to schemes étale
over `X` sends Zariski covering sieves to covering sieves of the small étale site. -/
theorem coverPreserving_restrictEtaleFunctor_smallEtaleTopology :
    CoverPreserving (Opens.grothendieckTopology X) X.smallEtaleTopology X.restrictEtaleFunctor where
  cover_preserve hS := smallNisnevichTopology_le_smallEtaleTopology X _
    ((coverPreserving_restrictEtaleFunctor X).cover_preserve hS)

/-- The functor from open subsets of `X` to schemes étale over `X` is continuous for the Zariski
and the small étale topologies. -/
instance : X.restrictEtaleFunctor.IsContinuous (Opens.grothendieckTopology X)
    X.smallEtaleTopology :=
  Functor.isContinuous_iff_coverPreserving.mpr
    (coverPreserving_restrictEtaleFunctor_smallEtaleTopology X)

section

variable (A : Type w) [Category.{w'} A] [HasWeakSheafify X.smallNisnevichTopology A]
  [∀ F : X.Opensᵒᵖ ⥤ A, X.restrictEtaleFunctor.op.HasLeftKanExtension F]

/-- The inverse image of the morphism of topoi from the small Nisnevich site to the Zariski site
of `X`: the pullback of sheaves along `X.restrictEtaleFunctor`, the Nisnevich sheafification of
the left Kan extension of a Zariski sheaf. -/
noncomputable def nisnevichToZariski :
    Sheaf (Opens.grothendieckTopology X) A ⥤ Sheaf X.smallNisnevichTopology A :=
  X.restrictEtaleFunctor.sheafPullback A _ _

/-- The inverse image from Zariski sheaves to Nisnevich sheaves is left adjoint to the direct
image, which restricts a Nisnevich sheaf to the open subschemes of `X`. -/
noncomputable def nisnevichToZariskiAdjunction :
    nisnevichToZariski X A ⊣
      X.restrictEtaleFunctor.sheafPushforwardContinuous A _ X.smallNisnevichTopology :=
  X.restrictEtaleFunctor.sheafAdjunctionContinuous A _ _

instance : (nisnevichToZariski X A).IsLeftAdjoint :=
  (nisnevichToZariskiAdjunction X A).isLeftAdjoint

/-- The inverse image from Zariski sheaves to Nisnevich sheaves sends the constant Zariski sheaf to
the constant Nisnevich sheaf. -/
noncomputable def constantSheafCompNisnevichToZariskiIso
    [HasWeakSheafify (Opens.grothendieckTopology X) A] :
    constantSheaf _ A ⋙ nisnevichToZariski X A ≅ constantSheaf _ A :=
  have := final_of_representablyFlat X.restrictEtaleFunctor
  X.restrictEtaleFunctor.constantSheafCompSheafPullbackIso A _ _

/-- **Composition of the comparison morphisms**: the inverse image from Zariski sheaves to
Nisnevich sheaves followed by the inverse image from Nisnevich sheaves to étale sheaves is the
pullback of sheaves along `X.restrictEtaleFunctor` from the Zariski site to the small étale site. -/
noncomputable def nisnevichToZariskiCompEtaleToNisnevichIso
    [HasWeakSheafify X.smallEtaleTopology A] :
    nisnevichToZariski X A ⋙ etaleToNisnevich X A ≅
      X.restrictEtaleFunctor.sheafPullback A (Opens.grothendieckTopology X) X.smallEtaleTopology :=
  ((nisnevichToZariskiAdjunction X A).comp (etaleToNisnevichAdjunction X A)).leftAdjointUniq
    (X.restrictEtaleFunctor.sheafAdjunctionContinuous A _ _)

end

/-- The inverse image from Zariski sheaves to Nisnevich sheaves is exact. -/
instance (A : Type w) [Category.{u} A] {FA : A → A → Type*} {CA : A → Type u}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] [HasFiniteLimits A]
    [HasColimits A] [PreservesFiniteLimits (CategoryTheory.forget A)]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimits (CategoryTheory.forget A)]
    [HasSheafify X.smallNisnevichTopology A] [HasSheafify (Opens.grothendieckTopology X) A] :
    PreservesFiniteLimits (nisnevichToZariski X A) := by
  dsimp only [nisnevichToZariski]
  infer_instance

end AlgebraicGeometry.Scheme
