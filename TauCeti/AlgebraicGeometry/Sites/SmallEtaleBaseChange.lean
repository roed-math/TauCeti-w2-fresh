/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.CoverPreserving

/-!
# Base change of the small étale site

A morphism of schemes `g : Y ⟶ X` induces the base change functor
`Etale.pullback g : X.Etale ⥤ Y.Etale`, `U ↦ U ×ₓ Y`, between the small étale sites. It preserves
finite limits and sends étale coverings to étale coverings, so it is representably flat and
continuous, and the pullback of sheaves along it is the inverse image of the morphism of small
étale topoi induced by `g`. The base change of a morphism of schemes étale over `X` is a base
change of schemes (`Etale.isPullback_pullback_map_left`), which is how coverings for other
topologies on `X.Etale`, such as the small Nisnevich topology, are seen to be preserved as well.

## Main declarations

* `AlgebraicGeometry.Scheme.Etale.pullback`: base change of schemes étale over `X` along
  `g : Y ⟶ X`.
* `AlgebraicGeometry.Scheme.Etale.isPullback_pullback_map_left`: the base change of a morphism is
  a pullback square of schemes.
* `AlgebraicGeometry.Scheme.Etale.pullbackCompForgetIso`: compatibility with base change of
  schemes over `X`.
* `AlgebraicGeometry.Scheme.coverPreserving_etalePullback`: base change preserves étale coverings.

## References

* [Stacks Project, Section 59.36 (03PZ)](https://stacks.math.columbia.edu/tag/03PZ)
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- Base change along `g : Y ⟶ X`, from schemes étale over `X` to schemes étale over `Y`. -/
@[expose] noncomputable def Etale.pullback : X.Etale ⥤ Y.Etale :=
  -- Instance search does not find these two instances for `@Etale`.
  @MorphismProperty.Over.pullback _ _ @Etale ⊤ _ _ _ g
    (MorphismProperty.instHasPullbacksAlongOfHasPullbacksAlong _ g)
    (MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStableUnderBaseChange _ g) _

@[simp]
lemma Etale.pullback_obj_left (W : X.Etale) :
    ((Etale.pullback g).obj W).left = Limits.pullback W.hom g :=
  rfl

@[simp]
lemma Etale.pullback_obj_hom (W : X.Etale) :
    ((Etale.pullback g).obj W).hom = pullback.snd W.hom g :=
  rfl

@[simp]
lemma Etale.pullback_map_left {Z W : X.Etale} (f : Z ⟶ W) :
    ((Etale.pullback g).map f).left =
      pullback.lift (pullback.fst Z.hom g ≫ f.left) (pullback.snd Z.hom g)
        (by simp [pullback.condition]) :=
  rfl

/-- The base change of a morphism `f : Z ⟶ W` of schemes étale over `X` is the base change of
`f.left` along `W ×ₓ Y ⟶ W`. -/
lemma Etale.isPullback_pullback_map_left {Z W : X.Etale} (f : Z ⟶ W) :
    IsPullback ((Etale.pullback g).map f).left (pullback.fst Z.hom g) (pullback.fst W.hom g)
      f.left := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback W.hom g).flip
  simpa using (IsPullback.of_hasPullback Z.hom g).flip

/-- Base change of schemes étale over `X` is base change of schemes over `X`. -/
noncomputable def Etale.pullbackCompForgetIso :
    Etale.pullback g ⋙ Etale.forget Y ≅ Etale.forget X ⋙ CategoryTheory.Over.pullback g :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦ by
    ext : 1
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Base change of schemes étale over `X` preserves finite limits. -/
instance : PreservesFiniteLimits (Etale.pullback g) :=
  have := preservesFiniteLimits_of_natIso (Etale.pullbackCompForgetIso g).symm
  preservesFiniteLimits_of_reflects_of_preserves _ (Etale.forget Y)

instance : RepresentablyFlat (Etale.pullback g) :=
  flat_of_preservesFiniteLimits _

/-- Base change along `g : Y ⟶ X` sends étale coverings in `X.Etale` to étale coverings in
`Y.Etale`. -/
theorem coverPreserving_etalePullback :
    CoverPreserving X.smallEtaleTopology Y.smallEtaleTopology (Etale.pullback g) where
  cover_preserve {W R} hR := by
    obtain ⟨ι, Z, f, rfl⟩ := R.exists_eq_ofArrows
    rw [ofArrows_mem_smallEtaleTopology_iff] at hR
    rw [Sieve.functorPushforward_ofArrows, ofArrows_mem_smallEtaleTopology_iff]
    have hf : Presieve.ofArrows _ (fun i ↦ (f i).left) ∈ precoverage @Etale W.left :=
      (ofArrows_mem_precoverage_iff (P := @Etale)).mpr
        ⟨fun x ↦ by simpa using hR.symm.subset (Set.mem_univ x), fun _ ↦ inferInstance⟩
    -- Instance search does not find that étale coverings are stable under base change.
    have : (precoverage @Etale).IsStableUnderBaseChange :=
      (fun (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] ↦
        (inferInstance : (precoverage P).IsStableUnderBaseChange)) @Etale
    have := Precoverage.mem_coverings_of_isPullback _ hf (pullback.fst W.hom g) _ _
      fun i ↦ Etale.isPullback_pullback_map_left g (f i)
    exact Set.eq_univ_of_forall fun x ↦
      Set.mem_iUnion.mpr (((ofArrows_mem_precoverage_iff (P := @Etale)).mp this).1 x)

instance : (Etale.pullback g).IsContinuous X.smallEtaleTopology Y.smallEtaleTopology :=
  Functor.isContinuous_iff_coverPreserving.mpr (coverPreserving_etalePullback g)

end AlgebraicGeometry.Scheme
