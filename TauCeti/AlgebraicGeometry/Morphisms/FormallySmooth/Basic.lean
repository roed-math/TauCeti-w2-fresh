/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Thickening

/-!
# Formally smooth and formally étale morphisms of schemes

A morphism of schemes `f : X ⟶ S` is *formally smooth* if for every first-order thickening
`i : T ⟶ T'` of affine schemes over `S`, every `S`-morphism `T ⟶ X` extends to at least one
`S`-morphism `T' ⟶ X`, and *formally étale* if it extends to exactly one. Formal unramifiedness,
the property that it extends to at most one, is Mathlib's `AlgebraicGeometry.FormallyUnramified`,
defined affine-locally by the ring-theoretic condition.

These lifting definitions do not mention finiteness, so they make sense for every morphism; for
morphisms locally of finite presentation they recover smooth and étale morphisms (Stacks,
Lemma 37.11.7 (02H6) and Lemma 37.8.10 (02HM)).

## Main definitions

* `TauCeti.AlgebraicGeometry.FormallySmooth f`: lifts along affine first-order thickenings exist.
* `TauCeti.AlgebraicGeometry.FormallyEtale f`: lifts along affine first-order thickenings exist and
  are unique.

## Main results

* Both classes contain the isomorphisms, are stable under composition and base change, and respect
  isomorphisms; a formally étale morphism is formally smooth.
* `TauCeti.AlgebraicGeometry.FormallyEtale.of_isOpenImmersion`: an open immersion is formally
  étale.

## Implementation notes

The test thickenings `T ⟶ T'` are required to have affine target, as in the Stacks project. The
source `T` is then affine as well, being closed in `T'`.

## References

* [Stacks Project, Definition 37.11.1](https://stacks.math.columbia.edu/tag/02H0), formally
  smooth morphisms.
* [Stacks Project, Definition 37.8.1](https://stacks.math.columbia.edu/tag/02HG), formally étale
  morphisms.
-/

public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {X Y Z S : Scheme.{u}}

/-- A morphism of schemes `f : X ⟶ S` is *formally smooth* if for every first-order thickening
`i : T ⟶ T'` with `T'` affine, every morphism `g : T ⟶ X` and every `h : T' ⟶ S` with
`g ≫ f = i ≫ h`, there is a morphism `l : T' ⟶ X` with `i ≫ l = g` and `l ≫ f = h`.
Stacks, Definition 37.11.1 (02H0). -/
@[stacks 02H0]
class FormallySmooth (f : X ⟶ S) : Prop where
  /-- Lifts along affine first-order thickenings exist. -/
  exists_lift {T T' : Scheme.{u}} [IsAffine T'] (i : T ⟶ T') [IsFirstOrderThickening i]
    (g : T ⟶ X) (h : T' ⟶ S) : g ≫ f = i ≫ h → ∃ l : T' ⟶ X, i ≫ l = g ∧ l ≫ f = h

/-- A morphism of schemes `f : X ⟶ S` is *formally étale* if for every first-order thickening
`i : T ⟶ T'` with `T'` affine, every morphism `g : T ⟶ X` and every `h : T' ⟶ S` with
`g ≫ f = i ≫ h`, there is a unique morphism `l : T' ⟶ X` with `i ≫ l = g` and `l ≫ f = h`.
Stacks, Definition 37.8.1 (02HG). -/
@[stacks 02HG]
class FormallyEtale (f : X ⟶ S) : Prop where
  /-- Lifts along affine first-order thickenings exist and are unique. -/
  existsUnique_lift {T T' : Scheme.{u}} [IsAffine T'] (i : T ⟶ T') [IsFirstOrderThickening i]
    (g : T ⟶ X) (h : T' ⟶ S) : g ≫ f = i ≫ h → ∃! l : T' ⟶ X, i ≫ l = g ∧ l ≫ f = h

namespace FormallyEtale

/-- A formally étale morphism is formally smooth. -/
instance (priority := 100) formallySmooth (f : X ⟶ S) [FormallyEtale f] : FormallySmooth f where
  exists_lift i _ g h w := (existsUnique_lift i g h w).exists

/-- Two lifts of the same morphism along an affine first-order thickening into a formally étale
morphism agree. -/
theorem hom_ext (f : X ⟶ S) [FormallyEtale f] {T T' : Scheme.{u}} [IsAffine T'] (i : T ⟶ T')
    [IsFirstOrderThickening i] {l₁ l₂ : T' ⟶ X} (hi : i ≫ l₁ = i ≫ l₂) (hf : l₁ ≫ f = l₂ ≫ f) :
    l₁ = l₂ :=
  (existsUnique_lift i (i ≫ l₂) (l₂ ≫ f) (by simp)).unique ⟨hi, hf⟩ ⟨rfl, rfl⟩

/-- A morphism is formally étale if it is formally smooth and lifts along affine first-order
thickenings are unique. -/
theorem of_formallySmooth (f : X ⟶ S) [FormallySmooth f]
    (H : ∀ {T T' : Scheme.{u}} [IsAffine T'] (i : T ⟶ T') [IsFirstOrderThickening i]
      (l₁ l₂ : T' ⟶ X), i ≫ l₁ = i ≫ l₂ → l₁ ≫ f = l₂ ≫ f → l₁ = l₂) :
    FormallyEtale f where
  existsUnique_lift i _ g h w := by
    obtain ⟨l, hl⟩ := FormallySmooth.exists_lift i g h w
    exact ⟨l, hl, fun l' hl' ↦ H i l' l (hl'.1.trans hl.1.symm) (hl'.2.trans hl.2.symm)⟩

end FormallyEtale

namespace FormallySmooth

/-- An isomorphism is formally smooth. -/
instance (priority := 100) of_isIso (f : X ⟶ S) [IsIso f] : FormallySmooth f where
  exists_lift i _ g h w := ⟨h ≫ inv f, by rw [← Category.assoc, ← w]; simp, by simp⟩

/-- A composite of formally smooth morphisms is formally smooth: lift first along `g`, then along
`f`. -/
instance comp (f : X ⟶ Y) (g : Y ⟶ S) [FormallySmooth f] [FormallySmooth g] :
    FormallySmooth (f ≫ g) where
  exists_lift i _ a h w := by
    obtain ⟨m, hm₁, hm₂⟩ := exists_lift (f := g) i (a ≫ f) h (by rw [Category.assoc, w])
    obtain ⟨l, hl₁, hl₂⟩ := exists_lift (f := f) i a m hm₁.symm
    exact ⟨l, hl₁, by rw [← Category.assoc, hl₂, hm₂]⟩

/-- Formal smoothness is stable under base change: lift along the original morphism and pair the
lift with the given map. -/
theorem of_isPullback {Y' : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y}
    {g' : Y' ⟶ X} (sq : IsPullback f' g' g f) [FormallySmooth g] : FormallySmooth g' where
  exists_lift i _ a h w := by
    obtain ⟨l, hl₁, hl₂⟩ := exists_lift (f := g) i (a ≫ f') (h ≫ f) (by
      rw [Category.assoc, sq.w, ← Category.assoc, w, Category.assoc])
    refine ⟨sq.lift l h hl₂, sq.hom_ext ?_ ?_, sq.lift_snd _ _ _⟩
    · rw [Category.assoc, sq.lift_fst, hl₁]
    · rw [Category.assoc, sq.lift_snd, w]

instance isStableUnderBaseChange : IsStableUnderBaseChange @FormallySmooth.{u} where
  of_isPullback sq hg := by
    have := hg
    exact of_isPullback sq

instance isStableUnderComposition : IsStableUnderComposition @FormallySmooth.{u} where
  comp_mem f g hf hg := by
    have := hf
    have := hg
    infer_instance

instance isMultiplicative : IsMultiplicative @FormallySmooth.{u} where
  id_mem _ := inferInstance

instance respectsIso : RespectsIso @FormallySmooth.{u} :=
  respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) ↦
    inferInstanceAs (FormallySmooth f)

/-- The first projection of a pullback along a formally smooth morphism is formally smooth. -/
instance pullback_fst (f : X ⟶ S) (g : Y ⟶ S) [FormallySmooth g] :
    FormallySmooth (pullback.fst f g) :=
  of_isPullback (IsPullback.of_hasPullback f g).flip

/-- The second projection of a pullback along a formally smooth morphism is formally smooth. -/
instance pullback_snd (f : X ⟶ S) (g : Y ⟶ S) [FormallySmooth f] :
    FormallySmooth (pullback.snd f g) :=
  of_isPullback (IsPullback.of_hasPullback f g)

end FormallySmooth

namespace FormallyEtale

/-- An isomorphism is formally étale. -/
instance (priority := 100) of_isIso (f : X ⟶ S) [IsIso f] : FormallyEtale f :=
  of_formallySmooth f fun _ _ _ _ _ hf ↦ by simpa using hf =≫ inv f

/-- A composite of formally étale morphisms is formally étale. -/
instance comp (f : X ⟶ Y) (g : Y ⟶ S) [FormallyEtale f] [FormallyEtale g] :
    FormallyEtale (f ≫ g) :=
  of_formallySmooth _ fun i _ l₁ l₂ hi hl ↦ by
    have := hom_ext g i (l₁ := l₁ ≫ f) (l₂ := l₂ ≫ f) (by simp only [← Category.assoc, hi])
      (by simpa using hl)
    exact hom_ext f i hi this

/-- Formal étaleness is stable under base change. -/
theorem of_isPullback {Y' : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y}
    {g' : Y' ⟶ X} (sq : IsPullback f' g' g f) [FormallyEtale g] : FormallyEtale g' :=
  have := FormallySmooth.of_isPullback sq
  of_formallySmooth _ fun i _ l₁ l₂ hi hl ↦ sq.hom_ext
    (hom_ext g i (by simp only [← Category.assoc, hi])
      (by simp only [Category.assoc, sq.w, reassoc_of% hl]))
    hl

instance isStableUnderBaseChange : IsStableUnderBaseChange @FormallyEtale.{u} where
  of_isPullback sq hg := by
    have := hg
    exact of_isPullback sq

instance isStableUnderComposition : IsStableUnderComposition @FormallyEtale.{u} where
  comp_mem f g hf hg := by
    have := hf
    have := hg
    infer_instance

instance isMultiplicative : IsMultiplicative @FormallyEtale.{u} where
  id_mem _ := inferInstance

instance respectsIso : RespectsIso @FormallyEtale.{u} :=
  respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) ↦
    inferInstanceAs (FormallyEtale f)

/-- The first projection of a pullback along a formally étale morphism is formally étale. -/
instance pullback_fst (f : X ⟶ S) (g : Y ⟶ S) [FormallyEtale g] :
    FormallyEtale (pullback.fst f g) :=
  of_isPullback (IsPullback.of_hasPullback f g).flip

/-- The second projection of a pullback along a formally étale morphism is formally étale. -/
instance pullback_snd (f : X ⟶ S) (g : Y ⟶ S) [FormallyEtale f] :
    FormallyEtale (pullback.snd f g) :=
  of_isPullback (IsPullback.of_hasPullback f g)

/-- An open immersion is formally étale: a first-order thickening is surjective, so a morphism out
of its target lands in the image of the open immersion as soon as its restriction does. -/
instance (priority := 100) of_isOpenImmersion (f : X ⟶ S) [IsOpenImmersion f] :
    FormallyEtale f where
  existsUnique_lift i _ g h w := by
    have hrange : Set.range h ⊆ Set.range f := by
      rintro _ ⟨t', rfl⟩
      obtain ⟨t, rfl⟩ := i.surjective t'
      exact ⟨g t, by rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]⟩
    refine ⟨IsOpenImmersion.lift f h hrange, ⟨?_, IsOpenImmersion.lift_fac _ _ _⟩,
      fun l hl ↦ IsOpenImmersion.lift_uniq _ _ _ l hl.2⟩
    rw [← cancel_mono f, Category.assoc, IsOpenImmersion.lift_fac, w]

end FormallyEtale

end TauCeti.AlgebraicGeometry
