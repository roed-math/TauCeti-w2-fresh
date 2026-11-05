/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.Local

/-!
# The infinitesimal lifting criterion for étale morphisms

A morphism locally of finite presentation is étale if and only if it is formally étale, that is,
if and only if lifts along affine first-order thickenings exist and are unique. A formally smooth
morphism locally of finite presentation is smooth.

The étale direction glues local lifts: a smooth morphism is formally smooth over small affine
opens by the ring-theoretic criterion, so lifts exist locally. For an étale morphism, lifts into a
formally unramified morphism are unique (Mathlib's `AlgebraicGeometry.FormallyUnramified.hom_ext`),
so the local lifts agree on overlaps.

## Main results

* `TauCeti.AlgebraicGeometry.FormallyEtale.of_etale`: an étale morphism is formally étale.
* `TauCeti.AlgebraicGeometry.etale_iff_formallyEtale`: a morphism locally of finite presentation
  is étale if and only if it is formally étale.
* `AlgebraicGeometry.Smooth.of_formallySmooth`: a formally smooth morphism locally of
  finite presentation is smooth.
* `TauCeti.AlgebraicGeometry.FormallySmooth.of_smooth_of_isAffine`: a smooth morphism of affine
  schemes is formally smooth.
* `TauCeti.AlgebraicGeometry.exists_affine_chart`: along a thickening `i : T ⟶ T'`, the affine opens
  `W ⊆ T'` with affine opens `U ⊆ X`, `V ⊆ S` containing the images of `i⁻¹ W` and `W` form a basis.
* `TauCeti.AlgebraicGeometry.exists_local_lift_of_smooth`: for a smooth morphism, lifts along a
  first-order thickening exist locally on its target.

## References

* [Stacks Project, Lemma 37.8.10](https://stacks.math.columbia.edu/tag/02HM), étale is formally
  étale and locally of finite presentation.
* [Stacks Project, Lemma 37.11.7](https://stacks.math.columbia.edu/tag/02H6), smooth is formally
  smooth and locally of finite presentation.
-/

public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

open TauCeti.AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A formally smooth morphism locally of finite presentation is smooth. Stacks, Lemma 37.11.7
(02H6), the direction that does not need lifts to glue. -/
theorem Smooth.of_formallySmooth (f : X ⟶ S) [LocallyOfFinitePresentation f] [FormallySmooth f] :
    Smooth f :=
  HasRingHomProperty.iff_appLE.2 fun U V e ↦ by
    have hs := FormallySmooth.formallySmooth_appLE f U.2 V.2 e
    have hp := HasRingHomProperty.appLE @LocallyOfFinitePresentation f ‹_› U V e
    algebraize [(f.appLE U V e).hom]
    exact Algebra.Smooth.mk

/-- A formally étale morphism locally of finite presentation is étale. -/
theorem Etale.of_formallyEtale (f : X ⟶ S) [LocallyOfFinitePresentation f] [FormallyEtale f] :
    Etale f :=
  HasRingHomProperty.iff_appLE.2 fun U V e ↦ by
    have hs := FormallyEtale.formallyEtale_appLE f U.2 V.2 e
    have hp := HasRingHomProperty.appLE @LocallyOfFinitePresentation f ‹_› U V e
    algebraize [(f.appLE U V e).hom]
    exact Algebra.Etale.mk

end AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A smooth morphism of affine schemes is formally smooth. This is the affine case of Stacks,
Lemma 37.11.7 (02H6), where lifts need not be glued. -/
theorem FormallySmooth.of_smooth_of_isAffine [IsAffine X] [IsAffine S] (f : X ⟶ S) [Smooth f] :
    FormallySmooth f := by
  have hf : f = X.isoSpec.hom ≫ Spec.map f.appTop ≫ S.isoSpec.inv := by
    rw [Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  have : FormallySmooth (Spec.map f.appTop) := by
    have := HasRingHomProperty.appTop @Smooth f ‹_›
    algebraize [f.appTop.hom]
    exact (FormallySmooth.SpecMap_iff _).2 (inferInstanceAs (Algebra.FormallySmooth _ _))
  rw [hf]
  infer_instance

/-- Affine charts along a thickening: in a commutative square `a ≫ f = i ≫ h` with `i : T ⟶ T'` a
thickening, every point of an open `O ⊆ T'` has an affine open neighbourhood `W ⊆ O` with affine
opens `U ⊆ X` and `V ⊆ S` such that `a (i⁻¹ W) ⊆ U`, `h W ⊆ V` and `f U ⊆ V`. -/
theorem exists_affine_chart {T T' : Scheme.{u}} {f : X ⟶ S} {i : T ⟶ T'} [IsThickening i]
    {a : T ⟶ X} {h : T' ⟶ S} (w : a ≫ f = i ≫ h) {O : T'.Opens} {x : T'} (hx : x ∈ O) :
    ∃ (W : T'.Opens) (U : X.Opens) (V : S.Opens), IsAffineOpen W ∧ IsAffineOpen U ∧
      IsAffineOpen V ∧ x ∈ W ∧ W ≤ O ∧ i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U ∧ W ≤ h ⁻¹ᵁ V ∧ U ≤ f ⁻¹ᵁ V := by
  obtain ⟨t, rfl⟩ := i.surjective x
  have hi := IsUniversalHomeomorphism.isHomeomorph i
  -- Choose affine opens `h (i t) ∈ V`, `a t ∈ U ⊆ f⁻¹ V`, and `i t ∈ W` with `W` inside `O`, inside
  -- `h⁻¹ V` and inside the image of `a⁻¹ U`, which is open as `i` is a homeomorphism.
  obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (show h (i t) ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show a t ∈ f ⁻¹ᵁ V by rwa [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, w])
  let O' : T'.Opens := ⟨i '' (a ⁻¹ᵁ U), hi.isOpenMap _ (a ⁻¹ᵁ U).2⟩
  obtain ⟨W, hW, hxW, hWO⟩ := Opens.isBasis_iff_nbhd.mp T'.isBasis_affineOpens
    (show i t ∈ O ⊓ h ⁻¹ᵁ V ⊓ O' from ⟨⟨hx, hxV⟩, t, hxU, rfl⟩)
  refine ⟨W, U, V, hW, hU, hV, hxW, fun y hy ↦ (hWO hy).1.1, fun s hs ↦ ?_,
    fun y hy ↦ (hWO hy).1.2, hUV⟩
  obtain ⟨t', ht', he⟩ := (hWO (show i s ∈ W from hs)).2
  exact hi.injective he ▸ ht'

section Lift

variable {T T' : Scheme.{u}} (f : X ⟶ S) (i : T ⟶ T') [IsFirstOrderThickening i]
  (a : T ⟶ X) (h : T' ⟶ S)

/-- Local lifts for a smooth morphism: every point of `T'` has an affine open neighbourhood `W`
over which `a` extends to `l : W ⟶ X` lying over `h`. The lifts are not unique, so for a smooth
morphism they need not glue; for an étale one they do (`FormallyEtale.of_etale`). -/
theorem exists_local_lift_of_smooth [Smooth f] (w : a ≫ f = i ≫ h) (x : T') :
    ∃ W : T'.Opens, IsAffineOpen W ∧ x ∈ W ∧ ∃ l : W.toScheme ⟶ X,
      pullback.snd i W.ι ≫ l = pullback.fst i W.ι ≫ a ∧ l ≫ f = W.ι ≫ h := by
  obtain ⟨W, U, V, hW, hU, hV, hxW, -, hWU, hWV, hUV⟩ := exists_affine_chart w (O := ⊤) trivial
  have : IsAffine U := hU
  have : IsAffine V := hV
  have : IsAffine W := hW
  refine ⟨W, hW, hxW, ?_⟩
  -- Restricted to `W`, the problem lives over the affine opens `U ⟶ V`.
  have ha : Set.range (pullback.fst i (Scheme.Opens.ι W) ≫ a) ⊆
      Set.range (Scheme.Opens.ι U) := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.Opens.range_ι]
    refine hWU (show i (pullback.fst i (Scheme.Opens.ι W) p) ∈ W from ?_)
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact (pullback.snd i (Scheme.Opens.ι W) p).2
  have hh : Set.range (Scheme.Opens.ι W ≫ h) ⊆ Set.range (Scheme.Opens.ι V) := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hWV p.2
  have : FormallySmooth (f.resLE V U hUV) := FormallySmooth.of_smooth_of_isAffine _
  obtain ⟨m, hm₁, hm₂⟩ := FormallySmooth.exists_lift (f := f.resLE V U hUV)
    (pullback.snd i (Scheme.Opens.ι W)) (IsOpenImmersion.lift (Scheme.Opens.ι U) _ ha)
    (IsOpenImmersion.lift (Scheme.Opens.ι V) _ hh) (by
      rw [← cancel_mono (Scheme.Opens.ι V)]
      simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, IsOpenImmersion.lift_fac,
        IsOpenImmersion.lift_fac_assoc, w, pullback.condition_assoc])
  refine ⟨m ≫ Scheme.Opens.ι U, ?_, ?_⟩
  · rw [← Category.assoc, hm₁, IsOpenImmersion.lift_fac]
  · rw [Category.assoc, ← Scheme.Hom.resLE_comp_ι f hUV, ← Category.assoc, hm₂,
      IsOpenImmersion.lift_fac]

/-- Two local lifts agree on the overlap of their domains, since lifts into a formally unramified
morphism are unique. -/
private theorem local_lift_compat [Etale f] {W₁ W₂ : T'.Opens} {l₁ : W₁.toScheme ⟶ X}
    {l₂ : W₂.toScheme ⟶ X} (hl₁ : pullback.snd i W₁.ι ≫ l₁ = pullback.fst i W₁.ι ≫ a)
    (hf₁ : l₁ ≫ f = W₁.ι ≫ h) (hl₂ : pullback.snd i W₂.ι ≫ l₂ = pullback.fst i W₂.ι ≫ a)
    (hf₂ : l₂ ≫ f = W₂.ι ≫ h) :
    pullback.fst W₁.ι W₂.ι ≫ l₁ = pullback.snd W₁.ι W₂.ι ≫ l₂ := by
  refine FormallyUnramified.hom_ext (pullback.snd i (pullback.fst W₁.ι W₂.ι ≫ W₁.ι))
    (IsFirstOrderThickening.isNilpotent_ker _) f ?_ ?_
  · -- Both sides restrict to `a` on the preimage of the overlap in `T`.
    have e₁ := pullback.lift_snd (pullback.fst i (pullback.fst W₁.ι W₂.ι ≫ W₁.ι))
      (pullback.snd i (pullback.fst W₁.ι W₂.ι ≫ W₁.ι) ≫ pullback.fst W₁.ι W₂.ι)
      (pullback.condition.trans (Category.assoc _ _ _).symm)
    have e₂ := pullback.lift_snd (pullback.fst i (pullback.fst W₁.ι W₂.ι ≫ W₁.ι))
      (pullback.snd i (pullback.fst W₁.ι W₂.ι ≫ W₁.ι) ≫ pullback.snd W₁.ι W₂.ι)
      (pullback.condition.trans <| by
        rw [Category.assoc]
        exact congrArg (pullback.snd i _ ≫ ·) pullback.condition)
    rw [← Category.assoc, ← e₁, Category.assoc, hl₁, pullback.lift_fst_assoc,
      ← Category.assoc, ← e₂, Category.assoc, hl₂, pullback.lift_fst_assoc]
  · rw [Category.assoc, Category.assoc, hf₁, hf₂, pullback.condition_assoc]

/-- An étale morphism is formally étale: lifts exist locally on the target of the thickening, and
they glue since lifts into an étale morphism are unique. Stacks, Lemma 37.8.10 (02HM). -/
instance (priority := 100) FormallyEtale.of_etale [Etale f] : FormallyEtale f := by
  refine (formallyEtale_iff f).2 ⟨⟨fun {T T'} _ i _ a h w ↦ ?_⟩, inferInstance⟩
  choose W _ hxW l hl₁ hl₂ using exists_local_lift_of_smooth f i a h w
  let 𝒰 := T'.openCoverOfIsOpenCover W
    (eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hxW x⟩)
  let L := 𝒰.glueMorphisms l fun x y ↦ local_lift_compat f i a h (hl₁ x) (hl₂ x) (hl₁ y) (hl₂ y)
  have hL (x : T') : (W x).ι ≫ L = l x := 𝒰.ι_glueMorphisms _ _ x
  refine ⟨L, Scheme.Cover.hom_ext (𝒰.pullback₁ i) _ _ fun (x : T') ↦ ?_,
    Scheme.Cover.hom_ext 𝒰 _ _ fun (x : T') ↦ ?_⟩
  · change pullback.fst i (W x).ι ≫ i ≫ L = pullback.fst i (W x).ι ≫ a
    rw [pullback.condition_assoc, hL, hl₁]
  · change (W x).ι ≫ L ≫ f = (W x).ι ≫ h
    rw [← Category.assoc, hL, hl₂]

end Lift

/-- A morphism locally of finite presentation is étale if and only if it is formally étale.
Stacks, Lemma 37.8.10 (02HM). -/
theorem etale_iff_formallyEtale (f : X ⟶ S) [LocallyOfFinitePresentation f] :
    Etale f ↔ FormallyEtale f :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ AlgebraicGeometry.Etale.of_formallyEtale f⟩

end TauCeti.AlgebraicGeometry
