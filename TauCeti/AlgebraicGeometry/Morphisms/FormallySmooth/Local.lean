/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.Affine

/-!
# Formal smoothness, unramifiedness and étaleness on affine opens

Mathlib's `AlgebraicGeometry.FormallyUnramified` is defined affine-locally by the ring-theoretic
condition, and Mathlib proves the infinitesimal criterion for it with nilpotent thickenings. In the
language of first-order thickenings it is exactly uniqueness of lifts along affine first-order
thickenings, so that a morphism is formally étale in the lifting sense if and only if it is
formally smooth and formally unramified. We also show that formally smooth (respectively formally
étale) morphisms are formally smooth (respectively formally étale) on all affine opens.

## Main results

* `TauCeti.AlgebraicGeometry.formallyUnramified_iff_hom_ext`: a morphism is formally unramified
  if and only if lifts along affine first-order thickenings are unique.
* `TauCeti.AlgebraicGeometry.formallyEtale_iff`: formally étale is formally smooth and formally
  unramified.
* `TauCeti.AlgebraicGeometry.FormallySmooth.formallySmooth_appLE` and
  `TauCeti.AlgebraicGeometry.FormallyEtale.formallyEtale_appLE`: the ring maps on affine opens of a
  formally smooth (respectively formally étale) morphism are formally smooth (respectively formally
  étale).

## References

* [Stacks Project, Definition 37.6.1](https://stacks.math.columbia.edu/tag/02H8), formally
  unramified morphisms.
* [Stacks Project, Definition 37.8.1](https://stacks.math.columbia.edu/tag/02HG), formally étale
  morphisms.
-/

public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

universe u

variable {X S T T' : Scheme.{u}}

namespace TauCeti.AlgebraicGeometry

/-- A morphism is formally unramified if and only if lifts along affine first-order thickenings
are unique. This is Mathlib's infinitesimal criterion `FormallyUnramified.hom_ext` and
`FormallyUnramified.of_hom_ext`, in the language of first-order thickenings.
Stacks, Definition 37.6.1 (02H8). -/
theorem formallyUnramified_iff_hom_ext (f : X ⟶ S) :
    FormallyUnramified f ↔ ∀ {T T' : Scheme.{u}} [IsAffine T'] (i : T ⟶ T')
      [IsFirstOrderThickening i] (l₁ l₂ : T' ⟶ X), i ≫ l₁ = i ≫ l₂ → l₁ ≫ f = l₂ ≫ f →
        l₁ = l₂ :=
  ⟨fun _ _ _ _ i _ _ _ hi hf ↦
      FormallyUnramified.hom_ext i (IsFirstOrderThickening.isNilpotent_ker i) f hi hf,
    fun H ↦ FormallyUnramified.of_hom_ext f fun _ _ φ hφ hker _ _ hi hf ↦
      have := (IsFirstOrderThickening.SpecMap_iff φ hφ).2 ((pow_two _).symm.trans hker)
      H (Spec.map φ) _ _ hi hf⟩

/-- A formally étale morphism is formally unramified. -/
instance (priority := 100) FormallyEtale.formallyUnramified (f : X ⟶ S) [FormallyEtale f] :
    FormallyUnramified f :=
  (formallyUnramified_iff_hom_ext f).2 fun i _ _ _ hi hf ↦ FormallyEtale.hom_ext f i hi hf

/-- A morphism is formally étale if and only if it is formally smooth and formally unramified. -/
theorem formallyEtale_iff (f : X ⟶ S) :
    FormallyEtale f ↔ FormallySmooth f ∧ FormallyUnramified f :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦
    FormallyEtale.of_formallySmooth f fun i _ _ _ hi hf ↦
      FormallyUnramified.hom_ext i (IsFirstOrderThickening.isNilpotent_ker i) f hi hf⟩

/-- On affine opens `V ⊆ f⁻¹ U`, a formally smooth morphism induces a formally smooth ring map
`Γ(S, U) ⟶ Γ(X, V)`. -/
theorem FormallySmooth.formallySmooth_appLE (f : X ⟶ S) [FormallySmooth f] {U : S.Opens}
    (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) :
    (f.appLE U V e).hom.FormallySmooth := by
  algebraize [(f.appLE U V e).hom]
  -- Lift along `Spec (B ⧸ I) ⟶ Spec B`; the lift lands in `V` since the thickening is surjective.
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ I hI g ↦ ?_
  have := IsFirstOrderThickening.SpecMap_mk I hI
  obtain ⟨l, hl₁, hl₂⟩ := FormallySmooth.exists_lift (f := f)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ hV.fromSpec)
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) B)) ≫ hU.fromSpec) (by
      rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e,
        ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
      congr 2
      ext x
      exact g.commutes x)
  have hrange : Set.range l ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨t, rfl⟩ := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).surjective x
    rw [← Scheme.Hom.comp_apply, hl₁, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  obtain ⟨l', hl'⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec l hrange)
  have hl : Spec.map l' ≫ hV.fromSpec = l := by rw [hl', IsOpenImmersion.lift_fac]
  rw [← hl, ← Spec.map_comp_assoc, cancel_mono] at hl₁
  rw [← hl, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e,
    ← Spec.map_comp_assoc, cancel_mono] at hl₂
  replace hl₁ := Spec.map_injective hl₁
  replace hl₂ := Spec.map_injective hl₂
  exact ⟨{ l'.hom with commutes' := fun r ↦ congr($hl₂ r) }, AlgHom.ext fun x ↦ congr($hl₁ x)⟩

/-- On affine opens `V ⊆ f⁻¹ U`, a formally étale morphism induces a formally étale ring map
`Γ(S, U) ⟶ Γ(X, V)`. -/
theorem FormallyEtale.formallyEtale_appLE (f : X ⟶ S) [FormallyEtale f] {U : S.Opens}
    (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) :
    (f.appLE U V e).hom.FormallyEtale := by
  have hs := FormallySmooth.formallySmooth_appLE f hU hV e
  have hu := f.formallyUnramified_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

end TauCeti.AlgebraicGeometry
