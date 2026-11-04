/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.Etale.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.Basic
public import TauCeti.RingTheory.RingHom.Smooth
public import TauCeti.RingTheory.RingHom.Unramified

/-!
# Formal smoothness of morphisms of affine schemes

For a ring map `φ : R ⟶ A`, the morphism `Spec A ⟶ Spec R` is formally smooth (respectively
formally étale) in the lifting sense exactly when `φ` is formally smooth (respectively formally
étale) in Mathlib's ring-theoretic sense. The comparison runs through global sections: an affine
first-order thickening `T ⟶ T'` is `Spec` of a surjection of rings with square-zero kernel.

## Main results

* `TauCeti.AlgebraicGeometry.FormallySmooth.SpecMap_iff`: `Spec.map φ` is formally smooth iff
  `φ` is.
* `TauCeti.AlgebraicGeometry.FormallyEtale.SpecMap_iff`: `Spec.map φ` is formally étale iff `φ`
  is.
* `TauCeti.AlgebraicGeometry.FormallySmooth.affineSpace`: affine space `𝔸(n; S) ⟶ S` is
  formally smooth over every base.

## References

* [Stacks Project, Definition 37.11.1](https://stacks.math.columbia.edu/tag/02H0).
* [Stacks Project, Definition 37.8.1](https://stacks.math.columbia.edu/tag/02HG).
-/

public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- For a ring map `φ : R ⟶ A`, `Spec A ⟶ Spec R` is formally smooth if and only if `φ` is
formally smooth. -/
theorem FormallySmooth.SpecMap_iff {R A : CommRingCat.{u}} (φ : R ⟶ A) :
    FormallySmooth (Spec.map φ) ↔ φ.hom.FormallySmooth := by
  refine ⟨fun H ↦ ?_, fun hφ ↦ ⟨fun {T T'} _ i _ a h w ↦ ?_⟩⟩
  · -- Test the lifting property on `Spec (B ⧸ I) ⟶ Spec B` for a square-zero ideal `I`.
    algebraize [φ.hom]
    refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ I hI g ↦ ?_
    have := IsFirstOrderThickening.SpecMap_mk I hI
    obtain ⟨l, hl₁, hl₂⟩ := H.exists_lift (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (by
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
        ext x
        exact g.commutes x)
    obtain ⟨l, rfl⟩ := Spec.map_surjective l
    rw [← Spec.map_comp] at hl₁ hl₂
    replace hl₁ := Spec.map_injective hl₁
    replace hl₂ := Spec.map_injective hl₂
    exact ⟨{ l.hom with commutes' := fun r ↦ congr($hl₂ r) }, AlgHom.ext fun x ↦ congr($hl₁ x)⟩
  · -- Transport the lifting problem to global sections and lift there.
    obtain ⟨_, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine i
    obtain ⟨α, hα⟩ := Spec.map_surjective (T.isoSpec.inv ≫ a)
    obtain ⟨η, hη⟩ := Spec.map_surjective (T'.isoSpec.inv ≫ h)
    have hw : φ ≫ α = η ≫ i.appTop := Spec.map_injective <| by
      rw [Spec.map_comp, Spec.map_comp, hα, hη, Category.assoc, w,
        Scheme.isoSpec_inv_naturality_assoc]
    obtain ⟨l, hl₁, hl₂⟩ := hφ.exists_lift η.hom i.appTop.hom hsurj
      ⟨2, IsFirstOrderThickening.ker_appTop_sq_eq_bot i⟩ α.hom congr(($hw).hom)
    refine ⟨T'.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom l), ?_, ?_⟩
    · rw [← Scheme.isoSpec_hom_naturality_assoc, ← Spec.map_comp,
        show CommRingCat.ofHom l ≫ i.appTop = α from CommRingCat.hom_ext hl₁, hα,
        Iso.hom_inv_id_assoc]
    · rw [Category.assoc, ← Spec.map_comp,
        show φ ≫ CommRingCat.ofHom l = η from CommRingCat.hom_ext hl₂, hη, Iso.hom_inv_id_assoc]

/-- For a ring map `φ : R ⟶ A`, `Spec A ⟶ Spec R` is formally étale if and only if `φ` is
formally étale. -/
theorem FormallyEtale.SpecMap_iff {R A : CommRingCat.{u}} (φ : R ⟶ A) :
    FormallyEtale (Spec.map φ) ↔ φ.hom.FormallyEtale := by
  refine ⟨fun H ↦ ?_, fun hφ ↦ ?_⟩
  · have hs := (FormallySmooth.SpecMap_iff φ).1 inferInstance
    algebraize [φ.hom]
    have : Algebra.FormallySmooth R A := hs
    suffices Algebra.FormallyUnramified R A from
      Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth
    -- Uniqueness of lifts along `Spec (B ⧸ I) ⟶ Spec B` gives formal unramifiedness.
    refine Algebra.FormallyUnramified.iff_comp_injective.2 fun B _ _ I hI g₁ g₂ e ↦ ?_
    have := IsFirstOrderThickening.SpecMap_mk I hI
    have := FormallyEtale.hom_ext (Spec.map φ)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (l₁ := Spec.map (CommRingCat.ofHom g₁.toRingHom))
      (l₂ := Spec.map (CommRingCat.ofHom g₂.toRingHom))
      (by
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
        ext x
        exact congr($e x))
      (by
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
        ext x
        exact (g₁.commutes x).trans (g₂.commutes x).symm)
    exact AlgHom.ext fun x ↦ congr($(Spec.map_injective this) x)
  · algebraize [φ.hom]
    have hφ' : φ.hom.FormallySmooth := (inferInstance : Algebra.FormallySmooth R A)
    have hφ'' : φ.hom.FormallyUnramified := (inferInstance : Algebra.FormallyUnramified R A)
    have := (FormallySmooth.SpecMap_iff φ).2 hφ'
    refine FormallyEtale.of_formallySmooth _ fun {T T'} _ i _ l₁ l₂ hi hf ↦ ?_
    -- Transport both lifts to global sections and compare them there.
    obtain ⟨_, -⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine i
    obtain ⟨m₁, hm₁⟩ := Spec.map_surjective (T'.isoSpec.inv ≫ l₁)
    obtain ⟨m₂, hm₂⟩ := Spec.map_surjective (T'.isoSpec.inv ≫ l₂)
    suffices m₁ = m₂ by
      rw [← cancel_epi T'.isoSpec.inv, ← hm₁, ← hm₂, this]
    have h₁ : φ ≫ m₁ = φ ≫ m₂ := Spec.map_injective <| by
      rw [Spec.map_comp, Spec.map_comp, hm₁, hm₂, Category.assoc, Category.assoc, hf]
    have h₂ : m₁ ≫ i.appTop = m₂ ≫ i.appTop := Spec.map_injective <| by
      rw [Spec.map_comp, Spec.map_comp, hm₁, hm₂, Scheme.isoSpec_inv_naturality_assoc,
        Scheme.isoSpec_inv_naturality_assoc, hi]
    exact CommRingCat.hom_ext <| hφ''.ext i.appTop.hom
      ⟨2, IsFirstOrderThickening.ker_appTop_sq_eq_bot i⟩ congr(($h₁).hom)
      congr(($h₂).hom)

/-- Affine space over any base is formally smooth: it is the base change of
`Spec ℤ[n] ⟶ Spec ℤ`, and polynomial rings are formally smooth. -/
instance FormallySmooth.affineSpace (n : Type u) (S : Scheme.{u}) :
    FormallySmooth (𝔸(n; S) ↘ S) := by
  have : FormallySmooth (terminal.from (Spec (CommRingCat.of (MvPolynomial n (ULift.{u} ℤ))))) := by
    have := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal (terminal.from _)
    rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C)),
      cancel_right_of_respectsIso (P := @FormallySmooth), FormallySmooth.SpecMap_iff,
      CommRingCat.hom_ofHom, ← MvPolynomial.algebraMap_eq, RingHom.formallySmooth_algebraMap]
    infer_instance
  exact FormallySmooth.pullback_fst _ _

end TauCeti.AlgebraicGeometry
