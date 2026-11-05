/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.IsLocalizedModule
public import TauCeti.RingTheory.Derivation.ToSquareZero

/-!
# Derivations into a localized square-zero ideal

Let `I` and `I'` be square-zero ideals of `R`-algebras `C` and `C'`, where `C'` is a `C`-algebra
mapping `I` into `I'`, and let `A` be an `R`-algebra with compatible maps `A → C ⧸ I` and
`A → C' ⧸ I'`, so that `I` and `I'` are `A`-modules (`Ideal.moduleOfSqEqBot`). If a `C`-linear
map `ι : I → I'` (typically the one induced by `C → C'`) is a localization at the powers of
`g : C` and `Ω[A⁄R]` is finitely presented, then so is post-composition
`Der_R(A, I) → Der_R(A, I')`: every derivation into `I'` is, after multiplication by a power of
`g`, the image of a derivation into `I`, and two derivations into `I` with the same image agree
after multiplication by a power of `g`.

This is `LinearMap.isLocalizedModule_compDerRestrictScalars` over the ring `C ⧸ I`, through which
the actions of `A` and `C` on `I` factor. It is the algebraic form of the quasi-coherence of the
sheaf of derivations into the ideal of a first-order thickening.

## Main results

* `Ideal.exists_derivation_comp_eq_pow_mul_of_sq_eq_bot`: every derivation into `I'` is the
  image of a derivation into `I` after multiplication by a power of `g`.
* `Ideal.exists_pow_mul_eq_of_derivation_comp_eq_of_sq_eq_bot`: two derivations into `I` with the
  same image in `I'` agree after multiplication by a power of `g`.
-/

public section

namespace Ideal

variable {R A C C' : Type*} [CommRing R] [CommRing A] [CommRing C] [CommRing C'] [Algebra R A]
  [Algebra R C] [Algebra R C'] [Algebra C C'] [IsScalarTower R C C']
  {I : Ideal C} {I' : Ideal C'} (hI : I ^ 2 = ⊥) (hI' : I' ^ 2 = ⊥)
  [Algebra A (C ⧸ I)] [Algebra A (C' ⧸ I')] [IsScalarTower R A (C ⧸ I)]
  [IsScalarTower R A (C' ⧸ I')]
  (hII' : ∀ x ∈ I, algebraMap C C' x ∈ I')
  (hA : ∀ a : A, Ideal.quotientMap I' (algebraMap C C') (fun x hx ↦ by
      simpa using hII' x hx) (algebraMap A (C ⧸ I) a) = algebraMap A (C' ⧸ I') a)
  [Module.FinitePresentation A Ω[A⁄R]] (g : C) (ι : I →ₗ[C] I') [IsLocalizedModule (.powers g) ι]

include hII' hA in
/-- Post-composition of derivations into square-zero ideals with a localization `ι : I → I'` at the
powers of `g` is a localization at the powers of `g`: the surjectivity and injectivity halves. -/
private theorem compDer_surj_and_exists_of_eq_of_sq_eq_bot :
    letI := moduleOfSqEqBot A hI
    letI := moduleOfSqEqBot A hI'
    haveI := isScalarTower_of_sq_eq_bot (R := R) (A := A) hI
    haveI := isScalarTower_of_sq_eq_bot (R := R) (A := A) hI'
    (∀ d' : Derivation R A I', ∃ (n : ℕ) (d : Derivation R A I),
      ∀ x, (ι (d x) : C') = algebraMap C C' (g ^ n) * d' x) ∧
    ∀ d₁ d₂ : Derivation R A I, (∀ x, ι (d₁ x) = ι (d₂ x)) →
      ∃ n : ℕ, ∀ x, g ^ n * (d₁ x : C) = g ^ n * d₂ x := by
  let := moduleOfSqEqBot A hI
  let := moduleOfSqEqBot A hI'
  have := isScalarTower_of_sq_eq_bot (R := R) (A := A) hI
  have := isScalarTower_of_sq_eq_bot (R := R) (A := A) hI'
  -- The actions of `A`, `R` and `C` on `I` and `I'` factor through `C ⧸ I`.
  let φ : C ⧸ I →+* C' ⧸ I' := Ideal.quotientMap I' (algebraMap C C') hII'
  let : Module (C ⧸ I) I := (isTorsionBySet_self_of_sq_eq_bot hI).module
  let : Module (C' ⧸ I') I' := (isTorsionBySet_self_of_sq_eq_bot hI').module
  let : Module (C ⧸ I) I' := Module.compHom I' φ
  have h₁ (c : C) (m : I) : (Ideal.Quotient.mk I c) • m = c • m :=
    (isTorsionBySet_self_of_sq_eq_bot hI).mk_smul c m
  have h₂ (c : C) (m : I') : (Ideal.Quotient.mk I c : C ⧸ I) • m = c • m := by
    change Ideal.Quotient.mk I' (algebraMap C C' c) • m = _
    rw [(isTorsionBySet_self_of_sq_eq_bot hI').mk_smul, algebraMap_smul]
  have : IsScalarTower A (C ⧸ I) I := ⟨fun a b m ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩
  have : IsScalarTower A (C ⧸ I) I' := ⟨fun a b m ↦ by
    rw [Algebra.smul_def]
    change φ (_ * b) • m = algebraMap A (C' ⧸ I') a • (φ b • m)
    rw [map_mul, mul_smul, ← hA]⟩
  have : IsScalarTower C (C ⧸ I) I := ⟨fun c b m ↦ by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    change (Ideal.Quotient.mk I c * Ideal.Quotient.mk I b) • m = _
    rw [← map_mul, h₁, h₁, mul_smul]⟩
  have : IsScalarTower C (C ⧸ I) I' := ⟨fun c b m ↦ by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    change (Ideal.Quotient.mk I c * Ideal.Quotient.mk I b) • m = _
    rw [← map_mul, h₂, h₂, mul_smul]⟩
  have : IsScalarTower R (C ⧸ I) I := ⟨fun r b m ↦ by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R C (C ⧸ I),
      Ideal.Quotient.algebraMap_eq, mul_smul, h₁, algebraMap_smul]⟩
  have : IsScalarTower R (C ⧸ I) I' := ⟨fun r b m ↦ by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R C (C ⧸ I),
      Ideal.Quotient.algebraMap_eq, mul_smul, h₂, algebraMap_smul]⟩
  let ι' : I →ₗ[C ⧸ I] I' :=
    { toFun := ι
      map_add' := ι.map_add
      map_smul' b m := by
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
        rw [h₁, RingHom.id_apply, h₂, ι.map_smul] }
  have : IsLocalizedModule (.powers g) (ι'.restrictScalars C) := ‹IsLocalizedModule _ ι›
  have := IsLocalizedModule.of_restrictScalars (.powers g) ι'
  let S := Algebra.algebraMapSubmonoid (C ⧸ I) (.powers g)
  have hS (s : S) : ∃ n : ℕ, (s : C ⧸ I) = Ideal.Quotient.mk I (g ^ n) := by
    obtain ⟨_, ⟨n, rfl⟩, hs⟩ := s.2
    exact ⟨n, hs.symm⟩
  refine ⟨fun d' ↦ ?_, fun d₁ d₂ e ↦ ?_⟩
  · obtain ⟨⟨d, s⟩, hs⟩ := IsLocalizedModule.surj S (LinearMap.compDerRestrictScalars R A ι') d'
    obtain ⟨n, hn⟩ := hS s
    refine ⟨n, d, fun x ↦ ?_⟩
    have := congrArg (fun D : Derivation R A I' ↦ (D x : C')) hs
    simp only [smul_apply, LinearMap.compDerRestrictScalars_apply] at this
    rw [show ι (d x) = ι' (d x) from rfl, ← this, Submonoid.smul_def, hn, h₂,
      Submodule.coe_smul_of_tower, Algebra.smul_def]
  · obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := S)
      (f := LinearMap.compDerRestrictScalars R A ι')
      (Derivation.ext fun x ↦ by
        simp only [LinearMap.compDerRestrictScalars_apply]
        exact e x)
    obtain ⟨n, hn⟩ := hS s
    refine ⟨n, fun x ↦ ?_⟩
    have := congrArg (fun D : Derivation R A I ↦ (D x : C)) hs
    simp only [smul_apply, Submonoid.smul_def, hn, h₁] at this
    simpa only [Submodule.coe_smul, smul_eq_mul] using this

include hII' hA in
/-- Every `R`-derivation `A → I'` is, after multiplication by a power of `g`, the image of an
`R`-derivation `A → I` under the localization `ι : I → I'` at the powers of `g`. -/
theorem exists_derivation_comp_eq_pow_mul_of_sq_eq_bot :
    letI := moduleOfSqEqBot A hI
    letI := moduleOfSqEqBot A hI'
    haveI := isScalarTower_of_sq_eq_bot (R := R) (A := A) hI
    haveI := isScalarTower_of_sq_eq_bot (R := R) (A := A) hI'
    ∀ d' : Derivation R A I', ∃ (n : ℕ) (d : Derivation R A I),
      ∀ x, (ι (d x) : C') = algebraMap C C' (g ^ n) * d' x :=
  (compDer_surj_and_exists_of_eq_of_sq_eq_bot hI hI' hII' hA g ι).1

include hI' hII' hA in
/-- Two `R`-derivations `A → I` with the same image under the localization `ι : I → I'` at the
powers of `g` agree after multiplication by a power of `g`. -/
theorem exists_pow_mul_eq_of_derivation_comp_eq_of_sq_eq_bot :
    letI := moduleOfSqEqBot A hI
    haveI := isScalarTower_of_sq_eq_bot (R := R) (A := A) hI
    ∀ d₁ d₂ : Derivation R A I, (∀ x, ι (d₁ x) = ι (d₂ x)) →
      ∃ n : ℕ, ∀ x, g ^ n * (d₁ x : C) = g ^ n * d₂ x :=
  (compDer_surj_and_exists_of_eq_of_sq_eq_bot hI hI' hII' hA g ι).2

end Ideal
