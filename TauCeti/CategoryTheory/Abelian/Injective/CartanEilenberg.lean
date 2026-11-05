/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.CategoryTheory.Abelian.Exact
public import TauCeti.CategoryTheory.Abelian.Injective.Horseshoe

/-!
# Cartan–Eilenberg resolutions of cochain complexes

Let `K` be a cochain complex in an abelian category with enough injectives, indexed by `ℕ`. For
each degree `q` there are two short exact sequences

* `0 ⟶ Zᵠ ⟶ Kᵠ ⟶ Kᵠ / Zᵠ ⟶ 0` (`CochainComplex.cyclesShortComplex`), with `Zᵠ = K.cycles q`;
* `0 ⟶ Kᵠ / Zᵠ ⟶ Zᵠ⁺¹ ⟶ Hᵠ⁺¹ ⟶ 0` (`CochainComplex.boundariesShortComplex`), whose first map is
  induced by the differential.

Choosing injective resolutions of the objects `Kᵠ / Zᵠ` and `Hᵠ⁺¹` and of `Z⁰`, the horseshoe lemma
(`CategoryTheory.InjectiveResolution.horseshoe`) gives injective resolutions of every `Zᵠ` and
every `Kᵠ` (`CochainComplex.cartanEilenbergResolution`), such that the differential of `K` lifts
to the composite `J(Kᵠ) ⟶ J(Kᵠ / Zᵠ) ⟶ J(Zᵠ⁺¹) ⟶ J(Kᵠ⁺¹)` of the chain maps of the horseshoes.
These lifts square to zero, and form the Cartan–Eilenberg double complex
`CochainComplex.cartanEilenberg K`, whose columns are injective resolutions of the terms of `K`,
the augmentations `Kᵠ ⟶ J(Kᵠ)⁰` commuting with the differentials
(`CochainComplex.cartanEilenbergResolution_ι₀_comp_cartanEilenbergD_f`). By construction, the
cycles, boundaries and cohomology of each row are resolved by the chosen resolutions of `Zᵠ`,
`Kᵠ / Zᵠ` and `Hᵠ`.

The Cartan–Eilenberg double complex is the input of the Grothendieck spectral sequence, and
hence of the Leray spectral sequence.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 5.7.
* [Stacks, Section 13.21 (015G)](https://stacks.math.columbia.edu/tag/015G)
-/

@[expose] public section

open CategoryTheory Category Limits Preadditive

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] (K : CochainComplex C ℕ)

/-- The short complex `Zᵠ ⟶ Kᵠ ⟶ Kᵠ / Zᵠ` of a cochain complex. -/
noncomputable abbrev cyclesShortComplex (q : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles q) (cokernel.π (K.iCycles q)) (cokernel.condition _)

/-- The short complex `Zᵠ ⟶ Kᵠ ⟶ Kᵠ / Zᵠ` is short exact. -/
lemma cyclesShortComplex_shortExact (q : ℕ) : (K.cyclesShortComplex q).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance

/-- The map `Kᵠ / Zᵠ ⟶ Zᵠ⁺¹` induced by the differential. -/
noncomputable def cokernelCyclesToCycles (q : ℕ) : cokernel (K.iCycles q) ⟶ K.cycles (q + 1) :=
  cokernel.desc _ (K.toCycles q (q + 1)) (by
    rw [← cancel_mono (K.iCycles (q + 1)), assoc, HomologicalComplex.toCycles_i,
      HomologicalComplex.iCycles_d, zero_comp])

@[reassoc (attr := simp)]
lemma π_cokernelCyclesToCycles (q : ℕ) :
    cokernel.π (K.iCycles q) ≫ K.cokernelCyclesToCycles q = K.toCycles q (q + 1) :=
  cokernel.π_desc _ _ _

@[reassoc (attr := simp)]
lemma cokernelCyclesToCycles_homologyπ (q : ℕ) :
    K.cokernelCyclesToCycles q ≫ K.homologyπ (q + 1) = 0 := by
  rw [← cancel_epi (cokernel.π (K.iCycles q)), π_cokernelCyclesToCycles_assoc,
    HomologicalComplex.toCycles_comp_homologyπ, comp_zero]

/-- The short complex `Kᵠ / Zᵠ ⟶ Zᵠ⁺¹ ⟶ Hᵠ⁺¹` of a cochain complex. -/
noncomputable abbrev boundariesShortComplex (q : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.cokernelCyclesToCycles q) (K.homologyπ (q + 1))
    (K.cokernelCyclesToCycles_homologyπ q)

/-- The map `Kᵠ / Zᵠ ⟶ Zᵠ⁺¹` is a monomorphism, since `Zᵠ` is the kernel of `Kᵠ ⟶ Zᵠ⁺¹`. -/
instance (q : ℕ) : Mono (K.cokernelCyclesToCycles q) := by
  refine Preadditive.mono_of_cancel_zero _ fun {T} x hx ↦ ?_
  obtain ⟨T', π, _, y, hy⟩ := surjective_up_to_refinements_of_epi (cokernel.π (K.iCycles q)) x
  have hy' : y ≫ K.d q (q + 1) = 0 := by
    rw [← HomologicalComplex.toCycles_i, ← π_cokernelCyclesToCycles, ← assoc, ← assoc, ← hy,
      assoc, assoc, reassoc_of% hx, zero_comp, comp_zero]
  have hy'' : y = K.liftCycles y (q + 1) (by simp) hy' ≫ K.iCycles q := by simp
  rw [← cancel_epi π, comp_zero, hy, hy'', assoc, cokernel.condition, comp_zero]

/-- The short complex `Kᵠ / Zᵠ ⟶ Zᵠ⁺¹ ⟶ Hᵠ⁺¹` is short exact. -/
lemma boundariesShortComplex_shortExact (q : ℕ) : (K.boundariesShortComplex q).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  have hS : (ShortComplex.mk _ _ (K.toCycles_comp_homologyπ q (q + 1))).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel q (q + 1) (by simp))
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x₂ hx₂
  obtain ⟨T', π, _, y, hy⟩ := hS.exact_up_to_refinements x₂ hx₂
  exact ⟨T', π, inferInstance, y ≫ cokernel.π _, by simpa using hy⟩

variable [HasInjectiveResolutions C]

/-- The chosen injective resolutions `J(Zᵠ)` of the cycles of a cochain complex: an arbitrary one
in degree `0`, and in degree `q + 1` the horseshoe of `0 ⟶ Kᵠ / Zᵠ ⟶ Zᵠ⁺¹ ⟶ Hᵠ⁺¹ ⟶ 0`. -/
noncomputable def cyclesResolution : (q : ℕ) → InjectiveResolution (K.cycles q)
  | 0 => injectiveResolution _
  | q + 1 => InjectiveResolution.horseshoe (K.boundariesShortComplex_shortExact q)
      (injectiveResolution _) (injectiveResolution _)

/-- The injective resolution `J(Kᵠ)` of the term of degree `q` of a cochain complex: the horseshoe
of `0 ⟶ Zᵠ ⟶ Kᵠ ⟶ Kᵠ / Zᵠ ⟶ 0`. -/
noncomputable def cartanEilenbergResolution (q : ℕ) : InjectiveResolution (K.X q) :=
  InjectiveResolution.horseshoe (K.cyclesShortComplex_shortExact q) (K.cyclesResolution q)
    (injectiveResolution _)

/-- The chain map `J(Zᵠ) ⟶ J(Kᵠ)` of the horseshoe, lifting `Zᵠ ⟶ Kᵠ`. -/
noncomputable def cyclesResolutionInl (q : ℕ) :
    (K.cyclesResolution q).cocomplex ⟶ (K.cartanEilenbergResolution q).cocomplex :=
  InjectiveResolution.horseshoeInl (K.cyclesShortComplex_shortExact q) (K.cyclesResolution q)
    (injectiveResolution _)

/-- The chain map `J(Kᵠ) ⟶ J(Kᵠ / Zᵠ)` of the horseshoe, lifting `Kᵠ ⟶ Kᵠ / Zᵠ`. -/
noncomputable def cartanEilenbergResolutionSnd (q : ℕ) :
    (K.cartanEilenbergResolution q).cocomplex ⟶
      (injectiveResolution (cokernel (K.iCycles q))).cocomplex :=
  InjectiveResolution.horseshoeSnd (K.cyclesShortComplex_shortExact q) (K.cyclesResolution q)
    (injectiveResolution _)

/-- The chain map `J(Kᵠ / Zᵠ) ⟶ J(Zᵠ⁺¹)` of the horseshoe, lifting `Kᵠ / Zᵠ ⟶ Zᵠ⁺¹`. -/
noncomputable def cokernelCyclesResolutionInl (q : ℕ) :
    (injectiveResolution (cokernel (K.iCycles q))).cocomplex ⟶
      (K.cyclesResolution (q + 1)).cocomplex :=
  InjectiveResolution.horseshoeInl (K.boundariesShortComplex_shortExact q)
    (injectiveResolution _) (injectiveResolution _)

@[reassoc (attr := simp)]
lemma cyclesResolutionInl_cartanEilenbergResolutionSnd (q : ℕ) :
    K.cyclesResolutionInl q ≫ K.cartanEilenbergResolutionSnd q = 0 :=
  (InjectiveResolution.horseshoeShortComplex (K.cyclesShortComplex_shortExact q)
    (K.cyclesResolution q) (injectiveResolution _)).zero

@[reassoc (attr := simp)]
lemma cyclesResolution_ι₀_comp_cyclesResolutionInl_f (q : ℕ) :
    (K.cyclesResolution q).ι₀ ≫ (K.cyclesResolutionInl q).f 0 =
      K.iCycles q ≫ (K.cartanEilenbergResolution q).ι₀ :=
  InjectiveResolution.ι₀_comp_horseshoeInl_f_zero (K.cyclesShortComplex_shortExact q)
    (K.cyclesResolution q) (injectiveResolution _)

@[reassoc (attr := simp)]
lemma cartanEilenbergResolution_ι₀_comp_cartanEilenbergResolutionSnd_f (q : ℕ) :
    (K.cartanEilenbergResolution q).ι₀ ≫ (K.cartanEilenbergResolutionSnd q).f 0 =
      cokernel.π (K.iCycles q) ≫ (injectiveResolution (cokernel (K.iCycles q))).ι₀ :=
  InjectiveResolution.horseshoe_ι₀_comp_horseshoeSnd_f_zero (K.cyclesShortComplex_shortExact q)
    (K.cyclesResolution q) (injectiveResolution _)

@[reassoc (attr := simp)]
lemma ι₀_comp_cokernelCyclesResolutionInl_f (q : ℕ) :
    (injectiveResolution (cokernel (K.iCycles q))).ι₀ ≫ (K.cokernelCyclesResolutionInl q).f 0 =
      K.cokernelCyclesToCycles q ≫ (K.cyclesResolution (q + 1)).ι₀ :=
  InjectiveResolution.ι₀_comp_horseshoeInl_f_zero (K.boundariesShortComplex_shortExact q)
    (injectiveResolution _) (injectiveResolution _)

/-- The lift `J(Kᵠ) ⟶ J(Kᵠ⁺¹)` of the differential of `K`: the composite
`J(Kᵠ) ⟶ J(Kᵠ / Zᵠ) ⟶ J(Zᵠ⁺¹) ⟶ J(Kᵠ⁺¹)` of the chain maps of the horseshoes. -/
noncomputable def cartanEilenbergD (q : ℕ) :
    (K.cartanEilenbergResolution q).cocomplex ⟶ (K.cartanEilenbergResolution (q + 1)).cocomplex :=
  K.cartanEilenbergResolutionSnd q ≫ K.cokernelCyclesResolutionInl q ≫
    K.cyclesResolutionInl (q + 1)

@[reassoc (attr := simp)]
lemma cartanEilenbergD_comp_cartanEilenbergD (q : ℕ) :
    K.cartanEilenbergD q ≫ K.cartanEilenbergD (q + 1) = 0 := by
  simp [cartanEilenbergD]

/-- The lifts of the differential of `K` commute with the augmentations: the square
`Kᵠ ⟶ J(Kᵠ)⁰`, `Kᵠ⁺¹ ⟶ J(Kᵠ⁺¹)⁰` commutes. -/
@[reassoc]
lemma cartanEilenbergResolution_ι₀_comp_cartanEilenbergD_f (q : ℕ) :
    (K.cartanEilenbergResolution q).ι₀ ≫ (K.cartanEilenbergD q).f 0 =
      K.d q (q + 1) ≫ (K.cartanEilenbergResolution (q + 1)).ι₀ := by
  simp [cartanEilenbergD]

/-- The Cartan–Eilenberg double complex of a cochain complex `K`: its `q`-th column is the
injective resolution `J(Kᵠ)`, and its differentials lift the differential of `K`. -/
noncomputable def cartanEilenberg : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  CochainComplex.of (fun q ↦ (K.cartanEilenbergResolution q).cocomplex) K.cartanEilenbergD
    K.cartanEilenbergD_comp_cartanEilenbergD

lemma cartanEilenberg_X (q : ℕ) :
    K.cartanEilenberg.X q = (K.cartanEilenbergResolution q).cocomplex := rfl

lemma cartanEilenberg_d (q : ℕ) : K.cartanEilenberg.d q (q + 1) = K.cartanEilenbergD q := by
  dsimp only [cartanEilenberg]
  exact CochainComplex.of_d _ _ q


end CochainComplex
