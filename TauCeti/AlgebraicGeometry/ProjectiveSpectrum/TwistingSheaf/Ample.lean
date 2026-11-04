/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.TensorProduct

/-!
# Ampleness of `𝒪(1)` on `Proj`

Let `A` be a graded ring such that the standard opens `D₊(f)` of the elements `f` of degree one
cover `Proj A`, so that the twisting sheaf `𝒪(1)` is invertible. For `r` of degree one, the global
section `r / 1` of `𝒪(1)` vanishes nowhere exactly on `D₊(r)`. Since the open sets `D₊(f)` are
affine, `𝒪(1)` is ample as soon as `Proj A` is quasi-compact.

## Main results

* `AlgebraicGeometry.Proj.nonvanishingLocus_toTwistingSheaf`: the nonvanishing locus of the global
  section `r / 1` of `𝒪(1)` is `D₊(r)`.
* `AlgebraicGeometry.Proj.isAmple_twistingSheaf_one`: `𝒪(1)` is ample on a quasi-compact `Proj A`,
  and so is every `𝒪(n)` with `n > 0` (`AlgebraicGeometry.Proj.isAmple_twistingSheaf`).

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.7, Example 7.1.1 and Proposition 7.10.
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Proj

universe u

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]
variable {ι : Type u} (f : ι → A) (hf : ∀ i, f i ∈ 𝒜 1)
  (hcover : ⨆ i, basicOpen 𝒜 (f i) = ⊤)

/-- **The nonvanishing locus of a degree-one section of `𝒪(1)` is its standard open.** If the
standard opens of degree-one elements cover `Proj A`, then for `r` of degree one the global section
`r / 1` of `𝒪(1)` vanishes nowhere exactly on `D₊(r)`: on `D₊(r)` it is the basis section of the
standard trivialization, and at a point `x` of `D₊(f)`, with `f` of degree one, at which it
generates `𝒪(1)`, the section `f / 1` is a multiple of it, so `r` cannot lie in `x`. -/
theorem nonvanishingLocus_toTwistingSheaf (r : 𝒜 1) :
    haveI := isInvertible_twistingSheaf_of_iSup_eq_top f hf hcover 1
    (twistingSheaf 𝒜 1).nonvanishingLocus (toTwistingSheaf 𝒜 Nat.cast_one ⊤ r) =
      basicOpen 𝒜 (r : A) := by
  have := isInvertible_twistingSheaf_of_iSup_eq_top f hf hcover 1
  -- On an open of `D₊(g)`, the section `g / 1` is the basis section `g¹` of the trivialization:
  -- both take the value `g / 1`, written `g ^ 1 / g ^ 0` for the basis section.
  have hgen (g : 𝒜 1) {W : (Proj 𝒜).Opens} (hW : W ≤ basicOpen 𝒜 (g : A)) :
      toTwistingSheaf 𝒜 Nat.cast_one W g = twistingSheaf.chartGenerator 1 (g : A) g.2 W hW :=
    twistingSheaf.ext fun x ↦ (toTwistingSheaf_apply_apply Nat.cast_one W g x).trans <|
      .trans (by congr 1 <;> simp; rfl)
        (twistingSheaf.chartGenerator_apply 1 (g : A) g.2 W hW x).symm
  refine le_antisymm (fun x hx ↦ ?_) ((Scheme.Modules.le_nonvanishingLocus_iff _
    (homOfLE le_top)).mpr fun W j ↦ ?_)
  · obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (hcover.ge (Opens.mem_top x))
    -- Over `W = X_{r/1} ∩ D₊(f i)`, the section `f i / 1` is a multiple `a • r / 1`.
    let W := (twistingSheaf 𝒜 1).nonvanishingLocus (toTwistingSheaf 𝒜 Nat.cast_one ⊤ r) ⊓
      basicOpen 𝒜 (f i)
    have hW := (Scheme.Modules.le_nonvanishingLocus_iff _ (homOfLE le_top)).mp
      (inf_le_left : W ≤ _) W (𝟙 W)
    obtain ⟨a, ha⟩ := hW.2 (toTwistingSheaf 𝒜 Nat.cast_one W ⟨f i, hf i⟩)
    -- The localization at the prime `x`, in which the values of sections of `𝒪(1)` lie.
    have := x.isPrime
    let P := x.asHomogeneousIdeal.toIdeal
    have hax : (a.1 ⟨x, hx, hxi⟩).val * algebraMap A (Localization.AtPrime P) r =
        algebraMap A (Localization.AtPrime P) (f i) := by
      rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap]
      exact congrArg (fun s ↦ s.1 ⟨x, hx, hxi⟩) ha
    -- The image of `f i` is a unit of the localization at `x`, so the image of `r` is one too.
    have hunit :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P (f i)).mpr hxi
    rw [← hax] at hunit
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P r).mp
      (isUnit_of_mul_isUnit_right hunit)
  · -- On an open of `D₊(r)`, multiplication by `r / 1` is the standard trivialization.
    simp only [res_toTwistingSheaf]
    rw [hgen r j.le]
    convert (twistingSheaf.chartSectionsLinearEquiv 1 (r : A) r.2 W j.le).bijective using 1
    exact funext fun a ↦ (twistingSheaf.chartSectionsLinearEquiv_apply _ _ _ _ _ a).symm

/-- **`𝒪(1)` is ample on a quasi-compact `Proj`.** If the standard opens of degree-one elements
cover `Proj A` and `Proj A` is quasi-compact, then `𝒪(1)` is ample: each point lies in some `D₊(f)`
with `f` of degree one, which is affine and the nonvanishing locus of the global section `f / 1`. -/
theorem isAmple_twistingSheaf_one [CompactSpace (Proj 𝒜)] :
    (TauCeti.AlgebraicGeometry.LineBundleClass.mk
      ⟨twistingSheaf 𝒜 1, isInvertible_twistingSheaf_of_iSup_eq_top f hf hcover 1⟩).IsAmple where
  compactSpace := inferInstance
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (hcover.ge (Opens.mem_top x))
    have h := nonvanishingLocus_toTwistingSheaf f hf hcover ⟨f i, hf i⟩
    refine ⟨1, Nat.one_pos, _, (pow_one _).symm, toTwistingSheaf 𝒜 Nat.cast_one ⊤ ⟨f i, hf i⟩,
      ?_, ?_⟩
    · exact h ▸ hxi
    · exact h ▸ isAffineOpen_basicOpen 𝒜 (f i) (hf i) Nat.one_pos

/-- **`𝒪(n)` is ample on a quasi-compact `Proj` for `n > 0`**, as the class of `𝒪(n)` is the
`n`-th power of the class of the ample `𝒪(1)`. -/
theorem isAmple_twistingSheaf [CompactSpace (Proj 𝒜)] {n : ℕ} (hn : 0 < n) :
    (TauCeti.AlgebraicGeometry.LineBundleClass.mk
      ⟨twistingSheaf 𝒜 n, isInvertible_twistingSheaf_of_iSup_eq_top f hf hcover n⟩).IsAmple := by
  rw [lineBundleClass_twistingSheaf_eq_zpow f hf hcover, zpow_natCast,
    TauCeti.AlgebraicGeometry.LineBundleClass.isAmple_pow_iff hn]
  exact isAmple_twistingSheaf_one f hf hcover

end AlgebraicGeometry.Proj
