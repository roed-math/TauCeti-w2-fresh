/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.TensorProduct

/-!
# Ampleness of `𝒪(1)` on `Proj`

Let `A` be a graded ring such that the standard opens `D₊(f)` of the elements `f` of degree one
cover `Proj A`, so that the twisting sheaves `𝒪(n)` are invertible. For `r` of degree `d`, the
global section `r / 1` of `𝒪(d)` vanishes nowhere exactly on `D₊(r)`. Every open `U` of `Proj A`
is a union of such standard opens `D₊(g) ⊆ U` with `g` of positive degree, and the open sets
`D₊(g)` are affine. So `𝒪(1)` pulls back to an ample line bundle along every immersion
`Z ⟶ Proj A` from a quasi-compact scheme. In particular `𝒪(1)` is ample as soon as `Proj A` is
quasi-compact. On `Proj A` this needs no extension of sections from nonvanishing loci: the
sections `g / 1` are already global.

## Main results

* `AlgebraicGeometry.Proj.nonvanishingLocus_toTwistingSheaf`: the nonvanishing locus of the global
  section `r / 1` of `𝒪(d)` is `D₊(r)`.
* `AlgebraicGeometry.Proj.exists_mem_basicOpen_le`: the standard opens of homogeneous elements of
  positive degree form a basis of the topology of `Proj A`.
* `AlgebraicGeometry.Proj.isAmple_pullback_twistingSheaf_one`: `𝒪(1)` pulls back to an ample line
  bundle along an immersion from a quasi-compact scheme.
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

/-- **The nonvanishing locus of a section `r / 1` of `𝒪(d)` is its standard open.** If the
standard opens of degree-one elements cover `Proj A`, then for `r` of degree `d` the global section
`r / 1` of `𝒪(d)` vanishes nowhere exactly on `D₊(r)`. At a point `x` of `D₊(f)`, with `f` of degree
one, the standard basis section `fᵈ / 1` of `𝒪(d)` generates the stalk. If `r / 1` generates it too,
then `fᵈ / 1` is a multiple of `r / 1`, so `r` cannot lie in `x`. Conversely, on `D₊(r) ∩ D₊(f)` the
section `fᵈ / 1` is the multiple `(fᵈ / r) • (r / 1)`. -/
theorem nonvanishingLocus_toTwistingSheaf {n : ℤ} {d : ℕ} (hd : (d : ℤ) = n) (r : 𝒜 d) :
    haveI := isInvertible_twistingSheaf_of_iSup_eq_top f hf hcover n
    (twistingSheaf 𝒜 n).nonvanishingLocus (toTwistingSheaf 𝒜 hd ⊤ r) =
      basicOpen 𝒜 (r : A) := by
  have := isInvertible_twistingSheaf_of_iSup_eq_top f hf hcover n
  have hfd (i : ι) : f i ^ d ∈ 𝒜 d := by simpa using SetLike.pow_mem_graded d (hf i)
  -- The standard basis section `fⁿ` of `𝒪(n)` vanishes nowhere on its domain.
  have hchart (i : ι) {W : (Proj 𝒜).Opens} (hW : W ≤ basicOpen 𝒜 (f i)) :
      W ≤ (twistingSheaf 𝒜 n).nonvanishingLocus
        (twistingSheaf.chartGenerator n (f i) (hf i) W hW) :=
    (Scheme.Modules.le_nonvanishingLocus_iff _ (𝟙 W)).mpr fun W' j ↦ by
      rw [Category.comp_id, twistingSheaf.res_chartGenerator]
      convert (twistingSheaf.chartSectionsLinearEquiv n (f i) (hf i) W'
        (j.le.trans hW)).bijective using 1
      exact funext fun a ↦ (twistingSheaf.chartSectionsLinearEquiv_apply _ _ _ _ _ a).symm
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (hcover.ge (Opens.mem_top x))
    -- Over `W = X_{r/1} ∩ D₊(f i)`, the section `f iᵈ / 1` is a multiple `a • r / 1`.
    let W := (twistingSheaf 𝒜 n).nonvanishingLocus (toTwistingSheaf 𝒜 hd ⊤ r) ⊓
      basicOpen 𝒜 (f i)
    have hW := (Scheme.Modules.le_nonvanishingLocus_iff _ (homOfLE le_top)).mp
      (inf_le_left : W ≤ _) W (𝟙 W)
    obtain ⟨a, ha⟩ := hW.2 (toTwistingSheaf 𝒜 hd W ⟨f i ^ d, hfd i⟩)
    -- The localization at the prime `x`, in which the values of sections of `𝒪(n)` lie.
    have := x.isPrime
    let P := x.asHomogeneousIdeal.toIdeal
    have hax : (a.1 ⟨x, hx, hxi⟩).val * algebraMap A (Localization.AtPrime P) r =
        algebraMap A (Localization.AtPrime P) (f i ^ d) := by
      rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap]
      exact congrArg (fun s ↦ s.1 ⟨x, hx, hxi⟩) ha
    -- The image of `f iᵈ` is a unit of the localization at `x`, so the image of `r` is one too.
    have hunit := (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P
      (f i ^ d)).mpr fun h ↦ hxi (x.isPrime.mem_of_pow_mem d h)
    rw [← hax] at hunit
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P r).mp
      (isUnit_of_mul_isUnit_right hunit)
  · obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (hcover.ge (Opens.mem_top x))
    let W := basicOpen 𝒜 (r : A) ⊓ basicOpen 𝒜 (f i)
    -- On `W`, the regular function `f iᵈ / r` times `r / 1` is the standard basis section.
    let a : Γ(Proj 𝒜, W) := (sectionsLinearEquivTwistingSheafZero 𝒜 W).symm
      (twistingSheaf.const (n := 0) (i := d) (j := d) (by simp) (f i ^ d) r (hfd i) r.2 W
        inf_le_left)
    have haval (y : W) : (a.1 y).val = Localization.mk (f i ^ d) ⟨r, (inf_le_left : W ≤ _) y.2⟩ :=
      sectionsLinearEquivTwistingSheafZero_symm_apply_val _ _ y
    have ha : a • (twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top : W ⟶ ⊤).op
        (toTwistingSheaf 𝒜 hd ⊤ r) =
          twistingSheaf.chartGenerator n (f i) (hf i) W inf_le_right := by
      refine twistingSheaf.ext fun (y : W) ↦ ?_
      have := y.1.isPrime
      refine (twistingSheaf.smul_apply a _ y).trans ?_
      rw [haval, res_toTwistingSheaf, toTwistingSheaf_apply_apply,
        twistingSheaf.chartGenerator_apply, Localization.mk_mul]
      refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
      subst hd
      simp only [Submonoid.coe_mul, Submonoid.coe_one, Int.toNat_natCast,
        show (-(d : ℤ)).toNat = 0 by omega, pow_zero]
      ring
    have h := hchart i (inf_le_right : W ≤ _) (⟨hx, hxi⟩ : x ∈ W)
    rw [← ha, Scheme.Modules.nonvanishingLocus_smul, Scheme.Modules.nonvanishingLocus_map] at h
    exact h.2.2

include hf hcover in
/-- **Every open of `Proj A` is a union of standard opens of positive degree.** If the standard
opens of degree-one elements cover `Proj A`, every point `x` of an open `U` lies in a standard open
`D₊(g) ⊆ U` of a homogeneous element `g` of positive degree: if `x ∈ D₊(a) ⊆ U` and `x ∈ D₊(f)` with
`f` of degree one, then `x` lies in `D₊(f aₖ)` for some homogeneous component `aₖ` of `a`. -/
theorem exists_mem_basicOpen_le {U : (Proj 𝒜).Opens} {x : Proj 𝒜} (hx : x ∈ U) :
    ∃ (d : ℕ) (g : 𝒜 d), 0 < d ∧ x ∈ basicOpen 𝒜 (g : A) ∧ basicOpen 𝒜 (g : A) ≤ U := by
  obtain ⟨_, ⟨a, rfl⟩, hxa, haU⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen 𝒜) hx
  rw [basicOpen_eq_iSup_proj] at hxa haU
  obtain ⟨k, hk⟩ := Opens.mem_iSup.mp hxa
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (hcover.ge (Opens.mem_top x))
  have hak : GradedRing.proj 𝒜 k a ∈ 𝒜 k := by
    rw [GradedRing.proj_apply]
    exact SetLike.coe_mem _
  refine ⟨1 + k, ⟨f i * GradedRing.proj 𝒜 k a, SetLike.mul_mem_graded (hf i) hak⟩, by omega, ?_, ?_⟩
  · rw [basicOpen_mul]
    exact ⟨hxi, hk⟩
  · rw [basicOpen_mul]
    exact inf_le_right.trans ((le_iSup (fun k ↦ basicOpen 𝒜 (GradedRing.proj 𝒜 k a)) k).trans haU)

/-- **`𝒪(1)` pulls back to an ample line bundle along an immersion from a quasi-compact
scheme.** Suppose the standard opens of degree-one elements cover `Proj A`, `Z` is quasi-compact
and `j : Z ⟶ Proj A` is an immersion. Then `j^* 𝒪(1)` is ample. Each point `z` of `Z` maps into
the open `U` in which `Z` is closed, and `j z` lies in a standard open `D₊(g) ⊆ U` with `g` of some
degree `d > 0`. The pullback of the global section `g / 1` of `𝒪(d)` vanishes nowhere exactly on
`j⁻¹ D₊(g)`. That open is affine, because `Z` is a closed subscheme of `U` and `D₊(g)` is an
affine open of `U`. -/
theorem isAmple_pullback_twistingSheaf_one {Z : Scheme.{u}} [CompactSpace Z] (j : Z ⟶ Proj 𝒜)
    [IsImmersion j] :
    (TauCeti.AlgebraicGeometry.LineBundleClass.pullback j
      (TauCeti.AlgebraicGeometry.LineBundleClass.mk
        ⟨twistingSheaf 𝒜 1, isInvertible_twistingSheaf_of_iSup_eq_top f hf hcover 1⟩)).IsAmple where
  compactSpace := inferInstance
  exists_isAffineOpen_nonvanishingLocus z := by
    obtain ⟨d, g, hd, hzg, hgU⟩ :=
      exists_mem_basicOpen_le f hf hcover (U := j.coborderRange) (subset_coborder ⟨z, rfl⟩)
    let O : TauCeti.AlgebraicGeometry.InvertibleSheaf (Proj 𝒜) :=
      ⟨twistingSheaf 𝒜 d, isInvertible_twistingSheaf_of_iSup_eq_top f hf hcover d⟩
    have : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible (Proj 𝒜) O.obj := O.property
    have : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Z
        ((Scheme.Modules.pullback j).obj O.obj) :=
      ((TauCeti.AlgebraicGeometry.InvertibleSheaf.pullback j).obj O).property
    -- The pulled-back section `j^* (g / 1)` vanishes nowhere exactly on `j⁻¹ D₊(g)`.
    let s : Γ(((TauCeti.AlgebraicGeometry.InvertibleSheaf.pullback j).obj O).obj, ⊤) :=
      j.pullbackSections O.obj ⊤ (toTwistingSheaf 𝒜 rfl ⊤ g)
    have hs :
        ((TauCeti.AlgebraicGeometry.InvertibleSheaf.pullback j).obj O).obj.nonvanishingLocus s =
          j ⁻¹ᵁ basicOpen 𝒜 (g : A) :=
      (Scheme.Modules.nonvanishingLocus_pullbackSections (M := O.obj) j _).trans
        (congrArg (j ⁻¹ᵁ ·) (nonvanishingLocus_toTwistingSheaf f hf hcover rfl g))
    refine ⟨d, hd, (TauCeti.AlgebraicGeometry.InvertibleSheaf.pullback j).obj O, ?_, s,
      hs ▸ hzg, hs ▸ ?_⟩
    · rw [← TauCeti.AlgebraicGeometry.LineBundleClass.pullback_mk,
        lineBundleClass_twistingSheaf_eq_zpow f hf hcover, zpow_natCast,
        ← TauCeti.AlgebraicGeometry.LineBundleClass.pullbackHom_apply, map_pow,
        TauCeti.AlgebraicGeometry.LineBundleClass.pullbackHom_apply]
    · -- `j` is the closed immersion `Z ⟶ U` followed by the inclusion of `U`.
      have h := ((isAffineOpen_basicOpen 𝒜 (g : A) g.2 hd).preimage_of_isOpenImmersion
        j.coborderRange.ι (by simpa using hgU)).preimage j.liftCoborder
      rwa [← Scheme.Hom.comp_preimage, j.liftCoborder_ι] at h

/-- **`𝒪(1)` is ample on a quasi-compact `Proj`.** If the standard opens of degree-one elements
cover `Proj A` and `Proj A` is quasi-compact, then `𝒪(1)` is ample: this is the case of the
identity immersion in `AlgebraicGeometry.Proj.isAmple_pullback_twistingSheaf_one`. -/
theorem isAmple_twistingSheaf_one [CompactSpace (Proj 𝒜)] :
    (TauCeti.AlgebraicGeometry.LineBundleClass.mk
      ⟨twistingSheaf 𝒜 1, isInvertible_twistingSheaf_of_iSup_eq_top f hf hcover 1⟩).IsAmple := by
  simpa only [TauCeti.AlgebraicGeometry.LineBundleClass.pullback_id] using
    isAmple_pullback_twistingSheaf_one f hf hcover (𝟙 (Proj 𝒜))

/-- **`𝒪(n)` is ample on a quasi-compact `Proj` for `n > 0`**, as the class of `𝒪(n)` is the
`n`-th power of the class of the ample `𝒪(1)`. -/
theorem isAmple_twistingSheaf [CompactSpace (Proj 𝒜)] {n : ℕ} (hn : 0 < n) :
    (TauCeti.AlgebraicGeometry.LineBundleClass.mk
      ⟨twistingSheaf 𝒜 n, isInvertible_twistingSheaf_of_iSup_eq_top f hf hcover n⟩).IsAmple := by
  rw [lineBundleClass_twistingSheaf_eq_zpow f hf hcover, zpow_natCast,
    TauCeti.AlgebraicGeometry.LineBundleClass.isAmple_pow_iff hn]
  exact isAmple_twistingSheaf_one f hf hcover

end AlgebraicGeometry.Proj
