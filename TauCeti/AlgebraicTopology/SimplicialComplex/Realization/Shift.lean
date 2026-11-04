/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Basic
public import Mathlib.Topology.Order.Lattice

/-!
# Sliding a point within its open simplex

Let `a` and `c` be two points of a weak realization in the same open simplex, so that they have
the same support `σ`. Write every point `y` as `y = λ • a + r`, where `λ ≥ 0` is the largest
coefficient with `r ≥ 0`, namely `λ = min_{w ∈ σ} y w / a w`; then `λ > 0` only when `σ` lies in
the support of `y`. The map `y ↦ λ • c + r` is a homeomorphism of the realization sending `a` to
`c`. It preserves the support of every point, so it fixes every vertex other than possibly `a`
and maps the polyhedron of every subcomplex onto itself; its inverse is the same construction
with `a` and `c` exchanged. It is the identity outside the open star of the open simplex of `a`.

This is the homogeneity of open simplices used to make prescribed points of a triangulated space
into vertices: slide the point to the barycenter of its open simplex, then subdivide.

## Main definitions

* `AbstractSimplicialComplex.shiftHomeomorph a c h`: the support-preserving homeomorphism of the
  realization sliding `a` to `c`, for `a` and `c` with the same support.

## Main results

* `AbstractSimplicialComplex.shiftHomeomorph_apply_self`: it sends `a` to `c`.
* `AbstractSimplicialComplex.support_shiftHomeomorph`: it preserves supports.
* `AbstractSimplicialComplex.shiftHomeomorph_symm`: its inverse is the slide from `c` to `a`.
-/

public section

noncomputable section

open Set TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} {K : AbstractSimplicialComplex ι}

attribute [local instance] Classical.decEq

/-- The support of a realization point is nonempty. -/
private theorem support_nonempty (x : Realization K) : x.1.support.Nonempty :=
  K.isRelLowerSet_faces.prop_of_mem (K.support_mem x)

/-- The largest multiple of `a` lying below `y` on the support of `a`:
`min_{w ∈ supp a} y w / a w`. -/
private def shiftCoeff (a : Realization K) (y : ι →₀ ℝ) : ℝ :=
  a.1.support.inf' (support_nonempty a) fun w => y w / a.1 w

private theorem shiftCoeff_nonneg (a y : Realization K) : 0 ≤ shiftCoeff a y.1 :=
  Finset.le_inf' _ _ fun w _ => div_nonneg (Realization.nonneg K y w) (Realization.nonneg K a w)

private theorem shiftCoeff_mul_le (a : Realization K) (y : ι →₀ ℝ) {w : ι}
    (hw : w ∈ a.1.support) :
    shiftCoeff a y * a.1 w ≤ y w :=
  (le_div_iff₀ (Realization.pos_of_mem_support K a hw)).mp (Finset.inf'_le _ hw)

private theorem exists_shiftCoeff_mul_eq (a : Realization K) (y : ι →₀ ℝ) :
    ∃ w ∈ a.1.support, shiftCoeff a y * a.1 w = y w := by
  obtain ⟨w, hw, heq⟩ := Finset.exists_mem_eq_inf' (support_nonempty a)
    fun w => y w / a.1 w
  refine ⟨w, hw, ?_⟩
  rw [shiftCoeff, heq, div_mul_cancel₀ _ (Realization.pos_of_mem_support K a hw).ne']

/-- If the coefficient is positive, the support of `a` lies in the support of `y`. -/
private theorem support_subset_of_shiftCoeff_pos (a : Realization K) {y : ι →₀ ℝ}
    (h : 0 < shiftCoeff a y) : a.1.support ⊆ y.support := fun _ hw =>
  Finsupp.mem_support_iff.mpr (lt_of_lt_of_le
    (mul_pos h (Realization.pos_of_mem_support K a hw)) (shiftCoeff_mul_le a y hw)).ne'

variable (a c : Realization K) (h : a.1.support = c.1.support)

/-- The barycentric coordinates of the slide of `y` from `a` to `c`. -/
private def shiftVal (y : ι →₀ ℝ) : ι →₀ ℝ :=
  y + shiftCoeff a y • (c.1 - a.1)

private theorem shiftVal_apply (y : ι →₀ ℝ) (w : ι) :
    shiftVal a c y w = y w + shiftCoeff a y * (c.1 w - a.1 w) := by
  simp [shiftVal]

include h in
private theorem shiftVal_nonneg (y : Realization K) (w : ι) : 0 ≤ shiftVal a c y.1 w := by
  rw [shiftVal_apply]
  by_cases hw : w ∈ a.1.support
  · nlinarith [shiftCoeff_mul_le a y.1 hw, shiftCoeff_nonneg a y, Realization.nonneg K c w]
  · have hc : w ∉ c.1.support := h ▸ hw
    rw [Finsupp.notMem_support_iff.mp hw, Finsupp.notMem_support_iff.mp hc]
    simpa using Realization.nonneg K y w

include h in
private theorem support_shiftVal_subset (y : Realization K) :
    (shiftVal a c y.1).support ⊆ y.1.support := by
  intro w hw
  rw [Finsupp.mem_support_iff, shiftVal_apply] at hw
  by_cases hwa : w ∈ a.1.support
  · rcases (shiftCoeff_nonneg a y).eq_or_lt with h0 | h0
    · rw [← h0] at hw
      simpa using hw
    · exact support_subset_of_shiftCoeff_pos a h0 hwa
  · have hc : w ∉ c.1.support := h ▸ hwa
    rw [Finsupp.notMem_support_iff.mp hwa, Finsupp.notMem_support_iff.mp hc] at hw
    simpa using hw

private theorem shiftVal_sum (y : Realization K) : (shiftVal a c y.1).sum (fun _ r => r) = 1 := by
  have hlin (x : ι →₀ ℝ) :
      x.sum (fun _ r => r) = Finsupp.lsum ℝ (fun _ : ι => (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) x := by
    rw [Finsupp.lsum_apply]
    rfl
  rw [hlin, shiftVal, map_add, map_smul, map_sub, ← hlin, ← hlin, ← hlin,
    Realization.sum_eq_one, Realization.sum_eq_one, Realization.sum_eq_one]
  simp

include h in
private theorem shiftVal_mem_standardSimplex (y : Realization K) {τ : Finset ι}
    (hτ : y.1.support ⊆ τ) :
    shiftVal a c y.1 ∈ convexHull ℝ (τ.image (fun v => Finsupp.single v (1 : ℝ)) :
      Set (ι →₀ ℝ)) := by
  rw [Finset.coe_image, mem_standardSimplex_iff]
  exact ⟨shiftVal_nonneg a c h y, shiftVal_sum a c y,
    (support_shiftVal_subset a c h y).trans hτ⟩

include h in
/-- The slide from `a` to `c`, as a map of the realization. -/
private def shift (y : Realization K) : Realization K :=
  ⟨shiftVal a c y.1, mem_realization_iff.mpr
    ⟨y.1.support, K.support_mem y, shiftVal_mem_standardSimplex a c h y subset_rfl⟩⟩

@[simp]
private theorem shift_val (y : Realization K) : (shift a c h y).1 = shiftVal a c y.1 :=
  (rfl)

private theorem support_shift_subset (y : Realization K) :
    (shift a c h y).1.support ⊆ y.1.support :=
  support_shiftVal_subset a c h y

/-- The slide does not change the coefficient: the coefficient of the slide of `y` with
respect to `c` is the coefficient of `y` with respect to `a`. -/
private theorem shiftCoeff_shift (y : Realization K) :
    shiftCoeff c (shift a c h y).1 = shiftCoeff a y.1 := by
  apply le_antisymm
  · obtain ⟨w, hw, heq⟩ := exists_shiftCoeff_mul_eq a y.1
    have hwc : w ∈ c.1.support := h ▸ hw
    refine (Finset.inf'_le _ hwc).trans_eq ?_
    rw [shift_val, shiftVal_apply, ← heq,
      div_eq_iff (Realization.pos_of_mem_support K c hwc).ne']
    ring
  · refine Finset.le_inf' _ _ fun w hwc => ?_
    have hw : w ∈ a.1.support := h ▸ hwc
    rw [le_div_iff₀ (Realization.pos_of_mem_support K c hwc), shift_val, shiftVal_apply]
    nlinarith [shiftCoeff_mul_le a y.1 hw]

private theorem shift_shift (y : Realization K) : shift c a h.symm (shift a c h y) = y := by
  apply Subtype.ext
  ext w
  rw [shift_val, shiftVal_apply, shiftCoeff_shift, shift_val, shiftVal_apply]
  ring

private theorem continuous_shift : Continuous (shift a c h) := by
  refine continuous_iff_faceInclusion.mpr fun τ => ?_
  let s : StandardSimplex τ.1 → StandardSimplex τ.1 := fun x =>
    ⟨shiftVal a c (faceInclusion K τ x).1, shiftVal_mem_standardSimplex a c h _
      (by rw [faceInclusion_val]; exact StandardSimplex.support_subset x)⟩
  have hs : Continuous s := by
    refine continuous_induced_rng.2 (continuous_pi fun w => ?_)
    have hcoord (v : ι) : Continuous fun x : StandardSimplex τ.1 => x.1 v :=
      (continuous_apply v).comp continuous_induced_dom
    have hcoeff : Continuous fun x : StandardSimplex τ.1 => shiftCoeff a x.1 :=
      Continuous.finset_inf'_apply (f := fun v (x : StandardSimplex τ.1) => x.1 v / a.1 v)
        (support_nonempty a) fun v _ => (hcoord v).div_const _
    simp only [s, Function.comp_apply, faceInclusion_val, shiftVal_apply]
    exact (hcoord w).add (hcoeff.mul continuous_const)
  refine ((continuous_faceInclusion K τ).comp hs).congr fun x => ?_
  apply Subtype.ext
  simp [s, faceInclusion_val]

/-- The support-preserving homeomorphism of the realization sliding `a` to `c` within their
common open simplex. -/
def shiftHomeomorph : Realization K ≃ₜ Realization K where
  toFun := shift a c h
  invFun := shift c a h.symm
  left_inv := shift_shift a c h
  right_inv := shift_shift c a h.symm
  continuous_toFun := continuous_shift a c h
  continuous_invFun := continuous_shift c a h.symm

/-- The inverse of the slide from `a` to `c` is the slide from `c` to `a`. -/
theorem shiftHomeomorph_symm : (shiftHomeomorph a c h).symm = shiftHomeomorph c a h.symm :=
  (rfl)

/-- The slide sends `a` to `c`. -/
@[simp]
theorem shiftHomeomorph_apply_self : shiftHomeomorph a c h a = c := by
  have h1 : shiftCoeff a a.1 = 1 := by
    obtain ⟨w, hw, heq⟩ := exists_shiftCoeff_mul_eq a a.1
    exact (mul_eq_right₀ (Realization.pos_of_mem_support K a hw).ne').mp heq
  apply Subtype.ext
  change shiftVal a c a.1 = c.1
  rw [shiftVal, h1, one_smul, add_sub_cancel]

/-- The slide preserves the support of every point. -/
@[simp]
theorem support_shiftHomeomorph (y : Realization K) :
    (shiftHomeomorph a c h y).1.support = y.1.support := by
  change (shift a c h y).1.support = y.1.support
  refine (support_shift_subset a c h y).antisymm ?_
  conv_lhs => rw [← shift_shift a c h y]
  exact support_shift_subset c a h.symm _

end AbstractSimplicialComplex
