/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BoundedCechCochains
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Geometry.Manifold.Complex.DolbeaultGluing
import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Bounded holomorphic cocycles lift to larger covers up to a coboundary

Let `X` be a compact Riemann surface with three finite families of open sets `V ⋐ U ⋐ U'`, the
`V i` covering `X` and each `U' i` a disc in the chart at a point `x i`. Every bounded
holomorphic Čech `1`-cocycle on the `V i` is the restriction of a bounded holomorphic cocycle on
the `U i` plus the coboundary of a bounded holomorphic `0`-cochain on the `V i`
(`TauCeti.BoundedCech.exists_restrictCocycles_add_d₀Cocycles_eq`).

This is Forster's Lemma 14.7 with the boundedness needed in 14.9. The unbounded statement is
`TauCeti.exists_mdifferentiableOn_cocycle_eq_add_sub_of_chart_ball` on the discs `U' i`; the
cocycle it produces is bounded on `U i` because `closure (U i)` is a compact subset of `U' i`,
and the `0`-cochain is bounded on `V i` because `ξ` is bounded. Together with
`TauCeti.BoundedCech.exists_finiteDimensional_isCompl_range_d₀Cocycles` this shows that the
bounded holomorphic coboundaries on `V` have a finite-dimensional complement in the bounded
holomorphic cocycles
(`TauCeti.BoundedCech.exists_finiteDimensional_isCompl_range_d₀Cocycles_of_chart_ball`). Such
covers exist: a compact Riemann surface is covered by finitely many chart discs of radii
`4⁻¹ * R`, inside the concentric discs of radii `2⁻¹ * R` and `R`
(`TauCeti.BoundedCech.exists_chart_ball_cover_finiteDimensional_isCompl_range_d₀Cocycles`).

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer,
  1981, §14 (14.7–14.9).
-/

public section

open scoped Manifold

namespace TauCeti.BoundedCech

open Set Metric TopologicalSpace BoundedContinuousFunction BoundedHolomorphicSections

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [T2Space X] [CompactSpace X] {ι : Type*} [Finite ι] {x : ι → X} {R : ι → ℝ}
  {U' : ι → Set X} {U V : ι → Opens X}

/-- **Bounded holomorphic cocycles lift to larger covers up to a coboundary** (Forster 14.7). On
a compact Riemann surface, let `U' i` be the disc of radius `R i` about `x i` in the chart at
`x i` (lying in the chart target), and `V i`, `U i` open with `closure (V i) ⊆ U i`,
`closure (U i) ⊆ U' i` and the `V i` covering `X`. Every bounded holomorphic cocycle on the
`V i` is the restriction of one on the `U i` plus a bounded holomorphic coboundary. -/
theorem exists_restrictCocycles_add_d₀Cocycles_eq
    (hR : ∀ i, ball (extChartAt 𝓘(ℂ) (x i) (x i)) (R i) ⊆ (extChartAt 𝓘(ℂ) (x i)).target)
    (hU' : ∀ i, U' i = (extChartAt 𝓘(ℂ) (x i)).source ∩
      extChartAt 𝓘(ℂ) (x i) ⁻¹' ball (extChartAt 𝓘(ℂ) (x i) (x i)) (R i))
    (hUU' : ∀ i, closure (U i : Set X) ⊆ U' i) (hVU : ∀ i, closure (V i : Set X) ⊆ U i)
    (hVcov : ⋃ i, (V i : Set X) = univ) (ξ : cocycles 𝓘(ℂ) V) :
    ∃ ζ : cocycles 𝓘(ℂ) U, ∃ η : cochains₀ 𝓘(ℂ) V,
      restrictCocycles (fun i => SetLike.coe_subset_coe.mp (subset_closure.trans (hVU i))) ζ +
        d₀Cocycles 𝓘(ℂ) V η = ξ := by
  have := Fintype.ofFinite ι
  have hUU'' (i : ι) : (U i : Set X) ⊆ U' i := subset_closure.trans (hUU' i)
  have hVU' (i : ι) : (V i : Set X) ⊆ U' i := (subset_closure.trans (hVU i)).trans (hUU'' i)
  -- The zero extensions of the components of `ξ`.
  have hξ := mem_cochains₁_iff.1 (mem_cocycles_iff.1 ξ.2).1
  set ξ' : ι → ι → X → ℂ := fun i j => extend ⟨(ξ : BoundedCochain₁ V) i j, hξ i j⟩
  have hξ'_apply (i j : ι) (z : ↥(V i ⊓ V j)) : ξ' i j z = (ξ : BoundedCochain₁ V) i j z :=
    extend_apply _ z
  have hcocycle (i j k : ι) (y : X) (hy : y ∈ (V i : Set X) ∩ V j ∩ V k) :
      ξ' i j y + ξ' j k y = ξ' i k y := by
    have h := congr($((mem_cocycles_iff.1 ξ.2).2) i j k ⟨y, hy⟩)
    simp only [d₁_apply, FunLike.coe_add, FunLike.coe_sub, Pi.add_apply, Pi.sub_apply,
      restrictBCF_apply, Pi.zero_apply, FunLike.coe_zero] at h
    rw [hξ'_apply i j ⟨y, hy.1⟩, hξ'_apply j k ⟨y, hy.1.2, hy.2⟩,
      hξ'_apply i k ⟨y, hy.1.1, hy.2⟩]
    linear_combination h
  have hbound (i k : ι) (y : X) (hy : y ∈ (V k : Set X) ∩ V i) :
      ‖ξ' k i y‖ ≤ ‖(ξ : BoundedCochain₁ V)‖ := by
    rw [hξ'_apply k i ⟨y, hy⟩]
    exact (((ξ : BoundedCochain₁ V) k i).norm_coe_le_norm _).trans
      ((norm_le_pi_norm ((ξ : BoundedCochain₁ V) k) i).trans (norm_le_pi_norm _ k))
  obtain ⟨ζ', η', hζ', hζcoc, hη', heq, hηb⟩ :=
    TauCeti.exists_mdifferentiableOn_cocycle_eq_add_sub_of_chart_ball hR hU'
      (fun i => (V i).isOpen) hVU' hVcov (fun i j => mdifferentiableOn_extend _) hcocycle
  -- `ζ'` is bounded on `U i ∩ U j`, whose closure is a compact subset of `U' i ∩ U' j`.
  have hUc (i j : ι) : closure ((U i : Set X) ∩ U j) ⊆ U' i ∩ U' j :=
    (closure_inter_subset_inter_closure _ _).trans (inter_subset_inter (hUU' i) (hUU' j))
  choose Cζ hCζ using fun i j =>
    (hζ' i j).exists_forall_norm_le_of_isCompact_closure isClosed_closure.isCompact (hUc i j)
  choose Cη hCη using fun i => hηb i _ (hbound i) isClosed_closure.isCompact
    ((hVU i).trans (hUU'' i))
  refine ⟨⟨fun i j => (of (U i ⊓ U j) (ζ' i j)
    ((hζ' i j).mono fun _ hy => ⟨hUU'' i hy.1, hUU'' j hy.2⟩) (Cζ i j) (hCζ i j) :
      ↥(U i ⊓ U j) →ᵇ ℂ), mem_cocycles_iff.2 ⟨mem_cochains₁_iff.2 fun i j => (of _ _ _ _ _).2,
    funext fun i => funext fun j => funext fun k => BoundedContinuousFunction.ext fun z => ?_⟩⟩,
    ⟨fun i => (of (V i) (-η' i) (hη' i).neg (Cη i)
      (fun y hy => (norm_neg (η' i y)).trans_le (hCη i y hy)) : ↥(V i) →ᵇ ℂ),
      mem_cochains₀_iff.2 fun i => (of _ _ _ _ _).2⟩,
    Subtype.ext <| funext fun i => funext fun j => BoundedContinuousFunction.ext fun z => ?_⟩
  · have hz := hζcoc i j k z ⟨⟨hUU'' i z.2.1.1, hUU'' j z.2.1.2⟩, hUU'' k z.2.2⟩
    simp only [d₁_apply, FunLike.coe_add, FunLike.coe_sub, Pi.add_apply, Pi.sub_apply,
      restrictBCF_apply, of_apply, Pi.zero_apply, FunLike.coe_zero]
    linear_combination hz
  · have hz := heq i j z z.2
    simp only [Submodule.coe_add, Pi.add_apply, coe_restrictCocycles_apply, restrict₁_apply,
      restrictBCF_apply, coe_d₀Cocycles_apply, d₀_apply, FunLike.coe_add, FunLike.coe_sub,
      Pi.sub_apply, Pi.neg_apply, of_apply]
    rw [← hξ'_apply i j z]
    linear_combination hz

/-- **Finiteness of bounded holomorphic `H¹` on a compact Riemann surface** (Forster 14.9, with
supremum norms). For `V ⋐ U ⋐ U'` as in
`TauCeti.BoundedCech.exists_restrictCocycles_add_d₀Cocycles_eq`, the bounded holomorphic
coboundaries on `V` have a finite-dimensional complement in the bounded holomorphic cocycles. -/
theorem exists_finiteDimensional_isCompl_range_d₀Cocycles_of_chart_ball
    (hR : ∀ i, ball (extChartAt 𝓘(ℂ) (x i) (x i)) (R i) ⊆ (extChartAt 𝓘(ℂ) (x i)).target)
    (hU' : ∀ i, U' i = (extChartAt 𝓘(ℂ) (x i)).source ∩
      extChartAt 𝓘(ℂ) (x i) ⁻¹' ball (extChartAt 𝓘(ℂ) (x i) (x i)) (R i))
    (hUU' : ∀ i, closure (U i : Set X) ⊆ U' i) (hVU : ∀ i, closure (V i : Set X) ⊆ U i)
    (hVcov : ⋃ i, (V i : Set X) = univ) :
    ∃ B : Submodule ℂ (cocycles 𝓘(ℂ) V), FiniteDimensional ℂ B ∧
      IsCompl (LinearMap.range (d₀Cocycles 𝓘(ℂ) V : cochains₀ 𝓘(ℂ) V →ₗ[ℂ] cocycles 𝓘(ℂ) V))
        B :=
  exists_finiteDimensional_isCompl_range_d₀Cocycles (fun _ => isClosed_closure.isCompact) hVU
    (exists_restrictCocycles_add_d₀Cocycles_eq hR hU' hUU' hVU hVcov)

/-- **A compact Riemann surface has a finite chart-disc cover with finite bounded `H¹`.** There
are finitely many points `y ∈ t` and radii `R y > 0`, the coordinate disc of radius `R y` lying in
the chart target at `y`, such that the chart discs `V y` of radii `4⁻¹ * R y` cover `X` and the
bounded holomorphic coboundaries on `V` have a finite-dimensional complement in the bounded
holomorphic cocycles. -/
theorem exists_chart_ball_cover_finiteDimensional_isCompl_range_d₀Cocycles :
    ∃ t : Finset X, ∃ R : X → ℝ, (∀ y, 0 < R y) ∧
      (∀ y, ball (extChartAt 𝓘(ℂ) y y) (R y) ⊆ (extChartAt 𝓘(ℂ) y).target) ∧
      ∃ V : t → Opens X, (∀ i, (V i : Set X) = (extChartAt 𝓘(ℂ) i.1).source ∩
        extChartAt 𝓘(ℂ) i.1 ⁻¹' ball (extChartAt 𝓘(ℂ) i.1 i.1) (4⁻¹ * R i)) ∧
      ⋃ i, (V i : Set X) = univ ∧
      ∃ B : Submodule ℂ (cocycles 𝓘(ℂ) V), FiniteDimensional ℂ B ∧
        IsCompl (LinearMap.range (d₀Cocycles 𝓘(ℂ) V : cochains₀ 𝓘(ℂ) V →ₗ[ℂ] cocycles 𝓘(ℂ) V))
          B := by
  obtain ⟨t, R, hR, hRt, hcov⟩ :=
    exists_finset_iUnion_extChartAt_preimage_ball_eq_univ (I := 𝓘(ℂ)) (M := X)
      (by norm_num : (0 : ℝ) < 4⁻¹)
  -- The chart disc of radius `r` about `y`.
  let disc (y : X) (r : ℝ) : Opens X :=
    ⟨(extChartAt 𝓘(ℂ) y).source ∩ extChartAt 𝓘(ℂ) y ⁻¹' ball (extChartAt 𝓘(ℂ) y y) r,
      isOpen_extChartAt_preimage' y isOpen_ball⟩
  have hcov' : ⋃ i : t, (disc i.1 (4⁻¹ * R i) : Set X) = univ :=
    eq_univ_of_forall fun y => by
      obtain ⟨z, hz, hy⟩ := mem_iUnion₂.1 (hcov.ge (mem_univ y))
      exact mem_iUnion.2 ⟨⟨z, hz⟩, hy⟩
  refine ⟨t, R, hR, hRt, fun i => disc i.1 (4⁻¹ * R i), fun _ => rfl, hcov',
    exists_finiteDimensional_isCompl_range_d₀Cocycles_of_chart_ball (x := Subtype.val)
      (R := fun i => R i) (U' := fun i => disc i.1 (R i)) (U := fun i => disc i.1 (2⁻¹ * R i))
      (fun i => hRt i) (fun _ => rfl) (fun i => ?_) (fun i => ?_) hcov'⟩
  · exact closure_extChartAt_source_inter_preimage_ball_subset _ (by linarith [hR i]) (hRt i)
  · exact closure_extChartAt_source_inter_preimage_ball_subset _ (by linarith [hR i])
      ((ball_subset_ball (by linarith [hR i])).trans (hRt i))

end TauCeti.BoundedCech
