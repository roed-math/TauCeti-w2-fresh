/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Compact
public import Mathlib.Topology.LocalAtTarget

/-!
# Locally finite polyhedra

When every vertex has finite closed star, a weak geometric realization is locally compact
and its topology agrees with the topology of its barycentric coordinates. The open stars
are the coordinate-positive neighbourhoods; each lies in a compact closed star. This permits
local models of combinatorial manifolds to be treated as coordinate subspaces without a
global finiteness assumption on the triangulation.

The sphere-or-ball link condition implies finiteness of every vertex star. Consequently
realizations of combinatorial manifolds satisfy both conclusions.

Conversely, a locally compact weak realization has finite vertex stars
(`finite_closedStar_faces_of_weaklyLocallyCompactSpace`): every neighbourhood of a vertex meets
the open simplex of each face containing it, while a compact neighbourhood meets only finitely
many open simplices. This applies to every space triangulated by `K`, such as a manifold, through
the triangulating homeomorphism.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2--3 (locally finite polyhedra and vertex stars).
* A. Hatcher, *Algebraic Topology*, Appendix A, Propositions A.1 and A.2 (compact subsets and
  local compactness of CW complexes).
-/

public section

noncomputable section

open Set Filter Topology TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] (K : AbstractSimplicialComplex ι)

/-- Finite vertex stars provide a compact neighbourhood around every realization point. -/
theorem locallyCompactSpace_realization_of_finite_vertex_stars
    (hfin : ∀ v : ι,
      (PreAbstractSimplicialComplex.closedStar K.toPreAbstractSimplicialComplex {v}).faces.Finite) :
    LocallyCompactSpace (Realization K) := by
  have : WeaklyLocallyCompactSpace (Realization K) := ⟨fun x => by
    obtain ⟨v, hv⟩ := K.exists_mem_openStarRealization x
    exact ⟨K.closedStarRealization {v}, K.isCompact_closedStarRealization (hfin v),
      mem_of_superset ((K.isOpen_openStarRealization v).mem_nhds hv)
        (K.openStarRealization_subset_closedStarRealization v)⟩⟩
  infer_instance

/-- With finite vertex stars, the weak topology is exactly the topology induced by
barycentric coordinates. No global finiteness assumption is needed. -/
theorem isEmbedding_realization_coe_of_finite_vertex_stars
    (hfin : ∀ v : ι,
      (PreAbstractSimplicialComplex.closedStar K.toPreAbstractSimplicialComplex {v}).faces.Finite) :
    Topology.IsEmbedding (fun x : Realization K => (x.1 : ι → ℝ)) := by
  -- Factor coordinates through their range and use its open-star cover.
  -- Check each restriction via the embedding of the compact closed star.
  let c : Realization K → (ι → ℝ) := fun x => x.1
  let U : ι → TopologicalSpace.Opens (range c) := fun v =>
    ⟨{y | 0 < y.1 v}, isOpen_lt continuous_const
      ((continuous_apply v).comp continuous_subtype_val)⟩
  have hpreimage (v : ι) : (rangeFactorization c) ⁻¹' (U v) = K.openStarRealization v := by
    ext x
    simp only [U, TopologicalSpace.Opens.coe_mk, mem_preimage, mem_ofPred_eq,
      mem_openStarRealization, rangeFactorization, c]
  have hcover : TopologicalSpace.IsOpenCover U := by
    refine TopologicalSpace.IsOpenCover.of_sets (fun v => (U v).isOpen) ?_
    apply Set.eq_univ_of_forall
    rintro ⟨_, x, rfl⟩
    obtain ⟨v, hv⟩ := K.exists_mem_openStarRealization x
    have hx : x ∈ (rangeFactorization c) ⁻¹' (U v) := by
      rw [hpreimage v]
      exact hv
    exact mem_iUnion.mpr ⟨v, hx⟩
  have hc : Continuous (rangeFactorization c) := (continuous_realization_coe K).rangeFactorization
  have he : Topology.IsEmbedding (rangeFactorization c) := by
    apply (hcover.isEmbedding_iff_restrictPreimage hc).mpr
    intro v
    let C := K.closedStarRealization {v}
    have hC : Topology.IsEmbedding (fun x : C => c x.1) :=
      (K.isClosedEmbedding_realization_coe_restrict
        (K.isCompact_closedStarRealization (hfin v))).isEmbedding
    have hsub : (rangeFactorization c) ⁻¹' (U v) ⊆ C := by
      rw [hpreimage v]
      exact K.openStarRealization_subset_closedStarRealization v
    have hi := hC.comp (Topology.IsEmbedding.inclusion hsub)
    -- Both sides evaluate to the coordinates of the same realization point:
    -- rangeFactorization, restrictPreimage, and inclusion only add subtype proofs.
    have hcomp : (Subtype.val ∘ Subtype.val) ∘ (U v).1.restrictPreimage (rangeFactorization c) =
        (fun x : C => c x.1) ∘ inclusion hsub := funext fun x => rfl
    rw [← hcomp] at hi
    exact (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal).of_comp_iff.mp hi
  exact Topology.IsEmbedding.subtypeVal.comp he

/-- The realization of a combinatorial manifold is locally compact. -/
theorem locallyCompactSpace_realization_of_isCombinatorialManifold {n : ℕ}
    (hK : PreAbstractSimplicialComplex.IsCombinatorialManifold K.toPreAbstractSimplicialComplex n) :
    LocallyCompactSpace (Realization K) :=
  K.locallyCompactSpace_realization_of_finite_vertex_stars fun v =>
    hK.finite_faces_closedStar v

/-- The weak realization of a combinatorial manifold embeds in its barycentric-coordinate
space. -/
theorem isEmbedding_realization_coe_of_isCombinatorialManifold {n : ℕ}
    (hK : PreAbstractSimplicialComplex.IsCombinatorialManifold K.toPreAbstractSimplicialComplex n) :
    Topology.IsEmbedding (fun x : Realization K => (x.1 : ι → ℝ)) :=
  K.isEmbedding_realization_coe_of_finite_vertex_stars fun v =>
    hK.finite_faces_closedStar v

omit [DecidableEq ι] in
/-- Every neighbourhood of a vertex `v` contains a point whose support is any prescribed face
containing `v`: the segment from `v` to the barycenter of the face leaves `v` through the open
simplex of the face. -/
theorem exists_mem_support_eq_of_mem_nhds_vertex {N : Set (Realization K)} {v : ι}
    (hN : N ∈ 𝓝 (vertex K v)) (σ : Face K) (hv : v ∈ σ.1) :
    ∃ x ∈ N, x.1.support = σ.1 := by
  classical
  let e : ι →₀ ℝ := Finsupp.single v 1
  let b : ι →₀ ℝ := faceBarycenter K σ
  have he :
      e ∈ convexHull ℝ (σ.1.image (fun w => Finsupp.single w (1 : ℝ)) : Set (ι →₀ ℝ)) :=
    subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hv))
  have hmem (t : unitInterval) : (1 - (t : ℝ)) • e + (t : ℝ) • b ∈
      convexHull ℝ (σ.1.image (fun w => Finsupp.single w (1 : ℝ)) : Set (ι →₀ ℝ)) :=
    convex_convexHull ℝ _ he (faceBarycenter_mem K σ) (sub_nonneg.mpr t.2.2) t.2.1
      (sub_add_cancel 1 _)
  let g : unitInterval → StandardSimplex σ.1 := fun t => ⟨_, hmem t⟩
  have hg : Continuous g := by
    refine continuous_induced_rng.2 (continuous_pi fun w => ?_)
    simp only [g, Function.comp_apply, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    fun_prop
  let G : ℝ → Realization K := fun t => faceInclusion K σ (g (projIcc 0 1 zero_le_one t))
  have hG : Continuous G := (continuous_faceInclusion K σ).comp (hg.comp continuous_projIcc)
  have hG0 : G 0 = vertex K v := by
    apply Subtype.ext
    simp [G, g, e, vertex_val]
  have hN0 : ∀ᶠ t in 𝓝 (0 : ℝ), G t ∈ N := hG.continuousAt.preimage_mem_nhds (hG0 ▸ hN)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), G t ∈ N ∧ t ∈ Ioo (0 : ℝ) 1 :=
    (hN0.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT zero_lt_one)
  obtain ⟨t, htN, ht0, ht1⟩ := hev.exists
  refine ⟨G t, htN, ?_⟩
  have hproj : (projIcc 0 1 zero_le_one t : ℝ) = t := by
    rw [projIcc_of_mem _ ⟨ht0.le, ht1.le⟩]
  ext w
  simp only [G, g, faceInclusion_val, Finsupp.mem_support_iff, Finsupp.coe_add,
    Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hproj, e, b,
    faceBarycenter_apply, Finsupp.single_apply]
  by_cases hw : w ∈ σ.1
  · have hc : (0 : ℝ) < (σ.1.card : ℝ)⁻¹ := by
      have := Finset.card_pos.mpr ⟨w, hw⟩
      positivity
    simp only [hw, ite_true, iff_true]
    split_ifs <;> nlinarith
  · have hvw : v ≠ w := fun h => hw (h ▸ hv)
    simp [hw, hvw]

/-- A vertex with a compact neighbourhood has a finite closed star. -/
theorem finite_closedStar_faces_of_isCompact {N : Set (Realization K)} {v : ι}
    (hN : N ∈ 𝓝 (vertex K v)) (hc : IsCompact N) :
    (PreAbstractSimplicialComplex.closedStar K.toPreAbstractSimplicialComplex {v}).faces.Finite :=
  by
  refine ((finite_image_support_of_isCompact hc).biUnion
    fun σ _ => (σ.powerset : Set (Finset ι)).toFinite).subset ?_
  intro ρ hρ
  have hρ' := PreAbstractSimplicialComplex.mem_closedStar_nonempty.mp hρ
  obtain ⟨x, hxN, hx⟩ := K.exists_mem_support_eq_of_mem_nhds_vertex hN ⟨ρ ∪ {v}, hρ'.2⟩
    (Finset.mem_union_right _ (Finset.mem_singleton_self v))
  exact mem_biUnion ⟨x, hxN, rfl⟩
    (Finset.mem_coe.mpr (Finset.mem_powerset.mpr (by
      change ρ ⊆ x.1.support
      rw [hx]
      exact Finset.subset_union_left)))

/-- A locally compact weak realization is locally finite: every vertex has a finite closed
star. -/
theorem finite_closedStar_faces_of_weaklyLocallyCompactSpace
    [WeaklyLocallyCompactSpace (Realization K)] (v : ι) :
    (PreAbstractSimplicialComplex.closedStar K.toPreAbstractSimplicialComplex {v}).faces.Finite :=
  have ⟨_, hc, hN⟩ := exists_compact_mem_nhds (vertex K v)
  K.finite_closedStar_faces_of_isCompact hN hc

end AbstractSimplicialComplex
