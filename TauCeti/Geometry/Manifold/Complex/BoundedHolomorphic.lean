/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Sets.Opens
public import TauCeti.Analysis.Complex.HolomorphicFunctions.Bounded
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Bounded holomorphic maps on an open subset of a complex manifold

For an open subset `W` of a complex manifold `X` modelled by `I`, and a complex normed space
`F`, `boundedHolomorphicSections I F W` is the space `H^∞(W, F)` of bounded holomorphic maps
`W → F`, as a complex subspace of the bounded continuous maps `W →ᵇ F` with the supremum norm.
For `F = ℂ` these are the bounded sections of the holomorphic structure sheaf over `W`.
Holomorphy can be checked on any ambient representative `X → F`, and every element has its zero
extension `TauCeti.BoundedHolomorphicSections.extend` as a canonical ambient representative.

This is the manifold counterpart of `TauCeti.boundedHolomorphicFunctions`, which treats open
subsets of a complex normed space; on the model space itself the two subspaces coincide
(`TauCeti.boundedHolomorphicSections_modelWithCornersSelf`). For `X` without boundary, both
results below are proved by reading maps in the extended charts of `X`:

* **Completeness.** For complete `F`, `H^∞(W, F)` is closed in `W →ᵇ F` (a uniform limit of
  holomorphic maps is holomorphic), hence a Banach space
  (`TauCeti.isClosed_boundedHolomorphicSections`).
* **Compactness (Montel).** If `W'` lies in a compact subset of `W` and `F` is proper,
  restriction `H^∞(W, F) → H^∞(W', F)` is a compact operator
  (`TauCeti.BoundedHolomorphicSections.isCompactOperator_restrict`): the Cauchy estimate in a
  chart makes the unit ball of `H^∞(W, F)` equicontinuous, and the Arzelà–Ascoli theorem applies.

For `F = ℂ` these are the Banach spaces of Čech cochains in the finiteness proof for the first
cohomology of the structure sheaf of a compact Riemann surface.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer,
  1981, §14 (Montel's theorem 14.2 and the Banach spaces of cochains 14.3–14.6, there with `L²`
  rather than supremum norms).
-/

public section

namespace TauCeti

open Filter Metric Set Topology TopologicalSpace BoundedContinuousFunction
open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The space `H^∞(W, F)` of bounded holomorphic maps on an open set `W` of a complex manifold,
as a subspace of the bounded continuous maps `W →ᵇ F` with the supremum norm. A bounded
continuous map belongs to it when some ambient map `X → F` agreeing with it on `W` is holomorphic
on `W`. -/
def boundedHolomorphicSections (W : Opens X) : Submodule ℂ (W →ᵇ F) where
  carrier := {f | ∃ g : X → F, MDifferentiableOn I 𝓘(ℂ, F) g W ∧ ∀ z : W, g z = f z}
  zero_mem' := ⟨0, mdifferentiableOn_const, fun _ => rfl⟩
  add_mem' := by
    rintro f h ⟨g, hg, hgf⟩ ⟨k, hk, hkh⟩
    exact ⟨g + k, hg.add hk, fun z => by simp [hgf, hkh]⟩
  smul_mem' := by
    rintro c f ⟨g, hg, hgf⟩
    exact ⟨c • g, hg.const_smul c, fun z => by simp [hgf]⟩

variable {I F}

/-- Membership means having an ambient holomorphic representative. -/
theorem mem_boundedHolomorphicSections_iff {W : Opens X} {f : W →ᵇ F} :
    f ∈ boundedHolomorphicSections I F W ↔
      ∃ g : X → F, MDifferentiableOn I 𝓘(ℂ, F) g W ∧ ∀ z : W, g z = f z := Iff.rfl

/-- Holomorphy can be tested on any ambient map agreeing with `f` on `W`. -/
theorem mem_boundedHolomorphicSections_iff_of_eqOn {W : Opens X} {f : W →ᵇ F} {g : X → F}
    (hgf : ∀ z : W, g z = f z) :
    f ∈ boundedHolomorphicSections I F W ↔ MDifferentiableOn I 𝓘(ℂ, F) g W := by
  constructor
  · rintro ⟨k, hk, hkf⟩
    exact hk.congr fun z hz => (hgf ⟨z, hz⟩).trans (hkf ⟨z, hz⟩).symm
  · exact fun hg => ⟨g, hg, hgf⟩

/-- Equivalently, the extension by zero is holomorphic on `W`. -/
theorem mem_boundedHolomorphicSections_iff_extend {W : Opens X} {f : W →ᵇ F} :
    f ∈ boundedHolomorphicSections I F W ↔
      MDifferentiableOn I 𝓘(ℂ, F) (Function.extend Subtype.val f (fun _ => 0)) W :=
  mem_boundedHolomorphicSections_iff_of_eqOn fun z =>
    Subtype.val_injective.extend_apply f (fun _ => 0) z

/-- The open subset of the extended chart at `x` that the inverse chart maps into `W`. -/
theorem isOpen_extChartAt_target_inter_preimage_symm [I.Boundaryless] (W : Opens X) (x : X) :
    IsOpen ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' W) :=
  (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x) W.isOpen

/-- On an open subset of a complex normed space, viewed as a manifold over itself, the bounded
holomorphic maps are those of `TauCeti.boundedHolomorphicFunctions`. -/
theorem boundedHolomorphicSections_modelWithCornersSelf (U : Opens E) :
    boundedHolomorphicSections 𝓘(ℂ, E) F U = boundedHolomorphicFunctions F U :=
  Submodule.ext fun _ => by
    rw [mem_boundedHolomorphicSections_iff, mem_boundedHolomorphicFunctions_iff]
    exact exists_congr fun _ => and_congr_left' mdifferentiableOn_iff_differentiableOn

section Chart

variable [IsManifold I 1 X] {W : Opens X} {g : X → F}

/-- A map holomorphic on `W`, read in the extended chart at `x`, is holomorphic on the part
of the chart that the inverse chart maps into `W`. -/
theorem MDifferentiableOn.differentiableOn_comp_extChartAt_symm
    (hg : MDifferentiableOn I 𝓘(ℂ, F) g W) (x : X) :
    DifferentiableOn ℂ (g ∘ (extChartAt I x).symm)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' W) :=
  (hg.comp ((mdifferentiableOn_extChartAt_symm (I := I) (x := x)).mono inter_subset_left)
    fun _ hy => hy.2).differentiableOn

/-- A map on `X` is holomorphic at `x` if it is complex differentiable, read in the extended
chart at `x`, at the image of `x`. -/
theorem mdifferentiableAt_of_differentiableAt_comp_extChartAt_symm {x : X}
    (h : DifferentiableAt ℂ (g ∘ (extChartAt I x).symm) (extChartAt I x x)) :
    MDifferentiableAt I 𝓘(ℂ, F) g x := by
  refine (h.mdifferentiableAt.comp x (mdifferentiableAt_extChartAt (mem_chart_source H x)))
    |>.congr_of_eventuallyEq ?_
  filter_upwards [chart_source_mem_nhds H x] with y hy
  simp [(chartAt H x).left_inv hy]

end Chart

section Complete

variable [IsManifold I 1 X] [I.Boundaryless] [CompleteSpace F]

/-- For complete `F`, the bounded holomorphic maps form a closed subspace of the bounded
continuous maps: a uniform limit of holomorphic maps is holomorphic. -/
theorem isClosed_boundedHolomorphicSections (W : Opens X) :
    IsClosed (boundedHolomorphicSections I F W : Set (W →ᵇ F)) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  obtain ⟨S, hS, hSf⟩ := mem_closure_iff_seq_limit.mp hf
  choose G hG hGF using hS
  have hext : ∀ z : W, Function.extend Subtype.val f (fun _ => 0) z = f z :=
    Subtype.val_injective.extend_apply f (fun _ => 0)
  refine mem_boundedHolomorphicSections_iff_extend.mpr fun x hx =>
    (mdifferentiableAt_of_differentiableAt_comp_extChartAt_symm ?_).mdifferentiableWithinAt
  -- Read the sequence in the chart at `x`: there it converges uniformly on an open set of the
  -- model space, so the limit is holomorphic there.
  set φ := extChartAt I x
  have hO := isOpen_extChartAt_target_inter_preimage_symm (I := I) W x
  have hxO : φ x ∈ φ.target ∩ φ.symm ⁻¹' W :=
    ⟨mem_extChartAt_target x, by simpa [φ, extChartAt_to_inv] using hx⟩
  refine (TendstoUniformlyOn.differentiableOn (l := atTop) ?_
    (Eventually.of_forall fun n =>
      MDifferentiableOn.differentiableOn_comp_extChartAt_symm (hG n) x) hO
    |>.differentiableAt (hO.mem_nhds hxO))
  have hT := Metric.tendstoUniformly_iff.mp (tendsto_iff_tendstoUniformly.mp hSf)
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => (hT ε hε).mono fun n hn y hy => ?_
  simp only [Function.comp_apply]
  rw [hext ⟨_, hy.2⟩, hGF n ⟨_, hy.2⟩]
  exact hn _

/-- For complete `F`, the bounded holomorphic maps form a Banach space. -/
instance (W : Opens X) : CompleteSpace (boundedHolomorphicSections I F W) :=
  (isClosed_boundedHolomorphicSections W).completeSpace_coe

end Complete

namespace BoundedHolomorphicSections

variable {W W' W'' : Opens X}

/-- Bounded holomorphic maps are determined by their values. -/
@[ext]
theorem ext {f g : boundedHolomorphicSections I F W} (h : ∀ z, (f : W →ᵇ F) z = (g : W →ᵇ F) z) :
    f = g :=
  Subtype.ext (BoundedContinuousFunction.ext h)

/-- Restrict an ambient map, holomorphic on `W` and bounded there by `C`, to an element of
`H^∞(W, F)`. -/
noncomputable def of (W : Opens X) (g : X → F) (hg : MDifferentiableOn I 𝓘(ℂ, F) g W) (C : ℝ)
    (hC : ∀ z ∈ W, ‖g z‖ ≤ C) : boundedHolomorphicSections I F W :=
  ⟨.ofNormedAddCommGroup (fun z : W => g z) hg.continuousOn.domRestrict C fun z => hC z z.2,
    g, hg, fun _ => rfl⟩

@[simp]
theorem of_apply (g : X → F) (hg : MDifferentiableOn I 𝓘(ℂ, F) g W) (C : ℝ)
    (hC : ∀ z ∈ W, ‖g z‖ ≤ C) (z : W) : (of W g hg C hC : W →ᵇ F) z = g z := (rfl)

/-- The ambient representative obtained by extending by zero. -/
noncomputable def extend (f : boundedHolomorphicSections I F W) : X → F :=
  Function.extend Subtype.val (f : W →ᵇ F) (fun _ => 0)

@[simp]
theorem extend_apply (f : boundedHolomorphicSections I F W) (z : W) :
    extend f z = (f : W →ᵇ F) z :=
  Subtype.val_injective.extend_apply _ _ _

/-- The zero extension is holomorphic on `W`. -/
theorem mdifferentiableOn_extend (f : boundedHolomorphicSections I F W) :
    MDifferentiableOn I 𝓘(ℂ, F) (extend f) W :=
  mem_boundedHolomorphicSections_iff_extend.mp f.property

/-- The zero extension is bounded everywhere by the supremum norm. -/
theorem norm_extend_apply_le (f : boundedHolomorphicSections I F W) (z : X) :
    ‖extend f z‖ ≤ ‖f‖ := by
  by_cases hz : z ∈ W
  · rw [extend_apply f ⟨z, hz⟩]
    exact norm_coe_le_norm (f : W →ᵇ F) ⟨z, hz⟩
  · rw [extend, Function.extend_apply' _ _ _ fun ⟨w, hw⟩ => hz (hw ▸ w.property), norm_zero]
    exact norm_nonneg _

/-- Restriction of bounded holomorphic maps to a smaller open set. -/
noncomputable def restrict (h : W' ≤ W) :
    boundedHolomorphicSections I F W →L[ℂ] boundedHolomorphicSections I F W' :=
  ((compContinuousCLM F ℂ ⟨fun z => ⟨z, h z.2⟩, continuous_subtype_val.subtype_mk _⟩).comp
    (boundedHolomorphicSections I F W).subtypeL).codRestrict _ fun f => by
    exact ⟨extend f, (mdifferentiableOn_extend f).mono h, fun z => extend_apply f ⟨z, h z.2⟩⟩

@[simp]
theorem restrict_apply (h : W' ≤ W) (f : boundedHolomorphicSections I F W) (z : W') :
    (restrict h f : W' →ᵇ F) z = (f : W →ᵇ F) ⟨z, h z.2⟩ := (rfl)

/-- Restriction agrees with restricting the same ambient representative. -/
@[simp]
theorem restrict_of (h : W' ≤ W) (g : X → F) (hg : MDifferentiableOn I 𝓘(ℂ, F) g W) (C : ℝ)
    (hC : ∀ z ∈ W, ‖g z‖ ≤ C) :
    restrict h (of W g hg C hC) = of W' g (MDifferentiableOn.mono hg h) C fun z hz => hC z (h hz) :=
  ext fun z => by simp

/-- Restriction does not increase the supremum norm. -/
theorem norm_restrict_apply_le (h : W' ≤ W) (f : boundedHolomorphicSections I F W) :
    ‖restrict h f‖ ≤ ‖f‖ :=
  norm_compContinuous_le (f : W →ᵇ F) _

/-- Restriction to the same open set is the identity. -/
@[simp]
theorem restrict_refl : restrict (I := I) (F := F) (le_refl W) = ContinuousLinearMap.id ℂ _ :=
  ContinuousLinearMap.ext fun _ => Subtype.ext (BoundedContinuousFunction.ext fun _ => rfl)

/-- Restrictions compose. -/
@[simp]
theorem restrict_comp_restrict (h : W' ≤ W) (h' : W'' ≤ W') :
    (restrict (I := I) (F := F) h').comp (restrict h) = restrict (h'.trans h) :=
  ContinuousLinearMap.ext fun _ => Subtype.ext (BoundedContinuousFunction.ext fun _ => rfl)

variable [IsManifold I 1 X]

/-- **Cauchy estimate in a chart.** If the ball of radius `R` around `x`, read in the extended
chart at `x`, is mapped by the inverse chart into `W`, then a bounded holomorphic function `f` on
`W` satisfies `dist (f z) (f x) ≤ 2 * ‖f‖ / R * dist (φ z) (φ x)` for every `z` in the chart
domain with `φ z` in that ball, where `φ` is the extended chart. -/
theorem dist_apply_le_of_ball_subset (f : boundedHolomorphicSections I F W) {x z : W} {R : ℝ}
    (hR : ball (extChartAt I (x : X) x) R ⊆
      (extChartAt I (x : X)).target ∩ (extChartAt I (x : X)).symm ⁻¹' W)
    (hzs : (z : X) ∈ (extChartAt I (x : X)).source)
    (hz : extChartAt I (x : X) z ∈ ball (extChartAt I (x : X) x) R) :
    dist ((f : W →ᵇ F) z) ((f : W →ᵇ F) x) ≤
      2 * ‖f‖ / R * dist (extChartAt I (x : X) z) (extChartAt I (x : X) x) := by
  set φ := extChartAt I (x : X)
  have hc : φ x ∈ ball (φ x) R := mem_ball_self (dist_nonneg.trans_lt hz)
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball
    ((MDifferentiableOn.differentiableOn_comp_extChartAt_symm (mdifferentiableOn_extend f)
      (x : X)).mono hR)
    (mapsTo_closedBall_of_forall_norm_le (fun y _ => norm_extend_apply_le f _) hc) hz
  rwa [Function.comp_apply, Function.comp_apply, φ.left_inv hzs,
    φ.left_inv (mem_extChartAt_source (x : X)), extend_apply, extend_apply] at h

variable [I.Boundaryless] [ProperSpace F]

/-- **Montel's theorem for bounded holomorphic maps on a complex manifold.** If `W'` lies in a
compact subset `K` of `W` and `F` is proper, restriction `H^∞(W, F) → H^∞(W', F)` is a compact
operator. -/
theorem isCompactOperator_restrict {K : Set X} (hK : IsCompact K) (hW'K : (W' : Set X) ⊆ K)
    (hKW : K ⊆ W) :
    IsCompactOperator
      (restrict (I := I) (F := F) (SetLike.coe_subset_coe.mp (hW'K.trans hKW))) := by
  -- The unit ball of `H^∞(W, F)` is equicontinuous on `K` by the Cauchy estimate
  -- `dist_apply_le_of_ball_subset` in charts, so the Arzelà–Ascoli theorem applies.
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ρ : C(K, W) := ⟨fun z => ⟨z, hKW z.2⟩, continuous_subtype_val.subtype_mk _⟩
  let σ : C(W', K) := ⟨fun z => ⟨z, hW'K z.2⟩, continuous_subtype_val.subtype_mk _⟩
  -- The unit ball of `H^∞(W, F)`, restricted to `K`.
  let A : Set (K →ᵇ F) :=
    (fun f : boundedHolomorphicSections I F W => (f : W →ᵇ F).compContinuous ρ) ''
      closedBall 0 1
  have hA : IsCompact (closure A) := by
    refine arzela_ascoli (closedBall 0 1) (isCompact_closedBall 0 1) A ?_ ?_
    · rintro _ z ⟨f, hf, rfl⟩
      rw [mem_closedBall_zero_iff] at hf ⊢
      exact (norm_coe_le_norm (f : W →ᵇ F) _).trans hf
    · -- Equicontinuity at `x`: in the extended chart `φ` at `x`, on a ball of radius `R` mapped
      -- into `W`, the Cauchy estimate gives the common modulus `2 / R * dist (φ z) (φ x)`.
      intro x
      set φ := extChartAt I (x : X)
      obtain ⟨R, hR, hRO⟩ := Metric.isOpen_iff.mp
        (isOpen_extChartAt_target_inter_preimage_symm (I := I) W x)
        (φ x) ⟨mem_extChartAt_target (x : X), by
          simpa [φ, extChartAt_to_inv] using hKW x.2⟩
      have hφ : ContinuousAt (fun z : K => φ z) x :=
        (continuousAt_extChartAt (x : X)).comp continuousAt_subtype_val
      refine equicontinuousAt_of_continuity_modulus (fun z : K => 2 / R * dist (φ z) (φ x)) ?_
        _ ?_
      · have hc : Tendsto (fun z : K => 2 / R * dist (φ z) (φ x)) (𝓝 x)
            (𝓝 (2 / R * dist (φ x) (φ x))) :=
          (hφ.tendsto.dist tendsto_const_nhds).const_mul _
        simpa using hc
      · filter_upwards [continuousAt_subtype_val.preimage_mem_nhds
          (extChartAt_source_mem_nhds (I := I) (x : X)),
          hφ.preimage_mem_nhds (ball_mem_nhds _ hR)] with z hzs hz
        rintro ⟨_, f, hf, rfl⟩
        rw [mem_closedBall_zero_iff] at hf
        rw [dist_comm]
        refine (dist_apply_le_of_ball_subset f (x := ρ x) (z := ρ z) hRO hzs hz).trans ?_
        gcongr
        · linarith
        · exact le_rfl
  let S : (K →ᵇ F) → (W' →ᵇ F) := fun φ => φ.compContinuous σ
  have hcomp : IsCompact (((↑) : boundedHolomorphicSections I F W' → W' →ᵇ F) ⁻¹'
      (S '' closure A)) :=
    (isClosed_boundedHolomorphicSections W').isClosedEmbedding_subtypeVal.isCompact_preimage
      (hA.image (continuous_compContinuous σ))
  refine (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).mpr
    ⟨closedBall 0 1, closedBall_mem_nhds _ one_pos, _, hcomp, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨_, subset_closure ⟨f, hf, rfl⟩, BoundedContinuousFunction.ext fun z =>
    (restrict_apply (SetLike.coe_subset_coe.mp (hW'K.trans hKW)) f z).symm⟩

/-- If `F` is proper, restriction to an open set with compact closure inside `W` is a compact
operator. -/
theorem isCompactOperator_restrict_of_isCompact_closure
    (hW' : IsCompact (closure (W' : Set X))) (hW'W : closure (W' : Set X) ⊆ W) :
    IsCompactOperator
      (restrict (I := I) (F := F) (SetLike.coe_subset_coe.mp (subset_closure.trans hW'W))) :=
  isCompactOperator_restrict hW' subset_closure hW'W

end BoundedHolomorphicSections

/-- A map holomorphic on an open set `W` is bounded on every subset `W'` whose closure is
compact and contained in `W`, so it restricts to an element of `H^∞(W', F)`
(`TauCeti.BoundedHolomorphicSections.of`). -/
theorem _root_.MDifferentiableOn.exists_forall_norm_le_of_isCompact_closure {W : Set X}
    {W' : Set X} {g : X → F} (hg : MDifferentiableOn I 𝓘(ℂ, F) g W) (hW' : IsCompact (closure W'))
    (hW'W : closure W' ⊆ W) : ∃ C, ∀ z ∈ W', ‖g z‖ ≤ C :=
  (hW'.exists_bound_of_continuousOn (hg.continuousOn.mono hW'W)).imp fun _ hC z hz =>
    hC z (subset_closure hz)

end TauCeti
