/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Cohomological dimension is invariant under isomorphism

An isomorphism of topological groups `e : G ≃ₜ* H` identifies the discrete `H`-modules with the
discrete `G`-modules, by restriction along `e`, and the map `Hⁱ(H, M) → Hⁱ(G, M)` it induces on
continuous cohomology is injective, being split by the map along `e⁻¹`. So the strict
`p`-cohomological dimension of `H` is at most that of `G`, and by symmetry they are equal. This is
how a computation of `scd_p` for one model of a profinite group, such as Mathlib's
`Field.absoluteGaloisGroup K` built on the algebraic closure, is read on another, such as
`AbsoluteGaloisGroup K` built on the separable closure.

## Main statements

* `TauCeti.StrictCohomologicalDimensionLE.of_continuousMulEquiv`: `scd_p G ≤ n` gives
  `scd_p H ≤ n` along `G ≃ₜ* H`, as the vanishing predicate.
* `TauCeti.strictCohomologicalDimensionAt_congr`: `scd_p G = scd_p H` along `G ≃ₜ* H`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable {p : ℕ} {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- **`scd_p ≤ n` transports along an isomorphism of topological groups**, as the vanishing
predicate: if `StrictCohomologicalDimensionLE p G n` and `G ≃ₜ* H`, then
`StrictCohomologicalDimensionLE p H n`. -/
theorem StrictCohomologicalDimensionLE.of_continuousMulEquiv (e : G ≃ₜ* H) {n : ℕ}
    (h : StrictCohomologicalDimensionLE.{v} p G n) : StrictCohomologicalDimensionLE.{v} p H n := by
  refine strictCohomologicalDimensionLE_iff.2 fun M _ _ _ _ _ i hi ↦ ?_
  -- `M` is a discrete `G`-module through `e`, and `Hⁱ(H, M)` embeds into `Hⁱ(G, M)`.
  let _ : DistribMulAction G M := DistribMulAction.compHom M (e : G →* H)
  have : ContinuousSMul G M :=
    ⟨(continuous_smul (M := H) (X := M)).comp (e.continuous.prodMap continuous_id)⟩
  have h0 := strictCohomologicalDimensionLE_iff.1 h M i hi
  have hinj := ContinuousCohomology.map_continuousMulEquiv_injective e (ofDiscreteModule ℤ H M) i
  refine (AddSubgroup.eq_bot_iff_forall _).2 fun x ⟨k, hk⟩ ↦ hinj ?_
  rw [_root_.map_zero]
  let F := ConcreteCategory.hom (_root_.ContinuousCohomology.map
    (X := ofDiscreteModule ℤ H M) (e : G →ₜ* H)
    (𝟙 (TopRep.res ((e : G →ₜ* H) : G →* H) (ofDiscreteModule ℤ H M))) i)
  have hx : F x ∈
      AddCommGroup.primaryComponent (continuousCohomology i (ofDiscreteModule ℤ G M)) p :=
    ⟨k, (map_nsmul F (p ^ k) x).symm.trans (by rw [hk, _root_.map_zero]; rfl)⟩
  rw [h0] at hx
  exact hx

/-- `scd_p H ≤ scd_p G` along `G ≃ₜ* H`. -/
private theorem strictCohomologicalDimensionAt_le_of_continuousMulEquiv (e : G ≃ₜ* H) :
    strictCohomologicalDimensionAt.{v} p H ≤ strictCohomologicalDimensionAt.{v} p G := by
  induction hcd : strictCohomologicalDimensionAt.{v} p G using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    exact (strictCohomologicalDimensionAt_le_iff p H n).2
      (((strictCohomologicalDimensionAt_le_iff p G n).1 hcd.le).of_continuousMulEquiv e)

/-- **The strict `p`-cohomological dimension is invariant under isomorphism of topological
groups.** -/
theorem strictCohomologicalDimensionAt_congr (e : G ≃ₜ* H) :
    strictCohomologicalDimensionAt.{v} p G = strictCohomologicalDimensionAt.{v} p H :=
  le_antisymm (strictCohomologicalDimensionAt_le_of_continuousMulEquiv e.symm)
    (strictCohomologicalDimensionAt_le_of_continuousMulEquiv e)

end TauCeti
