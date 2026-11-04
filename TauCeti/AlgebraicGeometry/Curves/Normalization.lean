/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Stalk
public import TauCeti.AlgebraicGeometry.Normalization.Basic
public import TauCeti.AlgebraicGeometry.Normalization.Finite
public import TauCeti.AlgebraicGeometry.Modules.StructureSheafSequence
import TauCeti.AlgebraicGeometry.AffineScheme

/-!
# The normalization of a nodal curve

Let `X` be a nodal curve over a field `K`, and `U = X ∖ Sing(X/K)` the complement of its singular
locus, with inclusion `ι : U ⟶ X`. The normalization of `X` is the normalization of `X` in `U`
along `ι` (`AlgebraicGeometry.Scheme.Hom.normalization`): over an affine open `W` of `X`, it is the
spectrum of the integral closure of `Γ(X, W)` in `Γ(X, U ∩ W)`.

This file proves that this normalization is finite over `X`. Every node `x` has an affine
neighbourhood `W` with a section `a` such that `U ∩ W = D(a)`, and the integral closure of
`Γ(X, W)` in `Γ(X, W)_a` is finite
(`AlgebraicGeometry.Scheme.exists_affineOpen_integralClosure_away`).
Every other point has an affine neighbourhood `W ⊆ U`, over which the integral closure is
`Γ(X, W)` itself. Finiteness of the normalization is local on `X`
(`AlgebraicGeometry.Scheme.Hom.isFinite_fromNormalization_of_iSup_eq_top`).

## Main results

* `AlgebraicGeometry.Scheme.isFinite_fromNormalization_compl_singularLocus`: the normalization of
  a nodal curve over a field in the complement of its singular locus is finite.
* `AlgebraicGeometry.Scheme.conductor_fromNormalization_compl_singularLocus`: its conductor is the
  ideal sheaf of the singular locus.
* `AlgebraicGeometry.Scheme.isSchemeTheoreticallyDominant_ι_compl_singularLocus`: the complement
  of the singular locus is scheme-theoretically dense.
* `AlgebraicGeometry.Scheme.shortExact_cokernelSequence_fromNormalization`: the normalization
  sequence `0 → 𝒪_X → ν_* 𝒪_X̃ → ν_* 𝒪_X̃ / 𝒪_X → 0` is short exact.

## References

* [Stacks Project, Section 53.19, Tag 0C46](https://stacks.math.columbia.edu/tag/0C46): nodes of
  curves over a field.
* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H): relative normalization.
-/

public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace TauCeti.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

/-- Every point of a nodal curve `X` over a field has an affine open neighbourhood `W` over which
the integral closure of `Γ(X, W)` in the functions on `W ∖ Sing(X/K)` is finite, with conductor
the ideal of the singular locus. Here `U` is the complement of the singular locus. -/
private theorem exists_affineOpen_integralClosure
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) {U : X.Opens}
    (hU : letI := hnodal.syntomic; (U : Set X) = ((X.singularLocus K).support : Set X)ᶜ) (x : X) :
    letI := hnodal.syntomic
    ∃ W : X.affineOpens, x ∈ W.1 ∧
      letI := (U.ι.app W).hom.toAlgebra
      Function.Injective (U.ι.app W).hom ∧
      Module.Finite Γ(X, W) (integralClosure Γ(X, W) Γ(U, U.ι ⁻¹ᵁ W)) ∧
      TauCeti.Algebra.conductor Γ(X, W) (integralClosure Γ(X, W) Γ(U, U.ι ⁻¹ᵁ W)) =
        (X.singularLocus K).ideal W := by
  let := hnodal.syntomic
  -- Over an affine open `W`, the functions on `U ∩ W` are those on `U.ι ''ᵁ U.ι ⁻¹ᵁ W = U ⊓ W`.
  have hUW (W : X.Opens) : U.ι ''ᵁ U.ι ⁻¹ᵁ W = U ⊓ W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hle (W : X.Opens) : U.ι ''ᵁ U.ι ⁻¹ᵁ W ≤ W := Set.image_preimage_subset _ _
  by_cases hx : x ∈ (X.singularLocus K).support
  · -- At a node, `U ∩ W = D(a)`, and the integral closure in `Γ(X, W)_a` is finite with
    -- conductor the prime of `x`, which is the ideal of the singular locus over `W`.
    obtain ⟨W, hxW, a, hbasic, hideal, hnzd, -, hfin, hcond, -⟩ :=
      X.exists_affineOpen_integralClosure_away hnodal hx
    refine ⟨W, hxW, ?_⟩
    have e : U.ι ''ᵁ U.ι ⁻¹ᵁ W = X.basicOpen a := by
      rw [hUW]
      refine Opens.ext ?_
      rw [hbasic, Opens.coe_inf, hU, Set.sdiff_eq, Set.inter_comm]
    let := (U.ι.app W).hom.toAlgebra
    -- `Γ(U, U.ι ⁻¹ᵁ W)` is `Γ(X, U.ι ''ᵁ U.ι ⁻¹ᵁ W)`, and `U.ι.app W` is the restriction map.
    have : IsLocalization.Away a Γ(U, U.ι ⁻¹ᵁ W) :=
      W.2.isLocalization_of_eq_basicOpen a (homOfLE (hle W)) e
    let φ := (IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a)
      Γ(U, U.ι ⁻¹ᵁ W)).mapIntegralClosure
    exact ⟨IsLocalization.injective (M := .powers a) _ (Submonoid.powers_le.mpr hnzd),
      .equiv φ.toLinearEquiv,
      ((TauCeti.Algebra.conductor_congr φ).symm.trans hcond).trans hideal.symm⟩
  · -- Away from the singular locus, `W ⊆ U` and `Γ(X, W)` is its own integral closure.
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (a := x) (hU ▸ hx : x ∈ (U : Set X)) U.isOpen
    refine ⟨⟨W, hW⟩, hxW, ?_⟩
    have e : U.ι ''ᵁ U.ι ⁻¹ᵁ W = X.basicOpen (1 : Γ(X, W)) := by
      rw [hUW, Scheme.basicOpen_one]
      exact inf_eq_right.mpr hWU
    let := (U.ι.app W).hom.toAlgebra
    have : IsLocalization.Away (1 : Γ(X, W)) Γ(U, U.ι ⁻¹ᵁ W) :=
      hW.isLocalization_of_eq_basicOpen 1 (homOfLE (hle W)) e
    have : IsNoetherianRing Γ(X, W) := by
      have := hnodal.syntomic.locallyOfFinitePresentation 1 (X ↘ Spec (.of K))
      have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
      exact IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    let ψ := IsLocalization.atOne Γ(X, W) Γ(U, U.ι ⁻¹ᵁ W)
    have : Module.Finite Γ(X, W) Γ(U, U.ι ⁻¹ᵁ W) := .equiv ψ.toLinearEquiv
    refine ⟨IsLocalization.injective (M := .powers 1) _
      (Submonoid.powers_le.mpr (Submonoid.one_mem _)),
      .of_injective (integralClosure Γ(X, W) Γ(U, U.ι ⁻¹ᵁ W)).val.toLinearMap
        Subtype.val_injective, ?_⟩
    -- Both ideals are the unit ideal: `Γ(X, W)` maps onto its integral closure, and no point of
    -- `W ⊆ U` is singular.
    refine (TauCeti.Algebra.conductor_eq_top_iff.mpr fun b ↦ ?_).trans ?_
    · obtain ⟨c, hc⟩ := ψ.surjective b.1
      exact ⟨c, Subtype.ext ((ψ.commutes c).symm.trans hc)⟩
    · refine ((Ideal.eq_top_iff_one _).mpr (by_contra fun h ↦ ?_)).symm
      obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ ((Ideal.ne_top_iff_one _).mpr h)
      have : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
      let y : (W : X.Opens) := ⟨hW.fromSpec ⟨M, hM.isPrime⟩,
        hW.range_fromSpec.subset (Set.mem_range_self _)⟩
      have hyM : hW.primeIdealOf y = ⟨M, hM.isPrime⟩ :=
        hW.fromSpec.isOpenEmbedding.injective (hW.fromSpec_primeIdealOf y)
      refine (hU ▸ hWU y.2 : y.1 ∈ ((X.singularLocus K).support : Set X)ᶜ)
        (((X.singularLocus K).mem_support_iff_of_mem (U := ⟨W, hW⟩) y.2).mpr
          ((X.mem_zeroLocus_iff _ y.1).mpr fun f hf hyf ↦ ?_))
      exact (IsAffineOpen.mem_basicOpen_iff_notMem_primeIdealOf hW y.2 f).mp hyf
        (hyM ▸ hIM hf)

/-- **The normalization of a nodal curve is finite.** Let `X` be a nodal curve over a field `K`.
The normalization of `X` in the complement `X ∖ Sing(X/K)` of its singular locus is finite over
`X`. -/
theorem _root_.AlgebraicGeometry.Scheme.isFinite_fromNormalization_compl_singularLocus
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    haveI := hnodal.syntomic.locallyOfFinitePresentation 1 (X ↘ Spec (.of K))
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
    IsFinite (Scheme.Opens.ι (X.singularLocus K).support.compl).fromNormalization := by
  let := hnodal.syntomic
  have := hnodal.syntomic.locallyOfFinitePresentation 1 (X ↘ Spec (.of K))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  choose W hxW hW using exists_affineOpen_integralClosure X hnodal
    (U := (X.singularLocus K).support.compl) rfl
  exact Scheme.Hom.isFinite_fromNormalization_of_iSup_eq_top _ W
    (top_le_iff.mp fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩) fun x ↦ (hW x).2.1

/-- **The conductor of a nodal curve.** Let `X` be a nodal curve over a field `K` and `ν` the
normalization of `X` in the complement of its singular locus. The conductor of `ν` is the ideal
sheaf of the singular locus `Sing(X/K)`. -/
theorem _root_.AlgebraicGeometry.Scheme.conductor_fromNormalization_compl_singularLocus
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    haveI := hnodal.syntomic.locallyOfFinitePresentation 1 (X ↘ Spec (.of K))
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
    haveI := X.isFinite_fromNormalization_compl_singularLocus hnodal
    (Scheme.Opens.ι (X.singularLocus K).support.compl).fromNormalization.conductor =
      X.singularLocus K := by
  let := hnodal.syntomic
  have := hnodal.syntomic.locallyOfFinitePresentation 1 (X ↘ Spec (.of K))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have := X.isFinite_fromNormalization_compl_singularLocus hnodal
  choose W hxW hW using exists_affineOpen_integralClosure X hnodal
    (U := (X.singularLocus K).support.compl) rfl
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top W
    (top_le_iff.mp fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩) fun x ↦ ?_
  rw [Scheme.Hom.conductor_fromNormalization_ideal]
  exact (hW x).2.2

/-- **The smooth locus of a nodal curve is scheme-theoretically dense.** Let `X` be a nodal curve
over a field `K`. Restriction of functions from `X` to the complement of `Sing(X/K)` is injective:
the inclusion of the complement is scheme-theoretically dominant. -/
theorem _root_.AlgebraicGeometry.Scheme.isSchemeTheoreticallyDominant_ι_compl_singularLocus
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    IsSchemeTheoreticallyDominant (Scheme.Opens.ι (X.singularLocus K).support.compl) := by
  let := hnodal.syntomic
  have := hnodal.syntomic.locallyOfFinitePresentation 1 (X ↘ Spec (.of K))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  choose W hxW hW using exists_affineOpen_integralClosure X hnodal
    (U := (X.singularLocus K).support.compl) rfl
  refine ⟨Scheme.IdealSheafData.ext_of_iSup_eq_top W
    (top_le_iff.mp fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩) fun x ↦ ?_⟩
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (hW x).1

/-- **The normalization sequence of a nodal curve.** Let `X` be a nodal curve over a field `K` and
`ν` the normalization of `X` in the complement of its singular locus. Pullback of functions
`𝒪_X → ν_* 𝒪_X̃` is injective, so with its cokernel it forms a short exact sequence
`0 → 𝒪_X → ν_* 𝒪_X̃ → ν_* 𝒪_X̃ / 𝒪_X → 0` of sheaves of modules. -/
theorem _root_.AlgebraicGeometry.Scheme.shortExact_cokernelSequence_fromNormalization
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    haveI := hnodal.syntomic.locallyOfFinitePresentation 1 (X ↘ Spec (.of K))
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
    (ShortComplex.cokernelSequence (SheafOfModules.unitToPushforwardObjUnit
      (Scheme.Opens.ι (X.singularLocus K).support.compl).fromNormalization.toRingCatSheafHom)
      ).ShortExact := by
  let := hnodal.syntomic
  have := hnodal.syntomic.locallyOfFinitePresentation 1 (X ↘ Spec (.of K))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have := X.isFinite_fromNormalization_compl_singularLocus hnodal
  have := X.isSchemeTheoreticallyDominant_ι_compl_singularLocus hnodal
  exact cokernelSequence_shortExact _

end TauCeti.AlgebraicGeometry
