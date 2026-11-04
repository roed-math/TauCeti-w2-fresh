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
public import TauCeti.AlgebraicGeometry.Modules.Stalk
import TauCeti.AlgebraicGeometry.AffineScheme
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Stalk
import TauCeti.RingTheory.IntegralClosure.Punctured

/-!
# The normalization of a nodal curve

Let `X` be a nodal curve over a field `K`, and `U = X ∖ Sing(X/K)` the complement of its singular
locus, with inclusion `ι : U ⟶ X`. The normalization `ν : X' ⟶ X` of `X` is the normalization of
`X` in `U` along `ι` (`AlgebraicGeometry.Scheme.Hom.normalization`): over an affine open `W` of
`X`, it is the spectrum of the integral closure of `Γ(X, W)` in `Γ(X, U ∩ W)`.

This file proves that this normalization is finite over `X`. Every node `x` has an affine
neighbourhood `W` with a section `a` such that `U ∩ W = D(a)`, and the integral closure of
`Γ(X, W)` in `Γ(X, W)_a` is finite
(`AlgebraicGeometry.Scheme.exists_affineOpen_integralClosure_away`).
Every other point has an affine neighbourhood `W ⊆ U`, over which the integral closure is
`Γ(X, W)` itself. Finiteness of the normalization is local on `X`
(`AlgebraicGeometry.Scheme.Hom.isFinite_fromNormalization_of_iSup_eq_top`).

On the same cover the conductor of `ν` is the ideal of the singular locus, and `ι` is
scheme-theoretically dominant, so the normalization sequence
`0 → 𝒪_X → ν_* 𝒪_X' → ν_* 𝒪_X' / 𝒪_X → 0` is short exact. Its cokernel is computed from the
cokernels of the integral closures: over an affine open its sections are the cokernel of
`Γ(X, W)` in its integral closure
(`AlgebraicGeometry.Scheme.Hom.cokernelUnitToPushforwardObjUnitSectionsEquiv`). Hence the cokernel
vanishes off `Sing(X/K)`, and its stalk at a node `x` is the residue field `κ(x)`: the classical
normalization sequence `0 → 𝒪_X → ν_* 𝒪_X' → ⨁_{x ∈ Sing(X/K)} κ(x) → 0`, with `δ`-invariant one
at every node.

## Main results

* `AlgebraicGeometry.Scheme.isFinite_fromNormalization_compl_singularLocus`: the normalization of
  a nodal curve over a field in the complement of its singular locus is finite.
* `AlgebraicGeometry.Scheme.conductor_fromNormalization_compl_singularLocus`: its conductor is the
  ideal sheaf of the singular locus.
* `AlgebraicGeometry.Scheme.isSchemeTheoreticallyDominant_ι_compl_singularLocus`: the complement
  of the singular locus is scheme-theoretically dense.
* `AlgebraicGeometry.Scheme.shortExact_cokernelSequence_fromNormalization`: the normalization
  sequence `0 → 𝒪_X → ν_* 𝒪_X' → ν_* 𝒪_X' / 𝒪_X → 0` is short exact.
* `AlgebraicGeometry.Scheme.annihilator_cokernel_fromNormalization_sections`: over every affine
  open `W`, the annihilator of the sections of `ν_* 𝒪_X' / 𝒪_X` is the ideal of the singular locus.
* `AlgebraicGeometry.Scheme.exists_affineOpen_cokernel_fromNormalization_sections`: locally on
  `X`, the sections of `ν_* 𝒪_X' / 𝒪_X` over an affine open `W` are the functions on the singular
  locus over `W`.
* `AlgebraicGeometry.Scheme.subsingleton_cokernel_fromNormalization_stalk`: the stalk of
  `ν_* 𝒪_X' / 𝒪_X` vanishes off the singular locus.
* `AlgebraicGeometry.Scheme.nonempty_cokernel_fromNormalization_stalk_linearEquiv`: at a node `x`,
  the stalk of `ν_* 𝒪_X' / 𝒪_X` is the residue field `κ(x)`, as an `𝒪_{X,x}`-module.

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
the ideal of the singular locus and with cokernel the functions on the singular locus over `W`.
If `x` is a node, this ideal is the prime of `x`, which is maximal. Here `U` is the complement of
the singular locus. -/
private theorem exists_affineOpen_integralClosure
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) {U : X.Opens}
    (hU : letI := hnodal.syntomic; (U : Set X) = ((X.singularLocus K).support : Set X)ᶜ) (x : X) :
    letI := hnodal.syntomic
    ∃ (W : X.affineOpens) (hxW : x ∈ W.1),
      letI := (U.ι.app W).hom.toAlgebra
      Function.Injective (U.ι.app W).hom ∧
      Module.Finite Γ(X, W) (integralClosure Γ(X, W) Γ(U, U.ι ⁻¹ᵁ W)) ∧
      TauCeti.Algebra.conductor Γ(X, W) (integralClosure Γ(X, W) Γ(U, U.ι ⁻¹ᵁ W)) =
        (X.singularLocus K).ideal W ∧
      Nonempty ((integralClosure Γ(X, W) Γ(U, U.ι ⁻¹ᵁ W) ⧸
        (1 : Submodule Γ(X, W) (integralClosure Γ(X, W) Γ(U, U.ι ⁻¹ᵁ W)))) ≃ₗ[Γ(X, W)]
          Γ(X, W) ⧸ (X.singularLocus K).ideal W) ∧
      (x ∈ (X.singularLocus K).support →
        (X.singularLocus K).ideal W = (W.2.primeIdealOf ⟨x, hxW⟩).asIdeal ∧
          (W.2.primeIdealOf ⟨x, hxW⟩).asIdeal.IsMaximal) := by
  let := hnodal.syntomic
  -- Over an affine open `W`, the functions on `U ∩ W` are those on `U.ι ''ᵁ U.ι ⁻¹ᵁ W = U ⊓ W`.
  have hUW (W : X.Opens) : U.ι ''ᵁ U.ι ⁻¹ᵁ W = U ⊓ W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hle (W : X.Opens) : U.ι ''ᵁ U.ι ⁻¹ᵁ W ≤ W := Set.image_preimage_subset _ _
  by_cases hx : x ∈ (X.singularLocus K).support
  · -- At a node, `U ∩ W = D(a)`, and the integral closure in `Γ(X, W)_a` is finite with
    -- conductor the prime of `x`, which is the ideal of the singular locus over `W`.
    obtain ⟨W, hxW, a, hbasic, hideal, hmax, hnzd, -, hfin, hcond, ⟨eQ⟩⟩ :=
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
      ((TauCeti.Algebra.conductor_congr φ).symm.trans hcond).trans hideal.symm,
      ⟨(TauCeti.Algebra.quotientOneEquiv φ).symm ≪≫ₗ eQ ≪≫ₗ
        Submodule.quotEquivOfEq _ _ hideal.symm⟩, fun _ ↦ ⟨hideal, hmax⟩⟩
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
    -- `Γ(X, W)` maps onto its integral closure, and no point of `W ⊆ U` is singular.
    have hsurj : Function.Surjective
        (algebraMap Γ(X, W) (integralClosure Γ(X, W) Γ(U, U.ι ⁻¹ᵁ W))) := fun b ↦ by
      obtain ⟨c, hc⟩ := ψ.surjective b.1
      exact ⟨c, Subtype.ext ((ψ.commutes c).symm.trans hc)⟩
    have htop : (X.singularLocus K).ideal ⟨W, hW⟩ = ⊤ := by
      refine (Ideal.eq_top_iff_one _).mpr (by_contra fun h ↦ ?_)
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
    -- Both cokernels vanish.
    have : Subsingleton (integralClosure Γ(X, W) Γ(U, U.ι ⁻¹ᵁ W) ⧸
        (1 : Submodule Γ(X, W) (integralClosure Γ(X, W) Γ(U, U.ι ⁻¹ᵁ W)))) :=
      Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun b _ ↦
        Submodule.mem_one.mpr (hsurj b))
    have : Subsingleton (Γ(X, W) ⧸ (X.singularLocus K).ideal ⟨W, hW⟩) :=
      Submodule.Quotient.subsingleton_iff.mpr htop
    exact ⟨IsLocalization.injective (M := .powers 1) _
      (Submonoid.powers_le.mpr (Submonoid.one_mem _)),
      .of_injective (integralClosure Γ(X, W) Γ(U, U.ι ⁻¹ᵁ W)).val.toLinearMap
        Subtype.val_injective,
      (TauCeti.Algebra.conductor_eq_top_iff.mpr hsurj).trans htop.symm,
      ⟨.ofSubsingleton _ _⟩, fun h ↦ absurd h hx⟩

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
  exact (hW x).2.2.1

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
`𝒪_X → ν_* 𝒪_X'` is injective, so with its cokernel it forms a short exact sequence
`0 → 𝒪_X → ν_* 𝒪_X' → ν_* 𝒪_X' / 𝒪_X → 0` of sheaves of modules. -/
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

/-- **The cokernel of the normalization sequence of a nodal curve is supported on the singular
locus.** Let `X` be a nodal curve over a field `K` and `ν` the normalization of `X` in the
complement of its singular locus. Over every affine open `W` of `X`, the annihilator of the
sections of the cokernel `ν_* 𝒪_X' / 𝒪_X` of the normalization sequence is the ideal `I(W)` of
the singular locus `Sing(X/K)`. -/
theorem _root_.AlgebraicGeometry.Scheme.annihilator_cokernel_fromNormalization_sections
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) (W : X.affineOpens) :
    letI := hnodal.syntomic
    haveI := hnodal.syntomic.locallyOfFinitePresentation 1 (X ↘ Spec (.of K))
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
    Module.annihilator Γ(X, W) (Γ(Limits.cokernel (SheafOfModules.unitToPushforwardObjUnit
      (Scheme.Opens.ι (X.singularLocus K).support.compl).fromNormalization.toRingCatSheafHom),
        W)) = (X.singularLocus K).ideal W := by
  let := hnodal.syntomic
  have := hnodal.syntomic.locallyOfFinitePresentation 1 (X ↘ Spec (.of K))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have := X.isFinite_fromNormalization_compl_singularLocus hnodal
  have := X.isSchemeTheoreticallyDominant_ι_compl_singularLocus hnodal
  let ι := Scheme.Opens.ι (X.singularLocus K).support.compl
  let := (ι.app W).hom.toAlgebra
  let := (ι.fromNormalization.app W).hom.toAlgebra
  -- The annihilator of the cokernel of `Γ(X, W)` in its integral closure is the conductor.
  rw [← (ι.fromNormalization.cokernelUnitToPushforwardObjUnitSectionsEquiv W).annihilator_eq,
    (TauCeti.Algebra.quotientOneEquiv (ι.normalizationObjAlgEquiv W)).annihilator_eq,
    ← TauCeti.Algebra.conductor_eq_annihilator, ← Scheme.Hom.conductor_fromNormalization_ideal,
    X.conductor_fromNormalization_compl_singularLocus hnodal]

/-- **The cokernel of the normalization sequence of a nodal curve, locally.** Let `X` be a nodal
curve over a field `K` and `ν` the normalization of `X` in the complement of its singular locus.
Every point of `X` has an affine open neighbourhood `W` over which the sections of the cokernel
`ν_* 𝒪_X' / 𝒪_X` of the normalization sequence are the functions `Γ(X, W) / I(W)` on the
singular locus `Sing(X/K)` over `W`, as `Γ(X, W)`-modules. -/
theorem _root_.AlgebraicGeometry.Scheme.exists_affineOpen_cokernel_fromNormalization_sections
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) (x : X) :
    letI := hnodal.syntomic
    haveI := hnodal.syntomic.locallyOfFinitePresentation 1 (X ↘ Spec (.of K))
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
    ∃ W : X.affineOpens, x ∈ W.1 ∧
      Nonempty (Γ(Limits.cokernel (SheafOfModules.unitToPushforwardObjUnit
        (Scheme.Opens.ι (X.singularLocus K).support.compl).fromNormalization.toRingCatSheafHom),
          W) ≃ₗ[Γ(X, W)] Γ(X, W) ⧸ (X.singularLocus K).ideal W) := by
  let := hnodal.syntomic
  have := hnodal.syntomic.locallyOfFinitePresentation 1 (X ↘ Spec (.of K))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have := X.isFinite_fromNormalization_compl_singularLocus hnodal
  have := X.isSchemeTheoreticallyDominant_ι_compl_singularLocus hnodal
  obtain ⟨W, hxW, -, -, -, ⟨e⟩, -⟩ := exists_affineOpen_integralClosure X hnodal
    (U := (X.singularLocus K).support.compl) rfl x
  let ι := Scheme.Opens.ι (X.singularLocus K).support.compl
  let := (ι.app W).hom.toAlgebra
  let := (ι.fromNormalization.app W).hom.toAlgebra
  -- The sections of the cokernel are the cokernel of `Γ(X, W)` in the sections of the
  -- normalization, which are the integral closure of `Γ(X, W)` in `Γ(X, W ∖ Sing(X/K))`.
  exact ⟨W, hxW, ⟨(ι.fromNormalization.cokernelUnitToPushforwardObjUnitSectionsEquiv W).symm ≪≫ₗ
    TauCeti.Algebra.quotientOneEquiv (ι.normalizationObjAlgEquiv W) ≪≫ₗ e⟩⟩

/-- **The cokernel of the normalization sequence vanishes off the singular locus.** Let `X` be a
nodal curve over a field `K` and `ν` the normalization of `X` in the complement of its singular
locus. At a point `x ∉ Sing(X/K)`, the stalk of the cokernel `ν_* 𝒪_X' / 𝒪_X` is zero. -/
theorem _root_.AlgebraicGeometry.Scheme.subsingleton_cokernel_fromNormalization_stalk
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) {x : X}
    (hx : letI := hnodal.syntomic; x ∉ (X.singularLocus K).support) :
    letI := hnodal.syntomic
    haveI := hnodal.syntomic.locallyOfFinitePresentation 1 (X ↘ Spec (.of K))
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
    Subsingleton (TopCat.Presheaf.stalk (C := Ab.{u}) (Scheme.Modules.presheaf (Limits.cokernel
      (SheafOfModules.unitToPushforwardObjUnit
        (Scheme.Opens.ι (X.singularLocus K).support.compl).fromNormalization.toRingCatSheafHom)))
      x) := by
  let := hnodal.syntomic
  have := hnodal.syntomic.locallyOfFinitePresentation 1 (X ↘ Spec (.of K))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have := X.isFinite_fromNormalization_compl_singularLocus hnodal
  let M : X.Modules := Limits.cokernel (SheafOfModules.unitToPushforwardObjUnit
    (Scheme.Opens.ι (X.singularLocus K).support.compl).fromNormalization.toRingCatSheafHom)
  have : M.IsQuasicoherent := Scheme.Hom.isQuasicoherent_cokernel_unitToPushforwardObjUnit _
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let y : (W : X.Opens) := ⟨x, hxW⟩
  -- Some function `f` in the ideal of the singular locus over `W` does not vanish at `x`.
  obtain ⟨f, hf, hxf⟩ : ∃ f ∈ (X.singularLocus K).ideal ⟨W, hW⟩, x ∈ X.basicOpen f := by
    by_contra! h
    exact hx (((X.singularLocus K).mem_support_iff_of_mem (U := ⟨W, hW⟩) hxW).mpr
      ((X.mem_zeroLocus_iff _ x).mpr fun f hf hxf ↦ h f hf hxf))
  let p := (hW.primeIdealOf y).asIdeal.primeCompl
  let := M.moduleSectionStalk y
  have hfp : f ∈ p := (hW.mem_basicOpen_iff_notMem_primeIdealOf hxW f).mp hxf
  have := M.isLocalizedModule_germₗ y hW
  -- `f` kills the sections of the cokernel over `W`, so their germs at `x` vanish.
  have hzero (m : Γ(M, W)) : M.germₗ y m = 0 := by
    refine (IsLocalizedModule.eq_zero_iff p (M.germₗ y)).mpr ⟨⟨f, hfp⟩, ?_⟩
    exact Module.mem_annihilator.mp
      ((X.annihilator_cokernel_fromNormalization_sections hnodal ⟨W, hW⟩).ge hf) m
  refine subsingleton_of_forall_eq 0 fun z ↦ ?_
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj p (M.germₗ y) z
  rw [hzero] at hs
  refine ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (M.germₗ y) s)).1 ?_
  rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, smul_zero]
  exact hs

/-- **The cokernel of the normalization sequence at a node.** Let `X` be a nodal curve over a
field `K` and `ν` the normalization of `X` in the complement of its singular locus. At a node
`x ∈ Sing(X/K)`, the stalk of the cokernel `ν_* 𝒪_X' / 𝒪_X` is the residue field `κ(x)`, as an
`𝒪_{X,x}`-module: one branch of `X'` over `x` contributes the functions on `x` modulo those on
`X`. -/
theorem _root_.AlgebraicGeometry.Scheme.nonempty_cokernel_fromNormalization_stalk_linearEquiv
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) {x : X}
    (hx : letI := hnodal.syntomic; x ∈ (X.singularLocus K).support) :
    letI := hnodal.syntomic
    haveI := hnodal.syntomic.locallyOfFinitePresentation 1 (X ↘ Spec (.of K))
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
    Nonempty (TopCat.Presheaf.stalk (C := Ab.{u}) (Scheme.Modules.presheaf (Limits.cokernel
      (SheafOfModules.unitToPushforwardObjUnit
        (Scheme.Opens.ι (X.singularLocus K).support.compl).fromNormalization.toRingCatSheafHom)))
      x ≃ₗ[X.presheaf.stalk x]
        X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) := by
  let := hnodal.syntomic
  have := hnodal.syntomic.locallyOfFinitePresentation 1 (X ↘ Spec (.of K))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have := X.isFinite_fromNormalization_compl_singularLocus hnodal
  have := X.isSchemeTheoreticallyDominant_ι_compl_singularLocus hnodal
  let M : X.Modules := Limits.cokernel (SheafOfModules.unitToPushforwardObjUnit
    (Scheme.Opens.ι (X.singularLocus K).support.compl).fromNormalization.toRingCatSheafHom)
  have : M.IsQuasicoherent := Scheme.Hom.isQuasicoherent_cokernel_unitToPushforwardObjUnit _
  obtain ⟨W, hxW, -, -, -, ⟨e⟩, hW⟩ := exists_affineOpen_integralClosure X hnodal
    (U := (X.singularLocus K).support.compl) rfl x
  obtain ⟨hideal, hmax⟩ := hW hx
  let y : (W : X.Opens) := ⟨x, hxW⟩
  let ι := Scheme.Opens.ι (X.singularLocus K).support.compl
  let := (ι.app W).hom.toAlgebra
  let := (ι.fromNormalization.app W).hom.toAlgebra
  -- Over `W`, the sections of the cokernel are `Γ(X, W)` modulo the prime of `x`.
  let e' : Γ(M, W) ≃ₗ[Γ(X, W)] Γ(X, W) ⧸ (W.2.primeIdealOf y).asIdeal :=
    (ι.fromNormalization.cokernelUnitToPushforwardObjUnitSectionsEquiv W).symm ≪≫ₗ
      TauCeti.Algebra.quotientOneEquiv (ι.normalizationObjAlgEquiv W) ≪≫ₗ e ≪≫ₗ
        Submodule.quotEquivOfEq _ _ hideal
  let p := (W.2.primeIdealOf y).asIdeal.primeCompl
  let := X.presheaf.algebra_section_stalk y
  let := M.moduleSectionStalk y
  have := M.isScalarTower_sectionStalk y
  have := W.2.isLocalization_stalk y
  have := M.isLocalizedModule_germₗ y W.2
  -- Both the stalk of the cokernel and the residue field are localizations of `Γ(X, W) / 𝔭_x`.
  have h₁ : IsLocalizedModule p (M.germₗ y ∘ₗ e'.symm.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right p (M.germₗ y) e'.symm
  have : IsLocalizedModule p (LinearMap.id : (X.presheaf.stalk x ⧸
      IsLocalRing.maximalIdeal (X.presheaf.stalk y)) →ₗ[Γ(X, W)] _) :=
    isLocalizedModule_id p _ (X.presheaf.stalk y)
  have h₂ : IsLocalizedModule p (LinearMap.id ∘ₗ
      (quotientEquivQuotientMaximalIdeal (W.2.primeIdealOf y).asIdeal
        (X.presheaf.stalk y)).toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right p _ _
  exact ⟨(IsLocalizedModule.linearEquiv p (M.germₗ y ∘ₗ e'.symm.toLinearMap) (LinearMap.id ∘ₗ
    (quotientEquivQuotientMaximalIdeal (W.2.primeIdealOf y).asIdeal
      (X.presheaf.stalk y)).toLinearMap)).extendScalarsOfIsLocalization p (X.presheaf.stalk y)⟩

end TauCeti.AlgebraicGeometry
