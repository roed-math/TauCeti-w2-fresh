/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Support.Comparison
public import TauCeti.Examples.AlgebraicGeometry.Cohomology.Support
public import TauCeti.Examples.AlgebraicGeometry.Cohomology.Support.Comparison

/-!
# Checks for cohomology with supports and local cohomology

This file collects the checks of cohomology with supports `H^q_Z(X, F)` and of native local
cohomology `H^q_I(M)`:

* `TauCeti.Supports.test_support_all` and `TauCeti.Supports.test_support_empty`: supports in the
  whole space give ordinary cohomology, supports in the empty set give zero;
* `TauCeti.Supports.test_support_affine_line_origin`: on the affine line `𝔸¹_k` with supports at
  the origin, `H⁰ = 0` and `H¹ ≅ k[t, t⁻¹] / k[t]`;
* `TauCeti.Supports.test_support_not_restriction`: `H⁰_Z(𝔸¹, 𝒪) = 0` is not the ring `k` of
  functions on the origin;
* `TauCeti.Supports.test_depth_dvr`: for a discrete valuation ring `R` with fraction field `K`,
  `H⁰_m(R) = 0` and `H¹_m(R) ≅ K / R`, from the native colimit-of-`Ext` functors;
* `TauCeti.Supports.localCohomology_module_comparison_dvr`: the same two facts as `R`-modules,
  derived instead from the Noetherian comparison `H^q_m(R) ≅ H^q_{V(m)}(Spec R, 𝒪)`
  (`DiscreteValuationRingExample.nonempty_localCohomology_iso_cohomologyWithSupport`) and the
  geometric computation at the closed point of `Spec R`.

The remaining checks are proved where their ingredients live:
`TauCeti.Supports.NilIdealExample.localCohomology_module_comparison_nil_ideal` and
`TauCeti.Supports.depth_localCohomology_zero_guard`.
-/

public section

universe u

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Polynomial LaurentPolynomial
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace TauCeti.Supports

/-- With supports in the whole space, cohomology with supports is ordinary cohomology, linearly
over the global functions. -/
theorem test_support_all {X : Scheme.{u}} (M : X.Modules) (q : ℕ) :
    Nonempty (cohomologyWithSupport ⊤ M q ≃ₗ[Γ(X, ⊤)] Cohomology M q) :=
  ⟨cohomologyWithSupportTopLinearEquiv M q⟩

/-- With supports in the empty set, cohomology with supports vanishes in every degree. -/
theorem test_support_empty {X : Scheme.{u}} (M : X.Modules) (q : ℕ) :
    Subsingleton (cohomologyWithSupport ⊥ M q) :=
  inferInstance

section AffineLine

open AffineLineExample

variable (k : Type u) [Field k]

/-- On the affine line `𝔸¹_k = Spec k[t]` with supports at the origin `V(t)`, the structure sheaf
has `H⁰ = 0` and `H¹ ≅ k[t, t⁻¹] / k[t]` as `k[t]`-modules. -/
theorem test_support_affine_line_origin :
    Subsingleton (cohomologyWithSupport ((Spec (CommRingCat.of k[X])).basicOpen
        (coordinate k)).compl (SheafOfModules.unit (Spec (CommRingCat.of k[X])).ringCatSheaf) 0) ∧
      let 𝒪 : (Spec (CommRingCat.of k[X])).Modules := SheafOfModules.unit _
      Nonempty ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of k[X])).inv.hom).obj
          (ModuleCat.of Γ(Spec (CommRingCat.of k[X]), ⊤)
            (cohomologyWithSupport ((Spec (CommRingCat.of k[X])).basicOpen (coordinate k)).compl
              𝒪 1)) ≃ₗ[k[X]]
        k[T;T⁻¹] ⧸ LinearMap.range (Algebra.linearMap k[X] k[T;T⁻¹])) :=
  ⟨subsingleton_cohomologyWithSupport_origin_zero k,
    ⟨cohomologyWithSupportOriginOneLinearEquiv k⟩⟩

/-- `H⁰_Z(X, 𝒪)` is not the ring of functions on `Z`: the origin `Z` of the affine line is the
image of the closed immersion `Spec k ⟶ 𝔸¹_k`, whose ring of functions `k` is nonzero, while
`H⁰_Z(𝔸¹_k, 𝒪) = 0`. -/
theorem test_support_not_restriction :
    Set.range (origin k) =
        (((Spec (CommRingCat.of k[X])).basicOpen (coordinate k)).compl : Set _) ∧
      Nontrivial Γ(Spec (CommRingCat.of k), ⊤) ∧
      Subsingleton (cohomologyWithSupport ((Spec (CommRingCat.of k[X])).basicOpen
        (coordinate k)).compl (SheafOfModules.unit (Spec (CommRingCat.of k[X])).ringCatSheaf) 0) :=
  ⟨range_origin k,
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toEquiv.nontrivial,
    subsingleton_cohomologyWithSupport_origin_zero k⟩

end AffineLine

section DiscreteValuationRing

open DiscreteValuationRingExample

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Native local cohomology of a discrete valuation ring `R` with fraction field `K` at its
maximal ideal: `H⁰_m(R) = 0` and `H¹_m(R) ≅ K / R`. -/
theorem test_depth_dvr (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] :
    IsZero ((localCohomology (IsLocalRing.maximalIdeal R) 0).obj (ModuleCat.of R R)) ∧
      Nonempty ((localCohomology (IsLocalRing.maximalIdeal R) 1).obj (ModuleCat.of R R) ≃ₗ[R]
        K ⧸ LinearMap.range (Algebra.linearMap R K)) :=
  isZero_localCohomology_zero_and_nonempty_one_linearEquiv K

namespace DiscreteValuationRingExample

/-- The Noetherian comparison `H^q_m(R) ≅ H^q_{V(m)}(Spec R, 𝒪)` identifies the native local
cohomology of a discrete valuation ring `R` at its maximal ideal, `R`-linearly, with cohomology of
the structure sheaf of `Spec R` with supports at the closed point `V(ϖ)`, in every degree. -/
theorem nonempty_localCohomology_iso_cohomologyWithSupport {ϖ : R} (hϖ : Irreducible ϖ) (q : ℕ) :
    let 𝒪 : (Spec (CommRingCat.of R)).Modules := SheafOfModules.unit _
    Nonempty ((localCohomology (IsLocalRing.maximalIdeal R) q).obj (ModuleCat.of R R) ≅
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).obj
        (ModuleCat.of Γ(Spec (CommRingCat.of R), ⊤)
          (cohomologyWithSupport (uniformizerLocus ϖ) 𝒪 q))) := by
  intro 𝒪
  have hZ : zeroLocusCloseds (R := CommRingCat.of R) (IsLocalRing.maximalIdeal R) =
      uniformizerLocus ϖ :=
    Closeds.ext ((coe_zeroLocusCloseds _).trans (coe_uniformizerLocus hϖ).symm)
  rw [← hZ]
  -- `tilde R` is the structure sheaf by definition (Mathlib's `tildeSelf` is `Iso.refl`).
  exact ⟨localCohomologyIsoCohomologyWithSupport (R := CommRingCat.of R)
    (IsLocalRing.maximalIdeal R) q (ModuleCat.of R R)⟩

end DiscreteValuationRingExample

/-- **`localCohomology_module_comparison_dvr`**: the native Noetherian comparison
`H^q_m(R) ≅ H^q_{V(m)}(Spec R, 𝒪)` and the geometric computation at the closed point of `Spec R`
give `H⁰_m(R) = 0` and `H¹_m(R) ≅ K / R` as `R`-modules, for a discrete valuation ring `R` with
fraction field `K`. -/
theorem localCohomology_module_comparison_dvr (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] :
    IsZero ((localCohomology (IsLocalRing.maximalIdeal R) 0).obj (ModuleCat.of R R)) ∧
      Nonempty ((localCohomology (IsLocalRing.maximalIdeal R) 1).obj (ModuleCat.of R R) ≃ₗ[R]
        K ⧸ LinearMap.range (Algebra.linearMap R K)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨e₀⟩ := nonempty_localCohomology_iso_cohomologyWithSupport R hϖ 0
  obtain ⟨e₁⟩ := nonempty_localCohomology_iso_cohomologyWithSupport R hϖ 1
  have := hϖ.isLocalizationAway_fractionRing (K := K)
  have : Subsingleton ((localCohomology (IsLocalRing.maximalIdeal R) 0).obj (ModuleCat.of R R)) :=
    e₀.toLinearEquiv.toEquiv.subsingleton_congr.2
      (subsingleton_cohomologyWithSupport_zero hϖ.ne_zero)
  exact ⟨ModuleCat.isZero_of_subsingleton _,
    ⟨e₁.toLinearEquiv.trans (cohomologyWithSupportSpecOneLinearEquiv ϖ K)⟩⟩

end DiscreteValuationRing

end TauCeti.Supports
