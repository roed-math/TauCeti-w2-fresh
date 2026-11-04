/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Support.Affine
public import TauCeti.Examples.Algebra.Homology.LocalCohomology
public import TauCeti.RingTheory.DiscreteValuationRing.FractionRing
import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-!
# Cohomology with supports in the local cohomology examples

This file computes the geometric side, cohomology of the structure sheaf of `Spec A` with
supports in `V(I)`, in the two examples of `TauCeti.Examples.Algebra.Homology.LocalCohomology`.

* Let `R` be a discrete valuation ring with fraction field `K` and uniformizer `ϖ`. The closed
  point `V(m) = V(ϖ)` of `Spec R` has open complement `D(ϖ) = Spec K`, so
  `H⁰_{V(ϖ)}(Spec R, 𝒪) = 0`, `H¹_{V(ϖ)}(Spec R, 𝒪) ≅ K / R` and the higher groups vanish.
* Let `A = k[x₀, x₁, …]/(x_j^{j+2})` and `I = (x₀, x₁, …)`. Since `V(I) = Spec A`, every global
  function is supported in `V(I)`, so `H⁰_{V(I)}(Spec A, 𝒪) ≅ A ≠ 0`. The native colimit-of-`Ext`
  group `H⁰_I(A)` vanishes and `A` is not Noetherian, so without a Noetherian hypothesis the
  native local cohomology does not compute cohomology with supports.

## Main declarations

* `TauCeti.Supports.DiscreteValuationRingExample.coe_uniformizerLocus`: `V(ϖ)` is `V(m)`;
* `TauCeti.Supports.DiscreteValuationRingExample.subsingleton_cohomologyWithSupport_zero` and
  `TauCeti.Supports.DiscreteValuationRingExample.cohomologyWithSupportOneEquiv`:
  `H⁰_{V(ϖ)}(Spec R, 𝒪) = 0` and `H¹_{V(ϖ)}(Spec R, 𝒪) ≃+ K / R`, and
  `TauCeti.Supports.DiscreteValuationRingExample.subsingleton_cohomologyWithSupport_add_two`:
  `H^{n+2}_{V(ϖ)}(Spec R, 𝒪) = 0`;
* `TauCeti.Supports.NilIdealExample.cohomologyWithSupportZeroEquiv`:
  `H⁰_{V(I)}(Spec A, 𝒪) ≃+ A`;
* `TauCeti.Supports.NilIdealExample.localCohomology_module_comparison_nil_ideal`: the README check
  of that name.
-/

public section

universe u

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace TauCeti.Supports

noncomputable section

namespace DiscreteValuationRingExample

variable {R : Type u} [CommRing R]

/-- The zero locus `V(ϖ)` of an element `ϖ` of `R`, as a closed subset of `Spec R`: the complement
of the basic open `D(ϖ)`. For a uniformizer `ϖ` it is the closed point `V(m)`
(`coe_uniformizerLocus`). -/
abbrev uniformizerLocus (ϖ : R) : Closeds (Spec (CommRingCat.of R)) :=
  ((Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ)).compl

/-- The structure sheaf of `Spec R` has no cohomology with supports in `V(ϖ)`, the closed point for
a uniformizer `ϖ`, in degrees at least two. -/
theorem subsingleton_cohomologyWithSupport_add_two (ϖ : R) (n : ℕ) :
    Subsingleton (cohomologyWithSupport (uniformizerLocus ϖ)
      (SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) (n + 2)) :=
  subsingleton_cohomologyWithSupport_basicOpen_add_two _ _ n

/-- For a nonzero element `ϖ` of a domain `R`, the structure sheaf of `Spec R` has no sections
supported in `V(ϖ)`: `H⁰_{V(ϖ)}(Spec R, 𝒪) = 0`. For a uniformizer of a discrete valuation ring,
`V(ϖ)` is the closed point. -/
theorem subsingleton_cohomologyWithSupport_zero [IsDomain R] {ϖ : R} (hϖ : ϖ ≠ 0) :
    Subsingleton (cohomologyWithSupport (uniformizerLocus ϖ)
      (SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) 0) := by
  have := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain R
  refine subsingleton_cohomologyWithSupport_basicOpen_zero _
    (mem_nonZeroDivisors_of_ne_zero fun h ↦ hϖ ?_)
  rw [← Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) ϖ]
  exact h ▸ map_zero _

variable [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}

/-- The zero locus of a uniformizer is the zero locus `V(m)` of the maximal ideal. -/
theorem coe_uniformizerLocus (hϖ : Irreducible ϖ) :
    (uniformizerLocus ϖ : Set (Spec (CommRingCat.of R))) =
      PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R) := by
  rw [uniformizerLocus, basicOpen_eq_of_affine, hϖ.maximalIdeal_eq, PrimeSpectrum.zeroLocus_span]
  exact (congrArg compl (PrimeSpectrum.basicOpen_eq_zeroLocus_compl ϖ)).trans (compl_compl _)

/-- Degree-one cohomology of the structure sheaf of `Spec R` with supports at the closed point is
the fraction field modulo `R`: `H¹_{V(ϖ)}(Spec R, 𝒪) ≅ K / R`. -/
def cohomologyWithSupportOneEquiv (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (hϖ : Irreducible ϖ) :
    cohomologyWithSupport (uniformizerLocus ϖ)
        (SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) 1 ≃+
      K ⧸ (algebraMap R K).range.toAddSubgroup :=
  have := isLocalizationAway_fractionRing (K := K) hϖ
  cohomologyWithSupportSpecOneEquiv ϖ K

end DiscreteValuationRingExample

namespace NilIdealExample

variable (k : Type u) [CommRing k]

/-- The zero locus `V(I)` of `I = (x₀, x₁, …)`, as a closed subset of `Spec A`. -/
def idealZeroLocus : Closeds (Spec (CommRingCat.of (CoordRing k))) :=
  ⟨PrimeSpectrum.zeroLocus (ideal k : Set (CoordRing k)), PrimeSpectrum.isClosed_zeroLocus _⟩

/-- `V(I)` is all of `Spec A`. -/
theorem idealZeroLocus_eq_top : idealZeroLocus k = ⊤ :=
  Closeds.ext zeroLocus_ideal

/-- Every global function on `Spec A` is supported in `V(I) = Spec A`, so the degree-zero
cohomology of the structure sheaf with supports in `V(I)` is `A`. -/
def cohomologyWithSupportZeroEquiv :
    cohomologyWithSupport (idealZeroLocus k)
        (SheafOfModules.unit (Spec (CommRingCat.of (CoordRing k))).ringCatSheaf) 0 ≃+
      CoordRing k := by
  -- the `Γ(X, ⊤)`-module instances are found on `X.Modules`, not on `SheafOfModules.unit`
  let 𝒪 : (Spec (CommRingCat.of (CoordRing k))).Modules := SheafOfModules.unit _
  exact (cohomologyWithSupportZeroLinearEquivOfEqTop (idealZeroLocus_eq_top k) 𝒪).toAddEquiv.trans
    (Scheme.ΓSpecIso (CommRingCat.of (CoordRing k))).commRingCatIsoToRingEquiv.toAddEquiv

instance [Nontrivial k] : Nontrivial (cohomologyWithSupport (idealZeroLocus k)
    (SheafOfModules.unit (Spec (CommRingCat.of (CoordRing k))).ringCatSheaf) 0) :=
  (cohomologyWithSupportZeroEquiv k).toEquiv.nontrivial

/-- Native local cohomology does not compute cohomology with supports over a non-Noetherian ring:
for `A = k[x₀, x₁, …]/(x_j^{j+2})` and `I = (x₀, x₁, …)`, `V(I) = Spec A` and the geometric
`H⁰_{V(I)}(Spec A, 𝒪) ≅ A` is nonzero, while the native `H⁰_I(A)` vanishes and `A` is not
Noetherian. -/
theorem localCohomology_module_comparison_nil_ideal [Nontrivial k] :
    PrimeSpectrum.zeroLocus (ideal k : Set (CoordRing k)) = Set.univ ∧
      Nontrivial (cohomologyWithSupport (idealZeroLocus k)
        (SheafOfModules.unit (Spec (CommRingCat.of (CoordRing k))).ringCatSheaf) 0) ∧
      IsZero ((localCohomology (ideal k) 0).obj (ModuleCat.of (CoordRing k) (CoordRing k))) ∧
      ¬IsNoetherianRing (CoordRing k) :=
  ⟨zeroLocus_ideal, inferInstance, isZero_localCohomology_zero, not_isNoetherianRing⟩

end NilIdealExample

end

end TauCeti.Supports
