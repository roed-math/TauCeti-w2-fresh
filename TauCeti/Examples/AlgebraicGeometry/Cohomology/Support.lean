/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.AlgebraicGeometry.Cohomology.Support.Affine
import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-!
# Cohomology with supports at the origin of the affine line

Let `k` be a field, `X = 𝔸¹_k = Spec k[t]` and `Z = V(t)` the origin. The complement of `Z` is the
basic open `D(t) = Spec k[t, t⁻¹]`, so the long exact sequence of the pair `(X, X ∖ Z)` and Serre's
vanishing theorem give

* `H_Z^0(X, 𝒪) = 0`, since `t` is a nonzerodivisor and no polynomial vanishes on `D(t)`;
* `H_Z^1(X, 𝒪) ≅ k[t, t⁻¹] / k[t]`;
* `H_Z^q(X, 𝒪) = 0` for `q ≥ 2`, since `X` and `D(t)` are affine.

In particular `H_Z^0(X, 𝒪)` is not the ring of functions on `Z`: the origin is the image of the
closed immersion `Spec k ⟶ X`, whose ring of functions is `k ≠ 0`.

## Main declarations

* `AffineLineExample.coordinate k`: the coordinate `t` as a global function on `Spec k[t]`;
* `AffineLineExample.subsingleton_cohomologyWithSupport_origin_zero`: `H_Z^0(X, 𝒪) = 0`;
* `AffineLineExample.cohomologyWithSupportOriginOneLinearEquiv`: `H_Z^1(X, 𝒪) ≅ k[t, t⁻¹] / k[t]`
  as `k[t]`-modules;
* `AffineLineExample.subsingleton_cohomologyWithSupport_origin_add_two`: `H_Z^{n+2}(X, 𝒪) = 0`;
* `AffineLineExample.origin k`: the closed immersion `Spec k ⟶ Spec k[t]` with image `Z`
  (`AffineLineExample.range_origin`);
* `AffineLineExample.isEmpty_cohomologyWithSupport_origin_zero_equiv`: `H_Z^0(X, 𝒪)` is not in
  bijection with the functions `k` on the origin.
-/

public section

open CategoryTheory AlgebraicGeometry Polynomial LaurentPolynomial

namespace TauCeti

namespace AlgebraicGeometry.Scheme.Modules.AffineLineExample

universe u

noncomputable section

variable (k : Type u) [Field k]

/-- The coordinate `t` of the affine line `Spec k[t]`, as a global function. Its zero locus is the
origin. -/
def coordinate : Γ(Spec (CommRingCat.of k[X]), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k[X])).inv X

/-- Global functions on the affine line are polynomials. -/
private def globalSectionsEquiv : Γ(Spec (CommRingCat.of k[X]), ⊤) ≃+* k[X] :=
  (Scheme.ΓSpecIso (CommRingCat.of k[X])).commRingCatIsoToRingEquiv

private lemma globalSectionsEquiv_coordinate : globalSectionsEquiv k (coordinate k) = X :=
  Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of k[X])) X

/-- The coordinate of the affine line is a nonzerodivisor. -/
lemma coordinate_mem_nonZeroDivisors :
    coordinate k ∈ nonZeroDivisors Γ(Spec (CommRingCat.of k[X]), ⊤) := by
  have := (globalSectionsEquiv k).toMulEquiv.isDomain k[X]
  refine mem_nonZeroDivisors_of_ne_zero fun h ↦ X_ne_zero (R := k) ?_
  rw [← globalSectionsEquiv_coordinate, h, map_zero]

/-- The structure sheaf of the affine line has no sections supported at the origin:
`H⁰_{V(t)}(𝔸¹, 𝒪) = 0`. -/
theorem subsingleton_cohomologyWithSupport_origin_zero :
    Subsingleton (cohomologyWithSupport ((Spec (CommRingCat.of k[X])).basicOpen
      (coordinate k)).compl (SheafOfModules.unit (Spec (CommRingCat.of k[X])).ringCatSheaf) 0) :=
  subsingleton_cohomologyWithSupport_basicOpen_zero _ (coordinate_mem_nonZeroDivisors k)

/-- Degree-one cohomology of the structure sheaf of the affine line with supports at the origin
is the `k[t]`-module of Laurent polynomials modulo polynomials:
`H¹_{V(t)}(𝔸¹, 𝒪) ≅ k[t, t⁻¹] / k[t]`, where `k[t]` acts through `k[t] ≅ Γ(𝔸¹, ⊤)`. -/
def cohomologyWithSupportOriginOneLinearEquiv :
    let 𝒪 : (Spec (CommRingCat.of k[X])).Modules := SheafOfModules.unit _
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of k[X])).inv.hom).obj
        (ModuleCat.of Γ(Spec (CommRingCat.of k[X]), ⊤)
          (cohomologyWithSupport ((Spec (CommRingCat.of k[X])).basicOpen (coordinate k)).compl
            𝒪 1)) ≃ₗ[k[X]]
      k[T;T⁻¹] ⧸ LinearMap.range (Algebra.linearMap k[X] k[T;T⁻¹]) :=
  cohomologyWithSupportSpecOneLinearEquiv X k[T;T⁻¹]

/-- The structure sheaf of the affine line has no cohomology with supports at the origin in
degrees at least two. -/
theorem subsingleton_cohomologyWithSupport_origin_add_two (n : ℕ) :
    Subsingleton (cohomologyWithSupport ((Spec (CommRingCat.of k[X])).basicOpen
      (coordinate k)).compl (SheafOfModules.unit (Spec (CommRingCat.of k[X])).ringCatSheaf)
        (n + 2)) :=
  subsingleton_cohomologyWithSupport_basicOpen_add_two _ _ n

/-- The origin of the affine line, as the closed point `Spec k ⟶ Spec k[t]` given by evaluation
at `0`. -/
def origin : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k[X]) :=
  Spec.map (CommRingCat.ofHom (evalRingHom 0))

instance : IsClosedImmersion (origin k) :=
  IsClosedImmersion.spec_of_surjective _ fun a ↦ ⟨Polynomial.C a, eval_C⟩

/-- The image of the origin is the zero locus `V(t)` of the coordinate. -/
theorem range_origin : Set.range (origin k) =
    (((Spec (CommRingCat.of k[X])).basicOpen (coordinate k)).compl : Set _) := by
  rw [coordinate, basicOpen_eq_of_affine]
  refine (range_comap_of_surjective _ _ fun a ↦ ⟨Polynomial.C a, eval_C⟩).trans ?_
  rw [CommRingCat.hom_ofHom, ker_evalRingHom, map_zero, sub_zero, PrimeSpectrum.zeroLocus_span]
  exact (compl_compl _).symm.trans
    (congrArg compl (PrimeSpectrum.basicOpen_eq_zeroLocus_compl X).symm)

/-- `H⁰_Z(X, 𝒪)` is not the ring of functions on `Z`: the origin `Z` is the image of the closed
immersion `Spec k ⟶ 𝔸¹`, whose ring of functions `k` is nonzero, while `H⁰_Z(𝔸¹, 𝒪) = 0`. -/
theorem isEmpty_cohomologyWithSupport_origin_zero_equiv :
    IsEmpty (cohomologyWithSupport ((Spec (CommRingCat.of k[X])).basicOpen
      (coordinate k)).compl (SheafOfModules.unit (Spec (CommRingCat.of k[X])).ringCatSheaf) 0 ≃
        Γ(Spec (CommRingCat.of k), ⊤)) := by
  have := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have := subsingleton_cohomologyWithSupport_origin_zero k
  exact ⟨fun e ↦ not_subsingleton _ e.symm.subsingleton⟩

end

end AlgebraicGeometry.Scheme.Modules.AffineLineExample

end TauCeti
