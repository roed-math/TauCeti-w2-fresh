/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
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

## Main declarations

* `AffineLineExample.coordinate k`: the coordinate `t` as a global function on `Spec k[t]`;
* `AffineLineExample.subsingleton_cohomologyWithSupport_origin_zero`: `H_Z^0(X, 𝒪) = 0`;
* `AffineLineExample.cohomologyWithSupportOriginOneEquiv`: `H_Z^1(X, 𝒪) ≃+ k[t, t⁻¹] / k[t]`;
* `AffineLineExample.subsingleton_cohomologyWithSupport_origin_add_two`: `H_Z^{n+2}(X, 𝒪) = 0`.
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

/-- The functions on `D(t)` are the Laurent polynomials, compatibly with the inclusion of
polynomials. -/
private def basicOpenRingEquiv :
    Γ(Spec (CommRingCat.of k[X]), (Spec (CommRingCat.of k[X])).basicOpen (coordinate k)) ≃+*
      k[T;T⁻¹] :=
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (coordinate k))
    (T := Submonoid.powers X) _ _ (globalSectionsEquiv k) (by
      rw [Submonoid.map_powers]
      exact congrArg _ (globalSectionsEquiv_coordinate k))

private lemma basicOpenRingEquiv_algebraMap (s : Γ(Spec (CommRingCat.of k[X]), ⊤)) :
    basicOpenRingEquiv k (algebraMap _ _ s) = toLaurent (globalSectionsEquiv k s) := by
  rw [basicOpenRingEquiv, IsLocalization.ringEquivOfRingEquiv_eq, algebraMap_eq_toLaurent]

/-- Degree-one cohomology of the structure sheaf of the affine line with supports at the origin
is the group of Laurent polynomials modulo polynomials:
`H¹_{V(t)}(𝔸¹, 𝒪) ≅ k[t, t⁻¹] / k[t]`. -/
def cohomologyWithSupportOriginOneEquiv :
    cohomologyWithSupport ((Spec (CommRingCat.of k[X])).basicOpen (coordinate k)).compl
        (SheafOfModules.unit (Spec (CommRingCat.of k[X])).ringCatSheaf) 1 ≃+
      k[T;T⁻¹] ⧸ (toLaurent : k[X] →+* k[T;T⁻¹]).range.toAddSubgroup :=
  (cohomologyWithSupportBasicOpenOneEquiv (coordinate k)).symm.trans
    (QuotientAddGroup.congr _ _ (basicOpenRingEquiv k).toAddEquiv (by
      ext y
      simp only [AddSubgroup.mem_map, Subring.mem_toAddSubgroup, RingHom.mem_range]
      constructor
      · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
        exact ⟨globalSectionsEquiv k s, (basicOpenRingEquiv_algebraMap k s).symm⟩
      · rintro ⟨p, rfl⟩
        refine ⟨_, ⟨(globalSectionsEquiv k).symm p, rfl⟩, ?_⟩
        exact (basicOpenRingEquiv_algebraMap k _).trans
          (congrArg _ (RingEquiv.apply_symm_apply _ p))))

/-- The structure sheaf of the affine line has no cohomology with supports at the origin in
degrees at least two. -/
theorem subsingleton_cohomologyWithSupport_origin_add_two (n : ℕ) :
    Subsingleton (cohomologyWithSupport ((Spec (CommRingCat.of k[X])).basicOpen
      (coordinate k)).compl (SheafOfModules.unit (Spec (CommRingCat.of k[X])).ringCatSheaf)
        (n + 2)) :=
  subsingleton_cohomologyWithSupport_basicOpen_add_two _ _ n

end

end AlgebraicGeometry.Scheme.Modules.AffineLineExample

end TauCeti
