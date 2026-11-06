/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Cycles and homology of complexes of abelian groups, elementwise

For a homological complex `K` of abelian groups, this file describes the cycles and homology of
`K` on elements, as `TauCeti.Algebra.Homology.ModuleCat.Basic` does for complexes of modules:

* `HomologicalComplex.ab_iCycles_injective`: a cycle is determined by its underlying element.
* `HomologicalComplex.ab_iCycles_toCycles_apply`: the cycle `toCycles x` of an element `x` is the
  element `d x`.
* `HomologicalComplex.ab_exists_iCycles_eq`: an element killed by the differential comes from a
  cycle.
* `HomologicalComplex.ab_homologyπ_eq_zero_iff`: a cycle has zero homology class exactly when it
  is a boundary.
-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex AddCommGrpCat c)

/-- The inclusion of the degree-`n` cycles of a complex of abelian groups into its degree-`n` term
is injective. -/
lemma ab_iCycles_injective (n : ι) : Function.Injective (K.iCycles n) :=
  (AddCommGrpCat.mono_iff_injective _).1 inferInstance

/-- The underlying element of the cycle `K.toCycles i j x` of a complex of abelian groups is the
differential of `x`. -/
lemma ab_iCycles_toCycles_apply (i j : ι) (x : K.X i) :
    K.iCycles j (K.toCycles i j x) = K.d i j x :=
  ConcreteCategory.congr_hom (K.toCycles_i i j) x

/-- An element of the degree-`i` term of a complex of abelian groups that is killed by the
differential to the next degree `j` is the underlying element of a cycle. -/
lemma ab_exists_iCycles_eq {i : ι} (j : ι) (hij : c.next i = j) (x : K.X i)
    (hx : K.d i j x = 0) : ∃ z, K.iCycles i z = x :=
  have hS := (ShortComplex.mk (K.iCycles i) (K.d i j) (K.iCycles_d i j)).exact_of_f_is_kernel
    (K.cyclesIsKernel i j hij)
  (ShortComplex.ab_exact_iff _).1 hS x hx

/-- A degree-`n` cycle of a complex of abelian groups has zero homology class exactly when it is a
boundary, the image of an element of the term of degree `c.prev n`. -/
lemma ab_homologyπ_eq_zero_iff {m n : ι} (hm : c.prev n = m) (z : K.cycles n) :
    K.homologyπ n z = 0 ↔ ∃ y : K.X m, K.toCycles m n y = z := by
  refine ⟨(ShortComplex.ab_exact_iff _).1 (ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk (K.toCycles m n) (K.homologyπ n) (K.toCycles_comp_homologyπ m n))
    (K.homologyIsCokernel m n hm)) z, ?_⟩
  rintro ⟨y, rfl⟩
  exact ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ m n) y

end HomologicalComplex
