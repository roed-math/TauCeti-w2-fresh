/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Lookahead.CmLatticeDictionary.Stubs
public import TauCeti.NumberTheory.ComplexMultiplication.ClassGroupAction

/-!
# The `j`-invariant classifies ideal classes and curves with complex multiplication

Let `K` be an imaginary quadratic field, oriented by a non-real embedding `σ : K →+* ℂ`, and let `O`
be an order of `K`. Two lattices have the same `j`-invariant exactly when they are homothetic
(`PeriodPair.weierstrassCurve_j_eq_iff`). Combined with the ideal-lattice dictionary of
`TauCeti.NumberTheory.ComplexMultiplication.LatticeClass`, this shows:

* two nonzero fractional ideals of `O` have the same class exactly when the curves `ℂ / σ(I)`
  have the same `j`-invariant (`NumberFieldOrder.jInvariant_eq_jInvariant_iff`), so the
  `j`-invariant of ideal classes is injective (`IdealClassMonoid.jInvariant_injective`);
* the `j`-invariant is a well-defined and injective function on the homothety classes of lattices
  with complex multiplication by `O` (`NumberFieldOrder.CMClass.jInvariant`,
  `NumberFieldOrder.CMClass.jInvariant_injective`);
* hence the classes of `Pic O` have pairwise distinct `j`-invariants
  (`NumberFieldOrder.injective_jInvariant_cmClassEquiv`).

## Main definitions

* `TauCeti.GlobalNumberFields.NumberFieldOrder.CMClass.jInvariant`: the `j`-invariant of a
  homothety class of lattices with complex multiplication by `O`.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.jInvariant_eq_jInvariant_iff`: equal `j`-invariants
  of ideals mean equal ideal classes.
* `TauCeti.GlobalNumberFields.IdealClassMonoid.jInvariant_injective`: the `j`-invariant of ideal
  classes is injective.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.CMClass.jInvariant_injective`: the `j`-invariant
  classifies lattices with complex multiplication by `O` up to homothety.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.injective_jInvariant_cmClassEquiv`: the classes of
  `Pic O` have pairwise distinct `j`-invariants.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, 2nd ed., Wiley, 2013, Theorem 10.9 and §11.A.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Graduate Texts in
  Mathematics 151, Springer, 1994, Proposition II.1.2.
-/

public noncomputable section

open NumberField

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K}

/-- **The `j`-invariant determines the ideal class.** Two nonzero fractional ideals of an order of
an imaginary quadratic field have the same `j`-invariant exactly when they have the same class. -/
theorem jInvariant_eq_jInvariant_iff (hK : Module.finrank ℚ K = 2) {σ : K →+* ℂ}
    (hσ : ¬ ComplexEmbedding.IsReal σ) {I J : O.nonzeroFractionalIdeals} :
    O.jInvariant hK hσ I = O.jInvariant hK hσ J ↔
      IdealClassMonoid.mk O I = IdealClassMonoid.mk O J := by
  obtain ⟨L, hL⟩ := exists_periodPair_lattice_eq hK hσ (nonZeroDivisors.ne_zero I.2)
  obtain ⟨L', hL'⟩ := exists_periodPair_lattice_eq hK hσ (nonZeroDivisors.ne_zero J.2)
  rw [jInvariant_eq hK hσ I hL, jInvariant_eq hK hσ J hL',
    mk_eq_mk_iff_exists_lattice_eq_smul hL hL', PeriodPair.weierstrassCurve_j_eq_iff]

/-- The `j`-invariant of a homothety class of lattices with complex multiplication by `O`: the
`j`-invariant of the curve `ℂ / Λ` of any lattice `Λ` in the class (`CMClass.jInvariant_mk`). -/
def CMClass.jInvariant {σ : K →+* ℂ} (x : CMClass O σ) : ℂ :=
  (Function.surjInv CMClass.mk_surjective x).1.weierstrassCurve.j

/-- The `j`-invariant of the class of `Λ` is the `j`-invariant of `ℂ / Λ`. -/
@[simp]
lemma CMClass.jInvariant_mk {σ : K →+* ℂ} (L : CMLattice O σ) :
    (CMClass.mk L).jInvariant = L.1.weierstrassCurve.j := by
  obtain ⟨c, hc⟩ := CMClass.mk_eq_mk_iff.mp (Function.surjInv_eq CMClass.mk_surjective
    (CMClass.mk L)).symm
  exact PeriodPair.weierstrassCurve_j_eq_of_lattice_eq_smul hc

/-- **The `j`-invariant classifies curves with complex multiplication by `O`.** Two lattices with
complex multiplication by `O` with the same `j`-invariant are homothetic. -/
theorem CMClass.jInvariant_injective {σ : K →+* ℂ} :
    Function.Injective (CMClass.jInvariant (O := O) (σ := σ)) := by
  intro x y h
  obtain ⟨L, rfl⟩ := CMClass.mk_surjective x
  obtain ⟨L', rfl⟩ := CMClass.mk_surjective y
  rw [CMClass.jInvariant_mk, CMClass.jInvariant_mk, PeriodPair.weierstrassCurve_j_eq_iff] at h
  exact CMClass.mk_eq_mk_iff.mpr h

/-- **The classes of `Pic O` have pairwise distinct `j`-invariants**: the `j`-invariant of the
curve `ℂ / σ(I)` determines the class of an invertible ideal `I`. -/
theorem injective_jInvariant_cmClassEquiv (hK : Module.finrank ℚ K = 2) {σ : K →+* ℂ}
    (hσ : ¬ ComplexEmbedding.IsReal σ) :
    Function.Injective fun a : Pic O ↦ (cmClassEquiv O σ hK hσ a).jInvariant :=
  CMClass.jInvariant_injective.comp (cmClassEquiv O σ hK hσ).injective

end NumberFieldOrder

namespace IdealClassMonoid

variable {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K}

/-- **The `j`-invariant of ideal classes is injective.** -/
theorem jInvariant_injective (hK : Module.finrank ℚ K = 2) {σ : K →+* ℂ}
    (hσ : ¬ ComplexEmbedding.IsReal σ) :
    Function.Injective (jInvariant (O := O) hK hσ) := by
  intro x y h
  obtain ⟨I, rfl⟩ := mk_surjective O x
  obtain ⟨J, rfl⟩ := mk_surjective O y
  rw [jInvariant_mk, jInvariant_mk] at h
  exact (NumberFieldOrder.jInvariant_eq_jInvariant_iff hK hσ).mp h

end IdealClassMonoid

end TauCeti.GlobalNumberFields
