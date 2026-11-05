/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.AlgebraicIsogeny
public import TauCeti.NumberTheory.ComplexMultiplication.IdealIsogeny
public import TauCeti.NumberTheory.ComplexMultiplication.JInvariant
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ

/-!
# The algebraic curves with complex multiplication of an imaginary quadratic order

Let `O` be an order of an imaginary quadratic field `K`, oriented by a non-real embedding
`σ : K → ℂ`, and let `L` be a lattice `σ(I)` of a proper fractional ideal `I` of `O`. The analytic
dictionary of `TauCeti/NumberTheory/ComplexMultiplication/` is here read on the **algebraic**
Weierstrass curve `E_I = E_L` over `ℂ`, through the algebraic isogenies of scalar maps
(`PeriodPair.scalarIsogeny`).

* **Endomorphism order.** `O` acts faithfully on `E_I` by algebraic endomorphisms, `α` acting by
  the isogeny of `z ↦ σ(α) z`. This complex multiplication is normalised: `α` pulls the invariant
  differential back to `σ(α)` times itself.
* **Ideal isogenies.** For an invertible integral ideal `𝔞` with inverse `𝔟`, the inclusion
  `σ(I) ⊆ σ(𝔟 I)` is an algebraic isogeny `E_I → E_{𝔞⁻¹ I}` with kernel the `𝔞`-torsion `E_I[𝔞]`
  and degree the norm `[O : 𝔞]`. It induces the action of `Pic O` on curves with CM by `O`.
* **Classification.** `E_I` and `E_J` are isomorphic over `ℂ` exactly when `I` and `J` have the
  same ideal class. Both sides are equivalent to equality of `j`-invariants, by the `j`-invariant
  classification of ideal classes and over the algebraically closed field `ℂ`.

## Main definitions

* `TauCeti.GlobalNumberFields.NumberFieldOrder.cmAction`: the normalised action of `O` on `E_I` by
  algebraic endomorphisms.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.pullbackDifferential_cmAction`: `α` pulls `ω` back
  to `σ(α) ω`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.ker_scalarIsogeny_one_eq_idealTorsion` and
  `TauCeti.GlobalNumberFields.NumberFieldOrder.degree_scalarIsogeny_one_eq_index`: the isogeny of
  `𝔞` has kernel `E_I[𝔞]` and degree `[O : 𝔞]`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.exists_scalarIsogeny_picSMul`: the action of
  `Pic O` on curves with complex multiplication by `O` is realised by these algebraic isogenies.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.exists_variableChange_smul_eq_iff_mk_eq`: `E_I` and
  `E_J` are isomorphic over `ℂ` exactly when `[I] = [J]`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Graduate Texts in
  Mathematics 151, Springer, 1994, §II.1 and §II.4.
* D. A. Cox, *Primes of the Form x² + ny²*, 2nd ed., Wiley, 2013, §10 and §11.
-/

public noncomputable section

open NumberField WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K} {σ : K →+* ℂ}
  {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} {L : PeriodPair}

/-! ### The endomorphism order -/

/-- **`O` acts on `E_I` by algebraic endomorphisms**: for a proper fractional ideal `I` and a
lattice `L = σ(I)`, an element `α ∈ O` acts by the isogeny of the scalar map `z ↦ σ(α) z`, through
the identification of `O` with the multiplier ring of `L`. -/
def cmAction (hI : O.IsProperFractionalIdeal I) (hL : (L.lattice : Set ℂ) = σ '' I) :
    CMAction O.toSubalgebra.toSubring L.weierstrassCurve.toAffine where
  toRingHom := L.multiplierCMAction.toRingHom.comp (multiplierRingEquiv hI hL).toRingHom
  injective' := L.multiplierCMAction.injective.comp (multiplierRingEquiv hI hL).injective

lemma cmAction_apply (hI : O.IsProperFractionalIdeal I) (hL : (L.lattice : Set ℂ) = σ '' I)
    (x : O.toSubalgebra.toSubring) :
    cmAction hI hL x = L.multiplierCMAction (multiplierRingEquiv hI hL x) :=
  (rfl)

/-- **The complex multiplication of `O` on `E_I` is normalised**: `α ∈ O` pulls the invariant
differential back to `σ(α)` times itself. -/
theorem pullbackDifferential_cmAction (hI : O.IsProperFractionalIdeal I)
    (hL : (L.lattice : Set ℂ) = σ '' I) (x : O.toSubalgebra.toSubring) :
    (cmAction hI hL x).pullbackDifferential (invariantDifferential _) =
      σ x • invariantDifferential _ := by
  rw [cmAction_apply, PeriodPair.pullbackDifferential_multiplierCMAction,
    coe_multiplierRingEquiv]

/-! ### The isogeny of an invertible ideal -/

/-- **The kernel of the isogeny of `𝔞` is the `𝔞`-torsion**: for an invertible integral ideal `𝔞`
with inverse `𝔟`, the algebraic isogeny `E_I → E_{𝔟 I}` of the inclusion `σ(I) ⊆ σ(𝔟 I)` has kernel
`E_I[𝔞]`. -/
theorem ker_scalarIsogeny_one_eq_idealTorsion (hI : O.IsProperFractionalIdeal I)
    (hL : (L.lattice : Set ℂ) = σ '' I) {𝔞 : Ideal O.toSubalgebra}
    {𝔟 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K}
    (h𝔞𝔟 : (𝔞 : FractionalIdeal _ K) * 𝔟 = 1)
    {L' : PeriodPair} (hL' : (L'.lattice : Set ℂ) = σ '' (𝔟 * I)) :
    (PeriodPair.scalarIsogeny 1 (mem_lattice_of_mul_eq_one h𝔞𝔟 hL hL')).ker =
      (idealTorsion hI hL 𝔞).map (Point.equivBaseChangeSelf _).toAddMonoidHom := by
  rw [PeriodPair.ker_scalarIsogeny, ← ker_scalarPointHom_one_eq_idealTorsion hI hL h𝔞𝔟 hL']
  rfl

/-- **The degree of the isogeny of `𝔞` is the norm `[O : 𝔞]`.** -/
theorem degree_scalarIsogeny_one_eq_index (hK : Module.finrank ℚ K = 2)
    (hI : O.IsProperFractionalIdeal I) (hL : (L.lattice : Set ℂ) = σ '' I)
    {𝔞 : Ideal O.toSubalgebra} {𝔟 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K}
    (h𝔞𝔟 : (𝔞 : FractionalIdeal _ K) * 𝔟 = 1)
    {L' : PeriodPair} (hL' : (L'.lattice : Set ℂ) = σ '' (𝔟 * I)) :
    (PeriodPair.scalarIsogeny 1 (mem_lattice_of_mul_eq_one h𝔞𝔟 hL hL')).degree =
      𝔞.toAddSubgroup.index := by
  rw [PeriodPair.degree_scalarIsogeny, ← natCard_idealTorsion_eq_index hK hI hL h𝔞𝔟 hL',
    ← ker_scalarPointHom_one_eq_idealTorsion hI hL h𝔞𝔟 hL']
  rfl

/-- **The Picard group acts by algebraic isogenies.** For `L = σ(I)` with `I` proper and every
class `a ∈ Pic O`, there are an invertible integral ideal `𝔞` of class `a` and a lattice `L'` in the
class `a · [L]` containing `L`. The inclusion is an algebraic isogeny `E_L → E_L'` with kernel the
`𝔞`-torsion `E_L[𝔞]` and degree the norm `[O : 𝔞]`. -/
theorem exists_scalarIsogeny_picSMul (hK : Module.finrank ℚ K = 2)
    (hσ : ¬ ComplexEmbedding.IsReal σ) (a : Pic O) (hI : O.IsProperFractionalIdeal I)
    (L : CMLattice O σ) (hL : (L.1.lattice : Set ℂ) = σ '' I) :
    ∃ (𝔞 : Ideal O.toSubalgebra)
      (h𝔞 : IsUnit (𝔞 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)) (L' : CMLattice O σ)
      (h : ∀ z ∈ L.1.lattice, ((1 : ℂˣ) : ℂ) * z ∈ L'.1.lattice),
      O.mkPic h𝔞.unit = a ∧ CMClass.mk L' = picSMul hK hσ a (CMClass.mk L) ∧
        (PeriodPair.scalarIsogeny 1 h).ker =
          (idealTorsion hI hL 𝔞).map (Point.equivBaseChangeSelf _).toAddMonoidHom ∧
        (PeriodPair.scalarIsogeny 1 h).degree = 𝔞.toAddSubgroup.index := by
  obtain ⟨𝔞, h𝔞, L', h, ha, hL', hker⟩ := exists_isogeny_picSMul hK hσ a hI L hL
  refine ⟨𝔞, h𝔞, L', h, ha, hL', ?_, ?_⟩
  · rw [PeriodPair.ker_scalarIsogeny, ← hker]
    rfl
  · -- The norm is computed with the inverse `𝔟` of `𝔞` and a lattice `σ(𝔟 I)`.
    have h𝔞𝔟 : (𝔞 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) * ↑h𝔞.unit⁻¹ = 1 :=
      h𝔞.mul_val_inv
    have hne : (↑h𝔞.unit⁻¹ * I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) ≠ 0 :=
      fun h0 ↦ hI.ne_zero (by rw [← one_mul I, ← h𝔞𝔟, mul_assoc, h0, mul_zero])
    obtain ⟨L'', hL''⟩ := exists_periodPair_lattice_eq hK hσ hne
    exact (PeriodPair.degree_scalarIsogeny 1 h).trans
      ((congrArg (fun H : AddSubgroup L.1.weierstrassCurve.toAffine.Point ↦ Nat.card H) hker).trans
        (natCard_idealTorsion_eq_index hK hI hL h𝔞𝔟 hL''))

/-! ### The classification of the curves -/

/-- **Curves with complex multiplication are classified by ideal classes**: for nonzero fractional
ideals `I`, `J` with lattices `σ(I)`, `σ(J)`, the curves `E_I` and `E_J` are isomorphic over `ℂ`, by
a change of variables, exactly when `I` and `J` have the same ideal class. -/
theorem exists_variableChange_smul_eq_iff_mk_eq (hK : Module.finrank ℚ K = 2)
    (hσ : ¬ ComplexEmbedding.IsReal σ) {I J : O.nonzeroFractionalIdeals} {L L' : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K))
    (hL' : (L'.lattice : Set ℂ) = σ '' (J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)) :
    (∃ C : VariableChange ℂ, C • L.weierstrassCurve = L'.weierstrassCurve) ↔
      IdealClassMonoid.mk O I = IdealClassMonoid.mk O J := by
  rw [← jInvariant_eq_jInvariant_iff hK hσ, jInvariant_eq hK hσ I hL, jInvariant_eq hK hσ J hL']
  refine ⟨fun ⟨C, hC⟩ ↦ ?_, fun h ↦ exists_variableChange_of_j_eq _ _ h⟩
  convert (variableChange_j L.weierstrassCurve C).symm using 2
  exact hC.symm

end NumberFieldOrder

end TauCeti.GlobalNumberFields
