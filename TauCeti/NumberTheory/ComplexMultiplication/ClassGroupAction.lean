/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ComplexMultiplication.LatticeClass
public import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.Basic

/-!
# The Picard group acts simply transitively on lattices with complex multiplication

Let `K` be an imaginary quadratic field, oriented by a non-real embedding `σ : K →+* ℂ`, and let `O`
be an order of `K`. A period lattice has complex multiplication by `O` (for `σ`) when its
multiplier ring is `σ(O)` (`NumberFieldOrder.CMLattice`); up to homothety these form the set
`NumberFieldOrder.CMClass O σ`, the set of isomorphism classes of complex elliptic curves with
complex multiplication by `O`.

In a quadratic order the proper fractional ideals are exactly the invertible ones
(`NumberFieldOrder.isProperFractionalIdeal_iff_isUnit_of_finrank_eq_two`). With the ideal-lattice
dictionary of `TauCeti.NumberTheory.ComplexMultiplication.LatticeClass`, this gives a bijection

  `NumberFieldOrder.cmClassEquiv : Pic O ≃ CMClass O σ`,   `[I] ↦ [σ(I)]`.

The Picard group therefore acts simply transitively on `CMClass O σ`. Following Silverman, the
class of an invertible ideal `𝔞` acts by `[σ(I)] ↦ [σ(𝔞⁻¹ I)]` (`NumberFieldOrder.picSMul`,
`NumberFieldOrder.picSMul_mk`), so that `Pic O` acts on the curves `E_I` by `𝔞 * E_I = E_{𝔞⁻¹ I}`.

## Main definitions

* `TauCeti.GlobalNumberFields.NumberFieldOrder.CMLattice`: period pairs with multiplier ring
  `σ(O)`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.CMClass`: their homothety classes.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.cmClassEquiv`: the bijection `Pic O ≃ CMClass O σ`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.picSMul`, `cmClassMulAction`: the action of the
  Picard group.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.cmClassEquiv_mkPic`: the class of `I` goes to the
  class of the lattice `σ(I)`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.picSMul_mk`: `[𝔞]` sends the class of `σ(I)` to the
  class of `σ(𝔞⁻¹ I)`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.exists_picSMul_eq`,
  `TauCeti.GlobalNumberFields.NumberFieldOrder.picSMul_eq_self_iff`: the action is transitive and
  free.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Graduate Texts in
  Mathematics 151, Springer, 1994, Proposition II.1.2.
* D. A. Cox, *Primes of the Form x² + ny²*, 2nd ed., Wiley, 2013, Theorem 10.19.
-/

public noncomputable section

open NumberField FractionalIdeal

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K]

variable (O : NumberFieldOrder K) (σ : K →+* ℂ)

/-- A period pair with **complex multiplication by `O`** for the orientation `σ`: its multiplier
ring is `σ(O)`. -/
abbrev CMLattice : Type := {L : PeriodPair // L.multiplierRing = O.toSubalgebra.toSubring.map σ}

/-- Homothety of lattices with complex multiplication by `O`. -/
def CMLattice.homothety : Setoid (CMLattice O σ) where
  r L L' := ∃ c : ℂˣ, L'.1.lattice = (c • L.1).lattice
  iseqv :=
    { refl L := ⟨1, by rw [one_smul]⟩
      symm := by
        rintro L L' ⟨c, hc⟩
        refine ⟨c⁻¹, ?_⟩
        rw [PeriodPair.lattice_smul _ c⁻¹, hc, ← PeriodPair.lattice_smul, smul_smul,
          inv_mul_cancel, one_smul]
      trans := by
        rintro L L' L'' ⟨c, hc⟩ ⟨d, hd⟩
        refine ⟨d * c, ?_⟩
        rw [hd, PeriodPair.lattice_smul _ d, hc, ← PeriodPair.lattice_smul, smul_smul] }

/-- The homothety classes of lattices with complex multiplication by `O`: the isomorphism classes
of complex elliptic curves `ℂ / Λ` whose endomorphism ring is `O`, acting through `σ`. -/
def CMClass : Type := Quotient (CMLattice.homothety O σ)

variable {O σ}

/-- The class of a lattice with complex multiplication by `O`. -/
def CMClass.mk (L : CMLattice O σ) : CMClass O σ :=
  Quotient.mk _ L

/-- Every class is the class of a lattice. -/
lemma CMClass.mk_surjective : Function.Surjective (CMClass.mk (O := O) (σ := σ)) :=
  Quotient.mk_surjective

/-- Two lattices with complex multiplication by `O` have the same class exactly when they are
homothetic. -/
lemma CMClass.mk_eq_mk_iff {L L' : CMLattice O σ} :
    CMClass.mk L = CMClass.mk L' ↔ ∃ c : ℂˣ, L'.1.lattice = (c • L.1).lattice :=
  Quotient.eq

/-- The lattice `σ(I)` of a proper fractional ideal, as a lattice with complex multiplication by
`O`. -/
def cmLatticeOfIsProper (hK : Module.finrank ℚ K = 2) (hσ : ¬ ComplexEmbedding.IsReal σ)
    {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} (hI : O.IsProperFractionalIdeal I) :
    CMLattice O σ :=
  ⟨(exists_periodPair_lattice_eq hK hσ hI.ne_zero).choose,
    multiplierRing_eq_map_of_isProper hI
      (exists_periodPair_lattice_eq hK hσ hI.ne_zero).choose_spec⟩

/-- The lattice of `cmLatticeOfIsProper` is `σ(I)`. -/
lemma coe_lattice_cmLatticeOfIsProper (hK : Module.finrank ℚ K = 2)
    (hσ : ¬ ComplexEmbedding.IsReal σ) {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K}
    (hI : O.IsProperFractionalIdeal I) :
    ((cmLatticeOfIsProper hK hσ hI).1.lattice : Set ℂ) = σ '' I :=
  (exists_periodPair_lattice_eq hK hσ hI.ne_zero).choose_spec

/-- A representative of a unit of the ideal class monoid. -/
private def unitRep (u : (IdealClassMonoid O)ˣ) : O.nonzeroFractionalIdeals :=
  Function.surjInv (IdealClassMonoid.mk_surjective O) u

/-- The class of the representative of `u` is `u`. -/
private lemma mk_unitRep (u : (IdealClassMonoid O)ˣ) : IdealClassMonoid.mk O (unitRep u) = u :=
  Function.surjInv_eq _ _

/-- The representative of a unit class is proper. -/
private lemma isProper_unitRep (u : (IdealClassMonoid O)ˣ) :
    O.IsProperFractionalIdeal (unitRep u : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :=
  O.isProperFractionalIdeal_of_isUnit
    ((IdealClassMonoid.isUnit_mk_iff O).mp ((mk_unitRep u).symm ▸ u.isUnit))

/-- The class of lattices with complex multiplication attached to a unit ideal class. -/
private def ofUnit (hK : Module.finrank ℚ K = 2) (hσ : ¬ ComplexEmbedding.IsReal σ)
    (u : (IdealClassMonoid O)ˣ) : CMClass O σ :=
  CMClass.mk (cmLatticeOfIsProper hK hσ (isProper_unitRep u))

/-- `ofUnit u` is the class of `σ(I)` for every representative `I` of `u`. -/
private lemma ofUnit_eq_mk (hK : Module.finrank ℚ K = 2) (hσ : ¬ ComplexEmbedding.IsReal σ)
    (u : (IdealClassMonoid O)ˣ) (I : O.nonzeroFractionalIdeals) (hI : IdealClassMonoid.mk O I = u)
    (L : CMLattice O σ)
    (hL : (L.1.lattice : Set ℂ) = σ '' (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)) :
    ofUnit hK hσ u = CMClass.mk L :=
  CMClass.mk_eq_mk_iff.mpr ((mk_eq_mk_iff_exists_lattice_eq_smul
    (coe_lattice_cmLatticeOfIsProper hK hσ (isProper_unitRep u)) hL).mp
      ((mk_unitRep u).trans hI.symm))

/-- Distinct unit classes give non-homothetic lattices. -/
private lemma ofUnit_injective (hK : Module.finrank ℚ K = 2) (hσ : ¬ ComplexEmbedding.IsReal σ) :
    Function.Injective (ofUnit (O := O) hK hσ) := by
  intro u v h
  have := (mk_eq_mk_iff_exists_lattice_eq_smul
    (coe_lattice_cmLatticeOfIsProper hK hσ (isProper_unitRep u))
    (coe_lattice_cmLatticeOfIsProper hK hσ (isProper_unitRep v))).mpr (CMClass.mk_eq_mk_iff.mp h)
  exact Units.ext ((mk_unitRep u).symm.trans (this.trans (mk_unitRep v)))

/-- Every lattice with complex multiplication by `O` is the lattice of a unit class. -/
private lemma ofUnit_surjective (hK : Module.finrank ℚ K = 2) (hσ : ¬ ComplexEmbedding.IsReal σ) :
    Function.Surjective (ofUnit (O := O) hK hσ) := by
  intro x
  obtain ⟨L, rfl⟩ := CMClass.mk_surjective x
  obtain ⟨I, hI, c, hc⟩ := exists_isProper_lattice_smul_eq hK hσ L.2
  set J : O.nonzeroFractionalIdeals := ⟨I, mem_nonZeroDivisors_of_ne_zero hI.ne_zero⟩
  have hJ : IsUnit (IdealClassMonoid.mk O J) :=
    (IdealClassMonoid.isUnit_mk_iff O).mpr (hI.isUnit_of_finrank_eq_two hK)
  refine ⟨hJ.unit, ?_⟩
  have hcL : (c • L.1).multiplierRing = O.toSubalgebra.toSubring.map σ := by
    rw [PeriodPair.multiplierRing_smul, L.2]
  rw [ofUnit_eq_mk hK hσ hJ.unit J hJ.unit_spec.symm ⟨c • L.1, hcL⟩ hc]
  exact (CMClass.mk_eq_mk_iff.mpr ⟨c, rfl⟩).symm

variable (O σ) in
/-- **Ideal classes and lattices with complex multiplication.** The bijection
`Pic O ≃ CMClass O σ` sending the class of an invertible ideal `I` to the class of the lattice
`σ(I)` (`cmClassEquiv_mkPic`). -/
def cmClassEquiv (hK : Module.finrank ℚ K = 2) (hσ : ¬ ComplexEmbedding.IsReal σ) :
    Pic O ≃ CMClass O σ :=
  (IdealClassMonoid.picEquivUnits O).toEquiv.trans
    (Equiv.ofBijective _ ⟨ofUnit_injective hK hσ, ofUnit_surjective hK hσ⟩)

/-- `cmClassEquiv` sends the Picard class of an invertible ideal `I` to the class of any lattice
`σ(I)`. -/
theorem cmClassEquiv_mkPic (hK : Module.finrank ℚ K = 2) (hσ : ¬ ComplexEmbedding.IsReal σ)
    (I : O.invertibleProperFractionalIdeals) (L : CMLattice O σ)
    (hL : (L.1.lattice : Set ℂ) = σ '' (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)) :
    cmClassEquiv O σ hK hσ (O.mkPic I) = CMClass.mk L := by
  change ofUnit hK hσ (IdealClassMonoid.picEquivUnits O (O.mkPic I)) = _
  rw [IdealClassMonoid.picEquivUnits_mkPic]
  exact ofUnit_eq_mk hK hσ _ _ (IdealClassMonoid.coe_unitsMk O I).symm L hL

/-! ### The action of the Picard group -/

/-- The action of the Picard group on lattices with complex multiplication by `O`: the class of
`𝔞` sends the class of `σ(I)` to the class of `σ(𝔞⁻¹ I)` (`picSMul_mk`). -/
def picSMul (hK : Module.finrank ℚ K = 2) (hσ : ¬ ComplexEmbedding.IsReal σ) (a : Pic O)
    (x : CMClass O σ) : CMClass O σ :=
  cmClassEquiv O σ hK hσ (a⁻¹ * (cmClassEquiv O σ hK hσ).symm x)

/-- Through `cmClassEquiv`, the class `a` acts by multiplication by `a⁻¹`. -/
lemma picSMul_cmClassEquiv (hK : Module.finrank ℚ K = 2) (hσ : ¬ ComplexEmbedding.IsReal σ)
    (a b : Pic O) :
    picSMul hK hσ a (cmClassEquiv O σ hK hσ b) = cmClassEquiv O σ hK hσ (a⁻¹ * b) := by
  rw [picSMul, Equiv.symm_apply_apply]

variable (O σ) in
/-- The Picard group acts on the classes of lattices with complex multiplication by `O`. -/
abbrev cmClassMulAction (hK : Module.finrank ℚ K = 2) (hσ : ¬ ComplexEmbedding.IsReal σ) :
    MulAction (Pic O) (CMClass O σ) where
  smul := picSMul hK hσ
  one_smul x := by
    change picSMul hK hσ 1 x = x
    rw [picSMul, inv_one, one_mul, Equiv.apply_symm_apply]
  mul_smul a b x := by
    change picSMul hK hσ (a * b) x = picSMul hK hσ a (picSMul hK hσ b x)
    rw [picSMul, picSMul, picSMul, Equiv.symm_apply_apply, mul_inv, mul_assoc]

/-- **The action of an ideal class on lattices.** The class of an invertible ideal `𝔞` sends the
class of the lattice `σ(I)` to the class of the lattice `σ(𝔞⁻¹ I)`. -/
theorem picSMul_mk (hK : Module.finrank ℚ K = 2) (hσ : ¬ ComplexEmbedding.IsReal σ)
    (𝔞 I : O.invertibleProperFractionalIdeals) (L L' : CMLattice O σ)
    (hL : (L.1.lattice : Set ℂ) = σ '' (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K))
    (hL' : (L'.1.lattice : Set ℂ) =
      σ '' ((𝔞⁻¹ * I : O.invertibleProperFractionalIdeals) :
        FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)) :
    picSMul hK hσ (O.mkPic 𝔞) (CMClass.mk L) = CMClass.mk L' := by
  rw [← cmClassEquiv_mkPic hK hσ I L hL, picSMul_cmClassEquiv, ← map_inv, ← map_mul,
    cmClassEquiv_mkPic hK hσ _ L' hL']

/-- The action of the Picard group is transitive. -/
theorem exists_picSMul_eq (hK : Module.finrank ℚ K = 2) (hσ : ¬ ComplexEmbedding.IsReal σ)
    (x y : CMClass O σ) : ∃ a : Pic O, picSMul hK hσ a x = y := by
  refine ⟨((cmClassEquiv O σ hK hσ).symm y)⁻¹ * (cmClassEquiv O σ hK hσ).symm x, ?_⟩
  rw [picSMul, mul_inv, inv_inv, mul_assoc, inv_mul_cancel, mul_one, Equiv.apply_symm_apply]

/-- The action of the Picard group is free. -/
theorem picSMul_eq_self_iff (hK : Module.finrank ℚ K = 2) (hσ : ¬ ComplexEmbedding.IsReal σ)
    (a : Pic O) (x : CMClass O σ) : picSMul hK hσ a x = x ↔ a = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, picSMul, inv_one, one_mul, Equiv.apply_symm_apply]⟩
  have h' := (Equiv.eq_symm_apply _).mpr h
  rwa [mul_eq_right, inv_eq_one] at h'

end NumberFieldOrder

end TauCeti.GlobalNumberFields
