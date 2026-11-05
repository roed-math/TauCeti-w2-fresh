/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ComplexMultiplication.ClassGroupAction
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import TauCeti.RingTheory.FractionalIdeal.Index
import TauCeti.RingTheory.Ideal.Quotient.Artinian

/-!
# The isogeny attached to an invertible integral ideal

Let `σ : K →+* ℂ` be an embedding of a number field, `O` an order of `K`, `I` a proper fractional
ideal of `O` with lattice `σ(I)`, and `𝔞` an integral ideal of `O` that is invertible as a
fractional ideal, with inverse `𝔞⁻¹`. The `𝔞`-torsion of the curve `E_I = ℂ / σ(I)` is the
subgroup `E_I[𝔞]` of points killed by every element of `𝔞`
(`NumberFieldOrder.idealTorsion`).

Since `𝔞 ⊆ O`, the lattice `σ(I)` is contained in `σ(𝔞⁻¹ I)`, and the scalar `1` induces a
surjective homomorphism `E_I(ℂ) → E_{𝔞⁻¹ I}(ℂ)`, the `𝔞`-isogeny of the action of the Picard group
(`NumberFieldOrder.picSMul_mk` sends the class of `σ(I)` to that of `σ(𝔞⁻¹ I)`). Its kernel is
exactly `E_I[𝔞]` (`NumberFieldOrder.ker_scalarPointHom_one_eq_idealTorsion`), so `E_I[𝔞]` has
`[𝔞⁻¹ I : I]` points, the degree of the isogeny
(`NumberFieldOrder.natCard_idealTorsion_eq_relIndex`). For an order of an imaginary quadratic field
this index is the norm `[O : 𝔞]` of `𝔞` (`NumberFieldOrder.natCard_idealTorsion_eq_index`), by
`FractionalIdeal.relIndex_coeIdeal_mul_eq_index`.

Every class of `Pic O` contains an invertible integral ideal
(`NumberFieldOrder.exists_mkPic_eq_coeIdeal`), so the action of the Picard group on the classes of
lattices with complex multiplication by `O` is realized by these isogenies
(`NumberFieldOrder.exists_isogeny_picSMul`).

## Main definitions

* `TauCeti.GlobalNumberFields.NumberFieldOrder.idealTorsion`: the `𝔞`-torsion subgroup `E_I[𝔞]`.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.ker_scalarPointHom_one_eq_idealTorsion`: the kernel
  of `E_I → E_{𝔞⁻¹ I}` is `E_I[𝔞]`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.natCard_idealTorsion`,
  `TauCeti.GlobalNumberFields.NumberFieldOrder.natCard_idealTorsion_eq_relIndex`: `E_I[𝔞]` has
  `[σ(𝔞⁻¹ I) : σ(I)] = [𝔞⁻¹ I : I]` points.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.natCard_idealTorsion_eq_index`: in an imaginary
  quadratic order, `E_I[𝔞]` has `[O : 𝔞]` points, the norm of `𝔞`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.exists_isogeny_picSMul`: the class `a ∈ Pic O` acts
  on lattices with complex multiplication by an isogeny `E_L → E_{a · L}` with kernel `E_L[𝔞]`
  for an integral ideal `𝔞` in the class `a`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Graduate Texts in
  Mathematics 151, Springer, 1994, Propositions II.1.2 and II.1.4.
-/

public noncomputable section

open NumberField FractionalIdeal

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K} {σ : K →+* ℂ}
  {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} {L : PeriodPair}

/-- An element of `O` as an element of the subring `O.toSubalgebra.toSubring`. -/
private def toSubring (x : O.toSubalgebra) : O.toSubalgebra.toSubring :=
  ⟨x, x.2⟩

/-- **The `𝔞`-torsion** `E_I[𝔞]` of the curve of a proper fractional ideal `I`: the points killed
by every element of the integral ideal `𝔞`. -/
def idealTorsion (hI : O.IsProperFractionalIdeal I) (hL : (L.lattice : Set ℂ) = σ '' I)
    (𝔞 : Ideal O.toSubalgebra) : AddSubgroup L.weierstrassCurve.toAffine.Point :=
  ⨅ α ∈ 𝔞, AddMonoidHom.ker (orderEndRingHom hI hL (toSubring α))

/-- `P(z)` is `𝔞`-torsion exactly when `σ(α) z ∈ σ(I)` for every `α ∈ 𝔞`. -/
lemma weierstrassPoint_mem_idealTorsion_iff (hI : O.IsProperFractionalIdeal I)
    (hL : (L.lattice : Set ℂ) = σ '' I) (𝔞 : Ideal O.toSubalgebra) (z : ℂ) :
    L.weierstrassPoint z ∈ idealTorsion hI hL 𝔞 ↔ ∀ α ∈ 𝔞, σ α * z ∈ L.lattice := by
  simp only [idealTorsion, AddSubgroup.mem_iInf]
  refine forall₂_congr fun α _ ↦ ?_
  change orderEndRingHom hI hL (toSubring α) (L.weierstrassPoint z) = 0 ↔ _
  rw [orderEndRingHom_weierstrassPoint, PeriodPair.weierstrassPoint_eq_zero_iff]
  rfl

/-- If `𝔞` is an integral ideal with inverse `𝔟`, then `I ⊆ 𝔟 I`, so the lattice `σ(I)` is
contained in `σ(𝔟 I)`. -/
lemma mem_lattice_of_mul_eq_one {𝔞 : Ideal O.toSubalgebra}
    {𝔟 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K}
    (h𝔞𝔟 : (𝔞 : FractionalIdeal _ K) * 𝔟 = 1)
    (hL : (L.lattice : Set ℂ) = σ '' I) {L' : PeriodPair}
    (hL' : (L'.lattice : Set ℂ) = σ '' (𝔟 * I)) :
    ∀ z ∈ L.lattice, (1 : ℂ) * z ∈ L'.lattice := by
  have hle : I ≤ 𝔟 * I := by
    calc I = 1 * I := (one_mul I).symm
      _ = (𝔞 : FractionalIdeal _ K) * 𝔟 * I := by rw [h𝔞𝔟]
      _ ≤ 1 * 𝔟 * I := by gcongr; exact coeIdeal_le_one
      _ = 𝔟 * I := by rw [one_mul]
  intro z hz
  rw [one_mul, ← SetLike.mem_coe, hL']
  rw [← SetLike.mem_coe, hL] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨y, hle hy, rfl⟩

/-- **The kernel of the `𝔞`-isogeny.** If `𝔞` is an integral ideal with inverse `𝔟`, the
homomorphism `E_I(ℂ) → E_{𝔟 I}(ℂ)` induced by `σ(I) ⊆ σ(𝔟 I)` has kernel the `𝔞`-torsion
`E_I[𝔞]`. -/
theorem ker_scalarPointHom_one_eq_idealTorsion (hI : O.IsProperFractionalIdeal I)
    (hL : (L.lattice : Set ℂ) = σ '' I) {𝔞 : Ideal O.toSubalgebra}
    {𝔟 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K}
    (h𝔞𝔟 : (𝔞 : FractionalIdeal _ K) * 𝔟 = 1)
    {L' : PeriodPair} (hL' : (L'.lattice : Set ℂ) = σ '' (𝔟 * I)) :
    (PeriodPair.scalarPointHom 1 (mem_lattice_of_mul_eq_one h𝔞𝔟 hL hL')).ker =
      idealTorsion hI hL 𝔞 := by
  have hmem : ∀ {L : PeriodPair} {J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K},
      (L.lattice : Set ℂ) = σ '' J → ∀ z, z ∈ L.lattice ↔ ∃ y ∈ J, σ y = z := fun hJ z ↦ by
    rw [← SetLike.mem_coe, hJ]
    rfl
  ext P
  obtain ⟨z, rfl⟩ := L.weierstrassPoint_surjective P
  rw [PeriodPair.weierstrassPoint_mem_ker_scalarPointHom_iff,
    weierstrassPoint_mem_idealTorsion_iff, one_mul, hmem hL']
  constructor
  · rintro ⟨y, hy, rfl⟩ α hα
    refine (hmem hL _).mpr ⟨α * y, ?_, map_mul σ _ _⟩
    have := mul_mem_mul (mem_coeIdeal_of_mem (nonZeroDivisors O.toSubalgebra) hα) hy
    rwa [← mul_assoc, h𝔞𝔟, one_mul] at this
  · intro h
    have h𝔞 : 𝔞 ≠ ⊥ := by
      rintro rfl
      rw [coeIdeal_bot, zero_mul] at h𝔞𝔟
      exact zero_ne_one h𝔞𝔟
    obtain ⟨α₀, hα₀, hα₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
    have hα₀K : (α₀ : K) ≠ 0 := fun h0 ↦ hα₀ne (Subtype.ext h0)
    have hσα₀ : σ α₀ ≠ 0 := (map_ne_zero σ).mpr hα₀K
    obtain ⟨y₀, -, hy₀⟩ := (hmem hL _).mp (h α₀ hα₀)
    set x := y₀ / α₀
    have hx : σ x = z := by
      rw [map_div₀, hy₀, mul_div_cancel_left₀ _ hσα₀]
    have hxI : spanSingleton (nonZeroDivisors O.toSubalgebra) x * 𝔞 ≤ I := by
      refine (FractionalIdeal.mul_le).mpr fun u hu v hv ↦ ?_
      obtain ⟨r, rfl⟩ := (mem_spanSingleton _).mp hu
      obtain ⟨α, hα, rfl⟩ := (mem_coeIdeal _).mp hv
      obtain ⟨y, hy, e⟩ := (hmem hL _).mp (h α hα)
      have hy' : y = (α : K) * x := σ.injective (by rw [e, map_mul, hx])
      rw [smul_mul_assoc, mul_comm]
      exact Submodule.smul_mem _ r (show (α : K) * x ∈ I from hy' ▸ hy)
    refine ⟨x, ?_, hx⟩
    rw [← spanSingleton_le_iff_mem]
    calc spanSingleton (nonZeroDivisors O.toSubalgebra) x
        = spanSingleton _ x * ((𝔞 : FractionalIdeal _ K) * 𝔟) := by rw [h𝔞𝔟, mul_one]
      _ = 𝔟 * (spanSingleton _ x * (𝔞 : FractionalIdeal _ K)) := by ring
      _ ≤ 𝔟 * I := by gcongr

/-- **The degree of the `𝔞`-isogeny.** If `𝔞` is an integral ideal with inverse `𝔟`, the
`𝔞`-torsion `E_I[𝔞]` has `[σ(𝔟 I) : σ(I)]` points. -/
theorem natCard_idealTorsion (hI : O.IsProperFractionalIdeal I)
    (hL : (L.lattice : Set ℂ) = σ '' I) {𝔞 : Ideal O.toSubalgebra}
    {𝔟 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K}
    (h𝔞𝔟 : (𝔞 : FractionalIdeal _ K) * 𝔟 = 1)
    {L' : PeriodPair} (hL' : (L'.lattice : Set ℂ) = σ '' (𝔟 * I)) :
    Nat.card (idealTorsion hI hL 𝔞) =
      L.lattice.toAddSubgroup.relIndex L'.lattice.toAddSubgroup := by
  rw [← ker_scalarPointHom_one_eq_idealTorsion hI hL h𝔞𝔟 hL']
  have := PeriodPair.natCard_ker_scalarPointHom (L := L) (L' := L') 1
    (by simpa using mem_lattice_of_mul_eq_one h𝔞𝔟 hL hL')
  rwa [one_smul] at this

/-- **The degree of the `𝔞`-isogeny as an index of ideals.** If `𝔞` is an integral ideal with
inverse `𝔟`, the `𝔞`-torsion `E_I[𝔞]` has `[𝔟 I : I]` points. -/
theorem natCard_idealTorsion_eq_relIndex (hI : O.IsProperFractionalIdeal I)
    (hL : (L.lattice : Set ℂ) = σ '' I) {𝔞 : Ideal O.toSubalgebra}
    {𝔟 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K}
    (h𝔞𝔟 : (𝔞 : FractionalIdeal _ K) * 𝔟 = 1)
    {L' : PeriodPair} (hL' : (L'.lattice : Set ℂ) = σ '' (𝔟 * I)) :
    Nat.card (idealTorsion hI hL 𝔞) =
      (I : Submodule O.toSubalgebra K).toAddSubgroup.relIndex
        ((𝔟 * I : FractionalIdeal _ K) : Submodule O.toSubalgebra K).toAddSubgroup := by
  have hmap : ∀ {M : PeriodPair} {J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K},
      (M.lattice : Set ℂ) = σ '' J → M.lattice.toAddSubgroup =
        (J : Submodule O.toSubalgebra K).toAddSubgroup.map σ.toAddMonoidHom :=
    fun hJ ↦ SetLike.coe_injective (by rw [AddSubgroup.coe_map]; exact hJ)
  rw [natCard_idealTorsion hI hL h𝔞𝔟 hL', hmap hL, hmap hL',
    AddSubgroup.relIndex_map_map_of_injective _ _ σ.injective]

/-- **The degree of the `𝔞`-isogeny is the norm of `𝔞`.** If `𝔞` is an integral ideal with
inverse `𝔟` of an order of an imaginary quadratic field, the `𝔞`-torsion `E_I[𝔞]` of the curve of a
proper fractional ideal `I` has `[O : 𝔞]` points. -/
theorem natCard_idealTorsion_eq_index (hK : Module.finrank ℚ K = 2)
    (hI : O.IsProperFractionalIdeal I) (hL : (L.lattice : Set ℂ) = σ '' I)
    {𝔞 : Ideal O.toSubalgebra} {𝔟 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K}
    (h𝔞𝔟 : (𝔞 : FractionalIdeal _ K) * 𝔟 = 1)
    {L' : PeriodPair} (hL' : (L'.lattice : Set ℂ) = σ '' (𝔟 * I)) :
    Nat.card (idealTorsion hI hL 𝔞) = 𝔞.toAddSubgroup.index := by
  have h𝔞 : 𝔞 ≠ ⊥ := by
    rintro rfl
    rw [coeIdeal_bot, zero_mul] at h𝔞𝔟
    exact zero_ne_one h𝔞𝔟
  have : Finite (O.toSubalgebra ⧸ 𝔞) := Ideal.finiteQuotientOfFreeOfNeBot _ h𝔞
  -- `I = 𝔞 (𝔟 I)` with `𝔟 I` invertible.
  have h𝔟 : IsUnit 𝔟 := ⟨⟨𝔟, 𝔞, by rw [mul_comm, h𝔞𝔟], h𝔞𝔟⟩, rfl⟩
  have hJ : IsUnit (𝔟 * I) := h𝔟.mul (hI.isUnit_of_finrank_eq_two hK)
  have h𝔞J : (𝔞 : FractionalIdeal _ K) * (hJ.unit : FractionalIdeal _ K) = I := by
    rw [IsUnit.unit_spec, ← mul_assoc, h𝔞𝔟, one_mul]
  rw [natCard_idealTorsion_eq_relIndex hI hL h𝔞𝔟 hL',
    ← FractionalIdeal.relIndex_coeIdeal_mul_eq_index hJ.unit
      (Ideal.finite_setOfPred_isMaximal_and_le 𝔞), h𝔞J, IsUnit.unit_spec]

/-! ### The action of the Picard group by isogenies -/

/-- **The Picard group acts by isogenies.** Let `I` be a proper fractional ideal of an order `O` of
an imaginary quadratic field and `L` a lattice `σ(I)`. Every class `a ∈ Pic O` is the class of an
invertible integral ideal `𝔞`, and the lattice `σ(I)` is contained in a lattice `L'` in the class
`a · [L]`, so that the scalar `1` induces an isogeny `E_L → E_L'` whose kernel is the `𝔞`-torsion
`E_L[𝔞]`. -/
theorem exists_isogeny_picSMul (hK : Module.finrank ℚ K = 2) (hσ : ¬ ComplexEmbedding.IsReal σ)
    (a : Pic O) (hI : O.IsProperFractionalIdeal I) (L : CMLattice O σ)
    (hL : (L.1.lattice : Set ℂ) = σ '' I) :
    ∃ (𝔞 : Ideal O.toSubalgebra)
      (h𝔞 : IsUnit (𝔞 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)) (L' : CMLattice O σ)
      (h : ∀ z ∈ L.1.lattice, (1 : ℂ) * z ∈ L'.1.lattice),
      O.mkPic h𝔞.unit = a ∧ CMClass.mk L' = picSMul hK hσ a (CMClass.mk L) ∧
        (PeriodPair.scalarPointHom 1 h).ker = idealTorsion hI hL 𝔞 := by
  obtain ⟨u, 𝔞, hu, rfl⟩ := O.exists_mkPic_eq_coeIdeal a
  have h𝔞 : IsUnit (𝔞 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) := by
    rw [← hu]
    exact u.isUnit
  have hu' : h𝔞.unit = u := Units.ext (by rw [IsUnit.unit_spec, hu])
  set J := (hI.isUnit_of_finrank_eq_two hK).unit
  have hJ : (J : FractionalIdeal _ K) = I := IsUnit.unit_spec _
  set L' := cmLatticeOfIsProper hK hσ (O.invertible_isProper (u⁻¹ * J))
  have h𝔞𝔟 : (𝔞 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) *
      (u⁻¹ : O.invertibleProperFractionalIdeals).val = 1 := by
    rw [← hu, Units.mul_inv]
  have hL' : (L'.1.lattice : Set ℂ) =
      σ '' ((u⁻¹ : O.invertibleProperFractionalIdeals).val * I) := by
    rw [coe_lattice_cmLatticeOfIsProper, Units.val_mul, hJ]
  refine ⟨𝔞, h𝔞, L', mem_lattice_of_mul_eq_one h𝔞𝔟 hL hL', by rw [hu'], ?_,
    ker_scalarPointHom_one_eq_idealTorsion hI hL h𝔞𝔟 hL'⟩
  exact (picSMul_mk hK hσ u J L L' (by rw [hL, hJ])
    (coe_lattice_cmLatticeOfIsProper hK hσ _)).symm

end NumberFieldOrder

end TauCeti.GlobalNumberFields
