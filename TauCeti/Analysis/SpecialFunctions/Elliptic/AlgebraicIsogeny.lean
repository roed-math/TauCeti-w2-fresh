/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.VeluIsogeny
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.ComplexMultiplication
public import TauCeti.Analysis.SpecialFunctions.Elliptic.Endomorphism
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Separability

/-!
# Scalar maps between lattices are algebraic isogenies

A scalar map `z ↦ c z` with `c Λ ⊆ Λ'` induces the analytic homomorphism
`PeriodPair.scalarPointHom c h : E_Λ(ℂ) → E_{Λ'}(ℂ)`. This file constructs the corresponding
**algebraic isogeny** `PeriodPair.scalarIsogeny c h : E_Λ → E_{Λ'}`: the isogeny of the
superlattice `c⁻¹ Λ' ⊇ Λ` (`PeriodPair.isogenyOfLE`, Vélu's isogeny) followed by the change of
variables `E_{c⁻¹ Λ'} ≅ E_{Λ'}` of the rescaling by `c`. It compares with the analytic scalar map:

* its kernel is the kernel of `scalarPointHom c h` and its degree is `[Λ' : c Λ]`;
* it pulls the invariant differential `ω = dx / 2y`, which corresponds to `dz`, back to `c ω`.

In characteristic zero an isogeny is determined by the constant by which it scales `ω`
(`TauCeti.Isogeny.eq_of_pullbackDifferential_invariantDifferential_eq`). Hence `scalarIsogeny c h`
is the only isogeny scaling `ω` by `c`, and the algebraic isogenies of scalar maps compose as the
scalars multiply. The scalar `n` gives multiplication by `n`, and for `n = [Λ' : c Λ]` the
isogeny of `n / c` is dual to that of `c`: both composites are multiplication by `n`, the algebraic
form of `PeriodPair.scalarPointHom_comp_dual`.

## Main definitions

* `PeriodPair.scalarIsogeny`: the algebraic isogeny `E_Λ → E_{Λ'}` of a scalar map `c Λ ⊆ Λ'`.
* `PeriodPair.multiplierCMAction`: the faithful action of the multiplier ring of `Λ` on `E_Λ` by
  algebraic endomorphisms, `α` acting by `scalarIsogeny α`.

## Main results

* `PeriodPair.ker_scalarIsogeny`, `PeriodPair.degree_scalarIsogeny`,
  `PeriodPair.degree_scalarIsogeny_eq_relIndex`: its kernel is that of the analytic scalar map,
  and its degree is `[Λ' : c Λ]`.
* `PeriodPair.pullbackDifferential_scalarIsogeny`: it pulls `ω` back to `c ω`.
* `PeriodPair.eq_scalarIsogeny_iff`: it is the only isogeny `E_Λ → E_{Λ'}` doing so, and
  `PeriodPair.scalarIsogeny_inj`: distinct scalars give distinct isogenies.
* `PeriodPair.scalarIsogeny_comp`: composition corresponds to multiplication of scalars.
* `PeriodPair.scalarIsogeny_intCast`: the scalar `n` gives multiplication by `n`.
* `PeriodPair.scalarIsogeny_comp_dual`, `PeriodPair.scalarIsogeny_dual_comp`: the isogenies of `c`
  and of `[Λ' : c Λ] / c` compose to multiplication by `[Λ' : c Λ]` in both orders.
* `PeriodPair.dual_scalarIsogeny`: hence the dual isogeny of the isogeny of `c` is the isogeny of
  `[Λ' : c Λ] / c`.
* `PeriodPair.pullbackDifferential_multiplierCMAction`: the action of the multiplier ring is
  normalised, `α` scaling `ω` by `α`.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §III.5 and §VI.4.
-/

public noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine TauCeti

namespace PeriodPair

variable {L L' : PeriodPair}

/-! ### The algebraic isogeny of a scalar map -/

private lemma mem_lattice_inv_smul_iff {c : ℂˣ} {z : ℂ} :
    z ∈ (c⁻¹ • L').lattice ↔ (c : ℂ) * z ∈ L'.lattice := by
  have := mul_mem_lattice_smul_iff (L := L') (c := c⁻¹) (x := (c : ℂ) * z)
  rwa [Units.val_inv_eq_inv_val, inv_mul_cancel_left₀ c.ne_zero] at this

private lemma variableChange_weierstrassCurve_inv_smul (c : ℂˣ) :
    (⟨c, 0, 0, 0⟩ : VariableChange ℂ) • (c⁻¹ • L').weierstrassCurve.toAffine =
      L'.weierstrassCurve.toAffine := by
  rw [toAffine, ← weierstrassCurve_smul, smul_inv_smul]

/-- **The algebraic isogeny of a scalar map.** If `c Λ ⊆ Λ'`, this is the isogeny
`E_Λ → E_{c⁻¹ Λ'}` of the superlattice `c⁻¹ Λ' ⊇ Λ`, followed by the isomorphism
`E_{c⁻¹ Λ'} ≅ E_{Λ'}` of the change of variables `(x, y) ↦ (c⁻² x, c⁻³ y)`. -/
def scalarIsogeny (c : ℂˣ) (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice) :
    Isogeny L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine :=
  (Isogeny.variableChangeIsogeny _ (variableChange_weierstrassCurve_inv_smul c)).comp
    (isogenyOfLE (lattice_le_lattice_inv_smul c h))

private lemma ker_scalarIsogeny_eq (c : ℂˣ) (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice) :
    (scalarIsogeny c h).ker = (isogenyOfLE (lattice_le_lattice_inv_smul c h)).ker := by
  refine le_antisymm ?_ (Isogeny.ker_le_ker_comp _ _)
  have hinv := Isogeny.ker_le_ker_comp (Isogeny.variableChangeIsogeny _
    (show (⟨c, 0, 0, 0⟩ : VariableChange ℂ)⁻¹ • L'.weierstrassCurve.toAffine =
      (c⁻¹ • L').weierstrassCurve.toAffine by
        rw [← variableChange_weierstrassCurve_inv_smul c, inv_smul_smul])) (scalarIsogeny c h)
  rwa [scalarIsogeny, ← Isogeny.comp_assoc, Isogeny.variableChangeIsogeny_inv_comp,
    Isogeny.id_comp] at hinv

/-- **The kernel of the isogeny of a scalar map is the kernel of the scalar map**: for `c Λ ⊆ Λ'`,
the points of `E_Λ(ℂ)` killed by `scalarIsogeny c h` are those killed by `P_Λ(z) ↦ P_{Λ'}(c z)`. -/
theorem ker_scalarIsogeny (c : ℂˣ) (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice) :
    (scalarIsogeny c h).ker =
      (scalarPointHom (c : ℂ) h).ker.map (Point.equivBaseChangeSelf _).toAddMonoidHom := by
  rw [ker_scalarIsogeny_eq, ker_isogenyOfLE]
  ext Q
  simp only [mem_latticePoints, AddSubgroup.mem_map, AddEquiv.coe_toAddMonoidHom]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨_, (weierstrassPoint_mem_ker_scalarPointHom_iff h t).mpr
      (mem_lattice_inv_smul_iff.mp ht), rfl⟩
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨z, rfl⟩ := L.weierstrassPoint_surjective P
    exact ⟨z, mem_lattice_inv_smul_iff.mpr
      ((weierstrassPoint_mem_ker_scalarPointHom_iff h z).mp hP), rfl⟩

/-- **The isogeny of a scalar map `z ↦ c z` pulls the invariant differential back to `c` times
the invariant differential**, as `z ↦ c z` pulls `dz` back to `c dz`. -/
theorem pullbackDifferential_scalarIsogeny (c : ℂˣ)
    (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice) :
    (scalarIsogeny c h).pullbackDifferential (invariantDifferential _) =
      (c : ℂ) • invariantDifferential _ := by
  rw [scalarIsogeny, Isogeny.pullbackDifferential_comp, LinearMap.comp_apply,
    Isogeny.pullbackDifferential_variableChangeIsogeny_invariantDifferential, map_smul,
    pullbackDifferential_isogenyOfLE]

/-- **The degree of the isogeny of a scalar map is the order of the kernel of the scalar map.** -/
theorem degree_scalarIsogeny (c : ℂˣ) (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice) :
    (scalarIsogeny c h).degree = Nat.card (scalarPointHom (c : ℂ) h).ker := by
  rw [scalarIsogeny, Isogeny.degree_comp, Isogeny.degree_variableChangeIsogeny, one_mul,
    ← natCard_ker_isogenyOfLE,
    ← ker_scalarIsogeny_eq c h, ker_scalarIsogeny,
    AddSubgroup.card_map_of_injective (Point.equivBaseChangeSelf _).injective]

/-- **The isogeny of a scalar map `c Λ ⊆ Λ'` has degree `[Λ' : c Λ]`.** -/
theorem degree_scalarIsogeny_eq_relIndex (c : ℂˣ)
    (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice) :
    (scalarIsogeny c h).degree =
      (c • L).lattice.toAddSubgroup.relIndex L'.lattice.toAddSubgroup := by
  rw [degree_scalarIsogeny, natCard_ker_scalarPointHom]

/-! ### Scalar maps are algebraic isogenies -/

/-- **The isogeny of a scalar map is characterised by its differential**: an isogeny
`E_Λ → E_{Λ'}` is `scalarIsogeny c h` exactly when it pulls the invariant differential back to
`c` times the invariant differential. -/
theorem eq_scalarIsogeny_iff (c : ℂˣ) (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice)
    {ψ : Isogeny L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine} :
    ψ = scalarIsogeny c h ↔
      ψ.pullbackDifferential (invariantDifferential _) = (c : ℂ) • invariantDifferential _ := by
  refine ⟨fun hψ ↦ hψ ▸ pullbackDifferential_scalarIsogeny c h, fun hψ ↦ ?_⟩
  exact Isogeny.eq_of_pullbackDifferential_invariantDifferential_eq
    (hψ.trans (pullbackDifferential_scalarIsogeny c h).symm)

/-- **Distinct scalars give distinct isogenies.** -/
theorem scalarIsogeny_inj {c d : ℂˣ} (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice)
    (h' : ∀ z ∈ L.lattice, (d : ℂ) * z ∈ L'.lattice) :
    scalarIsogeny c h = scalarIsogeny d h' ↔ c = d := by
  refine ⟨fun e ↦ ?_, fun e ↦ by subst e; rfl⟩
  rw [eq_scalarIsogeny_iff, pullbackDifferential_scalarIsogeny] at e
  exact Units.ext (smul_left_injective ℂ (invariantDifferential_ne_zero _) e)

/-- **The isogenies of scalar maps compose as the scalars multiply.** -/
theorem scalarIsogeny_comp {L'' : PeriodPair} (c d : ℂˣ)
    (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice)
    (h' : ∀ z ∈ L'.lattice, (d : ℂ) * z ∈ L''.lattice) :
    (scalarIsogeny d h').comp (scalarIsogeny c h) =
      scalarIsogeny (d * c) fun z hz ↦ by simpa [mul_assoc] using h' _ (h z hz) := by
  rw [eq_scalarIsogeny_iff, Isogeny.pullbackDifferential_comp, LinearMap.comp_apply,
    pullbackDifferential_scalarIsogeny, map_smul, pullbackDifferential_scalarIsogeny, smul_smul,
    Units.val_mul, mul_comm]

/-- **The scalar map `z ↦ n z` is multiplication by `n`.** -/
theorem scalarIsogeny_intCast {n : ℤ} (hn : n ≠ 0) :
    scalarIsogeny (L := L) (Units.mk0 (n : ℂ) (Int.cast_ne_zero.mpr hn))
        (fun _ hz ↦ L.intCast_mul_mem_lattice n hz) =
      Isogeny.mulByIntIsogenyOfNeZero _ hn := by
  refine ((eq_scalarIsogeny_iff _ _).mpr ?_).symm
  rw [Units.val_mk0, Int.cast_smul_eq_zsmul]
  exact Isogeny.pullbackDifferential_mulByIntIsogeny_invariantDifferential _ _

/-- **The dual, on the source.** With `n = [Λ' : c Λ]`, the isogeny of the scalar map `n / c`
after the isogeny of `c` is multiplication by `n` on `E_Λ`. -/
theorem scalarIsogeny_comp_dual (c : ℂˣ) (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice) :
    (scalarIsogeny (Units.mk0 _ (relIndex_div_ne_zero c h))
        (mk0_relIndex_div_mul_mem_lattice c h)).comp (scalarIsogeny c h) =
      Isogeny.mulByIntIsogenyOfNeZero _
        (Int.natCast_ne_zero.mpr (relIndex_lattice_smul_ne_zero c h)) := by
  refine Isogeny.eq_of_pullbackDifferential_invariantDifferential_eq ?_
  rw [Isogeny.pullbackDifferential_comp, LinearMap.comp_apply, pullbackDifferential_scalarIsogeny,
    map_smul, pullbackDifferential_scalarIsogeny, smul_smul, Units.val_mk0,
    div_mul_cancel₀ _ c.ne_zero,
    Isogeny.pullbackDifferential_mulByIntIsogeny_invariantDifferential,
    ← Int.cast_smul_eq_zsmul ℂ, Int.cast_natCast]

/-- **The dual, on the target.** With `n = [Λ' : c Λ]`, the isogeny of `c` after the isogeny of
the scalar map `n / c` is multiplication by `n` on `E_{Λ'}`. -/
theorem scalarIsogeny_dual_comp (c : ℂˣ) (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice) :
    (scalarIsogeny c h).comp (scalarIsogeny (Units.mk0 _ (relIndex_div_ne_zero c h))
        (mk0_relIndex_div_mul_mem_lattice c h)) =
      Isogeny.mulByIntIsogenyOfNeZero _
        (Int.natCast_ne_zero.mpr (relIndex_lattice_smul_ne_zero c h)) := by
  refine Isogeny.eq_of_pullbackDifferential_invariantDifferential_eq ?_
  rw [Isogeny.pullbackDifferential_comp, LinearMap.comp_apply, pullbackDifferential_scalarIsogeny,
    map_smul, pullbackDifferential_scalarIsogeny, smul_smul, Units.val_mk0,
    mul_div_cancel₀ _ c.ne_zero,
    Isogeny.pullbackDifferential_mulByIntIsogeny_invariantDifferential,
    ← Int.cast_smul_eq_zsmul ℂ, Int.cast_natCast]

/-- **The dual of the isogeny of a scalar map is the isogeny of the dual scalar**: with
`n = [Λ' : c Λ]`, the dual isogeny of `scalarIsogeny c h` is the isogeny of `n / c`. -/
theorem dual_scalarIsogeny (c : ℂˣ) (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice) :
    (scalarIsogeny c h).dual =
      scalarIsogeny (Units.mk0 _ (relIndex_div_ne_zero c h))
        (mk0_relIndex_div_mul_mem_lattice c h) := by
  refine ((Isogeny.eq_dual_iff_comp_eq _).mpr ?_).symm
  rw [scalarIsogeny_comp_dual]
  simp only [degree_scalarIsogeny_eq_relIndex]

/-! ### The algebraic action of the multiplier ring -/

variable (L) in
/-- The algebraic endomorphism of `E_Λ` of a multiplier `α` of `Λ`: the isogeny of the scalar map
`z ↦ α z` for `α ≠ 0`, and `0` for `α = 0`. -/
private def multiplierHom (α : L.multiplierRing) :
    Isogeny.Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine :=
  if hα : (α : ℂ) = 0 then 0 else
    Isogeny.Hom.ofIsogeny (scalarIsogeny (Units.mk0 _ hα) fun _ hz ↦ by
      rw [Units.val_mk0]
      exact mem_multiplierRing.mp α.2 _ hz)

private lemma pullbackDifferential_multiplierHom (α : L.multiplierRing) :
    (multiplierHom L α).pullbackDifferential (invariantDifferential _) =
      (α : ℂ) • invariantDifferential _ := by
  rw [multiplierHom]
  split_ifs with hα
  · rw [Isogeny.Hom.pullbackDifferential_zero, LinearMap.zero_apply, hα, zero_smul]
  · rw [Isogeny.Hom.pullbackDifferential_ofIsogeny, pullbackDifferential_scalarIsogeny,
      Units.val_mk0]

variable (L) in
/-- **The multiplier ring of `Λ` acts on `E_Λ` by algebraic endomorphisms**: a multiplier `α ≠ 0`
acts by the isogeny of the scalar map `z ↦ α z`. The action is normalised: `α` pulls the invariant
differential back to `α` times itself (`PeriodPair.pullbackDifferential_multiplierCMAction`). -/
def multiplierCMAction : CMAction L.multiplierRing L.weierstrassCurve.toAffine where
  toRingHom :=
    { toFun := multiplierHom L
      map_one' := Isogeny.Hom.eq_of_pullbackDifferential_invariantDifferential_eq (by
        rw [pullbackDifferential_multiplierHom, Isogeny.Hom.one_def,
          Isogeny.Hom.pullbackDifferential_id, OneMemClass.coe_one, one_smul, LinearMap.id_apply])
      map_mul' α β := Isogeny.Hom.eq_of_pullbackDifferential_invariantDifferential_eq (by
        rw [pullbackDifferential_multiplierHom, Isogeny.Hom.mul_def,
          Isogeny.Hom.pullbackDifferential_comp, LinearMap.comp_apply,
          pullbackDifferential_multiplierHom, map_smul, pullbackDifferential_multiplierHom,
          smul_smul, MulMemClass.coe_mul, mul_comm])
      map_zero' := Isogeny.Hom.eq_of_pullbackDifferential_invariantDifferential_eq (by
        rw [pullbackDifferential_multiplierHom, ZeroMemClass.coe_zero, zero_smul,
          Isogeny.Hom.pullbackDifferential_zero, LinearMap.zero_apply])
      map_add' α β := Isogeny.Hom.eq_of_pullbackDifferential_invariantDifferential_eq (by
        rw [pullbackDifferential_multiplierHom,
          Isogeny.Hom.pullbackDifferential_add_invariantDifferential,
          pullbackDifferential_multiplierHom, pullbackDifferential_multiplierHom,
          AddMemClass.coe_add, add_smul]) }
  injective' α β hαβ := by
    have h := congrArg (fun f ↦ f.pullbackDifferential (invariantDifferential _)) hαβ
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      pullbackDifferential_multiplierHom] at h
    exact Subtype.ext (smul_left_injective ℂ (invariantDifferential_ne_zero _) h)

/-- **The action of the multiplier ring is normalised**: a multiplier `α` pulls the invariant
differential of `E_Λ` back to `α` times itself, as `z ↦ α z` pulls `dz` back to `α dz`. -/
theorem pullbackDifferential_multiplierCMAction (α : L.multiplierRing) :
    (L.multiplierCMAction α).pullbackDifferential (invariantDifferential _) =
      (α : ℂ) • invariantDifferential _ :=
  pullbackDifferential_multiplierHom α

/-- A nonzero multiplier `α` acts by the isogeny of the scalar map `z ↦ α z`. -/
theorem multiplierCMAction_apply_of_ne_zero (α : L.multiplierRing) (hα : (α : ℂ) ≠ 0) :
    L.multiplierCMAction α = Isogeny.Hom.ofIsogeny (scalarIsogeny (Units.mk0 _ hα) fun _ hz ↦ by
      rw [Units.val_mk0]
      exact mem_multiplierRing.mp α.2 _ hz) := by
  change multiplierHom L α = _
  simp only [multiplierHom, hα, ↓reduceDIte]

end PeriodPair
