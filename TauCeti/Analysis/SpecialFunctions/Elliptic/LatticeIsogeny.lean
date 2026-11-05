/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.AlgebraicIsogeny
public import TauCeti.Lookahead.CmLatticeDictionary.Stubs
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Kernel
import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsSepClosed

/-!
# Every isogeny between curves of lattices is a scalar map

This file proves the converse of `PeriodPair.scalarIsogeny`: every algebraic isogeny
`φ : E_Λ → E_{Λ'}` is the isogeny of a scalar map `z ↦ c z` with `c Λ ⊆ Λ'`
(`PeriodPair.exists_eq_scalarIsogeny`). Two inputs go into it.

* **Period-lattice recovery** (`PeriodPair.lattice_eq_of_weierstrassCurve_eq`): equal Weierstrass
  curves have equal lattices. The `j`-invariant determines the lattice up to a scalar `c`, and
  `E_{c Λ} = E_Λ` forces `g₂ = c⁻⁴ g₂` and `g₃ = c⁻⁶ g₃`. Unless `c = ±1`, one of `g₂`, `g₃`
  vanishes and `c` is a fourth or sixth root of unity with `c² + 1 = t c`, `t ∈ {0, ±1}`. Then
  `ℤ + ℤ c` is stable under `c`, has the same `j`-invariant as `Λ`, so `Λ` is a multiple of it and
  `c Λ = Λ` as well.
* **The lattice of a kernel**: the preimage `M` of `ker φ` in `ℂ` is a lattice containing `Λ`
  with finite index, the lattice of a period pair by `PeriodPair.exists_lattice_eq`. Vélu's isogeny
  `E_Λ → E_M` has the same kernel as `φ`, so `φ` is it followed by a change of variables
  `E_M ≅ E_{Λ'}`. Between short Weierstrass forms that is a scaling by some `u`, so
  `E_{Λ'} = E_{u M}`, and lattice recovery gives `Λ' = u M ⊇ u Λ`.

Consequently the multiplier ring of `Λ` acts on `E_Λ` through *all* of its algebraic
endomorphisms: `End(E_Λ)` is the multiplier ring `{α ∈ ℂ | α Λ ⊆ Λ}`
(`PeriodPair.multiplierCMAction_surjective`, `PeriodPair.multiplierRingEquivHom`).

## Main results

* `PeriodPair.lattice_eq_of_weierstrassCurve_eq`: period-lattice recovery.
* `PeriodPair.exists_eq_scalarIsogeny`: every isogeny `E_Λ → E_{Λ'}` is `scalarIsogeny c h`.
* `PeriodPair.nonempty_isogeny_iff`: `E_Λ` and `E_{Λ'}` are isogenous exactly when `c Λ ⊆ Λ'`
  for some `c ∈ ℂˣ`.
* `PeriodPair.multiplierCMAction_surjective`, `PeriodPair.multiplierRingEquivHom`: the
  endomorphism ring of `E_Λ` is the multiplier ring of `Λ`.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §VI.4 and §VI.5.
-/

public noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine TauCeti

namespace PeriodPair

/-! ### Period-lattice recovery -/

variable {L L' : PeriodPair}

/-- If `E_{c Λ} = E_Λ`, then `g₂ = c⁻⁴ g₂` and `g₃ = c⁻⁶ g₃`, that is `g₂ (c⁴ - 1) = 0` and
`g₃ (c⁶ - 1) = 0`. -/
private lemma g₂_g₃_of_weierstrassCurve_smul_eq {c : ℂˣ}
    (h : (c • L).weierstrassCurve = L.weierstrassCurve) :
    L.g₂ * ((c : ℂ) ^ 4 - 1) = 0 ∧ L.g₃ * ((c : ℂ) ^ 6 - 1) = 0 := by
  have h₄ := congrArg WeierstrassCurve.a₄ h
  have h₆ := congrArg WeierstrassCurve.a₆ h
  simp only [weierstrassCurve_a₄, weierstrassCurve_a₆, g₂_smul, g₃_smul] at h₄ h₆
  have hc := c.ne_zero
  field_simp at h₄ h₆
  exact ⟨by linear_combination h₄, by linear_combination h₆⟩

/-- If `g₂ (c⁴ - 1) = 0` and `g₃ (c⁶ - 1) = 0` with `c² ≠ 1`, the `j`-invariant is `1728` if
`c⁴ = 1` (then `g₃ = 0`) and `0` otherwise (then `g₂ = 0`). -/
private lemma weierstrassCurve_j_eq_of_g₂_g₃ {c : ℂ} (hc : c ^ 2 ≠ 1)
    (h₂ : L.g₂ * (c ^ 4 - 1) = 0) (h₃ : L.g₃ * (c ^ 6 - 1) = 0) :
    L.weierstrassCurve.j = if c ^ 4 = 1 then 1728 else 0 := by
  have hΔ := L.weierstrassCurve_Δ_ne_zero
  rw [weierstrassCurve_Δ] at hΔ
  rw [weierstrassCurve_j]
  split_ifs with h4
  · have h6 : c ^ 6 - 1 ≠ 0 := fun h6 ↦ hc (by linear_combination h6 - c ^ 2 * h4)
    rw [(mul_eq_zero.mp h₃).resolve_right h6] at hΔ ⊢
    field_simp
    ring
  · simp [(mul_eq_zero.mp h₂).resolve_right (sub_ne_zero.mpr h4)]

/-- A scalar `c ≠ ±1` with `E_{c Λ} = E_Λ` satisfies `c² + 1 = t c` with `t² ≤ 1`: it is a primitive
fourth, third or sixth root of unity. -/
private lemma exists_sq_add_one_eq_of_weierstrassCurve_smul_eq {c : ℂˣ}
    (h : (c • L).weierstrassCurve = L.weierstrassCurve) (hc : (c : ℂ) ^ 2 ≠ 1) :
    ∃ t : ℤ, t ^ 2 ≤ 1 ∧ (c : ℂ) ^ 2 + 1 = t * c := by
  obtain ⟨h₂, h₃⟩ := g₂_g₃_of_weierstrassCurve_smul_eq h
  have hΔ := L.weierstrassCurve_Δ_ne_zero
  rw [weierstrassCurve_Δ] at hΔ
  by_cases h4 : (c : ℂ) ^ 4 = 1
  · refine ⟨0, by norm_num, ?_⟩
    have : ((c : ℂ) ^ 2 - 1) * ((c : ℂ) ^ 2 + 1) = 0 := by linear_combination h4
    simpa using (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc)
  -- Otherwise `g₂ = 0`, so `g₃ ≠ 0` and `c⁶ = 1`.
  have hg₂ := (mul_eq_zero.mp h₂).resolve_right (sub_ne_zero.mpr h4)
  have h6 : (c : ℂ) ^ 6 - 1 = 0 :=
    (mul_eq_zero.mp h₃).resolve_left fun hg₃ ↦ hΔ (by rw [hg₂, hg₃]; ring)
  have : ((c : ℂ) ^ 2 - 1) * (((c : ℂ) ^ 2 + 1 - c) * ((c : ℂ) ^ 2 + 1 + c)) = 0 := by
    linear_combination h6
  rcases mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc)) with h | h
  · exact ⟨1, by norm_num, by push_cast; linear_combination h⟩
  · exact ⟨-1, by norm_num, by push_cast; linear_combination h⟩

/-- The lattice `ℤ + ℤ c` of a non-real `c` with `c² + 1 = t c`. -/
private def unitLattice (c : ℂ) {t : ℤ} (ht : t ^ 2 ≤ 1) (hct : c ^ 2 + 1 = t * c) :
    PeriodPair where
  ω₁ := 1
  ω₂ := c
  indep := by
    refine LinearIndependent.pair_iff.mpr fun s s' hs ↦ ?_
    have hre := congrArg Complex.re hs
    have him := congrArg Complex.im hs
    simp only [Complex.real_smul, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      Complex.zero_re, Complex.zero_im] at hre him
    have hcim : c.im ≠ 0 := by
      intro h0
      have hc : c = (c.re : ℂ) := Complex.ext rfl (by simpa using h0)
      rw [hc] at hct
      have hreal : c.re ^ 2 + 1 = t * c.re := by exact_mod_cast hct
      have ht' : (t : ℝ) ^ 2 ≤ 1 := by exact_mod_cast ht
      nlinarith [sq_nonneg (2 * c.re - t)]
    have hs' : s' = 0 := by
      simp only [mul_zero, zero_mul, zero_add, add_zero] at him
      exact (mul_eq_zero.mp him).resolve_right hcim
    subst hs'
    simpa using hre

/-- `ℤ + ℤ c` is stable under multiplication by `c` and by `c⁻¹ = t - c`. -/
private lemma unitLattice_mul_mem (c : ℂˣ) {t : ℤ} (ht : t ^ 2 ≤ 1)
    (hct : (c : ℂ) ^ 2 + 1 = t * c) :
    (∀ z ∈ (unitLattice c ht hct).lattice, (c : ℂ) * z ∈ (unitLattice c ht hct).lattice) ∧
      ∀ z ∈ (unitLattice c ht hct).lattice, (c : ℂ)⁻¹ * z ∈ (unitLattice c ht hct).lattice := by
  have hinv : (c : ℂ)⁻¹ = t - c :=
    (eq_inv_of_mul_eq_one_left (by linear_combination -hct : ((t : ℂ) - c) * c = 1)).symm
  refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩ <;>
  obtain ⟨m, n, rfl⟩ := mem_lattice.mp hz <;> refine mem_lattice.mpr ?_
  · exact ⟨-n, m + n * t, by simp only [unitLattice]; push_cast; linear_combination -n * hct⟩
  · refine ⟨t * m + n, -m, ?_⟩
    simp only [unitLattice, hinv]
    push_cast
    linear_combination n * hct

/-- **`E_{c Λ} = E_Λ` only if `c Λ = Λ`.** -/
private lemma lattice_smul_eq_of_weierstrassCurve_smul_eq {c : ℂˣ}
    (h : (c • L).weierstrassCurve = L.weierstrassCurve) : (c • L).lattice = L.lattice := by
  by_cases hc : (c : ℂ) ^ 2 = 1
  · have hc' : (c : ℂ) = 1 ∨ (c : ℂ) = -1 := sq_eq_one_iff.mp hc
    refine lattice_smul_eq_self (fun z hz ↦ ?_) (fun z hz ↦ ?_) <;>
      rcases hc' with hc' | hc' <;> simp [hc', hz]
  obtain ⟨t, ht, hct⟩ := exists_sq_add_one_eq_of_weierstrassCurve_smul_eq h hc
  set K := unitLattice c ht hct
  obtain ⟨hK₁, hK₂⟩ := unitLattice_mul_mem c ht hct
  obtain ⟨hL₂, hL₃⟩ := g₂_g₃_of_weierstrassCurve_smul_eq h
  obtain ⟨hK₂', hK₃'⟩ := g₂_g₃_of_weierstrassCurve_smul_eq
    (weierstrassCurve_eq_of_lattice_eq (lattice_smul_eq_self hK₁ hK₂))
  obtain ⟨e, he⟩ := weierstrassCurve_j_eq_iff.mp
    ((weierstrassCurve_j_eq_of_g₂_g₃ hc hK₂' hK₃').trans
      (weierstrassCurve_j_eq_of_g₂_g₃ hc hL₂ hL₃).symm)
  -- `Λ = e (ℤ + ℤ c)` is stable under `c` and `c⁻¹` because `ℤ + ℤ c` is.
  have hmem : ∀ d : ℂ, (∀ z ∈ K.lattice, d * z ∈ K.lattice) →
      ∀ z ∈ L.lattice, d * z ∈ L.lattice := by
    intro d hd z hz
    rw [he, mem_lattice_smul_iff] at hz ⊢
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨d * w, hd w hw, by ring⟩
  exact lattice_smul_eq_self (hmem _ hK₁) (hmem _ hK₂)

/-- **Period-lattice recovery**: lattices with the same Weierstrass curve, that is with the same
`g₂` and `g₃`, are equal. -/
theorem lattice_eq_of_weierstrassCurve_eq (h : L.weierstrassCurve = L'.weierstrassCurve) :
    L.lattice = L'.lattice := by
  obtain ⟨c, hc⟩ := (weierstrassCurve_j_eq_iff (L := L) (L' := L')).mp (by congr 1)
  rw [hc, lattice_smul_eq_of_weierstrassCurve_smul_eq
    ((weierstrassCurve_eq_of_lattice_eq hc).symm.trans h.symm)]

/-- Lattices are equal exactly when their Weierstrass curves are. -/
theorem weierstrassCurve_eq_iff : L.weierstrassCurve = L'.weierstrassCurve ↔
    L.lattice = L'.lattice :=
  ⟨lattice_eq_of_weierstrassCurve_eq, weierstrassCurve_eq_of_lattice_eq⟩

/-! ### The lattice of the kernel of an isogeny -/

section Kernel

variable (φ : Isogeny L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine)

/-- The preimage in `ℂ` of the kernel of an isogeny out of `E_Λ`. -/
private def kerLattice : Submodule ℤ ℂ :=
  (φ.ker.comap
    ((Point.equivBaseChangeSelf _).toAddMonoidHom.comp L.weierstrassPointHom)).toIntSubmodule

private lemma mem_kerLattice {z : ℂ} :
    z ∈ kerLattice φ ↔ Point.equivBaseChangeSelf _ (L.weierstrassPoint z) ∈ φ.ker := by
  rw [kerLattice, ← SetLike.mem_coe, AddSubgroup.coe_toIntSubmodule, SetLike.mem_coe,
    AddSubgroup.mem_comap, AddMonoidHom.comp_apply, weierstrassPointHom_apply,
    AddEquiv.coe_toAddMonoidHom]

private lemma lattice_le_kerLattice : L.lattice ≤ kerLattice φ := fun z hz ↦ by
  rw [mem_kerLattice, (weierstrassPoint_eq_zero_iff _).mpr hz, map_zero]
  exact zero_mem _

/-- The kernel of `φ` has `deg φ` points, so `deg φ` kills it: `M ⊆ (deg φ)⁻¹ Λ`. -/
private lemma degree_mul_mem_lattice {z : ℂ} (hz : z ∈ kerLattice φ) :
    (φ.degree : ℂ) * z ∈ L.lattice := by
  have h := congrArg Subtype.val (card_nsmul_eq_zero' (G := φ.ker) (x := ⟨_, hz⟩))
  rw [Isogeny.card_ker_eq_degree] at h
  simp only [AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero] at h
  rw [← map_nsmul] at h
  simpa only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, weierstrassPointHom_apply,
    EmbeddingLike.map_eq_zero_iff, weierstrassPoint_eq_zero_iff, nsmul_eq_mul] using h

/-- The preimage of the kernel of an isogeny out of `E_Λ` is a lattice `M ⊇ Λ` whose image in
`E_Λ(ℂ)` is the kernel. -/
private lemma exists_lattice_ker :
    ∃ (N : PeriodPair) (h : L.lattice ≤ N.lattice), (isogenyOfLE h).ker = φ.ker := by
  have hd : (φ.degree : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr φ.degree_ne_zero
  have hsub : (kerLattice φ : Set ℂ) ⊆ ((Units.mk0 _ hd)⁻¹ • L).lattice := fun z hz ↦
    (mem_lattice_smul_iff _ _).mpr ⟨_, degree_mul_mem_lattice φ hz, by simp [hd]⟩
  have : DiscreteTopology (kerLattice φ) := DiscreteTopology.of_subset
    (inferInstanceAs (DiscreteTopology ((Units.mk0 _ hd)⁻¹ • L).lattice)) hsub
  have : IsZLattice ℝ (kerLattice φ) := ⟨eq_top_iff.mpr <|
    (IsZLattice.span_top (K := ℝ) (L := L.lattice)).symm.le.trans
      (Submodule.span_mono (lattice_le_kerLattice φ))⟩
  obtain ⟨N, hN⟩ := exists_lattice_eq (kerLattice φ)
  refine ⟨N, hN ▸ lattice_le_kerLattice φ, ?_⟩
  ext Q
  rw [ker_isogenyOfLE, mem_latticePoints]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact (mem_kerLattice φ).mp (hN ▸ ht)
  · intro hQ
    obtain ⟨P, rfl⟩ := (Point.equivBaseChangeSelf _).surjective Q
    obtain ⟨z, rfl⟩ := L.weierstrassPoint_surjective P
    exact ⟨z, hN ▸ (mem_kerLattice φ).mpr hQ, rfl⟩

end Kernel

/-! ### Every isogeny is a scalar map -/

/-- **Every isogeny between curves of lattices is the isogeny of a scalar map**: for an isogeny
`φ : E_Λ → E_{Λ'}` there is `c ∈ ℂˣ` with `c Λ ⊆ Λ'` and `φ = scalarIsogeny c h`. The scalar is
the constant by which `φ` scales the invariant differential. -/
theorem exists_eq_scalarIsogeny
    (φ : Isogeny L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine) :
    ∃ (c : ℂˣ) (h : ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice), φ = scalarIsogeny c h := by
  classical
  obtain ⟨N, hle, hker⟩ := exists_lattice_ker φ
  obtain ⟨C, ⟨hC, hCφ⟩, -⟩ := Isogeny.existsUnique_variableChangeIsogeny_comp_eq_of_ker_eq
    (natCard_ker_isogenyOfLE hle) (Isogeny.card_ker_eq_degree φ) hker
  -- `C` is a change of variables between short Weierstrass forms, hence a scaling by `C.u`.
  -- `toAffine` is the identity on Weierstrass curves.
  have hC' : C • N.weierstrassCurve = L'.weierstrassCurve := hC
  have : N.weierstrassCurve.IsShortNF := ⟨by simp, by simp, by simp⟩
  have : (C • N.weierstrassCurve).IsShortNF := hC' ▸ ⟨by simp, by simp, by simp⟩
  have h2 : IsRegular (2 : ℂ) := .of_ne_zero two_ne_zero
  have h3 : IsRegular (3 : ℂ) := .of_ne_zero three_ne_zero
  have hCu : C = ⟨C.u, 0, 0, 0⟩ := by
    ext
    · rfl
    · exact C.r_eq_zero_of_isShortNF N.weierstrassCurve h2 h3
    · exact C.s_eq_zero_of_isShortNF N.weierstrassCurve h2
    · exact C.t_eq_zero_of_isShortNF N.weierstrassCurve h2
  have hlat : L'.lattice = (C.u • N).lattice :=
    lattice_eq_of_weierstrassCurve_eq (by rw [weierstrassCurve_smul, ← hCu, hC'])
  refine ⟨C.u, fun z hz ↦ hlat ▸ (mul_mem_lattice_smul_iff _ _).mpr (hle hz),
    (eq_scalarIsogeny_iff _ _).mpr ?_⟩
  rw [← hCφ, Isogeny.pullbackDifferential_comp, LinearMap.comp_apply,
    Isogeny.pullbackDifferential_variableChangeIsogeny_invariantDifferential, map_smul,
    pullbackDifferential_isogenyOfLE]

/-- **`E_Λ` and `E_{Λ'}` are isogenous exactly when a multiple `c Λ` lies in `Λ'`.** -/
theorem nonempty_isogeny_iff :
    Nonempty (Isogeny L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine) ↔
      ∃ c : ℂˣ, ∀ z ∈ L.lattice, (c : ℂ) * z ∈ L'.lattice :=
  ⟨fun ⟨φ⟩ ↦ (exists_eq_scalarIsogeny φ).imp fun _ ⟨h, _⟩ ↦ h,
    fun ⟨c, h⟩ ↦ ⟨scalarIsogeny c h⟩⟩

/-- **Every endomorphism of `E_Λ` comes from a multiplier of `Λ`.** -/
theorem multiplierCMAction_surjective : Function.Surjective L.multiplierCMAction := by
  intro f
  obtain rfl | ⟨φ, rfl⟩ := f.eq_zero_or_exists_ofIsogeny
  · exact ⟨0, map_zero _⟩
  obtain ⟨c, h, rfl⟩ := exists_eq_scalarIsogeny φ
  refine ⟨⟨c, mem_multiplierRing.mpr h⟩, ?_⟩
  rw [multiplierCMAction_apply_of_ne_zero _ c.ne_zero]
  congr 2
  exact Units.ext rfl

variable (L) in
/-- **The endomorphism ring of `E_Λ` is the multiplier ring of `Λ`**, a multiplier `α` acting by
the isogeny of `z ↦ α z`. -/
def multiplierRingEquivHom :
    L.multiplierRing ≃+* Isogeny.Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine :=
  RingEquiv.ofBijective L.multiplierCMAction.toRingHom
    (⟨L.multiplierCMAction.injective', multiplierCMAction_surjective⟩ : Function.Bijective _)

@[simp]
theorem multiplierRingEquivHom_apply (α : L.multiplierRing) :
    L.multiplierRingEquivHom α = L.multiplierCMAction α := by
  rw [multiplierRingEquivHom]
  exact RingEquiv.ofBijective_apply _ _ _

end PeriodPair
