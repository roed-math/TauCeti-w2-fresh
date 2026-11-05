/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.Superlattice
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Velu.Isogeny
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Differential
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange
import Mathlib.Order.Filter.FilterProduct
import TauCeti.Order.Filter.Germ

/-!
# Vélu's quotient of `E_Λ` by `Λ' / Λ` is `E_{Λ'}`

Let `Λ ⊆ Λ'` be period lattices. The image `Φ = P_Λ(Λ')` of `Λ'` in `E_Λ(ℂ)` is a finite subgroup,
and Vélu's coordinates of the quotient by `Φ` are, as functions of `z`,
`∑_{t ∈ Λ' / Λ} (℘_Λ(z + t) - ℘_Λ(t))` and `∑_t ℘'_Λ(z + t) / 2`: by the analytic Vélu formulas
(`PeriodPair.hasSum_weierstrassP_of_le`) these are `℘_{Λ'}(z)` and `℘'_{Λ'}(z) / 2`. Hence they
satisfy the Weierstrass equation of `E_{Λ'}`, and **the algebraic quotient curve
`veluCurve E_Λ Φ` is `E_{Λ'}`**. The Vélu isogeny is therefore an algebraic isogeny
`E_Λ → E_{Λ'}` of degree `[Λ' : Λ]` with kernel `Φ`.

To compare functions on `E_Λ` with functions of `z` without a field of meromorphic functions, the
function field of `E_Λ` is evaluated at the generic point `(℘_Λ, ℘'_Λ / 2)` into the field of
germs of functions along an ultrafilter finer than the punctured neighbourhoods of `0`. This
evaluation is injective because `℘_Λ` has a pole at `0`, so it takes no constant value near `0` and
is transcendental over `ℂ` as a germ.

## Main definitions

* `PeriodPair.latticePoints`: the image `P_Λ(Λ')` of a lattice `Λ'` in the points of `E_Λ`.
* `PeriodPair.isogenyOfLE`: for `Λ ⊆ Λ'`, the algebraic isogeny `E_Λ → E_{Λ'}`.

## Main results

* `PeriodPair.veluCurve_latticePoints`: Vélu's quotient of `E_Λ` by `P_Λ(Λ')` is `E_{Λ'}`.
* `PeriodPair.fieldPullback_isogenyOfLE_genericX`, `PeriodPair.fieldPullback_isogenyOfLE_genericY`:
  the isogeny `E_Λ → E_{Λ'}` pulls the coordinates back to Vélu's coordinates.
* `PeriodPair.degree_isogenyOfLE`, `PeriodPair.ker_isogenyOfLE`: it has degree `[Λ' : Λ]` and
  kernel `P_Λ(Λ')`.
* `PeriodPair.pullbackDifferential_isogenyOfLE`: it pulls the invariant differential of `E_{Λ'}`
  back to that of `E_Λ`, both being `dz`.

## References

* J. Vélu, *Isogénies entre courbes elliptiques*, C. R. Acad. Sci. Paris Sér. A–B 273 (1971).
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §VI.4.
-/

public noncomputable section

open Filter Topology WeierstrassCurve WeierstrassCurve.Affine TauCeti

namespace PeriodPair

/-! ### Germs at the punctured origin -/

/-- An ultrafilter finer than the punctured neighbourhoods of `0`, along which germs of functions
form a field. -/
private def germUltrafilter : Ultrafilter ℂ := Ultrafilter.of (𝓝[≠] (0 : ℂ))

private lemma germUltrafilter_le : (germUltrafilter : Filter ℂ) ≤ 𝓝[≠] 0 := Ultrafilter.of_le _

/-- The field of germs of functions `ℂ → ℂ` along `germUltrafilter`. -/
private abbrev Germs : Type := (germUltrafilter : Filter ℂ).Germ ℂ

private lemma algebraMap_germs (c : ℂ) : algebraMap ℂ Germs c = ↑(fun _ : ℂ ↦ c) :=
  Germ.algebraMap_eq c

private lemma germs_eventually_notMem_lattice (L : PeriodPair) :
    ∀ᶠ z in (germUltrafilter : Filter ℂ), z ∉ L.lattice :=
  germUltrafilter_le (L.eventually_notMem_lattice 0)

private lemma germs_eventually_add_notMem_lattice (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) :
    ∀ᶠ z in (germUltrafilter : Filter ℂ), z + t ∉ L.lattice := by
  have hc : ContinuousAt (fun z : ℂ ↦ z + t) 0 := by fun_prop
  have hcl : IsClosed (L.lattice : Set ℂ) := L.isClosed_lattice
  exact germUltrafilter_le.trans nhdsWithin_le_nhds
    (hc.preimage_mem_nhds (hcl.isOpen_compl.mem_nhds (by simpa using ht)))

private lemma germs_eventually_weierstrassP_ne (L : PeriodPair) (c : ℂ) :
    ∀ᶠ z in (germUltrafilter : Filter ℂ), ℘[L] z ≠ c :=
  germUltrafilter_le (L.eventually_weierstrassP_ne continuousAt_const)

/-- Polynomial identities that hold eventually hold between the germs. -/
private lemma equation_germs {W : WeierstrassCurve ℂ} {f g : ℂ → ℂ}
    (h : ∀ᶠ z in (germUltrafilter : Filter ℂ), W.toAffine.Equation (f z) (g z)) :
    (W.toAffine⁄Germs).Equation (f : Germs) (g : Germs) := by
  rw [Affine.equation_baseChange_iff]
  simp only [algebraMap_germs]
  exact Germ.coe_eq.mpr (h.mono fun z hz ↦ (Affine.equation_iff _ _).mp hz)

/-! ### Evaluation of the function field of `E_Λ` at `(℘_Λ, ℘'_Λ / 2)` -/

variable (L : PeriodPair)

private lemma equation_weierstrassP_germs :
    (L.weierstrassCurve⁄Germs).toAffine.Equation (℘[L] : Germs)
      ((fun z ↦ ℘'[L] z / 2 : ℂ → ℂ) : Germs) :=
  equation_germs ((germs_eventually_notMem_lattice L).mono fun _ hz ↦ L.equation_weierstrassP hz)

/-- `℘_Λ` is transcendental over `ℂ` as a germ at the punctured origin: it takes no constant value
near its pole `0`. -/
private lemma transcendental_weierstrassP_germs : Transcendental ℂ (℘[L] : Germs) := by
  rintro ⟨p, hp, h⟩
  rw [Germ.algebra_aeval_coe, ← Germ.coe_zero, Germ.coe_eq] at h
  have hroots : ∀ᶠ z in (germUltrafilter : Filter ℂ), ∀ r ∈ p.roots.toFinset, ℘[L] z ≠ r :=
    (Finset.eventually_all _).2 fun r _ ↦ germs_eventually_weierstrassP_ne L r
  obtain ⟨z, hz, hr⟩ := (h.and hroots).exists
  exact hr _ (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr
    (by simpa [Polynomial.coe_aeval_eq_eval] using hz))) rfl

/-- Evaluation of the coordinate ring of `E_Λ` at the generic point `(℘_Λ, ℘'_Λ / 2)`. -/
private def evalCoord : L.weierstrassCurve.toAffine.CoordinateRing →ₐ[ℂ] Germs :=
  CoordinateRing.evalAlgHom (equation_weierstrassP_germs L)

private lemma injective_evalCoord : Function.Injective (evalCoord L) :=
  CoordinateRing.algHom_injective _ (by
    simpa [evalCoord, CoordinateRing.evalAlgHom_mk] using transcendental_weierstrassP_germs L)

/-- Evaluation of the function field of `E_Λ` at the generic point `(℘_Λ, ℘'_Λ / 2)`. -/
private def evalFF : L.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ] Germs :=
  IsFractionRing.liftAlgHom (injective_evalCoord L)

private lemma evalFF_genericX : evalFF L (genericX _) = (℘[L] : Germs) := by
  rw [genericX_def, evalFF, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  simp [evalCoord]

private lemma evalFF_genericY :
    evalFF L (genericY _) = ((fun z ↦ ℘'[L] z / 2 : ℂ → ℂ) : Germs) := by
  rw [genericY_def, evalFF, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  simp [evalCoord]

private lemma evalFF_algebraMap (c : ℂ) :
    evalFF L (algebraMap ℂ L.weierstrassCurve.toAffine.FunctionField c) = ↑(fun _ : ℂ ↦ c) := by
  rw [AlgHom.commutes, algebraMap_germs]

/-- **Translation by `P_Λ(t)` evaluates to translation by `t`**: under the evaluation at
`(℘_Λ, ℘'_Λ / 2)`, the translates of the coordinates by the point `P_Λ(t)` become the germs of
`℘_Λ(z + t)` and `℘'_Λ(z + t) / 2`, by the addition theorems. -/
private lemma evalFF_translation (t : ℂ) :
    evalFF L (translation _ (Point.equivBaseChangeSelf _ (L.weierstrassPoint t)) (genericX _)) =
        ↑(fun z ↦ ℘[L] (z + t)) ∧
      evalFF L (translation _ (Point.equivBaseChangeSelf _ (L.weierstrassPoint t)) (genericY _)) =
        ↑(fun z ↦ ℘'[L] (z + t) / 2) := by
  classical
  by_cases ht : t ∈ L.lattice
  · rw [L.weierstrassPoint_of_mem ht, map_zero, translation_zero, AlgEquiv.one_apply,
      AlgEquiv.one_apply, evalFF_genericX, evalFF_genericY]
    exact ⟨congrArg _ (funext fun z ↦ (L.weierstrassP_add_coe z ⟨t, ht⟩).symm),
      congrArg _ (funext fun z ↦ by rw [L.derivWeierstrassP_add_coe z ⟨t, ht⟩])⟩
  set K := L.weierstrassCurve.toAffine.FunctionField
  set ψ : K →+* Germs := (evalFF L : K →+* Germs)
  have hψ (a : K) : ψ a = evalFF L a := rfl
  have hW : (L.weierstrassCurve.toAffine⁄K).map ψ = L.weierstrassCurve.toAffine⁄Germs :=
    Affine.map_baseChange _ (evalFF L)
  have hne : ∀ᶠ z in (germUltrafilter : Filter ℂ), ℘[L] z ≠ ℘[L] t :=
    germs_eventually_weierstrassP_ne L _
  have hne' : (℘[L] : Germs) ≠ ↑(fun _ : ℂ ↦ ℘[L] t) := fun h ↦ by
    obtain ⟨z, h₁, h₂⟩ := ((Germ.coe_eq.mp h).and hne).exists
    exact h₂ h₁
  rw [L.weierstrassPoint_of_notMem ht, Point.equivBaseChangeSelf_some,
    translation_apply_genericX_some, translation_apply_genericY_some, ← hψ, ← hψ,
    ← Affine.map_addX, ← Affine.map_addY, ← Affine.map_slope, hW]
  simp only [hψ, evalFF_genericX, evalFF_genericY, evalFF_algebraMap]
  rw [Affine.slope_of_X_ne hne']
  simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, Affine.baseChange,
    WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃,
    map_zero]
  simp only [zero_mul, add_zero, sub_zero, ← Germ.coe_sub, ← Germ.coe_div, ← Germ.coe_pow,
    ← Germ.coe_neg, ← Germ.coe_mul, ← Germ.coe_add]
  have hev := hne.and (germs_eventually_notMem_lattice L)
  refine ⟨Germ.coe_eq.mpr (hev.mono fun z hz ↦ ?_), Germ.coe_eq.mpr (hev.mono fun z hz ↦ ?_)⟩
  · simp only [Pi.sub_apply, Pi.div_apply, Pi.pow_apply]
    rw [L.weierstrassP_add hz.2 ht hz.1]
    ring
  · simp only [Pi.sub_apply, Pi.div_apply, Pi.pow_apply, Pi.neg_apply, Pi.mul_apply,
      Pi.add_apply]
    rw [L.derivWeierstrassP_add hz.2 ht hz.1, L.weierstrassP_add hz.2 ht hz.1]
    ring

/-! ### The points of `Λ'` on `E_Λ` -/

/-- The `x`-coordinate of `P_Λ(z)` is `℘_Λ(z)`, both sides being `0` on `Λ`. -/
lemma xCoord_weierstrassPoint (z : ℂ) : Point.xCoord (L.weierstrassPoint z) = ℘[L] z := by
  by_cases hz : z ∈ L.lattice
  · rw [L.weierstrassPoint_of_mem hz, Point.xCoord_zero, L.weierstrassP_coe ⟨z, hz⟩]
  · rw [L.weierstrassPoint_of_notMem hz, Point.xCoord_some]

/-- The `y`-coordinate of `P_Λ(z)` is `℘'_Λ(z) / 2`, both sides being `0` on `Λ`. -/
lemma yCoord_weierstrassPoint (z : ℂ) : Point.yCoord (L.weierstrassPoint z) = ℘'[L] z / 2 := by
  by_cases hz : z ∈ L.lattice
  · rw [L.weierstrassPoint_of_mem hz, Point.yCoord_zero, L.derivWeierstrassP_coe ⟨z, hz⟩,
      zero_div]
  · rw [L.weierstrassPoint_of_notMem hz, Point.yCoord_some]

variable (L' : PeriodPair)

/-- The image `P_Λ(Λ')` of a lattice `Λ'` in the points of `E_Λ`, read on the base change of
`E_Λ` along the identity, where Vélu's construction takes its subgroups. For `Λ ⊆ Λ'` it is the
finite group `Λ' / Λ`. -/
def latticePoints : AddSubgroup (L.weierstrassCurve.toAffine⁄ℂ).toAffine.Point :=
  (L'.lattice.toAddSubgroup.map L.weierstrassPointHom).map
    (Point.equivBaseChangeSelf L.weierstrassCurve.toAffine).toAddMonoidHom

variable {L L'}

/-- The points of `P_Λ(Λ')` are the images of the points of `Λ'`. -/
lemma mem_latticePoints {Q : (L.weierstrassCurve.toAffine⁄ℂ).toAffine.Point} :
    Q ∈ L.latticePoints L' ↔
      ∃ t ∈ L'.lattice, Point.equivBaseChangeSelf _ (L.weierstrassPoint t) = Q := by
  simp [latticePoints, weierstrassPointHom_apply]

/-- For `Λ ⊆ Λ'`, the classes of `Λ' / Λ` enumerate `P_Λ(Λ')` through `t ↦ P_Λ(-t)`. -/
private def quotientToLatticePoints :
    (L'.lattice.toAddSubgroup ⧸ L.lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup) →
      L.latticePoints L' :=
  fun c ↦ ⟨Point.equivBaseChangeSelf _ (L.weierstrassPoint (-c.out)),
    mem_latticePoints.mpr ⟨_, neg_mem c.out.2, rfl⟩⟩

private lemma bijective_quotientToLatticePoints :
    Function.Bijective (quotientToLatticePoints (L := L) (L' := L')) := by
  constructor
  · intro c d hcd
    have hcd' : L.weierstrassPoint (-(c.out : ℂ)) = L.weierstrassPoint (-(d.out : ℂ)) :=
      (Point.equivBaseChangeSelf _).injective (congrArg Subtype.val hcd)
    rw [← sub_eq_zero, ← weierstrassPointHom_apply, ← weierstrassPointHom_apply, ← map_sub,
      ← AddMonoidHom.mem_ker, ker_weierstrassPointHom, Submodule.mem_toAddSubgroup] at hcd'
    rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' d, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using hcd'
  · rintro ⟨Q, hQ⟩
    obtain ⟨t, ht, rfl⟩ := mem_latticePoints.mp hQ
    refine ⟨-(QuotientAddGroup.mk (⟨t, ht⟩ : L'.lattice.toAddSubgroup)), Subtype.ext ?_⟩
    simp only [quotientToLatticePoints]
    congr 1
    set c : L'.lattice.toAddSubgroup ⧸ L.lattice.toAddSubgroup.addSubgroupOf
      L'.lattice.toAddSubgroup := -(QuotientAddGroup.mk (⟨t, ht⟩ : L'.lattice.toAddSubgroup))
    have hc : (QuotientAddGroup.mk c.out : L'.lattice.toAddSubgroup ⧸ _) =
        -(QuotientAddGroup.mk (⟨t, ht⟩ : L'.lattice.toAddSubgroup)) := QuotientAddGroup.out_eq' c
    rw [← QuotientAddGroup.mk_neg, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hc
    have hl : -(c.out : ℂ) - t ∈ L.lattice := by
      rw [Submodule.mem_toAddSubgroup] at hc
      convert hc using 1
    rw [show -(c.out : ℂ) = t + (-(c.out : ℂ) - t) by ring,
      L.weierstrassPoint_add_coe t ⟨_, hl⟩]

/-- For `Λ ⊆ Λ'`, the image of `Λ'` in `E_Λ(ℂ)` is finite. -/
lemma finite_latticePoints (h : L.lattice ≤ L'.lattice) : Finite (L.latticePoints L') :=
  have := finite_quotient_of_le h
  Finite.of_surjective _ (bijective_quotientToLatticePoints (L := L)).2

/-! ### Vélu's coordinates of `P_Λ(Λ')` -/

attribute [local instance] Fintype.ofFinite

/-- The `y`-coordinates of the points of `P_Λ(Λ')` sum to `0`, the subgroup being stable under
negation, which negates `y`-coordinates on `E_Λ`. -/
private lemma sum_yCoord_latticePoints [Finite (L.latticePoints L')] :
    ∑ Q : L.latticePoints L', Point.yCoord (Q : (L.weierstrassCurve.toAffine⁄ℂ).toAffine.Point) =
      0 := by
  have hneg (Q : L.latticePoints L') :
      Point.yCoord (-Q : (L.weierstrassCurve.toAffine⁄ℂ).toAffine.Point) =
        -Point.yCoord (Q : (L.weierstrassCurve.toAffine⁄ℂ).toAffine.Point) := by
    obtain ⟨Q, hQ⟩ := Q
    obtain ⟨t, -, rfl⟩ := mem_latticePoints.mp hQ
    rw [← map_neg, ← weierstrassPoint_neg, Point.yCoord_equivBaseChangeSelf,
      Point.yCoord_equivBaseChangeSelf, yCoord_weierstrassPoint, yCoord_weierstrassPoint,
      derivWeierstrassP_neg, neg_div]
  have hsum := Fintype.sum_equiv (Equiv.neg (L.latticePoints L'))
    (fun Q ↦ Point.yCoord (-Q : (L.weierstrassCurve.toAffine⁄ℂ).toAffine.Point))
    (fun Q ↦ Point.yCoord (Q : (L.weierstrassCurve.toAffine⁄ℂ).toAffine.Point))
    (fun Q ↦ by simp)
  simp only [hneg, Finset.sum_neg_distrib] at hsum
  linear_combination (-1 / 2 : ℂ) * hsum

/-- **Vélu's `x`-coordinate of `P_Λ(Λ')` evaluates to `℘_{Λ'}`.** -/
private lemma evalFF_veluX (h : L.lattice ≤ L'.lattice) [Finite (L.latticePoints L')] :
    evalFF L (veluX _ (L.latticePoints L')) = (℘[L'] : Germs) := by
  have := finite_quotient_of_le h
  rw [veluX_def, map_sub, map_sum, AlgHom.commutes, algebraMap_germs,
    ← (bijective_quotientToLatticePoints (L := L)).sum_comp,
    ← (bijective_quotientToLatticePoints (L := L)).sum_comp]
  simp only [quotientToLatticePoints, (evalFF_translation L _).1, Point.xCoord_equivBaseChangeSelf,
    xCoord_weierstrassPoint, ← Germ.coe_sum, ← Germ.coe_sub]
  refine Germ.coe_eq.mpr (Eventually.of_forall fun z ↦ ?_)
  rw [(hasSum_weierstrassP_of_le h z).unique (hasSum_fintype _), Finset.sum_sub_distrib]
  simp [weierstrassP_neg, sub_eq_add_neg]

/-- **Vélu's `y`-coordinate of `P_Λ(Λ')` evaluates to `℘'_{Λ'} / 2`.** -/
private lemma evalFF_veluY (h : L.lattice ≤ L'.lattice) [Finite (L.latticePoints L')] :
    evalFF L (veluY _ (L.latticePoints L')) = ((fun z ↦ ℘'[L'] z / 2 : ℂ → ℂ) : Germs) := by
  have := finite_quotient_of_le h
  rw [veluY_def, map_sub, map_sum, AlgHom.commutes, sum_yCoord_latticePoints, map_zero, sub_zero,
    ← (bijective_quotientToLatticePoints (L := L)).sum_comp]
  simp only [quotientToLatticePoints, (evalFF_translation L _).2, ← Germ.coe_sum]
  refine Germ.coe_eq.mpr (Eventually.of_forall fun z ↦ ?_)
  beta_reduce
  rw [(hasSum_derivWeierstrassP_of_le h z).unique (hasSum_fintype _), Finset.sum_div]
  simp [sub_eq_add_neg]

/-- **Vélu's quotient of `E_Λ` by `Λ' / Λ` is `E_{Λ'}`.** For period lattices `Λ ⊆ Λ'`, the
quotient curve of Vélu's construction for the finite subgroup `P_Λ(Λ')` of `E_Λ(ℂ)` is the
Weierstrass curve of `Λ'`. Vélu's coordinates are the rational functions of `℘_Λ` and `℘'_Λ`
describing `℘_{Λ'}` and `℘'_{Λ'} / 2`. -/
theorem veluCurve_latticePoints (h : L.lattice ≤ L'.lattice) [Finite (L.latticePoints L')] :
    veluCurve L.weierstrassCurve.toAffine (L.latticePoints L') = L'.weierstrassCurve := by
  classical
  refine (eq_veluCurve_of_equation _ _ ?_).symm
  have hW : (L'.weierstrassCurve.toAffine⁄L.weierstrassCurve.toAffine.FunctionField).map
      (evalFF L : L.weierstrassCurve.toAffine.FunctionField →+* Germs) =
        L'.weierstrassCurve.toAffine⁄Germs :=
    Affine.map_baseChange _ (evalFF L)
  rw [← Affine.map_equation _
    (evalFF L : L.weierstrassCurve.toAffine.FunctionField →+* Germs).injective, hW]
  change (L'.weierstrassCurve.toAffine⁄Germs).Equation (evalFF L _) (evalFF L _)
  rw [evalFF_veluX h, evalFF_veluY h]
  exact equation_germs ((germs_eventually_notMem_lattice L').mono fun _ hz ↦
    L'.equation_weierstrassP hz)

/-! ### The isogeny of a superlattice -/

private lemma degree_eqRec {W₁ W₂ W₃ : Affine ℂ} (e : W₂ = W₃) (φ : Isogeny W₁ W₂) :
    (e ▸ φ).degree = φ.degree := by
  subst e
  rfl

private lemma ker_eqRec {W₁ W₂ W₃ : Affine ℂ} [W₁.IsElliptic] (e : W₂ = W₃) (φ : Isogeny W₁ W₂) :
    (e ▸ φ).ker = φ.ker := by
  subst e
  rfl

/-- **The isogeny `E_Λ → E_{Λ'}` of a superlattice** `Λ ⊆ Λ'`: Vélu's isogeny of `E_Λ` with kernel
`P_Λ(Λ')`, whose target is `E_{Λ'}` by `PeriodPair.veluCurve_latticePoints`. -/
def isogenyOfLE (h : L.lattice ≤ L'.lattice) :
    Isogeny L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine :=
  haveI := finite_latticePoints h
  congrArg WeierstrassCurve.toAffine (veluCurve_latticePoints h) ▸
    veluIsogeny _ (L.latticePoints L')

private lemma fieldPullback_eqRec {W₁ W₂ W₃ : Affine ℂ} (e : W₂ = W₃) (φ : Isogeny W₁ W₂) :
    (e ▸ φ).fieldPullback (genericX W₃) = φ.fieldPullback (genericX W₂) ∧
      (e ▸ φ).fieldPullback (genericY W₃) = φ.fieldPullback (genericY W₂) := by
  subst e
  exact ⟨rfl, rfl⟩

/-- The isogeny of a superlattice pulls the coordinate `x` of `E_{Λ'}` back to Vélu's
`x`-coordinate for `P_Λ(Λ')`. -/
theorem fieldPullback_isogenyOfLE_genericX (h : L.lattice ≤ L'.lattice)
    [Finite (L.latticePoints L')] :
    (isogenyOfLE h).fieldPullback (genericX _) = veluX _ (L.latticePoints L') := by
  rw [isogenyOfLE, (fieldPullback_eqRec _ _).1, fieldPullback_veluIsogeny_genericX]

/-- The isogeny of a superlattice pulls the coordinate `y` of `E_{Λ'}` back to Vélu's
`y`-coordinate for `P_Λ(Λ')`. -/
theorem fieldPullback_isogenyOfLE_genericY (h : L.lattice ≤ L'.lattice)
    [Finite (L.latticePoints L')] :
    (isogenyOfLE h).fieldPullback (genericY _) = veluY _ (L.latticePoints L') := by
  rw [isogenyOfLE, (fieldPullback_eqRec _ _).2, fieldPullback_veluIsogeny_genericY]

/-- **The isogeny of a superlattice has degree `[Λ' : Λ]`.** -/
theorem degree_isogenyOfLE (h : L.lattice ≤ L'.lattice) :
    (isogenyOfLE h).degree = L.lattice.toAddSubgroup.relIndex L'.lattice.toAddSubgroup := by
  have := finite_quotient_of_le h
  rw [isogenyOfLE, degree_eqRec, degree_veluIsogeny, AddSubgroup.relIndex, AddSubgroup.index]
  exact (Nat.card_congr (Equiv.ofBijective _ bijective_quotientToLatticePoints)).symm

/-- **The kernel of the isogeny of a superlattice `Λ ⊆ Λ'` is `P_Λ(Λ')`.** -/
theorem ker_isogenyOfLE (h : L.lattice ≤ L'.lattice) :
    (isogenyOfLE h).ker = L.latticePoints L' := by
  rw [isogenyOfLE, ker_eqRec, ker_veluIsogeny]

/-- The kernel of the isogeny of a superlattice has as many points as its degree. -/
theorem natCard_ker_isogenyOfLE (h : L.lattice ≤ L'.lattice) :
    Nat.card (isogenyOfLE h).ker = (isogenyOfLE h).degree := by
  rw [ker_isogenyOfLE]
  rw [isogenyOfLE, degree_eqRec, degree_veluIsogeny]

/-- The denominator `2y + a₁x + a₃` of the invariant differential of `E_Λ` is `2y`. -/
private lemma invariantDifferentialDenom_weierstrassCurve (E : PeriodPair) :
    invariantDifferentialDenom E.weierstrassCurve.toAffine = 2 * genericY _ := by
  rw [invariantDifferentialDenom_def]
  simp

/-- **The isogeny of a superlattice preserves the invariant differential**: it pulls
`ω_{Λ'} = dx / 2y` back to `ω_Λ`, both corresponding to `dz`. Vélu's coordinates satisfy
`dX = 2 Y ω_Λ`, translations fixing `ω_Λ`. -/
theorem pullbackDifferential_isogenyOfLE (h : L.lattice ≤ L'.lattice) :
    (isogenyOfLE h).pullbackDifferential (invariantDifferential _) = invariantDifferential _ := by
  have := finite_latticePoints h
  have h2 : (2 : L.weierstrassCurve.toAffine.FunctionField) ≠ 0 := by
    rw [← map_ofNat (algebraMap ℂ _) 2]
    exact (map_ne_zero _).mpr two_ne_zero
  have hD : KaehlerDifferential.D ℂ L.weierstrassCurve.toAffine.FunctionField
      (veluX _ (L.latticePoints L')) =
        (2 * veluY _ (L.latticePoints L')) • invariantDifferential _ := by
    rw [veluX_def, veluY_def, sum_yCoord_latticePoints, map_zero, sub_zero, map_sub,
      Derivation.map_algebraMap, sub_zero, map_sum, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun Q _ ↦ ?_
    rw [D_translation_genericX, invariantDifferentialDenom_weierstrassCurve, map_mul, map_ofNat]
  rw [invariantDifferential_def L'.weierstrassCurve.toAffine,
    invariantDifferentialDenom_weierstrassCurve, Isogeny.pullbackDifferential_smul,
    Isogeny.pullbackDifferential_D, map_inv₀, map_mul, map_ofNat,
    fieldPullback_isogenyOfLE_genericX, fieldPullback_isogenyOfLE_genericY, hD, smul_smul,
    inv_mul_cancel₀ (mul_ne_zero h2 (veluY_ne_zero _ _)), one_smul]

end PeriodPair
