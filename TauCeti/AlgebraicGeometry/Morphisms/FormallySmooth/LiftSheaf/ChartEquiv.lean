/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftSheaf.Module
public import TauCeti.AlgebraicGeometry.Restrict
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftSheaf.Sub

/-!
# Derivations over an affine open as derivations of rings

Let `i : T ⟶ T'` be a first-order thickening, `W` an affine open of `T'` over which `a` lifts, and
`U ⊆ X`, `V ⊆ S` affine opens with `a (i ⁻¹ W) ⊆ U`, `h W ⊆ V` and `f U ⊆ V`. The derivations over
`W` of the sheaf `liftDerivationSheaf f i a` are then exactly the `Γ(V, ⊤)`-derivations
`Γ(U, ⊤) → ker (i ∣_ W)^♯`: reading a derivation on the chart `(U, W)` (`liftDerivationChart`) is a
bijection. It is compatible with the action of sections of `𝒪_{T'}` and with restriction to a
smaller affine open `W' ⊆ W`. This is the chart description `ℋ(W) = Der_{Γ(V)}(Γ(U), I(W))` of the
sheaf of derivations `Hom(a^* Ω_{X/S}, I)` of Stacks, Lemma 37.9.5 (04FJ).

## Main definitions

* `TauCeti.AlgebraicGeometry.liftDerivationChartEquiv`: the derivations over `W` are the
  `Γ(V, ⊤)`-derivations `Γ(U, ⊤) → ker (i ∣_ W)^♯`.

## Main results

* `TauCeti.AlgebraicGeometry.liftDerivationChart_surjective`: every derivation
  `Γ(U, ⊤) → ker (i ∣_ W)^♯` is the chart derivation of a derivation over `W`.
* `TauCeti.AlgebraicGeometry.coe_liftDerivationChart_smul`: the chart derivation of `t • D` is
  the chart derivation of `D` multiplied by `t`.
* `TauCeti.AlgebraicGeometry.coe_liftDerivationChart_restrict`: the chart derivation of the
  restriction of `D` to `W' ⊆ W` is the restriction of the chart derivation of `D`.

## References

* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

variable {X S T T' : Scheme.{u}} {f : X ⟶ S} {i : T ⟶ T'} {a : T ⟶ X} {h : T' ⟶ S}
  [IsFirstOrderThickening i] {W : T'.Opens} {U : X.Opens} {V : S.Opens} [IsAffine W.toScheme]

/-- The chart derivation of a sum of derivations over `W` is the sum of their chart
derivations. -/
theorem liftDerivationChart_add (w : a ≫ f = i ≫ h) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V) (l₀ : (liftSheaf f i a h).obj.obj (op W))
    (D E : liftDerivationSubgroup f i a W) :
    liftDerivationChart w hU hV hUV l₀ (D + E) =
      liftDerivationChart w hU hV hUV l₀ D + liftDerivationChart w hU hV hUV l₀ E := by
  let := (f.resLE V U hUV).appTop.hom.toAlgebra
  let := (h.resLE V W hV).appTop.hom.toAlgebra
  let := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
  let := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
    (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
  refine Derivation.ext fun y ↦ Subtype.ext ?_
  rw [add_apply, Submodule.coe_add, coe_liftDerivationChart_apply,
    coe_liftDerivationChart_apply, coe_liftDerivationChart_apply, AddSubgroup.coe_add,
    Pi.add_apply, AddMonoidHom.add_apply, map_add]

variable [IsAffine U.toScheme] [IsAffine V.toScheme]

/-- Every `Γ(V, ⊤)`-derivation `Γ(U, ⊤) → ker (i ∣_ W)^♯` is the chart derivation of a derivation
over `W`: the difference of a section of the sheaf of lifts with `l₀`. -/
theorem liftDerivationChart_surjective (w : a ≫ f = i ≫ h) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V) (l₀ : (liftSheaf f i a h).obj.obj (op W)) :
    Function.Surjective (liftDerivationChart w hU hV hUV l₀) := by
  have : (commSq_resLE w hU hV hUV).HasLift := ⟨⟨liftSheafObjEquivLiftStruct w hU hV hUV l₀⟩⟩
  let := liftStructAddTorsor (commSq_resLE w hU hV hUV)
  set e := liftSheafObjEquivLiftStruct w hU hV hUV
  exact fun d ↦ ⟨liftSheafSub (e.symm (d +ᵥ e l₀)) l₀, by
    rw [liftDerivationChart_liftSheafSub, Equiv.apply_symm_apply, vadd_vsub]⟩

/-- Over an affine open `W` of `T'` over which `a` lifts (through the section `l₀` of the sheaf of
lifts), with affine charts `U ⊆ X`, `V ⊆ S` (`a (i ⁻¹ W) ⊆ U`, `h W ⊆ V`, `f U ⊆ V`), the
derivations over `W` are the `Γ(V, ⊤)`-derivations `Γ(U, ⊤) → ker (i ∣_ W)^♯`, by reading a
derivation on the chart `(U, W)`. -/
noncomputable def liftDerivationChartEquiv (w : a ≫ f = i ≫ h) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V) (l₀ : (liftSheaf f i a h).obj.obj (op W)) :
    liftDerivationSubgroup f i a W ≃+
      letI := (f.resLE V U hUV).appTop.hom.toAlgebra
      letI := (h.resLE V W hV).appTop.hom.toAlgebra
      letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
      letI := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
        (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
      Derivation Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤) (RingHom.ker (i ∣_ W).appTop.hom) :=
  AddEquiv.ofBijective (AddMonoidHom.mk' _ (liftDerivationChart_add w hU hV hUV l₀))
    ⟨liftDerivationChart_injective w hU hV hUV l₀, liftDerivationChart_surjective w hU hV hUV l₀⟩

@[simp]
theorem liftDerivationChartEquiv_apply (w : a ≫ f = i ≫ h) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V) (l₀ : (liftSheaf f i a h).obj.obj (op W))
    (D : liftDerivationSubgroup f i a W) :
    liftDerivationChartEquiv w hU hV hUV l₀ D = liftDerivationChart w hU hV hUV l₀ D :=
  (rfl)

omit [IsAffine U.toScheme] [IsAffine V.toScheme] in
/-- The chart derivation of `t • D` is the chart derivation of `D` multiplied by `t`. -/
theorem coe_liftDerivationChart_smul (w : a ≫ f = i ≫ h) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V) (l₀ : (liftSheaf f i a h).obj.obj (op W))
    (t : Γ(T', W)) (D : liftDerivationSubgroup f i a W) (y : Γ(U.toScheme, ⊤)) :
    letI := (f.resLE V U hUV).appTop.hom.toAlgebra
    letI := (h.resLE V W hV).appTop.hom.toAlgebra
    letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
    letI := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
    (liftDerivationChart w hU hV hUV l₀ (t • D) y : Γ(W.toScheme, ⊤)) =
      W.topIso.inv t * liftDerivationChart w hU hV hUV l₀ D y := by
  rw [coe_liftDerivationChart_apply, coe_liftDerivationChart_apply,
    liftDerivationSubgroup.smul_apply, map_mul,
    (Subsingleton.elim _ (𝟙 W) : homOfLE (le_refl W) = 𝟙 W), op_id,
    CategoryTheory.Functor.map_id, CommRingCat.id_apply]

omit [IsAffine U.toScheme] [IsAffine V.toScheme] in
/-- The chart derivation of the restriction of a derivation `D` over `W` to an affine open
`W' ⊆ W` is the restriction of the chart derivation of `D` along `W' ⟶ W`. -/
theorem coe_liftDerivationChart_restrict {W' : T'.Opens} [IsAffine W'.toScheme]
    (w : a ≫ f = i ≫ h) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V)
    (e : W' ≤ W)
    (l₀ : (liftSheaf f i a h).obj.obj (op W)) (l₀' : (liftSheaf f i a h).obj.obj (op W'))
    (D : liftDerivationSubgroup f i a W) (y : Γ(U.toScheme, ⊤)) :
    letI := (f.resLE V U hUV).appTop.hom.toAlgebra
    letI := (h.resLE V W hV).appTop.hom.toAlgebra
    letI := (h.resLE V W' (e.trans hV)).appTop.hom.toAlgebra
    letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
    letI := quotientKerAppTopAlgebra (i ∣_ W') (a.resLE U (i ⁻¹ᵁ W') ((i.preimage_mono e).trans hU))
    letI := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
    letI := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W'))
    (liftDerivationChart w ((i.preimage_mono e).trans hU) (e.trans hV) hUV l₀'
        (liftDerivationSubgroupRestrict f i a e D) y : Γ(W'.toScheme, ⊤)) =
      (T'.homOfLE e).appTop (liftDerivationChart w hU hV hUV l₀ D y) := by
  rw [coe_liftDerivationChart_apply, coe_liftDerivationChart_apply,
    liftDerivationSubgroupRestrict_apply, ← Scheme.Opens.topIso_inv_map_homOfLE e,
    (isLiftDerivation_coe D).map_apply ⟨(U, W), le_rfl, hU⟩ W' e]

end TauCeti.AlgebraicGeometry
