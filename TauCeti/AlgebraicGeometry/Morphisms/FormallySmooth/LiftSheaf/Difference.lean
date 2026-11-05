/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftSheaf.Affine
public import TauCeti.AlgebraicGeometry.Scheme.AppLESub

/-!
# Differences of sections of the sheaf of lifts

For two sections `l₁`, `l₂` of the sheaf of lifts `liftSheaf f i a h` over an open `W` of `T'`, the
difference `Scheme.Hom.appLESub l₁ l₂ U V` (`x ↦ l₁^♯ x - l₂^♯ x` on sections of `X` over any open
`U`) describes how the two lifts differ, with no affine chart; when `i` is a first-order thickening
it is a derivation into the ideal of `i` (`Scheme.Hom.appLESub_mul_of_isFirstOrderThickening`).
Along a surjective `i` the two sections are equal if and only if all their differences vanish. Over
affine opens `W ⊆ T'`, `U ⊆ X`, `V ⊆ S`, the difference on `U` is the derivation by which the
corresponding lifts differ in the torsor `liftStructAddTorsor`, so the derivations read through two
affine charts `U₁`, `U₂` agree on sections with the same restriction to `U₁ ⊓ U₂`, even when
`U₁ ⊓ U₂` is not affine. This is the chart-free form of the differences of lifts in Stacks,
Lemma 37.9.5 (04FJ), where they are sections of `Hom(a^* Ω_{X/S}, I)`.

## Main results

* `TauCeti.AlgebraicGeometry.liftSheaf_ext_iff`: two sections of the sheaf of lifts are equal if
  and only if their differences vanish.
* `TauCeti.AlgebraicGeometry.liftSheaf_eq_of_appLESub_eq`: two sections that differ from a third
  section in the same way are equal.
* `TauCeti.AlgebraicGeometry.liftSheafObjEquivLiftStruct_vsub_apply_eq_appLESub`: over affine
  charts, the difference of two sections of the sheaf of lifts is the derivation by which the
  corresponding lifts differ.
* `TauCeti.AlgebraicGeometry.liftSheafObjEquivLiftStruct_vsub_apply_eq_of_map_eq`: the
  derivations read through two affine charts agree on sections that agree on the intersection.

## References

* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry


section LiftSheaf

variable {X S T T' : Scheme.{u}} {f : X ⟶ S} {i : T ⟶ T'} {a : T ⟶ X} {h : T' ⟶ S}
  {W : T'.Opens}

/-- Two sections of the sheaf of lifts agree after precomposing with `i ∣_ W`. -/
theorem morphismRestrict_comp_liftSheafObjEquiv (l₁ l₂ : (liftSheaf f i a h).obj.obj (op W)) :
    i ∣_ W ≫ (liftSheafObjEquiv f i a h W l₁).1 = i ∣_ W ≫ (liftSheafObjEquiv f i a h W l₂).1 :=
  (liftSheafObjEquiv f i a h W l₁).2.1.trans (liftSheafObjEquiv f i a h W l₂).2.1.symm

/-- Two sections of the sheaf of lifts agree after composing with `f`. -/
theorem liftSheafObjEquiv_comp (l₁ l₂ : (liftSheaf f i a h).obj.obj (op W)) :
    (liftSheafObjEquiv f i a h W l₁).1 ≫ f = (liftSheafObjEquiv f i a h W l₂).1 ≫ f :=
  (liftSheafObjEquiv f i a h W l₁).2.2.trans (liftSheafObjEquiv f i a h W l₂).2.2.symm

variable [Surjective i]

/-- Along a surjective `i`, two sections of the sheaf of lifts over `W` are equal if and only if
their differences on every open `U` of `X` vanish. -/
theorem liftSheaf_ext_iff {l₁ l₂ : (liftSheaf f i a h).obj.obj (op W)} :
    haveI : Surjective (i ∣_ W) := IsZariskiLocalAtTarget.restrict ‹_› W
    l₁ = l₂ ↔ ∀ U : X.Opens,
      Scheme.Hom.appLESub (liftSheafObjEquiv f i a h W l₁).1 (liftSheafObjEquiv f i a h W l₂).1 U _
        (Scheme.Hom.preimage_eq_of_comp_eq (morphismRestrict_comp_liftSheafObjEquiv l₁ l₂) U).ge
        le_rfl = 0 := by
  have : Surjective (i ∣_ W) := IsZariskiLocalAtTarget.restrict ‹_› W
  rw [← Scheme.Hom.eq_iff_appLESub_eq_zero (morphismRestrict_comp_liftSheafObjEquiv l₁ l₂),
    (liftSheafObjEquiv f i a h W).injective.eq_iff.symm, Subtype.ext_iff]

/-- Along a surjective `i`, two sections `l₁`, `l₂` of the sheaf of lifts over `W` that differ
from a third section `l` in the same way are equal. -/
theorem liftSheaf_eq_of_appLESub_eq {l l₁ l₂ : (liftSheaf f i a h).obj.obj (op W)}
    (H : ∀ (U : X.Opens) (V : W.toScheme.Opens)
      (e₁ : V ≤ (liftSheafObjEquiv f i a h W l₁).1 ⁻¹ᵁ U)
      (e₂ : V ≤ (liftSheafObjEquiv f i a h W l₂).1 ⁻¹ᵁ U)
      (e : V ≤ (liftSheafObjEquiv f i a h W l).1 ⁻¹ᵁ U),
      Scheme.Hom.appLESub (liftSheafObjEquiv f i a h W l₁).1 (liftSheafObjEquiv f i a h W l).1
          U V e₁ e =
        Scheme.Hom.appLESub (liftSheafObjEquiv f i a h W l₂).1 (liftSheafObjEquiv f i a h W l).1
          U V e₂ e) :
    l₁ = l₂ := by
  refine liftSheaf_ext_iff.2 fun U ↦ ?_
  have : Surjective (i ∣_ W) := IsZariskiLocalAtTarget.restrict ‹_› W
  have e := (Scheme.Hom.preimage_eq_of_comp_eq
    (morphismRestrict_comp_liftSheafObjEquiv l₂ l) U).le
  rw [← Scheme.Hom.appLESub_add_appLESub _ e, H U _ _ le_rfl e,
    Scheme.Hom.appLESub_add_appLESub, Scheme.Hom.appLESub_self]

variable [IsFirstOrderThickening i] [IsAffine W.toScheme] {U : X.Opens} {V : S.Opens}
  [IsAffine U.toScheme] [IsAffine V.toScheme]

/-- Over affine opens `W ⊆ T'`, `U ⊆ X` and `V ⊆ S`, the difference of two sections of the sheaf
of lifts on `U` is the derivation by which the corresponding lifts in the restricted square
differ in the torsor `liftStructAddTorsor`. -/
theorem liftSheafObjEquivLiftStruct_vsub_apply_eq_appLESub (w : a ≫ f = i ≫ h)
    (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V)
    [(commSq_resLE w hU hV hUV).HasLift] (l₁ l₂ : (liftSheaf f i a h).obj.obj (op W))
    (e₁ : ⊤ ≤ (liftSheafObjEquiv f i a h W l₁).1 ⁻¹ᵁ U)
    (e₂ : ⊤ ≤ (liftSheafObjEquiv f i a h W l₂).1 ⁻¹ᵁ U) (x : Γ(X, U)) :
    letI := liftStructAddTorsor (commSq_resLE w hU hV hUV)
    ((liftSheafObjEquivLiftStruct w hU hV hUV l₁ -ᵥ liftSheafObjEquivLiftStruct w hU hV hUV l₂)
        (U.ι.appLE U ⊤ (by simp) x) : Γ(W.toScheme, ⊤)) =
      Scheme.Hom.appLESub (liftSheafObjEquiv f i a h W l₁).1 (liftSheafObjEquiv f i a h W l₂).1 U ⊤
        e₁ e₂ x := by
  have key (L : (commSq_resLE w hU hV hUV).LiftStruct) (m : W.toScheme ⟶ X)
      (hm : L.l ≫ U.ι = m) (e : ⊤ ≤ m ⁻¹ᵁ U) :
      L.l.appTop (U.ι.appLE U ⊤ (by simp) x) = m.appLE U ⊤ e x := by
    subst hm
    have := Scheme.Hom.appLE_comp_appLE L.l U.ι U ⊤ (L.l ⁻¹ᵁ ⊤) (by simp) le_rfl
    rw [Scheme.Hom.appLE_eq_app] at this
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom this) x
  rw [liftStructAddTorsor_vsub_apply, Scheme.Hom.appLESub_apply,
    key _ _ (liftSheafObjEquivLiftStruct_apply_l_ι w hU hV hUV l₁) e₁,
    key _ _ (liftSheafObjEquivLiftStruct_apply_l_ι w hU hV hUV l₂) e₂]

omit [IsAffine U.toScheme] in
/-- The derivations by which two sections of the sheaf of lifts over an affine open `W` differ,
read through two affine charts `U₁` and `U₂` of `X`, agree on sections of `U₁` and `U₂` with the
same restriction to `U₁ ⊓ U₂`, which need not be affine. -/
theorem liftSheafObjEquivLiftStruct_vsub_apply_eq_of_map_eq (w : a ≫ f = i ≫ h)
    {U₁ U₂ : X.Opens} {V₁ V₂ : S.Opens} [IsAffine U₁.toScheme] [IsAffine U₂.toScheme]
    [IsAffine V₁.toScheme] [IsAffine V₂.toScheme]
    (hU₁ : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U₁) (hV₁ : W ≤ h ⁻¹ᵁ V₁) (hUV₁ : U₁ ≤ f ⁻¹ᵁ V₁)
    (hU₂ : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U₂) (hV₂ : W ≤ h ⁻¹ᵁ V₂) (hUV₂ : U₂ ≤ f ⁻¹ᵁ V₂)
    [(commSq_resLE w hU₁ hV₁ hUV₁).HasLift] [(commSq_resLE w hU₂ hV₂ hUV₂).HasLift]
    (l₁ l₂ : (liftSheaf f i a h).obj.obj (op W)) (x₁ : Γ(X, U₁)) (x₂ : Γ(X, U₂))
    (hx : X.presheaf.map (homOfLE inf_le_left).op x₁ =
      X.presheaf.map (homOfLE inf_le_right).op x₂) :
    letI := liftStructAddTorsor (commSq_resLE w hU₁ hV₁ hUV₁)
    letI := liftStructAddTorsor (commSq_resLE w hU₂ hV₂ hUV₂)
    ((liftSheafObjEquivLiftStruct w hU₁ hV₁ hUV₁ l₁ -ᵥ
        liftSheafObjEquivLiftStruct w hU₁ hV₁ hUV₁ l₂) (U₁.ι.appLE U₁ ⊤ (by simp) x₁) :
        Γ(W.toScheme, ⊤)) =
      (liftSheafObjEquivLiftStruct w hU₂ hV₂ hUV₂ l₁ -ᵥ
        liftSheafObjEquivLiftStruct w hU₂ hV₂ hUV₂ l₂) (U₂.ι.appLE U₂ ⊤ (by simp) x₂) := by
  -- Every section of the sheaf of lifts over `W` lands in `U₁ ⊓ U₂`.
  have hrange (U : X.Opens) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (l : (liftSheaf f i a h).obj.obj (op W)) :
      ⊤ ≤ (liftSheafObjEquiv f i a h W l).1 ⁻¹ᵁ U := fun y _ ↦ by
    have := range_subset_of_liftSheaf hU l ⟨y, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  have h₁₂ : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ (U₁ ⊓ U₂) := le_inf hU₁ hU₂
  rw [liftSheafObjEquivLiftStruct_vsub_apply_eq_appLESub w hU₁ hV₁ hUV₁ l₁ l₂
      (hrange _ hU₁ l₁) (hrange _ hU₁ l₂),
    liftSheafObjEquivLiftStruct_vsub_apply_eq_appLESub w hU₂ hV₂ hUV₂ l₁ l₂
      (hrange _ hU₂ l₁) (hrange _ hU₂ l₂),
    ← Scheme.Hom.map_appLESub (hrange _ h₁₂ l₁) (hrange _ h₁₂ l₂) inf_le_left x₁, hx,
    Scheme.Hom.map_appLESub]

end LiftSheaf

end TauCeti.AlgebraicGeometry
