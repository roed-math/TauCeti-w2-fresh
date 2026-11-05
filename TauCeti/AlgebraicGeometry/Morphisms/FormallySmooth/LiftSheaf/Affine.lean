/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.AffineLifts
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftSheaf.Basic

/-!
# Sections of the sheaf of lifts over affine opens

Let `a ≫ f = i ≫ h` be a commutative square with `i : T ⟶ T'` surjective, and let `W ⊆ T'`,
`U ⊆ X` and `V ⊆ S` be opens with `a (i⁻¹ W) ⊆ U`, `h W ⊆ V` and `f U ⊆ V`. Every section of the
sheaf of lifts `liftSheaf f i a h` over `W` lands in `U`, so the sections over `W` are the lifts in
the restricted square `a ∣ (i⁻¹ W ⟶ U)`, `i ∣_ W`, `f ∣ (U ⟶ V)`, `h ∣ (W ⟶ V)`. Restricting a
section to a smaller open `W' ⊆ W` is precomposing the lift with `W' ⟶ W`.

When `i` is a first-order thickening and `W`, `U`, `V` are affine, the lifts in the restricted
square form a torsor under `Der_{Γ(V)}(Γ(U), ker (i ∣_ W).appTop)` (`liftStructAddTorsor`), and
restriction to a smaller affine open `W' ⊆ W` is equivariant along the restriction of
derivations. The difference of two sections, read through a smaller affine open `U' ⊆ U`, is the
same derivation composed with the restriction `Γ(U, ⊤) ⟶ Γ(U', ⊤)`. These are the local torsors
whose gluing is the torsor of lifts of Stacks, Lemma 37.9.5 (04FJ).

## Main definitions

* `TauCeti.AlgebraicGeometry.liftSheafObjEquivLiftStruct`: the sections of the sheaf of lifts over
  `W` are the lifts in the restricted square.

## Main results

* `TauCeti.AlgebraicGeometry.liftSheafObjEquivLiftStruct_map`: restriction of sections is
  precomposition of lifts.
* `TauCeti.AlgebraicGeometry.liftSheafObjEquivLiftStruct_map_vadd`: restriction of sections to a
  smaller affine open is equivariant for the torsors of lifts under derivations.
* `TauCeti.AlgebraicGeometry.liftSheafObjEquivLiftStruct_vsub_apply_homOfLE`: the derivation by
  which two sections over `W` differ does not depend on the affine opens `U ⊆ X` and `V ⊆ S`
  through which it is read, up to restriction along a smaller `U' ⊆ U`.

## References

* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace TauCeti.AlgebraicGeometry

variable {X S T T' : Scheme.{u}} {f : X ⟶ S} {i : T ⟶ T'} {a : T ⟶ X} {h : T' ⟶ S}
  {W W' : T'.Opens} {U : X.Opens} {V : S.Opens}

/-- The restriction of a commutative square `a ≫ f = i ≫ h` over opens `W ⊆ T'`, `U ⊆ X` and
`V ⊆ S` with `a (i⁻¹ W) ⊆ U`, `h W ⊆ V` and `f U ⊆ V`. -/
theorem commSq_resLE (w : a ≫ f = i ≫ h) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (hV : W ≤ h ⁻¹ᵁ V)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    CommSq (a.resLE U (i ⁻¹ᵁ W) hU) (i ∣_ W) (f.resLE V U hUV) (h.resLE V W hV) :=
  ⟨by simp [← cancel_mono V.ι, w]⟩

section Surjective

variable [Surjective i]

/-- If `a (i⁻¹ W) ⊆ U` and `i` is surjective, every section of the sheaf of lifts over `W` lands
in `U`. -/
theorem range_subset_of_liftSheaf (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (l : (liftSheaf f i a h).obj.obj (op W)) :
    Set.range (liftSheafObjEquiv f i a h W l).1 ⊆ Set.range U.ι := by
  rintro _ ⟨y, rfl⟩
  have : Surjective (i ∣_ W) := IsZariskiLocalAtTarget.restrict ‹_› W
  obtain ⟨z, rfl⟩ := (i ∣_ W).surjective y
  rw [← Scheme.Hom.comp_apply, (liftSheafObjEquiv f i a h W l).2.1, Scheme.Hom.comp_apply,
    Scheme.Opens.range_ι]
  exact hU z.2

/-- If `i` is surjective, the sections over `W` of the sheaf of lifts of `a` along `i` over `S` are
the lifts in the square `a ∣ (i⁻¹ W ⟶ U)`, `i ∣_ W`, `f ∣ (U ⟶ V)`, `h ∣ (W ⟶ V)`, where
`a (i⁻¹ W) ⊆ U`, `h W ⊆ V` and `f U ⊆ V`: a section `l : W ⟶ X` lands in `U`. -/
noncomputable def liftSheafObjEquivLiftStruct (w : a ≫ f = i ≫ h) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V) :
    (liftSheaf f i a h).obj.obj (op W) ≃ (commSq_resLE w hU hV hUV).LiftStruct where
  toFun l :=
    { l := IsOpenImmersion.lift U.ι (liftSheafObjEquiv f i a h W l).1
        (range_subset_of_liftSheaf hU l)
      fac_left := by
        simp [← cancel_mono U.ι, (liftSheafObjEquiv f i a h W l).2.1]
      fac_right := by
        simp [← cancel_mono V.ι, (liftSheafObjEquiv f i a h W l).2.2] }
  invFun l := (liftSheafObjEquiv f i a h W).symm ⟨l.l ≫ U.ι,
    by rw [reassoc_of% l.fac_left, Scheme.Hom.resLE_comp_ι], by
    rw [Category.assoc, ← Scheme.Hom.resLE_comp_ι f hUV, reassoc_of% l.fac_right,
      Scheme.Hom.resLE_comp_ι]⟩
  left_inv l := (liftSheafObjEquiv f i a h W).symm_apply_eq.2 <|
    Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  right_inv l := CommSq.LiftStruct.ext <| by
    rw [← cancel_mono U.ι, IsOpenImmersion.lift_fac, Equiv.apply_symm_apply]

/-- The lift corresponding to a section `l` of the sheaf of lifts, followed by `U ⟶ X`, is `l`. -/
@[simp, reassoc]
theorem liftSheafObjEquivLiftStruct_apply_l_ι (w : a ≫ f = i ≫ h) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V) (l : (liftSheaf f i a h).obj.obj (op W)) :
    (liftSheafObjEquivLiftStruct w hU hV hUV l).l ≫ U.ι = (liftSheafObjEquiv f i a h W l).1 :=
  IsOpenImmersion.lift_fac _ _ _

/-- The section corresponding to a lift `l` in the restricted square is `l` followed by
`U ⟶ X`. -/
@[simp]
theorem coe_liftSheafObjEquivLiftStruct_symm_apply (w : a ≫ f = i ≫ h)
    (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V)
    (l : (commSq_resLE w hU hV hUV).LiftStruct) :
    (liftSheafObjEquiv f i a h W ((liftSheafObjEquivLiftStruct w hU hV hUV).symm l)).1 =
      l.l ≫ U.ι :=
  congrArg Subtype.val ((liftSheafObjEquiv f i a h W).apply_symm_apply _)

/-- Restricting a section of the sheaf of lifts to a smaller open `W' ⊆ W` is precomposing the
corresponding lift with `W' ⟶ W`. -/
theorem liftSheafObjEquivLiftStruct_map (w : a ≫ f = i ≫ h) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V) (e : W' ≤ W) (l : (liftSheaf f i a h).obj.obj (op W)) :
    liftSheafObjEquivLiftStruct w ((i.preimage_mono e).trans hU) (e.trans hV) hUV
        ((liftSheaf f i a h).obj.map (homOfLE e).op l) =
      (liftSheafObjEquivLiftStruct w hU hV hUV l).precomp (morphismRestrict_homOfLE i W' W e).symm
        (Scheme.Hom.map_resLE _ _ _) (Scheme.Hom.map_resLE _ _ _) _ :=
  CommSq.LiftStruct.ext <| by
    rw [← cancel_mono U.ι, liftSheafObjEquivLiftStruct_apply_l_ι, CommSq.LiftStruct.precomp_l,
      Category.assoc, liftSheafObjEquivLiftStruct_apply_l_ι, coe_liftSheafObjEquiv_map]

variable {U' : X.Opens} {V' : S.Opens}

/-- For opens `U' ⊆ U` of `X`, both containing `a (i⁻¹ W)`, the lift in `U'` corresponding to a
section `l`, followed by `U' ⟶ U`, is the lift in `U` corresponding to `l`. -/
@[reassoc]
theorem liftSheafObjEquivLiftStruct_apply_l_homOfLE (w : a ≫ f = i ≫ h)
    (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V) (hU' : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U')
    (hV' : W ≤ h ⁻¹ᵁ V') (hUV' : U' ≤ f ⁻¹ᵁ V') (e : U' ≤ U)
    (l : (liftSheaf f i a h).obj.obj (op W)) :
    (liftSheafObjEquivLiftStruct w hU' hV' hUV' l).l ≫ X.homOfLE e =
      (liftSheafObjEquivLiftStruct w hU hV hUV l).l := by
  rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, liftSheafObjEquivLiftStruct_apply_l_ι,
    liftSheafObjEquivLiftStruct_apply_l_ι]

end Surjective

variable [IsFirstOrderThickening i] [IsAffine W.toScheme] [IsAffine W'.toScheme]
  [IsAffine U.toScheme] [IsAffine V.toScheme]

/-- Restriction of sections of the sheaf of lifts from an affine open `W` to a smaller affine open
`W' ⊆ W` is equivariant for the torsors of lifts of `liftStructAddTorsor` in the restricted squares:
restricting `d +ᵥ l` gives the restriction of `l` acted on by the restriction of the derivation
`d` along `Γ(W, ⊤) ⟶ Γ(W', ⊤)`. -/
theorem liftSheafObjEquivLiftStruct_map_vadd (w : a ≫ f = i ≫ h) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V) (e : W' ≤ W)
    [(commSq_resLE w hU hV hUV).HasLift]
    [(commSq_resLE w ((i.preimage_mono e).trans hU) (e.trans hV) hUV).HasLift]
    (d : letI := (f.resLE V U hUV).appTop.hom.toAlgebra
      letI := (h.resLE V W hV).appTop.hom.toAlgebra
      letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
      letI := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
        (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
      Derivation Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤) (RingHom.ker (i ∣_ W).appTop.hom))
    (l : (liftSheaf f i a h).obj.obj (op W)) :
    letI := (f.resLE V U hUV).appTop.hom.toAlgebra
    letI := (h.resLE V W hV).appTop.hom.toAlgebra
    letI := (h.resLE V W' (e.trans hV)).appTop.hom.toAlgebra
    letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
    letI := quotientKerAppTopAlgebra (i ∣_ W') (a.resLE U (i ⁻¹ᵁ W') ((i.preimage_mono e).trans hU))
    letI := isScalarTower_quotientKerAppTopAlgebra (commSq_resLE w hU hV hUV)
    letI := isScalarTower_quotientKerAppTopAlgebra
      (commSq_resLE w ((i.preimage_mono e).trans hU) (e.trans hV) hUV)
    letI := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
    letI := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W'))
    letI : IsScalarTower Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤) (RingHom.ker (i ∣_ W).appTop.hom) :=
      Ideal.isScalarTower_of_sq_eq_bot (IsFirstOrderThickening.ker_appTop_sq_eq_bot _)
    letI : IsScalarTower Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤) (RingHom.ker (i ∣_ W').appTop.hom) :=
      Ideal.isScalarTower_of_sq_eq_bot (IsFirstOrderThickening.ker_appTop_sq_eq_bot _)
    letI := liftStructAddTorsor (commSq_resLE w hU hV hUV)
    letI := liftStructAddTorsor (commSq_resLE w ((i.preimage_mono e).trans hU) (e.trans hV) hUV)
    liftSheafObjEquivLiftStruct w ((i.preimage_mono e).trans hU) (e.trans hV) hUV
        ((liftSheaf f i a h).obj.map (homOfLE e).op
          ((liftSheafObjEquivLiftStruct w hU hV hUV).symm
            (d +ᵥ liftSheafObjEquivLiftStruct w hU hV hUV l))) =
      (kerAppTopLinearMap (T'.homOfLE e) (morphismRestrict_homOfLE i W' W e).symm
          (Scheme.Hom.map_resLE _ _ _)).compDer d +ᵥ
        liftSheafObjEquivLiftStruct w ((i.preimage_mono e).trans hU) (e.trans hV) hUV
          ((liftSheaf f i a h).obj.map (homOfLE e).op l) := by
  let := liftStructAddTorsor (commSq_resLE w hU hV hUV)
  let := liftStructAddTorsor (commSq_resLE w ((i.preimage_mono e).trans hU) (e.trans hV) hUV)
  refine (liftSheafObjEquivLiftStruct_map w hU hV hUV e _).trans ?_
  rw [Equiv.apply_symm_apply]
  exact (liftStructAddTorsor_precomp_vadd (commSq_resLE w hU hV hUV) _ _ _ _ d _).trans
    (congrArg (_ +ᵥ ·) (liftSheafObjEquivLiftStruct_map w hU hV hUV e l).symm)

/-- Restriction of sections of the sheaf of lifts from an affine open `W` to a smaller affine open
`W' ⊆ W` is compatible with differences: the restrictions of `l₁` and `l₂` differ by the
restriction of the derivation `l₁ -ᵥ l₂` along `Γ(W, ⊤) ⟶ Γ(W', ⊤)`. -/
theorem liftSheafObjEquivLiftStruct_map_vsub (w : a ≫ f = i ≫ h) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V) (e : W' ≤ W)
    [(commSq_resLE w hU hV hUV).HasLift]
    [(commSq_resLE w ((i.preimage_mono e).trans hU) (e.trans hV) hUV).HasLift]
    (l₁ l₂ : (liftSheaf f i a h).obj.obj (op W)) :
    letI := (f.resLE V U hUV).appTop.hom.toAlgebra
    letI := (h.resLE V W hV).appTop.hom.toAlgebra
    letI := (h.resLE V W' (e.trans hV)).appTop.hom.toAlgebra
    letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
    letI := quotientKerAppTopAlgebra (i ∣_ W') (a.resLE U (i ⁻¹ᵁ W') ((i.preimage_mono e).trans hU))
    letI := isScalarTower_quotientKerAppTopAlgebra (commSq_resLE w hU hV hUV)
    letI := isScalarTower_quotientKerAppTopAlgebra
      (commSq_resLE w ((i.preimage_mono e).trans hU) (e.trans hV) hUV)
    letI := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
    letI := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W'))
    letI : IsScalarTower Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤) (RingHom.ker (i ∣_ W).appTop.hom) :=
      Ideal.isScalarTower_of_sq_eq_bot (IsFirstOrderThickening.ker_appTop_sq_eq_bot _)
    letI : IsScalarTower Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤) (RingHom.ker (i ∣_ W').appTop.hom) :=
      Ideal.isScalarTower_of_sq_eq_bot (IsFirstOrderThickening.ker_appTop_sq_eq_bot _)
    letI := liftStructAddTorsor (commSq_resLE w hU hV hUV)
    letI := liftStructAddTorsor (commSq_resLE w ((i.preimage_mono e).trans hU) (e.trans hV) hUV)
    liftSheafObjEquivLiftStruct w ((i.preimage_mono e).trans hU) (e.trans hV) hUV
        ((liftSheaf f i a h).obj.map (homOfLE e).op l₁) -ᵥ
      liftSheafObjEquivLiftStruct w ((i.preimage_mono e).trans hU) (e.trans hV) hUV
        ((liftSheaf f i a h).obj.map (homOfLE e).op l₂) =
      (kerAppTopLinearMap (T'.homOfLE e) (morphismRestrict_homOfLE i W' W e).symm
          (Scheme.Hom.map_resLE _ _ _)).compDer
        (liftSheafObjEquivLiftStruct w hU hV hUV l₁ -ᵥ
          liftSheafObjEquivLiftStruct w hU hV hUV l₂) := by
  let := liftStructAddTorsor (commSq_resLE w hU hV hUV)
  let := liftStructAddTorsor (commSq_resLE w ((i.preimage_mono e).trans hU) (e.trans hV) hUV)
  exact (congrArg₂ (· -ᵥ ·) (liftSheafObjEquivLiftStruct_map w hU hV hUV e l₁)
    (liftSheafObjEquivLiftStruct_map w hU hV hUV e l₂)).trans
      (liftStructAddTorsor_precomp_vsub (commSq_resLE w hU hV hUV) _ _ _ _ _ _)

omit [IsAffine W'.toScheme] in
/-- The difference of two sections of the sheaf of lifts over an affine open `W` does not depend on
the affine opens `U ⊆ X` and `V ⊆ S` used to read the sections as lifts: for affine opens
`U' ⊆ U` and `V'` of the same kind, the derivation `Γ(U, ⊤) → Γ(W, ⊤)` read through `U` is the one
read through `U'` composed with the restriction `Γ(U, ⊤) ⟶ Γ(U', ⊤)`. -/
theorem liftSheafObjEquivLiftStruct_vsub_apply_homOfLE [IsAffine U'.toScheme]
    [IsAffine V'.toScheme] (w : a ≫ f = i ≫ h) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (hV : W ≤ h ⁻¹ᵁ V)
    (hUV : U ≤ f ⁻¹ᵁ V) (hU' : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U') (hV' : W ≤ h ⁻¹ᵁ V') (hUV' : U' ≤ f ⁻¹ᵁ V')
    (e : U' ≤ U) [(commSq_resLE w hU hV hUV).HasLift] [(commSq_resLE w hU' hV' hUV').HasLift]
    (l₁ l₂ : (liftSheaf f i a h).obj.obj (op W)) (x : Γ(U.toScheme, ⊤)) :
    letI := liftStructAddTorsor (commSq_resLE w hU hV hUV)
    letI := liftStructAddTorsor (commSq_resLE w hU' hV' hUV')
    ((liftSheafObjEquivLiftStruct w hU hV hUV l₁ -ᵥ liftSheafObjEquivLiftStruct w hU hV hUV l₂) x :
        Γ(W.toScheme, ⊤)) =
      (liftSheafObjEquivLiftStruct w hU' hV' hUV' l₁ -ᵥ
        liftSheafObjEquivLiftStruct w hU' hV' hUV' l₂) ((X.homOfLE e).appTop x) := by
  simp only [liftStructAddTorsor_vsub_apply,
    ← liftSheafObjEquivLiftStruct_apply_l_homOfLE w hU hV hUV hU' hV' hUV' e,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

end TauCeti.AlgebraicGeometry
