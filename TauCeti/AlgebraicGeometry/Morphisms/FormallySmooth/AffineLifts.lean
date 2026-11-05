/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineScheme
public import TauCeti.AlgebraicGeometry.Morphisms.Thickening
public import TauCeti.CategoryTheory.CommSq
public import TauCeti.RingTheory.Derivation.ToSquareZero

/-!
# Lifts in a square of affine schemes

Let `i : T ⟶ T'` be a closed immersion into an affine scheme, with ideal `I` of global sections
(the kernel of `i.appTop`), and consider a commutative square `g ≫ f = i ≫ h` with `X` and `S`
affine. A lift `l : T' ⟶ X` of `g` along `i` over `S` is determined by the ring map
`l.appTop : Γ(X, ⊤) ⟶ Γ(T', ⊤)`, so the lifts are the `Γ(S, ⊤)`-algebra lifts
`Γ(X, ⊤) →ₐ Γ(T', ⊤)` of `Γ(X, ⊤) → Γ(T, ⊤) = Γ(T', ⊤) ⧸ I`, that is,
`Ideal.LiftOfQuotient I Γ(S, ⊤) Γ(X, ⊤)`.

When `i` is a first-order thickening, `I ^ 2 = ⊥`, and the lifts, if there are any, form a torsor
under the derivations `Der_{Γ(S, ⊤)}(Γ(X, ⊤), I)`. This is the affine case of the torsor of lifts
of Stacks, Lemma 37.9.5 (04FJ), with `Hom(g^* Ω_{X/S}, I) = Der_{Γ(S, ⊤)}(Γ(X, ⊤), I)`. The torsor
is natural in the thickening: along a map of first-order thickenings, for instance the restriction
to a smaller affine open, precomposition of lifts is equivariant for the induced map of
derivations.

## Main definitions

* `TauCeti.AlgebraicGeometry.quotientKerAppTopAlgebra i g`: the `Γ(X, ⊤)`-algebra structure on
  `Γ(T', ⊤) ⧸ ker i.appTop` given by `g`.
* `TauCeti.AlgebraicGeometry.liftStructEquivLiftOfQuotient`: the lifts in an affine square are the
  algebra lifts of the map on global sections.
* `TauCeti.AlgebraicGeometry.liftStructAddTorsor`: along a first-order thickening of an affine
  scheme, the lifts in a square of affine schemes form a torsor under derivations.
* `TauCeti.AlgebraicGeometry.kerAppTopLinearMap`: a map of first-order thickenings into affine
  schemes induces a `Γ(X, ⊤)`-linear map of their square-zero ideals of global sections.

## Main results

* `TauCeti.AlgebraicGeometry.liftStructAddTorsor_precomp_vsub`,
  `TauCeti.AlgebraicGeometry.liftStructAddTorsor_precomp_vadd`: precomposing lifts along a map of
  first-order thickenings is equivariant for `liftStructAddTorsor`.

## References

* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ).
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {X S T T' : Scheme.{u}} {f : X ⟶ S} (i : T ⟶ T') (g : T ⟶ X) {h : T' ⟶ S}
  [IsAffine T']

section IsClosedImmersion

variable [IsClosedImmersion i]

/-- For a closed immersion `i : T ⟶ T'` into an affine scheme, the map `g : T ⟶ X` makes
`Γ(T', ⊤) ⧸ ker i.appTop ≃ Γ(T, ⊤)` a `Γ(X, ⊤)`-algebra. -/
noncomputable abbrev quotientKerAppTopAlgebra :
    Algebra Γ(X, ⊤) (Γ(T', ⊤) ⧸ RingHom.ker i.appTop.hom) :=
  ((RingHom.quotientKerEquivOfSurjective
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2).symm.toRingHom.comp
      g.appTop.hom).toAlgebra

/-- Under `quotientKerAppTopAlgebra i g`, the map `Γ(X, ⊤) → Γ(T', ⊤) ⧸ ker i.appTop` followed by
`Γ(T', ⊤) ⧸ ker i.appTop ≃ Γ(T, ⊤)` is `g.appTop`. -/
theorem quotientKerAppTopAlgebra_algebraMap (x : Γ(X, ⊤)) :
    letI := quotientKerAppTopAlgebra i g
    RingHom.quotientKerEquivOfSurjective (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
      (algebraMap Γ(X, ⊤) (Γ(T', ⊤) ⧸ RingHom.ker i.appTop.hom) x) = g.appTop x :=
  RingEquiv.apply_symm_apply _ _

/-- Under `quotientKerAppTopAlgebra i g`, `b : Γ(T', ⊤)` reduces to the image of `x : Γ(X, ⊤)`
modulo `ker i.appTop` exactly when `i.appTop b = g.appTop x`. -/
theorem quotientKerAppTopAlgebra_mk_eq_algebraMap_iff (b : Γ(T', ⊤)) (x : Γ(X, ⊤)) :
    letI := quotientKerAppTopAlgebra i g
    Ideal.Quotient.mk (RingHom.ker i.appTop.hom) b =
      algebraMap Γ(X, ⊤) (Γ(T', ⊤) ⧸ RingHom.ker i.appTop.hom) x ↔ i.appTop b = g.appTop x := by
  let := quotientKerAppTopAlgebra i g
  rw [← (RingHom.quotientKerEquivOfSurjective
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2).injective.eq_iff,
    quotientKerAppTopAlgebra_algebraMap, RingHom.quotientKerEquivOfSurjective_apply_mk]

variable {i g}

/-- In a commutative square `g ≫ f = i ≫ h`, the algebra structures on `Γ(X, ⊤)` and on
`Γ(T', ⊤)` given by `f` and `h` are compatible with `quotientKerAppTopAlgebra i g`. -/
theorem isScalarTower_quotientKerAppTopAlgebra (sq : CommSq g i f h) :
    letI := f.appTop.hom.toAlgebra
    letI := h.appTop.hom.toAlgebra
    letI := quotientKerAppTopAlgebra i g
    IsScalarTower Γ(S, ⊤) Γ(X, ⊤) (Γ(T', ⊤) ⧸ RingHom.ker i.appTop.hom) := by
  let := f.appTop.hom.toAlgebra
  let := h.appTop.hom.toAlgebra
  let := quotientKerAppTopAlgebra i g
  refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
  change Ideal.Quotient.mk _ (h.appTop r) = algebraMap Γ(X, ⊤) _ (f.appTop r)
  rw [quotientKerAppTopAlgebra_mk_eq_algebraMap_iff, ← CommRingCat.comp_apply,
    ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, sq.w]

variable [IsAffine X] [IsAffine S]

/-- The lifts in a commutative square `g ≫ f = i ≫ h` of a closed immersion `i` into an affine
scheme, with `X` and `S` affine, are the `Γ(S, ⊤)`-algebra lifts `Γ(X, ⊤) →ₐ Γ(T', ⊤)` of
`Γ(X, ⊤) → Γ(T', ⊤) ⧸ ker i.appTop` (`quotientKerAppTopAlgebra`): a lift `l` corresponds to
`l.appTop`. -/
noncomputable def liftStructEquivLiftOfQuotient (sq : CommSq g i f h) :
    letI := f.appTop.hom.toAlgebra
    letI := h.appTop.hom.toAlgebra
    letI := quotientKerAppTopAlgebra i g
    haveI := isScalarTower_quotientKerAppTopAlgebra sq
    sq.LiftStruct ≃ Ideal.LiftOfQuotient (RingHom.ker i.appTop.hom) Γ(S, ⊤) Γ(X, ⊤) :=
  letI := f.appTop.hom.toAlgebra
  letI := h.appTop.hom.toAlgebra
  letI := quotientKerAppTopAlgebra i g
  haveI := isScalarTower_quotientKerAppTopAlgebra sq
  { toFun l := ⟨
      { l.l.appTop.hom with
        commutes' r := by
          change (f.appTop ≫ l.l.appTop) r = h.appTop r
          rw [← Scheme.Hom.comp_appTop, l.fac_right] },
      AlgHom.ext fun x ↦ (quotientKerAppTopAlgebra_mk_eq_algebraMap_iff i g _ x).2 <| by
        change (l.l.appTop ≫ i.appTop) x = g.appTop x
        rw [← Scheme.Hom.comp_appTop, l.fac_left]⟩
    invFun φ :=
      { l := T'.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.1.toRingHom) ≫ X.isoSpec.inv
        fac_left := ext_of_isAffine <| by
          rw [Scheme.Hom.comp_appTop, toSpecΓ_SpecMap_isoSpec_inv_appTop]
          ext x
          exact (quotientKerAppTopAlgebra_mk_eq_algebraMap_iff i g _ x).1 (φ.mk_apply x)
        fac_right := ext_of_isAffine <| by
          rw [Scheme.Hom.comp_appTop, toSpecΓ_SpecMap_isoSpec_inv_appTop]
          ext r
          exact φ.1.commutes r }
    left_inv l := CommSq.LiftStruct.ext <| ext_of_isAffine <| by
      exact toSpecΓ_SpecMap_isoSpec_inv_appTop _
    right_inv φ := Subtype.ext <| AlgHom.ext fun x ↦ by
      change (T'.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.1.toRingHom) ≫ X.isoSpec.inv).appTop x =
        φ.1 x
      rw [toSpecΓ_SpecMap_isoSpec_inv_appTop]
      rfl }

@[simp]
theorem liftStructEquivLiftOfQuotient_apply_apply (sq : CommSq g i f h) (l : sq.LiftStruct)
    (x : Γ(X, ⊤)) : (liftStructEquivLiftOfQuotient sq l).1 x = l.l.appTop x :=
  (rfl)

end IsClosedImmersion

variable {i g} [IsAffine X] [IsAffine S]

/-- Along a first-order thickening `i` of an affine scheme, the lifts in a commutative square
`g ≫ f = i ≫ h` with `X` and `S` affine, if there is one, form a torsor under the
`Γ(S, ⊤)`-derivations `Γ(X, ⊤) → ker i.appTop`, where the square-zero ideal `ker i.appTop` is a
`Γ(X, ⊤)`-module through `g` (`Ideal.moduleOfSqEqBot`): a derivation `d` sends a lift `l` to the
lift with `appTop` equal to `d + l.appTop`, and two lifts differ by the derivation
`l₁.appTop - l₂.appTop`. This is the affine case of Stacks, Lemma 37.9.5 (04FJ). -/
@[reducible]
noncomputable def liftStructAddTorsor [IsFirstOrderThickening i] (sq : CommSq g i f h)
    [sq.HasLift] :
    letI := f.appTop.hom.toAlgebra
    letI := h.appTop.hom.toAlgebra
    letI := quotientKerAppTopAlgebra i g
    letI := Ideal.moduleOfSqEqBot Γ(X, ⊤) (IsFirstOrderThickening.ker_appTop_sq_eq_bot i)
    AddTorsor (Derivation Γ(S, ⊤) Γ(X, ⊤) (RingHom.ker i.appTop.hom)) sq.LiftStruct :=
  letI := f.appTop.hom.toAlgebra
  letI := h.appTop.hom.toAlgebra
  letI := quotientKerAppTopAlgebra i g
  haveI := isScalarTower_quotientKerAppTopAlgebra sq
  letI := Ideal.moduleOfSqEqBot Γ(X, ⊤) (IsFirstOrderThickening.ker_appTop_sq_eq_bot i)
  let e := liftStructEquivLiftOfQuotient sq
  haveI : Nonempty (Ideal.LiftOfQuotient (RingHom.ker i.appTop.hom) Γ(S, ⊤) Γ(X, ⊤)) :=
    ((CommSq.HasLift.iff sq).1 inferInstance).map e
  letI : AddTorsor (Derivation Γ(S, ⊤) Γ(X, ⊤) (RingHom.ker i.appTop.hom))
      (Ideal.LiftOfQuotient (RingHom.ker i.appTop.hom) Γ(S, ⊤) Γ(X, ⊤)) :=
    Ideal.derivationToSquareZeroAddTorsor (IsFirstOrderThickening.ker_appTop_sq_eq_bot i)
  letI vadd : VAdd (Derivation Γ(S, ⊤) Γ(X, ⊤) (RingHom.ker i.appTop.hom)) sq.LiftStruct :=
    ⟨fun d l ↦ e.symm (d +ᵥ e l)⟩
  { vadd with
    vsub l₁ l₂ := e l₁ -ᵥ e l₂
    zero_vadd l := e.symm_apply_eq.2 (zero_vadd _ (e l))
    add_vadd d₁ d₂ l := congrArg e.symm <| (add_vadd d₁ d₂ (e l)).trans
      (congrArg (d₁ +ᵥ ·) (e.apply_symm_apply (d₂ +ᵥ e l)).symm)
    nonempty := (CommSq.HasLift.iff sq).1 inferInstance
    vsub_vadd' l₁ l₂ := e.symm_apply_eq.2 (vsub_vadd (e l₁) (e l₂))
    vadd_vsub' d l := (congrArg (· -ᵥ e l) (e.apply_symm_apply (d +ᵥ e l))).trans
      (vadd_vsub d (e l)) }

/-- A derivation `d` acts on a lift `l` by `d + l.appTop` on global sections. -/
theorem liftStructAddTorsor_vadd_l_appTop [IsFirstOrderThickening i] (sq : CommSq g i f h)
    [sq.HasLift]
    (d : letI := f.appTop.hom.toAlgebra
      letI := h.appTop.hom.toAlgebra
      letI := quotientKerAppTopAlgebra i g
      letI := Ideal.moduleOfSqEqBot Γ(X, ⊤) (IsFirstOrderThickening.ker_appTop_sq_eq_bot i)
      Derivation Γ(S, ⊤) Γ(X, ⊤) (RingHom.ker i.appTop.hom))
    (l : sq.LiftStruct) (x : Γ(X, ⊤)) :
    letI := liftStructAddTorsor sq
    (d +ᵥ l).l.appTop x = d x + l.l.appTop x := by
  change (T'.toSpecΓ ≫ Spec.map _ ≫ X.isoSpec.inv).appTop x = _
  rw [toSpecΓ_SpecMap_isoSpec_inv_appTop]
  rfl

/-- Two lifts `l₁`, `l₂` differ by the derivation `l₁.appTop - l₂.appTop`. -/
theorem liftStructAddTorsor_vsub_apply [IsFirstOrderThickening i] (sq : CommSq g i f h)
    [sq.HasLift] (l₁ l₂ : sq.LiftStruct) (x : Γ(X, ⊤)) :
    letI := liftStructAddTorsor sq
    ((l₁ -ᵥ l₂) x : Γ(T', ⊤)) = l₁.l.appTop x - l₂.l.appTop x :=
  (rfl)

section Naturality

variable {T₂ T₂' : Scheme.{u}} [IsAffine T₂'] {i₂ : T₂ ⟶ T₂'} {g₂ : T₂ ⟶ X} {h₂ : T₂' ⟶ S}
  {φ : T₂' ⟶ T'} {ψ : T₂ ⟶ T}

omit [IsAffine X] in
variable (φ) in
/-- Along a map `(ψ, φ)` from the first-order thickening `i₂` to `i` (`ψ ≫ i = i₂ ≫ φ`), with
`ψ ≫ g = g₂`, the map `φ.appTop` restricts to a `Γ(X, ⊤)`-linear map
`ker i.appTop ⟶ ker i₂.appTop` of square-zero ideals, which are `Γ(X, ⊤)`-modules through `g` and
`g₂` (`Ideal.moduleOfSqEqBot`). -/
@[expose]
noncomputable def kerAppTopLinearMap [IsFirstOrderThickening i] [IsFirstOrderThickening i₂]
    (hψ : ψ ≫ i = i₂ ≫ φ) (hg : ψ ≫ g = g₂) :
    letI := quotientKerAppTopAlgebra i g
    letI := quotientKerAppTopAlgebra i₂ g₂
    letI := Ideal.moduleOfSqEqBot Γ(X, ⊤) (IsFirstOrderThickening.ker_appTop_sq_eq_bot i)
    letI := Ideal.moduleOfSqEqBot Γ(X, ⊤) (IsFirstOrderThickening.ker_appTop_sq_eq_bot i₂)
    RingHom.ker i.appTop.hom →ₗ[Γ(X, ⊤)] RingHom.ker i₂.appTop.hom :=
  letI := quotientKerAppTopAlgebra i g
  letI := quotientKerAppTopAlgebra i₂ g₂
  letI := Ideal.moduleOfSqEqBot Γ(X, ⊤) (IsFirstOrderThickening.ker_appTop_sq_eq_bot i)
  letI := Ideal.moduleOfSqEqBot Γ(X, ⊤) (IsFirstOrderThickening.ker_appTop_sq_eq_bot i₂)
  have hφ (b : Γ(T', ⊤)) : i₂.appTop (φ.appTop b) = ψ.appTop (i.appTop b) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, hψ]
  { toFun m := ⟨φ.appTop m, by
      change i₂.appTop (φ.appTop m) = 0
      rw [hφ, show i.appTop (m : Γ(T', ⊤)) = 0 from m.2, map_zero]⟩
    map_add' m n := Subtype.ext (map_add _ _ _)
    map_smul' a m := Subtype.ext <| by
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
        (algebraMap Γ(X, ⊤) (Γ(T', ⊤) ⧸ RingHom.ker i.appTop.hom) a)
      have hb₂ : Ideal.Quotient.mk (RingHom.ker i₂.appTop.hom) (φ.appTop b) =
          algebraMap Γ(X, ⊤) (Γ(T₂', ⊤) ⧸ RingHom.ker i₂.appTop.hom) a := by
        rw [quotientKerAppTopAlgebra_mk_eq_algebraMap_iff, hφ,
          (quotientKerAppTopAlgebra_mk_eq_algebraMap_iff i g b a).1 hb, ← hg,
          Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      rw [RingHom.id_apply, Ideal.coe_smul_of_sq_eq_bot _ hb₂]
      change φ.appTop ((a • m : RingHom.ker i.appTop.hom) : Γ(T', ⊤)) = _
      rw [Ideal.coe_smul_of_sq_eq_bot _ hb, map_mul] }

omit [IsAffine X] in
@[simp]
theorem coe_kerAppTopLinearMap_apply [IsFirstOrderThickening i] [IsFirstOrderThickening i₂]
    (hψ : ψ ≫ i = i₂ ≫ φ) (hg : ψ ≫ g = g₂) (m : RingHom.ker i.appTop.hom) :
    (kerAppTopLinearMap φ hψ hg m : Γ(T₂', ⊤)) = φ.appTop m :=
  rfl

/-- Along a map `(ψ, φ)` from the first-order thickening `i₂` to `i` (`ψ ≫ i = i₂ ≫ φ`), the
difference of the precomposed lifts `φ ≫ l₁` and `φ ≫ l₂` is the image of `l₁ -ᵥ l₂` under
`φ.appTop`: the torsors of lifts of `liftStructAddTorsor` are compatible with base change of the
thickening, for instance with restriction to a smaller affine open. -/
theorem liftStructAddTorsor_precomp_vsub_apply [IsFirstOrderThickening i]
    [IsFirstOrderThickening i₂] (sq : CommSq g i f h) [sq.HasLift] (hψ : ψ ≫ i = i₂ ≫ φ)
    (hg : ψ ≫ g = g₂) (hh : φ ≫ h = h₂) (sq₂ : CommSq g₂ i₂ f h₂) [sq₂.HasLift]
    (l₁ l₂ : sq.LiftStruct) (x : Γ(X, ⊤)) :
    letI := liftStructAddTorsor sq
    letI := liftStructAddTorsor sq₂
    ((l₁.precomp hψ hg hh sq₂ -ᵥ l₂.precomp hψ hg hh sq₂) x : Γ(T₂', ⊤)) =
      φ.appTop ((l₁ -ᵥ l₂) x : Γ(T', ⊤)) := by
  simp only [liftStructAddTorsor_vsub_apply, CommSq.LiftStruct.precomp_l, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, map_sub]

/-- Along a map `(ψ, φ)` from the first-order thickening `i₂` to `i` (`ψ ≫ i = i₂ ≫ φ`), the
difference of the precomposed lifts `φ ≫ l₁` and `φ ≫ l₂` is the derivation `l₁ -ᵥ l₂` composed with
`kerAppTopLinearMap φ hψ hg`. -/
theorem liftStructAddTorsor_precomp_vsub [IsFirstOrderThickening i]
    [IsFirstOrderThickening i₂] (sq : CommSq g i f h) [sq.HasLift] (hψ : ψ ≫ i = i₂ ≫ φ)
    (hg : ψ ≫ g = g₂) (hh : φ ≫ h = h₂) (sq₂ : CommSq g₂ i₂ f h₂) [sq₂.HasLift]
    (l₁ l₂ : sq.LiftStruct) :
    letI := f.appTop.hom.toAlgebra
    letI := h.appTop.hom.toAlgebra
    letI := h₂.appTop.hom.toAlgebra
    letI := quotientKerAppTopAlgebra i g
    letI := quotientKerAppTopAlgebra i₂ g₂
    haveI := isScalarTower_quotientKerAppTopAlgebra sq
    haveI := isScalarTower_quotientKerAppTopAlgebra sq₂
    letI := Ideal.moduleOfSqEqBot Γ(X, ⊤) (IsFirstOrderThickening.ker_appTop_sq_eq_bot i)
    letI := Ideal.moduleOfSqEqBot Γ(X, ⊤) (IsFirstOrderThickening.ker_appTop_sq_eq_bot i₂)
    haveI : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) (RingHom.ker i.appTop.hom) :=
      Ideal.isScalarTower_of_sq_eq_bot (IsFirstOrderThickening.ker_appTop_sq_eq_bot i)
    haveI : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) (RingHom.ker i₂.appTop.hom) :=
      Ideal.isScalarTower_of_sq_eq_bot (IsFirstOrderThickening.ker_appTop_sq_eq_bot i₂)
    letI := liftStructAddTorsor sq
    letI := liftStructAddTorsor sq₂
    l₁.precomp hψ hg hh sq₂ -ᵥ l₂.precomp hψ hg hh sq₂ =
      (kerAppTopLinearMap φ hψ hg).compDer (l₁ -ᵥ l₂) := by
  let := f.appTop.hom.toAlgebra
  let := h₂.appTop.hom.toAlgebra
  let := quotientKerAppTopAlgebra i₂ g₂
  let := Ideal.moduleOfSqEqBot Γ(X, ⊤) (IsFirstOrderThickening.ker_appTop_sq_eq_bot i₂)
  apply Derivation.ext
  intro x
  apply Subtype.ext
  exact liftStructAddTorsor_precomp_vsub_apply sq hψ hg hh sq₂ l₁ l₂ x

/-- Along a map `(ψ, φ)` from the first-order thickening `i₂` to `i` (`ψ ≫ i = i₂ ≫ φ`),
precomposing with `φ` sends `d +ᵥ l` to `d' +ᵥ (φ ≫ l)`, where `d'` is `d` composed with
`kerAppTopLinearMap φ hψ hg`. -/
theorem liftStructAddTorsor_precomp_vadd [IsFirstOrderThickening i]
    [IsFirstOrderThickening i₂] (sq : CommSq g i f h) [sq.HasLift] (hψ : ψ ≫ i = i₂ ≫ φ)
    (hg : ψ ≫ g = g₂) (hh : φ ≫ h = h₂) (sq₂ : CommSq g₂ i₂ f h₂) [sq₂.HasLift]
    (d : letI := f.appTop.hom.toAlgebra
      letI := h.appTop.hom.toAlgebra
      letI := quotientKerAppTopAlgebra i g
      letI := Ideal.moduleOfSqEqBot Γ(X, ⊤) (IsFirstOrderThickening.ker_appTop_sq_eq_bot i)
      Derivation Γ(S, ⊤) Γ(X, ⊤) (RingHom.ker i.appTop.hom)) (l : sq.LiftStruct) :
    letI := f.appTop.hom.toAlgebra
    letI := h.appTop.hom.toAlgebra
    letI := h₂.appTop.hom.toAlgebra
    letI := quotientKerAppTopAlgebra i g
    letI := quotientKerAppTopAlgebra i₂ g₂
    haveI := isScalarTower_quotientKerAppTopAlgebra sq
    haveI := isScalarTower_quotientKerAppTopAlgebra sq₂
    letI := Ideal.moduleOfSqEqBot Γ(X, ⊤) (IsFirstOrderThickening.ker_appTop_sq_eq_bot i)
    letI := Ideal.moduleOfSqEqBot Γ(X, ⊤) (IsFirstOrderThickening.ker_appTop_sq_eq_bot i₂)
    haveI : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) (RingHom.ker i.appTop.hom) :=
      Ideal.isScalarTower_of_sq_eq_bot (IsFirstOrderThickening.ker_appTop_sq_eq_bot i)
    haveI : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) (RingHom.ker i₂.appTop.hom) :=
      Ideal.isScalarTower_of_sq_eq_bot (IsFirstOrderThickening.ker_appTop_sq_eq_bot i₂)
    letI := liftStructAddTorsor sq
    letI := liftStructAddTorsor sq₂
    (d +ᵥ l).precomp hψ hg hh sq₂ =
      (kerAppTopLinearMap φ hψ hg).compDer d +ᵥ l.precomp hψ hg hh sq₂ := by
  let := liftStructAddTorsor sq
  let := liftStructAddTorsor sq₂
  rw [eq_vadd_iff_vsub_eq, liftStructAddTorsor_precomp_vsub, vadd_vsub]

end Naturality

end TauCeti.AlgebraicGeometry
