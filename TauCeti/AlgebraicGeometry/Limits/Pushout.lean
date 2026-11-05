/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import TauCeti.AlgebraicGeometry.Restrict
public import TauCeti.AlgebraicGeometry.Gluing.PushoutMap
public import TauCeti.AlgebraicGeometry.Limits.Existence

/-!
# Cofiltered limits of gluings along opens

Let `Uf ⟵ Vf ⟶ Sf` be a span of cofiltered diagrams of schemes whose components `α`, `β` are
open immersions with pullback naturality squares, and whose transition maps are affine. Let `X`
be covered by opens `U` and `W` such that `U = lim Uf` and `W = lim Sf`, compatibly with cones
`U ⊓ W ⟶ Vf` exhibiting `U ⊓ W` as the preimage of `Vf` in `U` and in `W`. Then `X` is the limit
of the gluings `Uf a ∪_{Vf a} Sf a` (`TauCeti.AlgebraicGeometry.Scheme.pushoutFunctor`).

This is how the models of the two halves of `X` are glued in the extension step of absolute
Noetherian approximation (Stacks, Proposition 32.5.4 (01ZA)).

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.pushoutFunctorCone`: the cone with point `X` on the gluings.
* `TauCeti.AlgebraicGeometry.Scheme.isLimitPushoutFunctorCone`: it is a limit cone.
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {Λ : Type u} [Category.{u} Λ] {Vf Uf Sf : Λ ⥤ Scheme.{u}} (α : Vf ⟶ Uf) (β : Vf ⟶ Sf)
  [∀ a, IsOpenImmersion (α.app a)] [∀ a, IsOpenImmersion (β.app a)] {X : Scheme.{u}}
  {U W : X.Opens} (hUW : U ⊔ W = ⊤) {πU : (Functor.const Λ).obj U.toScheme ⟶ Uf}
  {πW : (Functor.const Λ).obj W.toScheme ⟶ Sf} {πV : (Functor.const Λ).obj (U ⊓ W).toScheme ⟶ Vf}
  (hVU : ∀ a, πV.app a ≫ α.app a = X.homOfLE inf_le_left ≫ πU.app a)
  (hVW : ∀ a, πV.app a ≫ β.app a = X.homOfLE inf_le_right ≫ πW.app a)

/-- For `X` covered by opens `U` and `W` with cones `U ⟶ Uf`, `W ⟶ Sf` compatible along
`U ⊓ W ⟶ Vf`, the cone with point `X` on the gluings `Uf a ∪_{Vf a} Sf a`. -/
noncomputable def pushoutFunctorCone : Cone (pushoutFunctor α β) where
  pt := X
  π.app a := (isPushout_opens_of_sup_eq_top hUW).desc (W := pushout (α.app a) (β.app a))
    (πU.app a ≫ pushout.inl _ _) (πW.app a ≫ pushout.inr _ _) (by
      rw [← Category.assoc, ← hVU a, Category.assoc, pushout.condition, ← Category.assoc,
        hVW a, Category.assoc])
  π.naturality a b f := by
    refine (isPushout_opens_of_sup_eq_top hUW).hom_ext ?_ ?_
    -- `(pushoutFunctor α β).obj a` is `pushout (α.app a) (β.app a)` only after unfolding, so the
    -- lemmas about `pushout.inl`/`pushout.inr` are rewritten with `erw`.
    · have h := πU.naturality f
      dsimp at h ⊢
      simp only [Category.id_comp] at h
      erw [Category.id_comp, IsPushout.inl_desc, IsPushout.inl_desc_assoc]
      erw [Category.assoc, pushout_inl_pushoutFunctor_map]
      rw [h, Category.assoc]
      rfl
    · have h := πW.naturality f
      dsimp at h ⊢
      simp only [Category.id_comp] at h
      erw [Category.id_comp, IsPushout.inr_desc, IsPushout.inr_desc_assoc]
      erw [Category.assoc, pushout_inr_pushoutFunctor_map]
      rw [h, Category.assoc]
      rfl

@[reassoc (attr := simp)]
lemma ι_pushoutFunctorCone_π_app_left (a : Λ) :
    U.ι ≫ (pushoutFunctorCone α β hUW hVU hVW).π.app a = πU.app a ≫ pushout.inl _ _ :=
  IsPushout.inl_desc _ _ _ _

@[reassoc (attr := simp)]
lemma ι_pushoutFunctorCone_π_app_right (a : Λ) :
    W.ι ≫ (pushoutFunctorCone α β hUW hVU hVW).π.app a = πW.app a ≫ pushout.inr _ _ :=
  IsPushout.inr_desc _ _ _ _

/-- The open immersions `Uf a ⟶ Uf a ∪_{Vf a} Sf a`, as a natural transformation. -/
@[simps]
noncomputable def pushoutFunctorInl : Uf ⟶ pushoutFunctor α β where
  app a := pushout.inl (α.app a) (β.app a)
  naturality _ _ f := (pushout_inl_pushoutFunctor_map α β f).symm

/-- The open immersions `Sf a ⟶ Uf a ∪_{Vf a} Sf a`, as a natural transformation. -/
@[simps]
noncomputable def pushoutFunctorInr : Sf ⟶ pushoutFunctor α β where
  app a := pushout.inr (α.app a) (β.app a)
  naturality _ _ f := (pushout_inr_pushoutFunctor_map α β f).symm

instance (a : Λ) : IsOpenImmersion ((pushoutFunctorInl α β).app a) :=
  inferInstanceAs (IsOpenImmersion (pushout.inl (α.app a) (β.app a)))

instance (a : Λ) : IsOpenImmersion ((pushoutFunctorInr α β).app a) :=
  inferInstanceAs (IsOpenImmersion (pushout.inr (α.app a) (β.app a)))

/-- A morphism `φ : X ⟶ L` is an isomorphism if it restricts to open immersions on opens `U` and
`W` of `X` whose images cover `L`, with `U` and `W` the preimages of their images. -/
theorem isIso_of_isOpenImmersion_ι_comp {X L : Scheme.{u}} (φ : X ⟶ L) {U W : X.Opens}
    [IsOpenImmersion (U.ι ≫ φ)] [IsOpenImmersion (W.ι ≫ φ)]
    (hcov : (U.ι ≫ φ).opensRange ⊔ (W.ι ≫ φ).opensRange = ⊤)
    (hU : φ ⁻¹ᵁ (U.ι ≫ φ).opensRange = U) (hW : φ ⁻¹ᵁ (W.ι ≫ φ).opensRange = W) : IsIso φ := by
  -- Over the image of `O.ι ≫ φ`, the base change of `φ` is `𝟙 O`.
  have key (O : X.Opens) [IsOpenImmersion (O.ι ≫ φ)] (hO : φ ⁻¹ᵁ (O.ι ≫ φ).opensRange = O) :
      MorphismProperty.isomorphisms Scheme (φ ∣_ (O.ι ≫ φ).opensRange) := by
    refine (MorphismProperty.arrow_mk_iso_iff _ (morphismRestrictOpensRange _ _)).mpr ?_
    have h := IsOpenImmersion.isPullback (𝟙 _) O.ι (O.ι ≫ φ) φ (Category.id_comp _).symm
      (by rw [hO, Scheme.Opens.opensRange_ι])
    rw [MorphismProperty.isomorphisms.iff, ← h.flip.isoPullback_inv_snd]
    infer_instance
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun b : Bool ↦ bif b then (U.ι ≫ φ).opensRange else (W.ι ≫ φ).opensRange)
    (by rw [iSup_bool_eq]; exact hcov) fun b ↦ ?_
  cases b
  · exact key W hW
  · exact key U hU

/-- **Cofiltered limits commute with gluing along opens.** Let `Uf ⟵ Vf ⟶ Sf` be a span of
cofiltered diagrams of schemes along open immersions with pullback naturality squares, whose
transition maps are affine. Let `X` be covered by opens `U = lim Uf` and `W = lim Sf`, with
`U ⊓ W` the preimage of `Vf` in `U` and in `W`. Then `X` is the limit of the gluings
`Uf a ∪_{Vf a} Sf a`. -/
noncomputable def isLimitPushoutFunctorCone [IsCofiltered Λ]
    [∀ {a b : Λ} (f : a ⟶ b), IsAffineHom (Uf.map f)]
    [∀ {a b : Λ} (f : a ⟶ b), IsAffineHom (Sf.map f)]
    (hα : ∀ {a b : Λ} (f : a ⟶ b), IsPullback (α.app a) (Vf.map f) (Uf.map f) (α.app b))
    (hβ : ∀ {a b : Λ} (f : a ⟶ b), IsPullback (β.app a) (Vf.map f) (Sf.map f) (β.app b))
    (hU : IsLimit (Cone.mk _ πU)) (hW : IsLimit (Cone.mk _ πW))
    (hVU : ∀ a, IsPullback (πV.app a) (X.homOfLE inf_le_left) (α.app a) (πU.app a))
    (hVW : ∀ a, IsPullback (πV.app a) (X.homOfLE inf_le_right) (β.app a) (πW.app a)) :
    IsLimit (pushoutFunctorCone α β hUW (fun a ↦ (hVU a).w) fun a ↦ (hVW a).w) := by
  have : IsZariskiLocalAtTarget @IsAffineHom.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine
  have (a b : Λ) (f : a ⟶ b) : IsAffineHom ((pushoutFunctor α β).map f) :=
    pushoutFunctor_map_of_isZariskiLocalAtTarget α β @IsAffineHom f (hα f) (hβ f)
      inferInstance inferInstance
  let c := pushoutFunctorCone α β hUW (fun a ↦ (hVU a).w) fun a ↦ (hVW a).w
  let φ : X ⟶ limit (pushoutFunctor α β) := limit.lift _ c
  let a₀ : Λ := IsCofiltered.nonempty.some
  have hl := ι_pushoutFunctorCone_π_app_left α β hUW (fun a ↦ (hVU a).w) (fun a ↦ (hVW a).w)
  have hr := ι_pushoutFunctorCone_π_app_right α β hUW (fun a ↦ (hVU a).w) (fun a ↦ (hVW a).w)
  -- Over the images of `Uf a₀` and `Sf a₀`, the limit of the gluings is `U` and `W`.
  have hlU : limit.lift _ ((Cone.postcompose (pushoutFunctorInl α β)).obj (Cone.mk _ πU)) =
      U.ι ≫ φ :=
    limit.hom_ext fun a ↦ by
      rw [limit.lift_π, Category.assoc, show φ ≫ limit.π _ a = c.π.app a from limit.lift_π c a,
        hl a]
      rfl
  have hlW : limit.lift _ ((Cone.postcompose (pushoutFunctorInr α β)).obj (Cone.mk _ πW)) =
      W.ι ≫ φ :=
    limit.hom_ext fun a ↦ by
      rw [limit.lift_π, Category.assoc, show φ ≫ limit.π _ a = c.π.app a from limit.lift_π c a,
        hr a]
      rfl
  have hU' := IsLimit.isPullback_of_isPullback_naturality (pushoutFunctorInl α β)
    (fun f ↦ isPullback_pushout_inl_map (hα f).w (hβ f)) hU (limit.isLimit _) a₀
  have hW' := IsLimit.isPullback_of_isPullback_naturality (pushoutFunctorInr α β)
    (fun f ↦ isPullback_pushout_inr_map (hα f) (hβ f).w) hW (limit.isLimit _) a₀
  rw [limit.isLimit_lift, hlU, limit.cone_π] at hU'
  rw [limit.isLimit_lift, hlW, limit.cone_π] at hW'
  have : IsOpenImmersion (U.ι ≫ φ) := MorphismProperty.of_isPullback hU' inferInstance
  have : IsOpenImmersion (W.ι ≫ φ) := MorphismProperty.of_isPullback hW' inferInstance
  -- The preimages in `X` of the images of `Uf a₀` and `Sf a₀` are `U` and `W`.
  have hpU := preimage_opensRange_eq_of_isPullback (isPullback_pushout (α.app a₀) (β.app a₀)) hUW
    inf_le_left inf_le_right (hl a₀) (hr a₀) (hVW a₀)
  have hpW := preimage_opensRange_eq_of_isPullback (isPullback_pushout (α.app a₀) (β.app a₀)).flip
    (sup_comm U W ▸ hUW) inf_le_right inf_le_left (hr a₀) (hl a₀) (hVU a₀)
  have hφ : c.π.app a₀ = φ ≫ limit.π _ a₀ := (limit.lift_π c a₀).symm
  have : IsIso φ := by
    refine isIso_of_isOpenImmersion_ι_comp φ (U := U) (W := W) ?_ ?_ ?_
    · rw [hU'.opensRange_snd, hW'.opensRange_snd, ← Scheme.Hom.preimage_sup,
        ← Scheme.Hom.preimage_top (limit.π _ a₀)]
      exact congrArg _ (opensRange_pushout_inl_sup_opensRange_pushout_inr (α.app a₀) (β.app a₀))
    · rwa [hU'.opensRange_snd, ← Scheme.Hom.comp_preimage, ← hφ]
    · rwa [hW'.opensRange_snd, ← Scheme.Hom.comp_preimage, ← hφ]
  exact IsLimit.ofPointIso (i := this) (limit.isLimit _)

end TauCeti.AlgebraicGeometry.Scheme
