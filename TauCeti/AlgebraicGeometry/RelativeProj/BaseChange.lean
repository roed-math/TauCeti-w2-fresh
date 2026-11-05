/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeGluing
public import TauCeti.AlgebraicGeometry.RelativeProj.Pullback

/-!
# Base change of a relative `Proj`

Let `g : Y ⟶ X` be a morphism of schemes and `A` a graded quasicoherent algebra on `X`. This file
shows that the relative `Proj` of the pullback `g^* A` is the base change of the relative `Proj`
of `A`:

`Proj_Y(g^* A) ≅ Proj_X(A) ×_X Y` over `Y`.

The relative `Proj` of `g^* A` is glued from the schemes `Proj (⨁ n, Γ((g^* A)ₙ, V))` over all
affine opens `V` of `Y`, while the charts of `Proj_X(A) ×_X Y` constructed in
`TauCeti.AlgebraicGeometry.RelativeProj.Pullback` exist only over the affine opens `V` lying over
an affine open of `X`. These form a locally directed open cover of `Y`
(`TauCeti.AlgebraicGeometry.directedCoverOver`), since a basic open of such a `V` again lies over
an affine open of `X`. Over it, the schemes `Proj (⨁ n, Γ((g^* A)ₙ, V))` form a relative gluing
datum, and both `Proj_Y(g^* A)` and `Proj_X(A) ×_X Y` are recognised as its glued scheme by
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.isoOfIsPullback`.

## Main declarations

* `TauCeti.AlgebraicGeometry.directedCoverOver`: the locally directed open cover of `Y` by the
  affine opens lying over affine opens of `X`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.relativeProjPullbackIso`: the isomorphism
  `Proj_Y(g^* A) ≅ Proj_X(A) ×_X Y`, over `Y` and given on charts by
  `GradedQuasicoherentAlgebra.projPullbackToPullbackRelativeProj`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.isPullback_relativeProjPullback`: the
  relative `Proj` of `g^* A` is the base change of the relative `Proj` of `A` along `g`.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry Scheme.AffineZariskiSite

universe u

noncomputable section

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The affine opens of `Y` lying over an affine open of `X` along `g : Y ⟶ X`, ordered as in
`Y.AffineZariskiSite`, by being a basic open. -/
abbrev AffineZariskiSiteOver : Type u :=
  {V : Y.AffineZariskiSite // ∃ U : X.Opens, IsAffineOpen U ∧ V.toOpens ≤ g ⁻¹ᵁ U}

/-- The inclusion of the affine opens of `Y` lying over affine opens of `X` into all affine opens
of `Y`. -/
abbrev AffineZariskiSiteOver.inclusion : AffineZariskiSiteOver g ⥤ Y.AffineZariskiSite :=
  Monotone.functor (f := Subtype.val) fun _ _ h ↦ h

/-- The open cover of `Y` by the affine opens lying over affine opens of `X`, indexed as in
`Scheme.AffineZariskiSite.directedCover`. -/
abbrev directedCoverOver : Y.OpenCover where
  I₀ := AffineZariskiSiteOver g
  X V := V.1.toOpens
  f V := V.1.toOpens.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun y ↦ ?_, inferInstance⟩
    obtain ⟨U, hU, hgy, -⟩ := exists_isAffineOpen_mem_and_subset (x := g y) (U := ⊤) trivial
    obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := g ⁻¹ᵁ U) hgy
    exact ⟨⟨⟨V, hV⟩, U, hU, hVU⟩, ⟨y, hyV⟩, rfl⟩

/-- The cover of `Y` by the affine opens lying over affine opens of `X` is locally directed: a
basic open of such an affine open again lies over an affine open of `X`, so this is inherited from
`Scheme.AffineZariskiSite.directedCover`. -/
instance : (directedCoverOver g).LocallyDirected where
  trans f := Y.homOfLE (toOpens_mono (leOfHom f))
  directed {V W} x := by
    obtain ⟨k, hkV, hkW, y, hy⟩ := (directedCover Y).exists_lift_trans_eq (i := V.1) (j := W.1) x
    obtain ⟨U, hU, hVU⟩ := V.2
    exact ⟨⟨k, U, hU, (toOpens_mono (leOfHom hkV)).trans hVU⟩, homOfLE (leOfHom hkV),
      homOfLE (leOfHom hkW), y, hy⟩

namespace GradedQuasicoherentAlgebra

variable (B : GradedQuasicoherentAlgebra Y)

/-- The relative gluing datum of the relative `Proj` of a graded quasicoherent algebra `B` on
`Y`, restricted to the affine opens of `Y` lying over affine opens of `X`. -/
def relativeProjGluingDataOver : (directedCoverOver g).RelativeGluingData where
  functor := AffineZariskiSiteOver.inclusion g ⋙ B.obj.relativeProjFunctor
  natTrans :=
    { app V := B.obj.relativeProjGluingData.natTrans.app V.1
      naturality _ _ i := B.obj.relativeProjGluingData.natTrans.naturality
        ((AffineZariskiSiteOver.inclusion g).map i) }
  equifibered _ _ i := B.obj.relativeProjGluingData.equifibered
    ((AffineZariskiSiteOver.inclusion g).map i)

/-- The charts of the relative `Proj` of `B` over the affine opens of `Y` lying over affine opens
of `X`. -/
def relativeProjGluingDataOverToRelativeProj :
    (relativeProjGluingDataOver g B).functor ⟶ (Functor.const _).obj B.obj.relativeProj where
  app V := colimit.ι B.obj.relativeProjGluingData.functor V.1
  naturality _ _ i := (colimit.w B.obj.relativeProjGluingData.functor
    ((AffineZariskiSiteOver.inclusion g).map i)).trans (Category.comp_id _).symm

/-- The relative `Proj` of `B` is the glued scheme of `relativeProjGluingDataOver g B`. -/
def relativeProjGluingDataOverIso : (relativeProjGluingDataOver g B).glued ≅ B.obj.relativeProj :=
  (relativeProjGluingDataOver g B).isoOfIsPullback B.obj.relativeProjToBase
    (relativeProjGluingDataOverToRelativeProj g B)
    fun V ↦ B.obj.relativeProjGluingData.isPullback_natTrans_ι_toBase V.1

/-- The isomorphism `relativeProjGluingDataOverIso` lies over `Y`. -/
@[reassoc (attr := simp)]
theorem relativeProjGluingDataOverIso_hom_comp :
    (relativeProjGluingDataOverIso g B).hom ≫ B.obj.relativeProjToBase =
      (relativeProjGluingDataOver g B).toBase :=
  (relativeProjGluingDataOver g B).isoOfIsPullback_hom_comp B.obj.relativeProjToBase
    (relativeProjGluingDataOverToRelativeProj g B)
    fun V ↦ B.obj.relativeProjGluingData.isPullback_natTrans_ι_toBase V.1

variable (A : GradedQuasicoherentAlgebra X)

/-- The charts `projPullbackToPullbackRelativeProj` of `Proj_X(A) ×_X Y` over the affine opens
of `Y` lying over affine opens of `X`, each formed through a chosen such affine open of `X`. -/
def relativeProjGluingDataOverToPullback :
    (relativeProjGluingDataOver g ((pullback g).obj A)).functor ⟶
      (Functor.const _).obj (Limits.pullback A.obj.relativeProjToBase g) where
  app V := projPullbackToPullbackRelativeProj g A V.2.choose_spec.1 V.1.2 V.2.choose_spec.2
  naturality V W i := by
    -- term-mode chains: the indices are not reducibly affine opens, so `rw` motives are ill-typed
    refine (pullback.hom_ext ?_ ?_).trans (Category.comp_id _).symm
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (projPullbackToPullbackRelativeProj_fst g A _ _ _)).trans
        ((proj_map_restrict_projPullbackToRelativeProj g A _ W.1.2 _ V.1.2
          ((toOpensFunctor Y).map ((AffineZariskiSiteOver.inclusion g).map i)) _).trans
          ((projPullbackToRelativeProj_eq g A V.1.2 _ _ _ _).trans
            (projPullbackToPullbackRelativeProj_fst g A _ _ _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (projPullbackToPullbackRelativeProj_snd g A _ _ _)).trans
        ((reassoc_of% (((pullback g).obj A).obj.relativeProjToSpec.naturality
          ((AffineZariskiSiteOver.inclusion g).map i))) W.1.2.fromSpec |>.trans
          ((congrArg (_ ≫ ·) (W.1.2.map_fromSpec V.1.2 _)).trans
            (projPullbackToPullbackRelativeProj_snd g A _ _ _).symm)))

/-- Each chart `relativeProjGluingDataOverToPullback` exhibits `Proj (⨁ n, Γ((g^* A)ₙ, V))` as the
preimage of `V` in `Proj_X(A) ×_X Y`
(`GradedQuasicoherentAlgebra.isPullback_projPullbackToPullbackRelativeProj`, read over `V` rather
than over `Spec Γ(Y, V)`). -/
theorem isPullback_relativeProjGluingDataOverToPullback (V : AffineZariskiSiteOver g) :
    IsPullback ((relativeProjGluingDataOver g ((pullback g).obj A)).natTrans.app V)
      ((relativeProjGluingDataOverToPullback g A).app V) ((directedCoverOver g).f V)
      (Limits.pullback.snd A.obj.relativeProjToBase g) :=
  (isPullback_projPullbackToPullbackRelativeProj g A V.2.choose_spec.1 V.1.2
    V.2.choose_spec.2).flip.of_iso (Iso.refl _) V.1.2.isoSpec.symm (Iso.refl _) (Iso.refl _)
    (Category.id_comp _).symm ((Category.comp_id _).trans (Category.id_comp _).symm)
    (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- **The relative `Proj` commutes with base change**: for `g : Y ⟶ X` and a graded quasicoherent
algebra `A` on `X`, the relative `Proj` of `g^* A` is isomorphic to `Proj_X(A) ×_X Y`. Both are the
glued scheme of the schemes `Proj (⨁ n, Γ((g^* A)ₙ, V))` over the affine opens `V` of `Y` lying
over affine opens of `X`. -/
def relativeProjPullbackIso :
    ((pullback g).obj A).obj.relativeProj ≅ Limits.pullback A.obj.relativeProjToBase g :=
  (relativeProjGluingDataOverIso g ((pullback g).obj A)).symm ≪≫
    (relativeProjGluingDataOver g ((pullback g).obj A)).isoOfIsPullback _
      (relativeProjGluingDataOverToPullback g A)
      (isPullback_relativeProjGluingDataOverToPullback g A)

/-- The isomorphism `relativeProjPullbackIso` lies over `Y`. -/
@[reassoc (attr := simp)]
theorem relativeProjPullbackIso_hom_snd :
    (relativeProjPullbackIso g A).hom ≫ Limits.pullback.snd A.obj.relativeProjToBase g =
      ((pullback g).obj A).obj.relativeProjToBase :=
  (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    ((relativeProjGluingDataOver g ((pullback g).obj A)).isoOfIsPullback_hom_comp _
      (relativeProjGluingDataOverToPullback g A)
      (isPullback_relativeProjGluingDataOverToPullback g A))).trans
    ((Iso.inv_comp_eq _).mpr (relativeProjGluingDataOverIso_hom_comp g _).symm))

/-- **The isomorphism `relativeProjPullbackIso` is given by the charts**: over affine opens `U` of
`X` and `V ⊆ g⁻¹ U` of `Y`, the chart `Proj (⨁ n, Γ((g^* A)ₙ, V)) ⟶ Proj_Y(g^* A)` followed by
`relativeProjPullbackIso` is `projPullbackToPullbackRelativeProj`. -/
theorem relativeProjCover_f_relativeProjPullbackIso_hom {U : X.Opens} (hU : IsAffineOpen U)
    {V : Y.Opens} (hV' : IsAffineOpen V) (hV : V ≤ g ⁻¹ᵁ U) :
    ((pullback g).obj A).obj.relativeProjCover.f ⟨V, hV'⟩ ≫ (relativeProjPullbackIso g A).hom =
      projPullbackToPullbackRelativeProj g A hU hV' hV := by
  let v : AffineZariskiSiteOver g := ⟨⟨V, hV'⟩, U, hU, hV⟩
  have h₁ := (Iso.comp_inv_eq (relativeProjGluingDataOverIso g ((pullback g).obj A))).mpr
      ((relativeProjGluingDataOver g ((pullback g).obj A)).ι_isoOfIsPullback_hom _
        (relativeProjGluingDataOverToRelativeProj g ((pullback g).obj A))
        (fun V ↦ ((pullback g).obj A).obj.relativeProjGluingData.isPullback_natTrans_ι_toBase V.1)
        v).symm
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
    (((relativeProjGluingDataOver g ((pullback g).obj A)).ι_isoOfIsPullback_hom _
      (relativeProjGluingDataOverToPullback g A)
      (isPullback_relativeProjGluingDataOverToPullback g A) v).trans (pullback.hom_ext ?_ ?_)))
  · exact (projPullbackToPullbackRelativeProj_fst g A _ _ _).trans
      ((projPullbackToRelativeProj_eq g A hV' _ hU _ hV).trans
        (projPullbackToPullbackRelativeProj_fst g A _ _ _).symm)
  · exact (projPullbackToPullbackRelativeProj_snd g A _ _ _).trans
      (projPullbackToPullbackRelativeProj_snd g A _ _ _).symm

/-- **The relative `Proj` of `g^* A` is the base change of the relative `Proj` of `A`**: the square
formed by `Proj_Y(g^* A) ≅ Proj_X(A) ×_X Y ⟶ Proj_X(A)`, the structure morphisms and `g` is
cartesian. -/
theorem isPullback_relativeProjPullback :
    IsPullback ((relativeProjPullbackIso g A).hom ≫ Limits.pullback.fst _ _)
      ((pullback g).obj A).obj.relativeProjToBase A.obj.relativeProjToBase g :=
  IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ (relativeProjPullbackIso g A) rfl
    (relativeProjPullbackIso_hom_snd g A)

end GradedQuasicoherentAlgebra

end

end AlgebraicGeometry

end TauCeti
