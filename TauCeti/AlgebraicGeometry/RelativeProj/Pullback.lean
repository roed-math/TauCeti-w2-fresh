/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.PullbackSections
public import TauCeti.AlgebraicGeometry.RelativeProj.Basic

/-!
# Charts of the base change of a relative `Proj`

Let `g : Y ⟶ X` be a morphism of schemes and `A = ⨁ₙ Aₙ` a graded quasicoherent algebra on `X`,
with relative `Proj` `P = Proj_X(A) ⟶ X`. For affine opens `U` of `X` and `V ⊆ g⁻¹ U` of `Y`,
the pullback of graded sections `⨁ n, Γ(Aₙ, U) → ⨁ n, Γ((g^* A)ₙ, V)` induces a morphism

`Proj (⨁ n, Γ((g^* A)ₙ, V)) ⟶ Proj (⨁ n, Γ(Aₙ, U)) ⟶ P`

(`GradedQuasicoherentAlgebra.projPullbackToRelativeProj`). Pasting the cartesian square of
`Proj` of the pulled-back sections over `Spec Γ(Y, V) ⟶ Spec Γ(X, U)` with the chart of `P`
over `U`, it exhibits `Proj (⨁ n, Γ((g^* A)ₙ, V))` as the fibre product of `P` and
`Spec Γ(Y, V)` over `X`, hence as the preimage of `V` in the base change `P ×_X Y ⟶ Y`. These
are the charts over small affine opens of `Y` of the base change of `P` along `g`, which is to be
identified with the relative `Proj` of `g^* A`. They are natural in `V` and compatible with
shrinking `U` to a basic open.

The basic opens of an affine open of `Y` that lie over affine opens of `X` cover it, so the
finiteness conditions of a projective morphism pass from `A` to `g^* A`: over such basic opens by
the base change of graded sections, and then by locality of finite type and of finiteness.

## Main declarations

* `GradedQuasicoherentAlgebra.projPullbackToRelativeProj`: the morphism
  `Proj (⨁ n, Γ((g^* A)ₙ, V)) ⟶ Proj_X(A)`;
* `GradedQuasicoherentAlgebra.isPullback_projPullbackToRelativeProj`: it exhibits
  `Proj (⨁ n, Γ((g^* A)ₙ, V))` as `Proj_X(A) ×_X Spec Γ(Y, V)`;
* `GradedQuasicoherentAlgebra.isPullback_projPullbackToPullbackRelativeProj`: the induced morphism
  to `Proj_X(A) ×_X Y` exhibits `Proj (⨁ n, Γ((g^* A)ₙ, V))` as the preimage of `V`;
* `GradedQuasicoherentAlgebra.proj_map_restrict_projPullbackToRelativeProj` and
  `GradedQuasicoherentAlgebra.projPullbackToRelativeProj_basicOpen`: naturality in `V`, and
  independence of `U` along basic opens;
* `GradedQuasicoherentAlgebra.finiteType_pullback_sections_of_isAffineOpen` and
  `GradedQuasicoherentAlgebra.finite_pullback_sections_zero_of_isAffineOpen`: if the graded sections
  of `A` over every affine open are of finite type, with finite degree-zero part, then so are those
  of `g^* A` over every affine open of `Y`.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry Scheme.AffineZariskiSite
open scoped _root_.DirectSum

universe u

noncomputable section

namespace GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (A : GradedQuasicoherentAlgebra X) {U : X.Opens}
  (hU : IsAffineOpen U) {V : Y.Opens} (hV' : IsAffineOpen V) (hV : V ≤ g ⁻¹ᵁ U)

/-- **The chart of the base change of a relative `Proj`.** For affine opens `U` of `X` and
`V ⊆ g⁻¹ U` of `Y`, the morphism `Proj (⨁ n, Γ((g^* A)ₙ, V)) ⟶ Proj (⨁ n, Γ(Aₙ, U)) ⟶ Proj_X(A)`
induced by the pullback of graded sections, followed by the chart of the relative `Proj` over
`U`. -/
def projPullbackToRelativeProj :
    Proj (((pullback g).obj A).obj.gradedSectionsGrading V) ⟶ A.obj.relativeProj :=
  Proj.map (pullbackGradedSectionsLEGradedHom A hV)
      (irrelevant_le_map_pullbackGradedSectionsLEGradedHom A hU hV' hV) ≫
    A.obj.relativeProjCover.f (⟨U, hU⟩ : X.AffineZariskiSite)

/-- The chart `projPullbackToRelativeProj` lies over `Spec Γ(Y, V) ⟶ Y ⟶ X`. -/
@[reassoc]
theorem projPullbackToRelativeProj_relativeProjToBase :
    projPullbackToRelativeProj g A hU hV' hV ≫ A.obj.relativeProjToBase =
      Proj.toSpecCoeff (((pullback g).obj A).obj.gradedSectionsGrading V) ≫ hV'.fromSpec ≫ g := by
  have h := (isPullback_proj_map_pullbackGradedSectionsLEGradedHom A hU hV' hV).w
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (A.obj.relativeProjCover_f_relativeProjToBase ⟨U, hU⟩)).trans ?_)
  exact ((reassoc_of% h) hU.fromSpec).trans
    (congrArg (_ ≫ ·) (IsAffineOpen.SpecMap_appLE_fromSpec g hU hV' hV))

/-- **`Proj` of the pulled-back sections over `V` is the base change of the relative `Proj` to
`Spec Γ(Y, V)`**: the square formed by `projPullbackToRelativeProj`, the coefficient projection
`Proj (⨁ n, Γ((g^* A)ₙ, V)) ⟶ Spec Γ(Y, V)`, the structure morphism `Proj_X(A) ⟶ X` and
`Spec Γ(Y, V) ⟶ Y ⟶ X` is cartesian. It is the cartesian square of `Proj` of the pulled-back
sections over `Spec Γ(X, U)` pasted with the chart of `Proj_X(A)` over `U`. -/
theorem isPullback_projPullbackToRelativeProj :
    IsPullback (projPullbackToRelativeProj g A hU hV' hV)
      (Proj.toSpecCoeff (((pullback g).obj A).obj.gradedSectionsGrading V))
      A.obj.relativeProjToBase (hV'.fromSpec ≫ g) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec g hU hV' hV]
  exact (isPullback_proj_map_pullbackGradedSectionsLEGradedHom A hU hV' hV).paste_horiz
    (A.obj.isPullback_relativeProjCover_fromSpec ⟨U, hU⟩)

/-- The chart `projPullbackToRelativeProj`, as a morphism into the base change
`Proj_X(A) ×_X Y` over `Spec Γ(Y, V) ⟶ Y`. -/
def projPullbackToPullbackRelativeProj :
    Proj (((pullback g).obj A).obj.gradedSectionsGrading V) ⟶
      Limits.pullback A.obj.relativeProjToBase g :=
  Limits.pullback.lift (projPullbackToRelativeProj g A hU hV' hV)
    (Proj.toSpecCoeff _ ≫ hV'.fromSpec)
    ((projPullbackToRelativeProj_relativeProjToBase g A hU hV' hV).trans
      (Category.assoc _ _ _).symm)

/-- The first projection of `projPullbackToPullbackRelativeProj` is `projPullbackToRelativeProj`. -/
@[reassoc (attr := simp)]
theorem projPullbackToPullbackRelativeProj_fst :
    projPullbackToPullbackRelativeProj g A hU hV' hV ≫ Limits.pullback.fst _ _ =
      projPullbackToRelativeProj g A hU hV' hV :=
  Limits.pullback.lift_fst _ _ _

/-- The second projection of `projPullbackToPullbackRelativeProj` is the coefficient projection
followed by `Spec Γ(Y, V) ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem projPullbackToPullbackRelativeProj_snd :
    projPullbackToPullbackRelativeProj g A hU hV' hV ≫ Limits.pullback.snd _ _ =
      Proj.toSpecCoeff (((pullback g).obj A).obj.gradedSectionsGrading V) ≫ hV'.fromSpec :=
  Limits.pullback.lift_snd _ _ _

/-- **The preimage of `V` in the base change of the relative `Proj` is `Proj` of the pulled-back
sections over `V`**: the square formed by `projPullbackToPullbackRelativeProj`, the coefficient
projection to `Spec Γ(Y, V)`, the base change `Proj_X(A) ×_X Y ⟶ Y` and `Spec Γ(Y, V) ⟶ Y` is
cartesian. -/
theorem isPullback_projPullbackToPullbackRelativeProj :
    IsPullback (projPullbackToPullbackRelativeProj g A hU hV' hV)
      (Proj.toSpecCoeff (((pullback g).obj A).obj.gradedSectionsGrading V))
      (Limits.pullback.snd A.obj.relativeProjToBase g) hV'.fromSpec :=
  IsPullback.of_right (by
      simpa only [projPullbackToPullbackRelativeProj_fst] using
        isPullback_projPullbackToRelativeProj g A hU hV' hV)
    (projPullbackToPullbackRelativeProj_snd g A hU hV' hV) (IsPullback.of_hasPullback _ _)

/-- **Naturality in `V`**: for affine opens `W ⊆ V ⊆ g⁻¹ U` of `Y`, the chart over `W` is the
morphism `Proj (⨁ n, Γ((g^* A)ₙ, W)) ⟶ Proj (⨁ n, Γ((g^* A)ₙ, V))` induced by restriction of
sections, followed by the chart over `V`. -/
theorem proj_map_restrict_projPullbackToRelativeProj {W : Y.Opens} (hW' : IsAffineOpen W)
    (i : W ⟶ V) (h : HomogeneousIdeal.irrelevant
        (((pullback g).obj A).obj.gradedSectionsGrading W) ≤
      (HomogeneousIdeal.irrelevant (((pullback g).obj A).obj.gradedSectionsGrading V)).map
        (((pullback g).obj A).obj.restrictGradedSectionsGradedHom i)) :
    Proj.map _ h ≫ projPullbackToRelativeProj g A hU hV' hV =
      projPullbackToRelativeProj g A hU hW' ((leOfHom i).trans hV) :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) ((Proj.map_comp _ _ _ _).symm.trans
    (Proj.map_congr (GradedRingHom.ext fun x ↦ by
      rw [GradedRingHom.comp_apply, CommMon.restrictGradedSectionsGradedHom_apply,
        pullbackGradedSectionsLEGradedHom_apply, pullbackGradedSectionsLEGradedHom_apply,
        ← RingHom.comp_apply, restrictGradedSections_comp_pullbackGradedSectionsLE]) _ _)))

/-- **Compatibility with basic opens of `U`**: if `V ⊆ g⁻¹ D(f)` for a section `f` over `U`, the
chart over `V` through `D(f)` is the chart over `V` through `U`. -/
theorem projPullbackToRelativeProj_basicOpen (f : Γ(X, U)) (hV : V ≤ g ⁻¹ᵁ X.basicOpen f) :
    projPullbackToRelativeProj g A (hU.basicOpen f) hV' hV =
      projPullbackToRelativeProj g A hU hV'
        (hV.trans (g.preimage_mono (X.basicOpen_le f))) := by
  let U' : X.AffineZariskiSite := ⟨U, hU⟩
  have i : U'.basicOpen f ⟶ U' := homOfLE (U'.basicOpen_le f)
  -- the chart over `D(f)` is the transition map to the chart over `U` followed by the latter
  have hw : A.obj.relativeProjCover.f (U'.basicOpen f) =
      A.obj.relativeProjGluingData.functor.map i ≫ A.obj.relativeProjCover.f U' :=
    (colimit.w A.obj.relativeProjGluingData.functor i).symm
  refine (congrArg (_ ≫ ·) hw).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) ?_))
  rw [CommMon.relativeProjGluingData_functor_map]
  refine (Proj.map_comp _ _ _ _).symm.trans (Proj.map_congr (GradedRingHom.ext fun x ↦ ?_) _ _)
  -- the sections over `U'` are the sections over `U`, by definition
  have key (x : ⨁ n, Γ(A.obj.X n, U)) : pullbackGradedSectionsLEGradedHom A hV
      (A.obj.restrictGradedSectionsGradedHom (homOfLE (X.basicOpen_le f)) x) =
      pullbackGradedSectionsLEGradedHom A (hV.trans (g.preimage_mono (X.basicOpen_le f))) x := by
    rw [CommMon.restrictGradedSectionsGradedHom_apply, pullbackGradedSectionsLEGradedHom_apply,
      pullbackGradedSectionsLEGradedHom_apply, ← RingHom.comp_apply,
      pullbackGradedSectionsLE_comp_restrictGradedSections]
  exact key x

variable {g} in
/-- Over an affine open `V` of `Y`, the sections `h` whose basic open `D(h)` lies over an affine
open of `X` generate the unit ideal. -/
private theorem span_setOf_basicOpen_le_preimage_eq_top (hV' : IsAffineOpen V) :
    Ideal.span {h : Γ(Y, V) | ∃ U : X.Opens, IsAffineOpen U ∧ Y.basicOpen h ≤ g ⁻¹ᵁ U} = ⊤ := by
  refine hV'.iSup_basicOpen_eq_self_iff.mp (le_antisymm (iSup_le fun h ↦ Y.basicOpen_le h.1)
    fun y hy ↦ ?_)
  obtain ⟨U, hU, hgy, -⟩ := exists_isAffineOpen_mem_and_subset (x := g y) (U := ⊤) trivial
  obtain ⟨h, hle, hyh⟩ := hV'.exists_basicOpen_le (V := g ⁻¹ᵁ U) ⟨y, hgy⟩ hy
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨h, U, hU, hle⟩, hyh⟩

/-- **The pullback of a graded algebra of finite type is of finite type**: if the graded sections
of `A` over every affine open of `X` form a finitely generated algebra, then so do the graded
sections of `g^* A` over every affine open `V` of `Y`. Over the basic opens of `V` lying over
affine opens of `X` this is `finiteType_pullback_sections`, and finite type is local
(`CategoryTheory.CommMon.finiteType_gradedSections_of_span_eq_top`). -/
theorem finiteType_pullback_sections_of_isAffineOpen
    (hA : ∀ U : X.Opens, IsAffineOpen U → Algebra.FiniteType Γ(X, U) (⨁ n, Γ(A.obj.X n, U)))
    (hV' : IsAffineOpen V) :
    Algebra.FiniteType Γ(Y, V) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) :=
  ((pullback g).obj A).obj.finiteType_gradedSections_of_span_eq_top hV' _
    (span_setOf_basicOpen_le_preimage_eq_top hV') fun _ ⟨U, hU, hle⟩ ↦
      have := hA U hU
      finiteType_pullback_sections A hU (hV'.basicOpen _) hle

/-- **The degree-zero part of the pullback of a graded algebra is finite**: if the degree-zero
sections of `A` over every affine open of `X` form a finite module, then so do the degree-zero
sections of `g^* A` over every affine open `V` of `Y`. Over the basic opens of `V` lying over
affine opens of `X` this is `finite_pullback_sections_zero`, and finiteness of the sections of a
quasicoherent sheaf is local (`Module.Finite.of_localizationSpan'`). -/
theorem finite_pullback_sections_zero_of_isAffineOpen
    (hA : ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(A.obj.X 0, U))
    (hV' : IsAffineOpen V) :
    Module.Finite Γ(Y, V) Γ(((pullback g).obj A).obj.X 0, V) := by
  let s := {h : Γ(Y, V) | ∃ U : X.Opens, IsAffineOpen U ∧ Y.basicOpen h ≤ g ⁻¹ᵁ U}
  have (h : s) : IsLocalization.Away h.1 Γ(Y, Y.basicOpen h.1) := hV'.isLocalization_basicOpen h.1
  have (h : s) : IsLocalizedModule.Away h.1
      ((((pullback g).obj A).obj.X 0).basicOpenRestrict h.1) :=
    (((pullback g).obj A).obj.X 0).isLocalizedModule_basicOpenRestrict hV' h.1
  refine Module.Finite.of_localizationSpan' s (span_setOf_basicOpen_le_preimage_eq_top hV')
    (Rₚ := fun h ↦ Γ(Y, Y.basicOpen h.1))
    (Mₚ := fun h ↦ Γ(((pullback g).obj A).obj.X 0, Y.basicOpen h.1))
    (fun h ↦ (((pullback g).obj A).obj.X 0).basicOpenRestrict h.1) fun ⟨h, U, hU, hle⟩ ↦ ?_
  have := hA U hU
  exact finite_pullback_sections_zero A hU (hV'.basicOpen h) hle

end GradedQuasicoherentAlgebra

end

end AlgebraicGeometry

end TauCeti
