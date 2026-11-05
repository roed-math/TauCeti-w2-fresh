/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.PullbackSections
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf

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
identified with the relative `Proj` of `g^* A`. They are natural in `V` and do not depend on
`U`: two choices agree along basic opens common to both, and these cover.

The basic opens of an affine open of `Y` that lie over affine opens of `X` cover it, so the
finiteness conditions of a projective morphism, and generation in degree one, pass from `A` to
`g^* A`: over such basic opens by the base change of graded sections, and then by locality of
finite type, of finiteness and of generation in degree one.

## Main declarations

* `GradedQuasicoherentAlgebra.projPullbackToRelativeProj`: the morphism
  `Proj (⨁ n, Γ((g^* A)ₙ, V)) ⟶ Proj_X(A)`;
* `GradedQuasicoherentAlgebra.isPullback_projPullbackToRelativeProj`: it exhibits
  `Proj (⨁ n, Γ((g^* A)ₙ, V))` as `Proj_X(A) ×_X Spec Γ(Y, V)`;
* `GradedQuasicoherentAlgebra.isPullback_projPullbackToPullbackRelativeProj`: the induced morphism
  to `Proj_X(A) ×_X Y` exhibits `Proj (⨁ n, Γ((g^* A)ₙ, V))` as the preimage of `V`; so it is an
  open immersion, and these charts cover `Proj_X(A) ×_X Y`
  (`GradedQuasicoherentAlgebra.exists_projPullbackToPullbackRelativeProj_eq`);
* `GradedQuasicoherentAlgebra.proj_map_restrict_projPullbackToRelativeProj` and
  `GradedQuasicoherentAlgebra.projPullbackToRelativeProj_basicOpen`: naturality in `V`, and
  independence of `U` along basic opens;
* `GradedQuasicoherentAlgebra.projPullbackToRelativeProj_eq`: the chart over `V` does not depend
  on `U`;
* `GradedQuasicoherentAlgebra.finiteType_pullback_sections_of_isAffineOpen` and
  `GradedQuasicoherentAlgebra.finite_pullback_sections_zero_of_isAffineOpen`: if the graded sections
  of `A` over every affine open are of finite type, with finite degree-zero part, then so are those
  of `g^* A` over every affine open of `Y`;
* `GradedQuasicoherentAlgebra.isGeneratedInDegreeOne_pullback`: if `A` is generated in degree one,
  so is `g^* A`.
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

/-- The chart `projPullbackToPullbackRelativeProj` is an open immersion, as the base change of
`Spec Γ(Y, V) ⟶ Y`. -/
instance isOpenImmersion_projPullbackToPullbackRelativeProj :
    IsOpenImmersion (projPullbackToPullbackRelativeProj g A hU hV' hV) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_projPullbackToPullbackRelativeProj g A hU hV' hV).flip inferInstance

variable {A} in
/-- **The charts cover the base change**: every point of `Proj_X(A) ×_X Y` lies in the image of
the chart over some affine open `V` of `Y` lying over an affine open `U` of `X`. -/
theorem exists_projPullbackToPullbackRelativeProj_eq
    (z : ↥(Limits.pullback A.obj.relativeProjToBase g)) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV' : IsAffineOpen V)
      (hV : V ≤ g ⁻¹ᵁ U) (p : Proj (((pullback g).obj A).obj.gradedSectionsGrading V)),
      projPullbackToPullbackRelativeProj g A hU hV' hV p = z := by
  obtain ⟨U, hU, hgz, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := g (Limits.pullback.snd A.obj.relativeProjToBase g z)) (U := ⊤) trivial
  obtain ⟨V, hV', hzV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (x := Limits.pullback.snd A.obj.relativeProjToBase g z) (U := g ⁻¹ᵁ U) hgz
  obtain ⟨u, hu⟩ : Limits.pullback.snd A.obj.relativeProjToBase g z ∈ Set.range hV'.fromSpec := by
    rw [hV'.range_fromSpec]
    exact hzV
  obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_projPullbackToPullbackRelativeProj g A hU hV' hVU) z u hu.symm
  exact ⟨U, hU, V, hV', hVU, p, hp⟩

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

/-- Over a basic open `D(h) ⊆ V` lying over a basic open common to `U₁` and `U₂`, the charts
through `U₁` and through `U₂` agree. -/
private lemma proj_map_restrict_projPullbackToRelativeProj_eq {U₁ U₂ : X.Opens}
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂) (hV₁ : V ≤ g ⁻¹ᵁ U₁) (hV₂ : V ≤ g ⁻¹ᵁ U₂)
    {h : Γ(Y, V)} {f₁ : Γ(X, U₁)} {f₂ : Γ(X, U₂)} (e : X.basicOpen f₁ = X.basicOpen f₂)
    (hle : Y.basicOpen h ≤ g ⁻¹ᵁ X.basicOpen f₁) :
    Proj.map _ (((pullback g).obj A).obj.irrelevant_le_map_restrictGradedSectionsGradedHom h hV'
        (homOfLE (Y.basicOpen_le h))) ≫ projPullbackToRelativeProj g A hU₁ hV' hV₁ =
      Proj.map _ (((pullback g).obj A).obj.irrelevant_le_map_restrictGradedSectionsGradedHom h hV'
        (homOfLE (Y.basicOpen_le h))) ≫ projPullbackToRelativeProj g A hU₂ hV' hV₂ := by
  have hle₂ : Y.basicOpen h ≤ g ⁻¹ᵁ X.basicOpen f₂ := e ▸ hle
  -- the chart depends on `U` only as an open
  have hchart {W W' : X.Opens} (e : W = W') (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
      (hD : Y.basicOpen h ≤ g ⁻¹ᵁ W) (hD' : Y.basicOpen h ≤ g ⁻¹ᵁ W') :
      projPullbackToRelativeProj g A hW (hV'.basicOpen h) hD =
        projPullbackToRelativeProj g A hW' (hV'.basicOpen h) hD' := by
    subst e
    rfl
  -- both sides are the chart over `D(h)` through the common basic open
  have h₁ := projPullbackToRelativeProj_basicOpen g A hU₁ (hV'.basicOpen h) f₁ hle
  have h₂ := projPullbackToRelativeProj_basicOpen g A hU₂ (hV'.basicOpen h) f₂ hle₂
  exact (proj_map_restrict_projPullbackToRelativeProj g A hU₁ hV' hV₁ (hV'.basicOpen h) _ _).trans
    (h₁.symm.trans ((hchart e _ _ hle hle₂).trans (h₂.trans
      (proj_map_restrict_projPullbackToRelativeProj g A hU₂ hV' hV₂ (hV'.basicOpen h) _ _).symm)))

/-- `Proj` of the restriction of sections to a basic open `D(h) ⊆ V` is an open immersion: it is
the base change of `Spec Γ(Y, D(h)) ⟶ Spec Γ(Y, V)`
(`CategoryTheory.CommMon.isPullback_proj_restrictGradedSections`). -/
private lemma isOpenImmersion_proj_map_restrictGradedSections (h : Γ(Y, V)) :
    IsOpenImmersion (Proj.map _
      (((pullback g).obj A).obj.irrelevant_le_map_restrictGradedSectionsGradedHom h hV'
        (homOfLE (Y.basicOpen_le h)))) := by
  have : IsOpenImmersion (Spec.map (Y.presheaf.map (homOfLE (Y.basicOpen_le h)).op)) :=
    have : IsOpenImmersion (Spec.map (Y.presheaf.map (homOfLE (Y.basicOpen_le h)).op) ≫
        hV'.fromSpec) := by
      rw [hV'.map_fromSpec (hV'.basicOpen h)]
      infer_instance
    .of_comp _ hV'.fromSpec
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (((pullback g).obj A).obj.isPullback_proj_restrictGradedSections h hV'
      (homOfLE (Y.basicOpen_le h))).flip this

include hV' in
/-- The image in `V` of every point of `Proj (⨁ n, Γ((g^* A)ₙ, V))` lies in a basic open
`D(h) ⊆ V` lying over a basic open common to two affine opens `U₁` and `U₂` of `X` with
`V ⊆ g⁻¹ (U₁ ∩ U₂)` (`exists_basicOpen_le_affine_inter`). -/
private lemma exists_basicOpen_le_preimage_basicOpen {U₁ U₂ : X.Opens} (hU₁ : IsAffineOpen U₁)
    (hU₂ : IsAffineOpen U₂) (hV₁ : V ≤ g ⁻¹ᵁ U₁) (hV₂ : V ≤ g ⁻¹ᵁ U₂) {y : Y} (hy : y ∈ V) :
    ∃ (h : Γ(Y, V)) (f₁ : Γ(X, U₁)) (f₂ : Γ(X, U₂)), X.basicOpen f₁ = X.basicOpen f₂ ∧
      Y.basicOpen h ≤ g ⁻¹ᵁ X.basicOpen f₁ ∧ y ∈ Y.basicOpen h := by
  obtain ⟨f₁, f₂, e, hf⟩ := exists_basicOpen_le_affine_inter hU₁ hU₂ _ ⟨hV₁ hy, hV₂ hy⟩
  obtain ⟨h, hle, hyh⟩ := hV'.exists_basicOpen_le (V := g ⁻¹ᵁ X.basicOpen f₁) ⟨_, hf⟩ hy
  exact ⟨h, f₁, f₂, e, hle, hyh⟩

/-- A point of `Proj (⨁ n, Γ((g^* A)ₙ, V))` whose image in `V` lies in a basic open `D(h)` is in
the image of `Proj` of the sections over `D(h)`. -/
private lemma exists_proj_map_restrictGradedSections_eq (h : Γ(Y, V))
    (y : Proj (((pullback g).obj A).obj.gradedSectionsGrading V))
    (hy : hV'.fromSpec (Proj.toSpecCoeff _ y) ∈ Y.basicOpen h) :
    ∃ p : Proj (((pullback g).obj A).obj.gradedSectionsGrading (Y.basicOpen h)),
      Proj.map _ (((pullback g).obj A).obj.irrelevant_le_map_restrictGradedSectionsGradedHom h hV'
        (homOfLE (Y.basicOpen_le h))) p = y := by
  obtain ⟨u, hu⟩ : hV'.fromSpec (Proj.toSpecCoeff _ y) ∈ Set.range (hV'.basicOpen h).fromSpec := by
    rw [IsAffineOpen.range_fromSpec]
    exact hy
  have hu' : Spec.map (Y.presheaf.map (homOfLE (Y.basicOpen_le h)).op) u =
      Proj.toSpecCoeff _ y :=
    hV'.fromSpec.isOpenEmbedding.injective ((Scheme.Hom.comp_apply _ _ u).symm.trans
      ((congrArg (fun φ : Spec Γ(Y, Y.basicOpen h) ⟶ Y ↦ φ u)
        (hV'.map_fromSpec (hV'.basicOpen h) (homOfLE (Y.basicOpen_le h)).op)).trans hu))
  obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback
    (((pullback g).obj A).obj.isPullback_proj_restrictGradedSections h hV'
      (homOfLE (Y.basicOpen_le h))) y u hu'.symm
  exact ⟨p, hp⟩

/-- **Independence of `U`**: the chart over `V` does not depend on the affine open `U` of `X`
with `V ⊆ g⁻¹ U` through which it is formed. The two charts agree on the open cover of
`Proj (⨁ n, Γ((g^* A)ₙ, V))` by `Proj` of the sections over the basic opens `D(h) ⊆ V` that lie
over basic opens common to `U₁` and `U₂` (`exists_basicOpen_le_affine_inter`): there both are the
chart through that common basic open, by `proj_map_restrict_projPullbackToRelativeProj` and
`projPullbackToRelativeProj_basicOpen`. -/
theorem projPullbackToRelativeProj_eq {U₁ U₂ : X.Opens} (hU₁ : IsAffineOpen U₁)
    (hU₂ : IsAffineOpen U₂) (hV₁ : V ≤ g ⁻¹ᵁ U₁) (hV₂ : V ≤ g ⁻¹ᵁ U₂) :
    projPullbackToRelativeProj g A hU₁ hV' hV₁ = projPullbackToRelativeProj g A hU₂ hV' hV₂ :=
  -- the basic opens of `V` lying over basic opens common to `U₁` and `U₂`
  let J := {h : Γ(Y, V) // ∃ (f₁ : Γ(X, U₁)) (f₂ : Γ(X, U₂)),
    X.basicOpen f₁ = X.basicOpen f₂ ∧ Y.basicOpen h ≤ g ⁻¹ᵁ X.basicOpen f₁}
  Scheme.Cover.hom_ext (Scheme.Cover.mkOfCovers J
    (fun h ↦ Proj (((pullback g).obj A).obj.gradedSectionsGrading (Y.basicOpen h.1)))
    (fun h ↦ Proj.map _ (((pullback g).obj A).obj.irrelevant_le_map_restrictGradedSectionsGradedHom
      h.1 hV' (homOfLE (Y.basicOpen_le h.1))))
    (fun y ↦ by
      have hy : hV'.fromSpec (Proj.toSpecCoeff _ y) ∈ V := by
        change _ ∈ (V : Set Y)
        rw [← hV'.range_fromSpec]
        exact ⟨_, rfl⟩
      obtain ⟨h, f₁, f₂, e, hle, hyh⟩ :=
        exists_basicOpen_le_preimage_basicOpen g hV' hU₁ hU₂ hV₁ hV₂ hy
      let j : J := ⟨h, f₁, f₂, e, hle⟩
      exact ⟨j, exists_proj_map_restrictGradedSections_eq g A hV' j.1 y hyh⟩)
    fun h ↦ isOpenImmersion_proj_map_restrictGradedSections g A hV' h.1) _ _ fun h ↦
      proj_map_restrict_projPullbackToRelativeProj_eq g A hV' hU₁ hU₂ hV₁ hV₂
        h.2.choose_spec.choose_spec.1 h.2.choose_spec.choose_spec.2

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

/-- **The pullback of a graded algebra generated in degree one is generated in degree one.** Over
the basic opens of an affine open of `Y` lying over affine opens of `X` this is
`adjoin_gradedSectionsGrading_pullback_eq_top`, and generation in degree one is local
(`CategoryTheory.CommMon.adjoin_gradedSectionsGrading_eq_top_of_span_eq_top`). -/
theorem isGeneratedInDegreeOne_pullback (hA : A.obj.IsGeneratedInDegreeOne) :
    ((pullback g).obj A).obj.IsGeneratedInDegreeOne :=
  CommMon.isGeneratedInDegreeOne_iff.mpr fun _ hV' ↦
    ((pullback g).obj A).obj.adjoin_gradedSectionsGrading_eq_top_of_span_eq_top hV' _
      (span_setOf_basicOpen_le_preimage_eq_top hV') fun _ ⟨U, hU, hle⟩ ↦
        adjoin_gradedSectionsGrading_pullback_eq_top A hU (hV'.basicOpen _) hle
          (CommMon.isGeneratedInDegreeOne_iff.mp hA U hU)

end GradedQuasicoherentAlgebra

end

end AlgebraicGeometry

end TauCeti
