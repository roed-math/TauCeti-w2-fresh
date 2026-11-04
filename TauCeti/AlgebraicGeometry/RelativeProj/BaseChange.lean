/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.PullbackBaseChange
public import TauCeti.AlgebraicGeometry.RelativeProj.Basic

/-!
# The relative `Proj` of a pulled-back graded algebra

Let `g : X ⟶ Y` be a morphism of schemes and `A` a graded quasicoherent algebra on `Y`. Over
affine opens `U` of `Y` and `V ≤ g⁻¹ U` of `X`, pullback of sections gives the morphism
`Proj (⨁ n, Γ(g^* Aₙ, V)) ⟶ Proj (⨁ n, Γ(Aₙ, U))` from a chart of the relative `Proj` of `g^* A`
to a chart of the relative `Proj` of `A`, which is a base change
(`GradedQuasicoherentAlgebra.isPullback_proj_pullbackGradedSections`). These morphisms commute
with the transition maps of both relative `Proj`s, so they glue, along the locally directed open
cover of the relative `Proj` of `g^* A` by the charts over the pairs `V ≤ g⁻¹ U`, to a morphism
`Proj_X(g^* A) ⟶ Proj_Y(A)` over `g`; the resulting square is cartesian.

## Main results

In the namespace `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra`:

* `relativeProjGluingData_functor_map_comp_proj_map` and
  `proj_map_comp_relativeProjGluingData_functor_map`: the chart morphisms commute with the
  transition maps of the relative `Proj` of `g^* A`, respectively of `A`;
* `relativeProjPullbackCover`: the locally directed open cover of the relative `Proj` of `g^* A`
  by its charts over the pairs of affine opens `V ≤ g⁻¹ U`;
* `relativeProjPullbackHom`: the projection `Proj_X(g^* A) ⟶ Proj_Y(A)`, with
  `relativeProjCover_f_relativeProjPullbackHom` (its value on charts) and
  `relativeProjPullbackHom_relativeProjToBase` (it lies over `g`);
* `isPullback_relativeProjPullbackHom`: the square formed by the projection, the structure
  morphisms and `g` is cartesian.

## References

* [The Stacks Project, Lemma 27.16.10](https://stacks.math.columbia.edu/tag/01O3)
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry Scheme.AffineZariskiSite

universe u

namespace GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (A : GradedQuasicoherentAlgebra Y)

/-- Restricting the pullback of sections of `A` from `V` to `V' ≤ V` is pulling them back to `V'`,
as graded ring homomorphisms. -/
theorem restrictGradedSectionsGradedHom_comp_pullbackGradedSectionsGradedHom {U : Y.Opens}
    {V V' : X.Opens} (hV : V ≤ g ⁻¹ᵁ U) (i : V' ⟶ V) :
    (((pullback g).obj A).obj.restrictGradedSectionsGradedHom i).comp
        (A.pullbackGradedSectionsGradedHom g hV) =
      A.pullbackGradedSectionsGradedHom g ((leOfHom i).trans hV) :=
  GradedRingHom.ext fun x ↦ by
    simp [← A.restrictGradedSections_comp_pullbackGradedSections g hV i]

/-- Pulling back sections of `A` restricted from `U` to `U' ≤ U` is pulling them back from `U`,
as graded ring homomorphisms. -/
theorem pullbackGradedSectionsGradedHom_comp_restrictGradedSectionsGradedHom {U U' : Y.Opens}
    {V : X.Opens} (hV : V ≤ g ⁻¹ᵁ U) (j : U' ⟶ U) (hV' : V ≤ g ⁻¹ᵁ U') :
    (A.pullbackGradedSectionsGradedHom g hV').comp (A.obj.restrictGradedSectionsGradedHom j) =
      A.pullbackGradedSectionsGradedHom g hV :=
  GradedRingHom.ext fun x ↦ by
    simp [← A.pullbackGradedSections_comp_restrictGradedSections g hV j hV']

/-- The morphisms from the charts of the relative `Proj` of `g^* A` to the chart
`Proj (⨁ n, Γ(Aₙ, U))` commute with the transition maps of the relative `Proj` of `g^* A`. -/
@[reassoc]
theorem relativeProjGluingData_functor_map_comp_proj_map {U : Y.Opens} (hU : IsAffineOpen U)
    {V' V : X.AffineZariskiSite} (i : V' ⟶ V) (hV : V.toOpens ≤ g ⁻¹ᵁ U) :
    ((pullback g).obj A).obj.relativeProjGluingData.functor.map i ≫
        Proj.map (A.pullbackGradedSectionsGradedHom g hV)
          (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV hU V.2) =
      Proj.map (A.pullbackGradedSectionsGradedHom g ((leOfHom ((toOpensFunctor X).map i)).trans hV))
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g _ hU V'.2) := by
  rw [CommMon.relativeProjGluingData_functor_map]
  exact (Proj.map_comp ..).symm.trans (Proj.map_congr
    (A.restrictGradedSectionsGradedHom_comp_pullbackGradedSectionsGradedHom g hV _) _ _)

/-- The morphisms from a chart `Proj (⨁ n, Γ(g^* Aₙ, V))` of the relative `Proj` of `g^* A` to the
charts of the relative `Proj` of `A` commute with the transition maps of the relative `Proj`
of `A`. -/
@[reassoc]
theorem proj_map_comp_relativeProjGluingData_functor_map {U' U : Y.AffineZariskiSite} (j : U' ⟶ U)
    {V : X.Opens} (hV' : IsAffineOpen V) (hV : V ≤ g ⁻¹ᵁ U'.toOpens) :
    Proj.map (A.pullbackGradedSectionsGradedHom g hV)
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U'.2 hV') ≫
        A.obj.relativeProjGluingData.functor.map j =
      Proj.map (A.pullbackGradedSectionsGradedHom g
          (hV.trans fun _ hx ↦ leOfHom ((toOpensFunctor Y).map j) hx))
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g _ U.2 hV') := by
  rw [CommMon.relativeProjGluingData_functor_map]
  exact (Proj.map_comp ..).symm.trans (Proj.map_congr
    (A.pullbackGradedSectionsGradedHom_comp_restrictGradedSectionsGradedHom g _ _ hV) _ _)

/-- The morphisms `Proj (⨁ n, Γ(g^* Aₙ, V)) ⟶ Proj (⨁ n, Γ(Aₙ, U)) ⟶ Proj_Y(A)` induced by pullback
of sections, over the pairs of affine opens `V ≤ g⁻¹ U`, commute with the transition maps of the
relative `Proj` of `g^* A`. -/
@[reassoc]
theorem relativeProjGluingData_functor_map_comp_proj_map_comp_relativeProjCover_f
    {V V' : X.AffineZariskiSite} {U U' : Y.AffineZariskiSite} (hVV' : V ≤ V') (hUU' : U ≤ U')
    (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) (hV' : V'.toOpens ≤ g ⁻¹ᵁ U'.toOpens) :
    ((pullback g).obj A).obj.relativeProjGluingData.functor.map (homOfLE hVV') ≫
        Proj.map (A.pullbackGradedSectionsGradedHom g hV')
          (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV' U'.2 V'.2) ≫
        A.obj.relativeProjCover.f U' =
      Proj.map (A.pullbackGradedSectionsGradedHom g hV)
          (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2) ≫
        A.obj.relativeProjCover.f U := by
  have hw : A.obj.relativeProjGluingData.functor.map (homOfLE hUU') ≫
      A.obj.relativeProjCover.f U' = A.obj.relativeProjCover.f U :=
    Limits.colimit.w _ _
  exact (relativeProjGluingData_functor_map_comp_proj_map_assoc g A U'.2 _ hV' _).trans
    ((proj_map_comp_relativeProjGluingData_functor_map_assoc g A (homOfLE hUU') V.2 hV _).symm.trans
      (congrArg (_ ≫ ·) hw))

/-- The open cover of the relative `Proj` of `g^* A` by its charts `Proj (⨁ n, Γ(g^* Aₙ, V))` over
the affine opens `V` of `X` lying over an affine open `U` of `Y`, indexed by the pairs `(V, U)`
with `V ≤ g⁻¹ U`. -/
@[expose]
noncomputable def relativeProjPullbackCover : ((pullback g).obj A).obj.relativeProj.OpenCover :=
  .mkOfCovers {p : X.AffineZariskiSite × Y.AffineZariskiSite // p.1.toOpens ≤ g ⁻¹ᵁ p.2.toOpens}
    (fun p ↦ ((pullback g).obj A).obj.relativeProjCover.X p.1.1)
    (fun p ↦ ((pullback g).obj A).obj.relativeProjCover.f p.1.1) fun y ↦ by
      obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (g (((pullback g).obj A).obj.relativeProjToBase y))) isOpen_univ
      -- membership in a preimage of opens is membership of the image, by definition
      obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
        (show ((pullback g).obj A).obj.relativeProjToBase y ∈ g ⁻¹ᵁ U from hyU) (g ⁻¹ᵁ U).2
      -- `⟨V, hV⟩.toOpens` is `V` by definition; `hyV` is stated for `V`
      have hy := ((pullback g).obj A).obj.relativeProjToBase_preimage ⟨V, hV⟩ ▸
        (show y ∈ ((pullback g).obj A).obj.relativeProjToBase ⁻¹ᵁ V from hyV)
      obtain ⟨z, rfl⟩ := hy
      exact ⟨⟨(⟨V, hV⟩, ⟨U, hU⟩), hVU⟩, z, rfl⟩

/-- The pairs `(V, U)` indexing `relativeProjPullbackCover` are ordered componentwise by the small
affine Zariski sites of `X` and `Y`. -/
instance : Preorder (relativeProjPullbackCover g A).I₀ :=
  inferInstanceAs <| Preorder
    {p : X.AffineZariskiSite × Y.AffineZariskiSite // p.1.toOpens ≤ g ⁻¹ᵁ p.2.toOpens}

/-- The cover `relativeProjPullbackCover` is locally directed, with the transition maps of the
relative `Proj` of `g^* A`. -/
noncomputable instance : (relativeProjPullbackCover g A).LocallyDirected where
  trans {i j} hij := ((pullback g).obj A).obj.relativeProjGluingData.functor.map
    (homOfLE (leOfHom hij).1)
  trans_id i := CategoryTheory.Functor.map_id _ _
  trans_comp hij hjk := CategoryTheory.Functor.map_comp _ _ _
  w hij := Limits.colimit.w _ _
  directed {i j} x := by
    obtain ⟨k, hki, hkj, y, rfl⟩ : ∃ (k : X.AffineZariskiSite) (hki : k ⟶ i.1.1) (hkj : k ⟶ j.1.1)
        (y : ((pullback g).obj A).obj.relativeProjCover.X k),
        Limits.pullback.lift (((pullback g).obj A).obj.relativeProjGluingData.functor.map hki)
          (((pullback g).obj A).obj.relativeProjGluingData.functor.map hkj)
          ((Limits.colimit.w _ _).trans (Limits.colimit.w _ _).symm) y = x :=
      Scheme.Cover.LocallyDirected.directed
        (𝒰 := ((pullback g).obj A).obj.relativeProjGluingData.cover) (i := i.1.1) (j := j.1.1) x
    have hk : ((pullback g).obj A).obj.relativeProjCover.f k y ∈
        ((pullback g).obj A).obj.relativeProjToBase ⁻¹ᵁ k.toOpens := by
      rw [CommMon.relativeProjToBase_preimage _ k]
      exact ⟨y, rfl⟩
    set p := ((pullback g).obj A).obj.relativeProjToBase
      (((pullback g).obj A).obj.relativeProjCover.f k y)
    obtain ⟨a, b, e, hpa⟩ := exists_basicOpen_le_affine_inter i.1.2.2 j.1.2.2 (g p)
      ⟨i.2 (toOpens_mono (leOfHom hki) hk), j.2 (toOpens_mono (leOfHom hkj) hk)⟩
    obtain ⟨h, hh, hph⟩ := k.2.exists_basicOpen_le
      (V := g ⁻¹ᵁ (i.1.2.basicOpen a).toOpens) ⟨p, hpa⟩ hk
    obtain ⟨z, hz⟩ : ((pullback g).obj A).obj.relativeProjCover.f k y ∈
        (((pullback g).obj A).obj.relativeProjCover.f (k.basicOpen h)).opensRange := by
      rw [← CommMon.relativeProjToBase_preimage _ (k.basicOpen h)]
      exact hph
    have hlk : k.basicOpen h ⟶ k := homOfLE (k.basicOpen_le h)
    refine ⟨⟨(k.basicOpen h, i.1.2.basicOpen a), hh⟩,
      homOfLE ⟨(k.basicOpen_le h).trans (leOfHom hki), i.1.2.basicOpen_le a⟩,
      homOfLE ⟨(k.basicOpen_le h).trans (leOfHom hkj), b, e.symm⟩, z, ?_⟩
    obtain rfl : ((pullback g).obj A).obj.relativeProjGluingData.functor.map hlk z = y :=
      (((pullback g).obj A).obj.relativeProjCover.f k).isOpenEmbedding.injective (by
        have hw : ((pullback g).obj A).obj.relativeProjGluingData.functor.map hlk ≫
            ((pullback g).obj A).obj.relativeProjCover.f k =
              ((pullback g).obj A).obj.relativeProjCover.f (k.basicOpen h) :=
          Limits.colimit.w _ _
        rw [← hz, ← hw]
        exact (Scheme.Hom.comp_apply _ _ _).symm)
    refine Eq.trans ?_ (Scheme.Hom.comp_apply _ _ z)
    -- reduce the equality of points to the equality of morphisms into the pullback
    congr 5
    exact Limits.pullback.hom_ext
      ((Limits.pullback.lift_fst _ _ _).trans
        ((((pullback g).obj A).obj.relativeProjGluingData.functor.map_comp hlk hki).trans
          ((congrArg (_ ≫ ·) (Limits.pullback.lift_fst _ _ _).symm).trans
            (Category.assoc _ _ _).symm)))
      ((Limits.pullback.lift_snd _ _ _).trans
        ((((pullback g).obj A).obj.relativeProjGluingData.functor.map_comp hlk hkj).trans
          ((congrArg (_ ≫ ·) (Limits.pullback.lift_snd _ _ _).symm).trans
            (Category.assoc _ _ _).symm)))
  property_trans hij := by
    -- the transition maps of the cover are by definition those of the relative `Proj` of `g^* A`;
    -- instance search does not unfold the index type of the cover
    change IsOpenImmersion (((pullback g).obj A).obj.relativeProjGluingData.functor.map
      (homOfLE (leOfHom hij).1 : (_ : X.AffineZariskiSite) ⟶ _))
    infer_instance

/-- **The projection from the relative `Proj` of `g^* A` to that of `A`.** On the chart
`Proj (⨁ n, Γ(g^* Aₙ, V))` over an affine open `V ≤ g⁻¹ U` of `X`, with `U` an affine open of `Y`,
it is the morphism `Proj (⨁ n, Γ(g^* Aₙ, V)) ⟶ Proj (⨁ n, Γ(Aₙ, U))` induced by pullback of
sections, followed by the chart of the relative `Proj` of `A` over `U`. -/
noncomputable def relativeProjPullbackHom :
    ((pullback g).obj A).obj.relativeProj ⟶ A.obj.relativeProj :=
  (relativeProjPullbackCover g A).glueMorphismsOfLocallyDirected
    (fun i ↦ Proj.map (A.pullbackGradedSectionsGradedHom g i.2)
      (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g i.2 i.1.2.2 i.1.1.2) ≫
        A.obj.relativeProjCover.f i.1.2) fun {i j} hij ↦
    relativeProjGluingData_functor_map_comp_proj_map_comp_relativeProjCover_f g A
      (leOfHom hij).1 (leOfHom hij).2 i.2 j.2

/-- On the chart `Proj (⨁ n, Γ(g^* Aₙ, V))` over an affine open `V ≤ g⁻¹ U`, the projection
`relativeProjPullbackHom` is induced by pullback of sections from `U`. -/
@[reassoc]
theorem relativeProjCover_f_relativeProjPullbackHom (V : X.AffineZariskiSite)
    (U : Y.AffineZariskiSite) (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    ((pullback g).obj A).obj.relativeProjCover.f V ≫ relativeProjPullbackHom g A =
      Proj.map (A.pullbackGradedSectionsGradedHom g hV)
          (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.2 V.2) ≫
        A.obj.relativeProjCover.f U :=
  (relativeProjPullbackCover g A).map_glueMorphismsOfLocallyDirected _
    (fun hij ↦ relativeProjGluingData_functor_map_comp_proj_map_comp_relativeProjCover_f g A
      (leOfHom hij).1 (leOfHom hij).2 _ _) ⟨(V, U), hV⟩

/-- The projection `relativeProjPullbackHom` lies over `g`. -/
@[reassoc]
theorem relativeProjPullbackHom_relativeProjToBase :
    relativeProjPullbackHom g A ≫ A.obj.relativeProjToBase =
      ((pullback g).obj A).obj.relativeProjToBase ≫ g := by
  refine (relativeProjPullbackCover g A).hom_ext _ _ fun i ↦ ?_
  obtain ⟨⟨V, U⟩, hV⟩ := i
  -- the charts of `relativeProjPullbackCover` are by definition charts of the relative `Proj`
  change ((pullback g).obj A).obj.relativeProjCover.f V ≫ _ =
    ((pullback g).obj A).obj.relativeProjCover.f V ≫ _
  exact (relativeProjCover_f_relativeProjPullbackHom_assoc g A V U hV _).trans
    ((congrArg (_ ≫ ·) (A.obj.relativeProjCover_f_relativeProjToBase U)).trans
      (((A.isPullback_proj_pullbackGradedSections g hV U.2 V.2).w_assoc _).trans
        ((congrArg (_ ≫ ·) (IsAffineOpen.SpecMap_appLE_fromSpec g U.2 V.2 hV)).trans
          (((pullback g).obj A).obj.relativeProjCover_f_relativeProjToBase_assoc V g).symm)))

/-- **The relative `Proj` of `g^* A` is the base change of the relative `Proj` of `A`**: the
square formed by the projection `relativeProjPullbackHom`, the structure morphisms and `g` is
cartesian. -/
theorem isPullback_relativeProjPullbackHom :
    IsPullback ((pullback g).obj A).obj.relativeProjToBase (relativeProjPullbackHom g A) g
      A.obj.relativeProjToBase := by
  let 𝒰 : X.OpenCover := .mkOfCovers
    {p : X.AffineZariskiSite × Y.AffineZariskiSite // p.1.toOpens ≤ g ⁻¹ᵁ p.2.toOpens}
    (fun p ↦ Spec Γ(X, p.1.1.toOpens)) (fun p ↦ p.1.1.2.fromSpec) fun x ↦ by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g x)) isOpen_univ
      -- membership in a preimage of opens is membership of the image, by definition
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ g ⁻¹ᵁ U from hxU) (g ⁻¹ᵁ U).2
      have hV' : IsAffineOpen V := hV
      obtain ⟨z, hz⟩ : x ∈ Set.range hV'.fromSpec := by
        rw [hV'.range_fromSpec]
        exact hxV
      exact ⟨⟨(⟨V, hV⟩, ⟨U, hU⟩), hVU⟩, z, hz⟩
  refine Scheme.isPullback_of_openCover _ _ _ _ 𝒰 fun i ↦ ?_
  obtain ⟨⟨V, U⟩, hV⟩ := i
  have hchart := (((pullback g).obj A).obj.isPullback_relativeProjCover_fromSpec V).flip
  have hQ := ((A.isPullback_proj_pullbackGradedSections g hV U.2 V.2).paste_horiz
    (A.obj.isPullback_relativeProjCover_fromSpec U).flip).flip
  rw [← relativeProjCover_f_relativeProjPullbackHom g A V U hV,
    IsAffineOpen.SpecMap_appLE_fromSpec g U.2 V.2 hV] at hQ
  -- the pullback of the cover `𝒰` along the structure morphism is, by definition, given by the
  -- projections of the pullbacks of its charts
  change IsPullback (Limits.pullback.snd ((pullback g).obj A).obj.relativeProjToBase V.2.fromSpec)
    (Limits.pullback.fst _ _ ≫ relativeProjPullbackHom g A) (V.2.fromSpec ≫ g)
    A.obj.relativeProjToBase
  exact hQ.of_iso hchart.isoPullback (.refl _) (.refl _) (.refl _)
    ((Category.comp_id _).trans hchart.isoPullback_hom_snd.symm)
    ((Category.comp_id _).trans (hchart.isoPullback_hom_fst_assoc _).symm) (by simp) (by simp)

end GradedQuasicoherentAlgebra

end TauCeti.AlgebraicGeometry
