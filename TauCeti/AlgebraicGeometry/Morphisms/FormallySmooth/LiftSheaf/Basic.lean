/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.Criterion

/-!
# The sheaf of lifts along a thickening

For `f : X ⟶ S`, `i : T ⟶ T'`, `a : T ⟶ X` and `h : T' ⟶ S`, the lifts of `a` along `i` over `S`
form a sheaf of sets on `T'`: its sections over an open `W` of `T'` are the morphisms
`l : W ⟶ X` with `i ∣_ W ≫ l = a` on `i ⁻¹ᵁ W` and `l ≫ f = h` on `W`. A lift of `a` to all of
`T'` is a section over `⊤`.

When `f` is smooth and `i` is a first-order thickening, the sheaf of lifts is locally nonempty:
this is the carrier of the torsor of lifts of Stacks, Lemma 37.9.5 (04FJ), and its triviality on
affine `T'` is what makes a smooth morphism formally smooth (Stacks, Lemma 37.11.7 (02H6)).

## Main definitions

* `TauCeti.AlgebraicGeometry.liftSheaf f i a h`: the sheaf of lifts of `a` along `i` over `S`.
* `TauCeti.AlgebraicGeometry.liftSheafObjEquiv f i a h W`: its sections over `W`.

## Main results

* `TauCeti.AlgebraicGeometry.nonempty_liftSheaf_top_iff`: the sheaf of lifts has a section over
  `⊤` if and only if `a` lifts along `i` over `S`.
* `TauCeti.AlgebraicGeometry.liftSheaf_coversTop`: for `f` smooth and `i` a first-order
  thickening with `a ≫ f = i ≫ h`, the sheaf of lifts is locally nonempty.
* `TauCeti.AlgebraicGeometry.subsingleton_liftSheaf`: for `f` formally unramified (for example
  étale) and `i` a first-order thickening, the sheaf of lifts has at most one section over every
  open.

## References

* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ).
-/

public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace TauCeti.AlgebraicGeometry

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) (i : T ⟶ T') (a : T ⟶ X) (h : T' ⟶ S)

/-- The presheaf of lifts of `a` along `i` over `S`: its sections over `W` are the morphisms
`l : W ⟶ X` with `i ∣_ W ≫ l = a` on `i ⁻¹ᵁ W` and `l ≫ f = h` on `W`, restricted along the
inclusions of opens. -/
noncomputable def liftPresheaf : TopCat.Presheaf (Type u) T' where
  obj W := { l : Scheme.Opens.toScheme (X := T') W.unop ⟶ X //
    i ∣_ W.unop ≫ l = (i ⁻¹ᵁ W.unop).ι ≫ a ∧ l ≫ f = Scheme.Opens.ι (X := T') W.unop ≫ h }
  map {W₁ W₂} e := TypeCat.ofHom fun l ↦ ⟨T'.homOfLE e.unop.le ≫ l.1, by
    have : i ∣_ W₂.unop ≫ T'.homOfLE e.unop.le =
        T.homOfLE (i.preimage_mono e.unop.le) ≫ i ∣_ W₁.unop := by
      simp [← cancel_mono (Scheme.Opens.ι (X := T') W₁.unop)]
    rw [reassoc_of% this, l.2.1, Scheme.homOfLE_ι_assoc], by
    rw [Category.assoc, l.2.2, Scheme.homOfLE_ι_assoc]⟩
  map_id W := by
    ext l
    change T'.homOfLE _ ≫ l.1 = l.1
    rw [Scheme.homOfLE_rfl, Category.id_comp]
  map_comp e₁ e₂ := by
    ext l
    exact (Scheme.homOfLE_homOfLE_assoc T' _ _ l.1).symm

variable {ι : Type u} (U : ι → T'.Opens)

/-- The opens `U j` cover their union. -/
private noncomputable abbrev iSupCover : (iSup U).toScheme.OpenCover where
  I₀ := ι
  X j := (U j).toScheme
  f j := T'.homOfLE (le_iSup U j)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 x.2
    exact ⟨j, ⟨x.1, hj⟩, Subtype.ext (by simp)⟩

/-- Morphisms out of the opens `U j` that agree on the intersections glue to the union. -/
private lemma iSupCover_compat (l : ∀ j, (U j).toScheme ⟶ X)
    (hl : ∀ j k, T'.homOfLE inf_le_left ≫ l j = T'.homOfLE (inf_le_right (a := U j)) ≫ l k)
    (j k : ι) :
    pullback.fst ((iSupCover U).f j) ((iSupCover U).f k) ≫ l j =
      pullback.snd ((iSupCover U).f j) ((iSupCover U).f k) ≫ l k := by
  change pullback.fst (T'.homOfLE (le_iSup U j)) (T'.homOfLE (le_iSup U k)) ≫ l j =
    pullback.snd (T'.homOfLE (le_iSup U j)) (T'.homOfLE (le_iSup U k)) ≫ l k
  rw [← cancel_epi (isPullback_opens_inf_le (le_iSup U j) (le_iSup U k)).isoPullback.hom,
    IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
  exact hl j k

/-- The presheaf of lifts is a sheaf: lifts on the opens `U j` that agree on the intersections
glue to a lift on their union. -/
theorem liftPresheaf_isSheaf : (liftPresheaf f i a h).IsSheaf := by
  refine TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types _ fun ι U sf hsf ↦ ?_
  have hl (j k : ι) : T'.homOfLE inf_le_left ≫ (sf j).1 =
      T'.homOfLE (inf_le_right (a := U j)) ≫ (sf k).1 :=
    congrArg Subtype.val (hsf j k)
  let 𝒰 := iSupCover U
  let L := 𝒰.glueMorphisms (fun j ↦ (sf j).1) (iSupCover_compat U _ hl)
  have hL (j : ι) : T'.homOfLE (le_iSup U j) ≫ L = (sf j).1 :=
    𝒰.ι_glueMorphisms (fun j ↦ (sf j).1) (iSupCover_compat U _ hl) j
  refine ⟨⟨L, ?_, Scheme.Cover.hom_ext 𝒰 _ _ fun (j : ι) ↦ ?_⟩, fun j ↦ Subtype.ext (hL j),
    fun s hs ↦ Subtype.ext <| Scheme.Cover.hom_ext 𝒰 _ _ fun (j : ι) ↦ ?_⟩
  · -- Over each `U j`, factor the pullback of `i ∣_ (iSup U)` through `i ∣_ U j`.
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ (i ∣_ iSup U)) _ _ fun (j : ι) ↦ ?_
    have hP := isPullback_morphismRestrict i (U j)
    have hr : pullback.snd (i ∣_ iSup U) (𝒰.f j) ≫ Scheme.Opens.ι (X := T') (U j) =
        (pullback.fst (i ∣_ iSup U) (𝒰.f j) ≫ (i ⁻¹ᵁ iSup U).ι) ≫ i := by
      rw [Category.assoc, ← morphismRestrict_ι, pullback.condition_assoc]
      exact congrArg (pullback.snd (i ∣_ iSup U) (𝒰.f j) ≫ ·)
        (Scheme.homOfLE_ι T' (le_iSup U j)).symm
    change pullback.fst (i ∣_ iSup U) (𝒰.f j) ≫ i ∣_ iSup U ≫ L =
      pullback.fst (i ∣_ iSup U) (𝒰.f j) ≫ (i ⁻¹ᵁ iSup U).ι ≫ a
    rw [pullback.condition_assoc]
    change _ ≫ T'.homOfLE (le_iSup U j) ≫ L = _
    rw [hL, ← hP.lift_fst _ _ hr, Category.assoc, (sf j).2.1, ← Category.assoc, hP.lift_snd,
      Category.assoc]
  · change T'.homOfLE (le_iSup U j) ≫ L ≫ f =
      T'.homOfLE (le_iSup U j) ≫ Scheme.Opens.ι (X := T') (iSup U) ≫ h
    rw [reassoc_of% hL, (sf j).2.2, Scheme.homOfLE_ι_assoc]
  · change T'.homOfLE (le_iSup U j) ≫ s.1 = T'.homOfLE (le_iSup U j) ≫ L
    rw [hL]
    exact congrArg Subtype.val (hs j)

/-- The sheaf of lifts of `a` along `i` over `S`: its sections over an open `W` of `T'` are the
morphisms `l : W ⟶ X` with `i ∣_ W ≫ l = a` on `i ⁻¹ᵁ W` and `l ≫ f = h` on `W`. -/
noncomputable def liftSheaf : TopCat.Sheaf (Type u) T' :=
  ⟨liftPresheaf f i a h, liftPresheaf_isSheaf f i a h⟩

/-- The sections of the sheaf of lifts over `W` are the morphisms `l : W ⟶ X` with
`i ∣_ W ≫ l = a` on `i ⁻¹ᵁ W` and `l ≫ f = h` on `W`. -/
noncomputable def liftSheafObjEquiv (W : T'.Opens) :
    (liftSheaf f i a h).obj.obj (op W) ≃
      { l : W.toScheme ⟶ X // i ∣_ W ≫ l = (i ⁻¹ᵁ W).ι ≫ a ∧ l ≫ f = W.ι ≫ h } :=
  Equiv.refl _

/-- Restricting a section of the sheaf of lifts to a smaller open `W' ⊆ W` precomposes the
morphism with `W' ⟶ W`. -/
@[simp]
theorem coe_liftSheafObjEquiv_map {W W' : T'.Opens} (e : W' ≤ W)
    (l : (liftSheaf f i a h).obj.obj (op W)) :
    (liftSheafObjEquiv f i a h W' ((liftSheaf f i a h).obj.map (homOfLE e).op l) :
        W'.toScheme ⟶ X) =
      T'.homOfLE e ≫ (liftSheafObjEquiv f i a h W l : W.toScheme ⟶ X) :=
  (rfl)

/-- The sheaf of lifts has a section over `⊤` if and only if `a` lifts along `i` over `S`. -/
theorem nonempty_liftSheaf_top_iff :
    Nonempty ((liftSheaf f i a h).obj.obj (op ⊤)) ↔
      ∃ l : T' ⟶ X, i ≫ l = a ∧ l ≫ f = h := by
  refine ⟨fun ⟨l⟩ ↦ ⟨T'.topIso.inv ≫ l.1, ?_, ?_⟩, fun ⟨l, hl₁, hl₂⟩ ↦
    ⟨⟨(⊤ : T'.Opens).ι ≫ l, ?_, ?_⟩⟩⟩
  · -- `T` is the open `i ⁻¹ᵁ ⊤` of itself.
    let e : T ⟶ (i ⁻¹ᵁ ⊤).toScheme :=
      IsOpenImmersion.lift (i ⁻¹ᵁ ⊤).ι (𝟙 T) fun x _ ↦ ⟨⟨x, trivial⟩, rfl⟩
    have he : e ≫ (i ⁻¹ᵁ ⊤).ι = 𝟙 T := IsOpenImmersion.lift_fac _ _ _
    have hi : i ≫ T'.topIso.inv = e ≫ i ∣_ ⊤ := by
      rw [← cancel_mono (⊤ : T'.Opens).ι, Category.assoc, Scheme.toIso_inv_ι, Category.comp_id,
        Category.assoc, morphismRestrict_ι, reassoc_of% he]
    rw [reassoc_of% hi, l.2.1, reassoc_of% he]
  · rw [Category.assoc, l.2.2, Scheme.toIso_inv_ι_assoc]
  · rw [morphismRestrict_ι_assoc, hl₁]
  · rw [Category.assoc, hl₂]

/-- Lifts into a formally unramified morphism along a first-order thickening are unique: the sheaf
of lifts has at most one section over every open. -/
instance subsingleton_liftSheaf [FormallyUnramified f] [IsFirstOrderThickening i] (W : T'.Opens) :
    Subsingleton ((liftSheaf f i a h).obj.obj (op W)) :=
  ⟨fun l₁ l₂ ↦ Subtype.ext <| FormallyUnramified.hom_ext (i ∣_ W)
    (IsFirstOrderThickening.isNilpotent_ker _) f (l₁.2.1.trans l₂.2.1.symm)
    (l₁.2.2.trans l₂.2.2.symm)⟩

/-- For `f` smooth and `i` a first-order thickening with `a ≫ f = i ≫ h`, every point of `T'` has
an affine open neighbourhood over which `a` lifts along `i` over `S`. -/
theorem exists_nonempty_liftSheaf_of_smooth [Smooth f] [IsFirstOrderThickening i]
    (w : a ≫ f = i ≫ h) (x : T') :
    ∃ W : T'.Opens, IsAffineOpen W ∧ x ∈ W ∧ Nonempty ((liftSheaf f i a h).obj.obj (op W)) := by
  obtain ⟨W, hW, hxW, l, hl₁, hl₂⟩ := exists_local_lift_of_smooth f i a h w x
  refine ⟨W, hW, hxW, ⟨⟨l, ?_, hl₂⟩⟩⟩
  rw [← cancel_epi (pullbackRestrictIsoRestrict i W).hom,
    reassoc_of% pullbackRestrictIsoRestrict_hom_morphismRestrict, hl₁,
    ← pullbackRestrictIsoRestrict_inv_fst_assoc, Iso.hom_inv_id_assoc]

/-- For `f` smooth and `i` a first-order thickening with `a ≫ f = i ≫ h`, the sheaf of lifts is
locally nonempty: the opens over which it has a section cover `T'`. -/
theorem liftSheaf_coversTop [Smooth f] [IsFirstOrderThickening i] (w : a ≫ f = i ≫ h) :
    (Opens.grothendieckTopology T').CoversTop
      fun W : { W : T'.Opens // Nonempty ((liftSheaf f i a h).obj.obj (op W)) } ↦ W.1 := by
  rw [Opens.coversTop_iff]
  refine eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ?_
  obtain ⟨W, -, hxW, hW⟩ := exists_nonempty_liftSheaf_of_smooth f i a h w x
  exact ⟨⟨W, hW⟩, hxW⟩

end TauCeti.AlgebraicGeometry
