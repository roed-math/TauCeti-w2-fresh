/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Gluing two schemes along an open subscheme

A scheme covered by two opens is glued from them along their intersection, and conversely two
schemes `U` and `V` can be glued along open immersions `W ⟶ U` and `W ⟶ V`. In category-theoretic
terms, these are pushouts of open immersions in the category of schemes. This is the gluing step of
the descent of schemes of finite presentation along cofiltered limits (Stacks, Lemma 01ZM), which
proceeds by induction on the number of affine opens covering the scheme.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.isPushout_opens_of_sup_eq_top`: if `U ⊔ V = ⊤` for opens of
  `X`, then `X` is the pushout of `U ⟵ U ⊓ V ⟶ V`.
* `TauCeti.AlgebraicGeometry.Scheme.isPushout_of_isPullback_of_opensRange_sup_eq_top`: a pullback
  square of open immersions into `X` whose images cover `X` is a pushout. Since open immersions,
  pullback squares and covers are stable under base change, so are such pushouts.
* `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_opensRange_sup_eq_top`: a property local at the
  source holds for `f : X ⟶ Y` if and only if it holds on two opens covering `X`; in particular
  (`AlgebraicGeometry.IsZariskiLocalAtSource.pushout_desc_iff`) for a morphism out of a gluing.
* For open immersions `f : W ⟶ U` and `g : W ⟶ V`, the pushout of `f` and `g` exists (from Mathlib's
  colimits of locally directed diagrams of open immersions), `pushout.inl f g` and
  `pushout.inr f g` are open immersions whose images cover the pushout
  (`opensRange_pushout_inl_sup_opensRange_pushout_inr`), and the square is also a pullback
  (`isPullback_pushout`). The pushout is quasi-compact if `U` and `V` are, and quasi-separated if
  `U` and `V` are and `f` and `g` are quasi-compact.
* `TauCeti.AlgebraicGeometry.Scheme.isPullback_of_isPullback_of_opensRange_sup_eq_top`: a
  commutative square whose target corner is covered by two opens is a pullback as soon as it
  restricts to pullback squares over the two opens and over their intersection.
* `TauCeti.AlgebraicGeometry.Scheme.isPullback_pushout_desc_of_isPullback`: base change commutes
  with gluing. If `X` is covered by `U` and `V`, and `U`, `V`, `U ⊓ V` are the base changes along
  `S ⟶ T` of compatible schemes `YU`, `YV`, `W` over `T`, then `X` is the base change of the scheme
  glued from `YU` and `YV` along `W`. This is how the descended models of finitely presented
  schemes are glued.
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- A scheme covered by two opens `U` and `V` is the pushout of `U` and `V` along `U ⊓ V`. -/
theorem isPushout_opens_of_sup_eq_top {U V : X.Opens} (h : U ⊔ V = ⊤) :
    IsPushout (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (X.homOfLE inf_le_right) U.ι V.ι := by
  have hUV : TopologicalSpace.IsOpenCover (fun b : Bool ↦ bif b then U else V) := by
    rw [TopologicalSpace.IsOpenCover, iSup_bool_eq]
    exact h
  let 𝒰 := X.openCoverOfIsOpenCover _ hUV
  have hU : pullback.fst U.ι U.ι = pullback.snd U.ι U.ι := by
    rw [← cancel_mono U.ι, pullback.condition]
  have hV : pullback.fst V.ι V.ι = pullback.snd V.ι V.ι := by
    rw [← cancel_mono V.ι, pullback.condition]
  refine ⟨⟨by simp⟩, ⟨PushoutCocone.IsColimit.mk _ (fun s ↦ 𝒰.glueMorphisms
      (fun b ↦ Bool.casesOn (motive := fun b ↦ 𝒰.X b ⟶ s.pt) b s.inr s.inl) ?_) ?_ ?_ ?_⟩⟩
  · rintro (_ | _) (_ | _)
    · exact hV ▸ rfl
    -- The components of `𝒰` are `U.ι` and `V.ι` only after unfolding `cond`.
    · change pullback.fst V.ι U.ι ≫ s.inr = pullback.snd V.ι U.ι ≫ s.inl
      rw [← cancel_epi (isPullback_opens_inf U V).flip.isoPullback.hom]
      simpa using s.condition.symm
    · change pullback.fst U.ι V.ι ≫ s.inl = pullback.snd U.ι V.ι ≫ s.inr
      rw [← cancel_epi (isPullback_opens_inf U V).isoPullback.hom]
      simpa using s.condition
    · exact hU ▸ rfl
  · intro s
    exact 𝒰.ι_glueMorphisms _ _ true
  · intro s
    exact 𝒰.ι_glueMorphisms _ _ false
  · intro s m hl hr
    refine 𝒰.hom_ext _ _ fun b ↦ ?_
    rw [𝒰.ι_glueMorphisms]
    cases b
    · exact hr
    · exact hl

/-- A pullback square of open immersions `U ⟶ X ⟵ V` whose images cover `X` is a pushout:
`X` is glued from `U` and `V` along `W = U ×_X V`. -/
theorem isPushout_of_isPullback_of_opensRange_sup_eq_top {W U V : Scheme.{u}} {f : W ⟶ U}
    {g : W ⟶ V} {i : U ⟶ X} {j : V ⟶ X} [IsOpenImmersion i] [IsOpenImmersion j]
    (h : IsPullback f g i j)
    (hX : i.opensRange ⊔ j.opensRange = ⊤) : IsPushout f g i j := by
  have hI : IsPullback (X.homOfLE inf_le_left ≫ i.isoOpensRange.inv)
      (X.homOfLE inf_le_right ≫ j.isoOpensRange.inv) i j :=
    (isPullback_opens_inf i.opensRange j.opensRange).of_iso (Iso.refl _) i.isoOpensRange.symm
      j.isoOpensRange.symm (Iso.refl X) (by simp) (by simp) (by simp) (by simp)
  have hf := h.isoIsPullback_hom_fst _ _ hI
  have hg := h.isoIsPullback_hom_snd _ _ hI
  refine (isPushout_opens_of_sup_eq_top hX).of_iso' (h.isoIsPullback _ _ hI) i.isoOpensRange
    j.isoOpensRange (Iso.refl X) ?_ ?_ (by simp) (by simp)
  · rw [← Iso.comp_inv_eq, Category.assoc, hf]
  · rw [← Iso.comp_inv_eq, Category.assoc, hg]

/-- A property local at the source holds for `f : X ⟶ Y` if and only if it holds on two open
subschemes covering `X`. -/
theorem _root_.AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_opensRange_sup_eq_top
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P] {U V Y : Scheme.{u}}
    {i : U ⟶ X} {j : V ⟶ X} [IsOpenImmersion i] [IsOpenImmersion j]
    (hX : i.opensRange ⊔ j.opensRange = ⊤) (f : X ⟶ Y) :
    P f ↔ P (i ≫ f) ∧ P (j ≫ f) := by
  refine ⟨fun H ↦ ⟨IsZariskiLocalAtSource.comp H i, IsZariskiLocalAtSource.comp H j⟩,
    fun ⟨hi, hj⟩ ↦ IsZariskiLocalAtSource.of_iSup_eq_top
      (fun b : Bool ↦ bif b then i.opensRange else j.opensRange)
      (by rw [iSup_bool_eq]; exact hX) fun b ↦ ?_⟩
  -- `bif b then _ else _` only reduces to the two opens after unfolding `cond`.
  cases b
  · change P (j.opensRange.ι ≫ f)
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc]
    exact (P.cancel_left_of_respectsIso _ _).mpr hj
  · change P (i.opensRange.ι ≫ f)
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc]
    exact (P.cancel_left_of_respectsIso _ _).mpr hi

section Glue

variable {W U V : Scheme.{u}} (f : W ⟶ U) (g : W ⟶ V) [IsOpenImmersion f] [IsOpenImmersion g]

/-- The span of two open immersions is a locally directed diagram of open immersions. -/
instance isOpenImmersion_span_map {i j : WalkingSpan} (k : i ⟶ j) :
    IsOpenImmersion ((span f g).map k) := by
  cases k with
  | id => rw [WidePushoutShape.hom_id, CategoryTheory.Functor.map_id]; infer_instance
  | init j => cases j <;> simpa

/-- Two schemes can be glued along open immersions from a common scheme. -/
instance : HasPushout f g :=
  inferInstanceAs (HasColimit (span f g))

instance : IsOpenImmersion (pushout.inl f g) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span f g) _))

instance : IsOpenImmersion (pushout.inr f g) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span f g) _))

/-- The gluing of `U` and `V` along `W` is covered by the images of `U` and `V`. -/
theorem opensRange_pushout_inl_sup_opensRange_pushout_inr :
    (pushout.inl f g).opensRange ⊔ (pushout.inr f g).opensRange = ⊤ := by
  refine top_le_iff.mp fun x _ ↦ ?_
  obtain ⟨i, xi, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span f g) x
  rcases i with (_ | (_ | _))
  · refine Or.inl ⟨f xi, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    exact congr($(colimit.w (span f g) (WidePushoutShape.Hom.init WalkingPair.left)) xi)
  · exact Or.inl ⟨xi, rfl⟩
  · exact Or.inr ⟨xi, rfl⟩

/-- A property local at the source holds for a morphism out of the gluing of `U` and `V` if and
only if it holds on `U` and on `V`. -/
theorem _root_.AlgebraicGeometry.IsZariskiLocalAtSource.pushout_desc_iff
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P] {Y : Scheme.{u}} (a : U ⟶ Y)
    (b : V ⟶ Y) (w : f ≫ a = g ≫ b) : P (pushout.desc a b w) ↔ P a ∧ P b := by
  rw [IsZariskiLocalAtSource.iff_of_opensRange_sup_eq_top P
    (opensRange_pushout_inl_sup_opensRange_pushout_inr f g), pushout.inl_desc, pushout.inr_desc]

/-- Points of `U` and `V` with the same image in the gluing come from a point of `W`. -/
theorem exists_eq_of_pushout_inl_eq_pushout_inr {x : U} {y : V}
    (h : pushout.inl f g x = pushout.inr f g y) : ∃ w, f w = x ∧ g w = y := by
  obtain ⟨k, fi, fj, w, rfl, rfl⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (span f g)).mp h
  rcases k with (_ | (_ | _))
  · cases fi
    cases fj
    exact ⟨w, rfl, rfl⟩
  · cases fj
  · cases fi

/-- In the gluing of `U` and `V` along `W`, the images of `U` and `V` meet in the image of `W`. -/
theorem isPullback_pushout : IsPullback f g (pushout.inl f g) (pushout.inr f g) := by
  refine IsOpenImmersion.isPullback f g (pushout.inl f g) (pushout.inr f g)
    pushout.condition.symm ?_
  ext x
  -- Membership in `opensRange` and in a preimage are membership in `Set.range` and `Set.preimage`.
  change (pushout.inr f g) x ∈ Set.range (pushout.inl f g) ↔ x ∈ Set.range g
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨w, -, rfl⟩ := exists_eq_of_pushout_inl_eq_pushout_inr f g hy
    exact ⟨w, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨f z, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pushout.condition]⟩

/-- Gluing two quasi-compact schemes gives a quasi-compact scheme. -/
instance [CompactSpace U] [CompactSpace V] : CompactSpace (pushout f g : Scheme.{u}) := by
  refine ⟨?_⟩
  have h := congrArg (SetLike.coe : (pushout f g).Opens → _)
    (opensRange_pushout_inl_sup_opensRange_pushout_inr f g)
  simp only [TopologicalSpace.Opens.coe_sup, Scheme.Hom.coe_opensRange,
    TopologicalSpace.Opens.coe_top] at h
  rw [← h]
  exact (isCompact_range (pushout.inl f g).continuous).union
    (isCompact_range (pushout.inr f g).continuous)

/-- The intersection of the images of `A ⊆ U` and `B ⊆ V` in the gluing of `U` and `V` along `W`
is the image of `A ∩ f(g⁻¹(B))`. -/
theorem image_pushout_inl_inter_image_pushout_inr (A : Set U) (B : Set V) :
    pushout.inl f g '' A ∩ pushout.inr f g '' B = pushout.inl f g '' (A ∩ f '' (g ⁻¹' B)) := by
  ext x
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    obtain ⟨w, rfl, rfl⟩ := exists_eq_of_pushout_inl_eq_pushout_inr f g hab.symm
    exact ⟨f w, ⟨ha, w, hb, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨ha, w, hb, rfl⟩, rfl⟩
    refine ⟨⟨_, ha, rfl⟩, g w, hb, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pushout.condition]

/-- Gluing two quasi-separated schemes along quasi-compact opens gives a quasi-separated scheme. -/
instance [QuasiSeparatedSpace U] [QuasiSeparatedSpace V] [QuasiCompact f] [QuasiCompact g] :
    QuasiSeparatedSpace (pushout f g : Scheme.{u}) := by
  have key (A : U.affineOpens) (B : V.affineOpens) :
      IsCompact (pushout.inl f g '' A ∩ pushout.inr f g '' B) := by
    rw [image_pushout_inl_inter_image_pushout_inr]
    refine IsCompact.image (QuasiSeparatedSpace.inter_isCompact _ _ A.1.isOpen A.2.isCompact
      (f.isOpenEmbedding.isOpenMap _ (g ⁻¹ᵁ B.1).isOpen) ?_) (pushout.inl f g).continuous
    exact (g.isCompact_preimage B.2.isCompact).image f.continuous
  refine Scheme.quasiSeparatedSpace_of_isOpenCover (Sum.elim
    (fun A : U.affineOpens ↦ pushout.inl f g ''ᵁ A) (fun B : V.affineOpens ↦ pushout.inr f g ''ᵁ B))
    ?_ ?_ ?_
  · rw [TopologicalSpace.IsOpenCover, eq_top_iff,
      ← opensRange_pushout_inl_sup_opensRange_pushout_inr f g]
    rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · obtain ⟨A, hA, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨.inl ⟨A, hA⟩, y, hy, rfl⟩
    · obtain ⟨B, hB, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨.inr ⟨B, hB⟩, y, hy, rfl⟩
  · rintro (A | B)
    · exact A.2.image_of_isOpenImmersion _
    · exact B.2.image_of_isOpenImmersion _
  · rintro (A | B) (A' | B')
    · simp only [Sum.elim_inl, Scheme.Hom.coe_image]
      rw [← Set.image_inter (pushout.inl f g).isOpenEmbedding.injective]
      exact (QuasiSeparatedSpace.inter_isCompact _ _ A.1.isOpen A.2.isCompact A'.1.isOpen
        A'.2.isCompact).image (pushout.inl f g).continuous
    · exact key A B'
    · simp only [Sum.elim_inl, Sum.elim_inr, Scheme.Hom.coe_image]
      rw [Set.inter_comm]
      exact key A' B
    · simp only [Sum.elim_inr, Scheme.Hom.coe_image]
      rw [← Set.image_inter (pushout.inr f g).isOpenEmbedding.injective]
      exact (QuasiSeparatedSpace.inter_isCompact _ _ B.1.isOpen B.2.isCompact B'.1.isOpen
        B'.2.isCompact).image (pushout.inr f g).continuous

end Glue

/-- In a pullback square along the inclusion of opens `O ≤ V`, a point of `V` whose image lies in
the range of the right-hand map lies in `O`. -/
theorem mem_of_isPullback_homOfLE {O V : X.Opens} (h : O ≤ V) {W Y : Scheme.{u}} {ι : W ⟶ Y}
    {aW : O.toScheme ⟶ W} {aV : V.toScheme ⟶ Y} (H : IsPullback aW (X.homOfLE h) ι aV)
    {x : V.toScheme} (hx : aV x ∈ Set.range ι) : V.ι x ∈ O := by
  obtain ⟨w, hw⟩ := hx
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback w x hw
  have : X.homOfLE h (H.isoPullback.inv z) = x := by
    rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_snd, hz]
  rw [← this, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
  exact (Scheme.Opens.range_ι O).le ⟨_, rfl⟩

section Model

/-! ### Pullback squares over a target covered by two opens

Let `X ⟶ S` be covered by opens `U` and `V`, and let `P` be covered by the images of open
immersions `j₁ : Y₁ ⟶ P` and `j₂ : Y₂ ⟶ P` meeting in the image of `W`. A commutative square
`X ⟶ P ⟶ T`, `X ⟶ S ⟶ T` restricting to pullback squares over `Y₁`, `Y₂` and `W` (with
`U`, `V` and `U ⊓ V` as corners) is a pullback square. -/

variable {S T P Y₁ Y₂ W : Scheme.{u}} {f : X ⟶ S} {t : S ⟶ T} {q : P ⟶ T} {a : X ⟶ P}
  {U V : X.Opens} {j₁ : Y₁ ⟶ P} {j₂ : Y₂ ⟶ P} {ι₁ : W ⟶ Y₁} {ι₂ : W ⟶ Y₂}
  {a₁ : U.toScheme ⟶ Y₁} {a₂ : V.toScheme ⟶ Y₂}

/-- If `X` is covered by `U` and `V` mapping to `Y₁` and `Y₂`, and the points of `V` mapping into
the overlap `W` of `Y₁` and `Y₂` lie in an open `O ≤ U`, then `U` is the preimage of `Y₁`. -/
theorem preimage_opensRange_eq_of_isPullback [IsOpenImmersion j₁]
    (hP : IsPullback ι₁ ι₂ j₁ j₂) (hUV : U ⊔ V = ⊤) {O : X.Opens} (hOU : O ≤ U) (hOV : O ≤ V)
    {aO : O.toScheme ⟶ W} (ha₁ : U.ι ≫ a = a₁ ≫ j₁) (ha₂ : V.ι ≫ a = a₂ ≫ j₂)
    (H : IsPullback aO (X.homOfLE hOV) ι₂ a₂) : a ⁻¹ᵁ j₁.opensRange = U := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨y, hy⟩ := hx
    by_contra hxU
    have hxV : x ∈ V := by
      have : x ∈ U ⊔ V := hUV ▸ trivial
      exact this.resolve_left hxU
    obtain ⟨v, rfl⟩ : x ∈ Set.range V.ι := by rwa [Scheme.Opens.range_ι]
    have h : j₁ y = j₂ (a₂ v) := by
      rw [hy, ← Scheme.Hom.comp_apply, ha₂, Scheme.Hom.comp_apply]
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback y (a₂ v) h
    refine hxU (hOU (mem_of_isPullback_homOfLE hOV H ⟨hP.isoPullback.inv z, ?_⟩))
    rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_snd, hz]
  · obtain ⟨u, rfl⟩ : x ∈ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
    exact ⟨a₁ u, by rw [← Scheme.Hom.comp_apply, ← ha₁, Scheme.Hom.comp_apply]⟩

/-- Over an open `O` of `X` where the square restricts to a pullback square, two morphisms into `X`
agreeing after `a` and `f` agree on any open mapped into `O` by both. -/
private theorem comp_eq_of_isPullback {O : X.Opens} {Y : Scheme.{u}} {aO : O.toScheme ⟶ Y}
    {j : Y ⟶ P} [Mono j] (hj : O.ι ≫ a = aO ≫ j) (hO : IsPullback aO (O.ι ≫ f) (j ≫ q) t)
    {Z : Scheme.{u}} {m₁ m₂ : Z ⟶ X} (ha : m₁ ≫ a = m₂ ≫ a) (hf : m₁ ≫ f = m₂ ≫ f)
    (Z' : Z.Opens) (h₁ : Z' ≤ m₁ ⁻¹ᵁ O) (h₂ : Z' ≤ m₂ ⁻¹ᵁ O) : Z'.ι ≫ m₁ = Z'.ι ≫ m₂ := by
  have hr (m : Z ⟶ X) (h : Z' ≤ m ⁻¹ᵁ O) : Set.range (Z'.ι ≫ m) ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact h ((Scheme.Opens.range_ι Z').le ⟨z, rfl⟩)
  have : IsOpenImmersion.lift O.ι (Z'.ι ≫ m₁) (hr m₁ h₁) =
      IsOpenImmersion.lift O.ι (Z'.ι ≫ m₂) (hr m₂ h₂) := by
    refine hO.hom_ext ?_ ?_
    · rw [← cancel_mono j, Category.assoc, Category.assoc, ← hj,
        IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc, Category.assoc,
        Category.assoc, ha]
    · simp [hf]
  rw [← IsOpenImmersion.lift_fac O.ι (Z'.ι ≫ m₁) (hr m₁ h₁),
    ← IsOpenImmersion.lift_fac O.ι (Z'.ι ≫ m₂) (hr m₂ h₂), this]

/-- Over an open `O` of `X` where the square restricts to a pullback square, a pair of morphisms
to `P` and `S` agreeing in `T` lifts to `X` over the preimage of the image of `O`. -/
private theorem exists_comp_eq_of_isPullback {O : X.Opens} {Y : Scheme.{u}} {aO : O.toScheme ⟶ Y}
    {j : Y ⟶ P} [IsOpenImmersion j] (hj : O.ι ≫ a = aO ≫ j)
    (hO : IsPullback aO (O.ι ≫ f) (j ≫ q) t) {Z : Scheme.{u}} (y : Z ⟶ P) (z : Z ⟶ S)
    (hyz : y ≫ q = z ≫ t) :
    ∃ l : (y ⁻¹ᵁ j.opensRange).toScheme ⟶ X,
      l ≫ a = (y ⁻¹ᵁ j.opensRange).ι ≫ y ∧ l ≫ f = (y ⁻¹ᵁ j.opensRange).ι ≫ z := by
  have hr : Set.range ((y ⁻¹ᵁ j.opensRange).ι ≫ y) ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    exact (Scheme.Opens.range_ι (y ⁻¹ᵁ j.opensRange)).le ⟨x, rfl⟩
  have hy : IsOpenImmersion.lift j _ hr ≫ j ≫ q = ((y ⁻¹ᵁ j.opensRange).ι ≫ z) ≫ t := by
    rw [IsOpenImmersion.lift_fac_assoc, Category.assoc, hyz, Category.assoc]
  refine ⟨hO.lift _ _ hy ≫ O.ι, ?_, ?_⟩
  · rw [Category.assoc, hj, hO.lift_fst_assoc, IsOpenImmersion.lift_fac]
  · rw [Category.assoc, hO.lift_snd]

/-- **Pullback squares can be checked on two opens.** Let `X ⟶ S` be covered by opens `U` and
`V`, and let `P` be covered by the images of open immersions `j₁ : Y₁ ⟶ P` and `j₂ : Y₂ ⟶ P`
meeting in the image of `W`. If `U`, `V` and `U ⊓ V` are the base changes along `t : S ⟶ T` of
`Y₁`, `Y₂` and `W`, compatibly with `a : X ⟶ P`, then `X` is the base change of `P`. -/
theorem isPullback_of_isPullback_of_opensRange_sup_eq_top [IsOpenImmersion j₁]
    [IsOpenImmersion j₂] (hP : IsPullback ι₁ ι₂ j₁ j₂) (hP' : j₁.opensRange ⊔ j₂.opensRange = ⊤)
    (hUV : U ⊔ V = ⊤) {aW : (U ⊓ V : X.Opens).toScheme ⟶ W} (ha₁ : U.ι ≫ a = a₁ ≫ j₁)
    (ha₂ : V.ι ≫ a = a₂ ≫ j₂) (h₁ : IsPullback a₁ (U.ι ≫ f) (j₁ ≫ q) t)
    (h₂ : IsPullback a₂ (V.ι ≫ f) (j₂ ≫ q) t)
    (hW : IsPullback aW ((U ⊓ V).ι ≫ f) (ι₁ ≫ j₁ ≫ q) t)
    (hW₁ : aW ≫ ι₁ = X.homOfLE inf_le_left ≫ a₁) (hW₂ : aW ≫ ι₂ = X.homOfLE inf_le_right ≫ a₂) :
    IsPullback a f q t := by
  have hX := isPushout_opens_of_sup_eq_top hUV
  have hw : a ≫ q = f ≫ t := hX.hom_ext (by simp [reassoc_of% ha₁, h₁.w])
    (by simp [reassoc_of% ha₂, h₂.w])
  -- The overlap `U ⊓ V` is the base change of `W` inside `U` and inside `V`.
  have hW₁' : IsPullback aW (X.homOfLE inf_le_left) ι₁ a₁ :=
    IsPullback.of_bot (by rw [Scheme.homOfLE_ι_assoc]; exact hW) hW₁ h₁
  have hW₂' : IsPullback aW (X.homOfLE inf_le_right) ι₂ a₂ :=
    IsPullback.of_bot (by rw [Scheme.homOfLE_ι_assoc, ← hP.w_assoc]; exact hW) hW₂ h₂
  have hpre₁ := preimage_opensRange_eq_of_isPullback hP hUV inf_le_left inf_le_right ha₁ ha₂ hW₂'
  have hpre₂ := preimage_opensRange_eq_of_isPullback hP.flip (sup_comm U V ▸ hUV) inf_le_right
    inf_le_left ha₂ ha₁ hW₁'
  -- Uniqueness of lifts: compare on the preimages of `U` and `V`.
  have huniq {Z : Scheme.{u}} (m₁ m₂ : Z ⟶ X) (ha : m₁ ≫ a = m₂ ≫ a) (hf : m₁ ≫ f = m₂ ≫ f) :
      m₁ = m₂ := by
    have hpre (O : P.Opens) : m₁ ⁻¹ᵁ a ⁻¹ᵁ O = m₂ ⁻¹ᵁ a ⁻¹ᵁ O := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, ha]
    have hZ : m₁ ⁻¹ᵁ U ⊔ m₁ ⁻¹ᵁ V = ⊤ := by
      rw [← Scheme.Hom.preimage_sup, hUV, Scheme.Hom.preimage_top]
    refine (isPushout_opens_of_sup_eq_top hZ).hom_ext ?_ ?_
    · refine comp_eq_of_isPullback ha₁ h₁ ha hf _ le_rfl ?_
      rw [← hpre₁, hpre, hpre₁]
    · refine comp_eq_of_isPullback ha₂ h₂ ha hf _ le_rfl ?_
      rw [← hpre₂, hpre, hpre₂]
  -- Existence of lifts: lift over the preimages of `Y₁` and `Y₂` and glue.
  have hex {Z : Scheme.{u}} (y : Z ⟶ P) (z : Z ⟶ S) (hyz : y ≫ q = z ≫ t) :
      ∃ l : Z ⟶ X, l ≫ a = y ∧ l ≫ f = z := by
    obtain ⟨l₁, hl₁a, hl₁f⟩ := exists_comp_eq_of_isPullback ha₁ h₁ y z hyz
    obtain ⟨l₂, hl₂a, hl₂f⟩ := exists_comp_eq_of_isPullback ha₂ h₂ y z hyz
    have hZ : y ⁻¹ᵁ j₁.opensRange ⊔ y ⁻¹ᵁ j₂.opensRange = ⊤ := by
      rw [← Scheme.Hom.preimage_sup, hP', Scheme.Hom.preimage_top]
    have hZ' := isPushout_opens_of_sup_eq_top hZ
    refine ⟨hZ'.desc l₁ l₂ (huniq _ _ (by simp [hl₁a, hl₂a]) (by simp [hl₁f, hl₂f])),
      hZ'.hom_ext ?_ ?_, hZ'.hom_ext ?_ ?_⟩ <;> simp [hl₁a, hl₂a, hl₁f, hl₂f]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw (fun s ↦ (hex s.fst s.snd s.condition).choose)
    (fun s ↦ (hex s.fst s.snd s.condition).choose_spec.1)
    (fun s ↦ (hex s.fst s.snd s.condition).choose_spec.2) fun s m h₁ h₂ ↦ huniq _ _
      (h₁.trans (hex s.fst s.snd s.condition).choose_spec.1.symm)
      (h₂.trans (hex s.fst s.snd s.condition).choose_spec.2.symm)⟩⟩

variable {YU YV : Scheme.{u}} {ιU : W ⟶ YU} {ιV : W ⟶ YV} [IsOpenImmersion ιU]
  [IsOpenImmersion ιV] {qU : YU ⟶ T} {qV : YV ⟶ T} {aU : U.toScheme ⟶ YU} {aV : V.toScheme ⟶ YV}

/-- **Base change commutes with gluing.** Let `X ⟶ S` be covered by opens `U` and `V`, and let
`t : S ⟶ T`. Suppose that `U`, `V` and `U ⊓ V` are the base changes along `t` of schemes `YU`, `YV`
and `W` over `T`, compatibly with open immersions `W ⟶ YU` and `W ⟶ YV`. Then `X` is the base
change along `t` of the scheme glued from `YU` and `YV` along `W`. -/
theorem isPullback_pushout_desc_of_isPullback (hUV : U ⊔ V = ⊤) (hq : ιU ≫ qU = ιV ≫ qV)
    {aW : (U ⊓ V : X.Opens).toScheme ⟶ W} (hU : IsPullback aU (U.ι ≫ f) qU t)
    (hV : IsPullback aV (V.ι ≫ f) qV t) (hW : IsPullback aW ((U ⊓ V).ι ≫ f) (ιU ≫ qU) t)
    (hWU : aW ≫ ιU = X.homOfLE inf_le_left ≫ aU) (hWV : aW ≫ ιV = X.homOfLE inf_le_right ≫ aV) :
    IsPullback ((isPushout_opens_of_sup_eq_top hUV).desc (aU ≫ pushout.inl ιU ιV)
      (aV ≫ pushout.inr ιU ιV) (by rw [← reassoc_of% hWU, ← reassoc_of% hWV, pushout.condition]))
      f (pushout.desc qU qV hq) t :=
  isPullback_of_isPullback_of_opensRange_sup_eq_top (isPullback_pushout ιU ιV)
    (opensRange_pushout_inl_sup_opensRange_pushout_inr ιU ιV) hUV (IsPushout.inl_desc _ _ _ _)
    (IsPushout.inr_desc _ _ _ _) (by rwa [pushout.inl_desc]) (by rwa [pushout.inr_desc])
    (by rwa [pushout.inl_desc])
    hWU hWV

end Model

end TauCeti.AlgebraicGeometry.Scheme
