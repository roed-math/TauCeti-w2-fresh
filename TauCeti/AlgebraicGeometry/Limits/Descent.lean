/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Limits.OpenImmersion
public import TauCeti.AlgebraicGeometry.Gluing.Pushout
public import TauCeti.AlgebraicGeometry.Limits.AffineTransition
public import TauCeti.AlgebraicGeometry.Limits.AffineDescent

/-!
# Descent of schemes of finite presentation along cofiltered limits

Let `S = lim Sᵢ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps. Every scheme `X` of finite presentation over `S` descends to some member: there
are `i` and a scheme `Y` of finite presentation over `Sᵢ` with `X ≅ Y ×_{Sᵢ} S` over `S` (Stacks,
Lemma 32.10.1 (01ZM), essential surjectivity; full faithfulness is
`exists_pullbackMap_comp_eq_of_isLimit`).

The proof is by induction on the number of affine opens covering `X`. An affine open mapping into
the preimage of an affine open of a member descends by
`exists_isPullback_of_isLimit_of_isAffineOpen`.
For the inductive step, let `X = U ∪ V` with models `YU` and `YV` of `U` and `V` over `Sᵢ`.
1. The quasi-compact open `U ⊓ V` of `U = YU ×_{Sᵢ} S` is the preimage of a quasi-compact open
   `W` of some `YU ×_{Sᵢ} Sⱼ` (Stacks, Tag 01Z4), which is therefore a model of `U ⊓ V`.
2. The inclusion `U ⊓ V ⟶ V` descends to a morphism `W ×_{Sⱼ} Sₖ ⟶ YV ×_{Sᵢ} Sₖ` (01ZM, full
   faithfulness), which is an open immersion over some `Sₗ` (Stacks, Lemma 32.8.12 (0EUU)).
3. Over `Sₗ`, glue the models of `U` and `V` along the model of `U ⊓ V`; since base change commutes
   with gluing (`isPullback_pushout_desc_of_isPullback`), the glued scheme is a model of `X`.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.isPullback_lift_of_isPullback`: a model over `Sᵢ` base changes
  to a model over every later `Sⱼ`.
* `TauCeti.AlgebraicGeometry.Scheme.exists_isPullback_of_isLimit_of_le`: a quasi-compact open of a
  scheme with a model over `Sᵢ` has a model over some `Sⱼ`, an open of the base changed model.
* `TauCeti.AlgebraicGeometry.Scheme.exists_isPullback_of_isLimit_of_isAffineOpen_of_le`: affine
  opens mapping into the preimage of an affine open of a member have models.
* `TauCeti.AlgebraicGeometry.Scheme.exists_isPullback_of_isLimit_of_sup_eq_top`: the inductive
  step, gluing models of two opens covering `X`.
* `TauCeti.AlgebraicGeometry.Scheme.exists_isPullback_of_isLimit`: every scheme of finite
  presentation over `S` is the base change of a scheme of finite presentation over some member.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {c : Cone D} (hc : IsLimit c)

omit [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- A model `Y ⟶ Dᵢ` of a scheme `X ⟶ S` over a cone `S` base changes to a model
`Y ×_{Dᵢ} Dⱼ ⟶ Dⱼ` over every later member. -/
theorem isPullback_lift_of_isPullback {i j : I} (hji : j ⟶ i) {X Y : Scheme.{u}} {f : X ⟶ c.pt}
    {p : Y ⟶ D.obj i} {a : X ⟶ Y} (H : IsPullback a f p (c.π.app i)) :
    IsPullback (pullback.lift (f ≫ c.π.app j) a (by rw [Category.assoc, c.w, H.w])) f
      (pullback.fst (D.map hji) p) (c.π.app j) :=
  IsPullback.of_right (by rwa [pullback.lift_snd, c.w]) (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback (D.map hji) p).flip

include hc in
/-- Let `S = lim Sⱼ` be a cofiltered limit of schemes with affine transition maps, and let an open
`U` of `X ⟶ S` be the base change of `Y ⟶ Dᵢ`. A quasi-compact open `O ≤ U` is the base change of a
quasi-compact open `W` of some `Y ×_{Dᵢ} Dⱼ`, compatibly with the model of `U` (Stacks,
Tag 01Z4). -/
theorem exists_isPullback_of_isLimit_of_le {X : Scheme.{u}} (f : X ⟶ c.pt) {U O : X.Opens}
    (hOU : O ≤ U) (hO : IsCompact (O : Set X)) {i : I} {Y : Scheme.{u}} {p : Y ⟶ D.obj i}
    {a : U.toScheme ⟶ Y} (H : IsPullback a (U.ι ≫ f) p (c.π.app i)) :
    ∃ (j : I) (hji : j ⟶ i) (W : (pullback (D.map hji) p).Opens) (aO : O.toScheme ⟶ W),
      IsCompact (W : Set ↥(pullback (D.map hji) p)) ∧
        IsPullback aO (O.ι ≫ f) (W.ι ≫ pullback.fst (D.map hji) p) (c.π.app j) ∧
          aO ≫ W.ι = X.homOfLE hOU ≫ pullback.lift ((U.ι ≫ f) ≫ c.π.app j) a
            (by rw [Category.assoc, c.w, H.w]) := by
  -- The open `O` of `U = Y ×_{Dᵢ} S` is the preimage of an open `W` of some `Y ×_{Dᵢ} Dⱼ`.
  have hc' : IsCompact (U.ι ⁻¹ᵁ O : Set U.toScheme) := by
    rw [U.ι.isOpenEmbedding.isEmbedding.isCompact_iff]
    simpa [Set.image_preimage_eq_inter_range, Set.inter_eq_left.mpr hOU] using hO
  obtain ⟨j, hji, W, hW, hWO⟩ := exists_preimage_pullbackMap_eq_of_isLimit hc p _
    (H.flip.isoPullback.inv.isCompact_preimage hc')
  have hj := isPullback_lift_of_isPullback hji H
  set aj := pullback.lift (f := D.map hji) (g := p) ((U.ι ≫ f) ≫ c.π.app j) a
    (by rw [Category.assoc, c.w, H.w])
  have hpre : aj ⁻¹ᵁ W = U.ι ⁻¹ᵁ O := by
    have : aj = H.flip.isoPullback.hom ≫ pullback.map (c.π.app i) p (D.map hji) p (c.π.app j)
        (𝟙 _) (𝟙 _) (by simp) (by simp) := by
      apply pullback.hom_ext <;> simp [aj]
    rw [this, Scheme.Hom.comp_preimage, hWO, ← Scheme.Hom.comp_preimage, Iso.hom_inv_id]
    simp
  -- Hence `O ⟶ U ⟶ Y ×_{Dᵢ} Dⱼ` factors through `W`, and `O` is the base change of `W`.
  have hr : Set.range (X.homOfLE hOU ≫ aj) ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hx : U.ι (X.homOfLE hOU x) ∈ O := by
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      exact (Scheme.Opens.range_ι O).le ⟨x, rfl⟩
    have : X.homOfLE hOU x ∈ aj ⁻¹ᵁ W := hpre ▸ hx
    exact this
  have hpb : IsPullback (IsOpenImmersion.lift W.ι _ hr) (X.homOfLE hOU) W.ι aj :=
    IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ _).symm (by
      rw [Scheme.Opens.opensRange_ι, hpre, Scheme.opensRange_homOfLE])
  refine ⟨j, hji, W, IsOpenImmersion.lift W.ι _ hr, hW, ?_, IsOpenImmersion.lift_fac _ _ _⟩
  have := hpb.paste_vert hj
  rwa [Scheme.homOfLE_ι_assoc] at this

include hc in
/-- Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, and `X ⟶ S` covered by opens `U` and `V` with `U ⊓ V` quasi-compact. If `U` and
`V` are base changes of schemes of finite presentation over a member `Sᵢ`, then so is `X`, over a
later member. The inductive step of Stacks, Lemma 32.10.1 (01ZM). -/
theorem exists_isPullback_of_isLimit_of_sup_eq_top [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {X : Scheme.{u}} (f : X ⟶ c.pt) {U V : X.Opens}
    (hUV : U ⊔ V = ⊤) (hUV' : IsCompact ((U ⊓ V : X.Opens) : Set X)) {i : I}
    {YU YV : Scheme.{u}} {pU : YU ⟶ D.obj i} {pV : YV ⟶ D.obj i} [LocallyOfFinitePresentation pU]
    [QuasiCompact pU] [QuasiSeparated pU] [LocallyOfFinitePresentation pV] [QuasiCompact pV]
    [QuasiSeparated pV] {aU : U.toScheme ⟶ YU} {aV : V.toScheme ⟶ YV}
    (hU : IsPullback aU (U.ι ≫ f) pU (c.π.app i)) (hV : IsPullback aV (V.ι ≫ f) pV (c.π.app i)) :
    ∃ (l : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj l) (a : X ⟶ Y), LocallyOfFinitePresentation p ∧
      QuasiCompact p ∧ QuasiSeparated p ∧ IsPullback a f p (c.π.app l) := by
  -- Step 1: the overlap `U ⊓ V`, as an open of `U = YU ×_{Dᵢ} S`, is the base change of an
  -- open `Wⱼ` of some `YU ×_{Dᵢ} Dⱼ`.
  obtain ⟨j, hji, Wj, aW, hWj, hWj', hWU⟩ :=
    exists_isPullback_of_isLimit_of_le hc f inf_le_left hUV' hU
  have hUj := isPullback_lift_of_isPullback hji hU
  have hVj := isPullback_lift_of_isPullback hji hV
  -- Step 4: the inclusion `U ⊓ V ⟶ V` over `S` descends to a morphism `b` over some `Dₖ`.
  set pW := Wj.ι ≫ pullback.fst (D.map hji) pU
  set pVj := pullback.fst (D.map hji) pV
  have : CompactSpace Wj := isCompact_iff_compactSpace.mp hWj
  have : QuasiCompact pW := (quasiCompact_iff_compactSpace pW).mpr inferInstance
  set m : pullback (c.π.app j) pW ⟶ pullback (c.π.app j) pVj :=
    hWj'.flip.isoPullback.inv ≫ X.homOfLE inf_le_right ≫ hVj.flip.isoPullback.hom
  have hm : m ≫ pullback.fst _ _ = pullback.fst _ _ := by simp [m]
  obtain ⟨k, hkj, b, hb₁, hb₂⟩ := exists_pullbackMap_comp_eq_of_isLimit hc m hm
  -- Step 5: `b` is an open immersion over the limit, hence over some `Dₗ`.
  have : IsOpenImmersion (pullback.map (c.π.app k) (pullback.fst (D.map hkj) pW) (c.π.app k)
      (pullback.fst (D.map hkj) pVj) (𝟙 _) b (𝟙 _) (by simp) (by simp [hb₁])) :=
    (pullbackMap_iff_of_pullbackMap_comp_eq @IsOpenImmersion hkj hm hb₁ hb₂).mpr
      (by simp only [m]; infer_instance)
  obtain ⟨l, hlk, hl⟩ := exists_isOpenImmersion_pullbackMap_of_isLimit hc b hb₁
  -- Step 6: over `Dₗ`, glue the models of `U` and `V` along the model of `U ⊓ V`.
  set pUj := pullback.fst (D.map hji) pU
  have hUl := isPullback_lift_of_isPullback hlk (isPullback_lift_of_isPullback hkj hUj)
  have hVl := isPullback_lift_of_isPullback hlk (isPullback_lift_of_isPullback hkj hVj)
  have hWl := isPullback_lift_of_isPullback hlk (isPullback_lift_of_isPullback hkj hWj')
  set ιU := pullback.map (D.map hlk) (pullback.fst (D.map hkj) pW) (D.map hlk)
    (pullback.fst (D.map hkj) pUj) (𝟙 _) (pullback.map (D.map hkj) pW (D.map hkj) pUj (𝟙 _) Wj.ι
      (𝟙 _) (by simp) (by simp [pW, pUj])) (𝟙 _) (by simp) (by simp)
  set ιV := pullback.map (D.map hlk) (pullback.fst (D.map hkj) pW) (D.map hlk)
    (pullback.fst (D.map hkj) pVj) (𝟙 _) b (𝟙 _) (by simp) (by simp [hb₁])
  have hq : ιU ≫ pullback.fst (D.map hlk) (pullback.fst (D.map hkj) pUj) =
      ιV ≫ pullback.fst (D.map hlk) (pullback.fst (D.map hkj) pVj) := by
    simp [ιU, ιV]
  have hιU : ιU ≫ pullback.fst (D.map hlk) (pullback.fst (D.map hkj) pUj) =
      pullback.fst (D.map hlk) (pullback.fst (D.map hkj) pW) := by
    simp [ιU]
  refine ⟨l, _, _, _, ?_, ?_, ?_, isPullback_pushout_desc_of_isPullback hUV hq hUl hVl
    (by rwa [hιU]) ?_ ?_⟩
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
    exact (IsZariskiLocalAtSource.pushout_desc_iff (P := @LocallyOfFinitePresentation) ιU ιV _ _
      hq).mpr ⟨inferInstance, inferInstance⟩
  · exact (quasiCompact_iff_compactSpace _).mpr inferInstance
  · have := quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst (D.map hlk) (pullback.fst (D.map hkj) pUj))
    have := quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst (D.map hlk) (pullback.fst (D.map hkj) pVj))
    have : QuasiCompact ιU := (quasiCompact_iff_compactSpace ιU).mpr inferInstance
    have : QuasiCompact ιV := (quasiCompact_iff_compactSpace ιV).mpr inferInstance
    exact (quasiSeparated_iff_quasiSeparatedSpace _).mpr inferInstance
  · apply pullback.hom_ext
    · simp [ιU]
    · apply pullback.hom_ext
      · simp [ιU]
      · simp [ιU, hWU]
  · apply pullback.hom_ext
    · simp [ιV]
    · simp only [ιV, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      have e : pullback.lift (f := D.map hkj) (g := pW) ((U ⊓ V).ι ≫ f ≫ c.π.app k) aW
          (by simp [hWj'.w]) = hWj'.flip.isoPullback.hom ≫ pullback.map (c.π.app j) pW
            (D.map hkj) pW (c.π.app k) (𝟙 _) (𝟙 _) (by simp) (by simp) := by
        apply pullback.hom_ext <;> simp
      simp only [e, Category.assoc, hb₂]
      apply pullback.hom_ext <;> simp [m]

include hc in
/-- Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, and `X ⟶ S` locally of finite presentation. An affine open `O` of `X` mapping into
the preimage of an affine open `W` of a member `Sᵢ` is the base change of a scheme of finite
presentation over some `Sⱼ`. Stacks, Lemma 32.10.1 (01ZM), affine-local case. -/
theorem exists_isPullback_of_isLimit_of_isAffineOpen_of_le [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {X : Scheme.{u}} (f : X ⟶ c.pt)
    [LocallyOfFinitePresentation f] {O : X.Opens} (hO : IsAffineOpen O) {i : I}
    {W : (D.obj i).Opens} (hW : IsAffineOpen W) (hOW : O ≤ f ⁻¹ᵁ c.π.app i ⁻¹ᵁ W) :
    ∃ (j : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj j) (a : O.toScheme ⟶ Y),
      LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ QuasiSeparated p ∧
        IsPullback a (O.ι ≫ f) p (c.π.app j) := by
  have : IsAffine O := hO
  have := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFinitePresentation)
    (Q := @RingHom.FinitePresentation)
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
    (Q := @RingHom.FinitePresentation)
  have : LocallyOfFinitePresentation (f.resLE _ _ hOW) := IsZariskiLocalAtSource.resLE _ ‹_›
  obtain ⟨j, hji, Y, q, a, hY, hq, H⟩ :=
    exists_isPullback_of_isLimit_of_isAffineOpen hc hW (f.resLE _ _ hOW)
  have hres : IsPullback ((c.π.app j).resLE _ _ (by rw [← Scheme.Hom.comp_preimage, c.w]))
      (c.π.app i ⁻¹ᵁ W).ι (D.map hji ⁻¹ᵁ W).ι (c.π.app j) :=
    IsOpenImmersion.isPullback _ _ _ _ (Scheme.Hom.resLE_comp_ι _ _).symm (by
      rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, ← Scheme.Hom.comp_preimage, c.w])
  refine ⟨j, Y, q ≫ (D.map hji ⁻¹ᵁ W).ι, a, inferInstance,
    (quasiCompact_iff_compactSpace _).mpr inferInstance,
    (quasiSeparated_iff_quasiSeparatedSpace _).mpr inferInstance, ?_⟩
  have := H.paste_vert hres
  rwa [Scheme.Hom.resLE_comp_ι] at this

include hc in
/-- **Descent of schemes of finite presentation.** Let `S = lim Sⱼ` be a cofiltered limit of
quasi-compact quasi-separated schemes with affine transition maps. Every scheme `X` of finite
presentation over `S` is the base change `Y ×_{Sᵢ} S` of a scheme `Y` of finite presentation over
some member `Sᵢ`. Stacks, Lemma 32.10.1 (01ZM), essential surjectivity. -/
theorem exists_isPullback_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {X : Scheme.{u}} (f : X ⟶ c.pt)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj i) (a : X ⟶ Y), LocallyOfFinitePresentation p ∧
      QuasiCompact p ∧ QuasiSeparated p ∧ IsPullback a f p (c.π.app i) := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have := Scheme.compactSpace_of_isLimit D c hc
  have := quasiSeparatedSpace_of_isLimit hc i₀
  have := QuasiCompact.compactSpace_of_compactSpace f
  have := quasiSeparatedSpace_of_quasiSeparated f
  -- A model of `X ⟶ S` over an isomorphic scheme is a model of `X`.
  have transport {X' X'' Y Z : Scheme.{u}} {g : X' ⟶ c.pt} (e : X' ≅ X'') {g' : X'' ⟶ c.pt}
      (he : e.hom ≫ g' = g) {a : X'' ⟶ Y} {p : Y ⟶ Z} {π : c.pt ⟶ Z}
      (H : IsPullback a g' p π) : IsPullback (e.hom ≫ a) g p π := by
    simpa using
      (IsPullback.of_horiz_isIso (snd := g) (f := g') (g := 𝟙 _) ⟨by simp [he]⟩).paste_horiz H
  -- `good O`: the open `O` of `X` has a model over some member.
  let good (O : X.Opens) : Prop := ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj i)
    (a : O.toScheme ⟶ Y), LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ QuasiSeparated p ∧
      IsPullback a (O.ι ≫ f) p (c.π.app i)
  -- Models of two quasi-compact opens glue to a model of their union.
  have hsup (O₁ O₂ : X.Opens) (h₁ : IsCompact (O₁ : Set X)) (h₂ : IsCompact (O₂ : Set X))
      (g₁ : good O₁) (g₂ : good O₂) : good (O₁ ⊔ O₂) := by
    obtain ⟨i₁, Y₁, p₁, a₁, _, _, _, H₁⟩ := g₁
    obtain ⟨i₂, Y₂, p₂, a₂, _, _, _, H₂⟩ := g₂
    set O := O₁ ⊔ O₂
    have hrange (O' : X.Opens) (hO' : O' ≤ O) :
        Set.range ((O.ι ⁻¹ᵁ O').ι ≫ O.ι) = Set.range O'.ι := by
      simp [Set.range_comp, Set.image_preimage_eq_inter_range, hO']
    have hmodel (O' : X.Opens) (hO' : O' ≤ O) {i k : I} (hki : k ⟶ i) {Y : Scheme.{u}}
        {p : Y ⟶ D.obj i} {a : O'.toScheme ⟶ Y} (H : IsPullback a (O'.ι ≫ f) p (c.π.app i)) :
        IsPullback ((IsOpenImmersion.isoOfRangeEq _ _ (hrange O' hO')).hom ≫ _)
          ((O.ι ⁻¹ᵁ O').ι ≫ O.ι ≫ f) (pullback.fst (D.map hki) p) (c.π.app k) :=
      transport _ (by simp) (isPullback_lift_of_isPullback hki H)
    have hUV : O.ι ⁻¹ᵁ O₁ ⊔ O.ι ⁻¹ᵁ O₂ = ⊤ := by
      rw [← Scheme.Hom.preimage_sup, Scheme.Opens.ι_preimage_self]
    have hUV' : IsCompact ((O.ι ⁻¹ᵁ O₁ ⊓ O.ι ⁻¹ᵁ O₂ : O.toScheme.Opens) : Set O.toScheme) := by
      rw [O.ι.isOpenEmbedding.isEmbedding.isCompact_iff]
      convert QuasiSeparatedSpace.inter_isCompact _ _ O₁.isOpen h₁ O₂.isOpen h₂ using 1
      ext x
      simp only [TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_preimage, Set.mem_image,
        Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
        exact ⟨hy₁, hy₂⟩
      · rintro ⟨hx₁, hx₂⟩
        exact ⟨⟨x, Or.inl hx₁⟩, ⟨hx₁, hx₂⟩, rfl⟩
    exact exists_isPullback_of_isLimit_of_sup_eq_top hc (O.ι ≫ f) hUV hUV'
      (hmodel O₁ le_sup_left (IsCofiltered.minToLeft i₁ i₂) H₁)
      (hmodel O₂ le_sup_right (IsCofiltered.minToRight i₁ i₂) H₂)
  -- Affine opens mapping into the preimage of an affine open of a member have models.
  have hbase (x : X) : ∃ O : X.Opens, x ∈ O ∧ IsAffineOpen O ∧ good O := by
    obtain ⟨W, hW, hxW, -⟩ :=
      exists_isAffineOpen_mem_and_subset (x := c.π.app i₀ (f x)) (U := ⊤) trivial
    obtain ⟨O, hO, hxO, hOW⟩ :=
      exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ c.π.app i₀ ⁻¹ᵁ W) (x := x) hxW
    exact ⟨O, hxO, hO, exists_isPullback_of_isLimit_of_isAffineOpen_of_le hc f hO hW hOW⟩
  choose O hxO hO hgood using hbase
  have hfin (t : Finset X) : good (t.sup O) := by
    classical
    induction t using Finset.induction_on with
    | empty =>
      exact exists_isPullback_of_isLimit_of_isAffineOpen_of_le hc f (isAffineOpen_bot X)
        (isAffineOpen_bot (D.obj i₀)) bot_le
    | insert x t _ ih =>
      rw [Finset.sup_insert]
      refine hsup _ _ (hO x).isCompact ?_ (hgood x) ih
      rw [TopologicalSpace.Opens.coe_finset_sup, Finset.sup_eq_iSup]
      exact t.isCompact_biUnion fun y _ ↦ (hO y).isCompact
  -- Finitely many of them cover `X`.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (O x : Set X))
    (fun x ↦ (O x).isOpen) fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxO x⟩
  have htop : t.sup O = ⊤ := by
    refine top_le_iff.mp fun x _ ↦ ?_
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Finset.le_sup (f := O) hy hxy
  obtain ⟨i, Y, p, a, h₁, h₂, h₃, H⟩ := htop ▸ hfin t
  exact ⟨i, Y, p, X.topIso.inv ≫ a, h₁, h₂, h₃, transport X.topIso.symm (by simp) H⟩

end TauCeti.AlgebraicGeometry.Scheme
