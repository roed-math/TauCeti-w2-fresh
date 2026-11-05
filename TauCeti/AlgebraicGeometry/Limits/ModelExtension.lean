/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Limits.AffineModels
public import TauCeti.AlgebraicGeometry.Limits.GlobalSections
public import TauCeti.AlgebraicGeometry.Limits.NoetherianApproximation
public import TauCeti.AlgebraicGeometry.Limits.Pushout

/-!
# Extending finite-presentation models across a quasi-compact open

Let `Y` be a quasi-compact quasi-separated scheme covered by an open `U` and an affine open `W`,
and suppose `U` is the limit of a cofiltered diagram of quasi-compact quasi-separated schemes of
finite presentation over `ℤ`, with affine transition maps. Then so is `Y`. This is the extension
step in the proof of absolute Noetherian approximation (Stacks, Proposition 32.5.4 (01ZA)).

The models of `Y` are the gluings `Uⱼ ∪_{Vⱼ} Spec C`, where `Vⱼ ⊆ Uⱼ` are models of `U ∩ W`
and `C` runs over the finitely generated subrings of `Γ(W) ×_{Γ(U ∩ W)} Γ(Vⱼ)` containing enough
elements to make `Vⱼ` an open of `Spec C`
(`TauCeti.AlgebraicGeometry.Scheme.exists_finset_isPullback_fgSubringPair`); their limit is `Y`
by `TauCeti.AlgebraicGeometry.Scheme.isLimitPushoutFunctorCone`.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.exists_finite_iSup_basicOpen_eq`: a quasi-compact open of an
  affine scheme is a finite union of basic opens.
* `TauCeti.AlgebraicGeometry.Scheme.isPullback_opensDiagramι`: the naturality squares of the
  inclusions of preimages of an open of a member of a diagram are pullbacks.
* `TauCeti.AlgebraicGeometry.Scheme.exists_isLimit_pushout_fgSubringPair`: the gluing, given
  models `Vⱼ` of `U ∩ W` covered by compatible affine basic opens.
* `TauCeti.AlgebraicGeometry.Scheme.exists_isLimit_finitePresentation_of_sup_eq_top`: the
  extension step.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {U W : Y.Opens} {J : Type u} [Category.{u} J] {Uf Vf : J ⥤ Scheme.{u}}
  (α : Vf ⟶ Uf) [∀ j, IsOpenImmersion (α.app j)] (πU : (Functor.const J).obj U.toScheme ⟶ Uf)
  (πV : (Functor.const J).obj (W.ι ⁻¹ᵁ U).toScheme ⟶ Vf) {ι : Type*} (g : ι → Γ(W.toScheme, ⊤))
  (b : ∀ j, ι → Γ(Vf.obj j, ⊤))
  (hgb : ∀ j k, ((πV.app j).appTop ≫ (W.ι ⁻¹ᵁ U).topIso.hom) (b j k) =
    W.toScheme.presheaf.map (homOfLE le_top).op (g k))

/-- For opens `U` and `W` of a quasi-separated scheme with `U` and `W` quasi-compact, the open
`U ∩ W` of `W` is quasi-compact. -/
lemma isCompact_ι_preimage {Y : Scheme.{u}} [QuasiSeparatedSpace Y] {U W : Y.Opens}
    (hU : IsCompact (U : Set Y)) (hW : IsCompact (W : Set Y)) :
    IsCompact ((W.ι ⁻¹ᵁ U : W.toScheme.Opens) : Set W.toScheme) := by
  have h := QuasiSeparatedSpace.inter_isCompact (U : Set Y) W U.isOpen hU W.isOpen hW
  have := W.ι.isOpenEmbedding.isInducing.isCompact_preimage' h
    (by rw [Scheme.Opens.range_ι]; exact Set.inter_subset_right)
  convert this using 1
  ext x
  exact ⟨fun h ↦ ⟨h, (Scheme.Opens.range_ι W).subset ⟨x, rfl⟩⟩, And.left⟩

/-- A quasi-compact open of an affine scheme is a finite union of basic opens. -/
lemma exists_finite_iSup_basicOpen_eq {X : Scheme.{u}} [IsAffine X] {V : X.Opens}
    (hV : IsCompact (V : Set X)) :
    ∃ (ι : Type u) (_ : Finite ι) (g : ι → Γ(X, ⊤)), (∀ k, X.basicOpen (g k) ≤ V) ∧
      ⨆ k, X.basicOpen (g k) = V := by
  choose f hf hfx using fun x : V ↦ (isAffineOpen_top X).exists_basicOpen_le x trivial
  obtain ⟨t, ht⟩ := hV.elim_finite_subcover (fun x ↦ (X.basicOpen (f x) : Set X))
    (fun _ ↦ (X.basicOpen _).isOpen) fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hfx ⟨x, hx⟩⟩
  refine ⟨t, inferInstance, fun k ↦ f k.1, fun k ↦ hf _, le_antisymm (iSup_le fun k ↦ hf _)
    fun x hx ↦ ?_⟩
  obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨k, hk⟩, hxk⟩

/-- The naturality squares of the inclusions of the preimages of an open of a member of a
diagram are pullbacks. -/
lemma isPullback_opensDiagramι {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) {i : I}
    (V : (D.obj i).Opens) {a b : Over i} (f : a ⟶ b) :
    IsPullback ((opensDiagramι D i V).app a) ((opensDiagram D i V).map f) (D.map f.left)
      ((opensDiagramι D i V).app b) := by
  refine (IsOpenImmersion.isPullback _ _ _ _ ((opensDiagramι D i V).naturality f).symm ?_).flip
  -- The members and maps of `Over.forget i ⋙ D` are those of `D`, by definition.
  change D.map f.left ⁻¹ᵁ (D.map b.hom ⁻¹ᵁ V).ι.opensRange = (D.map a.hom ⁻¹ᵁ V).ι.opensRange
  rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, ← Scheme.Hom.comp_preimage,
    ← D.map_comp, Over.w f]

include hgb in
/-- Let `Y` be a quasi-compact quasi-separated scheme covered by an open `U` and an affine open
`W`. Let `U` be the limit of a cofiltered diagram `Uf` of quasi-compact quasi-separated schemes of
finite presentation over `ℤ` with affine transition maps, and let `Vf ⟶ Uf` be open subschemes
(with pullback naturality squares) whose limit is `U ∩ W`, covered by affine basic opens
`D(b j k)` compatible with the transition maps, with `b j k` restricting to `g k|_{U ∩ W}` for
`g k : Γ(W)` with `D(g k) ⊆ U`. Then `Y` is the limit of a cofiltered diagram of quasi-compact
quasi-separated schemes of finite presentation over `ℤ` with affine transition maps. Part of the
proof of Stacks, Proposition 32.5.4 (01ZA). -/
theorem exists_isLimit_pushout_fgSubringPair [IsCofiltered J] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (hUW : U ⊔ W = ⊤) (hW : IsAffineOpen W)
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (Uf.map f)]
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (Vf.map f)] [∀ j, CompactSpace (Uf.obj j)]
    [∀ j, QuasiSeparatedSpace (Uf.obj j)]
    [∀ j, LocallyOfFinitePresentation (terminal.from (Uf.obj j))] [∀ j, CompactSpace (Vf.obj j)]
    (hα : ∀ {j k : J} (f : j ⟶ k), IsPullback (α.app j) (Vf.map f) (Uf.map f) (α.app k))
    (hπU : IsLimit (Cone.mk _ πU)) (hπV : IsLimit (Cone.mk _ πV))
    (hVU : ∀ j, IsPullback (πV.app j) (W.ι ∣_ U) (α.app j) (πU.app j)) [Finite ι]
    (hg : ∀ k, W.toScheme.basicOpen (g k) ≤ W.ι ⁻¹ᵁ U)
    (hb : ∀ j k, IsAffineOpen ((Vf.obj j).basicOpen (b j k)))
    (hY : ∀ j, ⨆ k, (Vf.obj j).basicOpen (b j k) = ⊤)
    (hbD : ∀ {j j' : J} (f : j' ⟶ j) k, (Vf.map f).appTop (b j k) = b j' k) :
    ∃ (Λ : Type u) (_ : SmallCategory Λ) (_ : IsCofiltered Λ) (E : Λ ⥤ Scheme.{u})
      (ρ : (Functor.const Λ).obj Y ⟶ E), Nonempty (IsLimit (Cone.mk Y ρ)) ∧
      (∀ ⦃a b : Λ⦄ (f : a ⟶ b), IsAffineHom (E.map f)) ∧
      ∀ a, CompactSpace (E.obj a) ∧ QuasiSeparatedSpace (E.obj a) ∧
        LocallyOfFinitePresentation (terminal.from (E.obj a)) := by
  have : IsAffine W.toScheme := hW
  have : CompactSpace U.toScheme := Scheme.compactSpace_of_isLimit Uf _ hπU
  have hV := isCompact_ι_preimage (isCompact_iff_compactSpace.mpr ‹_›) hW.isCompact
  have (j : J) : QuasiSeparatedSpace (Vf.obj j) := (α.app j).isOpenEmbedding.quasiSeparatedSpace
  have (j : J) : LocallyOfFiniteType (terminal.from (Vf.obj j)) := by
    rw [terminal.hom_ext (terminal.from _) (α.app j ≫ terminal.from _)]
    infer_instance
  obtain ⟨s, hs, hS⟩ := exists_finset_isPullback_fgSubringPair πV g b hgb hV hg hb hY
  choose hopen hpb hrange using hS
  let P := CommRingCat.FGSubringPair (fiberProductSystem πV) s
  let p : P ⥤ J := CommRingCat.FGSubringPair.proj
  let Sf : P ⥤ Scheme.{u} := (CommRingCat.FGSubringPair.ring _ s).rightOp ⋙ Scheme.Spec
  let β : p ⋙ Vf ⟶ Sf :=
    { app a := toSpecFGSubring πV a.sub
      naturality _ _ f := (toSpecFGSubring_naturality πV f).symm }
  have (a : P) : IsOpenImmersion (β.app a) := hopen a
  have (a : P) : IsOpenImmersion ((Functor.whiskerLeft p α).app a) :=
    inferInstanceAs (IsOpenImmersion (α.app a.idx))
  let y (a : P) (k : ι) : a.sub := ⟨fiberProductElem πV g b hgb a.idx k, a.subset (hs a.idx k)⟩
  have hβ {a a' : P} (f : a ⟶ a') :
      IsPullback (β.app a) ((p ⋙ Vf).map f) (Sf.map f) (β.app a') :=
    (IsOpenImmersion.isPullback _ _ _ _ (toSpecFGSubring_naturality πV f)
      (preimage_opensRange_fgSubringPair πV g b hgb hbD f (y a') (fun _ ↦ rfl) (y a)
        (fun _ ↦ rfl) (hrange a' (y a') fun _ ↦ rfl) (hrange a (y a) fun _ ↦ rfl))).flip
  -- The cones on the two halves and on the overlap.
  let cU := (Cone.mk _ πU).whisker p
  have hcU : IsLimit cU := (Functor.Initial.isLimitWhiskerEquiv p _).symm hπU
  let c₀ := Scheme.Spec.mapCone (coneRightOpOfCocone
    (CommRingCat.FGSubringPair.cocone (s := s) (fiberProductCocone πV)))
  let cW := c₀.extend W.toScheme.isoSpec.hom
  have hcW : IsLimit cW :=
    (isLimitSpecFiberProductCocone πV hπV s).ofIsoLimit (c₀.extendIso W.toScheme.isoSpec.symm)
  let e : (U ⊓ W).toScheme ≅ (W.ι ⁻¹ᵁ U).toScheme :=
    (isPullback_opens_inf U W).isoIsPullback _ _ (isPullback_morphismRestrict W.ι U)
  let cV := ((Cone.mk _ πV).whisker p).extend e.hom
  have hVU' (a : P) : IsPullback (e.hom ≫ πV.app a.idx) (Y.homOfLE inf_le_left)
      (α.app a.idx) (πU.app a.idx) := by
    simpa [e] using
      (IsPullback.of_horiz_isIso (fst := e.hom) (g := 𝟙 U.toScheme) ⟨by simp [e]⟩).paste_horiz
        (hVU a.idx)
  have hVW' (a : P) : IsPullback (e.hom ≫ πV.app a.idx) (Y.homOfLE inf_le_right)
      (toSpecFGSubring πV a.sub) (W.toScheme.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom a.sub.val.toRingHom ≫ (fiberProductCone πV a.idx).fst)) := by
    simpa [e] using
      (IsPullback.of_horiz_isIso (fst := e.hom) (g := 𝟙 W.toScheme) ⟨by simp [e]⟩).paste_horiz
        (hpb a)
  have : IsZariskiLocalAtTarget @IsAffineHom.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine
  have (a a' : P) (f : a ⟶ a') : IsAffineHom ((p ⋙ Uf).map f) :=
    inferInstanceAs (IsAffineHom (Uf.map f.1))
  have (a a' : P) (f : a ⟶ a') : IsAffineHom (Sf.map f) :=
    inferInstanceAs (IsAffineHom (Spec.map _))
  have (a : P) : CompactSpace ((p ⋙ Uf).obj a) := inferInstanceAs (CompactSpace (Uf.obj a.idx))
  have (a : P) : CompactSpace ((p ⋙ Vf).obj a) := inferInstanceAs (CompactSpace (Vf.obj a.idx))
  have (a : P) : QuasiSeparatedSpace ((p ⋙ Uf).obj a) :=
    inferInstanceAs (QuasiSeparatedSpace (Uf.obj a.idx))
  have (a : P) : IsAffine (Sf.obj a) := inferInstanceAs (IsAffine (Spec (.of a.sub)))
  let α' := Functor.whiskerLeft p α
  refine ⟨P, inferInstance, inferInstance, pushoutFunctor α' β,
    (pushoutFunctorCone α' β hUW (πU := cU.π) (πW := cW.π) (πV := cV.π) (fun a ↦ (hVU' a).w)
      fun a ↦ (hVW' a).w).π,
    ⟨isLimitPushoutFunctorCone α' β hUW (πU := cU.π) (πW := cW.π) (πV := cV.π)
      (fun f ↦ hα f.1) hβ hcU hcW hVU' hVW'⟩,
    fun a a' f ↦ pushoutFunctor_map_of_isZariskiLocalAtTarget _ β @IsAffineHom f (hα f.1) (hβ f)
      inferInstance inferInstance, fun a ↦ ⟨?_, ?_, ?_⟩⟩
  · exact inferInstanceAs (CompactSpace (pushout (α'.app a) (β.app a) : Scheme.{u}))
  · exact inferInstanceAs (QuasiSeparatedSpace (pushout (α'.app a) (β.app a) : Scheme.{u}))
  · have : Algebra.FinitePresentation ℤ a.sub :=
      Algebra.FinitePresentation.of_finiteType.mp ((Subalgebra.fg_iff_finiteType _).mp a.fg)
    have hS := locallyOfFinitePresentation_terminal_from_Spec (.of a.sub)
    -- The members of `pushoutFunctor` are the pushouts, by definition.
    change LocallyOfFinitePresentation (terminal.from (pushout (α'.app a) (β.app a) : Scheme.{u}))
    rw [terminal.hom_ext (terminal.from _) (pushout.desc (terminal.from _) (terminal.from _)
      (terminal.hom_ext _ _))]
    have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
    exact (IsZariskiLocalAtSource.pushout_desc_iff _ _ @LocallyOfFinitePresentation.{u} _ _ _).mpr
      ⟨inferInstanceAs (LocallyOfFinitePresentation (terminal.from (Uf.obj a.idx))), hS⟩

/-- **The extension step of absolute Noetherian approximation.** Let `Y` be a quasi-compact
quasi-separated scheme covered by an open `U` and an affine open `W`. If `U` is the limit of a
cofiltered diagram of quasi-compact quasi-separated schemes of finite presentation over `ℤ` with
affine transition maps, then so is `Y`. Stacks, Proposition 32.5.4 (01ZA), induction step. -/
theorem exists_isLimit_finitePresentation_of_sup_eq_top {Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] {U W : Y.Opens} (hUW : U ⊔ W = ⊤) (hW : IsAffineOpen W) {I : Type u}
    [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    (π : (Functor.const I).obj U.toScheme ⟶ D) (hπ : IsLimit (Cone.mk _ π))
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ i, LocallyOfFinitePresentation (terminal.from (D.obj i))] :
    ∃ (Λ : Type u) (_ : SmallCategory Λ) (_ : IsCofiltered Λ) (E : Λ ⥤ Scheme.{u})
      (ρ : (Functor.const Λ).obj Y ⟶ E), Nonempty (IsLimit (Cone.mk Y ρ)) ∧
      (∀ ⦃a b : Λ⦄ (f : a ⟶ b), IsAffineHom (E.map f)) ∧
      ∀ a, CompactSpace (E.obj a) ∧ QuasiSeparatedSpace (E.obj a) ∧
        LocallyOfFinitePresentation (terminal.from (E.obj a)) := by
  have : IsAffine W.toScheme := hW
  let c : Cone D := Cone.mk _ π
  have : CompactSpace U.toScheme := Scheme.compactSpace_of_isLimit D c hπ
  -- Descend `U ∩ W` to a quasi-compact open `V₀` of a member.
  obtain ⟨i₀, V₀, hV₀c, hV₀⟩ := exists_preimage_eq D c hπ (U.ι ⁻¹ᵁ W)
    (isCompact_ι_preimage hW.isCompact (isCompact_iff_compactSpace.mpr ‹_›))
  let F := opensDiagram D i₀ V₀
  have (j : Over i₀) : CompactSpace (F.obj j) := isCompact_iff_compactSpace.mp
    (QuasiCompact.isCompact_preimage (f := D.map j.hom) _ V₀.2 hV₀c)
  have (j : Over i₀) : QuasiSeparatedSpace ((Over.forget i₀ ⋙ D).obj j) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj j.left))
  have (j : Over i₀) : QuasiSeparatedSpace (F.obj j) :=
    ((opensDiagramι D i₀ V₀).app j).isOpenEmbedding.quasiSeparatedSpace
  -- `U ∩ W`, as an open of `W`, is the limit of the `F j`.
  let V := W.ι ⁻¹ᵁ U
  let e₁ : V.toScheme ≅ (c.π.app i₀ ⁻¹ᵁ V₀).toScheme :=
    (isPullback_morphismRestrict W.ι U).isoIsPullback _ _
      (isPullback_morphismRestrict U.ι W).flip ≪≫ U.toScheme.isoOfEq hV₀.symm
  have he₁ : e₁.hom ≫ (c.π.app i₀ ⁻¹ᵁ V₀).ι = W.ι ∣_ U := by
    rw [Iso.trans_hom, Category.assoc]
    -- `c.pt` is `U.toScheme` only after unfolding `Cone.mk`, hence `erw`.
    erw [Scheme.isoOfEq_hom_ι]
    exact IsPullback.isoIsPullback_hom_fst _ _ _ _
  let c₀ := (opensCone D c i₀ V₀).extend e₁.hom
  have hc₀ : IsLimit c₀ :=
    (isLimitOpensCone D c hπ i₀ V₀).ofIsoLimit ((opensCone D c i₀ V₀).extendIso e₁.symm)
  -- Cover `U ∩ W` by basic opens of `W`, and descend their restrictions to a member.
  obtain ⟨ι, _, g, hg, hgV⟩ := exists_finite_iSup_basicOpen_eq
    (isCompact_ι_preimage (isCompact_iff_compactSpace.mpr ‹_›) hW.isCompact)
  let r (k : ι) : Γ(V.toScheme, ⊤) :=
    V.topIso.inv (W.toScheme.presheaf.map (homOfLE le_top).op (g k))
  have hr (k : ι) : V.ι ''ᵁ V.toScheme.basicOpen (r k) = W.toScheme.basicOpen (g k) := by
    rw [Scheme.Opens.ι_image_basicOpen_topIso_inv, Scheme.basicOpen_res, inf_eq_right.mpr (hg k)]
  have hra (k : ι) : IsAffineOpen (V.toScheme.basicOpen (r k)) := by
    have := ((isAffineOpen_top W.toScheme).basicOpen (g k)).preimage_of_isOpenImmersion V.ι
      (by rw [Scheme.Opens.opensRange_ι]; exact hg k)
    rwa [← hr k, Scheme.Hom.preimage_image_eq] at this
  have hrc : ⨆ k, V.toScheme.basicOpen (r k) = ⊤ := by
    refine V.ι.image_injective ?_
    -- `image_injective` is stated for `fun x ↦ V.ι ''ᵁ x`; beta-reduce.
    change V.ι ''ᵁ _ = V.ι ''ᵁ ⊤
    rw [Scheme.Hom.image_iSup, Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
    simp only [hr, hgV]
    rfl
  obtain ⟨j₁, t, ht, hta, htc⟩ := exists_appTop_π_eq_and_iSup_basicOpen_eq_top F c₀ hc₀ r hra hrc
  -- The models of `U` and of `U ∩ W` over `j₁`.
  let α := Functor.whiskerLeft (Over.forget j₁) (opensDiagramι D i₀ V₀)
  have (k : Over j₁) : IsOpenImmersion (α.app k) :=
    inferInstanceAs (IsOpenImmersion ((opensDiagramι D i₀ V₀).app k.left))
  have (k k' : Over j₁) (f : k ⟶ k') :
      IsAffineHom ((Over.forget j₁ ⋙ Over.forget i₀ ⋙ D).map f) :=
    inferInstanceAs (IsAffineHom (D.map f.left.left))
  have (k k' : Over j₁) (f : k ⟶ k') : IsAffineHom ((Over.forget j₁ ⋙ F).map f) :=
    inferInstanceAs (IsAffineHom (F.map f.left))
  have (k : Over j₁) : CompactSpace ((Over.forget j₁ ⋙ Over.forget i₀ ⋙ D).obj k) :=
    inferInstanceAs (CompactSpace (D.obj k.left.left))
  have (k : Over j₁) : QuasiSeparatedSpace ((Over.forget j₁ ⋙ Over.forget i₀ ⋙ D).obj k) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj k.left.left))
  have (k : Over j₁) : LocallyOfFinitePresentation
      (terminal.from ((Over.forget j₁ ⋙ Over.forget i₀ ⋙ D).obj k)) :=
    inferInstanceAs (LocallyOfFinitePresentation (terminal.from (D.obj k.left.left)))
  have (k : Over j₁) : CompactSpace ((Over.forget j₁ ⋙ F).obj k) :=
    inferInstanceAs (CompactSpace (F.obj k.left))
  refine exists_isLimit_pushout_fgSubringPair α
    ((c.whisker (Over.forget i₀)).whisker (Over.forget j₁)).π (c₀.whisker (Over.forget j₁)).π g
    (fun k κ ↦ (F.map k.hom).appTop (t κ)) (fun k κ ↦ ?_) hUW hW
    (fun f ↦ isPullback_opensDiagramι D V₀ f.left)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget j₁) _).symm
      ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) c).symm hπ))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget j₁) c₀).symm hc₀) (fun k ↦ ?_) hg
    (fun k κ ↦ ?_) (fun k ↦ ?_) fun {k k'} f κ ↦ ?_
  -- The whiskered cones and diagrams over `Over j₁` unfold to those over `Over i₀` and `I`.
  · change V.topIso.hom ((c₀.π.app k.left).appTop ((F.map k.hom).appTop (t κ))) = _
    rw [← elementwise_of% Scheme.Hom.comp_appTop, c₀.w, ht, Iso.inv_hom_id_apply]
  · refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
    · change _ = (e₁.hom ≫ (c.π.app k.left.left).resLE _ _ _) ≫ (D.map k.left.hom ⁻¹ᵁ V₀).ι
      rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, he₁]
      rfl
    · change c.π.app k.left.left ⁻¹ᵁ (D.map k.left.hom ⁻¹ᵁ V₀).ι.opensRange = _
      rw [Scheme.Opens.opensRange_ι, ← Scheme.Hom.comp_preimage, c.w, hV₀,
        (isPullback_morphismRestrict W.ι U).flip.opensRange_snd, Scheme.Opens.opensRange_ι]
  · rw [← Scheme.preimage_basicOpen_top]
    exact (hta κ).preimage _
  · change ⨆ κ, (F.obj k.left).basicOpen ((F.map k.hom).appTop (t κ)) = ⊤
    simp_rw [← Scheme.preimage_basicOpen_top, ← Scheme.Hom.preimage_iSup, htc,
      Scheme.Hom.preimage_top]
  · change (F.map f.left).appTop ((F.map k.hom).appTop (t κ)) = (F.map k'.hom).appTop (t κ)
    rw [← elementwise_of% Scheme.Hom.comp_appTop, ← F.map_comp, Over.w f]

end TauCeti.AlgebraicGeometry.Scheme
