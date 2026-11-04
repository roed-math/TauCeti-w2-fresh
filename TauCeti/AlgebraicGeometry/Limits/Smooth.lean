/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Limits.FinitePresentation
public import TauCeti.AlgebraicGeometry.Limits.ZariskiLocal
public import TauCeti.CategoryTheory.MorphismProperty.Limits
public import TauCeti.AlgebraicGeometry.Limits.NoetherianApproximation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Smooth.NoetherianDescent

/-!
# Smooth and étale morphisms are inherited from a finite stage

Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact schemes with affine transition maps, and
`Y` a scheme of finite presentation, quasi-compact and quasi-separated over a member `Sᵢ`. If the
base change `Y ×_{Sᵢ} S ⟶ S` is smooth, respectively étale, then so is `Y ×_{Sᵢ} Sⱼ ⟶ Sⱼ` for
some `j` (Stacks, Lemmas 32.8.9 (0C0C) and 32.8.10 (07RP)).

Both properties are local at the source and at the target, so it suffices to treat affine members
and affine `Y` (`exists_pullback_fst_of_isLimit_of_isZariskiLocalAtTarget` and
`exists_pullback_fst_of_isLimit_of_isZariskiLocalAtSource`).
There, Mathlib's Noetherian descent of smooth and étale algebras
(`Algebra.Smooth.exists_subalgebra_fg`, `Algebra.Etale.exists_subalgebra_fg`) writes
`Γ(Y ×_{Sᵢ} S) = Γ(S) ⊗[A₀] B₀` for a finitely generated subring `A₀ ⊆ Γ(S)` and a smooth
(étale) `A₀`-algebra `B₀`. Since `Spec A₀` is of finite presentation over `ℤ`, the morphism
`S ⟶ Spec A₀` factors through some `Sₖ` (Stacks, Proposition 32.6.1 (01ZC)), so
`Y ×_{Sᵢ} S ⟶ S` has two models over `Sₖ`: `Y ×_{Sᵢ} Sₖ` and the smooth (étale)
`Sₖ ×_{Spec A₀} Spec B₀`. Being isomorphic over the limit, they are isomorphic over some later
`Sⱼ` (Stacks, Lemmas 32.10.1 (01ZM) and 32.8.11 (081E)), and the property passes to
`Y ×_{Sᵢ} Sⱼ` (`TauCeti.AlgebraicGeometry.Scheme.exists_pullback_fst_of_isLimit_of_isPullback`,
for any property stable under base change).

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.exists_pullback_fst_of_isLimit_of_isPullback`: a property
  stable under base change passes to a finite stage as soon as the base change to the limit is a
  base change of a morphism with the property over a scheme of finite presentation over `ℤ`.
* `TauCeti.AlgebraicGeometry.Scheme.exists_smooth_pullback_fst_of_isLimit_of_isAffine`,
  `TauCeti.AlgebraicGeometry.Scheme.exists_etale_pullback_fst_of_isLimit_of_isAffine`: the case of
  affine members and affine `Y`.
* `TauCeti.AlgebraicGeometry.Scheme.exists_smooth_pullback_fst_of_isLimit`,
  `TauCeti.AlgebraicGeometry.Scheme.exists_etale_pullback_fst_of_isLimit`: smooth and étale
  morphisms are inherited from a finite stage.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace TauCeti.AlgebraicGeometry.Scheme

section General

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D} (hc : IsLimit c)

include hc in
/-- Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, `P` a property of morphisms stable under base change, and `Y` a scheme of finite
presentation, quasi-compact and quasi-separated over a member `Sᵢ`. Suppose that `Y ×_{Sᵢ} S ⟶ S`
is the base change, along some `S ⟶ T` with `T` locally of finite presentation over `ℤ`, of a
morphism `V ⟶ T` with `P`, locally of finite presentation, quasi-compact and quasi-separated.
Then `Y ×_{Sᵢ} Sⱼ ⟶ Sⱼ` has `P` for some `j`. -/
theorem exists_pullback_fst_of_isLimit_of_isPullback (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {i : I} {Y : Scheme.{u}} (q : Y ⟶ D.obj i)
    [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q] {T V : Scheme.{u}}
    [LocallyOfFinitePresentation (terminal.from T)] {t : c.pt ⟶ T} {σ : V ⟶ T}
    [LocallyOfFinitePresentation σ] [QuasiCompact σ] [QuasiSeparated σ] (hσ : P σ)
    {a : pullback (c.π.app i) q ⟶ V} (H : IsPullback a (pullback.fst _ _) σ t) :
    ∃ (j : I) (hji : j ⟶ i), P (pullback.fst (D.map hji) q) := by
  -- `S ⟶ T` factors through some `Sₖ`, and we may take `k` over `i`.
  obtain ⟨k₀, g₀, hg₀⟩ := exists_π_app_comp_eq_of_isLimit hc t
  let k := IsCofiltered.min i k₀
  let hki : k ⟶ i := IsCofiltered.minToLeft i k₀
  let g : D.obj k ⟶ T := D.map (IsCofiltered.minToRight i k₀) ≫ g₀
  have hg : c.π.app k ≫ g = t := by simp [g, hg₀]
  -- Over `Sₖ`, the two models `X = Y ×_{Sᵢ} Sₖ` and `W = Sₖ ×_T V` of `Y ×_{Sᵢ} S`.
  let p := pullback.fst (D.map hki) q
  let r := pullback.fst g σ
  have hX : IsPullback (pullback.map (c.π.app i) q (D.map hki) q (c.π.app k) (𝟙 Y) (𝟙 _)
      (by simp) (by simp)) (pullback.fst (c.π.app i) q) p (c.π.app k) := by
    refine IsPullback.of_right ?_ (by simp [p]) (IsPullback.of_hasPullback (D.map hki) q).flip
    convert (IsPullback.of_hasPullback (c.π.app i) q).flip using 1 <;> simp
  have hW : IsPullback (pullback.lift (pullback.fst _ _ ≫ c.π.app k) a (by simp [hg, H.w]))
      (pullback.fst (c.π.app i) q) r (c.π.app k) := by
    refine IsPullback.of_right ?_ (by simp [r]) (IsPullback.of_hasPullback g σ).flip
    convert H using 1; simp
  let e := hX.flip.isoPullback.symm ≪≫ hW.flip.isoPullback
  have he : e.hom ≫ pullback.fst _ _ = pullback.fst _ _ := by simp [e]
  -- The isomorphism `e` over `S` descends to a morphism `b` over some `Sⱼ`, which is an
  -- isomorphism over some later `Sₗ`.
  obtain ⟨j, hjk, b, hb₁, hb₂⟩ := exists_pullbackMap_comp_eq_of_isLimit hc e.hom he
  let ψ {Z : Scheme.{u}} (s : Z ⟶ D.obj k) :
      pullback (c.π.app j) (pullback.fst (D.map hjk) s) ≅ pullback (c.π.app k) s :=
    pullbackRightPullbackFstIso (D.map hjk) s (c.π.app j) ≪≫ pullback.congrHom (c.w hjk) rfl
  have : IsIso (pullback.map (c.π.app j) (pullback.fst (D.map hjk) p) (c.π.app j)
      (pullback.fst (D.map hjk) r) (𝟙 _) b (𝟙 _) (by simp) (by simp [hb₁])) := by
    have : pullback.map (c.π.app j) (pullback.fst (D.map hjk) p) (c.π.app j)
        (pullback.fst (D.map hjk) r) (𝟙 _) b (𝟙 _) (by simp) (by simp [hb₁]) =
        (ψ p).hom ≫ e.hom ≫ (ψ r).inv := by
      rw [← Category.assoc, Iso.eq_comp_inv]
      apply pullback.hom_ext
      · simp [ψ, he]
      · have h := congrArg (· ≫ pullback.snd (D.map hjk) r) hb₂
        simp only [Category.assoc, pullback.lift_snd, Category.comp_id] at h
        have key : (ψ p).hom ≫ pullback.map (c.π.app k) p (D.map hjk) p (c.π.app j) (𝟙 _) (𝟙 _)
            (by simp) (by simp) = pullback.snd _ _ := by
          apply pullback.hom_ext <;> simp [ψ, pullback.condition]
        rw [Category.assoc, Category.assoc, ← h, reassoc_of% key]
        simp [ψ]
    rw [this]
    infer_instance
  obtain ⟨l, hlj, hl⟩ := exists_isIso_pullbackMap_of_isLimit hc b hb₁
  refine ⟨l, (hlj ≫ hjk) ≫ hki, ?_⟩
  have h : P (pullback.fst (D.map hlj) (pullback.fst (D.map hjk) r)) :=
    P.pullback_fst _ _ (P.pullback_fst _ _ (P.pullback_fst _ _ hσ))
  rw [← P.cancel_left_of_respectsIso (pullback.map (D.map hlj)
    (pullback.fst (D.map hjk) p) (D.map hlj) (pullback.fst (D.map hjk) r) (𝟙 _) b (𝟙 _)
    _ _)] at h
  simp only [pullback.lift_fst, Category.comp_id] at h
  rw [← P.pullback_fst_pullback_fst_iff _ (D.map hki) _ (D.map_comp _ _).symm,
    ← P.pullback_fst_pullback_fst_iff _ (D.map hjk) _ (D.map_comp _ _).symm]
  exact h

end General

section Affine

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ i, IsAffine (D.obj i)] {c : Cone D} (hc : IsLimit c)

include hc in
/-- Let `S = lim Sⱼ` be a cofiltered limit of affine schemes, `P` a property of morphisms stable
under base change, and `Y` an affine scheme of finite presentation over a member `Sᵢ`. Suppose that
`Γ(Y ×_{Sᵢ} S) ≅ Γ(S) ⊗[A₀] B₀` as `Γ(S)`-algebras, for a finitely generated subring `A₀ ⊆ Γ(S)` and
a finitely presented `A₀`-algebra `B₀` such that `Spec B₀ ⟶ Spec A₀` has `P`. Then
`Y ×_{Sᵢ} Sⱼ ⟶ Sⱼ` has `P` for some `j`. -/
theorem exists_pullback_fst_of_isLimit_of_ringEquiv (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {i : I} {Y : Scheme.{u}} [IsAffine Y] (q : Y ⟶ D.obj i)
    [LocallyOfFinitePresentation q] (A₀ : Subalgebra ℤ Γ(c.pt, ⊤)) (hA₀ : A₀.FG) (B₀ : Type u)
    [CommRing B₀] [Algebra A₀ B₀] [Algebra.FinitePresentation A₀ B₀]
    (hB₀ : P (Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))))
    (e : Γ(pullback (c.π.app i) q, ⊤) ≃+* Γ(c.pt, ⊤) ⊗[A₀] B₀)
    (he : ∀ x : Γ(c.pt, ⊤), e ((pullback.fst (c.π.app i) q).appTop x) = x ⊗ₜ[A₀] (1 : B₀)) :
    ∃ (j : I) (hji : j ⟶ i), P (pullback.fst (D.map hji) q) := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : IsAffine (((Functor.const I).obj c.pt).obj i) := Scheme.isAffine_of_isLimit c hc
  have : Algebra.FinitePresentation ℤ A₀ :=
    Algebra.FinitePresentation.of_finiteType.mp ((Subalgebra.fg_iff_finiteType A₀).mp hA₀)
  have := locallyOfFinitePresentation_terminal_from_Spec (.of A₀)
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))) :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  let f := pullback.fst (c.π.app i) q
  let h : CommRingCat.of B₀ ⟶ Γ(pullback (c.π.app i) q, ⊤) :=
    CommRingCat.ofHom (e.symm.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
  have H : IsPushout (CommRingCat.ofHom (algebraMap A₀ Γ(c.pt, ⊤)))
      (CommRingCat.ofHom (algebraMap A₀ B₀)) f.appTop h := by
    refine (CommRingCat.isPushout_tensorProduct A₀ Γ(c.pt, ⊤) B₀).of_iso (Iso.refl _)
      (Iso.refl _) (Iso.refl _) e.symm.toCommRingCatIso rfl rfl ?_ rfl
    ext x
    simp [← he, f]
  refine exists_pullback_fst_of_isLimit_of_isPullback hc P q hB₀
    (t := c.pt.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A₀ Γ(c.pt, ⊤))))
    (a := (pullback (c.π.app i) q).isoSpec.hom ≫ Spec.map h) ?_
  refine (isPullback_SpecMap_of_isPushout _ _ _ _ H).flip.of_iso
    (pullback (c.π.app i) q).isoSpec.symm (Iso.refl _) c.pt.isoSpec.symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · exact Scheme.isoSpec_inv_naturality f
  · simp
  · simp

include hc in
/-- Let `S = lim Sⱼ` be a cofiltered limit of affine schemes and `Y` an affine scheme of finite
presentation over a member `Sᵢ`. If `Y ×_{Sᵢ} S ⟶ S` is smooth, then so is `Y ×_{Sᵢ} Sⱼ ⟶ Sⱼ` for
some `j`. -/
theorem exists_smooth_pullback_fst_of_isLimit_of_isAffine {i : I} {Y : Scheme.{u}} [IsAffine Y]
    (q : Y ⟶ D.obj i) [LocallyOfFinitePresentation q] [Smooth (pullback.fst (c.π.app i) q)] :
    ∃ (j : I) (hji : j ⟶ i), Smooth (pullback.fst (D.map hji) q) := by
  have : IsAffine (((Functor.const I).obj c.pt).obj i) := Scheme.isAffine_of_isLimit c hc
  let : Algebra Γ(c.pt, ⊤) Γ(pullback (c.π.app i) q, ⊤) :=
    (pullback.fst (c.π.app i) q).appTop.hom.toAlgebra
  have : Algebra.Smooth Γ(c.pt, ⊤) Γ(pullback (c.π.app i) q, ⊤) :=
    HasRingHomProperty.appTop @Smooth (pullback.fst (c.π.app i) q) ‹_›
  obtain ⟨A₀, B₀, _, _, hA₀, _, ⟨e⟩⟩ :=
    Algebra.Smooth.exists_subalgebra_fg ℤ Γ(c.pt, ⊤) Γ(pullback (c.π.app i) q, ⊤)
  refine exists_pullback_fst_of_isLimit_of_ringEquiv hc @Smooth q A₀ hA₀ B₀ ?_ e.toRingEquiv
    fun x ↦ ?_
  · exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr ‹_›)
  · exact (e.commutes x).trans (by simp [Algebra.TensorProduct.algebraMap_apply])

include hc in
/-- Let `S = lim Sⱼ` be a cofiltered limit of affine schemes and `Y` an affine scheme of finite
presentation over a member `Sᵢ`. If `Y ×_{Sᵢ} S ⟶ S` is étale, then so is `Y ×_{Sᵢ} Sⱼ ⟶ Sⱼ` for
some `j`. -/
theorem exists_etale_pullback_fst_of_isLimit_of_isAffine {i : I} {Y : Scheme.{u}} [IsAffine Y]
    (q : Y ⟶ D.obj i) [LocallyOfFinitePresentation q] [Etale (pullback.fst (c.π.app i) q)] :
    ∃ (j : I) (hji : j ⟶ i), Etale (pullback.fst (D.map hji) q) := by
  have : IsAffine (((Functor.const I).obj c.pt).obj i) := Scheme.isAffine_of_isLimit c hc
  let : Algebra Γ(c.pt, ⊤) Γ(pullback (c.π.app i) q, ⊤) :=
    (pullback.fst (c.π.app i) q).appTop.hom.toAlgebra
  have : Algebra.Etale Γ(c.pt, ⊤) Γ(pullback (c.π.app i) q, ⊤) :=
    HasRingHomProperty.appTop @Etale (pullback.fst (c.π.app i) q) ‹_›
  obtain ⟨A₀, B₀, _, _, hA₀, _, ⟨e⟩⟩ :=
    Algebra.Etale.exists_subalgebra_fg ℤ Γ(c.pt, ⊤) Γ(pullback (c.π.app i) q, ⊤)
  refine exists_pullback_fst_of_isLimit_of_ringEquiv hc @Etale q A₀ hA₀ B₀ ?_ e.toRingEquiv
    fun x ↦ ?_
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr ‹_›)
  · exact (e.commutes x).trans (by simp [Algebra.TensorProduct.algebraMap_apply])

/-- Let `S = lim Sⱼ` be a cofiltered limit of affine schemes and `P` a property of morphisms local
at the source and stable under base change, which is inherited from a finite stage by base changes
of affine schemes of finite presentation over a member. Then it is inherited by base changes of
quasi-compact schemes of finite presentation: cover them by finitely many affine opens. -/
theorem exists_pullback_fst_of_isLimit_of_isZariskiLocalAtSource (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P] [P.IsStableUnderBaseChange]
    (H : ∀ {i : I} {Y : Scheme.{u}} [IsAffine Y] (q : Y ⟶ D.obj i) [LocallyOfFinitePresentation q],
      P (pullback.fst (c.π.app i) q) → ∃ (j : I) (hji : j ⟶ i), P (pullback.fst (D.map hji) q))
    {i : I} {Y : Scheme.{u}} (q : Y ⟶ D.obj i) [LocallyOfFinitePresentation q] [QuasiCompact q]
    (hq : P (pullback.fst (c.π.app i) q)) :
    ∃ (j : I) (hji : j ⟶ i), P (pullback.fst (D.map hji) q) := by
  have := QuasiCompact.compactSpace_of_compactSpace q
  let 𝒰 := Y.affineCover.finiteSubcover
  -- Each of the finitely many affine opens of `Y` inherits `P` at some stage over `i`.
  have (k : 𝒰.I₀) : ∃ l : Over i, P (pullback.fst (D.map l.hom) (𝒰.f k ≫ q)) := by
    have : IsAffine (𝒰.X k) := by dsimp [𝒰]; infer_instance
    obtain ⟨j, hji, h⟩ := H (𝒰.f k ≫ q) <| by
      rw [← pullbackLeftPullbackSndIso_inv_fst, P.cancel_left_of_respectsIso]
      exact IsZariskiLocalAtSource.comp hq _
    exact ⟨Over.mk hji, h⟩
  choose l hl using this
  classical
  obtain ⟨m, hm⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image l)
  have hm' (k : 𝒰.I₀) : P (pullback.fst (D.map m.hom) (𝒰.f k ≫ q)) := by
    let f := (hm (Finset.mem_image_of_mem l (Finset.mem_univ k))).some
    exact P.pullback_fst_of_comp_eq _ _ (D.map f.left) (by rw [← D.map_comp, Over.w f]) (hl k)
  refine ⟨m.left, m.hom,
    IsZariskiLocalAtSource.of_openCover (𝒰.pullback₁ (pullback.snd (D.map m.hom) q)) fun k ↦ ?_⟩
  change P (pullback.fst _ _ ≫ pullback.fst _ _)
  rw [← pullbackLeftPullbackSndIso_hom_fst, P.cancel_left_of_respectsIso]
  exact hm' k

end Affine

section Global

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)] {c : Cone D}
  (hc : IsLimit c)

include hc in
/-- Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact schemes with affine transition maps,
and `Y` a scheme of finite presentation, quasi-compact and quasi-separated over a member `Sᵢ`. If
`Y ×_{Sᵢ} S ⟶ S` is smooth, then so is `Y ×_{Sᵢ} Sⱼ ⟶ Sⱼ` for some `j`. Stacks, Lemma 32.8.9
(0C0C). -/
theorem exists_smooth_pullback_fst_of_isLimit {i : I} {Y : Scheme.{u}} (q : Y ⟶ D.obj i)
    [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
    [Smooth (pullback.fst (c.π.app i) q)] :
    ∃ (j : I) (hji : j ⟶ i), Smooth (pullback.fst (D.map hji) q) := by
  have : IsZariskiLocalAtTarget @Smooth :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth) (Q := RingHom.Smooth)
  have : IsZariskiLocalAtSource @Smooth :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth) (Q := RingHom.Smooth)
  refine exists_pullback_fst_of_isLimit_of_isZariskiLocalAtTarget hc @Smooth
    @LocallyOfFinitePresentation ?_ q ‹_› ‹_›
  intro _ _ _ _ _ _ he _ _ q _ _ hq' hq
  have := hq'
  refine exists_pullback_fst_of_isLimit_of_isZariskiLocalAtSource @Smooth (fun q _ h ↦ ?_) q hq
  have := h
  exact exists_smooth_pullback_fst_of_isLimit_of_isAffine he q

include hc in
/-- Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact schemes with affine transition maps,
and `Y` a scheme of finite presentation, quasi-compact and quasi-separated over a member `Sᵢ`. If
`Y ×_{Sᵢ} S ⟶ S` is étale, then so is `Y ×_{Sᵢ} Sⱼ ⟶ Sⱼ` for some `j`. Stacks, Lemma 32.8.10
(07RP). -/
theorem exists_etale_pullback_fst_of_isLimit {i : I} {Y : Scheme.{u}} (q : Y ⟶ D.obj i)
    [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
    [Etale (pullback.fst (c.π.app i) q)] :
    ∃ (j : I) (hji : j ⟶ i), Etale (pullback.fst (D.map hji) q) := by
  have : IsZariskiLocalAtTarget @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale) (Q := RingHom.Etale)
  have : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  refine exists_pullback_fst_of_isLimit_of_isZariskiLocalAtTarget hc @Etale
    @LocallyOfFinitePresentation ?_ q ‹_› ‹_›
  intro _ _ _ _ _ _ he _ _ q _ _ hq' hq
  have := hq'
  refine exists_pullback_fst_of_isLimit_of_isZariskiLocalAtSource @Etale (fun q _ h ↦ ?_) q hq
  have := h
  exact exists_etale_pullback_fst_of_isLimit_of_isAffine he q

end Global

end TauCeti.AlgebraicGeometry.Scheme
