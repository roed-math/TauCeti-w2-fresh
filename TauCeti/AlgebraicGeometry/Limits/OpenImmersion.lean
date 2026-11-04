/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Limits.FinitePresentation
public import TauCeti.CategoryTheory.MorphismProperty.Limits

/-!
# Open immersions are inherited from a finite stage

Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, and let `g : X ⟶ Y` be a morphism of schemes over a member `Sᵢ`, with `X` locally
of finite presentation and quasi-compact over `Sᵢ` and `Y` locally of finite type, quasi-compact
and quasi-separated over `Sᵢ`. If the base change `X ×_{Sᵢ} S ⟶ Y ×_{Sᵢ} S` of `g` is an open
immersion, then so is its base change to some `Sⱼ` (Stacks, Lemma 32.8.12 (0EUU)).

The proof descends the image. The image of the base change of `g` is a quasi-compact open of
`Y ×_{Sᵢ} S = lim (Y ×_{Sᵢ} Sⱼ)`, hence the preimage of a quasi-compact open `W` of some
`Y ×_{Sᵢ} Sⱼ` (Stacks, Tag 01Z4). The preimage of `W` in `X ×_{Sᵢ} Sⱼ` contains the image of the
limit, hence the image of some later `X ×_{Sᵢ} Sₖ`, so the base change of `g` to `Sₖ` factors
through the preimage `Wₖ` of `W`. The factorization `X ×_{Sᵢ} Sₖ ⟶ Wₖ` is a morphism of schemes
over `Sₖ` whose base change to `S` is an isomorphism, so it is an isomorphism over some later `Sₗ`
(Stacks, Lemma 32.8.11 (081E)), and the base change of `g` to `Sₗ` is this isomorphism followed
by the open immersion of the preimage of `Wₖ`.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.exists_preimage_pullbackMap_eq_of_isLimit`: a quasi-compact
  open of the base change `X ×_{Sᵢ} S` of a scheme `X` over `Sᵢ` is the preimage of a
  quasi-compact open of some `X ×_{Sᵢ} Sⱼ`.
* `TauCeti.AlgebraicGeometry.Scheme.exists_isOpenImmersion_pullbackMap_of_isLimit`: a morphism of
  schemes over `Sᵢ` whose base change to the limit is an open immersion is an open immersion over
  some `Sⱼ`.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {c : Cone D} (hc : IsLimit c)

include hc in
/-- Let `S = lim Dⱼ` be a cofiltered limit of schemes with affine transition maps, and `X` a
scheme over a member `Dᵢ`. Every quasi-compact open of `X ×_{Dᵢ} S` is the preimage of a
quasi-compact open of some `X ×_{Dᵢ} Dⱼ`. Stacks, Tag 01Z4 (1), applied to the limit
`X ×_{Dᵢ} S = lim (X ×_{Dᵢ} Dⱼ)`. -/
theorem exists_preimage_pullbackMap_eq_of_isLimit {i : I} {X : Scheme.{u}} (p : X ⟶ D.obj i)
    (U : (pullback (c.π.app i) p).Opens)
    (hU : IsCompact (U : Set ↥(pullback (c.π.app i) p))) :
    ∃ (j : I) (hji : j ⟶ i) (V : (pullback (D.map hji) p).Opens),
      IsCompact (V : Set ↥(pullback (D.map hji) p)) ∧
        pullback.map (c.π.app i) p (D.map hji) p (c.π.app j) (𝟙 X) (𝟙 _) (by simp) (by simp) ⁻¹ᵁ
          V = U := by
  obtain ⟨j, V, hV, hVU⟩ := exists_preimage_eq (D.pullbackOver p) _ (hc.pullbackOver p) U hU
  exact ⟨j.left, j.hom, V, hV, hVU⟩

include hc in
/-- Let `S = lim Dⱼ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, and `g : X ⟶ Y` a morphism of schemes over a member `Dᵢ`, with `X` locally of
finite presentation and quasi-compact over `Dᵢ`, and `Y` locally of finite type, quasi-compact and
quasi-separated over `Dᵢ`. If the base change of `g` to `S` is an open immersion, then so is its
base change to some `Dⱼ`. Stacks, Lemma 32.8.12 (0EUU). -/
theorem exists_isOpenImmersion_pullbackMap_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I} {X Y : Scheme.{u}} {p : X ⟶ D.obj i}
    {q : Y ⟶ D.obj i} [LocallyOfFinitePresentation p] [QuasiCompact p] [LocallyOfFiniteType q]
    [QuasiCompact q] [QuasiSeparated q] (g : X ⟶ Y) (hg : g ≫ q = p)
    [IsOpenImmersion
      (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg]))] :
    ∃ (j : I) (hji : j ⟶ i), IsOpenImmersion
      (pullback.map (D.map hji) p (D.map hji) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])) := by
  let φ := pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])
  -- The base changes `φB` of `g` to the members, and the projections from the limit.
  let φB {j : I} (hji : j ⟶ i) : pullback (D.map hji) p ⟶ pullback (D.map hji) q :=
    pullback.map (D.map hji) p (D.map hji) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])
  let πX {j : I} (hji : j ⟶ i) : pullback (c.π.app i) p ⟶ pullback (D.map hji) p :=
    pullback.map _ _ _ _ (c.π.app j) (𝟙 X) (𝟙 _) (by simp) (by simp)
  let πY {j : I} (hji : j ⟶ i) : pullback (c.π.app i) q ⟶ pullback (D.map hji) q :=
    pullback.map _ _ _ _ (c.π.app j) (𝟙 Y) (𝟙 _) (by simp) (by simp)
  have π_φB {j : I} (hji : j ⟶ i) : πX hji ≫ φB hji = φ ≫ πY hji := by
    apply pullback.hom_ext <;> simp [πX, πY, φB, φ]
  -- The image of `φ` is the preimage of a quasi-compact open `W` of some `Y ×_{Dᵢ} Dⱼ`.
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have : CompactSpace ↥(((Functor.const I).obj c.pt).obj i) := ‹CompactSpace c.pt›
  have : CompactSpace ↥(pullback (c.π.app i) p) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst (c.π.app i) p)
  obtain ⟨j, hji, W, hWc, hW⟩ := exists_preimage_pullbackMap_eq_of_isLimit hc q φ.opensRange
    (isCompact_range φ.continuous)
  -- The preimage of `W` in `X ×_{Dᵢ} Dⱼ` contains the image of the limit, so the preimage of `W`
  -- in some later `X ×_{Dᵢ} Dₖ` is everything.
  obtain ⟨k, fkj, hk⟩ := exists_map_eq_top (D.pullbackOver p) _ (hc.pullbackOver p)
    (i := Over.mk hji) (φB hji ⁻¹ᵁ W) (by
      change πX hji ⁻¹ᵁ φB hji ⁻¹ᵁ W = ⊤
      rw [← Scheme.Hom.comp_preimage, π_φB, Scheme.Hom.comp_preimage]
      rw [hW, Scheme.Hom.preimage_opensRange])
  let W' := (D.pullbackOver q).map fkj ⁻¹ᵁ W
  have map_φB : (D.pullbackOver p).map fkj ≫ φB hji = φB k.hom ≫ (D.pullbackOver q).map fkj := by
    apply pullback.hom_ext <;> simp [φB]
  have hφB : Set.range (φB k.hom) ⊆ Set.range W'.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change ((D.pullbackOver q).map fkj) (φB k.hom x) ∈ W
    rw [← Scheme.Hom.comp_apply, ← map_φB, Scheme.Hom.comp_apply]
    exact (hk.ge (Set.mem_univ x) :)
  -- The factorization `g'` of `φB k.hom` through `W'`, a morphism of schemes over `D k.left`.
  let g' : pullback (D.map k.hom) p ⟶ W' := IsOpenImmersion.lift W'.ι (φB k.hom) hφB
  have hg' : g' ≫ W'.ι ≫ pullback.fst _ _ = pullback.fst _ _ := by
    simp [g', φB]
  have : QuasiCompact W'.ι :=
    (quasiCompact_iff_compactSpace _).mpr
      (isCompact_iff_compactSpace.mp (((D.pullbackOver q).map fkj).isCompact_preimage hWc))
  -- The base change `ι'` of the open immersion `W' ⟶ Y ×_{Dᵢ} Dₖ` to the limit, and the base
  -- change `N = M ≫ ι'` of `φB k.hom`, an open immersion since it is a base change of `φ`.
  let ι' := pullback.map (c.π.app k.left) (W'.ι ≫ pullback.fst _ _) (c.π.app k.left)
    (pullback.fst (D.map k.hom) q) (𝟙 _) W'.ι (𝟙 _) (by simp) (by simp)
  let M := pullback.map (c.π.app k.left) (pullback.fst (D.map k.hom) p) (c.π.app k.left)
    (W'.ι ≫ pullback.fst _ _) (𝟙 _) g' (𝟙 _) (by simp) (by simp [hg'])
  let N := pullback.map (c.π.app k.left) (pullback.fst (D.map k.hom) p) (c.π.app k.left)
    (pullback.fst (D.map k.hom) q) (𝟙 _) (φB k.hom) (𝟙 _) (by simp) (by simp [φB])
  have hMN : M ≫ ι' = N := by
    apply pullback.hom_ext <;> simp [M, ι', N, g']
  have : IsOpenImmersion N :=
    (MorphismProperty.pullback_map_pullback_map_iff (P := @IsOpenImmersion) (c.π.app k.left)
      (D.map k.hom) (c.w k.hom) g hg).mpr ‹_›
  have : IsOpenImmersion M := by
    have : IsOpenImmersion (M ≫ ι') := hMN ▸ ‹IsOpenImmersion N›
    exact IsOpenImmersion.of_comp M ι'
  -- `M` is surjective: every point of the target maps into the image of `φ`.
  let eY : pullback (c.π.app k.left) (pullback.fst (D.map k.hom) q) ⟶ pullback (c.π.app i) q :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
      rw [Category.assoc, ← pullback.condition (f := D.map k.hom), ← pullback.condition_assoc,
        c.w])
  let rX : pullback (c.π.app i) p ⟶ pullback (c.π.app k.left) (pullback.fst (D.map k.hom) p) :=
    pullback.lift (pullback.fst _ _) (πX k.hom) (by simp [πX])
  let rY : pullback (c.π.app i) q ⟶ pullback (c.π.app k.left) (pullback.fst (D.map k.hom) q) :=
    pullback.lift (pullback.fst _ _) (πY k.hom) (by simp [πY])
  have h_eY : eY ≫ rY = 𝟙 _ := by
    apply pullback.hom_ext
    · simp [eY, rY]
    · apply pullback.hom_ext
      · simp [eY, rY, πY, pullback.condition]
      · simp [eY, rY, πY]
  have h_rX : rX ≫ N = φ ≫ rY := by
    apply pullback.hom_ext
    · simp [rX, N, rY, φ]
    · apply pullback.hom_ext <;> simp [rX, N, rY, φ, πX, πY, φB]
  have h_πY : eY ≫ πY hji = pullback.snd _ _ ≫ (D.pullbackOver q).map fkj := by
    apply pullback.hom_ext
    · simp only [eY, πY, Functor.const_obj_obj, Category.assoc, Over.mk_left, Over.mk_hom,
        limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, pullback.lift_fst_assoc]
      rw [← pullback.condition_assoc]
      exact congrArg (pullback.fst _ _ ≫ ·) (c.w fkj.left).symm
    · simp [eY, πY]
  have hM : Surjective M := by
    refine ⟨fun z ↦ ?_⟩
    have hz : eY (ι' z) ∈ φ.opensRange := by
      rw [← hW]
      change πY hji (eY (ι' z)) ∈ W
      rw [← Scheme.Hom.comp_apply, h_πY, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply ι']
      have : ι' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ W'.ι := by simp [ι']
      rw [this, Scheme.Hom.comp_apply]
      exact (pullback.snd (c.π.app k.left) (W'.ι ≫ pullback.fst _ _) z).2
    obtain ⟨x, hx⟩ := hz
    refine ⟨rX x, ι'.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hMN, ← Scheme.Hom.comp_apply, h_rX, Scheme.Hom.comp_apply, hx,
      ← Scheme.Hom.comp_apply, h_eY]
    rfl
  have : IsIso M := (isIso_iff_isOpenImmersion_and_surjective M).mpr ⟨‹_›, hM⟩
  -- By Stacks 081E, the factorization `g'` is an isomorphism over some `D l`, and the base
  -- change of `g` to `D l` is this isomorphism followed by an open immersion.
  obtain ⟨l, hlk, hl⟩ := exists_isIso_pullbackMap_of_isLimit hc g' hg'
  refine ⟨l, hlk ≫ k.hom, ?_⟩
  refine (MorphismProperty.pullback_map_pullback_map_iff (P := @IsOpenImmersion) (D.map hlk)
    (D.map k.hom) (D.map_comp hlk k.hom).symm g hg).mp ?_
  rw [show pullback.map (D.map hlk) (pullback.fst (D.map k.hom) p) (D.map hlk)
      (pullback.fst (D.map k.hom) q) (𝟙 _) (φB k.hom) (𝟙 _) (by simp) (by simp [φB]) =
      pullback.map (D.map hlk) (pullback.fst (D.map k.hom) p) (D.map hlk)
        (W'.ι ≫ pullback.fst _ _) (𝟙 _) g' (𝟙 _) (by simp) (by simp [hg']) ≫
      pullback.map (D.map hlk) (W'.ι ≫ pullback.fst _ _) (D.map hlk)
        (pullback.fst (D.map k.hom) q) (𝟙 _) W'.ι (𝟙 _) (by simp) (by simp) by
    apply pullback.hom_ext <;> simp [g']]
  infer_instance

end TauCeti.AlgebraicGeometry.Scheme
