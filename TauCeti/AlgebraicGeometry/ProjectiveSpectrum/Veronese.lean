/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Veronese

/-!
# `Proj` of a Veronese subalgebra

Let `A = ⨁ₙ 𝒜 n` be an `ℕ`-graded commutative `R`-algebra, `d ≠ 0`, and `A^{(d)} = ⨁ₖ 𝒜 (d k)`
its Veronese subalgebra. Then `Proj A^{(d)} ≅ Proj A`, over `Spec 𝒜 0`.

A point of `Proj A` misses some homogeneous `f` of positive degree, hence misses `f^d ∈ A^{(d)}`,
so the basic opens `D₊(g)` for homogeneous `g ∈ A^{(d)}` of positive degree cover `Proj A`. They
also cover `Proj A^{(d)}`, and on them `A^{(d)}_{(g)} ≅ A_{(g)}` by
`TauCeti.GradedAlgebra.awayVeroneseEquiv`. These chart isomorphisms agree on overlaps, so they
glue to mutually inverse morphisms.

## Main definitions

* `AlgebraicGeometry.Proj.veroneseChart`, `AlgebraicGeometry.Proj.veroneseChartInv`: for
  homogeneous `g ∈ A^{(d)}` of positive degree, the charts `Spec A_{(g)} ⟶ Proj A^{(d)}` and
  `Spec A^{(d)}_{(g)} ⟶ Proj A`.
* `AlgebraicGeometry.Proj.veroneseAffineOpenCover`: the cover of `Proj A` by the `Spec A_{(g)}`.
* `AlgebraicGeometry.Proj.veroneseIso`: the isomorphism `Proj A^{(d)} ≅ Proj A`.

## Main results

* `AlgebraicGeometry.Proj.iSup_basicOpen_veronese_eq_top`: the `D₊(g)` for homogeneous
  `g ∈ A^{(d)}` of positive degree cover `Proj A`.
* `AlgebraicGeometry.Proj.awayι_fromVeronese`, `AlgebraicGeometry.Proj.awayι_toVeronese`:
  on the charts, `veroneseIso` is `Spec` of `awayVeroneseEquiv`.
* `AlgebraicGeometry.Proj.toVeronese_preimage_basicOpen`: the inverse of `veroneseIso` pulls the
  basic open `D₊(a)` of `Proj A^{(d)}` back to the basic open `D₊(a)` of `Proj A`.
* `AlgebraicGeometry.Proj.veroneseIso_hom_toSpecZero`,
  `AlgebraicGeometry.Proj.veroneseIso_hom_toSpecCoeff`: `veroneseIso` lies over `Spec 𝒜 0`, hence
  over `Spec R`.
* `AlgebraicGeometry.Proj.map_veroneseMap_veroneseIso_hom`: `veroneseIso` is natural in graded
  ring maps.

## References

* [The Stacks Project, Lemma 27.11.8 (0B5J)](https://stacks.math.columbia.edu/tag/0B5J)
-/

@[expose] public section

open CategoryTheory HomogeneousLocalization TauCeti.GradedAlgebra

namespace AlgebraicGeometry.Proj

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : ℕ) [NeZero d]

omit [NeZero d] in
/-- The basic opens `D₊(g)` of `Proj A`, for `g` homogeneous of positive degree in the Veronese
subalgebra `A^{(d)}`, cover `Proj A`: a point missing `f ∈ 𝒜 n` misses `f ^ d ∈ 𝒜 (d n)`. -/
theorem iSup_basicOpen_veronese_eq_top :
    ⨆ g : Σ k : ℕ+, veroneseGrading 𝒜 d k, basicOpen 𝒜 ((g.2 : veronese 𝒜 d) : A) = ⊤ := by
  refine top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
  obtain ⟨n, hn, f, hf, hfx⟩ : ∃ n > 0, ∃ f ∈ 𝒜 n, f ∉ x.asHomogeneousIdeal := by
    by_contra! h
    exact x.not_irrelevant_le ((HomogeneousIdeal.irrelevant_le _).2 fun n hn f hf ↦ h n hn f hf)
  have hfd : f ^ d ∈ 𝒜 (d * n) := by
    simpa only [smul_eq_mul] using SetLike.pow_mem_graded d hf
  refine ⟨⟨⟨n, hn⟩, ⟨⟨f ^ d, mem_veronese_of_mem hfd⟩, mem_veroneseGrading.2 hfd⟩⟩, ?_⟩
  exact (mem_basicOpen 𝒜 _ x).2 fun h ↦ hfx (x.isPrime.mem_of_pow_mem d h)

variable {𝒜 d} {g : veronese 𝒜 d} {k : ℕ}

/-- For `g` homogeneous of positive degree `k` in the Veronese subalgebra `A^{(d)}`, the chart
`Spec A_{(g)} ≅ Spec A^{(d)}_{(g)} ⟶ Proj A^{(d)}`. -/
noncomputable def veroneseChart (hg : g ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) :
    Spec (.of (Away 𝒜 (g : A))) ⟶ Proj (veroneseGrading 𝒜 d) :=
  Spec.map (CommRingCat.ofHom (awayVeroneseEquiv hg : _ →+* _)) ≫
    awayι (veroneseGrading 𝒜 d) g hg hk

/-- The charts `AlgebraicGeometry.Proj.veroneseChart` agree on overlaps: on `D₊(g h) ⊆ D₊(g)` the
chart of `g` restricts to the chart of `g h`. -/
@[reassoc]
theorem SpecMap_awayMap_veroneseChart {h x : veronese 𝒜 d} {k' : ℕ}
    (hg : g ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) (hh : h ∈ veroneseGrading 𝒜 d k')
    (hgh : x = g * h) :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 (f := (g : A)) (mem_veroneseGrading.1 hh)
        (congrArg Subtype.val hgh))) ≫ veroneseChart hg hk =
      veroneseChart (hgh ▸ SetLike.mul_mem_graded hg hh) (hk.trans_le (k.le_add_right k')) := by
  have hx : x ∈ veroneseGrading 𝒜 d (k + k') := hgh ▸ SetLike.mul_mem_graded hg hh
  have e : (awayMap 𝒜 (f := (g : A)) (mem_veroneseGrading.1 hh) (congrArg Subtype.val hgh)).comp
      (awayVeroneseEquiv hg : _ →+* _) =
      (awayVeroneseEquiv hx : _ →+* _).comp (awayMap (veroneseGrading 𝒜 d) hh hgh) :=
    RingHom.ext fun a ↦ (awayVeroneseEquiv_awayMap hg hh hx hgh a).symm
  rw [veroneseChart, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, e,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, SpecMap_awayMap_awayι, veroneseChart]

/-- The chart `AlgebraicGeometry.Proj.veroneseChart` does not depend on the degree chosen for
`g`. -/
theorem veroneseChart_congr {k' : ℕ} (hg : g ∈ veroneseGrading 𝒜 d k) (hk : 0 < k)
    (hg' : g ∈ veroneseGrading 𝒜 d k') (hk' : 0 < k') :
    veroneseChart hg hk = veroneseChart hg' hk' := by
  rw [veroneseChart, veroneseChart, awayι_congr hg hk hg' hk']
  rfl

/-- For `g` homogeneous of positive degree `k` in the Veronese subalgebra `A^{(d)}`, the chart
`Spec A^{(d)}_{(g)} ≅ Spec A_{(g)} ⟶ Proj A`. -/
noncomputable def veroneseChartInv (hg : g ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) :
    Spec (.of (Away (veroneseGrading 𝒜 d) g)) ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom ((awayVeroneseEquiv hg).symm : _ →+* _)) ≫
    awayι 𝒜 (g : A) (mem_veroneseGrading.1 hg) (Nat.mul_pos (NeZero.pos d) hk)

/-- The chart `AlgebraicGeometry.Proj.veroneseChartInv` does not depend on the degree chosen for
`g`. -/
theorem veroneseChartInv_congr {k' : ℕ} (hg : g ∈ veroneseGrading 𝒜 d k) (hk : 0 < k)
    (hg' : g ∈ veroneseGrading 𝒜 d k') (hk' : 0 < k') :
    veroneseChartInv hg hk = veroneseChartInv hg' hk' := by
  rw [veroneseChartInv, veroneseChartInv, awayι_congr (mem_veroneseGrading.1 hg)
    (Nat.mul_pos (NeZero.pos d) hk) (mem_veroneseGrading.1 hg') (Nat.mul_pos (NeZero.pos d) hk')]
  rfl

/-- The charts `AlgebraicGeometry.Proj.veroneseChartInv` agree on overlaps. -/
@[reassoc]
theorem SpecMap_awayMap_veroneseChartInv {h x : veronese 𝒜 d} {k' : ℕ}
    (hg : g ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) (hh : h ∈ veroneseGrading 𝒜 d k')
    (hgh : x = g * h) :
    Spec.map (CommRingCat.ofHom (awayMap (veroneseGrading 𝒜 d) hh hgh)) ≫
        veroneseChartInv hg hk =
      veroneseChartInv (hgh ▸ SetLike.mul_mem_graded hg hh) (hk.trans_le (k.le_add_right k')) := by
  have hx : x ∈ veroneseGrading 𝒜 d (k + k') := hgh ▸ SetLike.mul_mem_graded hg hh
  have e : (awayMap (veroneseGrading 𝒜 d) hh hgh).comp ((awayVeroneseEquiv hg).symm : _ →+* _) =
      ((awayVeroneseEquiv hx).symm : _ →+* _).comp
        (awayMap 𝒜 (f := (g : A)) (mem_veroneseGrading.1 hh) (congrArg Subtype.val hgh)) :=
    RingHom.ext fun a ↦ (awayVeroneseEquiv hx).injective <| by
      obtain ⟨a, rfl⟩ := (awayVeroneseEquiv hg).surjective a
      simp [awayVeroneseEquiv_awayMap hg hh hx hgh]
  rw [veroneseChartInv, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, e,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, SpecMap_awayMap_awayι,
    veroneseChartInv, awayι_congr]

/-- The charts `AlgebraicGeometry.Proj.veroneseChart` agree on the overlap `D₊(g) ∩ D₊(h)`. -/
theorem pullback_fst_veroneseChart {h : veronese 𝒜 d} {k' : ℕ} (hg : g ∈ veroneseGrading 𝒜 d k)
    (hk : 0 < k) (hh : h ∈ veroneseGrading 𝒜 d k') (hk' : 0 < k') :
    Limits.pullback.fst
        (awayι 𝒜 (g : A) (mem_veroneseGrading.1 hg) (Nat.mul_pos (NeZero.pos d) hk))
        (awayι 𝒜 (h : A) (mem_veroneseGrading.1 hh) (Nat.mul_pos (NeZero.pos d) hk')) ≫
        veroneseChart hg hk =
      Limits.pullback.snd _ _ ≫ veroneseChart hh hk' := by
  rw [← cancel_epi (pullbackAwayιIso 𝒜 _ _ _ _ (x := ((g * h : veronese 𝒜 d) : A)) rfl).inv,
    pullbackAwayιIso_inv_fst_assoc, pullbackAwayιIso_inv_snd_assoc,
    SpecMap_awayMap_veroneseChart hg hk hh rfl,
    SpecMap_awayMap_veroneseChart hh hk' hg (mul_comm _ _), veroneseChart_congr]

/-- The charts `AlgebraicGeometry.Proj.veroneseChartInv` agree on the overlap
`D₊(g) ∩ D₊(h)`. -/
theorem pullback_fst_veroneseChartInv {h : veronese 𝒜 d} {k' : ℕ}
    (hg : g ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) (hh : h ∈ veroneseGrading 𝒜 d k')
    (hk' : 0 < k') :
    Limits.pullback.fst (awayι (veroneseGrading 𝒜 d) g hg hk)
        (awayι (veroneseGrading 𝒜 d) h hh hk') ≫ veroneseChartInv hg hk =
      Limits.pullback.snd _ _ ≫ veroneseChartInv hh hk' := by
  rw [← cancel_epi (pullbackAwayιIso _ hg hk hh hk' (x := g * h) rfl).inv,
    pullbackAwayιIso_inv_fst_assoc, pullbackAwayιIso_inv_snd_assoc,
    SpecMap_awayMap_veroneseChartInv hg hk hh rfl,
    SpecMap_awayMap_veroneseChartInv hh hk' hg (mul_comm _ _), veroneseChartInv_congr]

variable (𝒜 d)

/-- `Proj A` is covered by the charts `Spec A_{(g)}` for `g` homogeneous of positive degree in
the Veronese subalgebra `A^{(d)}`. -/
noncomputable def veroneseAffineOpenCover : (Proj 𝒜).AffineOpenCover where
  I₀ := Σ k : ℕ+, veroneseGrading 𝒜 d k
  X g := .of (Away 𝒜 ((g.2 : veronese 𝒜 d) : A))
  f g := awayι 𝒜 _ (mem_veroneseGrading.1 g.2.2) (Nat.mul_pos (NeZero.pos d) g.1.pos)
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_basicOpen_veronese_eq_top 𝒜 d).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (awayι 𝒜 _ _ _).opensRange
    rw [opensRange_awayι]
    exact (TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_basicOpen_veronese_eq_top 𝒜 d).ge (Set.mem_univ x))).choose_spec

/-- The morphism `Proj A ⟶ Proj A^{(d)}`, glued from the charts
`AlgebraicGeometry.Proj.veroneseChart`. -/
noncomputable def toVeronese : Proj 𝒜 ⟶ Proj (veroneseGrading 𝒜 d) :=
  (veroneseAffineOpenCover 𝒜 d).openCover.glueMorphisms
    (fun g : Σ k : ℕ+, veroneseGrading 𝒜 d k ↦ veroneseChart g.2.2 g.1.pos)
    fun (g h : Σ k : ℕ+, veroneseGrading 𝒜 d k) ↦
      pullback_fst_veroneseChart g.2.2 g.1.pos h.2.2 h.1.pos

/-- The morphism `Proj A^{(d)} ⟶ Proj A`, glued from the charts
`AlgebraicGeometry.Proj.veroneseChartInv`. -/
noncomputable def fromVeronese : Proj (veroneseGrading 𝒜 d) ⟶ Proj 𝒜 :=
  (affineOpenCover (veroneseGrading 𝒜 d)).openCover.glueMorphisms
    (fun g : Σ k : ℕ+, veroneseGrading 𝒜 d k ↦ veroneseChartInv g.2.2 g.1.pos)
    fun (g h : Σ k : ℕ+, veroneseGrading 𝒜 d k) ↦
      pullback_fst_veroneseChartInv g.2.2 g.1.pos h.2.2 h.1.pos

variable {𝒜 d}

/-- On the chart `Spec A_{(g)}`, `AlgebraicGeometry.Proj.toVeronese` is
`AlgebraicGeometry.Proj.veroneseChart`. -/
@[reassoc (attr := simp)]
theorem awayι_toVeronese (hg : g ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) :
    awayι 𝒜 (g : A) (mem_veroneseGrading.1 hg) (Nat.mul_pos (NeZero.pos d) hk) ≫
      toVeronese 𝒜 d = veroneseChart hg hk :=
  (veroneseAffineOpenCover 𝒜 d).openCover.ι_glueMorphisms _ _ ⟨⟨k, hk⟩, ⟨g, hg⟩⟩

/-- On the chart `Spec A^{(d)}_{(g)}`, `AlgebraicGeometry.Proj.fromVeronese` is
`AlgebraicGeometry.Proj.veroneseChartInv`. -/
@[reassoc (attr := simp)]
theorem awayι_fromVeronese (hg : g ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) :
    awayι (veroneseGrading 𝒜 d) g hg hk ≫ fromVeronese 𝒜 d = veroneseChartInv hg hk :=
  (affineOpenCover (veroneseGrading 𝒜 d)).openCover.ι_glueMorphisms _ _ ⟨⟨k, hk⟩, ⟨g, hg⟩⟩

/-- The preimage under `AlgebraicGeometry.Proj.toVeronese` of the basic open `D₊(a)` of
`Proj A^{(d)}`, for `a ∈ A^{(d)}` homogeneous of positive degree, is the basic open `D₊(a)` of
`Proj A`. On the chart of `g`, both are cut out by `aᵏ / gᵏ'` (up to a `d`-th power). -/
theorem toVeronese_preimage_basicOpen {a : veronese 𝒜 d} {k' : ℕ}
    (ha : a ∈ veroneseGrading 𝒜 d k') (hk' : 0 < k') :
    toVeronese 𝒜 d ⁻¹ᵁ basicOpen (veroneseGrading 𝒜 d) a = basicOpen 𝒜 (a : A) := by
  ext x
  have hx := (veroneseAffineOpenCover 𝒜 d).covers x
  generalize (veroneseAffineOpenCover 𝒜 d).idx x = i at hx
  obtain ⟨k, g, hg⟩ := i
  obtain ⟨y, rfl⟩ := hx
  change y ∈ awayι 𝒜 (g : A) (mem_veroneseGrading.1 hg) (Nat.mul_pos (NeZero.pos d) k.pos) ⁻¹ᵁ
      (toVeronese 𝒜 d ⁻¹ᵁ basicOpen (veroneseGrading 𝒜 d) a) ↔
    y ∈ awayι 𝒜 (g : A) (mem_veroneseGrading.1 hg) (Nat.mul_pos (NeZero.pos d) k.pos) ⁻¹ᵁ
      basicOpen 𝒜 (a : A)
  rw [← Scheme.Hom.comp_preimage, awayι_toVeronese hg k.pos]
  unfold veroneseChart
  rw [Scheme.Hom.comp_preimage, awayι_preimage_basicOpen (hm' := hk') (g_deg := ha),
    awayι_preimage_basicOpen (hm' := Nat.mul_pos (NeZero.pos d) hk')
      (g_deg := mem_veroneseGrading.1 ha)]
  -- the element `aᵈᵏ / gᵈᵏ'` of `A_{(g)}` is the `d`-th power of the image of `aᵏ / gᵏ'`
  have e : Away.isLocalizationElem (mem_veroneseGrading.1 hg) (mem_veroneseGrading.1 ha) =
      awayVeroneseEquiv hg (Away.isLocalizationElem hg ha) ^ d := by
    apply val_injective
    simp only [awayVeroneseEquiv_mk, HomogeneousLocalization.val_pow, Away.val_mk,
      Localization.mk_pow]
    congr 1
    · simp [← pow_mul, mul_comm]
    · ext; simp [← pow_mul, mul_comm]
  change awayVeroneseEquiv hg (Away.isLocalizationElem hg ha) ∉ y.asIdeal ↔
    Away.isLocalizationElem (mem_veroneseGrading.1 hg) (mem_veroneseGrading.1 ha) ∉ y.asIdeal
  rw [e]
  exact not_congr (y.isPrime.pow_mem_iff_mem d (NeZero.pos d)).symm

variable (𝒜 d)

/-- For `d ≠ 0`, the `Proj` of the Veronese subalgebra `A^{(d)} = ⨁ₖ 𝒜 (d k)` is `Proj A`. -/
noncomputable def veroneseIso : Proj (veroneseGrading 𝒜 d) ≅ Proj 𝒜 where
  hom := fromVeronese 𝒜 d
  inv := toVeronese 𝒜 d
  hom_inv_id := (affineOpenCover (veroneseGrading 𝒜 d)).openCover.hom_ext _ _
    fun ⟨k, x, hx⟩ ↦ by
      change awayι _ x hx k.pos ≫ _ = awayι _ x hx k.pos ≫ _
      rw [awayι_fromVeronese_assoc hx k.pos, veroneseChartInv, Category.assoc, awayι_toVeronese,
        veroneseChart, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, RingEquiv.symm_comp,
        CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]
  inv_hom_id := (veroneseAffineOpenCover 𝒜 d).openCover.hom_ext _ _
    fun ⟨k, x, hx⟩ ↦ by
      change awayι 𝒜 _ (mem_veroneseGrading.1 hx) (Nat.mul_pos (NeZero.pos d) k.pos) ≫ _ =
        awayι 𝒜 _ (mem_veroneseGrading.1 hx) (Nat.mul_pos (NeZero.pos d) k.pos) ≫ _
      rw [awayι_toVeronese_assoc hx k.pos, veroneseChart, Category.assoc, awayι_fromVeronese,
        veroneseChartInv, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, RingEquiv.comp_symm,
        CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]

/-- The identification `Proj A^{(d)} ≅ Proj A` lies over `Spec 𝒜 0`: the degree-zero part of
`A^{(d)}` is `𝒜 0`. -/
@[reassoc]
theorem veroneseIso_hom_toSpecZero :
    (veroneseIso 𝒜 d).hom ≫ toSpecZero 𝒜 =
      toSpecZero (veroneseGrading 𝒜 d) ≫
        Spec.map (CommRingCat.ofHom ((veroneseGradingZeroEquiv 𝒜 d).symm : _ →+* _)) :=
  (affineOpenCover (veroneseGrading 𝒜 d)).openCover.hom_ext _ _ fun ⟨k, x, hx⟩ ↦ by
    change awayι _ x hx k.pos ≫ _ = awayι _ x hx k.pos ≫ _
    have e : ((awayVeroneseEquiv hx).symm : _ →+* _).comp
        (fromZeroRingHom 𝒜 (.powers (x : A))) =
        (fromZeroRingHom _ (.powers x)).comp ((veroneseGradingZeroEquiv 𝒜 d).symm : _ →+* _) :=
      RingHom.ext fun a ↦ (awayVeroneseEquiv hx).injective <| by
        obtain ⟨a, rfl⟩ := (veroneseGradingZeroEquiv 𝒜 d).surjective a
        simp [awayVeroneseEquiv_fromZeroRingHom]
    rw [veroneseIso, awayι_fromVeronese_assoc hx k.pos, veroneseChartInv, Category.assoc,
      awayι_toSpecZero, awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]

/-- The identification `Proj A^{(d)} ≅ Proj A` lies over `Spec R`. -/
@[reassoc]
theorem veroneseIso_hom_toSpecCoeff :
    (veroneseIso 𝒜 d).hom ≫ toSpecCoeff 𝒜 = toSpecCoeff (veroneseGrading 𝒜 d) := by
  rw [toSpecCoeff_def, veroneseIso_hom_toSpecZero_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, toSpecCoeff_def]
  -- both sides are `Spec` of `algebraMap R (veroneseGrading 𝒜 d 0)`
  rfl

section Map

variable {R' B : Type u} [CommRing R'] [CommRing B] [Algebra R' B] {ℬ : ℕ → Submodule R' B}
  [GradedAlgebra ℬ] {𝒜 d}

/-- The identification `Proj A^{(d)} ≅ Proj A` is natural in graded ring maps `f : A → B`. -/
@[reassoc]
theorem map_veroneseMap_veroneseIso_hom (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hfd : HomogeneousIdeal.irrelevant (veroneseGrading ℬ d) ≤
      (HomogeneousIdeal.irrelevant (veroneseGrading 𝒜 d)).map (veroneseMap d f)) :
    map (veroneseMap d f) hfd ≫ (veroneseIso 𝒜 d).hom = (veroneseIso ℬ d).hom ≫ map f hf :=
  (mapAffineOpenCover _ hfd).openCover.hom_ext _ _
    fun (s : Σ k : ℕ+, veroneseGrading 𝒜 d k) ↦ by
    obtain ⟨k, g, hg⟩ := s
    change awayι _ (veroneseMap d f g) ((veroneseMap d f).map_mem hg) k.pos ≫ _ =
      awayι _ (veroneseMap d f g) ((veroneseMap d f).map_mem hg) k.pos ≫ _
    change _ ≫ _ ≫ fromVeronese 𝒜 d = _ ≫ fromVeronese ℬ d ≫ _
    rw [awayι_comp_map_assoc (hi := k.pos) (hs := hg), awayι_fromVeronese,
      awayι_fromVeronese_assoc, veroneseChartInv, veroneseChartInv, Category.assoc]
    -- on the chart `D₊(g)`, both sides are `Spec` of the maps `A_{(g)} → B^{(d)}_{(f g)}` that
    -- `awayVeroneseEquiv_awayMap_veroneseMap` identifies
    have e : CommRingCat.ofHom ((awayVeroneseEquiv hg).symm : _ →+* _) ≫
        CommRingCat.ofHom (Away.map (veroneseMap d f) g) =
        CommRingCat.ofHom (Away.map f (g : A)) ≫
          CommRingCat.ofHom (awayVeroneseEquiv ((veroneseMap d f).map_mem hg)).symm.toRingHom := by
      refine CommRingCat.hom_ext (RingHom.ext fun y ↦ ?_)
      apply (awayVeroneseEquiv ((veroneseMap d f).map_mem hg)).injective
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, RingHom.coe_coe,
        Function.comp_apply]
      rw [awayVeroneseEquiv_awayMap_veroneseMap f hg, RingEquiv.apply_symm_apply]
      exact ((awayVeroneseEquiv ((veroneseMap d f).map_mem hg)).apply_symm_apply _).symm
    rw [← Spec.map_comp_assoc, e, Spec.map_comp, Category.assoc]
    exact congrArg (_ ≫ ·)
      (awayι_comp_map f hf (Nat.mul_pos (NeZero.pos d) k.pos) _ (mem_veroneseGrading.1 hg)).symm

end Map

end AlgebraicGeometry.Proj
