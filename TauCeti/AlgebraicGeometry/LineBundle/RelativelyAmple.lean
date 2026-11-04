/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Fibers
public import TauCeti.AlgebraicGeometry.LineBundle.Ample

/-!
# Relatively ample line bundles

Let `f : X ⟶ S` be a morphism of schemes. A line bundle `L` on `X` is *relatively ample* for `f` if
`f` is quasi-compact and the restriction of `L` to the preimage of every affine open of `S` is
ample. As ampleness, this depends only on the isomorphism class of `L`, so it is defined as a
predicate `LineBundleClass.IsRelativelyAmple` on line-bundle classes.

## Main definitions

* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple a f`: the line-bundle class `a`
  is relatively ample for `f`.

## Main results

* `TauCeti.AlgebraicGeometry.LineBundleClass.isRelativelyAmple_pow_iff`: for `n > 0`, the power
  `aⁿ` is relatively ample exactly when `a` is.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.mul_mk_of_isGloballyGenerated`: a
  relatively ample class times a globally generated line bundle is relatively ample.
* `TauCeti.AlgebraicGeometry.LineBundleClass.isRelativelyAmple_one_iff`: the trivial class is
  relatively ample exactly for quasi-affine morphisms; in particular it is relatively ample for
  affine morphisms (`LineBundleClass.isRelativelyAmple_one`).
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.isSeparated`: a morphism carrying
  a relatively ample class is separated.
* `TauCeti.AlgebraicGeometry.LineBundleClass.isRelativelyAmple_iff_isAmple`: over an affine base,
  relative ampleness is ampleness.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.isRelativelyAmple`: over a separated base, an
  ample class is relatively ample for every quasi-compact morphism.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.pullback`: relative ampleness is
  preserved by pullback along affine morphisms of the source; in particular it is
  invariant under isomorphisms of the source over the base
  (`LineBundleClass.isRelativelyAmple_pullback_iff_of_isIso`).
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.isAmple_fiber`: a relatively ample
  class is ample on every fibre.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.comp`: relative ampleness is
  preserved by composition with an affine morphism.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.of_comp`: relative ampleness for
  `f ≫ g` implies relative ampleness for `f` when `g` is separated; for affine `g` the two are
  equivalent (`LineBundleClass.isRelativelyAmple_comp_iff`).
* `TauCeti.AlgebraicGeometry.LineBundleClass.isRelativelyAmple_iff_of_iSup_eq_top`: relative
  ampleness is local on the base; one direction is `LineBundleClass.IsRelativelyAmple.restrict`.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.pullback_snd`: relative ampleness
  is stable under base change.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.pullback_fst_mul_pullback_snd`:
  the exterior product `pr₁* a · pr₂* b` of relatively ample classes is relatively ample for
  `X ×_S Y ⟶ S`.

## References

* [The Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH), the definition of a
  relatively ample invertible sheaf.
* R. Hartshorne, *Algebraic Geometry*, Section II.7.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X Y S : Scheme.{u}}

namespace LineBundleClass

/-- A line-bundle class `a` on `X` is **relatively ample** for `f : X ⟶ S` if `f` is
quasi-compact and the restriction of `a` to the preimage `f⁻¹ V` of every affine open `V` of `S` is
ample. For a line bundle `L`, this says that `L` is relatively ample for `f`. -/
@[stacks 01VH]
structure IsRelativelyAmple (a : LineBundleClass X) (f : X ⟶ S) : Prop where
  /-- A morphism carrying a relatively ample line bundle is quasi-compact. -/
  quasiCompact : QuasiCompact f
  /-- The restriction to the preimage of every affine open of the base is ample. -/
  isAmple_pullback (V : S.Opens) (hV : IsAffineOpen V) : (pullback (f ⁻¹ᵁ V).ι a).IsAmple

/-- If a positive power `aⁿ` of a line-bundle class is relatively ample for `f`, then so is
`a`. -/
theorem IsRelativelyAmple.of_pow {a : LineBundleClass X} {f : X ⟶ S} {n : ℕ} (hn : 0 < n)
    (h : (a ^ n).IsRelativelyAmple f) : a.IsRelativelyAmple f where
  quasiCompact := h.quasiCompact
  isAmple_pullback V hV := IsAmple.of_pow hn <| by
    simpa only [← pullbackHom_apply, map_pow] using h.isAmple_pullback V hV

/-- **Positive powers of a relatively ample class are relatively ample.** -/
theorem IsRelativelyAmple.pow {a : LineBundleClass X} {f : X ⟶ S} (h : a.IsRelativelyAmple f)
    {n : ℕ} (hn : 0 < n) : (a ^ n).IsRelativelyAmple f where
  quasiCompact := h.quasiCompact
  isAmple_pullback V hV := by
    simpa only [← pullbackHom_apply, map_pow] using (h.isAmple_pullback V hV).pow hn

/-- For `n > 0`, the power `aⁿ` of a line-bundle class is relatively ample for `f` exactly when `a`
is. -/
@[simp]
theorem isRelativelyAmple_pow_iff {a : LineBundleClass X} {f : X ⟶ S} {n : ℕ} (hn : 0 < n) :
    (a ^ n).IsRelativelyAmple f ↔ a.IsRelativelyAmple f :=
  ⟨IsRelativelyAmple.of_pow hn, fun h ↦ h.pow hn⟩

/-- **A relatively ample class times a globally generated line bundle is relatively ample.** -/
theorem IsRelativelyAmple.mul_mk_of_isGloballyGenerated {a : LineBundleClass X} {f : X ⟶ S}
    (h : a.IsRelativelyAmple f) {K : InvertibleSheaf X} (hK : K.IsGloballyGenerated) :
    (a * LineBundleClass.mk K).IsRelativelyAmple f where
  quasiCompact := h.quasiCompact
  isAmple_pullback V hV := by
    rw [← pullbackHom_apply, map_mul, pullbackHom_apply, pullbackHom_apply, pullback_mk]
    exact (h.isAmple_pullback V hV).mul_mk_of_isGloballyGenerated (hK.pullback _)

/-- **A morphism carrying a relatively ample line bundle is separated.** Over every affine open
`V` of the base, `f⁻¹ V` carries an ample line bundle and is therefore a separated scheme
(`LineBundleClass.IsAmple.isSeparated`), so `f ∣_ V` is separated; and separatedness is local on
the base. -/
theorem IsRelativelyAmple.isSeparated {a : LineBundleClass X} {f : X ⟶ S}
    (h : a.IsRelativelyAmple f) : IsSeparated f := by
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsSeparated) _
    (iSup_affineOpens_eq_top S)).mpr fun V ↦ ?_
  have := (h.isAmple_pullback V V.2).isSeparated
  infer_instance

/-- **Relative ampleness over an affine base implies ampleness.** If the base `S` is affine and
`a` is relatively ample for `f : X ⟶ S`, then `a` is ample: `X` is the preimage of `S` itself. -/
theorem IsRelativelyAmple.isAmple [IsAffine S] {a : LineBundleClass X} {f : X ⟶ S}
    (h : a.IsRelativelyAmple f) : a.IsAmple := by
  -- `f ⁻¹ᵁ ⊤` is `⊤` by definition (`Scheme.Hom.preimage_top`).
  have h' : (pullback (⊤ : X.Opens).ι a).IsAmple := h.isAmple_pullback ⊤ (isAffineOpen_top S)
  simpa using h'.pullback X.topIso.inv

/-- **Ampleness over a separated base implies relative ampleness.** If the base `S` is separated,
`f : X ⟶ S` is quasi-compact and `a` is ample, then `a` is relatively ample for `f`: the inclusion
of an affine open `V` of `S` is an affine morphism, and so is its base change, the inclusion of the
preimage `f⁻¹ V`, so ampleness pulls back along it. -/
theorem IsAmple.isRelativelyAmple [S.IsSeparated] {a : LineBundleClass X} (h : a.IsAmple)
    (f : X ⟶ S) [QuasiCompact f] : a.IsRelativelyAmple f where
  quasiCompact := inferInstance
  isAmple_pullback V hV := by
    have : IsAffine V := hV
    -- `V ⟶ S ⟶ ⊤_ Scheme` is a morphism of affine schemes and `S ⟶ ⊤_ Scheme` is separated.
    have : IsAffineHom V.ι := IsAffineHom.of_comp V.ι (Limits.terminal.from S)
    have : IsAffineHom (f ⁻¹ᵁ V).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict f V) this
    exact h.pullback _

/-- Over an affine base, relative ampleness is ampleness. -/
theorem isRelativelyAmple_iff_isAmple [IsAffine S] (a : LineBundleClass X) (f : X ⟶ S) :
    a.IsRelativelyAmple f ↔ a.IsAmple := by
  refine ⟨IsRelativelyAmple.isAmple, fun h ↦ ?_⟩
  have := h.compactSpace
  have : QuasiCompact f := (quasiCompact_iff_compactSpace f).mpr inferInstance
  exact h.isRelativelyAmple f

/-- **Relative ampleness is preserved by pullback along an affine morphism.** If `a` is relatively
ample for `f` and `j : Y ⟶ X` is an affine morphism, for instance a closed immersion or an
isomorphism, then the pullback of `a` along `j` is relatively ample for `j ≫ f`. -/
theorem IsRelativelyAmple.pullback {a : LineBundleClass X} {f : X ⟶ S}
    (h : a.IsRelativelyAmple f) (j : Y ⟶ X) [IsAffineHom j] :
    (pullback j a).IsRelativelyAmple (j ≫ f) where
  quasiCompact := by
    have := h.quasiCompact
    infer_instance
  isAmple_pullback V hV := by
    -- `(j ≫ f) ⁻¹ᵁ V` is `j ⁻¹ᵁ f ⁻¹ᵁ V` by definition (`Scheme.Hom.comp_preimage`), but the
    -- type of the pulled-back class depends on the open, so the lemma cannot be rewritten with.
    -- The inclusion of `j ⁻¹ᵁ f ⁻¹ᵁ V` followed by `j` is `j ∣_ f ⁻¹ᵁ V` followed by the
    -- inclusion of `f ⁻¹ᵁ V`.
    change (LineBundleClass.pullback (j ⁻¹ᵁ f ⁻¹ᵁ V).ι
      (LineBundleClass.pullback j a)).IsAmple
    have : IsAffineHom (j ∣_ f ⁻¹ᵁ V) :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict j _).flip inferInstance
    rw [pullback_comp, ← morphismRestrict_ι, ← pullback_comp]
    exact (h.isAmple_pullback V hV).pullback _

/-- **A relatively ample class is ample on every fibre.** If `a` is relatively ample for
`f : X ⟶ S`, then its pullback to the fibre `f⁻¹(s)` is ample for every point `s` of `S`: relative
ampleness pulls back along the affine inclusion of the fibre, and the fibre is the whole preimage
of any affine open containing `s`. -/
theorem IsRelativelyAmple.isAmple_fiber {a : LineBundleClass X} {f : X ⟶ S}
    (h : a.IsRelativelyAmple f) (s : S) : (LineBundleClass.pullback (f.fiberι s) a).IsAmple := by
  obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
  have htop : (f.fiberι s ≫ f) ⁻¹ᵁ V = ⊤ := by
    rw [Scheme.Hom.fiber_fac, Scheme.Hom.comp_preimage,
      Scheme.fromSpecResidueField_preimage_eq_top s hsV, Scheme.Hom.preimage_top]
  have h' := (h.pullback (f.fiberι s)).isAmple_pullback V hV
  rw [htop] at h'
  simpa using h'.pullback (f.fiber s).topIso.inv

/-- **Relative ampleness is invariant under isomorphisms over the base.** If `e : X' ⟶ X` is an
isomorphism, then the pullback of `a` along `e` is relatively ample for `e ≫ f` exactly when `a`
is relatively ample for `f`. -/
theorem isRelativelyAmple_pullback_iff_of_isIso {X' : Scheme.{u}} (e : X' ⟶ X) [IsIso e]
    (a : LineBundleClass X) (f : X ⟶ S) :
    (pullback e a).IsRelativelyAmple (e ≫ f) ↔ a.IsRelativelyAmple f := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.pullback e⟩
  simpa [pullback_comp] using h.pullback (inv e)

/-- **Relative ampleness is preserved by composition with an affine morphism.** If `a` is
relatively ample for `f : X ⟶ S` and `g : S ⟶ T` is affine, then `a` is relatively ample for
`f ≫ g`: the preimage under `g` of an affine open of `T` is an affine open of `S`. -/
theorem IsRelativelyAmple.comp {T : Scheme.{u}} {a : LineBundleClass X} {f : X ⟶ S}
    (h : a.IsRelativelyAmple f) (g : S ⟶ T) [IsAffineHom g] : a.IsRelativelyAmple (f ≫ g) where
  quasiCompact := by
    have := h.quasiCompact
    infer_instance
  -- `(f ≫ g) ⁻¹ᵁ W` is `f ⁻¹ᵁ g ⁻¹ᵁ W` by definition (`Scheme.Hom.comp_preimage`).
  isAmple_pullback W hW := h.isAmple_pullback (g ⁻¹ᵁ W) (hW.preimage g)

/-- **Relative ampleness restricts to opens of the base.** If `a` is relatively ample for
`f : X ⟶ S` and `U` is an open of `S`, then the restriction of `a` to `f⁻¹ U` is relatively ample
for the restriction `f ∣_ U : f⁻¹ U ⟶ U`. -/
theorem IsRelativelyAmple.restrict {a : LineBundleClass X} {f : X ⟶ S}
    (h : a.IsRelativelyAmple f) (U : S.Opens) :
    (LineBundleClass.pullback (f ⁻¹ᵁ U).ι a).IsRelativelyAmple (f ∣_ U) where
  quasiCompact := by
    have := h.quasiCompact
    infer_instance
  isAmple_pullback V hV := by
    -- The preimage of `V` under `f ∣_ U`, viewed in `X`, is the preimage of `V` viewed in `S`.
    have hrange : Set.range (((f ∣_ U) ⁻¹ᵁ V).ι ≫ (f ⁻¹ᵁ U).ι) =
        Set.range (f ⁻¹ᵁ (U.ι ''ᵁ V)).ι := by
      rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_comp,
        Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, image_morphismRestrict_preimage]
    have := (isAmple_pullback_iff_of_isIso (IsOpenImmersion.isoOfRangeEq _ _ hrange).hom _).mpr
      (h.isAmple_pullback _ (hV.image_of_isOpenImmersion U.ι))
    rwa [pullback_comp, IsOpenImmersion.isoOfRangeEq_hom_fac, ← pullback_comp] at this

/-- **Relative ampleness is local on the base.** If `S` is covered by opens `Uᵢ` and the
restriction of `a` to every `f⁻¹ Uᵢ` is relatively ample for `f ∣_ Uᵢ`, then `a` is relatively
ample for `f`. Let `V` be an affine open of `S`. The functions `g` on `V` with `D(g)` inside some
`Uᵢ` have basic opens covering `V`. Their pullbacks to `f⁻¹ V` have basic opens `f⁻¹ D(g)`, the
preimages of affine opens of the `Uᵢ`, on which `a` is ample. These are quasi-compact, so `f⁻¹ V`
is quasi-compact, and ampleness can be checked on such a cover
(`LineBundleClass.IsAmple.of_iSup_basicOpen_eq_top`). -/
theorem isRelativelyAmple_of_iSup_eq_top {a : LineBundleClass X} {f : X ⟶ S} {ι : Type*}
    (U : ι → S.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, (LineBundleClass.pullback (f ⁻¹ᵁ U i).ι a).IsRelativelyAmple (f ∣_ U i)) :
    a.IsRelativelyAmple f := by
  -- The global functions on `f⁻¹ V` pulled back from `V`, and their basic opens.
  let r (V : S.Opens) (g : Γ(S, V)) : Γ(f ⁻¹ᵁ V, ⊤) := (f ⁻¹ᵁ V).topIso.inv (f.app V g)
  have himage (V : S.Opens) (g : Γ(S, V)) :
      (f ⁻¹ᵁ V).ι ''ᵁ (f ⁻¹ᵁ V).toScheme.basicOpen (r V g) = f ⁻¹ᵁ S.basicOpen g := by
    rw [Scheme.Opens.ι_image_basicOpen_topIso_inv, Scheme.preimage_basicOpen]
  -- The class is ample on `f⁻¹ D(g)` when `D(g) ⊆ Uᵢ`.
  have hpiece (V : S.Opens) (hV : IsAffineOpen V) (g : Γ(S, V)) (i : ι)
      (hgi : S.basicOpen g ≤ U i) :
      (LineBundleClass.pullback ((f ⁻¹ᵁ V).toScheme.basicOpen (r V g)).ι
        (LineBundleClass.pullback (f ⁻¹ᵁ V).ι a)).IsAmple := by
    -- `D(g)` is an affine open of `Uᵢ`, over which `a` is ample.
    have hW : IsAffineOpen ((U i).ι ⁻¹ᵁ S.basicOpen g) :=
      (hV.basicOpen g).preimage_of_isOpenImmersion (U i).ι (by rwa [Scheme.Opens.opensRange_ι])
    have h' := (h i).isAmple_pullback _ hW
    rw [pullback_comp] at h'
    -- Both open subschemes of `X` are `f⁻¹ D(g)`.
    have hrange : Set.range (((f ⁻¹ᵁ V).toScheme.basicOpen (r V g)).ι ≫ (f ⁻¹ᵁ V).ι) =
        Set.range (((f ∣_ U i) ⁻¹ᵁ ((U i).ι ⁻¹ᵁ S.basicOpen g)).ι ≫ (f ⁻¹ᵁ U i).ι) := by
      rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_comp,
        Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, himage,
        image_morphismRestrict_preimage, (U i).ι.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι, inf_eq_right.mpr hgi]
    rw [pullback_comp, ← IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange, ← pullback_comp,
      isAmple_pullback_iff_of_isIso]
    exact h'
  -- The basic opens `D(g)` with `D(g)` inside some `Uᵢ` cover an affine open `V`.
  have hcov (V : S.Opens) (hV : IsAffineOpen V) (x : S) (hx : x ∈ V) :
      ∃ g : Γ(S, V), (∃ i, S.basicOpen g ≤ U i) ∧ x ∈ S.basicOpen g := by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hU.ge (TopologicalSpace.Opens.mem_top x))
    obtain ⟨g, hgi, hg⟩ := hV.exists_basicOpen_le (V := U i) ⟨x, hi⟩ hx
    exact ⟨g, ⟨i, hgi⟩, hg⟩
  -- The preimage of an affine open is a finite union of the quasi-compact `f⁻¹ D(g)`.
  have hcpt (V : S.Opens) (hV : IsAffineOpen V) : IsCompact (f ⁻¹ᵁ V : Set X) := by
    have hpc (g : {g : Γ(S, V) // ∃ i, S.basicOpen g ≤ U i}) :
        IsCompact (f ⁻¹ᵁ S.basicOpen g.1 : Set X) := by
      obtain ⟨g, i, hgi⟩ := g
      have := (hpiece V hV g i hgi).compactSpace
      have hc := isCompact_range
        (((f ⁻¹ᵁ V).toScheme.basicOpen (r V g)).ι ≫ (f ⁻¹ᵁ V).ι).continuous
      rwa [← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
        himage] at hc
    obtain ⟨s, hs⟩ := hV.isCompact.elim_finite_subcover
      (fun g : {g : Γ(S, V) // ∃ i, S.basicOpen g ≤ U i} ↦ (S.basicOpen g.1 : Set S))
      (fun g ↦ (S.basicOpen g.1).isOpen) fun x hx ↦ by
        obtain ⟨g, hgi, hg⟩ := hcov V hV x hx
        exact Set.mem_iUnion.mpr ⟨⟨g, hgi⟩, hg⟩
    have heq : (f ⁻¹ᵁ V : Set X) = ⋃ g ∈ s, (f ⁻¹ᵁ S.basicOpen g.1 : Set X) := by
      refine subset_antisymm (fun x hx ↦ ?_) (Set.iUnion₂_subset fun g _ x hx ↦ ?_)
      · obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.mp (hs hx)
        exact Set.mem_iUnion₂.mpr ⟨g, hg, hxg⟩
      · exact S.basicOpen_le g.1 hx
    rw [heq]
    exact s.isCompact_biUnion fun g _ ↦ hpc g
  refine ⟨quasiCompact_iff_forall_isAffineOpen.mpr hcpt, fun V hV ↦ ?_⟩
  have : CompactSpace (f ⁻¹ᵁ V) := isCompact_iff_compactSpace.mp (hcpt V hV)
  refine IsAmple.of_iSup_basicOpen_eq_top
    (fun g : {g : Γ(S, V) // ∃ i, S.basicOpen g ≤ U i} ↦ r V g.1) ?_
    fun ⟨g, i, hgi⟩ ↦ hpiece V hV g i hgi
  refine eq_top_iff.mpr fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
  obtain ⟨g, hgi, hg⟩ := hcov V hV (f y.1) y.2
  refine ⟨⟨g, hgi⟩, ?_⟩
  rw [← (f ⁻¹ᵁ V).ι.preimage_image_eq ((f ⁻¹ᵁ V).toScheme.basicOpen (r V g)), himage]
  exact hg

/-- **Relative ampleness is local on the base**: for an open cover `Uᵢ` of `S`, the class `a` is
relatively ample for `f` exactly when its restriction to every `f⁻¹ Uᵢ` is relatively ample for
`f ∣_ Uᵢ`. -/
theorem isRelativelyAmple_iff_of_iSup_eq_top {a : LineBundleClass X} {f : X ⟶ S} {ι : Type*}
    (U : ι → S.Opens) (hU : ⨆ i, U i = ⊤) :
    a.IsRelativelyAmple f ↔
      ∀ i, (LineBundleClass.pullback (f ⁻¹ᵁ U i).ι a).IsRelativelyAmple (f ∣_ U i) :=
  ⟨fun h i ↦ h.restrict (U i), isRelativelyAmple_of_iSup_eq_top U hU⟩

/-- **Relative ampleness descends along a separated morphism.** If `a` is relatively ample for
`f ≫ g` and `g : S ⟶ T` is separated, then `a` is relatively ample for `f`. Over an affine open `W`
of `T`, the class `a` is ample on `(f ≫ g)⁻¹ W = f⁻¹ (g⁻¹ W)` and `g⁻¹ W` is a separated scheme, so
`a` is relatively ample for `f ∣_ g⁻¹ W` (`LineBundleClass.IsAmple.isRelativelyAmple`). These
opens cover `S`, and relative ampleness is local on the base. -/
theorem IsRelativelyAmple.of_comp {T : Scheme.{u}} {a : LineBundleClass X} {f : X ⟶ S}
    {g : S ⟶ T} [IsSeparated g] (h : a.IsRelativelyAmple (f ≫ g)) : a.IsRelativelyAmple f := by
  refine isRelativelyAmple_of_iSup_eq_top (fun W : T.affineOpens ↦ g ⁻¹ᵁ W) ?_ fun W ↦ ?_
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  have : IsAffine W := W.2
  have : (g ⁻¹ᵁ W).toScheme.IsSeparated := ⟨Limits.terminal.comp_from (g ∣_ W) ▸ inferInstance⟩
  -- `(f ≫ g) ⁻¹ᵁ W` is `f ⁻¹ᵁ g ⁻¹ᵁ W` by definition (`Scheme.Hom.comp_preimage`).
  have h' : (LineBundleClass.pullback (f ⁻¹ᵁ g ⁻¹ᵁ W).ι a).IsAmple := h.isAmple_pullback W W.2
  have := h'.compactSpace
  have : QuasiCompact ((f ∣_ g ⁻¹ᵁ W) ≫ g ∣_ W) :=
    (quasiCompact_iff_compactSpace _).mpr inferInstance
  have : QuasiCompact (f ∣_ g ⁻¹ᵁ W) := .of_comp _ (g ∣_ W)
  exact h'.isRelativelyAmple _

/-- For an affine morphism `g`, a class is relatively ample for `f ≫ g` exactly when it is
relatively ample for `f`. -/
theorem isRelativelyAmple_comp_iff {T : Scheme.{u}} {a : LineBundleClass X} {f : X ⟶ S}
    (g : S ⟶ T) [IsAffineHom g] : a.IsRelativelyAmple (f ≫ g) ↔ a.IsRelativelyAmple f :=
  ⟨IsRelativelyAmple.of_comp, fun h ↦ h.comp g⟩

/-- **Relative ampleness is stable under base change.** If `a` is relatively ample for
`f : X ⟶ S` and `g : S' ⟶ S` is any morphism, then the pullback of `a` to `X ×_S S'` is relatively
ample for the projection to `S'`. The affine opens `V'` of `S'` mapping into an affine open `V` of
`S` cover `S'`, and relative ampleness is local on the base. Over such a `V'`, the preimage of
`V'` maps to `f⁻¹ V` by a base change of the affine morphism `V' ⟶ V`, and `a` is ample on
`f⁻¹ V`, so its pullback is ample. -/
theorem IsRelativelyAmple.pullback_snd {S' : Scheme.{u}} {a : LineBundleClass X} {f : X ⟶ S}
    (h : a.IsRelativelyAmple f) (g : S' ⟶ S) :
    (LineBundleClass.pullback (Limits.pullback.fst f g) a).IsRelativelyAmple
      (Limits.pullback.snd f g) := by
  set f' := Limits.pullback.snd f g
  set g' := Limits.pullback.fst f g
  -- The affine opens of `S'` mapping into an affine open of `S` cover `S'`.
  let 𝒱 := {V' : S'.Opens // IsAffineOpen V' ∧ ∃ V : S.Opens, IsAffineOpen V ∧ V' ≤ g ⁻¹ᵁ V}
  refine isRelativelyAmple_of_iSup_eq_top (fun V' : 𝒱 ↦ V'.1)
    (eq_top_iff.mpr fun s' _ ↦ ?_) fun ⟨V', hV', V, hV, hle⟩ ↦ ?_
  · obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (x := g s') (U := ⊤) trivial
    obtain ⟨V', hV', hsV', hle⟩ := exists_isAffineOpen_mem_and_subset (x := s') (U := g ⁻¹ᵁ V) hsV
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V', hV', V, hV, hle⟩, hsV'⟩
  have : IsAffine V' := hV'
  have : IsAffine V := hV
  rw [isRelativelyAmple_iff_isAmple, pullback_comp]
  -- The open of the cover indexed by `⟨V', _⟩` is `V'` by definition.
  change (LineBundleClass.pullback ((f' ⁻¹ᵁ V').ι ≫ g') a).IsAmple
  -- `f'⁻¹ V' ⟶ X` factors through `f⁻¹ V`, by a base change of the affine `V' ⟶ V`.
  let k : (V' : Scheme) ⟶ V := IsOpenImmersion.lift V.ι (V'.ι ≫ g) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hle x.2)
  let e : (f' ⁻¹ᵁ V' : Scheme) ⟶ f ⁻¹ᵁ V := IsOpenImmersion.lift (f ⁻¹ᵁ V).ι ((f' ⁻¹ᵁ V').ι ≫ g')
    (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      -- Membership in `f ⁻¹ᵁ V` is membership of the image in `V`.
      change f (g' ((f' ⁻¹ᵁ V').ι x)) ∈ V
      rw [← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply]
      exact hle x.2)
  have hk : k ≫ V.ι = V'.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have he : e ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g' := IsOpenImmersion.lift_fac _ _ _
  have hsq : IsPullback e (f' ∣_ V') (f ∣_ V) k := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict f V).flip
    · rw [he, hk]
      exact (isPullback_morphismRestrict f' V').flip.paste_horiz (IsPullback.of_hasPullback f g)
    · rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, hk,
        ← Category.assoc, he, morphismRestrict_ι_assoc, Category.assoc, Limits.pullback.condition]
  have : IsAffineHom e := MorphismProperty.of_isPullback hsq.flip inferInstance
  rw [← he, ← pullback_comp]
  exact (h.isAmple_pullback V hV).pullback e

/-- **Exterior products of relatively ample classes are relatively ample.** If `a` is relatively
ample for `f : X ⟶ S` and `b` is relatively ample for `g : Y ⟶ S`, then `pr₁* a · pr₂* b` is
relatively ample for `X ×_S Y ⟶ S`. Over an affine open `V` of `S`, the preimage of `V` in
`X ×_S Y` is the fibre product of `f⁻¹ V` and `g⁻¹ V` over `V`, on which the classes are ample
(`LineBundleClass.IsAmple.pullback_mul_pullback`). -/
theorem IsRelativelyAmple.pullback_fst_mul_pullback_snd {a : LineBundleClass X}
    {b : LineBundleClass Y} {f : X ⟶ S} {g : Y ⟶ S} (ha : a.IsRelativelyAmple f)
    (hb : b.IsRelativelyAmple g) :
    (LineBundleClass.pullback (Limits.pullback.fst f g) a *
      LineBundleClass.pullback (Limits.pullback.snd f g) b).IsRelativelyAmple
      (Limits.pullback.snd f g ≫ g) where
  quasiCompact := by
    have := ha.quasiCompact
    have := hb.quasiCompact
    infer_instance
  isAmple_pullback V hV := by
    have : IsAffine V := hV
    set p₁ := Limits.pullback.fst f g
    set p₂ := Limits.pullback.snd f g
    -- The preimage of `V` is `p₂ ⁻¹ᵁ g ⁻¹ᵁ V` by definition (`Scheme.Hom.comp_preimage`).
    set W := (p₂ ≫ g) ⁻¹ᵁ V
    let q₁ : (W : Scheme) ⟶ f ⁻¹ᵁ V := IsOpenImmersion.lift (f ⁻¹ᵁ V).ι (W.ι ≫ p₁) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      -- Membership in `f ⁻¹ᵁ V` is membership of the image in `V`.
      change f (p₁ (W.ι x)) ∈ V
      rw [← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply]
      exact x.2)
    let q₂ : (W : Scheme) ⟶ g ⁻¹ᵁ V := p₂ ∣_ g ⁻¹ᵁ V
    have hq₁ : q₁ ≫ (f ⁻¹ᵁ V).ι = W.ι ≫ p₁ := IsOpenImmersion.lift_fac _ _ _
    have hq₂ : q₂ ≫ (g ⁻¹ᵁ V).ι = W.ι ≫ p₂ := morphismRestrict_ι _ _
    have hsq : IsPullback q₁ q₂ (f ∣_ V) (g ∣_ V) := by
      refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict f V).flip
      · rw [hq₁, morphismRestrict_ι]
        exact (isPullback_morphismRestrict p₂ (g ⁻¹ᵁ V)).flip.paste_horiz
          (IsPullback.of_hasPullback f g)
      · rw [← cancel_mono V.ι]
        simp only [Category.assoc, morphismRestrict_ι]
        rw [reassoc_of% hq₁, reassoc_of% hq₂, Limits.pullback.condition]
    rw [pullback_mul, pullback_comp, pullback_comp, ← hq₁, ← hq₂, ← pullback_comp,
      ← pullback_comp]
    exact (ha.isAmple_pullback V hV).pullback_mul_pullback (hb.isAmple_pullback V hV) hsq

/-- The trivial class is relatively ample for `f` exactly when `f` is quasi-affine: `f` is
quasi-compact and the preimage of every affine open of the base is quasi-affine. -/
@[simp]
theorem isRelativelyAmple_one_iff {f : X ⟶ S} :
    (1 : LineBundleClass X).IsRelativelyAmple f ↔
      QuasiCompact f ∧ ∀ V : S.Opens, IsAffineOpen V → (f ⁻¹ᵁ V).toScheme.IsQuasiAffine := by
  refine ⟨fun h ↦ ⟨h.quasiCompact, fun V hV ↦ ?_⟩, fun ⟨hf, h⟩ ↦ ⟨hf, fun V hV ↦ ?_⟩⟩
  · simpa using h.isAmple_pullback V hV
  · have := h V hV
    simpa using isAmple_one (X := (f ⁻¹ᵁ V).toScheme)

/-- The trivial class is relatively ample for an affine morphism. -/
theorem isRelativelyAmple_one (f : X ⟶ S) [IsAffineHom f] :
    (1 : LineBundleClass X).IsRelativelyAmple f :=
  isRelativelyAmple_one_iff.mpr ⟨inferInstance, fun V hV ↦
    have : IsAffine (f ⁻¹ᵁ V) := hV.preimage f
    inferInstance⟩

/-- Every torsion line-bundle class is relatively ample for an affine morphism. -/
theorem isRelativelyAmple_of_pow_eq_one (f : X ⟶ S) [IsAffineHom f] {a : LineBundleClass X}
    {n : ℕ} (hn : 0 < n) (h : a ^ n = 1) : a.IsRelativelyAmple f :=
  .of_pow hn (h ▸ isRelativelyAmple_one f)

end LineBundleClass

namespace InvertibleSheaf

/-- For `n > 0`, the tensor power `L^{⊗n}` is relatively ample for `f` exactly when `L` is. -/
theorem isRelativelyAmple_tensorPow_iff {L : InvertibleSheaf X} {f : X ⟶ S} {n : ℕ}
    (hn : 0 < n) :
    (LineBundleClass.mk (L.tensorPow n)).IsRelativelyAmple f ↔
      (LineBundleClass.mk L).IsRelativelyAmple f := by
  rw [LineBundleClass.mk_tensorPow, LineBundleClass.isRelativelyAmple_pow_iff hn]

end InvertibleSheaf

end AlgebraicGeometry

end TauCeti
