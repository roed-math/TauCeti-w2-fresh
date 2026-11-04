/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import TauCeti.AlgebraicGeometry.Fibers
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample
public import TauCeti.AlgebraicGeometry.RelativeProj.Proper
public import TauCeti.AlgebraicGeometry.RelativeProj.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf

/-!
# Relatively ample and relatively very ample line bundles, and projective morphisms

Let `f : X ⟶ S` be a morphism of schemes. A line bundle `L` on `X` is *relatively ample* for `f` if
`f` is quasi-compact and the restriction of `L` to the preimage of every affine open of `S` is
ample. As ampleness, this depends only on the isomorphism class of `L`, so it is defined as a
predicate `LineBundleClass.IsRelativelyAmple` on line-bundle classes. A line bundle `L` is
*relatively very ample* for `f` if there are a graded quasi-coherent `𝒪_S`-algebra `A`, generated
in degree one, and an immersion `i : X ⟶ Proj_S(A)` over `S` with `i^* 𝒪(1) ≅ L`. The morphism
`f` is *projective* if it factors as a closed immersion into such a relative `Proj`, with `A` of
finite type and `A₀` finite over `𝒪_S`, followed by its structure morphism.

Since `A₁` generates `A` and the degree-zero parts of the homogeneous localizations of `A` only
see the positive part of `A`, `Proj_S(A)` is a closed subscheme of `ℙ(A₁) = Proj_S(Sym A₁)` with
`𝒪(1)` pulling back to `𝒪(1)`; conversely `Sym ℰ` satisfies all the conditions above when `ℰ` is
quasi-coherent (and of finite type, for projectivity). So these are the notions of the Stacks
Project defined through `ℙ(ℰ)`.

## Main definitions

* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple a f`: the line-bundle class `a`
  is relatively ample for `f`.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.IsRelativelyVeryAmple L f`: `L` is relatively very
  ample for `f`.
* `TauCeti.AlgebraicGeometry.IsProjective f`: `f` is projective.

## Main results

* `TauCeti.AlgebraicGeometry.LineBundleClass.isRelativelyAmple_pow_iff`: for `n > 0`, the power
  `aⁿ` is relatively ample exactly when `a` is.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.mul_mk_of_isGloballyGenerated`: a
  relatively ample class times a globally generated line bundle is relatively ample.
* `TauCeti.AlgebraicGeometry.LineBundleClass.isRelativelyAmple_one_iff`: the trivial class is
  relatively ample exactly for quasi-affine morphisms; in particular it is relatively ample for
  affine morphisms (`LineBundleClass.isRelativelyAmple_one`).
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
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.restrict`: relative ampleness
  restricts to opens of the base.
* `TauCeti.AlgebraicGeometry.LineBundleClass.isRelativelyAmple_relativeProjTwistingSheafOne`:
  `𝒪(1)` is relatively ample on the relative `Proj` of an algebra generated in degree one whose
  structure morphism is quasi-compact.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.isRelativelyVeryAmple_relativeProjTwistingSheaf`:
  `𝒪(1)` is relatively very ample on the relative `Proj` of an algebra generated in degree one.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.IsRelativelyVeryAmple.pullback`: relative very
  ampleness is preserved by pullback along an immersion.
* `TauCeti.AlgebraicGeometry.IsProjective.exists_isRelativelyVeryAmple_isRelativelyAmple`: a
  projective morphism has a line bundle that is relatively very ample and relatively ample.
* `TauCeti.AlgebraicGeometry.IsProjective.isProper`: a projective morphism is proper.
* `TauCeti.AlgebraicGeometry.isProjective_relativeProjToBase_gradedSymmetricAlgebra`: the
  projective bundle `ℙ(F) = Proj_S(Sym F)` of a quasicoherent sheaf `F` of finite type is
  projective, and `𝒪(1)` on it is relatively ample
  (`LineBundleClass.isRelativelyAmple_relativeProjTwistingSheafOne_gradedSymmetricAlgebra`).

## References

* [The Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH), the definition of a
  relatively ample invertible sheaf.
* The Stacks Project, Chapter *Morphisms of Schemes*, sections *Very ample sheaves* and
  *Projective morphisms*.
* R. Hartshorne, *Algebraic Geometry*, Sections II.5 and II.7.
-/

public section

open CategoryTheory AlgebraicGeometry DirectSum

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X Y S : Scheme.{u}}

/-- The invertible sheaf `𝒪(1)` on the relative `Proj` of a graded algebra generated in degree
one. -/
noncomputable abbrev _root_.CategoryTheory.CommMon.relativeProjTwistingSheafOne
    (A : CommMon (GradedObject ℕ S.Modules)) [∀ n, (A.X n).IsQuasicoherent]
    (hA : A.IsGeneratedInDegreeOne) : InvertibleSheaf A.relativeProj :=
  ⟨A.relativeProjTwistingSheaf 1, A.isInvertible_relativeProjTwistingSheaf hA 1⟩

namespace InvertibleSheaf

/-- A line bundle `L` on `X` is **relatively very ample** for `f : X ⟶ S` if there are a graded
quasi-coherent `𝒪_S`-algebra `A`, generated in degree one, and an immersion
`i : X ⟶ Proj_S(A)` over `S` such that `i^* 𝒪(1) ≅ L`. -/
def IsRelativelyVeryAmple (L : InvertibleSheaf X) (f : X ⟶ S) : Prop :=
  ∃ (A : CommMon (GradedObject ℕ S.Modules)) (_ : ∀ n, (A.X n).IsQuasicoherent)
    (_ : A.IsGeneratedInDegreeOne) (i : X ⟶ A.relativeProj),
    IsImmersion i ∧ i ≫ A.relativeProjToBase = f ∧
      Nonempty ((Scheme.Modules.pullback i).obj (A.relativeProjTwistingSheaf 1) ≅ L.obj)

/-- Relative very ampleness depends only on the isomorphism class of the line bundle. -/
theorem IsRelativelyVeryAmple.of_iso {L K : InvertibleSheaf X} {f : X ⟶ S}
    (hL : L.IsRelativelyVeryAmple f) (e : L.obj ≅ K.obj) : K.IsRelativelyVeryAmple f := by
  obtain ⟨A, _, hA, i, hi, hif, ⟨e'⟩⟩ := hL
  exact ⟨A, _, hA, i, hi, hif, ⟨e' ≪≫ e⟩⟩

/-- **`𝒪(1)` is relatively very ample.** On the relative `Proj` of a graded algebra generated in
degree one, the twisting sheaf `𝒪(1)` is relatively very ample for the structure morphism. -/
theorem isRelativelyVeryAmple_relativeProjTwistingSheaf (A : CommMon (GradedObject ℕ S.Modules))
    [∀ n, (A.X n).IsQuasicoherent] (hA : A.IsGeneratedInDegreeOne) :
    (A.relativeProjTwistingSheafOne hA).IsRelativelyVeryAmple A.relativeProjToBase :=
  ⟨A, inferInstance, hA, 𝟙 _, inferInstance, Category.id_comp _,
    ⟨(Scheme.Modules.pullbackId _).app _⟩⟩

/-- **Relative very ampleness is preserved by pullback along an immersion.** If `L` is relatively
very ample for `f` and `j : Y ⟶ X` is an immersion, then `j^* L` is relatively very ample for
`j ≫ f`. -/
theorem IsRelativelyVeryAmple.pullback {L : InvertibleSheaf X} {f : X ⟶ S}
    (hL : L.IsRelativelyVeryAmple f) (j : Y ⟶ X) [IsImmersion j] :
    ((InvertibleSheaf.pullback j).obj L).IsRelativelyVeryAmple (j ≫ f) := by
  obtain ⟨A, _, hA, i, hi, rfl, ⟨e⟩⟩ := hL
  exact ⟨A, _, hA, j ≫ i, inferInstance, Category.assoc _ _ _,
    ⟨((Scheme.Modules.pullbackComp j i).app _).symm ≪≫ (Scheme.Modules.pullback j).mapIso e⟩⟩

/-- A relatively very ample line bundle lives on a scheme separated over the base. -/
theorem IsRelativelyVeryAmple.isSeparated {L : InvertibleSheaf X} {f : X ⟶ S}
    (hL : L.IsRelativelyVeryAmple f) : IsSeparated f := by
  obtain ⟨A, _, -, i, hi, rfl, -⟩ := hL
  infer_instance

end InvertibleSheaf

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

/-- **`𝒪(1)` is relatively ample on a quasi-compact relative `Proj`.** If `A` is generated in degree
one and the structure morphism `Proj_S(A) ⟶ S` is quasi-compact, then `𝒪(1)` is relatively ample
for it: over an affine open `V` of `S`, the relative `Proj` is the quasi-compact scheme
`Proj (⨁ n, Γ(Aₙ, V))`, on which `𝒪(1)` restricts to the twisting sheaf `𝒪(1)`, which is ample. -/
theorem LineBundleClass.isRelativelyAmple_relativeProjTwistingSheafOne
    (A : CommMon (GradedObject ℕ S.Modules)) [∀ n, (A.X n).IsQuasicoherent]
    (hA : A.IsGeneratedInDegreeOne) [QuasiCompact A.relativeProjToBase] :
    (LineBundleClass.mk (A.relativeProjTwistingSheafOne hA)).IsRelativelyAmple
      A.relativeProjToBase where
  quasiCompact := inferInstance
  isAmple_pullback V hV := by
    let U : S.AffineZariskiSite := ⟨V, hV⟩
    let c := A.relativeProjCover.f U
    -- The chart over `V` is the preimage of `V`.
    have hrange : Set.range c = Set.range (A.relativeProjToBase ⁻¹ᵁ V).ι := by
      rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι,
        A.relativeProjToBase_preimage U]
    let e := IsOpenImmersion.isoOfRangeEq c _ hrange
    rw [← isAmple_pullback_iff_of_isIso e.hom, pullback_comp,
      IsOpenImmersion.isoOfRangeEq_hom_fac, pullback_mk]
    -- The degree-one standard opens cover the chart, which is quasi-compact.
    have hcover : ⨆ g : A.gradedSectionsGrading V 1,
        Proj.basicOpen (A.gradedSectionsGrading V) (g : ⨁ n, Γ(A.X n, V)) = ⊤ :=
      Proj.iSup_basicOpen_eq_top' _ _ (fun g ↦ ⟨1, g.2⟩)
        (by simpa using A.isGeneratedInDegreeOne_iff.mp hA V hV)
    have : CompactSpace (Proj (A.gradedSectionsGrading V)) := by
      have hV' := QuasiCompact.isCompact_preimage (f := A.relativeProjToBase) _ V.isOpen
        hV.isCompact
      have hpre : A.relativeProjToBase ⁻¹' V = c '' Set.univ := by
        rw [Set.image_univ, hrange, Scheme.Opens.range_ι]
        rfl
      rw [hpre, ← c.isOpenEmbedding.isCompact_iff] at hV'
      exact ⟨hV'⟩
    -- On the chart, the pullback of `𝒪(1)` is the twisting sheaf `𝒪(1)`.
    have hiso : (Scheme.Modules.pullback c).obj (A.relativeProjTwistingSheaf 1) ≅
        Proj.twistingSheaf (A.gradedSectionsGrading V) 1 :=
      ((Scheme.Modules.restrictFunctorIsoPullback c).app _).symm ≪≫
        A.restrictRelativeProjTwistingSheafIso 1 U
    rw [show LineBundleClass.mk ((InvertibleSheaf.pullback c).obj _) = LineBundleClass.mk
        ⟨_, Proj.isInvertible_twistingSheaf_of_iSup_eq_top _ (fun g ↦ g.2) hcover 1⟩ from
      LineBundleClass.mk_eq_mk_iff.mpr ⟨eqToIso (InvertibleSheaf.pullback_obj_obj _ _) ≪≫ hiso⟩]
    exact Proj.isAmple_twistingSheaf_one _ (fun g ↦ g.2) hcover

/-- A morphism `f : X ⟶ S` is **projective** if it factors as a closed immersion
`i : X ⟶ Proj_S(A)` followed by the structure morphism of the relative `Proj` of a graded
quasi-coherent `𝒪_S`-algebra `A` generated in degree one, of finite type over `𝒪_S`, with `A₀`
finite over `𝒪_S`. -/
class IsProjective (f : X ⟶ S) : Prop where
  /-- `f` is a closed immersion into such a relative `Proj` followed by its structure morphism. -/
  exists_isClosedImmersion : ∃ (A : CommMon (GradedObject ℕ S.Modules))
    (_ : ∀ n, (A.X n).IsQuasicoherent) (_ : A.IsGeneratedInDegreeOne)
    (_ : ∀ U : S.Opens, IsAffineOpen U → Algebra.FiniteType Γ(S, U) (⨁ n, Γ(A.X n, U)))
    (_ : ∀ U : S.Opens, IsAffineOpen U → Module.Finite Γ(S, U) Γ(A.X 0, U))
    (i : X ⟶ A.relativeProj), IsClosedImmersion i ∧ i ≫ A.relativeProjToBase = f

/-- The structure morphism of the relative `Proj` of a graded algebra generated in degree one, of
finite type and with finite degree-zero part, is projective. -/
theorem isProjective_relativeProjToBase (A : CommMon (GradedObject ℕ S.Modules))
    [∀ n, (A.X n).IsQuasicoherent] (hA : A.IsGeneratedInDegreeOne)
    (h : ∀ U : S.Opens, IsAffineOpen U → Algebra.FiniteType Γ(S, U) (⨁ n, Γ(A.X n, U)))
    (h₀ : ∀ U : S.Opens, IsAffineOpen U → Module.Finite Γ(S, U) Γ(A.X 0, U)) :
    IsProjective A.relativeProjToBase :=
  ⟨A, inferInstance, hA, h, h₀, 𝟙 _, inferInstance, Category.id_comp _⟩

/-- A closed immersion followed by a projective morphism is projective. -/
instance (j : Y ⟶ X) [IsClosedImmersion j] (f : X ⟶ S) [IsProjective f] :
    IsProjective (j ≫ f) := by
  obtain ⟨A, _, hA, h, h₀, i, hi, rfl⟩ := IsProjective.exists_isClosedImmersion (f := f)
  exact ⟨A, _, hA, h, h₀, j ≫ i, inferInstance, Category.assoc _ _ _⟩

/-- **A projective morphism has a relatively very ample and relatively ample line bundle**: the
pullback of `𝒪(1)` along the closed immersion into the relative `Proj`. It is relatively ample
because `𝒪(1)` is relatively ample on the relative `Proj`, whose structure morphism is proper, and
relative ampleness pulls back along the closed immersion, an affine morphism. -/
theorem IsProjective.exists_isRelativelyVeryAmple_isRelativelyAmple (f : X ⟶ S) [IsProjective f] :
    ∃ L : InvertibleSheaf X,
      L.IsRelativelyVeryAmple f ∧ (LineBundleClass.mk L).IsRelativelyAmple f := by
  obtain ⟨A, _, hA, h, h₀, i, hi, rfl⟩ := IsProjective.exists_isClosedImmersion (f := f)
  have := CommMon.isProper_relativeProjToBase h h₀
  refine ⟨(InvertibleSheaf.pullback i).obj (A.relativeProjTwistingSheafOne hA),
    ⟨A, _, hA, i, inferInstance, rfl, ⟨Iso.refl _⟩⟩, ?_⟩
  rw [← LineBundleClass.pullback_mk]
  exact (LineBundleClass.isRelativelyAmple_relativeProjTwistingSheafOne A hA).pullback i

/-- **A projective morphism is proper**: it is a closed immersion followed by the structure
morphism of a relative `Proj` of a graded algebra of finite type with finite degree-zero part. -/
instance IsProjective.isProper (f : X ⟶ S) [IsProjective f] : IsProper f := by
  obtain ⟨A, _, -, h, h₀, i, hi, rfl⟩ := IsProjective.exists_isClosedImmersion (f := f)
  have := CommMon.isProper_relativeProjToBase h h₀
  infer_instance

/-! ### Projective bundles -/

section ProjectiveBundle

variable (F : QuasicoherentSheaf S)

/-- **`𝒪(1)` is relatively very ample on a projective bundle**: on `ℙ(F) = Proj_S(Sym F)` for a
quasicoherent sheaf `F`, since `Sym F` is generated in degree one. -/
theorem InvertibleSheaf.isRelativelyVeryAmple_relativeProjTwistingSheaf_gradedSymmetricAlgebra :
    (((gradedSymmetricAlgebra S).obj F).obj.relativeProjTwistingSheafOne
      (isGeneratedInDegreeOne_gradedSymmetricAlgebra F)).IsRelativelyVeryAmple
      ((gradedSymmetricAlgebra S).obj F).obj.relativeProjToBase :=
  isRelativelyVeryAmple_relativeProjTwistingSheaf _ _

/-- **`𝒪(1)` is relatively ample on a projective bundle**: on `ℙ(F) = Proj_S(Sym F)` for a
quasicoherent sheaf `F` of finite type, whose structure morphism is proper. -/
theorem LineBundleClass.isRelativelyAmple_relativeProjTwistingSheafOne_gradedSymmetricAlgebra
    [F.obj.IsFiniteType] :
    (LineBundleClass.mk (((gradedSymmetricAlgebra S).obj F).obj.relativeProjTwistingSheafOne
      (isGeneratedInDegreeOne_gradedSymmetricAlgebra F))).IsRelativelyAmple
      ((gradedSymmetricAlgebra S).obj F).obj.relativeProjToBase :=
  have := isProper_relativeProjToBase_gradedSymmetricAlgebra F
  isRelativelyAmple_relativeProjTwistingSheafOne _ _

/-- **A projective bundle is projective**: for a quasicoherent sheaf `F` of finite type,
`ℙ(F) = Proj_S(Sym F) ⟶ S` is projective. -/
instance isProjective_relativeProjToBase_gradedSymmetricAlgebra [F.obj.IsFiniteType] :
    IsProjective ((gradedSymmetricAlgebra S).obj F).obj.relativeProjToBase :=
  isProjective_relativeProjToBase _ (isGeneratedInDegreeOne_gradedSymmetricAlgebra F)
    (fun _ hU ↦ finiteType_sections_gradedSymmetricAlgebra F hU)
    (fun U _ ↦ finite_sections_gradedSymmetricAlgebra_zero F U)

end ProjectiveBundle

end AlgebraicGeometry

end TauCeti
