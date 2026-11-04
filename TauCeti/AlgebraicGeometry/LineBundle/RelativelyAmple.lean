/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.RelativeProj.Proper
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

* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.of_pow`: if a positive power `aⁿ`
  is relatively ample, then so is `a`.
* `TauCeti.AlgebraicGeometry.LineBundleClass.isRelativelyAmple_one_iff`: the trivial class is
  relatively ample exactly for quasi-affine morphisms; in particular it is relatively ample for
  affine morphisms (`LineBundleClass.isRelativelyAmple_one`).
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.isAmple`: over an affine base, a
  relatively ample class is ample.
* `TauCeti.AlgebraicGeometry.LineBundleClass.isRelativelyAmple_pullback_iff_of_isIso`: relative
  ampleness is invariant under isomorphisms of the source over the base.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.isRelativelyVeryAmple_relativeProjTwistingSheaf`:
  `𝒪(1)` is relatively very ample on the relative `Proj` of an algebra generated in degree one.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.IsRelativelyVeryAmple.pullback`: relative very
  ampleness is preserved by pullback along an immersion.
* `TauCeti.AlgebraicGeometry.IsProjective.exists_isRelativelyVeryAmple`: a projective morphism
  has a relatively very ample line bundle.
* `TauCeti.AlgebraicGeometry.IsProjective.isProper`: a projective morphism is proper.

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

/-- **Relative ampleness over an affine base implies ampleness.** If the base `S` is affine and
`a` is relatively ample for `f : X ⟶ S`, then `a` is ample: `X` is the preimage of `S` itself. -/
theorem IsRelativelyAmple.isAmple [IsAffine S] {a : LineBundleClass X} {f : X ⟶ S}
    (h : a.IsRelativelyAmple f) : a.IsAmple := by
  -- `f ⁻¹ᵁ ⊤` is `⊤` by definition (`Scheme.Hom.preimage_top`).
  have h' : (pullback (⊤ : X.Opens).ι a).IsAmple := h.isAmple_pullback ⊤ (isAffineOpen_top S)
  simpa using h'.pullback_of_isOpenImmersion X.topIso.inv

/-- **Relative ampleness is invariant under isomorphisms over the base.** If `e : X' ⟶ X` is an
isomorphism, then the pullback of `a` along `e` is relatively ample for `e ≫ f` exactly when `a`
is relatively ample for `f`. -/
theorem isRelativelyAmple_pullback_iff_of_isIso {X' : Scheme.{u}} (e : X' ⟶ X) [IsIso e]
    (a : LineBundleClass X) (f : X ⟶ S) :
    (pullback e a).IsRelativelyAmple (e ≫ f) ↔ a.IsRelativelyAmple f := by
  -- Over an open `V` of the base, the inclusion of `(e ≫ f)⁻¹ V` followed by `e` is the
  -- isomorphism `e ∣_ f⁻¹ V` followed by the inclusion of `f⁻¹ V`.
  have hV (V : S.Opens) : (pullback ((e ≫ f) ⁻¹ᵁ V).ι (pullback e a)).IsAmple ↔
      (pullback (f ⁻¹ᵁ V).ι a).IsAmple := by
    -- `(e ≫ f) ⁻¹ᵁ V` is `e ⁻¹ᵁ f ⁻¹ᵁ V` by definition (`Scheme.Hom.comp_preimage`), but the
    -- type of the pulled-back class depends on the open, so the lemma cannot be rewritten with.
    change (pullback (e ⁻¹ᵁ f ⁻¹ᵁ V).ι (pullback e a)).IsAmple ↔ _
    rw [pullback_comp, ← morphismRestrict_ι, ← pullback_comp, isAmple_pullback_iff_of_isIso]
  refine ⟨fun h ↦ ⟨?_, fun V hV' ↦ (hV V).mp (h.isAmple_pullback V hV')⟩,
    fun h ↦ ⟨?_, fun V hV' ↦ (hV V).mpr (h.isAmple_pullback V hV')⟩⟩
  · have := h.quasiCompact
    rw [← IsIso.inv_hom_id_assoc e f]
    infer_instance
  · have := h.quasiCompact
    infer_instance

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

/-- If a positive tensor power `L^{⊗n}` is relatively ample for `f`, then so is `L`. -/
theorem isRelativelyAmple_of_tensorPow {L : InvertibleSheaf X} {f : X ⟶ S} {n : ℕ} (hn : 0 < n)
    (h : (LineBundleClass.mk (L.tensorPow n)).IsRelativelyAmple f) :
    (LineBundleClass.mk L).IsRelativelyAmple f :=
  .of_pow hn (LineBundleClass.mk_tensorPow L n ▸ h)

end InvertibleSheaf

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

/-- **A projective morphism has a relatively very ample line bundle**: the pullback of `𝒪(1)`
along the closed immersion into the relative `Proj`. -/
theorem IsProjective.exists_isRelativelyVeryAmple (f : X ⟶ S) [IsProjective f] :
    ∃ L : InvertibleSheaf X, L.IsRelativelyVeryAmple f := by
  obtain ⟨A, _, hA, -, -, i, hi, rfl⟩ := IsProjective.exists_isClosedImmersion (f := f)
  exact ⟨(InvertibleSheaf.pullback i).obj (A.relativeProjTwistingSheafOne hA),
    A, _, hA, i, inferInstance, rfl, ⟨Iso.refl _⟩⟩

/-- **A projective morphism is proper**: it is a closed immersion followed by the structure
morphism of a relative `Proj` of a graded algebra of finite type with finite degree-zero part. -/
instance IsProjective.isProper (f : X ⟶ S) [IsProjective f] : IsProper f := by
  obtain ⟨A, _, -, h, h₀, i, hi, rfl⟩ := IsProjective.exists_isClosedImmersion (f := f)
  have := CommMon.isProper_relativeProjToBase h h₀
  infer_instance

end AlgebraicGeometry

end TauCeti
