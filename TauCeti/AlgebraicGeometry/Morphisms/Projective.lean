/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import TauCeti.AlgebraicGeometry.LineBundle.RelativelyAmple.Comp
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample
public import TauCeti.AlgebraicGeometry.RelativeProj.Proper
public import TauCeti.AlgebraicGeometry.RelativeProj.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf

/-!
# Relatively very ample line bundles and projective morphisms

Let `f : X ⟶ S` be a morphism of schemes. A line bundle `L` on `X` is *relatively very ample* for
`f` if there are a graded quasi-coherent `𝒪_S`-algebra `A`, generated in degree one, and an
immersion `i : X ⟶ Proj_S(A)` over `S` with `i^* 𝒪(1) ≅ L`. The morphism `f` is *projective* if
it factors as a closed immersion into such a relative `Proj`, with `A` of finite type and `A₀`
finite over `𝒪_S`, followed by its structure morphism.

Since `A₁` generates `A` and the degree-zero parts of the homogeneous localizations of `A` only
see the positive part of `A`, `Proj_S(A)` is a closed subscheme of `ℙ(A₁) = Proj_S(Sym A₁)` with
`𝒪(1)` pulling back to `𝒪(1)`; conversely `Sym ℰ` satisfies all the conditions above when `ℰ` is
quasi-coherent (and of finite type, for projectivity). So these are the notions of the Stacks
Project defined through `ℙ(ℰ)`.

## Main definitions

* `TauCeti.AlgebraicGeometry.InvertibleSheaf.IsRelativelyVeryAmple L f`: `L` is relatively very
  ample for `f`.
* `TauCeti.AlgebraicGeometry.IsProjective f`: `f` is projective.

## Main results

* `TauCeti.AlgebraicGeometry.InvertibleSheaf.isRelativelyVeryAmple_relativeProjTwistingSheaf`:
  `𝒪(1)` is relatively very ample on the relative `Proj` of an algebra generated in degree one.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.IsRelativelyVeryAmple.pullback`: relative very
  ampleness is preserved by pullback along an immersion.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.IsRelativelyVeryAmple.isRelativelyAmple`: a
  relatively very ample line bundle for a quasi-compact morphism is relatively ample. In
  particular `𝒪(1)` is relatively ample on the relative `Proj` of an algebra generated in degree
  one whose structure morphism is quasi-compact
  (`LineBundleClass.isRelativelyAmple_relativeProjTwistingSheafOne`).
* `TauCeti.AlgebraicGeometry.IsProjective.exists_isRelativelyVeryAmple_isRelativelyAmple`: a
  projective morphism has a line bundle that is relatively very ample and relatively ample.
* `TauCeti.AlgebraicGeometry.IsProjective.exists_isRelativelyAmple_comp`: over a quasi-compact
  base, a composite of projective morphisms has a relatively ample line bundle.
* `TauCeti.AlgebraicGeometry.IsProjective.isProper`: a projective morphism is proper.
* `TauCeti.AlgebraicGeometry.isProjective_relativeProjToBase_gradedSymmetricAlgebra`: the
  projective bundle `ℙ(F) = Proj_S(Sym F)` of a quasicoherent sheaf `F` of finite type is
  projective, and `𝒪(1)` on it is relatively ample
  (`LineBundleClass.isRelativelyAmple_relativeProjTwistingSheafOne_gradedSymmetricAlgebra`).
* `TauCeti.AlgebraicGeometry.isProjective_toSpecCoeff_comp_fromSpec`: over an affine scheme `S`,
  `Proj (Sym Γ(F, S)) ⟶ Spec Γ(S, S) ≅ S` is projective for `F` quasicoherent of finite type.

Closed immersions, in particular isomorphisms, are projective
(`TauCeti.AlgebraicGeometry.isProjective_of_isClosedImmersion`); this is proved in
`TauCeti.AlgebraicGeometry.Blowup.Projective`, through the blowup along the unit ideal sheaf.
A scheme projective over a ring `R` in the sense of `AlgebraicGeometry.Scheme.IsProjectiveOver` is
projective over `Spec R` (`AlgebraicGeometry.Scheme.IsProjectiveOver.isProjective`, in
`TauCeti.AlgebraicGeometry.Morphisms.ProjectiveOver`).

## References

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


/-- **A relatively very ample line bundle is relatively ample for a quasi-compact morphism.** If
`L` is relatively very ample for a quasi-compact `f : X ⟶ S`, then `L` is relatively ample for `f`.
Let `i : X ⟶ Proj_S(A)` be an immersion over `S` with `i^* 𝒪(1) ≅ L`. Over an affine open `V` of
`S`, the relative `Proj` is the chart `Proj (⨁ n, Γ(Aₙ, V))`, on which `𝒪(1)` restricts to the
twisting sheaf `𝒪(1)`. The restriction of `i` to the quasi-compact `f⁻¹ V` is an immersion into
this chart, and `𝒪(1)` pulls back to an ample line bundle along it. -/
theorem InvertibleSheaf.IsRelativelyVeryAmple.isRelativelyAmple {L : InvertibleSheaf X}
    {f : X ⟶ S} (hL : L.IsRelativelyVeryAmple f) [QuasiCompact f] :
    (LineBundleClass.mk L).IsRelativelyAmple f where
  quasiCompact := inferInstance
  isAmple_pullback V hV := by
    obtain ⟨A, _, hA, i, hi, rfl, ⟨e⟩⟩ := hL
    let W := A.relativeProjToBase ⁻¹ᵁ V
    have hLi : LineBundleClass.mk L =
        LineBundleClass.pullback i (LineBundleClass.mk (A.relativeProjTwistingSheafOne hA)) := by
      rw [LineBundleClass.pullback_mk]
      exact LineBundleClass.mk_eq_mk_iff.mpr ⟨e.symm⟩
    -- `(i ≫ π) ⁻¹ᵁ V` is `i ⁻¹ᵁ W` by definition (`Scheme.Hom.comp_preimage`), but the type of
    -- the pulled-back class depends on the open, so the lemma cannot be rewritten with.
    rw [hLi]
    change (LineBundleClass.pullback (i ⁻¹ᵁ W).ι (LineBundleClass.pullback i
      (LineBundleClass.mk (A.relativeProjTwistingSheafOne hA)))).IsAmple
    -- The inclusion of `i ⁻¹ᵁ W` followed by `i` is `i ∣_ W` followed by the inclusion of `W`.
    rw [LineBundleClass.pullback_comp, ← morphismRestrict_ι, ← LineBundleClass.pullback_comp]
    let U : S.AffineZariskiSite := ⟨V, hV⟩
    let c := A.relativeProjCover.f U
    -- The chart over `V` is the preimage of `V`.
    have hrange : Set.range c = Set.range W.ι := by
      rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι]
      exact congrArg SetLike.coe (A.relativeProjToBase_preimage U).symm
    let e' := IsOpenImmersion.isoOfRangeEq c _ hrange
    have hW : W.ι = e'.inv ≫ c := by
      rw [← IsOpenImmersion.isoOfRangeEq_hom_fac c W.ι hrange, Iso.inv_hom_id_assoc]
    rw [hW, ← LineBundleClass.pullback_comp, LineBundleClass.pullback_mk,
      LineBundleClass.pullback_comp]
    -- The degree-one standard opens cover the chart.
    have hcover : ⨆ g : A.gradedSectionsGrading V 1,
        Proj.basicOpen (A.gradedSectionsGrading V) (g : ⨁ n, Γ(A.X n, V)) = ⊤ :=
      Proj.iSup_basicOpen_eq_top' _ _ (fun g ↦ ⟨1, g.2⟩)
        (by simpa using A.isGeneratedInDegreeOne_iff.mp hA V hV)
    -- On the chart, the pullback of `𝒪(1)` is the twisting sheaf `𝒪(1)`.
    have hiso : (Scheme.Modules.pullback c).obj (A.relativeProjTwistingSheaf 1) ≅
        Proj.twistingSheaf (A.gradedSectionsGrading V) 1 :=
      ((Scheme.Modules.restrictFunctorIsoPullback c).app _).symm ≪≫
        A.restrictRelativeProjTwistingSheafIso 1 U
    rw [show LineBundleClass.mk ((InvertibleSheaf.pullback c).obj _) = LineBundleClass.mk
        ⟨_, Proj.isInvertible_twistingSheaf_of_iSup_eq_top _ (fun g ↦ g.2) hcover 1⟩ from
      LineBundleClass.mk_eq_mk_iff.mpr ⟨eqToIso (InvertibleSheaf.pullback_obj_obj _ _) ≪≫ hiso⟩]
    -- The preimage of the affine open `V` under the quasi-compact `f` is quasi-compact.
    have : CompactSpace (i ⁻¹ᵁ W) := isCompact_iff_compactSpace.mp
      (QuasiCompact.isCompact_preimage (f := i ≫ A.relativeProjToBase) _ V.isOpen hV.isCompact)
    -- The instance is supplied by hand: at the type `_ ⟶ Proj _` of the lemma, instance search
    -- does not see through the chart `A.relativeProjCover.X U` to find it.
    have hj : IsImmersion ((i ∣_ W) ≫ e'.inv) := inferInstance
    exact @Proj.isAmple_pullback_twistingSheaf_one _ _ _ _ _ _ _ _ _ (fun g ↦ g.2) hcover _ _
      ((i ∣_ W) ≫ e'.inv) hj

/-- **`𝒪(1)` is relatively ample on a quasi-compact relative `Proj`.** If `A` is generated in degree
one and the structure morphism `Proj_S(A) ⟶ S` is quasi-compact, then `𝒪(1)` is relatively ample
for it, being relatively very ample. -/
theorem LineBundleClass.isRelativelyAmple_relativeProjTwistingSheafOne
    (A : CommMon (GradedObject ℕ S.Modules)) [∀ n, (A.X n).IsQuasicoherent]
    (hA : A.IsGeneratedInDegreeOne) [QuasiCompact A.relativeProjToBase] :
    (LineBundleClass.mk (A.relativeProjTwistingSheafOne hA)).IsRelativelyAmple
      A.relativeProjToBase :=
  (InvertibleSheaf.isRelativelyVeryAmple_relativeProjTwistingSheaf A hA).isRelativelyAmple

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

/-- **A composite of projective morphisms has a relatively ample line bundle** over a
quasi-compact base: if `L` and `M` are relatively ample for the projective morphisms `f` and `g`
(`IsProjective.exists_isRelativelyVeryAmple_isRelativelyAmple`), then `L ⊗ f^* M^{⊗n}` is
relatively ample for `f ≫ g` once `n` is large
(`LineBundleClass.IsRelativelyAmple.exists_isRelativelyAmple_comp_mul_pullback_pow`). -/
theorem IsProjective.exists_isRelativelyAmple_comp [CompactSpace S] (f : X ⟶ Y) (g : Y ⟶ S)
    [IsProjective f] [IsProjective g] : ∃ a : LineBundleClass X, a.IsRelativelyAmple (f ≫ g) := by
  obtain ⟨L, -, hL⟩ := IsProjective.exists_isRelativelyVeryAmple_isRelativelyAmple f
  obtain ⟨M, -, hM⟩ := IsProjective.exists_isRelativelyVeryAmple_isRelativelyAmple g
  obtain ⟨N, hN⟩ := hL.exists_isRelativelyAmple_comp_mul_pullback_pow hM
  exact ⟨_, hN N le_rfl⟩

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

/-- **Over an affine base, the `Proj` of a symmetric algebra is projective**: for `S` affine and a
quasicoherent sheaf `F` of finite type, `Proj (Sym Γ(F, S)) ⟶ Spec Γ(S, S) ≅ S` is projective. It
is the projective bundle `ℙ(F) ⟶ S`, through `relativeProjGradedSymmetricAlgebraIso`. -/
instance isProjective_toSpecCoeff_comp_fromSpec [IsAffine S] [F.obj.IsFiniteType] :
    IsProjective (Proj.toSpecCoeff (TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(S, ⊤)
        (PresheafOfModulesOfCommRing.obj (R := S.presheaf) F.obj.val (Opposite.op ⊤))) ≫
      (isAffineOpen_top S).fromSpec) := by
  rw [← relativeProjGradedSymmetricAlgebraIso_inv_relativeProjToBase]
  infer_instance

end ProjectiveBundle

end AlgebraicGeometry

end TauCeti
