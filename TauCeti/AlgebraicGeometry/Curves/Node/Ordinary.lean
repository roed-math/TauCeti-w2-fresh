/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Descent
public import TauCeti.Lookahead.PrestableModelOfNodalSpecialFiber.Stubs
import TauCeti.AlgebraicGeometry.Curves.Node.Locality
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Base
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.PureRelativeDimension

/-!
# Curves with only ordinary nodes are nodal

Let `X` be a scheme over a field `F`. A point `x` of `X` is an **ordinary node or smooth point**
(`TauCeti.AlgebraicGeometry.IsOrdinaryNodeOrSmoothAt`) if either `X` is smooth of relative
dimension one over `F` on an open neighbourhood of `x`, or `x` lies in the image of an étale
neighbourhood `U ⟶ X` that admits an étale morphism over `F` to the split node chart
`Spec F[u, v] ⧸ (uv)`. This is the étale-local form of an ordinary double point.

A curve all of whose points are ordinary nodes or smooth points is at worst nodal of relative
dimension one, since the node chart and smooth curves are nodal and nodality is étale local on
the source. Because nodality descends along field extensions, it suffices that this holds after
some field extension `F ⟶ L`, for instance after passing to an algebraic closure.

## Main definitions

* `TauCeti.AlgebraicGeometry.IsOrdinaryNodeOrSmoothAt`: a point is an ordinary node or a smooth
  point of a scheme over a field.

## Main results

* `TauCeti.AlgebraicGeometry.isOrdinaryNodeOrSmoothAt_of_mem_smoothLocus`: points of the smooth
  locus of a syntomic curve are smooth points.
* `TauCeti.AlgebraicGeometry.AffineAtWorstNodalOfRelativeDimensionOne.comp_spec_map_of_etale`:
  nodality over an affine base is preserved by an étale change of base ring.
* `TauCeti.AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne.of_isOrdinaryNodeOrSmoothAt`: a
  scheme over a field whose points are all ordinary nodes or smooth points is at worst nodal.
* `AtWorstNodalOfRelativeDimensionOne.of_baseChange_isOrdinaryNodeOrSmoothAt`: the same
  conclusion when this holds after a field extension.
* `AtWorstNodalOfRelativeDimensionOne.of_forall_exists_isSeparable`: the same conclusion when,
  at each point, this holds after a finite separable extension depending on the point.
* `AtWorstNodalOfRelativeDimensionOne.of_forall_notMem_smoothLocus_exists_isSeparable`: for a
  syntomic curve, it suffices to ask this at the points outside the smooth locus.

## References

* [Stacks Project, Section 53.19, Tag 0C46](https://stacks.math.columbia.edu/tag/0C46): nodes.
* [Stacks Project, Section 53.20, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58): families
  of nodal curves.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {F : Type u} [Field F] {X : Scheme.{u}}

/-- A point `x` of a scheme `X` over a field `F` is an **ordinary node or a smooth point** if
either `X` is smooth of relative dimension one over `F` near `x`, or some étale neighbourhood of
`x` is étale over the split node chart `Spec F[u, v] ⧸ (uv)` compatibly with the maps to
`Spec F`. -/
def IsOrdinaryNodeOrSmoothAt (f : X ⟶ Spec (.of F)) (x : X) : Prop :=
  (∃ V : X.Opens, x ∈ V ∧ SmoothOfRelativeDimension 1 (V.ι ≫ f)) ∨
    ∃ (U : Scheme.{u}) (e : U ⟶ X) (c : U ⟶ Spec (.of (NodeAlgebra F 0))),
      Etale e ∧ Etale c ∧ x ∈ Set.range e ∧
        c ≫ Spec.map (CommRingCat.ofHom (algebraMap F (NodeAlgebra F 0))) = e ≫ f

/-- Every point of the split node chart `Spec F[u, v] ⧸ (uv)` is an ordinary node or a smooth
point. -/
theorem isOrdinaryNodeOrSmoothAt_nodeAlgebra (x : Spec (.of (NodeAlgebra F 0))) :
    IsOrdinaryNodeOrSmoothAt (Spec.map (CommRingCat.ofHom (algebraMap F (NodeAlgebra F 0)))) x :=
  .inr ⟨_, 𝟙 _, 𝟙 _, inferInstance, inferInstance, ⟨x, rfl⟩, by simp⟩

/-- A point in the smooth locus of a syntomic curve over a field is a smooth point, hence an
ordinary node or a smooth point. This is the half of the converse of the nodal criterion that
needs no field extension. -/
theorem isOrdinaryNodeOrSmoothAt_of_mem_smoothLocus (f : X ⟶ Spec (.of F))
    [SyntomicOfRelativeDimension 1 f] {x : X} (hx : x ∈ f.smoothLocus) :
    IsOrdinaryNodeOrSmoothAt f x := by
  have : PureRelativeDimension 1 f := .of_syntomicOfRelativeDimension f
  exact .inl ⟨f.smoothLocus, hx, inferInstance⟩

/-- After any field extension `F ⟶ L`, a point of the base change lying over a point of the
smooth locus is a smooth point, hence an ordinary node or a smooth point. -/
theorem isOrdinaryNodeOrSmoothAt_pullback_fst_of_mem_smoothLocus (L : Type u) [Field L]
    [Algebra F L] (f : X ⟶ Spec (.of F)) [SyntomicOfRelativeDimension 1 f]
    {y : ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap F L))) f)}
    (hy : pullback.snd _ f y ∈ f.smoothLocus) :
    IsOrdinaryNodeOrSmoothAt (pullback.fst _ f) y := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap F L))
  have h₁ : (pullbackSymmetry g f).hom y ∈ (pullback.snd f g).smoothLocus := by
    refine Scheme.Hom.preimage_smoothLocus_le_smoothLocus_pullback_snd f g ?_
    rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst]
    exact hy
  have h₂ : y ∈ ((pullbackSymmetry g f).hom ≫ pullback.snd f g).smoothLocus := by
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    exact h₁
  have h₃ : y ∈ (pullback.fst g f).smoothLocus := by
    convert h₂ using 2
    exact (pullbackSymmetry_hom_comp_snd g f).symm
  exact isOrdinaryNodeOrSmoothAt_of_mem_smoothLocus _ h₃

/-- Composing with an étale change of affine base `Spec S ⟶ Spec R` preserves the nodal-curve
criterion: syntomicity of relative dimension one is preserved, and the singular subscheme relative
to `R` is the one relative to `S`, since `Ω[X⁄R] = Ω[X⁄S]`. -/
theorem AffineAtWorstNodalOfRelativeDimensionOne.comp_spec_map_of_etale {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S] {f : X ⟶ Spec (.of S)}
    (h : AffineAtWorstNodalOfRelativeDimensionOne f) :
    AffineAtWorstNodalOfRelativeDimensionOne
      (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let : X.Over (Spec (.of S)) := ⟨f⟩
  let : X.Over (Spec (.of R)) := ⟨f ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))⟩
  have : SyntomicOfRelativeDimension 1 f := h.syntomic
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of S)) := h.syntomic
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    simpa [RingHom.etale_algebraMap] using ‹Algebra.Etale R S›
  -- An étale morphism is syntomic of relative dimension zero, and dimensions add.
  have hs : SyntomicOfRelativeDimension 1 (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    add_zero 1 ▸ inferInstanceAs (SyntomicOfRelativeDimension (1 + 0) _)
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := hs
  refine AffineAtWorstNodalOfRelativeDimensionOne.mk hs ?_
  have : Unramified ((X.singularLocus S).subschemeι ≫ f) := h.unramified_singularLocus
  change Unramified ((X.singularLocus R).subschemeι ≫ f ≫ Spec.map _)
  rw [Scheme.singularLocus_eq_of_formallyUnramified_base (R := R) (S := S) rfl,
    ← Category.assoc]
  infer_instance

/-- An ordinary node or smooth point has an étale neighbourhood that is at worst nodal of
relative dimension one over the base field. -/
theorem IsOrdinaryNodeOrSmoothAt.exists_etale {f : X ⟶ Spec (.of F)} {x : X}
    (h : IsOrdinaryNodeOrSmoothAt f x) :
    ∃ (U : Scheme.{u}) (e : U ⟶ X), Etale e ∧ x ∈ Set.range e ∧
      AtWorstNodalOfRelativeDimensionOne (e ≫ f) := by
  rcases h with ⟨V, hxV, hV⟩ | ⟨U, e, c, he, hc, hxe, hce⟩
  · exact ⟨V, V.ι, inferInstance, by simpa using hxV,
      AtWorstNodalOfRelativeDimensionOne.of_smooth _⟩
  · refine ⟨U, e, he, hxe, ?_⟩
    rw [← hce, atWorstNodalOfRelativeDimensionOne_iff_of_isAffine _ (Iso.refl _)]
    simpa using (NodeAlgebra.affineAtWorstNodalOfRelativeDimensionOne (0 : F)).comp_of_etale c

/-- A scheme over a field all of whose points are ordinary nodes or smooth points is at worst
nodal of relative dimension one. -/
theorem AtWorstNodalOfRelativeDimensionOne.of_isOrdinaryNodeOrSmoothAt (f : X ⟶ Spec (.of F))
    (h : ∀ x, IsOrdinaryNodeOrSmoothAt f x) : AtWorstNodalOfRelativeDimensionOne f := by
  choose U e he hx hU using fun x ↦ (h x).exists_etale
  exact AtWorstNodalOfRelativeDimensionOne.of_etale_cover f e (fun x ↦ ⟨x, hx x⟩) hU

/-- A scheme over a field `F` is at worst nodal of relative dimension one if, after some field
extension `F ⟶ L`, all points of its base change are ordinary nodes or smooth points. For
instance `L` may be an algebraic closure of `F`. -/
theorem AtWorstNodalOfRelativeDimensionOne.of_baseChange_isOrdinaryNodeOrSmoothAt
    (L : Type u) [Field L] [Algebra F L] (f : X ⟶ Spec (.of F))
    (h : ∀ x, IsOrdinaryNodeOrSmoothAt
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap F L))) f) x) :
    AtWorstNodalOfRelativeDimensionOne f := by
  have hL : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map (CommRingCat.ofHom (algebraMap F L))) := by
    obtain ⟨hfl, hs⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap F L))).mpr
      (by simpa using RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
    exact ⟨⟨hs, hfl⟩, inferInstance⟩
  exact MorphismProperty.of_pullback_fst_of_descendsAlong hL
    (AtWorstNodalOfRelativeDimensionOne.of_isOrdinaryNodeOrSmoothAt _ h)

/-- **The criterion with finite separable residue extensions.** A scheme over a field `F` is at
worst nodal of relative dimension one if each point `x` has, after some finite separable
extension `F ⟶ L` depending on `x`, a point above it in the base change that is an ordinary node or
a smooth point. At a smooth point one may take `L = F`; at a singular point `L` splits the two
branches. -/
theorem AtWorstNodalOfRelativeDimensionOne.of_forall_exists_isSeparable (f : X ⟶ Spec (.of F))
    (h : ∀ x, ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : FiniteDimensional F L)
      (_ : Algebra.IsSeparable F L)
      (y : ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap F L))) f)),
      pullback.snd _ f y = x ∧ IsOrdinaryNodeOrSmoothAt (pullback.fst _ f) y) :
    AtWorstNodalOfRelativeDimensionOne f := by
  choose L _ _ _ _ y hy hL using h
  choose U e he hx hU using fun x ↦ (hL x).exists_etale
  have : ∀ x, Algebra.Etale F (L x) := fun x ↦ ⟨Algebra.FormallyEtale.of_isSeparable F (L x),
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  have : ∀ x, Etale (Spec.map (CommRingCat.ofHom (algebraMap F (L x)))) := fun x ↦ by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    simpa [RingHom.etale_algebraMap] using this x
  refine AtWorstNodalOfRelativeDimensionOne.of_etale_cover f (fun x ↦ e x ≫ pullback.snd _ f)
    (fun x ↦ ⟨x, ?_⟩) fun x ↦ ?_
  · obtain ⟨u, hu⟩ := hx x
    exact ⟨u, by simp [hu, hy]⟩
  · have := hU x
    rw [atWorstNodalOfRelativeDimensionOne_iff_of_isAffine _ (Iso.refl _),
      Iso.refl_hom, Category.comp_id] at this
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      atWorstNodalOfRelativeDimensionOne_iff_of_isAffine _ (Iso.refl _), Iso.refl_hom,
      Category.comp_id]
    exact this.comp_spec_map_of_etale (R := F)

/-- **The criterion with finite separable residue extensions at singular points.** A syntomic
curve over a field `F` is at worst nodal if each point outside its smooth locus has, after some
finite separable extension `F ⟶ L` depending on the point, a point above it in the base change
that is an ordinary node or a smooth point. -/
theorem AtWorstNodalOfRelativeDimensionOne.of_forall_notMem_smoothLocus_exists_isSeparable
    (f : X ⟶ Spec (.of F)) [SyntomicOfRelativeDimension 1 f]
    (h : ∀ x ∉ f.smoothLocus, ∃ (L : Type u) (_ : Field L) (_ : Algebra F L)
      (_ : FiniteDimensional F L) (_ : Algebra.IsSeparable F L)
      (y : ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap F L))) f)),
      pullback.snd _ f y = x ∧ IsOrdinaryNodeOrSmoothAt (pullback.fst _ f) y) :
    AtWorstNodalOfRelativeDimensionOne f := by
  refine AtWorstNodalOfRelativeDimensionOne.of_forall_exists_isSeparable f fun x ↦ ?_
  by_cases hx : x ∈ f.smoothLocus
  · have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap F F))) :=
      ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap F F))).mpr
        (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2
    obtain ⟨y, hy⟩ := (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap F F))) f).surjective x
    exact ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, y, hy,
      isOrdinaryNodeOrSmoothAt_pullback_fst_of_mem_smoothLocus F f (hy ▸ hx)⟩
  · exact h x hx

end TauCeti.AlgebraicGeometry
