/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Noetherian approximation of affine schemes

Every commutative ring `A` is the directed union of its finitely generated `ℤ`-subalgebras
`ℤ[s]`, `s` a finite subset of `A`, and each `ℤ[s]` is of finite presentation over `ℤ` because
`ℤ` is Noetherian. Since `Spec` is a right adjoint, `Spec A` is therefore the cofiltered limit of
the affine schemes `Spec ℤ[s]`, which are of finite presentation over `ℤ`, with affine transition
maps. This is the affine case of absolute Noetherian approximation (Stacks,
Proposition 32.5.4 (01ZA)).

## Main declarations

* `TauCeti.AlgebraicGeometry.finsetAdjoinDiagram`: the diagram `s ↦ ℤ[s]` of finitely generated
  `ℤ`-subalgebras of `A`, indexed by the finite subsets of `A`.
* `TauCeti.AlgebraicGeometry.isColimitFinsetAdjoinCocone`: `A` is the colimit of this diagram.
* `TauCeti.AlgebraicGeometry.Scheme.exists_isLimit_finitePresentation_of_isAffine`: every
  affine scheme is a cofiltered limit, with affine transition maps, of affine schemes of finite
  presentation over `ℤ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

variable (A : Type u) [CommRing A]

/-- The finitely generated `ℤ`-subalgebras `ℤ[s]` of `A`, for `s` a finite subset of `A`, with
the inclusions between them. -/
@[simps obj]
noncomputable def finsetAdjoinDiagram : Finset A ⥤ CommRingCat.{u} where
  obj s := .of (Algebra.adjoin ℤ (s : Set A))
  map {s t} h := CommRingCat.ofHom
    (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.le))).toRingHom

/-- The cocone on `finsetAdjoinDiagram A` with point `A`, given by the inclusions `ℤ[s] → A`. -/
@[simps pt]
noncomputable def finsetAdjoinCocone : Cocone (finsetAdjoinDiagram A) where
  pt := .of A
  ι.app s := CommRingCat.ofHom (Algebra.adjoin ℤ (s : Set A)).val.toRingHom

/-- A ring `A` is the filtered colimit of its finitely generated `ℤ`-subalgebras. -/
noncomputable def isColimitFinsetAdjoinCocone : IsColimit (finsetAdjoinCocone A) := by
  have : ReflectsFilteredColimits (forget CommRingCat.{u}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  refine isColimitOfReflects (forget _) (Types.FilteredColimit.isColimitOf' _
    ((forget CommRingCat.{u}).mapCocone (finsetAdjoinCocone A)) ?_ ?_)
  · intro x
    exact ⟨{x}, ⟨x, Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_singleton_self x))⟩, rfl⟩
  · intro s x y h
    refine ⟨s, 𝟙 s, ?_⟩
    simp only [CategoryTheory.Functor.map_id, types_id_apply]
    exact Subtype.ext h

instance (s : Finset A) : Algebra.FinitePresentation ℤ ((finsetAdjoinDiagram A).obj s) :=
  Algebra.FinitePresentation.of_finiteType.mp
    (Subalgebra.fg_iff_finiteType _ |>.mp (Subalgebra.fg_adjoin_finset s))

/-- The spectrum of a ring of finite presentation over `ℤ` is of finite presentation over the
terminal scheme. -/
lemma locallyOfFinitePresentation_terminal_from_Spec (R : CommRingCat.{u})
    [Algebra.FinitePresentation ℤ R] : LocallyOfFinitePresentation (terminal.from (Spec R)) := by
  let e : ⊤_ Scheme.{u} ≅ Spec (.of (ULift.{u} ℤ)) :=
    terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal
  let g : CommRingCat.of (ULift.{u} ℤ) ⟶ R :=
    CommRingCat.ofHom ((algebraMap ℤ R).comp ULift.ringEquiv.toRingHom)
  have : LocallyOfFinitePresentation (Spec.map g) := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact (RingHom.finitePresentation_algebraMap.mpr inferInstance).comp
      (.of_bijective ULift.ringEquiv.bijective)
  rw [terminal.hom_ext (terminal.from (Spec R)) (Spec.map g ≫ e.inv)]
  infer_instance

/-- Every affine scheme `X` is a cofiltered limit, with affine transition maps, of affine schemes
of finite presentation over `ℤ`. This is the affine case of absolute Noetherian approximation.
Stacks, Proposition 32.5.4 (01ZA), affine case. -/
theorem Scheme.exists_isLimit_finitePresentation_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I) (D : I ⥤ Scheme.{u})
      (π : (Functor.const I).obj X ⟶ D), Nonempty (IsLimit (Cone.mk X π)) ∧
      (∀ ⦃i j : I⦄ (f : i ⟶ j), IsAffineHom (D.map f)) ∧
      ∀ i, IsAffine (D.obj i) ∧ LocallyOfFinitePresentation (terminal.from (D.obj i)) := by
  let A := Γ(X, ⊤)
  have : PreservesLimits Scheme.Spec.{u} := ΓSpec.adjunction.rightAdjoint_preservesLimits
  let c := Scheme.Spec.mapCone (finsetAdjoinCocone A).op
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec (isColimitFinsetAdjoinCocone A).op
  refine ⟨(Finset A)ᵒᵖ, inferInstance, inferInstance, (finsetAdjoinDiagram A).op ⋙ Scheme.Spec,
    (c.extend X.isoSpec.hom).π, ⟨hc.ofIsoLimit (c.extendIso X.isoSpec.symm)⟩,
    fun _ _ _ ↦ ?_, fun s ↦ ⟨?_, ?_⟩⟩
  · dsimp; infer_instance
  · dsimp; infer_instance
  · exact locallyOfFinitePresentation_terminal_from_Spec ((finsetAdjoinDiagram A).obj s.unop)

end TauCeti.AlgebraicGeometry
