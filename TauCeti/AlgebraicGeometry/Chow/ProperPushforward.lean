/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.PrincipalPushforward
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.Lookahead.ChowProperPushforward.Stubs

/-!
# Proper pushforward of rational equivalences

Let `F` be a family witnessing a rational equivalence to zero on `X`: integral closed subschemes
`i_j : W_j ⟶ X` of dimension `n + 1` with nonzero rational functions `r_j`, whose cycle is
`Σ_j (i_j)_* div(r_j)`. For a quasi-compact morphism `f : X ⟶ Y`, the scheme-theoretic images
`f(W_j)` of the members that keep their dimension, with the norms `N_{K(W_j)/K(f(W_j))}(r_j)`,
form a family `RatEquivFamily.map F f` on `Y`. If `f` is proper over a field `k`, the pushforward
of the cycle of `F` is the cycle of `F.map f` plus the pushforwards `(i_j ≫ f)_* div(r_j)` of the
members whose image has smaller dimension
(`Chow.RatEquivFamily.map_cycle_eq_cycle_map_add_finsum`, from Fulton, *Intersection Theory*,
Proposition 1.4(b), as `Chow.map_height_div_eq_map_imageι`).

Fulton's Proposition 1.4(a), that these remaining pushforwards vanish, then makes the pushforward
of the cycle of `F` the cycle of `F.map f` (`Chow.RatEquivFamily.cycle_map_eq_map_cycle`), so that
proper pushforward preserves rational equivalence; Proposition 1.4(a) is not proved here.
-/

public section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace TauCeti.AlgebraicGeometry.Chow

namespace RatEquivFamily

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] {n : ℤ} (F : RatEquivFamily X n)

/-- The pushforward of the `j`-th summand of a family is `(i_j ≫ f)_* div(r_j)`. -/
lemma map_component (f : X ⟶ Y) [QuasiCompact f] (j : F.ι) :
    AlgebraicCycle.map f height height (F.component j) =
      AlgebraicCycle.map (F.i j ≫ f) height height (AlgebraicCycle.div (F.r j)) := by
  rw [F.component_def, AlgebraicCycle.map_height_comp_of_isClosedImmersion]

/-- The pushforwards `(i_j ≫ f)_* div(r_j)` of the members of a family have locally finite
supports. -/
lemma locallyFinite_support_map_comp (f : X ⟶ Y) [QuasiCompact f] :
    LocallyFinite fun j ↦
      (AlgebraicCycle.map (F.i j ≫ f) height height (AlgebraicCycle.div (F.r j))).support := by
  simpa only [F.map_component] using AlgebraicCycle.locallyFinite_support_map f height height
    F.component F.locallyFinite_support_component

/-- The pushforward of the cycle of a family has, at each point, the sum of the coefficients of
the pushforwards `(i_j ≫ f)_* div(r_j)`. -/
lemma map_cycle_apply (f : X ⟶ Y) [QuasiCompact f] (y : Y) :
    AlgebraicCycle.map f height height F.cycle y =
      ∑ᶠ j, AlgebraicCycle.map (F.i j ≫ f) height height (AlgebraicCycle.div (F.r j)) y := by
  have h : F.cycle =
      Function.locallyFinsupp.locallyFiniteSum F.component F.locallyFinite_support_component := by
    ext x
    rw [cycle_apply, Function.locallyFinsupp.locallyFiniteSum_apply]
  rw [h, AlgebraicCycle.map_locallyFiniteSum, Function.locallyFinsupp.locallyFiniteSum_apply]
  exact finsum_congr fun j ↦ by rw [F.map_component]

/-- The members of a family whose image under `f` has the same dimension. -/
def mapIndex (f : X ⟶ Y) : Set F.ι :=
  {j | height (f (F.i j (genericPoint (F.W j)))) = height (genericPoint (F.W j))}

omit [IsLocallyNoetherian X] in
@[simp]
lemma mem_mapIndex (f : X ⟶ Y) {j : F.ι} :
    j ∈ F.mapIndex f ↔ height (f (F.i j (genericPoint (F.W j)))) = height (genericPoint (F.W j)) :=
  Iff.rfl

variable [IsLocallyNoetherian Y]

/-- The image family of a family under a quasi-compact morphism `f`: the scheme-theoretic images
`f(W_j)` of the members `j ∈ F.mapIndex f` that keep their dimension, with the norms
`N_{K(W_j)/K(f(W_j))}(r_j)`. The body is exposed so that its members can be read off. -/
@[expose] noncomputable def map (f : X ⟶ Y) [QuasiCompact f] : RatEquivFamily Y n where
  ι := F.mapIndex f
  W j := (F.i j ≫ f).image
  i j := (F.i j ≫ f).imageι
  genericPoint_mem j := by
    have h := (F.i j ≫ f).imageι.height_apply_eq_height (genericPoint (F.i j ≫ f).image)
    rw [← (F.i j ≫ f).toImage.genericPoint_eq_of_isDominant, ← Scheme.Hom.comp_apply,
      Scheme.Hom.toImage_imageι, Scheme.Hom.comp_apply] at h
    rw [← (F.i j ≫ f).toImage.genericPoint_eq_of_isDominant, mem_pointsOfDimension, ← h,
      (F.mem_mapIndex f).mp j.2]
    exact mem_pointsOfDimension.mp (F.genericPoint_mem j)
  r j := letI := (F.i j ≫ f).toImage.functionFieldMap.hom.toAlgebra
    Units.map (Algebra.norm (F.i j ≫ f).image.functionField (S := (F.W j).functionField)) (F.r j)
  locallyFinite := by
    -- `f(W_j)` is the closure of `f '' W_j`, and only finitely many `W_j` meet the quasi-compact
    -- preimage of an affine open.
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    have hI := F.locallyFinite.finite_nonempty_inter_compact
      (QuasiCompact.isCompact_preimage (f := f) _ U.isOpen hU.isCompact)
    refine ⟨U, U.isOpen.mem_nhds hyU, (hI.preimage Subtype.val_injective.injOn).subset ?_⟩
    rintro j ⟨z, hz, hzU⟩
    have hz : z ∈ Set.range (F.i j ≫ f).imageι := hz
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker] at hz
    obtain ⟨_, hw, w, rfl⟩ := mem_closure_iff.mp hz U U.isOpen hzU
    exact ⟨F.i j w, Set.mem_range_self w, by rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply]⟩

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] in
/-- The rational functions of the image family are the norms. -/
lemma map_r (f : X ⟶ Y) [QuasiCompact f] (j : (F.map f).ι) :
    letI := (F.i j.1 ≫ f).toImage.functionFieldMap.hom.toAlgebra
    (F.map f).r j =
      Units.map (Algebra.norm (F.i j.1 ≫ f).image.functionField (S := (F.W j.1).functionField))
        (F.r j.1) :=
  rfl

variable (k : Type u) [Field k] [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]

/-- For `f` proper over `k`, a member `j ∈ F.mapIndex f` pushes forward to the `j`-th summand of
the image family (Fulton, *Intersection Theory*, Proposition 1.4(b)). -/
lemma map_comp_div_eq_component_map (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (j : (F.map f).ι) :
    AlgebraicCycle.map (F.i j.1 ≫ f) height height (AlgebraicCycle.div (F.r j.1)) =
      (F.map f).component j := by
  -- `W_j` is a scheme over `k` through `X`, and `i_j ≫ f` is a proper morphism over `k`.
  let _ : (F.W j.1).Over (Spec (.of k)) := ⟨F.i j.1 ≫ X ↘ Spec (.of k)⟩
  have : LocallyOfFiniteType (F.W j.1 ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (F.i j.1 ≫ X ↘ Spec (.of k)))
  have : (F.i j.1 ≫ f).IsOver (Spec (.of k)) := ⟨by
    -- The structure morphism of `W_j` is, by the definition above, `i_j` followed by that of `X`.
    change (F.i j.1 ≫ f) ≫ Y ↘ Spec (.of k) = F.i j.1 ≫ X ↘ Spec (.of k)
    rw [Category.assoc, comp_over]⟩
  have hj : height ((F.i j.1 ≫ f) (genericPoint (F.W j.1))) = height (genericPoint (F.W j.1)) := by
    rw [Scheme.Hom.comp_apply, ← F.mem_mapIndex f]
    exact j.2
  rw [map_height_div_eq_map_imageι k (F.i j.1 ≫ f) hj, component_def, map_r]
  -- The members of the image family are the images `(i_j ≫ f).imageι`, by definition.
  rfl

/-- **Pushforward of a rational equivalence.** For `f` proper over `k`, the pushforward of the
cycle of a family is the cycle of its image family plus the pushforwards `(i_j ≫ f)_* div(r_j)`
of the members whose image has smaller dimension. -/
theorem map_cycle_eq_cycle_map_add_finsum (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (y : Y) :
    AlgebraicCycle.map f height height F.cycle y =
      (F.map f).cycle y + ∑ᶠ j ∈ (F.mapIndex f)ᶜ,
        AlgebraicCycle.map (F.i j ≫ f) height height (AlgebraicCycle.div (F.r j)) y := by
  have hfin := (F.locallyFinite_support_map_comp f).point_finite y
  rw [map_cycle_apply, cycle_apply, ← finsum_mem_univ,
    ← finsum_mem_inter_add_sdiff' (F.mapIndex f) (by rw [Set.univ_inter]; exact hfin),
    Set.univ_inter, ← Set.compl_eq_univ_sdiff]
  congr 1
  exact (finsum_set_coe_eq_finsum_mem (F.mapIndex f)).symm.trans <| finsum_congr fun j ↦
    congrArg (fun c : AlgebraicCycle Y ℤ ↦ c y) (F.map_comp_div_eq_component_map k f j)

/-- For `f` proper over `k`, if the members whose image has smaller dimension push forward to
zero (Fulton, *Intersection Theory*, Proposition 1.4(a)), then the pushforward of the cycle of a
family is the cycle of its image family. -/
theorem cycle_map_eq_map_cycle (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (h : ∀ j ∉ F.mapIndex f,
      AlgebraicCycle.map (F.i j ≫ f) height height (AlgebraicCycle.div (F.r j)) = 0) :
    (F.map f).cycle = AlgebraicCycle.map f height height F.cycle := by
  ext y
  rw [F.map_cycle_eq_cycle_map_add_finsum k f y, finsum_mem_eq_zero_of_forall_eq_zero
    fun j hj ↦ by rw [h j hj, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply], add_zero]

end RatEquivFamily

end TauCeti.AlgebraicGeometry.Chow
