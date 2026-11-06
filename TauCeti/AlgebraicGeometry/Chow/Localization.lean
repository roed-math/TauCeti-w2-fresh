/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import TauCeti.AlgebraicGeometry.Chow.OpenRestriction
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic
import TauCeti.AlgebraicGeometry.Chow.DivisorClass
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Restricting Chow groups to an open subscheme

Let `X` be a scheme locally of finite type over a field `K` and `j : U ⟶ X` an open immersion.
A rational equivalence on `X` restricts to one on `U`: each integral closed subscheme `W` of the
family is replaced by `W ×_X U`, which is integral of the same dimension when it is nonempty, and
each rational function on `W` by its pullback, whose orders of vanishing are those on `W`. Hence
the restriction of cycles `Z_k(X) → Z_k(U)` descends to `CH_k(X) → CH_k(U)`. The descended map is
surjective, and it kills the classes pushed forward from the closed complement of `U`.

Conversely, a rational equivalence on `U` extends to `X`: the closure in `X` of an integral closed
subscheme `W` of `U` (the scheme-theoretic image of `W ⟶ X`) is integral of the same dimension,
with `W` as a dense open subscheme, so a rational function on `W` is one on its closure. Hence a
class restricting to zero on `U` is pushed forward from the complement, which gives the
localisation sequence `CH_k(Z) → CH_k(X) → CH_k(U) → 0`.

The schemes `X` and `U` are locally Noetherian, being locally of finite type over a field; the
statements assume this as instances, since the Chow groups need it to be stated.

## Main definitions and results

All in the namespace `TauCeti.AlgebraicGeometry.Chow`:

* `RatEquivFamily.restrict`: the restriction of a rational-equivalence family to `U`.
* `RatEquivFamily.cycle_restrict`: its cycle is the restriction of the cycle of the family.
* `cyclesRestrict_mem_ratEquiv`: restriction preserves rational equivalence.
* `ChowGroup.restrict`: the restriction `CH_k(X) →+ CH_k(U)`, and `ChowGroup.restrict_surjective`.
* `ChowGroup.restrict_comp_pushforward`: the composite `CH_k(Z) → CH_k(X) → CH_k(U)` vanishes for
  a closed immersion `Z ⟶ X` onto the complement of `U`.
* `RatEquivFamily.cycle_mem_cyclesOfDimension`: the cycle of a rational-equivalence family is a
  `k`-cycle.
* `RatEquivFamily.closure`, `RatEquivFamily.cycleRestrict_cycle_closure`: the closure in `X` of a
  rational-equivalence family on `U`, which restricts to it.
* `ChowGroup.localization_exact`: the localisation sequence is exact at `CH_k(X)`.

In the namespace `TauCeti.AlgebraicGeometry.Scheme.Hom`, about the scheme-theoretic image of a
quasi-compact `f`: `range_imageι` (it is the closure of the image), `isIntegral_image`, and
`isIso_functionFieldMap_of_isOpenImmersion`.

## References

* [Stacks, Section 42.19](https://stacks.math.columbia.edu/tag/02RV)
* Fulton, *Intersection Theory*, Proposition 1.8
-/

@[expose] public section

open CategoryTheory Limits Order Topology AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
variable (K : Type u) [Field K] [X.Over (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]

namespace RatEquivFamily

variable {k : ℤ} (F : RatEquivFamily X k)

/-- The members of a family meeting the open subscheme `U`. -/
def RestrictIndex : Type u :=
  {a : F.ι // (Set.range (F.i a) ∩ Set.range j).Nonempty}

instance (a : F.RestrictIndex j) : Nonempty ((pullback (F.i a.1) j : Scheme.{u}) : Type u) := by
  obtain ⟨_, ⟨w, rfl⟩, ⟨x, hx⟩⟩ := a.2
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback w x hx.symm
  exact ⟨z⟩

instance (a : F.RestrictIndex j) : IsIntegral (pullback (F.i a.1) j) :=
  isIntegral_of_isOpenImmersion (pullback.fst (F.i a.1) j)

instance (a : F.RestrictIndex j) : IsDominant (pullback.fst (F.i a.1) j) :=
  ⟨(pullback.fst (F.i a.1) j).isOpenEmbedding.isOpen_range.dense
    (Set.range_nonempty _)⟩

variable [IsLocallyNoetherian X] [IsLocallyNoetherian U]

/-- The restriction of a rational-equivalence family on `X` to the open subscheme `U`: the members
`W` meeting `U` are replaced by `W ×_X U` and their rational functions by the pullbacks. -/
noncomputable def restrict : RatEquivFamily U k where
  ι := F.RestrictIndex j
  W a := pullback (F.i a.1) j
  i a := pullback.snd (F.i a.1) j
  genericPoint_mem a := by
    let : (F.W a.1).Over (Spec (.of K)) := ⟨F.i a.1 ≫ X ↘ Spec (.of K)⟩
    have : LocallyOfFiniteType (F.W a.1 ↘ Spec (.of K)) :=
      inferInstanceAs (LocallyOfFiniteType (F.i a.1 ≫ X ↘ Spec (.of K)))
    rw [← apply_mem_pointsOfDimension_iff (pullback.fst (F.i a.1) j) K,
      genericPoint_eq_of_isOpenImmersion]
    exact F.genericPoint_mem a.1
  r a := Units.map (pullback.fst (F.i a.1) j).functionFieldMap.hom.toMonoidHom (F.r a.1)
  locallyFinite := by
    have h := (F.locallyFinite.comp_injective (Subtype.val_injective (p := fun a ↦
      (Set.range (F.i a) ∩ Set.range j).Nonempty))).preimage_continuous j.continuous
    exact h.subset fun a ↦ (Scheme.Pullback.range_snd (F.i a.1) j).le

/-- The summands of the restricted family are the restrictions of the summands of the family. -/
lemma component_restrict (a : F.RestrictIndex j) (x : U) :
    (F.restrict j K).component a x = F.component a.1 (j x) := by
  by_cases hx : x ∈ Set.range (pullback.snd (F.i a.1) j)
  · obtain ⟨w, rfl⟩ := hx
    refine ((F.restrict j K).component_apply a w).trans ?_
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, F.component_apply]
    exact Scheme.ord_functionFieldMap (pullback.fst (F.i a.1) j) _ w
  · rw [(F.restrict j K).component_apply_eq_zero_of_notMem_range a hx,
      F.component_apply_eq_zero_of_notMem_range]
    rwa [Scheme.Pullback.range_snd] at hx

/-- The cycle of the restricted family is the restriction of the cycle of the family. -/
lemma cycle_restrict : (F.restrict j K).cycle = cycleRestrict j F.cycle := by
  classical
  ext x
  rw [cycle_apply, cycleRestrict_apply, cycle_apply]
  refine (finsum_congr fun a ↦ F.component_restrict j K a x).trans <|
    (finsum_subtype_eq_finsum_cond (fun a ↦ (Set.range (F.i a) ∩ Set.range j).Nonempty)
    (f := fun a ↦ F.component a (j x))).trans (finsum_congr fun a ↦ ?_)
  rw [finsum_eq_if]
  split_ifs with ha
  · rfl
  · exact (F.component_apply_eq_zero_of_notMem_range a fun hx ↦ ha ⟨j x, hx, x, rfl⟩).symm

end RatEquivFamily

variable [IsLocallyNoetherian X] [IsLocallyNoetherian U]

/-- Restriction to an open subscheme preserves rational equivalence. -/
theorem cyclesRestrict_mem_ratEquiv {k : ℤ} {α : cyclesOfDimension X k} (hα : α ∈ RatEquiv X k) :
    cyclesRestrict j K k α ∈ RatEquiv U k := by
  obtain ⟨F, hF⟩ := mem_ratEquiv_iff.mp hα
  refine mem_ratEquiv_iff.mpr ⟨F.restrict j K, ?_⟩
  rw [F.cycle_restrict j K, hF]
  rfl

namespace ChowGroup

include j K in
/-- The restriction `CH_k(X) →+ CH_k(U)` of Chow groups along an open immersion `j : U ⟶ X`, for `X`
locally of finite type over a field `K`: the flat pullback along `j`. -/
noncomputable def restrict (k : ℤ) : ChowGroup X k →+ ChowGroup U k :=
  lift (cycleClass.comp (cyclesRestrict j K k)) fun _ hα ↦ by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, cycleClass_eq_zero_iff]
    exact cyclesRestrict_mem_ratEquiv j K hα

variable {j K} in
@[simp]
lemma restrict_cycleClass {k : ℤ} (α : cyclesOfDimension X k) :
    restrict j K k (cycleClass α) = cycleClass (cyclesRestrict j K k α) :=
  lift_cycleClass _ _ α

/-- The restriction of Chow groups to an open subscheme is surjective. -/
theorem restrict_surjective (k : ℤ) : Function.Surjective (restrict j K k) := by
  intro c
  obtain ⟨β, rfl⟩ := cycleClass_surjective c
  obtain ⟨α, rfl⟩ := cyclesRestrict_surjective j K k β
  exact ⟨cycleClass α, restrict_cycleClass α⟩

/-- Classes pushed forward from the closed complement of `U` restrict to zero on `U`: the composite
`CH_k(Z) → CH_k(X) → CH_k(U)` vanishes. -/
theorem restrict_comp_pushforward {Z : Scheme.{u}} [IsLocallyNoetherian Z] (i : Z ⟶ X)
    [IsClosedImmersion i] (h : Set.range i = (Set.range j)ᶜ) (k : ℤ) :
    (restrict j K k).comp (pushforward i) = 0 := by
  ext β
  have hβ : cyclesPushforward i β ∈ (cyclesRestrict j K k).ker := by
    rw [ker_cyclesRestrict_eq_range_cyclesPushforward j K i h]
    exact ⟨β, rfl⟩
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, pushforward_cycleClass,
    restrict_cycleClass, AddMonoidHom.mem_ker.mp hβ, map_zero, AddMonoidHom.zero_comp,
    AddMonoidHom.zero_apply]

end ChowGroup

section Closure

/-! ### Closures of integral subschemes of `U`

An integral closed subscheme `W` of `U` has a closure in `X`: the scheme-theoretic image of
`W ⟶ U ⟶ X`. It is integral, contains `W` as a dense open subscheme, and so has the function
field and the dimension of `W`. Taking closures turns a rational-equivalence family on `U` into
one on `X` restricting to it, which proves the localisation sequence. -/

/-- The scheme-theoretic image of a quasi-compact morphism is the closure of the topological
image. -/
lemma _root_.TauCeti.AlgebraicGeometry.Scheme.Hom.range_imageι {W Y : Scheme.{u}} (f : W ⟶ Y)
    [QuasiCompact f] : Set.range f.imageι = closure (Set.range f) := by
  have h : Set.range f = f.imageι '' Set.range f.toImage := by
    rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, f.toImage_imageι]
  rw [h, f.imageι.isClosedEmbedding.closure_image_eq, f.toImage.denseRange.closure_range,
    Set.image_univ]

/-- The scheme-theoretic image of a quasi-compact morphism from an integral scheme is integral. -/
instance _root_.TauCeti.AlgebraicGeometry.Scheme.Hom.isIntegral_image {W Y : Scheme.{u}}
    [IsIntegral W] (f : W ⟶ Y) [QuasiCompact f] : IsIntegral f.image := by
  have : IrreducibleSpace f.image := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← f.toImage.denseRange.closure_range,
      ← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ W).image _
      f.toImage.continuous.continuousOn).closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Pulling back rational functions along a dominant open immersion of irreducible schemes is an
isomorphism of function fields. -/
instance _root_.TauCeti.AlgebraicGeometry.Scheme.Hom.isIso_functionFieldMap_of_isOpenImmersion
    {W Y : Scheme.{u}} [IrreducibleSpace W] [IrreducibleSpace Y] (f : W ⟶ Y) [IsOpenImmersion f]
    [IsDominant f] : IsIso f.functionFieldMap := by
  have key {x y : Y} (h : x = y) : IsIso (Y.presheaf.stalkSpecializes (specializes_of_eq h)) := by
    subst h
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    infer_instance
  have := key f.genericPoint_eq_of_isDominant
  have e : Y.presheaf.stalkSpecializes (specializes_of_eq f.genericPoint_eq_of_isDominant) ≫
      f.stalkMap (genericPoint W) = f.functionFieldMap := by
    rw [Scheme.Hom.eq_functionFieldMap_iff, Spec.map_comp_assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
  rw [← e]
  infer_instance

include K in
/-- The cycle `Σ_j (i j)_* div (r j)` of a rational-equivalence family is a `k`-cycle. -/
lemma RatEquivFamily.cycle_mem_cyclesOfDimension {k : ℤ} (F : RatEquivFamily X k) :
    F.cycle ∈ cyclesOfDimension X k := by
  refine mem_cyclesOfDimension_iff.mpr fun x hx ↦ ?_
  obtain ⟨a, ha⟩ : ∃ a, F.component a x ≠ 0 := by
    by_contra! h
    exact hx ((F.cycle_apply x).trans (finsum_eq_zero_of_forall_eq_zero h))
  obtain ⟨w, rfl⟩ : x ∈ Set.range (F.i a) := by
    by_contra hxa
    exact ha (F.component_apply_eq_zero_of_notMem_range a hxa)
  rw [F.component_apply] at ha
  let : (F.W a).Over (Spec (.of K)) := ⟨F.i a ≫ X ↘ Spec (.of K)⟩
  have : LocallyOfFiniteType (F.W a ↘ Spec (.of K)) :=
    inferInstanceAs (LocallyOfFiniteType (F.i a ≫ X ↘ Spec (.of K)))
  obtain ⟨n, hn, hnk⟩ := mem_pointsOfDimension.mp (F.genericPoint_mem a)
  -- `W` has dimension `n`, the height of its generic point, and `w` has codimension one in `W`.
  have hdim : topologicalKrullDim (F.W a) = n := by
    rw [← coheight_add_height_eq_topologicalKrullDim K (genericPoint (F.W a)), hn,
      Order.coheight_eq_zero.mpr
        (TauCeti.AlgebraicGeometry.Scheme.isMax_iff_eq_genericPoint.mpr rfl)]
    simp
  have hw : Order.coheight w = 1 := by
    by_contra hw
    exact ha (Scheme.ord_eq_zero_of_coheight_neq_one hw _)
  obtain ⟨m, hm, hmk⟩ := mem_pointsOfDimension.mp
    ((coheight_eq_one_iff_mem_pointsOfDimension K hdim).mp hw)
  exact mem_pointsOfDimension.mpr ⟨m, Scheme.Hom.height_apply_eq_height (F.i a) w ▸ hm, by omega⟩

namespace RatEquivFamily

variable {k : ℤ} (F : RatEquivFamily U k)

/-- The closure in `X` of a rational-equivalence family on the open subscheme `U`: each member
`W` is replaced by its scheme-theoretic image in `X`, and each rational function by the rational
function with the same pullback to the dense open subscheme `W`. -/
noncomputable def closure : RatEquivFamily X k where
  ι := F.ι
  W a := (F.i a ≫ j).image
  i a := (F.i a ≫ j).imageι
  genericPoint_mem a := by
    let : (F.i a ≫ j).image.Over (Spec (.of K)) := ⟨(F.i a ≫ j).imageι ≫ X ↘ Spec (.of K)⟩
    have : LocallyOfFiniteType ((F.i a ≫ j).image ↘ Spec (.of K)) :=
      inferInstanceAs (LocallyOfFiniteType ((F.i a ≫ j).imageι ≫ X ↘ Spec (.of K)))
    rw [← genericPoint_eq_of_isOpenImmersion (F.i a ≫ j).toImage,
      apply_mem_pointsOfDimension_iff _ K]
    exact F.genericPoint_mem a
  r a := Units.map (inv (F.i a ≫ j).toImage.functionFieldMap).hom.toMonoidHom (F.r a)
  locallyFinite x := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    have hc : IsCompact (j ⁻¹' (V : Set X)) :=
      QuasiCompact.isCompact_preimage _ V.isOpen hV.isCompact
    refine ⟨V, V.isOpen.mem_nhds hxV,
      (F.locallyFinite.finite_nonempty_inter_compact hc).subset fun a ha ↦ ?_⟩
    change (Set.range (F.i a ≫ j).imageι ∩ V).Nonempty at ha
    rw [Scheme.Hom.range_imageι, closure_inter_open_nonempty_iff V.isOpen] at ha
    obtain ⟨_, ⟨w, rfl⟩, hw⟩ := ha
    exact ⟨F.i a w, ⟨w, rfl⟩, hw⟩

/-- The closure of a family restricts on `U` to the family. -/
lemma cycleRestrict_cycle_closure : cycleRestrict j (F.closure j K).cycle = F.cycle := by
  ext x
  rw [cycleRestrict_apply, cycle_apply, cycle_apply]
  refine finsum_congr fun (a : F.ι) ↦ ?_
  by_cases hx : x ∈ Set.range (F.i a)
  · obtain ⟨w, rfl⟩ := hx
    have hw : j (F.i a w) = (F.i a ≫ j).imageι ((F.i a ≫ j).toImage w) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]
    have : IsLocallyNoetherian (F.i a ≫ j).image :=
      LocallyOfFiniteType.isLocallyNoetherian (F.i a ≫ j).imageι
    rw [hw, F.component_apply]
    refine ((F.closure j K).component_apply a _).trans <|
      (Scheme.ord_functionFieldMap (F.i a ≫ j).toImage _ w).symm.trans ?_
    congr 1
    change (F.i a ≫ j).toImage.functionFieldMap.hom
      ((inv (F.i a ≫ j).toImage.functionFieldMap).hom (F.r a)) = _
    rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
  · rw [F.component_apply_eq_zero_of_notMem_range a hx]
    refine (F.closure j K).component_apply_eq_zero_of_notMem_range a fun hcl ↦ hx ?_
    change j x ∈ Set.range (F.i a ≫ j).imageι at hcl
    rw [Scheme.Hom.range_imageι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp] at hcl
    rwa [← (F.i a).isClosedEmbedding.isClosed_range.closure_eq,
      j.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image]

end RatEquivFamily

end Closure

namespace ChowGroup

/-- **The localisation sequence** (Fulton, Proposition 1.8): for a closed immersion `i : Z ⟶ X`
onto the complement of `U`, the sequence `CH_k(Z) → CH_k(X) → CH_k(U) → 0` is exact. Exactness at
`CH_k(U)` is `ChowGroup.restrict_surjective`. -/
theorem localization_exact {Z : Scheme.{u}} [IsLocallyNoetherian Z] (i : Z ⟶ X)
    [IsClosedImmersion i] (h : Set.range i = (Set.range j)ᶜ) (k : ℤ) :
    Function.Exact (pushforward i) (restrict j K k) := by
  refine fun c ↦ ⟨fun hc ↦ ?_, ?_⟩
  · obtain ⟨α, rfl⟩ := cycleClass_surjective c
    rw [restrict_cycleClass, cycleClass_eq_zero_iff] at hc
    obtain ⟨F, hF⟩ := mem_ratEquiv_iff.mp hc
    -- The closure of a family exhibiting `α|U ∼ 0` is a rational equivalence `β ∼ 0` on `X`
    -- with `β|U = α|U`, so `α - β` is supported on `Z`.
    let β : cyclesOfDimension X k :=
      ⟨(F.closure j K).cycle, (F.closure j K).cycle_mem_cyclesOfDimension K⟩
    have hβ : β ∈ RatEquiv X k := mem_ratEquiv_iff.mpr ⟨F.closure j K, rfl⟩
    have hker : α - β ∈ (cyclesRestrict j K k).ker := by
      rw [AddMonoidHom.mem_ker, map_sub, sub_eq_zero]
      exact Subtype.ext (hF.symm.trans (F.cycleRestrict_cycle_closure j K).symm)
    rw [ker_cyclesRestrict_eq_range_cyclesPushforward j K i h] at hker
    obtain ⟨γ, hγ⟩ := hker
    refine ⟨cycleClass γ, ?_⟩
    rw [pushforward_cycleClass, hγ, map_sub, cycleClass_eq_zero_iff.mpr hβ, sub_zero]
  · rintro ⟨c, rfl⟩
    rw [← AddMonoidHom.comp_apply, restrict_comp_pushforward j K i h, AddMonoidHom.zero_apply]

end ChowGroup

end TauCeti.AlgebraicGeometry.Chow
