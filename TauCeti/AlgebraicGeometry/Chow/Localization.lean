/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.OpenRestriction
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Restricting Chow groups to an open subscheme

Let `X` be a scheme locally of finite type over a field `K` and `j : U ⟶ X` an open immersion.
A rational equivalence on `X` restricts to one on `U`: each integral closed subscheme `W` of the
family is replaced by `W ×_X U`, which is integral of the same dimension when it is nonempty, and
each rational function on `W` by its pullback, whose orders of vanishing are those on `W`. Hence
the restriction of cycles `Z_k(X) → Z_k(U)` descends to `CH_k(X) → CH_k(U)`. The descended map is
surjective, and it kills the classes pushed forward from the closed complement of `U`.

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

end TauCeti.AlgebraicGeometry.Chow
