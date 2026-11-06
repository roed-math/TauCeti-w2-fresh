/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.ClosedImmersion
public import TauCeti.AlgebraicGeometry.Scheme.KrullDimension
import TauCeti.Topology.KrullDimension.Basic

/-!
# Restricting cycles to an open subscheme

Let `X` be a scheme locally of finite type over a field `K` and `j : U ⟶ X` an open immersion.
The closure of a point `u` of `U` is a nonempty open part of the closure of `j u`, so the two
closures have the same dimension; hence `j` preserves the dimension of points. Composing with `j`
therefore sends `k`-cycles on `X` to `k`-cycles on `U`. This is the flat pullback `j^*` along the
open immersion `j`, which is flat of relative dimension `0`, and the restriction map
`Z_k(X) → Z_k(U)` of the localisation sequence.

Conversely a cycle on `U` extends by zero to a cycle on `X`. Its support is locally finite because
every point of `X` has a Noetherian affine neighbourhood `V`, and `V ∩ U` is quasi-compact. So the
restriction is surjective, and its kernel consists of the cycles supported on the closed complement
of `U`: for a closed immersion `i : Z ⟶ X` onto that complement, `Z_k(Z) → Z_k(X) → Z_k(U) → 0` is
exact.

## Main definitions and results

All in the namespace `TauCeti.AlgebraicGeometry.Chow`:

* `height_apply_of_isOpenImmersion`: an open immersion into a scheme locally of finite type over a
  field preserves the height of points.
* `cyclesRestrict`: the restriction `Z_k(X) →+ Z_k(U)`.
* `cyclesExtend`: the extension by zero `Z_k(U) →+ Z_k(X)`.
* `cyclesRestrict_surjective`: the restriction of `k`-cycles is surjective.
* `ker_cyclesRestrict_eq_range_cyclesPushforward`: the kernel of the restriction is the image of
  the pushforward along a closed immersion onto the complement.

## References

* [Stacks, Section 42.14](https://stacks.math.columbia.edu/tag/02RA) and
  [Section 42.19](https://stacks.math.columbia.edu/tag/02RV)
* Fulton, *Intersection Theory*, §1.7 and Proposition 1.8
-/
@[expose] public section

open CategoryTheory Order Topology AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- An open immersion into a scheme locally of finite type over a field preserves the height of
points, that is, the dimension of their closures. -/
theorem height_apply_of_isOpenImmersion (K : Type u) [Field K] [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] (x : U) : height (j x) = height x := by
  have hpre : j ⁻¹' closure {j x} = closure {x} := by
    rw [j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous,
      ← Set.image_singleton, j.isOpenEmbedding.injective.preimage_image]
  have h : (height (j x) : WithBot ℕ∞) = height x := by
    rw [height_eq_topologicalKrullDim_closure_singleton,
      height_eq_topologicalKrullDim_closure_singleton, ← hpre,
      j.isOpenEmbedding.isEmbedding.topologicalKrullDim_preimage]
    exact (topologicalKrullDim_inter_eq_of_locallyOfFiniteType (X ↘ Spec (.of K))
      isIrreducible_singleton.closure isClosed_closure j.isOpenEmbedding.isOpen_range
      ⟨j x, subset_closure rfl, x, rfl⟩).symm
  exact_mod_cast h

/-- An open immersion into a scheme locally of finite type over a field preserves the dimension
of points. -/
theorem apply_mem_pointsOfDimension_iff (K : Type u) [Field K] [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] {k : ℤ} {x : U} :
    j x ∈ pointsOfDimension X k ↔ x ∈ pointsOfDimension U k := by
  simp [height_apply_of_isOpenImmersion j K]

/-- The pullback of an algebraic cycle along an open immersion: the coefficient at `x` is the
coefficient at `j x`. -/
noncomputable def cycleRestrict (α : AlgebraicCycle X ℤ) : AlgebraicCycle U ℤ where
  toFun x := α (j x)
  supportWithinDomain' _ _ := Set.mem_univ _
  supportLocallyFiniteWithinDomain' x _ := by
    obtain ⟨t, ht, hfin⟩ := α.supportLocallyFiniteWithinDomain' (j x) (Set.mem_univ _)
    refine ⟨j ⁻¹' t, j.continuous.continuousAt.preimage_mem_nhds ht, ?_⟩
    exact hfin.preimage j.isOpenEmbedding.injective.injOn

@[simp]
lemma cycleRestrict_apply (α : AlgebraicCycle X ℤ) (x : U) : cycleRestrict j α x = α (j x) :=
  rfl

/-- The restriction `Z_k(X) →+ Z_k(U)` of `k`-cycles along an open immersion `j : U ⟶ X`, for `X`
locally of finite type over a field `K`. -/
noncomputable def cyclesRestrict (K : Type u) [Field K] [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] (k : ℤ) :
    cyclesOfDimension X k →+ cyclesOfDimension U k where
  toFun α := ⟨cycleRestrict j α, mem_cyclesOfDimension_iff.mpr fun x hx ↦
    (apply_mem_pointsOfDimension_iff j K).mp
      (mem_cyclesOfDimension_iff.mp α.2 (show α.1 (j x) ≠ 0 from hx))⟩
  map_zero' := rfl
  map_add' _ _ := rfl

variable {j} in
@[simp]
lemma cyclesRestrict_apply {K : Type u} [Field K] [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] {k : ℤ} (α : cyclesOfDimension X k) (x : U) :
    (cyclesRestrict j K k α).1 x = α.1 (j x) :=
  rfl

/-- The extension by zero of an algebraic cycle on an open subscheme `U` of a locally Noetherian
scheme `X`: the coefficient at `j x` is the coefficient at `x`, and the coefficients off `U` are
zero. Its support is locally finite since every point of `X` has a Noetherian neighbourhood `V`,
whose open part `V ∩ U` is quasi-compact. -/
noncomputable def cycleExtend [IsLocallyNoetherian X] (β : AlgebraicCycle U ℤ) :
    AlgebraicCycle X ℤ where
  toFun := Function.extend j β 0
  supportWithinDomain' _ _ := Set.mem_univ _
  supportLocallyFiniteWithinDomain' x _ := by
    obtain ⟨V, hV, hxV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
    have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have := noetherianSpace_of_isAffineOpen V hV
    have hc : IsCompact ((V : Set X) ∩ Set.range j) := by
      have := (TopologicalSpace.NoetherianSpace.isCompact (V.ι ⁻¹' Set.range j)).image
        V.ι.continuous
      rwa [Set.image_preimage_eq_range_inter, Scheme.Opens.range_ι] at this
    have hc' : IsCompact (j ⁻¹' V) := by
      have := (j.isOpenEmbedding.isInducing.isCompact_preimage_iff Set.inter_subset_right).mpr hc
      rwa [Set.preimage_inter, Set.preimage_range, Set.inter_univ] at this
    refine ⟨V, V.isOpen.mem_nhds hxV, ((β.locallyFiniteSupport.finite_inter_support_of_isCompact
      hc').image j).subset ?_⟩
    rintro y ⟨hyV, hy⟩
    by_cases hyj : y ∈ Set.range j
    · obtain ⟨z, rfl⟩ := hyj
      rw [Function.mem_support, j.isOpenEmbedding.injective.extend_apply] at hy
      exact ⟨z, ⟨hyV, hy⟩, rfl⟩
    · exact absurd (Function.extend_apply' _ _ _ fun ⟨z, hz⟩ ↦ hyj ⟨z, hz⟩) hy

@[simp]
lemma cycleExtend_apply [IsLocallyNoetherian X] (β : AlgebraicCycle U ℤ) (x : U) :
    cycleExtend j β (j x) = β x :=
  j.isOpenEmbedding.injective.extend_apply _ _ _

lemma cycleExtend_apply_of_notMem_range [IsLocallyNoetherian X] (β : AlgebraicCycle U ℤ) {x : X}
    (hx : x ∉ Set.range j) : cycleExtend j β x = 0 :=
  Function.extend_apply' _ _ _ fun ⟨z, hz⟩ ↦ hx ⟨z, hz⟩

/-- Restriction undoes extension by zero. -/
@[simp]
lemma cycleRestrict_cycleExtend [IsLocallyNoetherian X] (β : AlgebraicCycle U ℤ) :
    cycleRestrict j (cycleExtend j β) = β := by
  ext x
  simp

/-- The extension by zero `Z_k(U) →+ Z_k(X)` of `k`-cycles along an open immersion `j : U ⟶ X`, for
`X` locally of finite type over a field `K`. -/
noncomputable def cyclesExtend (K : Type u) [Field K] [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] (k : ℤ) :
    cyclesOfDimension U k →+ cyclesOfDimension X k :=
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  { toFun β := ⟨cycleExtend j β, mem_cyclesOfDimension_iff.mpr fun x hx ↦ by
      by_cases hxj : x ∈ Set.range j
      · obtain ⟨y, rfl⟩ := hxj
        refine (apply_mem_pointsOfDimension_iff j K).mpr (mem_cyclesOfDimension_iff.mp β.2 ?_)
        rwa [Function.mem_support, cycleExtend_apply] at hx
      · exact absurd (cycleExtend_apply_of_notMem_range j β.1 hxj) hx⟩
    map_zero' := Subtype.ext <| Function.locallyFinsuppWithin.ext fun x ↦ by
      by_cases hxj : x ∈ Set.range j
      · obtain ⟨y, rfl⟩ := hxj
        simp
      · simp [cycleExtend_apply_of_notMem_range j _ hxj]
    map_add' β γ := Subtype.ext <| Function.locallyFinsuppWithin.ext fun x ↦ by
      by_cases hxj : x ∈ Set.range j
      · obtain ⟨y, rfl⟩ := hxj
        simp
      · simp [cycleExtend_apply_of_notMem_range j _ hxj] }

variable (K : Type u) [Field K] [X.Over (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]

/-- Restriction undoes extension by zero on `k`-cycles. -/
@[simp]
lemma cyclesRestrict_cyclesExtend {k : ℤ} (β : cyclesOfDimension U k) :
    cyclesRestrict j K k (cyclesExtend j K k β) = β :=
  Subtype.ext <| Function.locallyFinsuppWithin.ext fun x ↦ by
    have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
    exact cycleExtend_apply j β.1 x

/-- Every `k`-cycle on an open subscheme is the restriction of a `k`-cycle on the ambient scheme:
the map `Z_k(X) → Z_k(U)` of the localisation sequence is surjective. -/
theorem cyclesRestrict_surjective (k : ℤ) : Function.Surjective (cyclesRestrict j K k) :=
  fun β ↦ ⟨cyclesExtend j K k β, cyclesRestrict_cyclesExtend j K β⟩

/-- A `k`-cycle restricts to zero on `U` exactly when it is supported off `U`. -/
lemma cyclesRestrict_eq_zero_iff {k : ℤ} {α : cyclesOfDimension X k} :
    cyclesRestrict j K k α = 0 ↔ (α : AlgebraicCycle X ℤ).support ⊆ (Set.range j)ᶜ := by
  refine ⟨fun h ↦ ?_, fun h ↦ Subtype.ext <| Function.locallyFinsuppWithin.ext fun x ↦ ?_⟩
  · rintro _ hx ⟨y, rfl⟩
    exact hx congr($h.1 y)
  · by_contra hx
    exact h hx ⟨x, rfl⟩

/-- **Localisation sequence for cycles.** If `i : Z ⟶ X` is a closed immersion onto the complement
of the open immersion `j : U ⟶ X`, then the cycles of `X` restricting to zero on `U` are exactly
the pushforwards of cycles on `Z`: the sequence `Z_k(Z) → Z_k(X) → Z_k(U) → 0` is exact. -/
theorem ker_cyclesRestrict_eq_range_cyclesPushforward {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (h : Set.range i = (Set.range j)ᶜ) (k : ℤ) :
    (cyclesRestrict j K k).ker = (cyclesPushforward i (k := k)).range := by
  ext α
  rw [AddMonoidHom.mem_ker, cyclesRestrict_eq_zero_iff, mem_range_cyclesPushforward_iff, h]

end TauCeti.AlgebraicGeometry.Chow
