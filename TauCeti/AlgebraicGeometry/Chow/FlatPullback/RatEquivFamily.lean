/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.FlatPullback.RatEquiv
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.AlgebraicGeometry.Scheme.ConstantOnClosed

/-!
# The pullback of a rational-equivalence family

For `f : X ⟶ Y` and a rational-equivalence family `F` on `Y`, with members `W_j ⟶ Y`, the
pulled-back family on `X` has one member for each irreducible component of each `X ×_Y W_j`
(Stacks, Lemma 42.20.1). This file constructs that family and computes its summands.

## Main definitions

* `TauCeti.AlgebraicGeometry.Chow.RatEquivFamily.flatPullback`: for `f` flat of pure relative
  dimension `n`, the family on `X` whose members are the reduced irreducible components `W'` of the
  schemes `X ×_Y W_j`, with the pullbacks of the `r_j` raised to the multiplicity of `W'`.

## Main results

* `TauCeti.AlgebraicGeometry.Chow.locallyFinite_closure_pullback_fst`: for `X` locally Noetherian,
  the closures in `X` of the generic points of the irreducible components of the schemes
  `X ×_Y W_j` form a locally finite family;
* `TauCeti.AlgebraicGeometry.Chow.RatEquivFamily.component_flatPullback_apply`: the summand of a
  member `W'` at a point of `W'` is its multiplicity times the order of the pullback of `r_j`
  (`TauCeti.AlgebraicGeometry.Scheme.ord_pow`);
* `TauCeti.AlgebraicGeometry.Chow.RatEquivFamily.cycle_flatPullback_apply`: the cycle of the
  pulled-back family is the iterated sum over the members `W_j` and then over the components of
  `X ×_Y W_j` (`TauCeti.finsum_fiberwise` along `Sigma.fst`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace TauCeti.AlgebraicGeometry.Scheme

/-- The order of a power of a nonzero rational function is the corresponding multiple of its
order. -/
theorem ord_pow {Z : Scheme.{u}} [IsIntegral Z] [IsLocallyNoetherian Z]
    {r : Z.functionField} (hr : r ≠ 0) (m : ℕ) {z : Z} : Z.ord (r ^ m) z = m * Z.ord r z := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Z.ord_mul (pow_ne_zero m hr) hr, ih]
    push_cast
    ring

end TauCeti.AlgebraicGeometry.Scheme

namespace TauCeti.AlgebraicGeometry.Chow

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open Limits in
/-- **The components of the pullback of a family are locally finite.** Let `X` be locally
Noetherian and `F` a rational-equivalence family on `Y`, with members `W_j`. The closures in `X` of
the generic points of the irreducible components of the schemes `X ×_Y W_j` form a locally finite
family: a Noetherian affine open `V` of `X` has quasi-compact image in `Y`, which meets finitely
many `W_j`, and `V` contains only finitely many generic points of each closed set `f⁻¹(W_j)`
(`finite_maximal_mem_inter`). -/
theorem locallyFinite_closure_pullback_fst [IsLocallyNoetherian X] {k : ℤ}
    (F : RatEquivFamily Y k) :
    LocallyFinite fun η : Σ j : F.ι,
        {η : ↥(pullback f (F.i j)) // ∀ η' : ↥(pullback f (F.i j)), η' ⤳ η → η ⤳ η'} ↦
      closure {pullback.fst f (F.i η.1) η.2.1} := by
  intro x
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : NoetherianSpace (V : Set X) := noetherianSpace_of_isAffineOpen V hV
  have hJ := F.locallyFinite.finite_nonempty_inter_compact (hV.isCompact.image f.continuous)
  -- Over each member `W_j` meeting `f '' V`, only finitely many generic points of `f⁻¹(W_j)`.
  have ht : ∀ j : F.ι, Set.Finite {η : {η : ↥(pullback f (F.i j)) //
      ∀ η' : ↥(pullback f (F.i j)), η' ⤳ η → η ⤳ η'} | pullback.fst f (F.i j) η.1 ∈
        {x | x ∈ (V : Set X) ∧ x ∈ f ⁻¹' Set.range (F.i j) ∧
          ∀ x' ∈ f ⁻¹' Set.range (F.i j), x' ⤳ x → x' = x}} := fun j ↦
    (finite_maximal_mem_inter ((F.i j).isClosedEmbedding.isClosed_range.preimage f.continuous)
      V.isOpen).preimage
      ((pullback.fst f (F.i j)).isClosedEmbedding.injective.comp Subtype.val_injective).injOn
  refine ⟨V, V.isOpen.mem_nhds hxV, (hJ.sigma fun j _ ↦ ht j).subset ?_⟩
  rintro ⟨j, η, hη⟩ ⟨z, hzη, hzV⟩
  have hfst : pullback.fst f (F.i j) η ∈ (V : Set X) :=
    (specializes_iff_mem_closure.mpr hzη).mem_open V.isOpen hzV
  have hcond : f (pullback.fst f (F.i j) η) = F.i j (pullback.snd f (F.i j) η) := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  refine ⟨⟨F.i j (pullback.snd f (F.i j) η), ⟨_, rfl⟩, _, hfst, hcond⟩,
    hfst, ⟨_, hcond.symm⟩, fun x' hx' hx'η ↦ ?_⟩
  obtain ⟨η', rfl⟩ : x' ∈ Set.range (pullback.fst f (F.i j)) := by
    rwa [Scheme.Pullback.range_fst]
  have h : η' ⤳ η :=
    (pullback.fst f (F.i j)).isClosedEmbedding.isInducing.specializes_iff.mp hx'η
  exact (hx'η.antisymm ((hη η' h).map (pullback.fst f (F.i j)).continuous)).eq

open Limits in
/-- The member of the pulled-back family for a generic point `η` of `X ×_Y W` lies in the closure
of the image of `η` in `X` (`Scheme.Hom.range_subschemeι_comp`). -/
theorem range_subschemeι_comp_pullback_fst_subset {W : Scheme.{u}} (i : W ⟶ Y)
    (η : ↥(pullback f i)) :
    Set.range ((Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩).subschemeι ≫
      pullback.fst f i) ⊆ closure {pullback.fst f i η} := by
  rw [Scheme.Hom.range_subschemeι_comp, Closeds.coe_mk, ← Set.image_singleton]
  exact image_closure_subset_closure_image (pullback.fst f i).continuous

section Family

variable (K : Type u) [Field K] [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
  [f.IsOver (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K))] [Flat f] (n : ℕ) [PureRelativeDimension n f]
  [IsLocallyNoetherian X] {k : ℤ}

open Limits in
/-- **The flat pullback of a rational-equivalence family** (Stacks, Lemma 42.20.1). For `f` flat
of pure relative dimension `n` between schemes locally of finite type over `K`, and a family `F`
on `Y` with members `W_j` and functions `r_j`, the family on `X` has one member for each generic
point `η` of an irreducible component of `X ×_Y W_j`: the reduced closure `W'` of `η`, of
dimension `k + 1 + n` (`height_eq_height_genericPoint_add_of_pullback`), embedded into `X`
through `X ×_Y W_j`, with the function `φ(r_j) ^ m`, where `φ` pulls rational functions back along
the dominant `W' ⟶ W_j` (`isDominant_subschemeι_pullback_snd`) and `m` is the fibre length of `f`
at the image of `η` (the multiplicity of `W'` in `f⁻¹(W_j)`). -/
noncomputable def RatEquivFamily.flatPullback (F : RatEquivFamily Y k) :
    RatEquivFamily X (k + n) where
  ι := Σ j : F.ι,
    {η : ↥(pullback f (F.i j)) // ∀ η' : ↥(pullback f (F.i j)), η' ⤳ η → η ⤳ η'}
  W η := (Scheme.IdealSheafData.vanishingIdeal ⟨closure {η.2.1}, isClosed_closure⟩).subscheme
  i η := (Scheme.IdealSheafData.vanishingIdeal ⟨closure {η.2.1}, isClosed_closure⟩).subschemeι ≫
    pullback.fst f (F.i η.1)
  genericPoint_mem η := by
    obtain ⟨m, hm, hmk⟩ := mem_pointsOfDimension.mp (F.genericPoint_mem η.1)
    refine mem_pointsOfDimension.mpr ⟨m + n, ?_, by push_cast; omega⟩
    rw [← Scheme.Hom.height_apply_eq_height
        (Scheme.IdealSheafData.vanishingIdeal ⟨closure {η.2.1}, isClosed_closure⟩).subschemeι,
      Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure_singleton,
      height_eq_height_genericPoint_add_of_pullback f K (n := n) (F.i η.1) η.2.2, hm]
    norm_cast
  r η :=
    have := isDominant_subschemeι_pullback_snd f (F.i η.1) η.2.2
    Units.map ((Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {η.2.1}, isClosed_closure⟩).subschemeι ≫
        pullback.snd f (F.i η.1)).functionFieldMap.hom.toMonoidHom (F.r η.1) ^
      (fiberLength f (pullback.fst f (F.i η.1) η.2.1)).toNat
  locallyFinite := (locallyFinite_closure_pullback_fst f F).subset fun η ↦
    range_subschemeι_comp_pullback_fst_subset f (F.i η.1) η.2.1

open Limits in
/-- At a point `w` of the member `W'` of the pulled-back family for `η`, its summand is `m` times
the order at `w` of the pullback `φ(r_j)` of `r_j`, with `m` the fibre length of `f` at the image of
`η` (`Scheme.ord_pow`). -/
theorem RatEquivFamily.component_flatPullback_apply (F : RatEquivFamily Y k)
    (η : (F.flatPullback f K n).ι)
    [IsDominant ((Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {η.2.1}, isClosed_closure⟩).subschemeι ≫ pullback.snd f (F.i η.1))]
    (w : (F.flatPullback f K n).W η) :
    (F.flatPullback f K n).component η ((F.flatPullback f K n).i η w) =
      (fiberLength f (pullback.fst f (F.i η.1) η.2.1)).toNat *
        ((F.flatPullback f K n).W η).ord (((Scheme.IdealSheafData.vanishingIdeal
          ⟨closure {η.2.1}, isClosed_closure⟩).subschemeι ≫
            pullback.snd f (F.i η.1)).functionFieldMap.hom
              (F.r η.1 : (F.W η.1).functionField)) w := by
  rw [RatEquivFamily.component_apply]
  exact (Scheme.ord_pow (Units.ne_zero _) _).trans rfl

open Limits in
/-- The summand of the pulled-back family for `η` vanishes off the closure of the image of `η` in
`X`. -/
theorem RatEquivFamily.component_flatPullback_apply_eq_zero (F : RatEquivFamily Y k)
    (η : (F.flatPullback f K n).ι) {x : X} (hx : x ∉ closure {pullback.fst f (F.i η.1) η.2.1}) :
    (F.flatPullback f K n).component η x = 0 :=
  RatEquivFamily.component_apply_eq_zero_of_notMem_range _ _ fun h ↦
    hx (range_subschemeι_comp_pullback_fst_subset f (F.i η.1) η.2.1 h)

open Limits in
/-- The summand of the pulled-back family for a component of `X ×_Y W_j` vanishes at the points of
`X` not over `W_j`. -/
theorem RatEquivFamily.component_flatPullback_apply_eq_zero_of_notMem_range
    (F : RatEquivFamily Y k) (η : (F.flatPullback f K n).ι) {x : X}
    (hx : f x ∉ Set.range (F.i η.1)) : (F.flatPullback f K n).component η x = 0 := by
  refine RatEquivFamily.component_flatPullback_apply_eq_zero f K n F η fun h ↦ hx ?_
  have hη : pullback.fst f (F.i η.1) η.2.1 ∈ f ⁻¹' Set.range (F.i η.1) :=
    ⟨pullback.snd f (F.i η.1) η.2.1, by
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩
  exact closure_minimal (Set.singleton_subset_iff.mpr hη)
    ((F.i η.1).isClosedEmbedding.isClosed_range.preimage f.continuous) h

open Limits in
/-- The cycle of the pulled-back family, at a point `x` of `X`, is the iterated sum over the members
`W_j` of `F` and then over the irreducible components of `X ×_Y W_j` of the summands at `x`. -/
theorem RatEquivFamily.cycle_flatPullback_apply (F : RatEquivFamily Y k) (x : X) :
    (F.flatPullback f K n).cycle x =
      ∑ᶠ (j : F.ι) (η : {η : ↥(pullback f (F.i j)) //
        ∀ η' : ↥(pullback f (F.i j)), η' ⤳ η → η ⤳ η'}),
          (F.flatPullback f K n).component ⟨j, η⟩ x := by
  rw [RatEquivFamily.cycle_apply]
  refine (finsum_fiberwise (α := (F.flatPullback f K n).ι) Sigma.fst _
    ((F.flatPullback f K n).locallyFinite_support_component.point_finite x)).symm.trans
      (finsum_congr fun j ↦ ?_)
  exact (finsum_comp_equiv (Equiv.sigmaSubtype j).symm).symm

end Family

end TauCeti.AlgebraicGeometry.Chow
