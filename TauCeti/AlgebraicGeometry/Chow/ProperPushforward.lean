/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.ClosedImmersion
public import TauCeti.AlgebraicGeometry.Chow.PrincipalPushforward
import TauCeti.AlgebraicGeometry.Chow.PrincipalVanishing
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.Lookahead.ChowProperPushforward.Stubs

/-!
# Proper pushforward of Chow groups

Let `k` be a field and `f : X ⟶ Y` a proper morphism over `k` of schemes locally of finite type
over `k`. Mathlib's pushforward of cycles with residue-degree weights,
`f_*[V] = [K(V) : K(f(V))] [f(V)]` when `dim f(V) = dim V` and `0` otherwise (`Chow.cyclesMap`),
preserves rational equivalence (Fulton, *Intersection Theory*, Theorem 1.4), so it descends to
the proper pushforward `f_* : CH_n(X) →+ CH_n(Y)` of Chow groups
(`Chow.ChowGroup.properPushforward`), with `(g ∘ f)_* = g_* ∘ f_*`. For `X` proper over `k`, the
degree of zero-cycles descends to `deg : CH_0(X) →+ ℤ` (`Chow.ChowGroup.degree`), and
`deg ∘ f_* = deg`.

Without properness, pushforward does not respect rational equivalence: on the affine line over
`k`, the class of the origin is rationally equivalent to zero but has degree one.

Let `F` be a family witnessing a rational equivalence to zero on `X`: integral closed subschemes
`i_j : W_j ⟶ X` of dimension `n + 1` with nonzero rational functions `r_j`, whose cycle is
`Σ_j (i_j)_* div(r_j)`. For a quasi-compact morphism `f : X ⟶ Y`, the scheme-theoretic images
`f(W_j)` of the members that keep their dimension, with the norms `N_{K(W_j)/K(f(W_j))}(r_j)`,
form a family `RatEquivFamily.map F f` on `Y`. If `f` is proper over a field `k`, the pushforward
of the cycle of `F` is the cycle of `F.map f` plus the pushforwards `(i_j ≫ f)_* div(r_j)` of the
members whose image has smaller dimension
(`Chow.RatEquivFamily.map_cycle_eq_cycle_map_add_finsum`, from Fulton, *Intersection Theory*,
Proposition 1.4(b), as `Chow.map_height_div_eq_map_imageι`).

Fulton's Proposition 1.4(a), that these remaining pushforwards vanish
(`Chow.map_height_div_eq_zero_of_height_lt`), then makes the pushforward of the cycle of `F` the
cycle of `F.map f` (`Chow.RatEquivFamily.cycle_map_eq_map_cycle`), so that proper pushforward
preserves rational equivalence (`Chow.cyclesMap_mem_ratEquiv`).

## Main definitions

* `TauCeti.AlgebraicGeometry.Chow.ChowGroup.properPushforward`: the proper pushforward
  `f_* : CH_n(X) →+ CH_n(Y)`.
* `TauCeti.AlgebraicGeometry.Chow.ChowGroup.degree`: the degree `CH_0(X) →+ ℤ` for `X` proper
  over `k`.

## Main results

* `TauCeti.AlgebraicGeometry.Chow.cyclesMap_mem_ratEquiv`: proper pushforward preserves rational
  equivalence.
* `TauCeti.AlgebraicGeometry.Chow.ChowGroup.properPushforward_comp`: `(g ∘ f)_* = g_* ∘ f_*`.
* `TauCeti.AlgebraicGeometry.Chow.ChowGroup.degree_comp_properPushforward`: `deg ∘ f_* = deg`.

## References

* W. Fulton, *Intersection Theory*, Theorem 1.4 and Definition 1.4.
* The Stacks Project, Sections 02R3, 02S0 and 0AZ0.
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

omit [IsLocallyNoetherian Y] in
/-- For `f` proper over `k`, a member whose image has smaller dimension pushes forward to zero
(Fulton, *Intersection Theory*, Proposition 1.4(a)). -/
lemma map_comp_div_eq_zero_of_notMem_mapIndex (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    {j : F.ι} (hj : j ∉ F.mapIndex f) :
    AlgebraicCycle.map (F.i j ≫ f) height height (AlgebraicCycle.div (F.r j)) = 0 := by
  -- `W_j` is a scheme over `k` through `X`, and `i_j ≫ f` is a proper morphism over `k`.
  let _ : (F.W j).Over (Spec (.of k)) := ⟨F.i j ≫ X ↘ Spec (.of k)⟩
  have : LocallyOfFiniteType (F.W j ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (F.i j ≫ X ↘ Spec (.of k)))
  have : (F.i j ≫ f).IsOver (Spec (.of k)) := ⟨by
    -- The structure morphism of `W_j` is, by the definition above, `i_j` followed by that of `X`.
    change (F.i j ≫ f) ≫ Y ↘ Spec (.of k) = F.i j ≫ X ↘ Spec (.of k)
    rw [Category.assoc, comp_over]⟩
  refine map_height_div_eq_zero_of_height_lt k (F.i j ≫ f)
    ((height_apply_le_height k (F.i j ≫ f) _).lt_of_ne ?_) (F.r j)
  rw [Scheme.Hom.comp_apply]
  exact hj

/-- **Proper pushforward of a rational equivalence.** For `f` proper over `k`, the pushforward of
the cycle of a family is the cycle of its image family. -/
theorem cycle_map_eq_map_cycle (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f] :
    (F.map f).cycle = AlgebraicCycle.map f height height F.cycle := by
  ext y
  rw [F.map_cycle_eq_cycle_map_add_finsum k f y, finsum_mem_eq_zero_of_forall_eq_zero
    fun j hj ↦ by
      rw [F.map_comp_div_eq_zero_of_notMem_mapIndex k f hj,
        Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply], add_zero]

end RatEquivFamily

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]

section Pushforward

variable [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of k))]

/-- **Proper pushforward preserves rational equivalence** (Fulton, *Intersection Theory*,
Theorem 1.4). For `f` proper over a field `k`, the pushforward of an `n`-cycle rationally
equivalent to zero is rationally equivalent to zero. -/
theorem cyclesMap_mem_ratEquiv (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f] {n : ℤ}
    {α : cyclesOfDimension X n} (hα : α ∈ RatEquiv X n) : cyclesMap k f α ∈ RatEquiv Y n := by
  obtain ⟨F, hF⟩ := mem_ratEquiv_iff.mp hα
  exact mem_ratEquiv_iff.mpr
    ⟨F.map f, by rw [F.cycle_map_eq_map_cycle k f, hF, coe_cyclesMap]⟩

namespace ChowGroup

/-- The **proper pushforward** `f_* : CH_n(X) →+ CH_n(Y)` of Chow groups along a proper morphism
over a field `k`, induced by the pushforward of cycles `[V] ↦ [K(V) : K(f(V))] [f(V)]`. -/
noncomputable def properPushforward (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    {n : ℤ} : ChowGroup X n →+ ChowGroup Y n :=
  lift (cycleClass.comp (cyclesMap k f)) fun _ hα ↦
    cycleClass_eq_zero_iff.mpr (cyclesMap_mem_ratEquiv k f hα)

variable {k}

/-- The proper pushforward of the class of a cycle is the class of its pushforward. -/
@[simp]
lemma properPushforward_cycleClass (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f] {n : ℤ}
    (α : cyclesOfDimension X n) :
    properPushforward k f (cycleClass α) = cycleClass (cyclesMap k f α) :=
  lift_cycleClass _ _ α

variable (k)

/-- Proper pushforward along the identity is the identity. -/
@[simp]
lemma properPushforward_id {n : ℤ} :
    properPushforward k (𝟙 X) = AddMonoidHom.id (ChowGroup X n) := by
  ext α
  simp

/-- **Functoriality of proper pushforward**: `(g ∘ f)_* = g_* ∘ f_*`. -/
lemma properPushforward_comp (f : X ⟶ Y) (g : Y ⟶ Z) [f.IsOver (Spec (.of k))]
    [g.IsOver (Spec (.of k))] [IsProper f] [IsProper g] {n : ℤ} :
    properPushforward k (f ≫ g) =
      (properPushforward k g).comp (properPushforward k f : _ →+ ChowGroup Y n) := by
  ext α
  simp [cyclesMap_comp]

/-- Along a closed immersion over `k`, proper pushforward is the closed-immersion pushforward
`Chow.ChowGroup.pushforward`. -/
lemma properPushforward_eq_pushforward (i : X ⟶ Y) [i.IsOver (Spec (.of k))]
    [IsClosedImmersion i] {n : ℤ} :
    properPushforward k i = (pushforward i : ChowGroup X n →+ ChowGroup Y n) := by
  ext α
  simp [cyclesMap_eq_cyclesPushforward]

end ChowGroup

end Pushforward

namespace ChowGroup

section Degree

variable (X) [CompactSpace X] [IsProper (X ↘ Spec (.of k))]

/-- The **degree** `deg : CH_0(X) →+ ℤ` of zero-cycle classes on a scheme proper over a field
`k`, induced by the degree `Σ n_x [x] ↦ Σ n_x [κ(x) : k]` of zero-cycles. It is well defined
because the degree of a zero-cycle is the coefficient of its pushforward to `Spec k`, and proper
pushforward preserves rational equivalence. -/
noncomputable def degree : ChowGroup X 0 →+ ℤ :=
  lift (cyclesDegree k X) fun α hα ↦ by
    -- The degree of `α` is the coefficient of its pushforward to `Spec k`, which is rationally
    -- equivalent to zero, hence zero.
    let _ : (Spec (.of k)).Over (Spec (.of k)) := ⟨𝟙 _⟩
    have : (X ↘ Spec (.of k)).IsOver (Spec (.of k)) := ⟨Category.comp_id _⟩
    have h := congrArg (equivIntOfUnique (Spec (.of k)))
      (cycleClass_eq_zero_iff.mpr (cyclesMap_mem_ratEquiv k (X ↘ Spec (.of k)) hα))
    rw [equivIntOfUnique_cycleClass, map_zero, coe_cyclesMap] at h
    rw [AddMonoidHom.mem_ker, cyclesDegree_apply, ← AlgebraicCycle.degree_apply]
    exact (degree_eq_map_height_apply k _).trans h

variable {k X}

/-- The degree of the class of a zero-cycle is its degree. -/
@[simp]
lemma degree_cycleClass (α : cyclesOfDimension X 0) :
    degree k X (cycleClass α) = cyclesDegree k X α :=
  lift_cycleClass _ _ α

variable [CompactSpace Y] [IsProper (Y ↘ Spec (.of k))]

/-- **Proper pushforward preserves degrees**: `deg (f_* c) = deg c` for `f` proper over `k`
between schemes proper over `k`. -/
@[simp]
lemma degree_properPushforward (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (c : ChowGroup X 0) : degree k Y (properPushforward k f c) = degree k X c := by
  obtain ⟨α, rfl⟩ := cycleClass_surjective c
  rw [properPushforward_cycleClass, degree_cycleClass, degree_cycleClass, cyclesDegree_cyclesMap]

/-- **Proper pushforward preserves degrees**: `deg ∘ f_* = deg`. -/
lemma degree_comp_properPushforward (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f] :
    (degree k Y).comp (properPushforward k f) = degree k X :=
  AddMonoidHom.ext (degree_properPushforward f)

end Degree

end ChowGroup

end TauCeti.AlgebraicGeometry.Chow
