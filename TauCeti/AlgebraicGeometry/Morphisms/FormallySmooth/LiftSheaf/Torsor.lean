/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftSheaf.Sub
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Torsor

/-!
# The torsor of lifts along a first-order thickening

For `f : X ⟶ S` smooth, `i : T ⟶ T'` a first-order thickening, and `a : T ⟶ X`, `h : T' ⟶ S` with
`a ≫ f = i ≫ h`, the sheaf of lifts `liftSheaf f i a h` is a torsor under the sheaf of derivations
`liftDerivationSheaf f i a` (Stacks, Lemma 37.9.5 (04FJ)), in the sense of
`CategoryTheory.Sheaf.Torsor`: a derivation `D` sends a section `l` to the unique section `D • l`
with `liftSheafSub (D • l) l = D`. The sheaf of lifts is locally nonempty because `f` is smooth.

## Main definitions

* `TauCeti.AlgebraicGeometry.liftDerivationGrpSheaf f i a`: the sheaf of derivations as a sheaf of
  multiplicative groups.
* `TauCeti.AlgebraicGeometry.liftTorsor w`: the sheaf of lifts as a torsor under it.

## Main results

* `TauCeti.AlgebraicGeometry.liftSheafSub_smul`: `liftSheafSub (D • l) l = D`.

## References

* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ).
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace TauCeti.AlgebraicGeometry

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) (i : T ⟶ T') (a : T ⟶ X)

instance : (AddCommGrpCat.toCommGrp.{u}).IsEquivalence :=
  inferInstanceAs commGroupAddCommGroupEquivalence.inverse.IsEquivalence

/-- The sheaf of derivations of `a⁻¹ 𝒪_X` over `𝒪_S` into the ideal of `i`, as a sheaf of
multiplicative groups. -/
@[expose] noncomputable def liftDerivationGrpSheaf :
    Sheaf (Opens.grothendieckTopology T') GrpCat.{u} :=
  (sheafCompose _ (AddCommGrpCat.toCommGrp.{u} ⋙ forget₂ CommGrpCat.{u} GrpCat.{u})).obj
    (liftDerivationSheaf f i a)

variable {f i a} {h : T' ⟶ S} [IsFirstOrderThickening i] (w : a ≫ f = i ≫ h)

/-- A derivation `D` over `W` sends a section `l` of the sheaf of lifts to the unique section with
difference `D` with `l`. -/
noncomputable def liftSMul {W : T'.Opens} (D : liftDerivationSubgroup f i a W)
    (l : (liftSheaf f i a h).obj.obj (op W)) : (liftSheaf f i a h).obj.obj (op W) :=
  (exists_liftSheafSub_eq w l D).choose

/-- `liftSMul D l` differs from `l` by `D`. -/
theorem liftSheafSub_liftSMul {W : T'.Opens} (D : liftDerivationSubgroup f i a W)
    (l : (liftSheaf f i a h).obj.obj (op W)) : liftSheafSub (liftSMul w D l) l = D :=
  (exists_liftSheafSub_eq w l D).choose_spec

/-- The action of the derivations over `W` on the sections of the sheaf of lifts over `W`: `D`
sends `l` to the unique section `D • l` with `liftSheafSub (D • l) l = D`. -/
noncomputable abbrev liftMulAction (W : T'.Opens) :
    MulAction (Multiplicative (liftDerivationSubgroup f i a W))
      ((liftSheaf f i a h).obj.obj (op W)) where
  smul D l := liftSMul w D.toAdd l
  one_smul l := liftSheafSub_left_injective l <|
    (liftSheafSub_liftSMul w _ l).trans (liftSheafSub_self l).symm
  mul_smul D E l := liftSheafSub_left_injective l <| by
    -- Unfold the action to `liftSMul`.
    change liftSheafSub (liftSMul w (D * E).toAdd l) l =
      liftSheafSub (liftSMul w D.toAdd (liftSMul w E.toAdd l)) l
    rw [liftSheafSub_liftSMul, ← liftSheafSub_add_liftSheafSub _ (liftSMul w E.toAdd l) l,
      liftSheafSub_liftSMul, liftSheafSub_liftSMul, toAdd_mul]

/-- A derivation `D` acting on a section `l` of the sheaf of lifts differs from `l` by `D`. -/
theorem liftSheafSub_smul {W : T'.Opens} (D : Multiplicative (liftDerivationSubgroup f i a W))
    (l : (liftSheaf f i a h).obj.obj (op W)) :
    letI := liftMulAction w W
    liftSheafSub (D • l) l = D.toAdd :=
  liftSheafSub_liftSMul w D.toAdd l

/-- The action of derivations on the sheaf of lifts commutes with restriction. -/
theorem liftSMul_map {W W' : T'.Opens} (e : W' ≤ W) (D : liftDerivationSubgroup f i a W)
    (l : (liftSheaf f i a h).obj.obj (op W)) :
    (liftSheaf f i a h).obj.map (homOfLE e).op (liftSMul w D l) =
      liftSMul w (liftDerivationSubgroupRestrict f i a e D)
        ((liftSheaf f i a h).obj.map (homOfLE e).op l) :=
  liftSheafSub_left_injective ((liftSheaf f i a h).obj.map (homOfLE e).op l) <| by
    simp only
    rw [← liftSheafSub_map, liftSheafSub_liftSMul, liftSheafSub_liftSMul]

/-- The derivations over `W` act simply transitively on the sections of the sheaf of lifts. -/
theorem liftMulAction_bijective (W : T'.Opens) :
    letI := liftMulAction w W
    Function.Bijective fun x : Multiplicative (liftDerivationSubgroup f i a W) ×
      (liftSheaf f i a h).obj.obj (op W) ↦ (x.1 • x.2, x.2) := by
  let := liftMulAction w W
  refine ⟨fun ⟨D, l⟩ ⟨E, l'⟩ hDE ↦ ?_, fun ⟨l', l⟩ ↦ ?_⟩
  · simp only [Prod.mk.injEq] at hDE
    obtain ⟨hDE, rfl⟩ := hDE
    have := congrArg (liftSheafSub · l) hDE
    simp only [liftSheafSub_smul] at this
    rw [Multiplicative.toAdd.injective this]
  · refine ⟨⟨Multiplicative.ofAdd (liftSheafSub l' l), l⟩, Prod.ext ?_ rfl⟩
    exact liftSheafSub_left_injective l (liftSheafSub_smul w _ l)

/-- For `f` smooth, the sheaf of lifts of `a` along the first-order thickening `i` over `S` is a
torsor under the sheaf of derivations `liftDerivationGrpSheaf f i a` (Stacks, Lemma 37.9.5
(04FJ)). -/
noncomputable def liftTorsor [Smooth f] : Sheaf.Torsor (liftDerivationGrpSheaf f i a) where
  sheaf := liftSheaf f i a h
  mulAction W := liftMulAction w W.unop
  map_smul W W' e D l := by
    obtain ⟨e, rfl⟩ : ∃ e' : W'.unop ≤ W.unop, e = (homOfLE e').op :=
      ⟨leOfHom e.unop, Subsingleton.elim _ _⟩
    exact liftSMul_map w e D.toAdd l
  coversTop := liftSheaf_coversTop f i a h w
  bijective W := liftMulAction_bijective w W.unop

end TauCeti.AlgebraicGeometry
