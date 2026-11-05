/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import TauCeti.AlgebraicGeometry.AlgebraicCycle.Principal
public import TauCeti.AlgebraicGeometry.Chow.Pushforward
public import TauCeti.AlgebraicGeometry.OrderOfVanishing.Norm
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic

/-!
# Proper pushforward of a principal divisor

Let `k` be a field and `f : X ⟶ Y` a proper dominant morphism of integral schemes locally of finite
type over `k`, of the same dimension. Then the function field `K(X)` is finite over `K(Y)`, and
for a nonzero rational function `r` on `X`, the pushforward of its principal cycle with
residue-degree weights is the principal cycle of its norm:
`f_* div(r) = div(N_{K(X)/K(Y)}(r))` (`Chow.map_height_div`; Fulton, *Intersection Theory*,
Proposition 1.4(b)).

The coefficients are compared one point `y ∈ Y` at a time.

* If `y` has codimension one, `f` is finite over an affine neighbourhood of `y`
  (`TauCeti.AlgebraicGeometry.exists_isFinite_morphismRestrict_of_height_add_one` and
  `AlgebraicGeometry.Scheme.Hom.exists_isAffineOpen_finite_app_of_isFinite_morphismRestrict`), and
  the identity is the order of a norm at a point of codimension one
  (`TauCeti.AlgebraicGeometry.ord_norm_eq_finsum_of_isAffineOpen`).
* Otherwise both sides vanish: a point `x` over `y` with finite residue extension has the dimension
  of `y`, hence also its codimension (`TauCeti.AlgebraicGeometry.coheight_apply_eq_coheight`), so
  `r` has order zero at `x`.

Since pushforward preserves degrees, a principal divisor and the principal divisor of its norm
have the same degree (`Chow.degree_div_eq_degree_div_norm`): on curves, the degree of principal
divisors can be computed after a finite map to another curve.

For a proper morphism `f` from an integral scheme whose image has the same dimension,
`Chow.map_height_div_eq_map_imageι` applies this to the factorization of `f` through its integral
scheme-theoretic image: `f_* div(r)` is `div(N(r))` on `f(X)`, pushed into `Y`. When instead the
image has dimension less than `dim X - 1`, `f_* div(r) = 0`
(`Chow.map_height_div_eq_zero_of_height_add_one_lt`, part of Fulton's Proposition 1.4(a)).
-/

public section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace TauCeti.AlgebraicGeometry

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]

variable [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

namespace Chow

/-- **Proper pushforward of a principal divisor** (Fulton, *Intersection Theory*,
Proposition 1.4(b)). Let `f : X ⟶ Y` be a proper dominant morphism over a field `k` of integral
schemes locally of finite type over `k`, of the same dimension, so that `K(X)` is finite over
`K(Y)` (`TauCeti.AlgebraicGeometry.functionFieldMap_finite_of_topologicalKrullDim_eq`). For a
nonzero rational function `r` on `X`, the pushforward of `div r` with residue-degree weights is
`div N_{K(X)/K(Y)}(r)`. -/
theorem map_height_div (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f] [IsDominant f]
    (h : topologicalKrullDim X = topologicalKrullDim Y) (r : X.functionFieldˣ) :
    letI := f.functionFieldMap.hom.toAlgebra
    AlgebraicCycle.map f height height (AlgebraicCycle.div r) =
      AlgebraicCycle.div (Units.map (Algebra.norm Y.functionField (S := X.functionField)) r) := by
  let _ := f.functionFieldMap.hom.toAlgebra
  ext y
  rw [map_height_apply k, AlgebraicCycle.div_apply, Units.coe_map]
  simp only [AlgebraicCycle.div_apply]
  by_cases hy : coheight y = 1
  · -- `f` is finite over an affine neighbourhood of `y`, where the orders of the norm are known.
    obtain ⟨n, hn⟩ : ∃ n : ℕ, height y = n := ⟨_, height_eq_toNat_trdeg_residueField k y⟩
    have hY : topologicalKrullDim Y = n + 1 := by
      rw [← coheight_add_height_eq_topologicalKrullDim k y, hy, hn, add_comm]
      norm_cast
    obtain ⟨V, hyV, hV⟩ :=
      exists_isFinite_morphismRestrict_of_height_add_one k f (h.trans hY) hY hn
    obtain ⟨U, -, hU, hfU, hfin, hyU⟩ :=
      f.exists_isAffineOpen_finite_app_of_isFinite_morphismRestrict hyV
    rw [← f.appLE_eq_app] at hfin
    exact (ord_norm_eq_finsum_of_isAffineOpen f hU hfU hfin hyU hy r.ne_zero).symm
  · -- Both sides vanish: the points over `y` with finite residue extension have the codimension
    -- of `y`.
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hy]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    subst hx
    by_cases hd : f.residueDegree x = 0
    · rw [hd, Nat.cast_zero, mul_zero]
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one, zero_mul]
      rwa [← coheight_apply_eq_coheight k f h
        (height_apply_eq_height_of_residueDegree_ne_zero k f hd)]

/-- **Degrees of principal divisors and norms.** Let `f : X ⟶ Y` be a proper dominant morphism
over a field `k` of quasi-compact integral schemes locally of finite type over `k`, of the same
dimension. For a nonzero rational function `r` on `X`, the principal cycle of `r` and that of its
norm `N_{K(X)/K(Y)}(r)` have the same degree over `k`. -/
theorem degree_div_eq_degree_div_norm [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y)
    [f.IsOver (Spec (.of k))] [IsProper f] [IsDominant f]
    (h : topologicalKrullDim X = topologicalKrullDim Y) (r : X.functionFieldˣ) :
    letI := f.functionFieldMap.hom.toAlgebra
    AlgebraicCycle.degree (X ↘ Spec (.of k)) (AlgebraicCycle.div r) =
      AlgebraicCycle.degree (Y ↘ Spec (.of k)) (AlgebraicCycle.div
        (Units.map (Algebra.norm Y.functionField (S := X.functionField)) r)) := by
  rw [← map_height_div k f h r, degree_map_height k f]

omit [IsIntegral Y] in
/-- **Proper pushforward of a principal divisor through the image.** Let `f : X ⟶ Y` be a proper
morphism over a field `k` from an integral scheme, between schemes locally of finite type over `k`,
whose image `f(X)` has the dimension of `X`. Then `f` factors through the integral scheme-theoretic
image `f(X)` (`f = f.toImage ≫ f.imageι`), `K(X)` is finite over `K(f(X))`, and for a nonzero
rational function `r` on `X`, the pushforward of `div r` is the cycle `div N_{K(X)/K(f(X))}(r)`
on `f(X)`, pushed into `Y`. -/
theorem map_height_div_eq_map_imageι (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (h : height (f (genericPoint X)) = height (genericPoint X)) (r : X.functionFieldˣ) :
    letI := f.toImage.functionFieldMap.hom.toAlgebra
    AlgebraicCycle.map f height height (AlgebraicCycle.div r) =
      AlgebraicCycle.map f.imageι height height (AlgebraicCycle.div
        (Units.map (Algebra.norm f.image.functionField (S := X.functionField)) r)) := by
  let _ := f.toImage.functionFieldMap.hom.toAlgebra
  -- The image is a scheme over `k`, locally of finite type, through `Y`.
  let _ : f.image.Over (Spec (.of k)) := ⟨f.imageι ≫ Y ↘ Spec (.of k)⟩
  have : f.imageι.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : f.toImage.IsOver (Spec (.of k)) := ⟨by
    -- The structure morphism of the image is, by the definition above, `f.imageι` followed by
    -- that of `Y`.
    change f.toImage ≫ f.imageι ≫ Y ↘ Spec (.of k) = _
    rw [f.toImage_imageι_assoc, comp_over]⟩
  have : LocallyOfFiniteType (f.image ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (f.imageι ≫ Y ↘ Spec (.of k)))
  have : IsProper (f.toImage ≫ f.imageι) := by rw [f.toImage_imageι]; infer_instance
  have : IsProper f.toImage := IsProper.of_comp f.toImage f.imageι
  -- `X` and its image have the same dimension: the closed immersion `f.imageι` preserves heights.
  have hdim : topologicalKrullDim X = topologicalKrullDim f.image := by
    have hι := f.imageι.height_apply_eq_height (f.toImage (genericPoint X))
    rw [← Scheme.Hom.comp_apply, f.toImage_imageι, f.toImage.genericPoint_eq_of_isDominant,
      h] at hι
    rw [topologicalKrullDim_eq_height_genericPoint, topologicalKrullDim_eq_height_genericPoint, hι]
  rw [← map_height_div k f.toImage hdim r, ← map_height_comp k f.toImage f.imageι]
  -- Substitute `f = f.toImage ≫ f.imageι`; the two sides differ only in instance arguments.
  have key : ∀ (g : X ⟶ Y) [QuasiCompact g], g = f →
      AlgebraicCycle.map f height height (AlgebraicCycle.div r) =
        AlgebraicCycle.map g height height (AlgebraicCycle.div r) := by
    rintro g _ rfl
    rfl
  exact key _ f.toImage_imageι

omit [IsIntegral Y] [IsLocallyNoetherian Y] in
/-- **Principal divisors vanish under a large drop of dimension.** Let `f : X ⟶ Y` be a
quasi-compact morphism over a field `k` from an integral scheme, between schemes locally of
finite type over `k`, whose image has dimension less than `dim X - 1`. Then `f_* div r = 0` for
every nonzero rational function `r` on `X`: the points of `div r` have dimension `dim X - 1`, and
those with finite residue extension would keep that dimension in the image. -/
theorem map_height_div_eq_zero_of_height_add_one_lt (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [QuasiCompact f] (h : height (f (genericPoint X)) + 1 < height (genericPoint X))
    (r : X.functionFieldˣ) :
    AlgebraicCycle.map f height height (AlgebraicCycle.div r) = 0 := by
  ext y
  rw [map_height_apply k, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
  refine finsum_mem_eq_zero_of_forall_eq_zero fun x _ ↦ ?_
  by_contra hne
  rw [AlgebraicCycle.div_apply] at hne
  have hd : f.residueDegree x ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hne
  -- `x` has codimension one, so `height x + 1 = dim X`.
  have hx1 : coheight x = 1 := by
    by_contra h'
    exact left_ne_zero_of_mul hne (Scheme.ord_eq_zero_of_coheight_neq_one h' _)
  have hdim := coheight_add_height_eq_topologicalKrullDim k x
  rw [topologicalKrullDim_eq_height_genericPoint, hx1, add_comm] at hdim
  have hdim' : height x + 1 = height (genericPoint X) := WithBot.coe_injective hdim
  -- `f x` is a specialization of `f η`, of the height of `x`.
  have hle : height (f x) ≤ height (f (genericPoint X)) :=
    height_mono (((genericPoint_spec X).specializes (Set.mem_univ x)).map f.continuous)
  rw [height_apply_eq_height_of_residueDegree_ne_zero k f hd] at hle
  exact h.not_ge (hdim' ▸ add_le_add_left hle 1)

end Chow

end TauCeti.AlgebraicGeometry
