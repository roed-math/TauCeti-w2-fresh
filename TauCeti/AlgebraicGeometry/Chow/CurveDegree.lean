/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicCycle.Principal
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Degree
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Principal
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import TauCeti.AlgebraicGeometry.Chow.PrincipalPushforward
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
import TauCeti.AlgebraicGeometry.Normalization.Finite
import TauCeti.AlgebraicGeometry.Normalization.Regular
import TauCeti.AlgebraicGeometry.Scheme.Normal
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Finiteness

/-!
# Principal divisors on proper curves have degree zero

Let `X` be an integral scheme of dimension one, proper over a field `k`. The degree over `k` of the
principal cycle of a nonzero rational function `r` on `X` vanishes:
`deg div(r) = Σ_x [κ(x) : k] ord_x(r) = 0` (Fulton, *Intersection Theory*, Proposition 1.4(a), for
a curve over a point).

The principal cycle `AlgebraicCycle.div r` and the principal Weil divisor of `r` in the order system
`WeilDivisor.OrderSystem.ofScheme X` have the same coefficients, the orders of vanishing of `r` at
the points of codimension one, so the degree of the cycle is the residue-degree-weighted degree
`SchemeWeilDivisor.relativeDegree` of the divisor (`Chow.degree_div_eq_relativeDegree`). When the
local rings of `X` at its closed points are discrete valuation rings, that degree vanishes by the
Riemann–Roch comparison of Euler characteristics
(`SchemeWeilDivisor.relativeDegree_principalDivisor`, with the finiteness of `H¹(X, 𝒪_X)` from
`TauCeti.AlgebraicGeometry.finiteDimensional_cohomology_one_trivial_of_isProper`).

In general, the normalization `ν : X' ⟶ X` of `X` in its function field is finite
(`TauCeti.AlgebraicGeometry.isFinite_fromNormalization_fromSpecStalk_genericPoint_of_field`), and
`X'` is a normal proper curve. For `r` pulled back to `X'`, proper pushforward along `ν` gives
`0 = deg div_{X'}(r) = deg div_X(N(r)) = [K(X') : K(X)] • deg div_X(r)`
(`Chow.degree_div_eq_degree_div_norm`, Fulton, Proposition 1.4(b)).

## Main results

* `TauCeti.AlgebraicGeometry.Chow.degree_div_eq_relativeDegree`: on a Noetherian integral scheme,
  the degree of the principal cycle of `r` is the relative degree of the principal Weil divisor of
  `r`.
* `TauCeti.AlgebraicGeometry.Chow.degree_div_eq_zero_of_isDiscreteValuationRing`: on a proper
  integral curve over `k` whose codimension-one local rings are discrete valuation rings, principal
  cycles have degree zero.
* `TauCeti.AlgebraicGeometry.Chow.degree_div_eq_zero`: on every proper integral curve over `k`,
  principal cycles have degree zero.

## References

* W. Fulton, *Intersection Theory*, Proposition 1.4.
* R. Hartshorne, *Algebraic Geometry*, II, Corollary 6.10.
-/

public section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace TauCeti.AlgebraicGeometry

namespace Chow

/-- **The degree of a principal cycle as a degree of Weil divisors.** On a Noetherian integral
scheme `X`, for a morphism `f : X ⟶ Y` and a nonzero rational function `r`, the residue-degree
weighted degree of the principal cycle `div r` is the relative degree of the principal Weil divisor
of `r`: both are `Σ_x [κ(x) : κ(f x)] ord_x(r)` over the points of codimension one. -/
theorem degree_div_eq_relativeDegree {X Y : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Y) (r : X.functionFieldˣ) :
    AlgebraicCycle.degree f (AlgebraicCycle.div r) =
      SchemeWeilDivisor.relativeDegree f
        ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor (Additive.ofMul r)) := by
  set D := (WeilDivisor.OrderSystem.ofScheme X).principalDivisor (Additive.ofMul r)
  have hD (x : CodimensionOnePoint X) : D x = X.ord (r : X.functionField) x := by
    change WeilDivisor.coeff D x = _
    rw [WeilDivisor.OrderSystem.coeff_principalDivisor, WeilDivisor.OrderSystem.ofScheme_ord,
      SchemeWeilDivisor.orderAt_apply, toMul_ofMul]
  rw [SchemeWeilDivisor.relativeDegree_apply, Finsupp.sum,
    ← finsum_eq_sum_of_support_subset _ (fun x hx ↦ by
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      exact left_ne_zero_of_mul hx),
    AlgebraicCycle.degree_apply, ← finsum_mem_univ,
    finsum_mem_inter_support_eq' _ _ {x : X | coheight x = 1} fun x hx ↦ iff_of_true trivial (by
      by_contra h
      exact hx (by
        simp only [AlgebraicCycle.div_apply, Scheme.ord_eq_zero_of_coheight_neq_one h, smul_zero])),
    ← finsum_set_coe_eq_finsum_mem]
  refine finsum_congr fun x ↦ ?_
  rw [hD, AlgebraicCycle.div_apply, nsmul_eq_mul, mul_comm]

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsLocallyNoetherian X] [CompactSpace X] [IsProper (X ↘ Spec (.of k))]

/-- **Principal divisors on a normal proper curve have degree zero.** Let `X` be an integral scheme
of dimension one, proper over a field `k`, whose codimension-one local rings are discrete valuation
rings. Then for every nonzero rational function `r` on `X`, `deg div(r) = 0`. -/
theorem degree_div_eq_zero_of_isDiscreteValuationRing
    [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
    (hX : topologicalKrullDim X = 1) (r : X.functionFieldˣ) :
    AlgebraicCycle.degree (X ↘ Spec (.of k)) (AlgebraicCycle.div r) = 0 := by
  have : IsNoetherian X := {}
  have := finiteDimensional_cohomology_one_trivial_of_isProper k hX
  rw [degree_div_eq_relativeDegree]
  exact SchemeWeilDivisor.relativeDegree_principalDivisor k
    (fun x ↦ by exact_mod_cast (coheight_le_topologicalKrullDim x).trans hX.le) _

/-- Principal cycles on `X` have degree zero as soon as `X` is dominated by a finite morphism from
a normal integral scheme: push the principal cycle of `r` pulled back along `ν` forward again. -/
private lemma degree_div_eq_zero_of_isFinite (hX : topologicalKrullDim X = 1) {X' : Scheme.{u}}
    [IsIntegral X'] [IsNormalScheme X'] (ν : X' ⟶ X) [IsFinite ν] [IsDominant ν]
    (r : X.functionFieldˣ) :
    AlgebraicCycle.degree (X ↘ Spec (.of k)) (AlgebraicCycle.div r) = 0 := by
  -- The source is a normal proper curve over `k`.
  let _ : X'.Over (Spec (.of k)) := ⟨ν ≫ X ↘ Spec (.of k)⟩
  have : ν.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsProper (X' ↘ Spec (.of k)) := inferInstanceAs (IsProper (ν ≫ X ↘ Spec (.of k)))
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian ν
  have : CompactSpace X' :=
    (quasiCompact_iff_compactSpace (X' ↘ Spec (.of k))).mp inferInstance
  have (y : CodimensionOnePoint X') : IsDiscreteValuationRing (X'.presheaf.stalk (y : X')) :=
    IsNormalScheme.isDiscreteValuationRing_stalk X' y y.property
  -- It has the dimension of `X`.
  have hdim : topologicalKrullDim X' = topologicalKrullDim X := by
    refine le_antisymm ν.topologicalKrullDim_le ?_
    rw [topologicalKrullDim_eq_height_genericPoint X, ← ν.genericPoint_eq_of_isDominant,
      topologicalKrullDim_eq_height_genericPoint X']
    exact_mod_cast height_apply_le_height k ν _
  let _ := ν.functionFieldMap.hom.toAlgebra
  have : Module.Finite X.functionField X'.functionField :=
    functionFieldMap_finite_of_topologicalKrullDim_eq k ν hdim
  have h := degree_div_eq_degree_div_norm k ν hdim
    (Units.map (algebraMap X.functionField X'.functionField) r)
  rw [degree_div_eq_zero_of_isDiscreteValuationRing k (hdim.trans hX)] at h
  have hnorm : Units.map (Algebra.norm X.functionField (S := X'.functionField))
      (Units.map (algebraMap X.functionField X'.functionField) r) =
        r ^ Module.finrank X.functionField X'.functionField := by
    ext
    simp [Algebra.norm_algebraMap]
  rw [hnorm, AlgebraicCycle.div_pow, map_nsmul, eq_comm, smul_eq_zero] at h
  exact h.resolve_left Module.finrank_pos.ne'

/-- **Principal divisors on a proper curve have degree zero** (Fulton, *Intersection Theory*,
Proposition 1.4(a), for a curve over a point). Let `X` be an integral scheme of dimension one,
proper over a field `k`. Then for every nonzero rational function `r` on `X`,
`deg div(r) = Σ_x [κ(x) : k] ord_x(r) = 0`.

The normalization `ν : X' ⟶ X` of `X` in its function field is finite, and `X'` is a normal proper
curve over `k`, where principal cycles have degree zero
(`Chow.degree_div_eq_zero_of_isDiscreteValuationRing`). Pushing forward along `ν`
(`Chow.degree_div_eq_degree_div_norm`), `0 = deg div_{X'}(r) = deg div_X(N(r)) = d • deg div_X(r)`
for `r` pulled back to `X'`, where `d = [K(X') : K(X)] > 0`. -/
theorem degree_div_eq_zero (hX : topologicalKrullDim X = 1) (r : X.functionFieldˣ) :
    AlgebraicCycle.degree (X ↘ Spec (.of k)) (AlgebraicCycle.div r) = 0 := by
  have := isFinite_fromNormalization_fromSpecStalk_genericPoint_of_field (Y := X) k
  have := isRegular_normalization_fromSpecStalk_genericPoint hX.le
  have : IsDominant (X.fromSpecStalk (genericPoint X)).fromNormalization := by
    have : IsDominant ((X.fromSpecStalk (genericPoint X)).toNormalization ≫
        (X.fromSpecStalk (genericPoint X)).fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]
      infer_instance
    exact IsDominant.of_comp (X.fromSpecStalk (genericPoint X)).toNormalization _
  exact degree_div_eq_zero_of_isFinite k hX (X.fromSpecStalk (genericPoint X)).fromNormalization r

end Chow

end TauCeti.AlgebraicGeometry
