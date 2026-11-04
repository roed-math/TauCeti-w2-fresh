/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.IntegralClosure.Punctured
public import TauCeti.RingTheory.Node.Resolution

/-!
# The normalization of a neighbourhood of an isolated node

Let `q` be a maximal ideal of a commutative ring `A` and `u : A` with `√(u) = q`, so that `Spec A_u`
is `Spec A` with the closed point `q` removed. Suppose the local ring `A_q` is a node in the shape
of `TauCeti.RingTheory.Node.Resolution`: its maximal ideal is `(u, y)`, not principal, with `u` a
nonzerodivisor, `a u² + b u y + y² = 0` and `b² - 4a` a unit. Then the integral closure `C` of `A`
in `A_u` is finite over `A`, its conductor is `q`, and its cokernel `C / A` is `A / q`.

Indeed `(A_q)_u = A_q ⊗[A] A_u` is a localization of `A_u` at `q`, and the integral closure of `A_q`
in it is the blowup chart `A_q[𝔪/u]` (`TauCeti.integralClosure_eq_affineBlowup`), whose conductor is
`𝔪` and whose cokernel is the residue field (`TauCeti.conductor_affineBlowup_eq_maximalIdeal`,
`TauCeti.affineBlowupQuotientEquiv`). The cokernel of `A → C` is local at `q`
(`TauCeti.integralClosureQuotientEquiv`), so these local statements globalize.

## Main results

* `TauCeti.conductor_integralClosure_away_eq_of_maximalIdeal_eq_span`: the integral closure of
  `A` in `A_u` is finite, with conductor `q` and cokernel `A / q`.
-/

public section

noncomputable section

open IsLocalRing TensorProduct

namespace TauCeti

variable {A : Type*} [CommRing A] (q : Ideal A) [q.IsMaximal] {u : A} (Aq : Type*) [CommRing Aq]
  [Algebra A Aq] [IsLocalization.AtPrime Aq q] [IsLocalRing Aq] [IsNoetherianRing Aq]

/-- `TauCeti.conductor_integralClosure_away_eq_of_maximalIdeal_eq_span` for a given localization
`L'` of `A_u` at `q`, which is also a localization of `A_q` away from `u`. Stating it for an
abstract `L'` keeps instance search on the cokernels fast. -/
private theorem conductor_integralClosure_away_eq_aux (L' : Type*) [CommRing L']
    [Algebra Aq L'] [Algebra A L'] [Algebra (Localization.Away u) L'] [IsScalarTower A Aq L']
    [IsScalarTower A (Localization.Away u) L']
    [IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away u) q.primeCompl) L']
    [IsLocalization.Away (algebraMap A Aq u) L'] (hu : (Ideal.span {u}).radical = q)
    {y a b : Aq} (hm : maximalIdeal Aq = Ideal.span {algebraMap A Aq u, y})
    (hx : algebraMap A Aq u ∈ nonZeroDivisors Aq) (hprin : ¬ (maximalIdeal Aq).IsPrincipal)
    (hrel : a * algebraMap A Aq u ^ 2 + b * algebraMap A Aq u * y + y ^ 2 = 0)
    (hd : IsUnit (discrim a b 1)) :
    Module.Finite A (integralClosure A (Localization.Away u)) ∧
      Algebra.conductor A (integralClosure A (Localization.Away u)) = q ∧
      Nonempty ((integralClosure A (Localization.Away u) ⧸
        (1 : Submodule A (integralClosure A (Localization.Away u)))) ≃ₗ[A] A ⧸ q) := by
  have hIC := integralClosure_eq_affineBlowup (S := L') hm hrel hd
  have e : (integralClosure Aq L' ⧸ (1 : Submodule Aq (integralClosure Aq L'))) ≃ₗ[Aq]
      Aq ⧸ maximalIdeal Aq := by
    rw [hIC]
    exact affineBlowupQuotientEquiv hm hrel hx hprin
  refine ⟨finite_integralClosure_of_quotientEquiv q _ Aq L' hu e,
    conductor_integralClosure_eq_of_conductor_eq_maximalIdeal q _ Aq L' hu ?_,
    ⟨integralClosureQuotientEquivOfQuotientEquiv q _ Aq L' hu e⟩⟩
  rw [hIC]
  exact conductor_affineBlowup_eq_maximalIdeal hm hrel hx hprin

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **The normalization of a neighbourhood of an isolated node.** Let `q` be a maximal ideal of `A`
with `√(u) = q`, and suppose the maximal ideal of `A_q` is `(u, y)`, not principal, with `u` a
nonzerodivisor, `a u² + b u y + y² = 0` and `b² - 4a` a unit. Then the integral closure of `A` in
`A_u` is finite over `A`, its conductor is `q`, and its cokernel is `A / q`. -/
theorem conductor_integralClosure_away_eq_of_maximalIdeal_eq_span
    (hu : (Ideal.span {u}).radical = q) {y a b : Aq}
    (hm : maximalIdeal Aq = Ideal.span {algebraMap A Aq u, y})
    (hx : algebraMap A Aq u ∈ nonZeroDivisors Aq) (hprin : ¬ (maximalIdeal Aq).IsPrincipal)
    (hrel : a * algebraMap A Aq u ^ 2 + b * algebraMap A Aq u * y + y ^ 2 = 0)
    (hd : IsUnit (discrim a b 1)) :
    Module.Finite A (integralClosure A (Localization.Away u)) ∧
      Algebra.conductor A (integralClosure A (Localization.Away u)) = q ∧
      Nonempty ((integralClosure A (Localization.Away u) ⧸
        (1 : Submodule A (integralClosure A (Localization.Away u)))) ≃ₗ[A] A ⧸ q) := by
  -- `(A_q)_u = A_q ⊗[A] A_u` is a localization of `A_u` at `q`, and of `A_q` away from `u`.
  have : IsLocalization.Away (algebraMap A Aq u) (Aq ⊗[A] Localization.Away u) := by
    have := IsLocalization.tensor (S := Aq) (Localization.Away u) (Submonoid.powers u)
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at this
  exact conductor_integralClosure_away_eq_aux q Aq (Aq ⊗[A] Localization.Away u) hu hm hx hprin
    hrel hd

end TauCeti
