/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import TauCeti.AlgebraicGeometry.Chow.FlatPullback
public import TauCeti.AlgebraicGeometry.Chow.OpenRestriction
public import TauCeti.RingTheory.OrderOfVanishing.MinimalPrimes
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Flat pullback and orders of vanishing

The flat pullback of a principal divisor is computed one codimension-one point at a time
(Fulton, *Intersection theory*, Proposition 1.7; Stacks, Lemma 42.20.1). The local input is that a
flat local homomorphism `A → B` multiplies orders of vanishing by the length of the closed fibre:
`ord_B(a) = ord_A(a) · ℓ_B(B ⧸ 𝔪_A B)`.

## Main results

* `TauCeti.Ring.ord_algebraMap_of_flat`: for a flat local homomorphism `A → B`,
  `Ring.ord B (algebraMap A B a) = Ring.ord A a * length B (B ⧸ 𝔪_A B)`;
* `TauCeti.Ring.ord_mul_length_eq_finsum_minimalPrimes`: if moreover `B` is Noetherian of
  dimension at most one and `a` is a non-zero-divisor, `ord_A(a) · ℓ_B(B ⧸ 𝔪_A B)` is the sum over
  the minimal primes `𝔮` of `B` of `ℓ_{B_𝔮}(B_𝔮) · ord_{B ⧸ 𝔮}(a)` (the local form of Stacks,
  Lemma 42.20.1);
* `TauCeti.AlgebraicGeometry.Chow.ord_stalkMap`: for `f : X ⟶ Y` flat and `x : X`, pulling a
  germ `a` at `f x` back to `x` multiplies its order of vanishing by `fiberLength f x`;
* `TauCeti.AlgebraicGeometry.Chow.cycleFlatPullback_of_isOpenImmersion`: along an open immersion
  `j`, flat pullback of cycles is the restriction `cycleRestrict j` (the fibre lengths are `1`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace Ring

open IsLocalRing

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
  [Module.Flat A B] [IsLocalHom (algebraMap A B)]

/-- **Orders of vanishing under flat local homomorphisms.** For a flat local homomorphism
`A → B`, the order of vanishing of `a : A` in `B` is its order in `A` times the length of the
closed fibre `B ⧸ 𝔪_A B`: `B ⧸ a B` is the base change `B ⊗[A] (A ⧸ a A)`, and base change along
`A → B` multiplies lengths by `ℓ_B(B ⧸ 𝔪_A B)` (`IsLocalRing.length_baseChange`). -/
theorem ord_algebraMap_of_flat (a : A) :
    _root_.Ring.ord B (algebraMap A B a) =
      _root_.Ring.ord A a * Module.length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by
  rw [_root_.Ring.ord, _root_.Ring.ord, ← IsLocalRing.length_baseChange,
    ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
      (Ideal.span {a})).toLinearEquiv.length_eq, Ideal.map_span, Set.image_singleton]

open scoped nonZeroDivisors in
/-- **Orders of vanishing under flat local homomorphisms, over the minimal primes.** Let `A → B`
be a flat local homomorphism with `B` Noetherian of dimension at most one, and `a` a
non-zero-divisor of `A`. Then `ord_A(a) · ℓ_B(B ⧸ 𝔪_A B)` is the sum over the minimal primes `𝔮`
of `B` of `ℓ_{B_𝔮}(B_𝔮) · ord_{B ⧸ 𝔮}(a)`: by flatness the image of `a` is a non-zero-divisor of
`B`, and `ord_algebraMap_of_flat` and `ord_eq_finsum_minimalPrimes` compute its order in `B`
in two ways. -/
theorem ord_mul_length_eq_finsum_minimalPrimes [IsNoetherianRing B] [_root_.Ring.KrullDimLE 1 B]
    {a : A} (ha : a ∈ A⁰) :
    _root_.Ring.ord A a * Module.length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) =
      ∑ᶠ 𝔮 : {𝔮 : PrimeSpectrum B // 𝔮.asIdeal ∈ minimalPrimes B},
        Module.length (Localization.AtPrime 𝔮.1.asIdeal) (Localization.AtPrime 𝔮.1.asIdeal) *
          _root_.Ring.ord (B ⧸ 𝔮.1.asIdeal) (Ideal.Quotient.mk _ (algebraMap A B a)) := by
  have hreg : IsSMulRegular B a := Module.Flat.isSMulRegular_of_nonZeroDivisors ha
  refine (ord_algebraMap_of_flat a).symm.trans (ord_eq_finsum_minimalPrimes ?_)
  refine mem_nonZeroDivisors_iff_right.mpr fun x hx => hreg ?_
  change a • x = a • (0 : B)
  rw [smul_zero, Algebra.smul_def, mul_comm, hx]

end Ring

namespace AlgebraicGeometry.Chow

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Flat pullback multiplies orders of vanishing by the fibre length.** For `f : X ⟶ Y` flat
and `x : X`, a germ `a` at `f x` pulled back to `x` has order of vanishing
`ord_{𝒪_{X,x}}(f^# a) = ord_{𝒪_{Y,f x}}(a) · fiberLength f x` (`Ring.ord_algebraMap_of_flat` for
the flat local map `𝒪_{Y,f x} → 𝒪_{X,x}`). -/
theorem ord_stalkMap [Flat f] (x : X) (a : Y.presheaf.stalk (f x)) :
    _root_.Ring.ord (X.presheaf.stalk x) (f.stalkMap x a) =
      _root_.Ring.ord (Y.presheaf.stalk (f x)) a * fiberLength f x := by
  let := (f.stalkMap x).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  exact Ring.ord_algebraMap_of_flat a

/-- The fibre length of an open immersion is `1`: its stalk maps are isomorphisms, so the
fibre's local ring at `x` is the residue field `κ(x)`. -/
theorem fiberLength_of_isOpenImmersion (j : X ⟶ Y) [IsOpenImmersion j] (x : X) :
    fiberLength j x = 1 := by
  rw [fiberLength, IsLocalRing.map_maximalIdeal_of_surjective _
    (ConcreteCategory.bijective_of_isIso (j.stalkMap x)).2]
  have := isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal
    (X.presheaf.stalk x)).out
  exact Module.length_eq_one _ _

/-- **Flat pullback along an open immersion is restriction**: for an open immersion
`j : X ⟶ Y` into a locally Noetherian scheme, `cycleFlatPullback j = cycleRestrict j`. Every point
is the generic point of its fibre (`j` is injective), with fibre length `1`
(`fiberLength_of_isOpenImmersion`). -/
theorem cycleFlatPullback_of_isOpenImmersion [IsLocallyNoetherian X] (j : X ⟶ Y)
    [IsOpenImmersion j] (α : AlgebraicCycle Y ℤ) :
    cycleFlatPullback j α = cycleRestrict j α := by
  ext x
  have hmax : Maximal (· ∈ j ⁻¹' {j x}) x :=
    ⟨rfl, fun z hz _ ↦ (j.isOpenEmbedding.injective hz).le⟩
  rw [cycleFlatPullback_apply, ite_eq_left hmax, fiberLength_of_isOpenImmersion,
    cycleRestrict_apply]
  simp

end AlgebraicGeometry.Chow

end TauCeti
