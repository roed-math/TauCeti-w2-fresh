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
import TauCeti.Algebra.Module.Equiv.Length
import TauCeti.AlgebraicGeometry.Scheme.StalkSpecializes
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
* `TauCeti.AlgebraicGeometry.Scheme.comap_stalkSpecializes_maximalIdeal_mem_minimalPrimes_iff`:
  the minimal primes of `𝒪_{X,y}` are the primes of the generizations of `y` without proper
  generization (every prime comes from a generization,
  `Scheme.exists_comap_stalkSpecializes_maximalIdeal_eq`);
* `TauCeti.AlgebraicGeometry.Chow.ord_stalkMap`: for `f : X ⟶ Y` flat and `x : X`, pulling a
  germ `a` at `f x` back to `x` multiplies its order of vanishing by `fiberLength f x`;
* `TauCeti.AlgebraicGeometry.Chow.fiberLength_of_apply_eq_genericPoint`: over the generic point
  of an integral scheme, `fiberLength f x` is the length of `𝒪_{X,x}`;
* `TauCeti.AlgebraicGeometry.Chow.length_localization_stalkSpecializes`: for `x ⤳ y`, localizing
  `𝒪_{X,y}` at the prime of `x` does not change the length of `𝒪_{X,x}`;
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

namespace AlgebraicGeometry.Scheme

open IsLocalRing

variable {X : Scheme.{u}} {x y : X}

/-- **Every prime of a stalk comes from a generization.** Every prime `𝔮` of `𝒪_{X,y}` is the
prime lying under the maximal ideal of `𝒪_{X,x}` for some generization `x` of `y`: on an affine
open `Spec R` containing `y`, take `x` to be the point of `R` under `𝔮`. -/
theorem exists_comap_stalkSpecializes_maximalIdeal_eq (𝔮 : Ideal (X.presheaf.stalk y))
    [𝔮.IsPrime] :
    ∃ x : X, ∃ h : x ⤳ y,
      (maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom = 𝔮 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  replace hU : IsAffineOpen U := hU
  let := X.presheaf.algebra_section_stalk ⟨y, hyU⟩
  have := hU.isLocalization_stalk ⟨y, hyU⟩
  set P := hU.primeIdealOf ⟨y, hyU⟩
  -- The prime `q` of `Γ(X, U)` under `𝔮`, contained in the prime `P` of `y`.
  let q : Spec Γ(X, U) := ⟨𝔮.comap (algebraMap Γ(X, U) _), inferInstance⟩
  have hqP : q.asIdeal ≤ P.asIdeal := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk y) P.asIdeal]
    exact Ideal.comap_mono (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))
  have hxy : hU.fromSpec q ⤳ y :=
    (((PrimeSpectrum.le_iff_specializes q P).mp hqP).map hU.fromSpec.continuous).trans
      (specializes_of_eq (hU.fromSpec_primeIdealOf ⟨y, hyU⟩))
  have hprime : hU.primeIdealOf ⟨_, hxy.mem_open U.isOpen hyU⟩ = q :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
  refine ⟨_, hxy, ?_⟩
  -- Both primes of the localization `𝒪_{X,y}` pull back to `q` on `Γ(X, U)`.
  rw [← IsLocalization.map_under P.asIdeal.primeCompl (X.presheaf.stalk y)
      ((maximalIdeal _).comap (X.presheaf.stalkSpecializes hxy).hom),
    ← IsLocalization.map_under P.asIdeal.primeCompl (X.presheaf.stalk y) 𝔮]
  congr 1
  exact (comap_germ_comap_stalkSpecializes_maximalIdeal hU hyU hxy).trans (congrArg _ hprime)

/-- The primes of `𝒪_{X,y}` attached to generizations of `y` are ordered as the generizations
are: if `x ⤳ x'`, the prime of `x` is contained in the prime of `x'`. -/
theorem comap_stalkSpecializes_maximalIdeal_mono {x' : X} (h : x ⤳ y)
    (h' : x' ⤳ y) (hxx' : x ⤳ x') :
    (maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom ≤
      (maximalIdeal (X.presheaf.stalk x')).comap (X.presheaf.stalkSpecializes h').hom := by
  have hcomp : X.presheaf.stalkSpecializes h = X.presheaf.stalkSpecializes h' ≫
      X.presheaf.stalkSpecializes hxx' := (TopCat.Presheaf.stalkSpecializes_comp _ _ _).symm
  rw [hcomp, CommRingCat.hom_comp, ← Ideal.comap_comap]
  refine Ideal.comap_mono (le_maximalIdeal ?_)
  exact (Ideal.comap_isPrime _ (maximalIdeal (X.presheaf.stalk x))).ne_top

/-- **Minimal primes of a stalk.** For a generization `x` of `y`, the prime of `𝒪_{X,y}`
attached to `x` is minimal exactly when `x` has no proper generization, that is, when `x` is the
generic point of an irreducible component through `y`. -/
theorem comap_stalkSpecializes_maximalIdeal_mem_minimalPrimes_iff (h : x ⤳ y) :
    (maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom ∈
        minimalPrimes (X.presheaf.stalk y) ↔ ∀ x' : X, x' ⤳ x → x ⤳ x' := by
  refine ⟨fun hmin x' hx' ↦ ?_, fun H ↦ ⟨⟨inferInstance, bot_le⟩, fun 𝔮 h𝔮 hle ↦ ?_⟩⟩
  · refine specializes_of_comap_stalkSpecializes_maximalIdeal_le h (hx'.trans h) ?_
    exact hmin.2 ⟨inferInstance, bot_le⟩
      (comap_stalkSpecializes_maximalIdeal_mono (hx'.trans h) h hx')
  · have := h𝔮.1
    obtain ⟨x', hx', rfl⟩ := exists_comap_stalkSpecializes_maximalIdeal_eq 𝔮
    exact comap_stalkSpecializes_maximalIdeal_mono h hx'
      (H x' (specializes_of_comap_stalkSpecializes_maximalIdeal_le hx' h hle))

end AlgebraicGeometry.Scheme

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

/-- Over a point whose local ring is a field (for instance the generic point of an integral
scheme), the closed fibre of `𝒪_{f x} → 𝒪_{X,x}` is all of `𝒪_{X,x}`, so `fiberLength f x` is the
length of the local ring `𝒪_{X,x}`. This identifies the multiplicity of a component `W'` of
`f⁻¹(W)` in `f^*[W]` with the length of `𝒪_{f⁻¹(W),η'}` at its generic point `η'`. -/
theorem fiberLength_of_maximalIdeal_eq_bot {x : X}
    (h : IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)) = ⊥) :
    fiberLength f x = Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  rw [fiberLength, h, Ideal.map_bot]
  exact (Submodule.quotEquivOfEqBot _ rfl).length_eq

/-- Over the generic point of an integral scheme, `fiberLength f x` is the length of `𝒪_{X,x}`
(the local ring at the generic point is the function field). -/
theorem fiberLength_of_apply_eq_genericPoint [IsIntegral Y] {x : X} (hx : f x = genericPoint Y) :
    fiberLength f x = Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  refine fiberLength_of_maximalIdeal_eq_bot f ?_
  have : ∀ y : Y, y = genericPoint Y → IsLocalRing.maximalIdeal (Y.presheaf.stalk y) = ⊥ := by
    rintro y rfl
    exact IsLocalRing.maximalIdeal_eq_bot (R := Y.functionField)
  exact this _ hx

/-- **Lengths of stalks at generizations.** For a specialization `x ⤳ y`, the length of the
localization of `𝒪_{X,y}` at the prime of `x` is the length of `𝒪_{X,x}`
(`Scheme.isLocalization_stalkSpecializes`). For a minimal prime `𝔮` of `𝒪_{X,y}` this computes the
weight `ℓ(B_𝔮)` of `Ring.ord_mul_length_eq_finsum_minimalPrimes` as a length at the generic point
of a component through `y`. -/
theorem length_localization_stalkSpecializes {x y : X} (h : x ⤳ y) :
    Module.length
        (Localization.AtPrime ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap
          (X.presheaf.stalkSpecializes h).hom))
        (Localization.AtPrime ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap
          (X.presheaf.stalkSpecializes h).hom)) =
      Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  let := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have := Scheme.isLocalization_stalkSpecializes h
  exact (IsLocalization.algEquiv (Ideal.primeCompl ((IsLocalRing.maximalIdeal
    (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom)) _
      (X.presheaf.stalk x)).toRingEquiv.length_self_eq

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
