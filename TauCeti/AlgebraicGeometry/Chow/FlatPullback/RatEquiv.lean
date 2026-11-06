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
import TauCeti.RingTheory.OrderOfVanishing
import TauCeti.AlgebraicGeometry.Scheme.StalkSpecializes
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order
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
* `TauCeti.AlgebraicGeometry.Scheme.stalkMinimalPrime_bijective`: the minimal primes of
  `𝒪_{X,y}` correspond to the generic points of the irreducible components through `y`;
* `TauCeti.AlgebraicGeometry.Scheme.ord_stalkMap_of_isClosedImmersion`: for an integral closed
  subscheme `Z`, orders of vanishing in `𝒪_{Z,z}` are orders in the quotient of `𝒪_{X,z}` by the
  prime of the generic point of `Z` (`Scheme.ker_stalkMap_eq_comap_maximalIdeal`);
* `TauCeti.AlgebraicGeometry.Scheme.ord_functionFieldMap_div_algebraMap_stalk`: for such a `Z`
  and `h : X ⟶ W` with `Z ⟶ W` dominant, the order on `Z` of the pullback of a rational function
  `a / b` on `W` is a difference of orders in that quotient
  (`Scheme.ord_functionFieldMap_algebraMap_stalk`); `Chow.isDominant_subschemeι_pullback_snd`:
  the reduced components of `X ×_Y W` dominate `W` for `f` flat;
* `TauCeti.AlgebraicGeometry.Chow.ord_mul_fiberLength_eq_finsum`: for `f` flat over an integral
  scheme, `ord(a) · fiberLength f y` is the sum over the components through `y`, with generic
  points `x`, of `fiberLength f x` times the order of `a` along the component;
* `TauCeti.AlgebraicGeometry.Chow.ord_stalkMap`: for `f : X ⟶ Y` flat and `x : X`, pulling a
  germ `a` at `f x` back to `x` multiplies its order of vanishing by `fiberLength f x`;
* `TauCeti.AlgebraicGeometry.Chow.fiberLength_of_apply_eq_genericPoint`: over the generic point
  of an integral scheme, `fiberLength f x` is the length of `𝒪_{X,x}`;
* `TauCeti.AlgebraicGeometry.Scheme.ker_stalkMap_pullback_fst_le`: for a closed immersion
  `W ⟶ Y`, the kernel of `𝒪_{X,x} ↠ 𝒪_{X ×_Y W,x}` lies in `𝔪_{f x} 𝒪_{X,x}`;
* `TauCeti.AlgebraicGeometry.Chow.fiberLength_pullback_snd`: for `f` flat and `i : W ⟶ Y` a
  closed immersion, the base change `X ×_Y W ⟶ W` has the fibre lengths of `f`;
* `TauCeti.AlgebraicGeometry.Chow.height_eq_height_genericPoint_add`: for `f` flat of pure
  relative dimension `n` over an integral scheme `Y`, every irreducible component of `X` has
  dimension `dim Y + n`; `height_eq_height_genericPoint_add_of_pullback`: the components of
  `X ×_Y W`, for an integral closed subscheme `W` of `Y`, have dimension `dim W + n`;
  `height_snd_eq_and_maximal_of_height_eq`: for `W` of dimension `k + 1`, a point of `X ×_Y W` of
  dimension `k + n` off the generic fibre lies over a point of `W` of dimension `k` and is generic
  in its fibre under `f`;
* `TauCeti.AlgebraicGeometry.Chow.ringKrullDim_stalk_pullback_le_one`: for `f` of pure relative
  dimension `n` and a closed subscheme `W` of dimension at most `k + 1`, the local rings of
  `X ×_Y W` at points of dimension `k + n` have dimension at most one
  (`Scheme.ringKrullDim_stalk_le_one`);
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

/-- **Stalks of an integral closed subscheme.** For a closed immersion `i : Z ⟶ X` of an
integral scheme and `z : Z`, the kernel of `𝒪_{X,i z} ↠ 𝒪_{Z,z}` is the prime of `𝒪_{X,i z}`
attached to the image of the generic point of `Z`: `𝒪_{Z,z}` embeds into the function field
`𝒪_{Z,η}`, and the kernel of `𝒪_{X,i η} ↠ 𝒪_{Z,η}` is the maximal ideal. -/
theorem ker_stalkMap_eq_comap_maximalIdeal {Z : Scheme.{u}} [IsIntegral Z] (i : Z ⟶ X)
    [IsClosedImmersion i] (z : Z) :
    RingHom.ker (i.stalkMap z).hom =
      (maximalIdeal (X.presheaf.stalk (i (genericPoint Z)))).comap
        (X.presheaf.stalkSpecializes
          (i.base.hom.map_specializes ((genericPoint_spec Z).specializes trivial))).hom := by
  set hη : genericPoint Z ⤳ z := (genericPoint_spec Z).specializes trivial
  have hinj : Function.Injective (Z.presheaf.stalkSpecializes hη).hom :=
    IsFractionRing.injective (Z.presheaf.stalk z) Z.functionField
  have hmax : RingHom.ker (i.stalkMap (genericPoint Z)).hom =
      maximalIdeal (X.presheaf.stalk (i (genericPoint Z))) :=
    have := RingHom.ker_isMaximal_of_surjective _ (i.stalkMap_surjective (genericPoint Z))
    IsLocalRing.eq_maximalIdeal this
  ext a
  rw [← hmax, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker,
    i.stalkSpecializes_stalkMap_apply _ _ hη, map_eq_zero_iff _ hinj]

/-- For a closed immersion `i : Z ⟶ X` of an integral scheme, the order of vanishing of a germ
`a` at `i z` pulled back to `𝒪_{Z,z}` is its order in the quotient of `𝒪_{X,i z}` by the prime
of the generic point of `Z` (`ker_stalkMap_eq_comap_maximalIdeal`). This identifies the factor
`ord_{B ⧸ 𝔮}(a)` of `Ring.ord_mul_length_eq_finsum_minimalPrimes` with an order of vanishing on a
component. -/
theorem ord_stalkMap_of_isClosedImmersion {Z : Scheme.{u}} [IsIntegral Z] (i : Z ⟶ X)
    [IsClosedImmersion i] (z : Z) (a : X.presheaf.stalk (i z)) :
    _root_.Ring.ord (Z.presheaf.stalk z) (i.stalkMap z a) =
      _root_.Ring.ord (X.presheaf.stalk (i z) ⧸ (maximalIdeal
          (X.presheaf.stalk (i (genericPoint Z)))).comap (X.presheaf.stalkSpecializes
            (i.base.hom.map_specializes ((genericPoint_spec Z).specializes trivial))).hom)
        (Ideal.Quotient.mk _ a) := by
  let σ := (Ideal.quotEquivOfEq (ker_stalkMap_eq_comap_maximalIdeal i z).symm).trans
    (RingHom.quotientKerEquivOfSurjective (i.stalkMap_surjective z))
  have hσ : σ (Ideal.Quotient.mk _ a) = i.stalkMap z a := by
    simp only [σ, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [← hσ, Ring.ord_ringEquiv]

/-- **Orders along an integral closed subscheme, through a dominant map.** Let `ι : Z ⟶ X` be a
closed immersion of a locally Noetherian integral scheme, with generic point mapping to `η`, and
`h : X ⟶ W` a morphism to an integral scheme with `ι ≫ h` dominant. At a codimension-one point
`z` of `Z`, the order of the pullback to `K(Z)` of a nonzero germ `a` at `h (ι z)` is the order of
`h^# a` in the quotient of `𝒪_{X,ι z}` by the prime of `η` (`ord_stalkMap_of_isClosedImmersion`).
This is the factor `ord_{B ⧸ 𝔮}` of `Chow.ord_mul_fiberLength_eq_finsum` for a component `Z` of
`X`. -/
theorem ord_functionFieldMap_algebraMap_stalk {Z W : Scheme.{u}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsIntegral W] (ι : Z ⟶ X) [IsClosedImmersion ι] (h : X ⟶ W)
    [IsDominant (ι ≫ h)] {z : Z} (hz : Order.coheight z = 1) {η : X}
    (hgen : ι (genericPoint Z) = η) (hη : η ⤳ ι z) {a : W.presheaf.stalk (h (ι z))} (ha : a ≠ 0) :
    Z.ord ((ι ≫ h).functionFieldMap.hom (algebraMap _ W.functionField a)) z =
      (_root_.Ring.ord (X.presheaf.stalk (ι z) ⧸ (maximalIdeal (X.presheaf.stalk η)).comap
          (X.presheaf.stalkSpecializes hη).hom)
        (Ideal.Quotient.mk _ (h.stalkMap (ι z) a))).toNat := by
  subst hgen
  have hmap : (ι ≫ h).functionFieldMap.hom (algebraMap _ W.functionField a) =
      algebraMap (Z.presheaf.stalk z) Z.functionField ((ι ≫ h).stalkMap z a) :=
    (ι ≫ h).functionFieldMap_algebraMap_stalk z a
  have hne : (ι ≫ h).stalkMap z a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hmap
    exact ha ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp
      ((map_eq_zero_iff _ (RingHom.injective _)).mp hmap))
  have hcomp : (ι ≫ h).stalkMap z a = ι.stalkMap z (h.stalkMap (ι z) a) := by
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  rw [hmap, ord_algebraMap_stalk hz hne, hcomp, ord_stalkMap_of_isClosedImmersion]

/-- The quotient form of `ord_functionFieldMap_algebraMap_stalk`: a rational function `a / b` on
`W`, with `a` and `b` nonzero germs at `h (ι z)`, pulls back to a rational function on `Z` whose
order at `z` is the difference of the orders of `h^# a` and `h^# b` along `Z`. Every rational
function on `W` has this form (`IsFractionRing.div_surjective`). -/
theorem ord_functionFieldMap_div_algebraMap_stalk {Z W : Scheme.{u}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsIntegral W] (ι : Z ⟶ X) [IsClosedImmersion ι] (h : X ⟶ W)
    [IsDominant (ι ≫ h)] {z : Z} (hz : Order.coheight z = 1) {η : X}
    (hgen : ι (genericPoint Z) = η) (hη : η ⤳ ι z) {a b : W.presheaf.stalk (h (ι z))} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    Z.ord ((ι ≫ h).functionFieldMap.hom
        (algebraMap _ W.functionField a / algebraMap _ W.functionField b)) z =
      (_root_.Ring.ord (X.presheaf.stalk (ι z) ⧸ (maximalIdeal (X.presheaf.stalk η)).comap
          (X.presheaf.stalkSpecializes hη).hom)
        (Ideal.Quotient.mk _ (h.stalkMap (ι z) a))).toNat -
      (_root_.Ring.ord (X.presheaf.stalk (ι z) ⧸ (maximalIdeal (X.presheaf.stalk η)).comap
          (X.presheaf.stalkSpecializes hη).hom)
        (Ideal.Quotient.mk _ (h.stalkMap (ι z) b))).toNat := by
  have hne {c : W.presheaf.stalk (h (ι z))} (hc : c ≠ 0) :
      (ι ≫ h).functionFieldMap.hom (algebraMap _ W.functionField c) ≠ 0 :=
    (map_ne_zero_iff _ (RingHom.injective _)).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hc)
  rw [map_div₀, div_eq_mul_inv, Scheme.ord_mul (hne ha) (inv_ne_zero (hne hb)), Scheme.ord_inv,
    ord_functionFieldMap_algebraMap_stalk ι h hz hgen hη ha,
    ord_functionFieldMap_algebraMap_stalk ι h hz hgen hη hb, sub_eq_add_neg]

/-- The minimal prime of `𝒪_{X,y}` attached to a generization `x` of `y` without proper
generization (the generic point of an irreducible component through `y`). -/
noncomputable def stalkMinimalPrime (y : X) (x : {x : X // x ⤳ y ∧ ∀ x' : X, x' ⤳ x → x ⤳ x'}) :
    {𝔮 : PrimeSpectrum (X.presheaf.stalk y) // 𝔮.asIdeal ∈ minimalPrimes (X.presheaf.stalk y)} :=
  ⟨⟨(maximalIdeal (X.presheaf.stalk x.1)).comap (X.presheaf.stalkSpecializes x.2.1).hom,
    inferInstance⟩, (comap_stalkSpecializes_maximalIdeal_mem_minimalPrimes_iff x.2.1).2 x.2.2⟩

/-- **Minimal primes of a stalk are the components through the point.** The minimal primes of
`𝒪_{X,y}` correspond bijectively to the generic points of the irreducible components of `X`
through `y`. -/
theorem stalkMinimalPrime_bijective (y : X) : Function.Bijective (stalkMinimalPrime y) := by
  refine ⟨fun x x' h ↦ ?_, fun 𝔮 ↦ ?_⟩
  · have h : (stalkMinimalPrime y x).1.asIdeal = (stalkMinimalPrime y x').1.asIdeal := by rw [h]
    exact Subtype.ext ((specializes_of_comap_stalkSpecializes_maximalIdeal_le x.2.1 x'.2.1
      h.le).antisymm (specializes_of_comap_stalkSpecializes_maximalIdeal_le x'.2.1 x.2.1
        h.ge)).eq
  · obtain ⟨x, hx, h⟩ := exists_comap_stalkSpecializes_maximalIdeal_eq 𝔮.1.asIdeal
    have hmin := 𝔮.2
    rw [← h] at hmin
    exact ⟨⟨x, hx, (comap_stalkSpecializes_maximalIdeal_mem_minimalPrimes_iff hx).1 hmin⟩,
      Subtype.ext (PrimeSpectrum.ext h)⟩

/-- **Stalks of a closed subscheme.** For a closed immersion `p : Z ⟶ X` and an affine open `U`
of `X` containing `p z`, the kernel of `𝒪_{X,p z} ↠ 𝒪_{Z,z}` lies in the ideal generated by the
sections `I(U)` of the ideal sheaf of `p`: a germ `s / t` killed in `𝒪_{Z,z}` is killed on
`p⁻¹ U` by some `p(m)` with `m` a unit at `p z`, so `m s ∈ I(U)`. -/
theorem ker_stalkMap_le_map_ideal_ker {Z : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p] (z : Z)
    (U : X.affineOpens) (hz : p z ∈ U.1) :
    RingHom.ker (p.stalkMap z).hom ≤ (p.ker.ideal U).map (X.presheaf.germ U (p z) hz).hom := by
  intro a ha
  let := X.presheaf.algebra_section_stalk ⟨p z, hz⟩
  have := U.2.isLocalization_stalk ⟨p z, hz⟩
  obtain ⟨⟨s, t⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (U.2.primeIdealOf ⟨p z, hz⟩).asIdeal.primeCompl a
  have hs : p.stalkMap z (X.presheaf.germ U (p z) hz s) = 0 := by
    have : X.presheaf.germ U (p z) hz s =
        algebraMap Γ(X, U) (X.presheaf.stalk (p z)) t *
          IsLocalization.mk' (X.presheaf.stalk (p z)) s t :=
      (IsLocalization.mk'_spec' _ s t).symm
    rw [this, map_mul, RingHom.mem_ker.mp ha, mul_zero]
  rw [Scheme.Hom.germ_stalkMap_apply] at hs
  have hV : IsAffineOpen (p ⁻¹ᵁ U.1) := U.2.preimage p
  have hz' : z ∈ p ⁻¹ᵁ U.1 := hz
  let := Z.presheaf.algebra_section_stalk ⟨z, hz'⟩
  have := hV.isLocalization_stalk ⟨z, hz'⟩
  obtain ⟨⟨m, hm⟩, hm0⟩ :=
    (IsLocalization.map_eq_zero_iff (hV.primeIdealOf ⟨z, hz'⟩).asIdeal.primeCompl _ _).mp hs
  obtain ⟨m', rfl⟩ := p.app_surjective U.1 U.2 m
  have hm' : IsUnit (X.presheaf.germ U (p z) hz m') := by
    refine isUnit_of_map_unit (p.stalkMap z).hom _ ?_
    rw [Scheme.Hom.germ_stalkMap_apply]
    exact IsLocalization.map_units (M := (hV.primeIdealOf ⟨z, hz'⟩).asIdeal.primeCompl)
      (Z.presheaf.stalk z) ⟨_, hm⟩
  have hu : IsUnit (X.presheaf.germ U (p z) hz m' * algebraMap Γ(X, U) _ t) :=
    hm'.mul (IsLocalization.map_units _ t)
  have hmem : m' * s ∈ p.ker.ideal U := by
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker, map_mul]
    exact hm0
  have key : X.presheaf.germ U (p z) hz m' * algebraMap Γ(X, U) _ t *
      IsLocalization.mk' (X.presheaf.stalk (p z)) s t = X.presheaf.germ U (p z) hz (m' * s) := by
    rw [mul_assoc, IsLocalization.mk'_spec', map_mul]
    rfl
  change IsLocalization.mk' _ s t ∈ _
  rw [← hu.unit.inv_mul_cancel_left (IsLocalization.mk' _ s t)]
  refine Ideal.mul_mem_left _ _ ?_
  rw [IsUnit.unit_spec, key]
  exact Ideal.mem_map_of_mem _ hmem

/-- A section in the kernel of `i.app U` has germs in the maximal ideal at every point of `U` in
the image of `i`. -/
theorem germ_mem_maximalIdeal_of_mem_ker_app {W Y : Scheme.{u}} (i : W ⟶ Y)
    (U : Y.affineOpens) {s : Γ(Y, U)} (hs : s ∈ RingHom.ker (i.app U).hom) {y : Y} (hyU : y ∈ U.1)
    (hy : y ∈ Set.range i) :
    Y.presheaf.germ U y hyU s ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
  obtain ⟨w, rfl⟩ := hy
  refine fun hu ↦ not_isUnit_zero (M₀ := W.presheaf.stalk w) ?_
  have := hu.map (i.stalkMap w).hom
  rwa [Scheme.Hom.germ_stalkMap_apply, RingHom.mem_ker.mp hs, map_zero] at this

open Limits in
/-- **Stalks of a base change along a closed immersion.** For `i : W ⟶ Y` a closed immersion and
`x` a point of `X ×_Y W`, the kernel of `𝒪_{X,x} ↠ 𝒪_{X ×_Y W,x}` lies in `𝔪_{f x} 𝒪_{X,x}`: the
ideal sheaf of `X ×_Y W` is the inverse image of that of `W`
(`IdealSheafData.ker_fst_of_isClosedImmersion`), whose sections vanish at `f x ∈ W`. -/
theorem ker_stalkMap_pullback_fst_le {Y W : Scheme.{u}} (f : X ⟶ Y) (i : W ⟶ Y)
    [IsClosedImmersion i] (x : ↥(pullback f i)) :
    RingHom.ker ((pullback.fst f i).stalkMap x).hom ≤
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (pullback.fst f i x)))).map
        (f.stalkMap (pullback.fst f i x)).hom := by
  set x₀ := pullback.fst f i x
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show f x₀ ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨V, hV, hxV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (show x₀ ∈ f ⁻¹ᵁ U from hyU)
  have hrange : f x₀ ∈ Set.range i := ⟨pullback.snd f i x, by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩
  have hg : f.appLE U V hVU ≫ X.presheaf.germ V x₀ hxV =
      Y.presheaf.germ U (f x₀) hyU ≫ f.stalkMap x₀ := by
    simp [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE]
  refine (ker_stalkMap_le_map_ideal_ker (pullback.fst f i) x ⟨V, hV⟩ hxV).trans ?_
  rw [_root_.AlgebraicGeometry.Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_le _ f ⟨U, hU⟩ ⟨V, hV⟩ hVU,
    Ideal.map_map, ← CommRingCat.hom_comp, hg, CommRingCat.hom_comp, ← Ideal.map_map]
  refine Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr fun s hs ↦ ?_)
  rw [Scheme.Hom.ker_apply] at hs
  exact germ_mem_maximalIdeal_of_mem_ker_app i ⟨U, hU⟩ hs hyU hrange

/-- At a point `x` of height `m` on a scheme all of whose points have height at most `m + 1`, the
local ring has dimension at most one: `height x + coheight x` is at most the dimension of `X`. -/
theorem ringKrullDim_stalk_le_one {m : ℕ} (hx : Order.height x = m)
    (h : ∀ z : X, Order.height z ≤ m + 1) : ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  have : Nonempty X := ⟨x⟩
  have hle : (↑(Order.height x + Order.coheight x) : WithBot ℕ∞) ≤ ↑((m : ℕ∞) + 1) :=
    calc (↑(Order.height x + Order.coheight x) : WithBot ℕ∞)
        ≤ Order.krullDim X := Order.krullDim_eq_iSup_height_add_coheight_of_nonempty (α := X) ▸
          WithBot.coe_le_coe.mpr (le_iSup (fun a : X ↦ Order.height a + Order.coheight a) x)
      _ ≤ ↑((m : ℕ∞) + 1) := Order.krullDim_eq_iSup_height_of_nonempty (α := X) ▸
          WithBot.coe_le_coe.mpr (iSup_le h)
  rw [hx] at hle
  rw [ringKrullDim_stalk_eq_coheight]
  exact_mod_cast (ENat.add_le_add_iff_left (ENat.natCast_ne_top m)).mp (WithBot.coe_le_coe.mp hle)

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

/-- A flat morphism to an integral scheme sends every point without proper generization (the
generic point of an irreducible component) to the generic point: flat morphisms are generizing
(`Flat.generalizingMap`). -/
theorem apply_eq_genericPoint_of_forall_specializes [Flat f] [IsIntegral Y] {x : X}
    (hx : ∀ x' : X, x' ⤳ x → x ⤳ x') : f x = genericPoint Y := by
  obtain ⟨x', hx', hx'Y⟩ :=
    Flat.generalizingMap f ((genericPoint_spec Y).specializes (Set.mem_univ (f x)))
  exact ((((hx x' hx').map f.continuous).trans (specializes_of_eq hx'Y)).antisymm
    ((genericPoint_spec Y).specializes trivial)).eq

open Limits in
/-- **The components of `X ×_Y W` dominate `W`.** For `f` flat, `i : W ⟶ Y` with `W` integral
and `η` the generic point of an irreducible component of `X ×_Y W`, the reduced closure of `η`
maps dominantly to `W`: `η` lies over the generic point of `W`
(`apply_eq_genericPoint_of_forall_specializes` for the flat base change). Rational functions on
`W` pull back along this map to the components of `f⁻¹(W)`
(`Scheme.ord_functionFieldMap_div_algebraMap_stalk`). -/
theorem isDominant_subschemeι_pullback_snd [Flat f] {W : Scheme.{u}} [IsIntegral W] (i : W ⟶ Y)
    {η : ↥(pullback f i)} (hη : ∀ x' : ↥(pullback f i), x' ⤳ η → η ⤳ x') :
    IsDominant ((Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩).subschemeι ≫
      pullback.snd f i) := by
  rw [isDominant_iff_genericPoint_eq]
  exact (congrArg (pullback.snd f i).base
    (Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure_singleton η)).trans
    (apply_eq_genericPoint_of_forall_specializes (pullback.snd f i) hη)

/-- Let `f : X ⟶ Y` be flat of pure relative dimension `n` between schemes locally of finite type
over a field `K`, with `Y` integral. Every irreducible component of `X`, with generic point `x`,
has dimension `dim Y + n`: `x` lies over the generic point of `Y`
(`apply_eq_genericPoint_of_forall_specializes`) and is a generic point of its fibre
(`height_eq_height_add`). -/
theorem height_eq_height_genericPoint_add (K : Type u) [Field K] [X.Over (Spec (.of K))]
    [Y.Over (Spec (.of K))] [f.IsOver (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [Flat f] [IsIntegral Y] {n : ℕ}
    [PureRelativeDimension n f] {x : X} (hx : ∀ x' : X, x' ⤳ x → x ⤳ x') :
    Order.height x = Order.height (genericPoint Y) + n := by
  rw [← apply_eq_genericPoint_of_forall_specializes f hx]
  exact height_eq_height_add f K ⟨rfl, fun x' _ hx' ↦ hx x' hx'⟩

/-- For `f` flat over an integral scheme, at the generic point `x` of an irreducible component of
`X` the fibre length is the length of `𝒪_{X,x}`: this is the multiplicity of the component in
`f^*[Y]`. -/
theorem fiberLength_of_forall_specializes [Flat f] [IsIntegral Y] {x : X}
    (hx : ∀ x' : X, x' ⤳ x → x ⤳ x') :
    fiberLength f x = Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) :=
  fiberLength_of_apply_eq_genericPoint f (apply_eq_genericPoint_of_forall_specializes f hx)

/-- If `g : Z ⟶ X` is surjective on the stalk at `z` and its kernel there lies in
`𝔪_{f (g z)} 𝒪_{X,g z}`, then `g` does not change the fibre length:
`𝒪_{Z,z} ⧸ 𝔪 𝒪_{Z,z}` is `𝒪_{X,g z} ⧸ 𝔪 𝒪_{X,g z}`. -/
theorem fiberLength_comp_of_ker_le {Z : Scheme.{u}} (g : Z ⟶ X) (z : Z)
    (hg : Function.Surjective (g.stalkMap z))
    (h : RingHom.ker (g.stalkMap z).hom ≤
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (g z)))).map (f.stalkMap (g z)).hom) :
    fiberLength (g ≫ f) z = fiberLength f (g z) := by
  let := (g.stalkMap z).hom.toAlgebra
  set J := (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (g z)))).map (f.stalkMap (g z)).hom
  have hstalk : ((g ≫ f).stalkMap z).hom = (g.stalkMap z).hom.comp (f.stalkMap (g z)).hom := by
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  let φ : X.presheaf.stalk (g z) →ₐ[X.presheaf.stalk (g z)]
      Z.presheaf.stalk z ⧸ J.map (algebraMap (X.presheaf.stalk (g z)) (Z.presheaf.stalk z)) :=
    (Ideal.Quotient.mkₐ _ _).comp (Algebra.ofId _ _)
  have hg' : Function.Surjective (g.stalkMap z).hom := hg
  have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective.comp hg'
  have hker : RingHom.ker φ = J := by
    change RingHom.ker ((Ideal.Quotient.mk _).comp (g.stalkMap z).hom) = J
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    change Ideal.comap (g.stalkMap z).hom (J.map (g.stalkMap z).hom) = J
    rw [Ideal.comap_map_of_surjective _ hg', ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr h]
  calc fiberLength (g ≫ f) z
      = Module.length (Z.presheaf.stalk z)
          (Z.presheaf.stalk z ⧸ J.map (algebraMap (X.presheaf.stalk (g z)) _)) := by
        rw [fiberLength, hstalk]
        simp only [J]
        rw [Ideal.map_map]
        rfl
    _ = Module.length (X.presheaf.stalk (g z))
          (Z.presheaf.stalk z ⧸ J.map (algebraMap (X.presheaf.stalk (g z)) _)) :=
        (Module.length_eq_of_surjective hg').symm
    _ = fiberLength f (g z) :=
        ((Ideal.quotientEquivAlgOfEq _ hker.symm).trans
          (Ideal.quotientKerAlgEquivOfSurjective hφ)).toLinearEquiv.length_eq.symm

/-- A morphism surjective on the stalk at `w` has fibre length `1` there: the closed fibre of
`𝒪_{Y,i w} ↠ 𝒪_{W,w}` is the residue field of `𝒪_{W,w}`. -/
theorem fiberLength_eq_one_of_surjective {W : Scheme.{u}} (i : W ⟶ Y) (w : W)
    (hi : Function.Surjective (i.stalkMap w)) : fiberLength i w = 1 := by
  rw [fiberLength, IsLocalRing.map_maximalIdeal_of_surjective _ hi]
  have : IsSimpleModule (W.presheaf.stalk w) (W.presheaf.stalk w ⧸ IsLocalRing.maximalIdeal _) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  exact Module.length_eq_one _ _

open Limits in
/-- **Fibre lengths of a base change along a closed immersion.** For `f : X ⟶ Y` flat and
`i : W ⟶ Y` a closed immersion, the fibre length of the base change `X ×_Y W ⟶ W` at `x` is the
fibre length of `f` at the image of `x` in `X`: the kernel of `𝒪_{X,x} ↠ 𝒪_{X ×_Y W,x}` lies in
`𝔪_{f x} 𝒪_{X,x}` (`Scheme.ker_stalkMap_pullback_fst_le`), so both closed fibres agree
(`fiberLength_comp_of_ker_le`), and `W ⟶ Y` has fibre length `1`. With the generic-length
multiplicities of `cycleFlatPullback`, this identifies the multiplicity of a component of
`f⁻¹(W)` in `f^*[W]` with its multiplicity in the cycle of the scheme `X ×_Y W`. -/
theorem fiberLength_pullback_snd [Flat f] {W : Scheme.{u}} (i : W ⟶ Y) [IsClosedImmersion i]
    (x : ↥(pullback f i)) :
    fiberLength (pullback.snd f i) x = fiberLength f (pullback.fst f i x) := by
  have := fiberLength_comp (pullback.snd f i) i x
  rw [fiberLength_eq_one_of_surjective i _ (i.stalkMap_surjective _), mul_one, ← pullback.condition,
    fiberLength_comp_of_ker_le f _ x ((pullback.fst f i).stalkMap_surjective x)
      (Scheme.ker_stalkMap_pullback_fst_le f i x)] at this
  exact this.symm

open Limits in
/-- Let `f : X ⟶ Y` be flat of pure relative dimension `n` between schemes locally of finite type
over a field `K`, and `i : W ⟶ Y` a closed immersion of an integral scheme. Every irreducible
component of `X ×_Y W`, with generic point `x`, has dimension `dim W + n`: `x` lies over the generic
point of `W` (`apply_eq_genericPoint_of_forall_specializes` for the flat base change), so its image
in `X` is a generic point of a fibre of `f` (`height_eq_height_add`), and the closed immersions
`X ×_Y W ⟶ X` and `i` preserve heights. -/
theorem height_eq_height_genericPoint_add_of_pullback (K : Type u) [Field K]
    [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))] [f.IsOver (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [LocallyOfFiniteType (Y ↘ Spec (.of K))] [Flat f]
    {n : ℕ} [PureRelativeDimension n f] {W : Scheme.{u}} [IsIntegral W] (i : W ⟶ Y)
    [IsClosedImmersion i] {x : ↥(pullback f i)}
    (hx : ∀ x' : ↥(pullback f i), x' ⤳ x → x ⤳ x') :
    Order.height x = Order.height (genericPoint W) + n := by
  have hsnd : pullback.snd f i x = genericPoint W :=
    apply_eq_genericPoint_of_forall_specializes (pullback.snd f i) hx
  have hfx : f (pullback.fst f i x) = i (genericPoint W) := by
    rw [← hsnd, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hmax : Maximal (· ∈ f ⁻¹' {f (pullback.fst f i x)}) (pullback.fst f i x) := by
    refine ⟨rfl, fun y hy hxy ↦ ?_⟩
    obtain ⟨y', rfl⟩ : y ∈ Set.range (pullback.fst f i) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨genericPoint W, ((show f y = _ from hy).trans hfx).symm⟩
    have h : y' ⤳ x := (pullback.fst f i).isClosedEmbedding.isInducing.specializes_iff.mp hxy
    exact (hx y' h).map (pullback.fst f i).continuous
  rw [← Scheme.Hom.height_apply_eq_height (pullback.fst f i),
    height_eq_height_add f K (n := n) hmax, hfx, Scheme.Hom.height_apply_eq_height]

open Limits in
/-- **Points of dimension `k + n` on `X ×_Y W`.** Let `f : X ⟶ Y` be a morphism of pure relative
dimension `n` between schemes locally of finite type over a field `K`, and `i : W ⟶ Y` a closed
immersion of an integral scheme of dimension `k + 1`. A point `x` of `X ×_Y W` of dimension
`k + n` that does not lie over the generic point of `W` lies over a point of `W` of dimension `k`
(a codimension-one point, where `div r` may be supported), and its image in `X` is a generic point
of its fibre under `f` (`maximal_mem_preimage_singleton_of_height_asFiber_eq`): this is where
`cycleFlatPullback f` is supported. -/
theorem height_snd_eq_and_maximal_of_height_eq (K : Type u) [Field K]
    [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))] [f.IsOver (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [LocallyOfFiniteType (Y ↘ Spec (.of K))]
    {n k : ℕ} [PureRelativeDimension n f] {W : Scheme.{u}} [IsIntegral W] (i : W ⟶ Y)
    [IsClosedImmersion i] (hW : Order.height (genericPoint W) = k + 1) {x : ↥(pullback f i)}
    (hx : Order.height x = (k + n : ℕ)) (hgen : pullback.snd f i x ≠ genericPoint W) :
    Order.height (pullback.snd f i x) = k ∧
      Maximal (· ∈ f ⁻¹' {f (pullback.fst f i x)}) (pullback.fst f i x) := by
  have hz : f (pullback.fst f i x) = i (pullback.snd f i x) := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hle : pullback.snd f i x ≤ genericPoint W := (genericPoint_spec W).specializes trivial
  have htop : Order.height (genericPoint W) < ⊤ := by
    rw [hW]
    exact_mod_cast ENat.natCast_lt_top (k + 1)
  have hw : Order.height (pullback.snd f i x) ≤ k := by
    have hlt : pullback.snd f i x < genericPoint W := lt_of_le_not_ge hle fun h ↦
      hgen (Specializes.antisymm (h : pullback.snd f i x ⤳ genericPoint W) hle).eq
    have := Order.height_strictMono hlt ((Order.height_mono hle).trans_lt htop)
    rw [hW] at this
    exact (ENat.lt_add_one_iff (ENat.natCast_ne_top k)).mp this
  have hfib := height_asFiber_le (n := n) f (pullback.fst f i x)
  have hsum := height_eq_height_add_height_asFiber f K (pullback.fst f i x)
  have himg : Order.height (f (pullback.fst f i x)) = Order.height (pullback.snd f i x) := by
    rw [hz, Scheme.Hom.height_apply_eq_height]
  rw [Scheme.Hom.height_apply_eq_height, hx, himg] at hsum
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top k) hw)
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top n) hfib)
  rw [← ha] at hw hsum ⊢
  rw [← hb] at hfib hsum
  norm_cast at hw hfib hsum
  have hab : a = k ∧ b = n := by omega
  refine ⟨by rw [hab.1], maximal_mem_preimage_singleton_of_height_asFiber_eq (n := n) f ?_⟩
  rw [← hb, hab.2]

open Limits in
/-- Let `f : X ⟶ Y` be a morphism of pure relative dimension `n` between schemes locally of finite
type over a field `K`, and `i : W ⟶ Y` a closed immersion from a scheme all of whose points have
dimension at most `k + 1` (for instance an integral closed subscheme of dimension `k + 1`). At a
point of `X ×_Y W` of dimension `k + n`, the local ring has dimension at most one: every point of
`X ×_Y W` has dimension at most `k + 1 + n` (`height_le_height_add`), heights being preserved by
the closed immersions `X ×_Y W ⟶ X` and `i`. -/
theorem ringKrullDim_stalk_pullback_le_one (K : Type u) [Field K] [X.Over (Spec (.of K))]
    [Y.Over (Spec (.of K))] [f.IsOver (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] {n k : ℕ} [PureRelativeDimension n f]
    {W : Scheme.{u}} (i : W ⟶ Y) [IsClosedImmersion i] (hW : ∀ w : W, Order.height w ≤ k + 1)
    {x : ↥(pullback f i)} (hx : Order.height x = (k + n : ℕ)) :
    ringKrullDim ((pullback f i).presheaf.stalk x) ≤ 1 := by
  refine Scheme.ringKrullDim_stalk_le_one hx fun z ↦ ?_
  have hz : f (pullback.fst f i z) = i (pullback.snd f i z) := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  calc Order.height z = Order.height (pullback.fst f i z) :=
        (Scheme.Hom.height_apply_eq_height _ z).symm
    _ ≤ Order.height (f (pullback.fst f i z)) + n := height_le_height_add f K _
    _ = Order.height (pullback.snd f i z) + n := by
        rw [hz, Scheme.Hom.height_apply_eq_height]
    _ ≤ k + 1 + n := by gcongr; exact hW _
    _ = ↑(k + n) + 1 := by push_cast; ring

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

open scoped nonZeroDivisors in
/-- **Flat pullback of an order of vanishing, over the components** (the local form of Stacks,
Lemma 42.20.1). Let `f : X ⟶ Y` be flat over an integral scheme, `X` locally Noetherian, and
`y : X` with `𝒪_{X,y}` of dimension at most one. For a non-zero-divisor `a` of `𝒪_{Y,f y}`,
`ord(a) · fiberLength f y` is the sum, over the generic points `x` of the irreducible components of
`X` through `y`, of `fiberLength f x` times the order of `a` in the quotient of `𝒪_{X,y}` by the
prime of `x`. -/
theorem ord_mul_fiberLength_eq_finsum [Flat f] [IsIntegral Y] [IsLocallyNoetherian X] {y : X}
    [_root_.Ring.KrullDimLE 1 (X.presheaf.stalk y)] {a : Y.presheaf.stalk (f y)}
    (ha : a ∈ (Y.presheaf.stalk (f y))⁰) :
    _root_.Ring.ord (Y.presheaf.stalk (f y)) a * fiberLength f y =
      ∑ᶠ x : {x : X // x ⤳ y ∧ ∀ x' : X, x' ⤳ x → x ⤳ x'}, fiberLength f x *
        _root_.Ring.ord (X.presheaf.stalk y ⧸ (IsLocalRing.maximalIdeal
          (X.presheaf.stalk x.1)).comap (X.presheaf.stalkSpecializes x.2.1).hom)
          (Ideal.Quotient.mk _ (f.stalkMap y a)) := by
  let := (f.stalkMap y).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f y)) (X.presheaf.stalk y) := Flat.stalkMap f y
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f y)) (X.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
  refine (Ring.ord_mul_length_eq_finsum_minimalPrimes ha).trans
    (finsum_eq_of_bijective _ (Scheme.stalkMinimalPrime_bijective y) fun x ↦ ?_).symm
  rw [fiberLength_of_forall_specializes f x.2.2, ← length_localization_stalkSpecializes x.2.1]
  rfl

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
