/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localizing a fibre product of rings away from an element

Let `f : R →+* C` and `h : A →+* C` be ring maps, and let `P = R ×_C A` be their fibre product,
Mathlib's `RingHom.eqLocus (f.comp (RingHom.fst R A)) (h.comp (RingHom.snd R A))` (the ring
underlying `CommRingCat.pullbackCone f h`). For `x = (g, b)` in `P`, if `f` becomes an isomorphism
`R_g ≅ C_{f g}` after inverting `g`, then the second projection `P → A` becomes an isomorphism
`P_x ≅ A_b`: the fibre product of `R_g ≅ C_{f g}` with `A_b → C_{f g}` is `A_b`, and localization
commutes with fibre products.

This is the ring-theoretic step of Stacks, Lemma 32.5.2 (01Z9), in which `R → C` is the restriction
`R → Γ(V, 𝒪)` to a quasi-compact open `V ⊆ Spec R`, `g` ranges over elements with `D(g) ⊆ V`, and
`A` is the ring of global sections of a model of `V` of finite type over `ℤ`: there, the lemma shows
that the model is an open subscheme of `Spec (R ×_{Γ(V, 𝒪)} A)`.

## Main results

* `TauCeti.isLocalization_away_eqLocus_of_bijective_awayMap`: `A_b` is the localization of
  `R ×_C A` away from `(g, b)` if `R_g → C_{f g}` is bijective.
-/

@[expose] public section

namespace TauCeti

variable {R A C : Type*} [CommRing R] [CommRing A] [CommRing C] {f : R →+* C} {h : A →+* C}

/-- If `f : R →+* C` becomes bijective after inverting `g`, then for `x = (g, b)` in the fibre
product `R ×_C A` of `f` and `h : A →+* C`, any localization `B` of `A` away from `b` is, through
the second projection, the localization of `R ×_C A` away from `x`. Part of Stacks, Lemma 32.5.2
(01Z9). -/
theorem isLocalization_away_eqLocus_of_bijective_awayMap
    (x : (f.comp (RingHom.fst R A)).eqLocus (h.comp (RingHom.snd R A)))
    (hx : Function.Bijective (Localization.awayMap f x.1.1))
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization.Away x.1.2 B]
    [Algebra ((f.comp (RingHom.fst R A)).eqLocus (h.comp (RingHom.snd R A))) B]
    (hB : algebraMap _ B = (algebraMap A B).comp
      ((RingHom.snd R A).comp ((f.comp (RingHom.fst R A)).eqLocus
        (h.comp (RingHom.snd R A))).subtype)) :
    IsLocalization.Away x B := by
  obtain ⟨⟨g, b⟩, hgb⟩ := x
  have hgb' : f g = h b := hgb
  have hB' (y : (f.comp (RingHom.fst R A)).eqLocus (h.comp (RingHom.snd R A))) :
      algebraMap _ B y = algebraMap A B y.1.2 := by
    rw [hB]
    rfl
  refine IsLocalization.Away.mk _ ?_ (fun s ↦ ?_) (fun y₁ y₂ hy ↦ ?_)
  · rw [hB']
    exact IsLocalization.Away.algebraMap_isUnit b
  · obtain ⟨n, a, hs⟩ := IsLocalization.Away.surj b s
    obtain ⟨r, m, hr⟩ := Localization.awayMap_surjective_iff.mp hx.2 (h a)
    have hy : (r, b ^ m * a) ∈ (f.comp (RingHom.fst R A)).eqLocus (h.comp (RingHom.snd R A)) := by
      change f r = h (b ^ m * a)
      rw [hr, map_mul, map_pow, hgb']
    refine ⟨n + m, ⟨_, hy⟩, ?_⟩
    rw [hB', hB']
    change s * algebraMap A B b ^ (n + m) = algebraMap A B (b ^ m * a)
    rw [pow_add, ← mul_assoc, hs, map_mul, map_pow, mul_comm]
  · rw [hB', hB'] at hy
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq b hy
    have hy₁ : f y₁.1.1 = h y₁.1.2 := y₁.2
    have hy₂ : f y₂.1.1 = h y₂.1.2 := y₂.2
    obtain ⟨k, hk⟩ := (Localization.awayMap_injective_iff (f := f) (r := g)).mp hx.1
      (g ^ n * (y₁.1.1 - y₂.1.1)) (by
        rw [map_mul, map_sub, map_pow, hgb', hy₁, hy₂, ← map_pow, ← map_sub, ← map_mul, mul_sub,
          hn, sub_self, map_zero])
    refine ⟨k + n, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change g ^ (k + n) * y₁.1.1 = g ^ (k + n) * y₂.1.1
      rw [← sub_eq_zero, ← mul_sub, pow_add, mul_assoc, hk]
    · change b ^ (k + n) * y₁.1.2 = b ^ (k + n) * y₂.1.2
      rw [pow_add, mul_assoc, mul_assoc, hn]

end TauCeti
