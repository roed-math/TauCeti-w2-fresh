/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import TauCeti.RingTheory.GradedAlgebra.VeroneseSubalgebra

/-!
# Homogeneous localizations of a Veronese subalgebra

Let `A = ⨁ₙ 𝒜 n` be an `ℕ`-graded commutative `R`-algebra, `d ≠ 0`, and `A^{(d)} = ⨁ₖ 𝒜 (d k)` its
Veronese subalgebra. A fraction of `A^{(d)}` of degree zero, `a / s` with `a, s` of degree `k` in
`A^{(d)}`, is a fraction of `A` of degree zero, with `a, s` of degree `d k` in `A`. This gives a
ring map from the homogeneous localization of `A^{(d)}` at a submonoid `P` to the homogeneous
localization of `A` at the image of `P`.

For a homogeneous `f ∈ A^{(d)}` this map is an isomorphism

`A^{(d)}_{(f)} ≅ A_{(f)}`

(`TauCeti.GradedAlgebra.awayVeroneseEquiv`): if `f` has degree `k` in `A^{(d)}`, then an element
`a / fⁿ` of `A_{(f)}` has numerator `a ∈ 𝒜 (n d k) = 𝒜 (d (n k))`, which lies in `A^{(d)}`. These
are the affine charts of the identification `Proj A^{(d)} ≅ Proj A`.

## Main definitions

* `TauCeti.GradedAlgebra.veroneseHomogeneousLocalizationMap`: the map from the homogeneous
  localization of `A^{(d)}` at `P` to that of `A` at the image of `P`.
* `TauCeti.GradedAlgebra.awayVeroneseEquiv`: for homogeneous `f ∈ A^{(d)}`, the isomorphism
  `A^{(d)}_{(f)} ≃+* A_{(f)}`.

## Main results

* `TauCeti.GradedAlgebra.injective_veroneseHomogeneousLocalizationMap_powers` and
  `TauCeti.GradedAlgebra.surjective_veroneseHomogeneousLocalizationMap_powers`: the map
  `A^{(d)}_{(f)} → A_{(f)}` is bijective for homogeneous `f ∈ A^{(d)}`.

## References

* [The Stacks Project, Lemma 27.11.8 (0B5J)](https://stacks.math.columbia.edu/tag/0B5J)
-/

@[expose] public section

open HomogeneousLocalization

namespace TauCeti.GradedAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : ℕ)

variable {𝒜 d} in
/-- A fraction of degree `k` of the Veronese subalgebra, read as a fraction of degree `d k`
of `A`. -/
@[simps!]
def NumDenSameDeg.ofVeronese {P : Submonoid (veronese 𝒜 d)} {Q : Submonoid A}
    (hPQ : P ≤ Q.comap (veronese 𝒜 d).val) (c : NumDenSameDeg (veroneseGrading 𝒜 d) P) :
    NumDenSameDeg 𝒜 Q where
  deg := d * c.deg
  num := ⟨(c.num : veronese 𝒜 d), c.num.2⟩
  den := ⟨(c.den : veronese 𝒜 d), c.den.2⟩
  den_mem := hPQ c.den_mem

variable {P : Submonoid (veronese 𝒜 d)} {Q : Submonoid A} (hPQ : P ≤ Q.comap (veronese 𝒜 d).val)

/-- The ring map between the localizations underlying
`TauCeti.GradedAlgebra.veroneseHomogeneousLocalizationMap`. -/
noncomputable def veroneseLocalizationMap : Localization P →+* Localization Q :=
  IsLocalization.map _ (veronese 𝒜 d).val.toRingHom hPQ

theorem veroneseLocalizationMap_mk (a : veronese 𝒜 d) (s : P) :
    veroneseLocalizationMap 𝒜 d hPQ (.mk a s) = .mk (a : A) ⟨s, hPQ s.2⟩ := by
  simp only [veroneseLocalizationMap, Localization.mk_eq_mk']
  exact IsLocalization.map_mk' (T := Q) _ a s

/-- The function underlying `TauCeti.GradedAlgebra.veroneseHomogeneousLocalizationMap`. -/
def veroneseHomogeneousLocalizationFun :
    HomogeneousLocalization (veroneseGrading 𝒜 d) P → HomogeneousLocalization 𝒜 Q :=
  Quotient.map' (NumDenSameDeg.ofVeronese hPQ) fun x y (e : x.embedding = y.embedding) ↦ by
    apply_fun veroneseLocalizationMap 𝒜 d hPQ at e
    change (NumDenSameDeg.ofVeronese hPQ x).embedding = (NumDenSameDeg.ofVeronese hPQ y).embedding
    simp only [NumDenSameDeg.embedding, veroneseLocalizationMap_mk] at e ⊢
    exact e

theorem val_veroneseHomogeneousLocalizationFun
    (x : HomogeneousLocalization (veroneseGrading 𝒜 d) P) :
    (veroneseHomogeneousLocalizationFun 𝒜 d hPQ x).val =
      veroneseLocalizationMap 𝒜 d hPQ x.val := by
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [val_mk, veroneseLocalizationMap_mk]
  rfl

variable [NeZero d]

/-- The homogeneous localization of the Veronese subalgebra `A^{(d)}` at a submonoid `P` maps to
the homogeneous localization of `A` at a submonoid `Q` containing the image of `P`: a fraction of
degree `k` of `A^{(d)}` is a fraction of degree `d k` of `A`. -/
noncomputable def veroneseHomogeneousLocalizationMap :
    HomogeneousLocalization (veroneseGrading 𝒜 d) P →+* HomogeneousLocalization 𝒜 Q where
  toFun := veroneseHomogeneousLocalizationFun 𝒜 d hPQ
  map_one' := val_injective _ <| by simp [val_veroneseHomogeneousLocalizationFun]
  map_mul' x y := val_injective _ <| by simp [val_veroneseHomogeneousLocalizationFun]
  map_zero' := val_injective _ <| by simp [val_veroneseHomogeneousLocalizationFun]
  map_add' x y := val_injective _ <| by simp [val_veroneseHomogeneousLocalizationFun]

@[simp]
theorem val_veroneseHomogeneousLocalizationMap
    (x : HomogeneousLocalization (veroneseGrading 𝒜 d) P) :
    (veroneseHomogeneousLocalizationMap 𝒜 d hPQ x).val = veroneseLocalizationMap 𝒜 d hPQ x.val :=
  val_veroneseHomogeneousLocalizationFun 𝒜 d hPQ x

section Away

variable {𝒜 d} {f : veronese 𝒜 d}

omit [NeZero d] in
/-- The powers of `f ∈ A^{(d)}` map into the powers of `f` in `A`. -/
theorem powers_le_comap_val_powers :
    Submonoid.powers f ≤ (Submonoid.powers (f : A)).comap (veronese 𝒜 d).val := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp⟩

/-- The map `A^{(d)}_{(f)} → A_{(f)}` is injective. -/
theorem injective_veroneseHomogeneousLocalizationMap_powers :
    Function.Injective
      (veroneseHomogeneousLocalizationMap 𝒜 d (powers_le_comap_val_powers (f := f))) := by
  intro x y e
  obtain ⟨c, rfl⟩ := x.mk_surjective
  obtain ⟨c', rfl⟩ := y.mk_surjective
  apply_fun HomogeneousLocalization.val at e
  simp only [val_veroneseHomogeneousLocalizationMap, val_mk, veroneseLocalizationMap_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists] at e
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := e
  refine val_injective _ ?_
  simp only [val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨⟨f ^ n, n, rfl⟩, Subtype.ext (by simpa using hn)⟩

/-- For homogeneous `f ∈ A^{(d)}`, the map `A^{(d)}_{(f)} → A_{(f)}` is surjective. -/
theorem surjective_veroneseHomogeneousLocalizationMap_powers {k : ℕ}
    (hf : f ∈ veroneseGrading 𝒜 d k) :
    Function.Surjective
      (veroneseHomogeneousLocalizationMap 𝒜 d (powers_le_comap_val_powers (f := f))) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (mem_veroneseGrading.1 hf) z
  have ha' : a ∈ 𝒜 (d * (n • k)) := by
    rwa [smul_eq_mul, mul_left_comm, ← smul_eq_mul]
  refine ⟨Away.mk (veroneseGrading 𝒜 d) hf n ⟨a, mem_veronese_of_mem ha'⟩
    (mem_veroneseGrading.2 ha'), val_injective _ ?_⟩
  rw [val_veroneseHomogeneousLocalizationMap, Away.val_mk, Away.val_mk,
    veroneseLocalizationMap_mk]
  rfl

/-- For `f` homogeneous of degree `k` in the Veronese subalgebra `A^{(d)}`, the homogeneous
localizations `A^{(d)}_{(f)}` and `A_{(f)}` agree: a fraction `a / fⁿ` of `A` of degree zero has
numerator of degree `n d k`, so it is a fraction of `A^{(d)}`. -/
noncomputable def awayVeroneseEquiv {k : ℕ} (hf : f ∈ veroneseGrading 𝒜 d k) :
    Away (veroneseGrading 𝒜 d) f ≃+* Away 𝒜 (f : A) :=
  .ofBijective _ ⟨injective_veroneseHomogeneousLocalizationMap_powers,
    surjective_veroneseHomogeneousLocalizationMap_powers hf⟩

@[simp]
theorem val_awayVeroneseEquiv {k : ℕ} (hf : f ∈ veroneseGrading 𝒜 d k)
    (x : Away (veroneseGrading 𝒜 d) f) :
    (awayVeroneseEquiv hf x).val = veroneseLocalizationMap 𝒜 d powers_le_comap_val_powers x.val :=
  val_veroneseHomogeneousLocalizationMap 𝒜 d _ x

end Away

end TauCeti.GradedAlgebra
