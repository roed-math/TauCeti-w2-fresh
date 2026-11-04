/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TopCohomology
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TwistingSheaf
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Vanishing

/-!
# Cohomology of the twisting sheaves on projective space

Let `M` be a free module with a basis indexed by a type with `n + 1` elements, `n ≥ 1`, over a
commutative ring `R`, so that `Proj (Sym M) = ℙⁿ_R` is projective space of dimension `n` over `R`.
This file assembles the computation of the cohomology `Hᵠ(ℙⁿ_R, 𝒪(d))` of the twisting sheaves for
every degree `q` and every twist `d : ℤ`, as `R`-modules:

* in degree `0` and twist `d = j ≥ 0`, it is the module of forms of degree `j`
  (`TauCeti.SymmetricAlgebra.cohomologyZeroTwistingSheafLinearEquiv`);
* in degree `n` and twist `d = -j - n - 1`, it is the dual of the module of forms of degree `j`
  (`TauCeti.SymmetricAlgebra.cohomologyTopTwistingSheafLinearEquiv`);
* in all other cases it is zero: in degree `0` for `d < 0`
  (`TauCeti.SymmetricAlgebra.subsingleton_cohomology_zero_twistingSheaf_of_neg`), in degrees
  `0 < q < n` (`Module.Basis.subsingleton_cohomology_twistingSheaf_of_lt_card`), in degree `n` for
  `d > -n - 1` (`Module.Basis.subsingleton_cohomology_twistingSheaf_of_neg_card_lt`) and in degrees
  `q > n` (`Module.Basis.subsingleton_cohomology_proj_of_card_le`).

## Main statements

* `TauCeti.SymmetricAlgebra.projectiveSpace_cohomology`: the cohomology of `𝒪(d)` on `ℙⁿ_R` in
  every degree.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.1.
* [Stacks, Lemmas 30.8.1–30.8.3 (01XS)](https://stacks.math.columbia.edu/tag/01XS)
-/

public section

open AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

namespace TauCeti.SymmetricAlgebra

universe u

variable {R : Type u} {M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]

local notation "𝒜" => homogeneousSubmodule R M

/-- **The cohomology of the twisting sheaves on projective space.** Let `M` be a free `R`-module
with a basis indexed by a type `κ` with `n + 1` elements, `n ≥ 1`, so that `Proj (Sym M)` is
projective space `ℙⁿ_R` over the commutative ring `R`, and let `q : ℕ` and `d : ℤ`. Then
`Hᵠ(ℙⁿ_R, 𝒪(d))` is the module of forms of degree `d` when `q = 0` and `d ≥ 0`, the dual of the
module of forms of degree `-d - n - 1` when `q = n` and `d ≤ -n - 1`, and zero otherwise. -/
theorem projectiveSpace_cohomology {κ : Type*} [Fintype κ] (b : Module.Basis κ R M) {n : ℕ}
    (hn : n ≠ 0) (hκ : Fintype.card κ = n + 1) (q : ℕ) (d : ℤ) :
    (q = 0 → ∀ j : ℕ, d = j →
      Nonempty (Cohomology (Proj.twistingSheaf 𝒜 d) q ≃ₗ[R] 𝒜 j)) ∧
    (q = n → ∀ j : ℕ, d = -((j + (n + 1) : ℕ) : ℤ) →
      Nonempty (Cohomology (Proj.twistingSheaf 𝒜 d) q ≃ₗ[R] Module.Dual R (𝒜 j))) ∧
    ((q = 0 → d < 0) → (q = n → -((n + 1 : ℕ) : ℤ) < d) →
      Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 d) q)) := by
  have : Nontrivial κ := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  refine ⟨?_, ?_, fun h₀ hn' ↦ ?_⟩
  · rintro rfl j rfl
    exact ⟨cohomologyZeroTwistingSheafLinearEquiv j b⟩
  · rintro rfl j rfl
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact ⟨cohomologyTopTwistingSheafLinearEquiv b hκ j⟩
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact subsingleton_cohomology_zero_twistingSheaf_of_neg (h₀ rfl) b
  rcases lt_trichotomy q n with hqn | rfl | hqn
  · exact b.subsingleton_cohomology_twistingSheaf_of_lt_card d hq (by omega)
  · exact b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt (by simpa [hκ] using hn' rfl) hq
  · exact b.subsingleton_cohomology_proj_of_card_le _ q (by omega)

end TauCeti.SymmetricAlgebra
