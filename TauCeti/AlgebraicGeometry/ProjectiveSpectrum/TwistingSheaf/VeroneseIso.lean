/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Veronese
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Veronese

/-!
# Twisting sheaves of `Proj` of a Veronese subalgebra

Let `A = ⨁ₙ 𝒜 n` be an `ℕ`-graded commutative `R`-algebra, `d ≠ 0`, and `A^{(d)} = ⨁ₖ 𝒜 (d k)`
its Veronese subalgebra. The isomorphism `Proj A^{(d)} ≅ Proj A` of
`AlgebraicGeometry.Proj.veroneseIso` is glued from affine charts. Here we identify its inverse
`AlgebraicGeometry.Proj.toVeronese` on points with the contraction `q ↦ q ∩ A^{(d)}` of
`AlgebraicGeometry.ProjectiveSpectrum.veroneseComap`, along which the twisting sheaf sections
`Γ(U, 𝒪_{Proj A^{(d)}}(n)) → Γ(V, 𝒪_{Proj A}(d n))` are pulled back.

## Main results

* `AlgebraicGeometry.Proj.toVeronese_apply`: on points, `toVeronese` is the contraction
  `q ↦ q ∩ A^{(d)}`.
* `AlgebraicGeometry.Proj.coe_toVeronese_preimage`,
  `AlgebraicGeometry.Proj.veroneseComap_fromVeronese_apply`: its consequences for preimages of
  opens and for `fromVeronese`.

## References

* [Stacks, Lemma 27.11.8 (0B5J)](https://stacks.math.columbia.edu/tag/0B5J)
-/

@[expose] public section

open CategoryTheory TauCeti.GradedAlgebra

namespace AlgebraicGeometry.Proj

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {d : ℕ} [NeZero d]

/-- **On points, `AlgebraicGeometry.Proj.toVeronese` is the contraction** `q ↦ q ∩ A^{(d)}`. Both
primes miss some homogeneous `g ∈ A^{(d)}` of positive degree, and by
`AlgebraicGeometry.Proj.toVeronese_preimage_basicOpen` they contain the same homogeneous
elements of positive degree; multiplying by `g` reduces every degree to a positive one. -/
theorem toVeronese_apply (x : Proj 𝒜) :
    toVeronese 𝒜 d x = ProjectiveSpectrum.veroneseComap 𝒜 d x := by
  obtain ⟨⟨k₀, g, hg⟩, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_basicOpen_veronese_eq_top 𝒜 d).ge (Set.mem_univ x))
  have key {k : ℕ} {a : veronese 𝒜 d} (ha : a ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) :
      a ∈ (toVeronese 𝒜 d x).asHomogeneousIdeal ↔ (a : A) ∈ x.asHomogeneousIdeal := by
    have := congrArg (x ∈ ·) (toVeronese_preimage_basicOpen ha hk)
    simp only [eq_iff_iff] at this
    exact not_iff_not.mp ((mem_basicOpen _ _ _).symm.trans (this.trans (mem_basicOpen _ _ _)))
  have hgx : (g : A) ∉ x.asHomogeneousIdeal := (mem_basicOpen _ _ _).1 hx
  have hgy : g ∉ (toVeronese 𝒜 d x).asHomogeneousIdeal := fun h ↦ hgx ((key hg k₀.pos).1 h)
  refine ProjectiveSpectrum.ext (HomogeneousIdeal.ext' fun k a ha ↦ ?_)
  have hag := key (SetLike.mul_mem_graded ha hg) (Nat.add_pos_right k k₀.pos)
  change a ∈ (toVeronese 𝒜 d x).asHomogeneousIdeal ↔ (a : A) ∈ x.asHomogeneousIdeal
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (x.isPrime.mem_or_mem (hag.1 (Ideal.mul_mem_right _ _ h))).resolve_right hgx
  · exact ((toVeronese 𝒜 d x).isPrime.mem_or_mem
      (hag.2 (Ideal.mul_mem_right (g : A) x.asHomogeneousIdeal.toIdeal h))).resolve_right hgy

/-- The preimage of an open `U ⊆ Proj A^{(d)}` under `AlgebraicGeometry.Proj.toVeronese` is its
preimage under the contraction `q ↦ q ∩ A^{(d)}`. -/
theorem coe_toVeronese_preimage (U : (Proj (veroneseGrading 𝒜 d)).Opens) :
    (toVeronese 𝒜 d ⁻¹ᵁ U).1 = ProjectiveSpectrum.veroneseComap 𝒜 d ⁻¹' U.1 :=
  Set.ext fun x ↦ show toVeronese 𝒜 d x ∈ U ↔ _ by rw [toVeronese_apply]; rfl

/-- The contraction `q ↦ q ∩ A^{(d)}` inverts `AlgebraicGeometry.Proj.fromVeronese` on
points. -/
@[simp]
theorem veroneseComap_fromVeronese_apply (p : Proj (veroneseGrading 𝒜 d)) :
    ProjectiveSpectrum.veroneseComap 𝒜 d (fromVeronese 𝒜 d p) = p := by
  rw [← toVeronese_apply, ← Scheme.Hom.comp_apply]
  exact congrArg (fun f : Proj (veroneseGrading 𝒜 d) ⟶ _ ↦ f p) (veroneseIso 𝒜 d).hom_inv_id

end AlgebraicGeometry.Proj
