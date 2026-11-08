/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Ample
public import TauCeti.AlgebraicGeometry.LineBundle.RelativelyAmple

/-!
# Local generation after relatively ample twisting

Over a quasi-compact base, twisting a line bundle by sufficiently high powers of a relatively
ample line bundle makes it globally generated over the preimages of the members of an affine
open cover of the base. A single bound works over the whole base and for every larger exponent.
This is the local generation input to the construction of relative projective embeddings.

The affine result is `InvertibleSheaf.exists_isGloballyGenerated_tensorPow_of_isAmple`.
Quasi-compactness permits taking the maximum of the bounds for a finite affine cover.

## References

* The Stacks Project, Lemma 29.39.3 (Tag 01VU).
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

variable {X S : Scheme.{u}}

/-- Over a quasi-compact base, sufficiently high relatively ample twists of a line bundle are
globally generated over an affine neighbourhood of every base point, with one uniform bound. -/
theorem IsRelativelyAmple.exists_locally_isGloballyGenerated_tensorPow [CompactSpace S]
    {L : InvertibleSheaf X} {f : X ⟶ S} (hL : (LineBundleClass.mk L).IsRelativelyAmple f)
    (K : InvertibleSheaf X) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ s : S, ∃ V : S.Opens, IsAffineOpen V ∧ s ∈ V ∧
      ((InvertibleSheaf.pullback (f ⁻¹ᵁ V).ι).obj
        ((L.tensorPow n).tensorProduct K)).IsGloballyGenerated := by
  have key (V : S.affineOpens) : ∃ N : ℕ, ∀ n, N ≤ n →
      ((InvertibleSheaf.pullback (f ⁻¹ᵁ V.1).ι).obj
        ((L.tensorPow n).tensorProduct K)).IsGloballyGenerated := by
    have h := hL.isAmple_pullback V V.2
    rw [pullback_mk] at h
    obtain ⟨N, hN⟩ := InvertibleSheaf.exists_isGloballyGenerated_tensorPow_of_isAmple h
      ((InvertibleSheaf.pullback (f ⁻¹ᵁ V.1).ι).obj K)
    refine ⟨N, fun n hn ↦ ?_⟩
    obtain ⟨e⟩ : Nonempty
        (((((InvertibleSheaf.pullback (f ⁻¹ᵁ V.1).ι).obj L).tensorPow n).tensorProduct
            ((InvertibleSheaf.pullback (f ⁻¹ᵁ V.1).ι).obj K)).obj ≅
          ((InvertibleSheaf.pullback (f ⁻¹ᵁ V.1).ι).obj
            ((L.tensorPow n).tensorProduct K)).obj) := by
      rw [← mk_eq_mk_iff]
      simp only [mk_tensorProduct, mk_tensorPow, ← pullback_mk, ← pullbackHom_apply,
        map_mul, map_pow]
    exact (InvertibleSheaf.isGloballyGenerated_iff_of_iso e).mp (hN n hn)
  choose N hN using key
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun V : S.affineOpens ↦ (V : Set S))
    (fun V ↦ V.1.isOpen) fun s _ ↦ by
      obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hsV⟩
  refine ⟨T.sup N, fun n hn s ↦ ?_⟩
  obtain ⟨V, hV, hsV⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ s))
  exact ⟨V, V.2, hsV, hN V n ((Finset.le_sup hV).trans hn)⟩

end TauCeti.AlgebraicGeometry.LineBundleClass
