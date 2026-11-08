/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Ample

/-!
# Global generation after ample twisting

For an ample line bundle `L` on a scheme `X`, every line bundle `K` becomes globally generated
when tensored with a sufficiently high power of `L`. There is no Noetherian hypothesis.
This is the rank-one case of the positive-twisting generation theorem used to construct
projective embeddings.

First, when the affine nonvanishing loci of sections of `L` itself cover `X`, sections of `K`
over these opens extend after tensoring with powers of `L`. Quasi-compactness gives a uniform
bound. An ample `L` has a positive power with such a cover, and applying the first result to
finitely many residue classes of exponents gives all sufficiently large powers of `L`.

## References

* The Stacks Project, Proposition 28.26.13 (Tag 01Q3).
* R. Hartshorne, *Algebraic Geometry*, Theorem II.7.6.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

universe u

variable {X : Scheme.{u}} {L : InvertibleSheaf X}

/-- If affine nonvanishing loci of global sections of `L` cover a quasi-compact separated
scheme, every line bundle is globally generated after sufficiently positive twisting by `L`. -/
private theorem exists_isGloballyGenerated_tensorPow_of_affine_cover
    [CompactSpace X] [X.IsSeparated]
    (hL : ∀ x : X, ∃ s : Γ(L.obj, ⊤), x ∈ L.obj.nonvanishingLocus s ∧
      IsAffineOpen (L.obj.nonvanishingLocus s)) (K : InvertibleSheaf X) :
    ∃ N : ℕ, ∀ n, N ≤ n → ((L.tensorPow n).tensorProduct K).IsGloballyGenerated := by
  -- A local generator of `K` over `X_s` extends after multiplication by powers of `s`.
  have key (x : X) : ∃ (m : ℕ) (W : X.Opens), x ∈ W ∧ ∀ n, m ≤ n →
      ∃ t : Γ(((L.tensorPow n).tensorProduct K).obj, ⊤),
        W ≤ ((L.tensorPow n).tensorProduct K).obj.nonvanishingLocus t := by
    obtain ⟨s, hxs, hs⟩ := hL x
    let U := L.obj.nonvanishingLocus s
    have : IsAffine U := hs
    obtain ⟨t', hxt'⟩ := isGloballyGenerated_iff.mp
      (isGloballyGenerated_of_isQuasiAffine ((pullback U.ι).obj K)) ⟨x, hxs⟩
    obtain ⟨t, ht⟩ := exists_nonvanishingLocus_eq_image K
      (LineBundleClass.pullback_mk U.ι K).symm t'
    have hxt : x ∈ K.obj.nonvanishingLocus t := ht ▸ ⟨⟨x, hxs⟩, hxt', rfl⟩
    obtain ⟨a, b, ξ, hξ⟩ := exists_map_eq_tmul_sectionPow (L := L) (F := K) (U := ⊤)
      (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ) s t
    let F := (L.tensorPow b).tensorProduct ((L.tensorPow a).tensorProduct K)
    have hD : U ≤ L.obj.nonvanishingLocus (L.obj.presheaf.map
        (homOfLE (Scheme.Modules.nonvanishingLocus_le s)).op s) := by
      rw [Scheme.Modules.nonvanishingLocus_map, inf_idem]
    have hξD : U ⊓ F.obj.nonvanishingLocus ξ = K.obj.nonvanishingLocus t := by
      have h := congrArg (Scheme.Modules.nonvanishingLocus _) hξ
      rw [Scheme.Modules.nonvanishingLocus_map, nonvanishingLocus_tmul,
        nonvanishingLocus_tmul, nonvanishingLocus_sectionPow_of_le hD,
        nonvanishingLocus_sectionPow_of_le hD] at h
      exact h.trans (by
        rw [← inf_assoc, inf_idem, inf_eq_right.mpr (Scheme.Modules.nonvanishingLocus_le t)])
    refine ⟨b + a, U ⊓ F.obj.nonvanishingLocus ξ, hξD ▸ hxt, fun n hn ↦ ?_⟩
    let G := (L.tensorPow (n - (b + a))).tensorProduct F
    obtain ⟨e⟩ : Nonempty (G.obj ≅ ((L.tensorPow n).tensorProduct K).obj) := by
      rw [← LineBundleClass.mk_eq_mk_iff]
      simp only [G, F, LineBundleClass.mk_tensorProduct, LineBundleClass.mk_tensorPow]
      simp only [← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
    let τ : Γ(G.obj, ⊤) := tmul (sectionPow s (n - (b + a))) ξ
    refine ⟨e.hom.app ⊤ τ, ?_⟩
    rw [Scheme.Modules.nonvanishingLocus_hom_app]
    exact (inf_le_inf (nonvanishingLocus_le_nonvanishingLocus_sectionPow s _) le_rfl).trans
      (nonvanishingLocus_tmul _ _).ge
  choose N W hxW hW using key
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (W x : Set X))
    (fun x ↦ (W x).isOpen) fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxW x⟩
  refine ⟨T.sup N, fun n hn ↦ isGloballyGenerated_iff.mpr fun x ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ x))
  obtain ⟨t, ht⟩ := hW y n ((Finset.le_sup hy).trans hn)
  exact ⟨t, ht hxy⟩

/-- Tensoring a line bundle with sufficiently high powers of an ample line bundle makes it
globally generated. The bound works for every larger exponent, without Noetherian hypotheses. -/
theorem exists_isGloballyGenerated_tensorPow_of_isAmple
    (hL : (LineBundleClass.mk L).IsAmple) (K : InvertibleSheaf X) :
    ∃ N : ℕ, ∀ n, N ≤ n → ((L.tensorPow n).tensorProduct K).IsGloballyGenerated := by
  have := hL.compactSpace
  have := hL.isSeparated
  obtain ⟨d, hd, hcover⟩ := hL.exists_pos_forall_exists_isAffineOpen_nonvanishingLocus
  have hD := hcover (L.tensorPow d) (LineBundleClass.mk_tensorPow L d)
  -- Treat each exponent modulo `d`; there are only finitely many twists to consider.
  have key (r : Fin d) : ∃ N : ℕ, ∀ n, N ≤ n →
      (((L.tensorPow d).tensorPow n).tensorProduct
        ((L.tensorPow r).tensorProduct K)).IsGloballyGenerated :=
    exists_isGloballyGenerated_tensorPow_of_affine_cover
      hD ((L.tensorPow r).tensorProduct K)
  choose N hN using key
  refine ⟨d * Finset.univ.sup N, fun n hn ↦ ?_⟩
  let r : Fin d := ⟨n % d, Nat.mod_lt n hd⟩
  have hbound : N r ≤ n / d := by
    have hmul : d * N r ≤ n := (Nat.mul_le_mul_left d (Finset.le_sup (Finset.mem_univ r))).trans hn
    exact (Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using hmul)
  obtain ⟨e⟩ : Nonempty
      ((((L.tensorPow d).tensorPow (n / d)).tensorProduct ((L.tensorPow r).tensorProduct K)).obj ≅
        ((L.tensorPow n).tensorProduct K).obj) := by
    rw [← LineBundleClass.mk_eq_mk_iff]
    simp only [LineBundleClass.mk_tensorProduct, LineBundleClass.mk_tensorPow, ← pow_mul,
      ← mul_assoc, ← pow_add]
    dsimp only [r]
    rw [Nat.div_add_mod]
  exact (isGloballyGenerated_iff_of_iso e).mp (hN r (n / d) hbound)

end TauCeti.AlgebraicGeometry.InvertibleSheaf
