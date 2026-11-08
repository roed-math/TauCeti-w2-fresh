/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Constructible sets in cofiltered limits of schemes

For a cofiltered diagram with affine transition maps, a constructible subset of a quasi-compact
quasi-separated member whose preimage in the limit is empty already has empty preimage in some
later member. Consequently inclusions and equalities between constructible subsets can be
detected at a finite stage. This is the constructible-set form of the analogous criterion for
quasi-compact opens in Stacks, Section 32.4 (Tag 081A). Together with Chevalley's theorem it
allows surjectivity of finitely presented morphisms to be detected at a finite stage.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry Topology TopologicalSpace

namespace TauCeti.AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {c : Cone D} (hc : IsLimit c)

include hc in
/-- A constructible subset of a quasi-compact quasi-separated member of a cofiltered diagram
with affine transition maps has empty preimage in the limit only if it has empty preimage in
some later member. -/
theorem exists_map_preimage_eq_empty_of_isConstructible {i : I}
    [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)] {s : Set (D.obj i)}
    (hs : IsConstructible s) (h : c.π.app i ⁻¹' s = ∅) :
    ∃ (j : I) (fji : j ⟶ i), D.map fji ⁻¹' s = ∅ := by
  classical
  have : Nonempty (D.obj i).affineOpens := ⟨⟨⊥, isAffineOpen_bot _⟩⟩
  induction s, hs using IsConstructible.induction_of_isTopologicalBasis
      (fun U : (D.obj i).affineOpens ↦ (U.1 : Set (D.obj i)))
      (by simpa [Opens.IsBasis, Set.image_eq_range] using (D.obj i).isBasis_affineOpens)
      (fun U ↦ U.2.isCompact) with
  | sdiff U t ht =>
    let V : (D.obj i).Opens := ⨆ W ∈ t, W.1
    have H : c.π.app i ⁻¹ᵁ U.1 ≤ c.π.app i ⁻¹ᵁ V := by
      intro x hx
      have : x ∉ c.π.app i ⁻¹' ((U.1 : Set (D.obj i)) \ ⋃ W ∈ t, (W.1 : Set (D.obj i))) := by
        rw [h]
        exact Set.notMem_empty x
      simpa [V] using not_not.mp (fun hn ↦ this ⟨hx, hn⟩)
    obtain ⟨j, fji, hj⟩ := exists_map_preimage_le_map_preimage D c hc U.2.isCompact H
    refine ⟨j, fji, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
    intro x hx
    exact hx.2 (by simpa [V] using hj hx.1)
  | union s hs t ht ihs iht =>
    have hs' : c.π.app i ⁻¹' s = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      (fun x hx ↦ Set.eq_empty_iff_forall_notMem.mp h x (Or.inl hx))
    have ht' : c.π.app i ⁻¹' t = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      (fun x hx ↦ Set.eq_empty_iff_forall_notMem.mp h x (Or.inr hx))
    obtain ⟨j, fji, hj⟩ := ihs hs'
    obtain ⟨k, fki, hk⟩ := iht ht'
    obtain ⟨l, flj, flk, e⟩ := IsCofiltered.cospan fji fki
    refine ⟨l, flj ≫ fji, ?_⟩
    rw [Set.preimage_union]
    have h₁ : D.map (flj ≫ fji) ⁻¹' s = ∅ := by
      ext x
      simpa only [Functor.map_comp, Scheme.Hom.comp_apply, Set.mem_preimage,
        Set.notMem_empty, iff_false] using Set.eq_empty_iff_forall_notMem.mp hj (D.map flj x)
    have h₂ : D.map (flj ≫ fji) ⁻¹' t = ∅ := by
      rw [e]
      ext x
      simpa only [Functor.map_comp, Scheme.Hom.comp_apply, Set.mem_preimage,
        Set.notMem_empty, iff_false] using Set.eq_empty_iff_forall_notMem.mp hk (D.map flk x)
    rw [h₁, h₂, Set.union_empty]

include hc in
/-- Inclusion between the preimages of two constructible subsets of a quasi-compact
quasi-separated member can be detected at a finite stage. -/
theorem exists_map_preimage_subset_map_preimage_of_isConstructible {i : I}
    [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)] {s t : Set (D.obj i)}
    (hs : IsConstructible s) (ht : IsConstructible t)
    (h : c.π.app i ⁻¹' s ⊆ c.π.app i ⁻¹' t) :
    ∃ (j : I) (fji : j ⟶ i), D.map fji ⁻¹' s ⊆ D.map fji ⁻¹' t := by
  obtain ⟨j, fji, hj⟩ := exists_map_preimage_eq_empty_of_isConstructible hc (hs.sdiff ht)
    (by rw [Set.preimage_sdiff, Set.sdiff_eq_empty]; exact h)
  exact ⟨j, fji, Set.sdiff_eq_empty.mp (by rwa [Set.preimage_sdiff] at hj)⟩

include hc in
/-- Equality between the preimages of two constructible subsets of a quasi-compact
quasi-separated member can be detected at a finite stage. -/
theorem exists_map_preimage_eq_map_preimage_of_isConstructible {i : I}
    [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)] {s t : Set (D.obj i)}
    (hs : IsConstructible s) (ht : IsConstructible t)
    (h : c.π.app i ⁻¹' s = c.π.app i ⁻¹' t) :
    ∃ (j : I) (fji : j ⟶ i), D.map fji ⁻¹' s = D.map fji ⁻¹' t := by
  obtain ⟨j, fji, hj⟩ := exists_map_preimage_subset_map_preimage_of_isConstructible hc hs ht h.le
  obtain ⟨k, fki, hk⟩ := exists_map_preimage_subset_map_preimage_of_isConstructible hc ht hs h.ge
  obtain ⟨l, flj, flk, e⟩ := IsCofiltered.cospan fji fki
  refine ⟨l, flj ≫ fji, Set.Subset.antisymm ?_ ?_⟩
  · simp only [Functor.map_comp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    exact Set.preimage_mono hj
  · rw [e]
    simp only [Functor.map_comp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    exact Set.preimage_mono hk

end TauCeti.AlgebraicGeometry.Scheme
