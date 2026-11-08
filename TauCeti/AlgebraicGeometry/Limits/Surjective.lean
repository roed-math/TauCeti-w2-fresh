/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Limits.Constructible
public import TauCeti.AlgebraicGeometry.Limits.BaseChange

/-!
# Surjectivity is inherited from a finite stage

Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps. If a quasi-compact locally finitely presented morphism over a member becomes
surjective over `S`, it is surjective over some later member. By Chevalley's theorem its image
is constructible. The complement of the image has empty preimage in `S`, so it already has
empty preimage at a finite stage by the constructible-set criterion.

This criterion allows a surjective covering morphism constructed over a limit to be spread out.
It is used when spreading out surjective covers in descent arguments for proper morphisms.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry Topology

namespace TauCeti.AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {c : Cone D} (hc : IsLimit c)

include hc in
/-- A quasi-compact locally finitely presented morphism over a quasi-compact quasi-separated
member that is surjective after base change to the limit is surjective at some finite stage. -/
theorem exists_surjective_pullback_fst_of_isLimit {i : I}
    [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)] {X : Scheme.{u}}
    (q : X ⟶ D.obj i) [QuasiCompact q] [LocallyOfFinitePresentation q]
    [Surjective (pullback.fst (c.π.app i) q)] :
    ∃ (j : I) (fji : j ⟶ i), Surjective (pullback.fst (D.map fji) q) := by
  have hs : IsConstructible (Set.range q) := by
    simpa only [Set.image_univ] using q.isConstructible_image IsConstructible.univ
  have h : c.π.app i ⁻¹' (Set.range q)ᶜ = ∅ := by
    rw [Set.preimage_compl, ← Scheme.Pullback.range_fst, range_eq_univ, Set.compl_univ]
  obtain ⟨j, fji, hj⟩ := exists_map_preimage_eq_empty_of_isConstructible hc hs.compl h
  refine ⟨j, fji, ?_⟩
  rw [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst,
    ← Set.compl_empty_iff, ← Set.preimage_compl, hj]

include hc in
/-- A quasi-compact locally finitely presented morphism between schemes over a member, with
quasi-compact quasi-separated target over that member, that becomes surjective over the limit
becomes surjective over some later member. -/
theorem exists_surjective_pullbackMap_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I} {X Y : Scheme.{u}}
    {p : X ⟶ D.obj i} {q : Y ⟶ D.obj i} [QuasiCompact q] [QuasiSeparated q]
    (g : X ⟶ Y) [QuasiCompact g] [LocallyOfFinitePresentation g] (hg : g ≫ q = p)
    [Surjective
      (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg]))] :
    ∃ (j : I) (hji : j ⟶ i), Surjective
      (pullback.map (D.map hji) p (D.map hji) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])) :=
  exists_pullbackMap_of_pullbackOver c @Surjective g hg
    (fun h ↦ have := h; exists_surjective_pullback_fst_of_isLimit (hc.pullbackOver q) _) ‹_›

end TauCeti.AlgebraicGeometry.Scheme
