/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Limits.Surjective
public import TauCeti.AlgebraicGeometry.Limits.Morphisms
public import TauCeti.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Properness at a finite stage for subschemes of proper schemes

Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact schemes with affine transition maps.
Suppose a quasi-compact scheme `X` over a member `Sᵢ` admits an immersion into a scheme proper
over `Sᵢ`. If `X ×_{Sᵢ} S` is proper over `S`, then `X ×_{Sᵢ} Sⱼ` is proper over some `Sⱼ`.
Indeed the immersion becomes closed over the limit, and closed immersions descend to a finite
stage. In particular this applies to quasi-projective schemes once a projective embedding has
been chosen.

The same conclusion holds when `X` has a proper surjective cover admitting such an immersion:
universal closedness descends through the cover, and separatedness descends independently.
These are the steps of the properness descent proof after the construction of a Chow cover;
the existence of that cover is a separate input. See Stacks, Lemma 32.13.1 (Tag 081F).

For finitely presented schemes there is a second useful criterion: a separated model becomes
proper at a finite stage if, over the limit, it receives a surjective morphism from the base
change of a proper finitely presented scheme over a member. The covering morphism descends,
surjectivity is inherited at a finite stage, and universal closedness passes to its target.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  {c : Cone D} (hc : IsLimit c)

include hc in
/-- For a quasi-compact scheme over a member admitting an immersion into a proper scheme over
that member, properness after base change to the limit implies properness at a finite stage. -/
theorem exists_isProper_pullback_fst_of_isLimit_of_isImmersion {i : I} {X Y : Scheme.{u}}
    (q : X ⟶ D.obj i) [QuasiCompact q] (r : Y ⟶ D.obj i) [IsProper r]
    (g : X ⟶ Y) [IsImmersion g] (hg : g ≫ r = q)
    [IsProper (pullback.fst (c.π.app i) q)] :
    ∃ (j : I) (fji : j ⟶ i), IsProper (pullback.fst (D.map fji) q) := by
  have : MorphismProperty.RespectsIso @IsImmersion.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : QuasiCompact (g ≫ r) := hg ▸ inferInstance
  have : QuasiCompact g := QuasiCompact.of_comp g r
  let a := pullback.map (c.π.app i) q (c.π.app i) r (𝟙 _) g (𝟙 _)
    (by simp) (by simp [hg])
  have ha : a ≫ pullback.fst (c.π.app i) r = pullback.fst (c.π.app i) q := by simp [a]
  have : IsImmersion a :=
    (MorphismProperty.pullback_map_iff_pullback_fst_pullback_snd
      (P := @IsImmersion) (c.π.app i) g hg).mpr inferInstance
  have : IsProper (a ≫ pullback.fst (c.π.app i) r) := ha ▸ inferInstance
  have : IsProper a := IsProper.of_comp a (pullback.fst (c.π.app i) r)
  have : IsClosedImmersion a := IsClosedImmersion.of_isPreimmersion a
    (by simpa only [Set.image_univ] using a.isClosedMap _ isClosed_univ)
  obtain ⟨j, fji, hj⟩ := exists_isClosedImmersion_pullbackMap_of_isLimit hc g hg
  let b := pullback.map (D.map fji) q (D.map fji) r (𝟙 _) g (𝟙 _)
    (by simp) (by simp [hg])
  have : IsClosedImmersion b := hj
  refine ⟨j, fji, ?_⟩
  have : IsProper (b ≫ pullback.fst (D.map fji) r) := inferInstance
  simpa only [b, pullback.lift_fst, Category.comp_id] using this

include hc in
/-- Suppose a quasi-compact quasi-separated scheme `X` over a member has a proper surjective
cover `Z` admitting an immersion into a proper scheme over that member. If `X` is proper over
the limit, then it is proper at some finite stage. The existence of the cover is not asserted. -/
theorem exists_isProper_pullback_fst_of_isLimit_of_isProper_surjective {i : I}
    {X Z Y : Scheme.{u}} (q : X ⟶ D.obj i) [QuasiCompact q] [QuasiSeparated q]
    [LocallyOfFiniteType q] (π : Z ⟶ X) [IsProper π] [Surjective π]
    (r : Y ⟶ D.obj i) [IsProper r] (g : Z ⟶ Y) [IsImmersion g] (hg : g ≫ r = π ≫ q)
    [IsProper (pullback.fst (c.π.app i) q)] :
    ∃ (j : I) (fji : j ⟶ i), IsProper (pullback.fst (D.map fji) q) := by
  -- Properness of the cover over the limit passes from `X` to `Z`.
  let a := pullback.map (c.π.app i) (π ≫ q) (c.π.app i) q (𝟙 _) π (𝟙 _)
    (by simp) (by simp)
  have : IsProper a :=
    (MorphismProperty.pullback_map_iff_pullback_fst_pullback_snd
      (P := @IsProper) (c.π.app i) π rfl).mpr inferInstance
  have : IsProper (pullback.fst (c.π.app i) (π ≫ q)) := by
    have : IsProper (a ≫ pullback.fst (c.π.app i) q) := inferInstance
    simpa only [a, pullback.lift_fst, Category.comp_id] using this
  obtain ⟨j, fji, hj⟩ := exists_isProper_pullback_fst_of_isLimit_of_isImmersion hc
    (π ≫ q) r g hg
  obtain ⟨k, fki, hk⟩ := exists_isSeparated_pullback_fst_of_isLimit hc q
  obtain ⟨l, flj, flk, e⟩ := IsCofiltered.cospan fji fki
  -- Enlarge both stages so the source of the cover is proper and its target is separated.
  have : IsProper (pullback.fst (D.map (flj ≫ fji)) (π ≫ q)) := by
    have : IsProper (pullback.fst (D.map fji) (π ≫ q)) := hj
    exact (MorphismProperty.pullback_fst_pullback_fst_iff (P := @IsProper) (D.map flj)
      (D.map fji) (π ≫ q) (D.map_comp flj fji).symm).mp inferInstance
  have : IsSeparated (pullback.fst (D.map (flj ≫ fji)) q) := by
    rw [e]
    have : IsSeparated (pullback.fst (D.map fki) q) := hk
    exact (MorphismProperty.pullback_fst_pullback_fst_iff (P := @IsSeparated) (D.map flk)
      (D.map fki) q (D.map_comp flk fki).symm).mp inferInstance
  let b := pullback.map (D.map (flj ≫ fji)) (π ≫ q) (D.map (flj ≫ fji)) q (𝟙 _) π (𝟙 _)
    (by simp) (by simp)
  have : Surjective b :=
    (MorphismProperty.pullback_map_iff_pullback_fst_pullback_snd
      (P := @Surjective) (D.map (flj ≫ fji)) π rfl).mpr inferInstance
  have : UniversallyClosed (b ≫ pullback.fst (D.map (flj ≫ fji)) q) := by
    simpa only [b, pullback.lift_fst, Category.comp_id] using
      (inferInstance : UniversallyClosed (pullback.fst (D.map (flj ≫ fji)) (π ≫ q)))
  have := UniversallyClosed.of_comp_surjective b (pullback.fst (D.map (flj ≫ fji)) q)
  exact ⟨l, flj ≫ fji, ⟨⟩⟩

include hc in
/-- A separated finitely presented scheme over a member becomes proper at a finite stage if,
over the limit, it receives a surjective morphism from the base change of a proper finitely
presented scheme over that member. Only the covering morphism needs to be given over the limit. -/
theorem exists_isProper_pullback_fst_of_isLimit_of_surjective
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I} {X Z : Scheme.{u}}
    (q : X ⟶ D.obj i) [IsSeparated q] [QuasiCompact q] [LocallyOfFinitePresentation q]
    (r : Z ⟶ D.obj i) [IsProper r] [LocallyOfFinitePresentation r]
    (a : pullback (c.π.app i) r ⟶ pullback (c.π.app i) q) [Surjective a]
    (ha : a ≫ pullback.fst _ _ = pullback.fst _ _) :
    ∃ (j : I) (fji : j ⟶ i), IsProper (pullback.fst (D.map fji) q) := by
  obtain ⟨j, fji, b, hb₁, hb₂⟩ := exists_pullbackMap_comp_eq_of_isLimit hc a ha
  let qj := pullback.fst (D.map fji) q
  let rj := pullback.fst (D.map fji) r
  have : QuasiCompact (b ≫ qj) := hb₁ ▸ inferInstanceAs (QuasiCompact rj)
  have : QuasiCompact b := QuasiCompact.of_comp b qj
  have : LocallyOfFinitePresentation (b ≫ qj) :=
    hb₁ ▸ inferInstanceAs (LocallyOfFinitePresentation rj)
  have : LocallyOfFinitePresentation b := locallyOfFinitePresentation_of_comp b qj
  have : Surjective (pullback.map (c.π.app j) rj (c.π.app j) qj (𝟙 _) b (𝟙 _)
      (by simp) (by simpa using hb₁.symm)) :=
    (pullbackMap_iff_of_pullbackMap_comp_eq (P := @Surjective) fji ha hb₁ hb₂).mpr ‹_›
  obtain ⟨k, fkj, hk⟩ := exists_surjective_pullbackMap_of_isLimit hc b hb₁
  let d := pullback.map (D.map fkj) rj (D.map fkj) qj (𝟙 _) b (𝟙 _)
    (by simp) (by simpa using hb₁.symm)
  have : Surjective d := hk
  have : UniversallyClosed (d ≫ pullback.fst (D.map fkj) qj) := by
    simpa only [d, pullback.lift_fst, Category.comp_id] using
      (inferInstance : UniversallyClosed (pullback.fst (D.map fkj) rj))
  have := UniversallyClosed.of_comp_surjective d (pullback.fst (D.map fkj) qj)
  have : IsProper (pullback.fst (D.map fkj) qj) := ⟨⟩
  exact ⟨k, fkj ≫ fji,
    (MorphismProperty.pullback_fst_pullback_fst_iff (P := @IsProper)
      (D.map fkj) (D.map fji) q (D.map_comp fkj fji).symm).mp this⟩

end TauCeti.AlgebraicGeometry.Scheme
