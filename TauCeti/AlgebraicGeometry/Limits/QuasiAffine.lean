/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Quasi-compact opens of finite type in an affine scheme

Let `W ⟶ Spec R` be a quasi-compact open immersion with `W` of finite type over `ℤ`. Then there
is a finite subset `s ⊆ R` such that for every subring `A ⊆ R` containing `s`, the composite
`W ⟶ Spec R ⟶ Spec A` is still an open immersion. In particular `W` is an open subscheme of
`Spec A` for a finitely generated `ℤ`-subalgebra `A ⊆ R`, and `R` is the directed union of such
subalgebras (Stacks, Lemma 32.5.1 (01Z7)); this is the first step of absolute Noetherian
approximation.

The proof covers the image of `W` by finitely many basic opens `D(f) ⊆ Spec R`. Each `R_f` is of
finite type over `ℤ`, and `s` contains the `f` and numerators of generators of each `R_f`; then
`R_f` is the localization of `A` away from `f`, so `Spec R_f ⟶ Spec A` is an open immersion, and
the map `W ⟶ Spec A` is injective because `D(f) ⊆ Spec R` is the preimage of `D(f) ⊆ Spec A`.

## Main declarations

* `TauCeti.AlgebraicGeometry.finiteType_intCastRingHom_of_locallyOfFiniteType_terminal_from_Spec`:
  a ring whose spectrum is locally of finite type over the terminal scheme is of finite type
  over `ℤ`.
* `TauCeti.AlgebraicGeometry.exists_finset_isOpenImmersion_away_comp_SpecMap_val`: the case of a
  single basic open.
* `TauCeti.AlgebraicGeometry.Scheme.exists_finset_isOpenImmersion_comp_SpecMap_val`: Stacks 01Z7.
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

/-- If the spectrum of `R` is locally of finite type over the terminal scheme, then `ℤ → R` is
of finite type. -/
lemma finiteType_intCastRingHom_of_locallyOfFiniteType_terminal_from_Spec (R : CommRingCat.{u})
    [LocallyOfFiniteType (terminal.from (Spec R))] : (Int.castRingHom R).FiniteType := by
  let e : ⊤_ Scheme.{u} ≅ Spec (.of (ULift.{u} ℤ)) :=
    terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal
  let g : CommRingCat.of (ULift.{u} ℤ) ⟶ R :=
    CommRingCat.ofHom ((algebraMap ℤ R).comp ULift.ringEquiv.toRingHom)
  have : LocallyOfFiniteType (Spec.map g) := by
    rw [specULiftZIsTerminal.hom_ext (Spec.map g) (terminal.from (Spec R) ≫ e.hom)]
    infer_instance
  have hg : g.hom.FiniteType := HasRingHomProperty.Spec_iff.mp this
  let e' : ℤ ≃+* ULift.{u} ℤ := ULift.ringEquiv.symm
  convert hg.comp (RingHom.FiniteType.of_surjective e'.toRingHom e'.surjective)
  ext
  simp [g]

variable {R : Type u} [CommRing R]

/-- If `R_f` is of finite type over `ℤ`, there is a finite subset `s ⊆ R` containing `f` such
that for every subring `A ⊆ R` containing `s`, the ring `R_f` is the localization of `A` away
from `f`, so that `Spec R_f ⟶ Spec R ⟶ Spec A` is an open immersion. -/
lemma exists_finset_isOpenImmersion_away_comp_SpecMap_val (f : R)
    [Algebra.FiniteType ℤ (Localization.Away f)] :
    ∃ s : Finset R, f ∈ s ∧ ∀ A : Subalgebra ℤ R, (s : Set R) ⊆ A →
      IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) ≫
        Spec.map (CommRingCat.ofHom A.val.toRingHom)) := by
  classical
  obtain ⟨T, hT⟩ := Algebra.FiniteType.out (R := ℤ) (A := Localization.Away f)
  choose x hx using fun t : Localization.Away f ↦ IsLocalization.surj (Submonoid.powers f) t
  refine ⟨insert f (T.image fun t ↦ (x t).1), Finset.mem_insert_self _ _, fun A hA ↦ ?_⟩
  have hfA : f ∈ A := hA (Finset.mem_insert_self _ _)
  let fA : A := ⟨f, hfA⟩
  let : Algebra A (Localization.Away f) :=
    ((algebraMap R (Localization.Away f)).comp A.val.toRingHom).toAlgebra
  have hle : Submonoid.powers fA ≤ (Submonoid.powers f).comap A.val.toRingHom := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp [fA]⟩
  let ψ : Localization.Away fA →+* Localization.Away f :=
    IsLocalization.map (Localization.Away f) A.val.toRingHom hle
  have hψ : Function.Surjective ψ := by
    intro z
    have hz : z ∈ Algebra.adjoin ℤ (T : Set (Localization.Away f)) := hT ▸ Algebra.mem_top
    induction hz using Algebra.adjoin_induction with
    | algebraMap n => exact ⟨n, by simp⟩
    | add _ _ _ _ h₁ h₂ => exact ψ.range.add_mem h₁ h₂
    | mul _ _ _ _ h₁ h₂ => exact ψ.range.mul_mem h₁ h₂
    | mem t ht => ?_
    have hr : (x t).1 ∈ A := hA (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ht))
    obtain ⟨n, hn⟩ := (x t).2.2
    refine ⟨IsLocalization.mk' _ (⟨(x t).1, hr⟩ : A)
      (⟨fA ^ n, n, rfl⟩ : Submonoid.powers fA), ?_⟩
    rw [IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul]
    convert (hx t).symm using 3
    case e'_3 => rw [← hn]; simp [fA]
    simp
  have : IsLocalization.Away fA (Localization.Away f) := by
    refine (isLocalization_iff _ _).mpr ⟨?_, fun z ↦ ?_, fun {a b} h ↦ ?_⟩
    · rintro ⟨_, n, rfl⟩
      exact IsLocalization.map_units (Localization.Away f)
        (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
    · obtain ⟨w, rfl⟩ := hψ z
      obtain ⟨⟨a, m⟩, h⟩ := IsLocalization.surj (Submonoid.powers fA) w
      refine ⟨⟨a, m⟩, ?_⟩
      have := congr(ψ $h)
      rwa [map_mul, IsLocalization.map_eq, IsLocalization.map_eq] at this
    · obtain ⟨⟨_, n, rfl⟩, hc⟩ :=
        (IsLocalization.eq_iff_exists (Submonoid.powers f) (Localization.Away f)).mp h
      exact ⟨⟨fA ^ n, n, rfl⟩, Subtype.ext (by simpa [fA] using hc)⟩
  have := IsOpenImmersion.of_isLocalization fA (S := Localization.Away f)
  rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- Let `ι : W ⟶ Spec R` be an open immersion with `W` quasi-compact and locally of finite type
over `ℤ`. Then there is a finite subset `s ⊆ R` such that for every subring `A ⊆ R` containing
`s`, the composite `W ⟶ Spec R ⟶ Spec A` is an open immersion. Taking `A = ℤ[s]` makes `W` an
open subscheme of the spectrum of a finitely generated `ℤ`-algebra, and since these `A` are
cofinal among the subrings of `R`, `R` is the directed union of such subrings.
Stacks, Lemma 32.5.1 (01Z7). -/
theorem Scheme.exists_finset_isOpenImmersion_comp_SpecMap_val {W : Scheme.{u}}
    (ι : W ⟶ Spec (.of R)) [IsOpenImmersion ι] [CompactSpace W]
    [LocallyOfFiniteType (terminal.from W)] :
    ∃ s : Finset R, ∀ A : Subalgebra ℤ R, (s : Set R) ⊆ A →
      IsOpenImmersion (ι ≫ Spec.map (CommRingCat.ofHom A.val.toRingHom)) := by
  classical
  obtain ⟨F, hF⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp
    ⟨isCompact_range ι.continuous, ι.isOpenEmbedding.isOpen_range⟩
  let j (f : R) := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))
  have hF' (p : Spec (.of R)) : p ∈ Set.range ι ↔ ∃ f ∈ F, f ∉ p.asIdeal :=
    (Set.ext_iff.mp hF p).symm.trans (by
      change ¬ (F : Set R) ⊆ p.asIdeal ↔ _
      simp [Set.not_subset])
  have hj (f : R) (p : Spec (.of R)) : p ∈ Set.range (j f) ↔ f ∉ p.asIdeal :=
    Set.ext_iff.mp (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f) p
  have hmem (x : W) : ∃ f ∈ F, ι x ∈ Set.range (j f) := by
    obtain ⟨f, hf, hfx⟩ := (hF' (ι x)).mp (Set.mem_range_self x)
    exact ⟨f, hf, (hj f _).mpr hfx⟩
  have hle (f : R) (hf : f ∈ F) : Set.range (j f) ⊆ Set.range ι :=
    fun p hp ↦ (hF' p).mpr ⟨f, hf, (hj f p).mp hp⟩
  have hft (f : R) (hf : f ∈ F) : Algebra.FiniteType ℤ (Localization.Away f) := by
    have : LocallyOfFiniteType (terminal.from (Spec (.of (Localization.Away f)))) := by
      rw [terminal.hom_ext (terminal.from _)
        (IsOpenImmersion.lift ι (j f) (hle f hf) ≫ terminal.from W)]
      infer_instance
    refine RingHom.finiteType_algebraMap.mp ?_
    convert finiteType_intCastRingHom_of_locallyOfFiniteType_terminal_from_Spec
      (.of (Localization.Away f))
    exact RingHom.ext_int _ _
  choose! s hfs hs using fun f (hf : f ∈ F) ↦
    have := hft f hf
    exists_finset_isOpenImmersion_away_comp_SpecMap_val f
  refine ⟨F.biUnion s, fun A hA ↦ ?_⟩
  have hsA (f : R) (hf : f ∈ F) : (s f : Set R) ⊆ A :=
    fun y hy ↦ hA (Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨f, hf, hy⟩))
  let g := Spec.map (CommRingCat.ofHom A.val.toRingHom)
  refine IsOpenImmersion.of_forall_source_exists _ (fun x y hxy ↦ ?_) fun x ↦ ?_
  · obtain ⟨f, hf, x', hx'⟩ := hmem x
    let fA : A := ⟨f, hsA f hf (hfs f hf)⟩
    have hy : ι y ∈ Set.range (j f) := by
      have hx : f ∉ (ι x).asIdeal := (hj f _).mp ⟨x', hx'⟩
      have hg : g (ι x) = g (ι y) := hxy
      refine (hj f _).mpr fun h ↦ hx ?_
      have : fA ∈ (g (ι y)).asIdeal := h
      exact (hg ▸ this : fA ∈ (g (ι x)).asIdeal)
    obtain ⟨y', hy'⟩ := hy
    have := hs f hf A (hsA f hf)
    have : x' = y' := (j f ≫ g).isOpenEmbedding.injective (by
      simp only [Scheme.Hom.comp_apply]
      rw [hx', hy']
      exact hxy)
    exact ι.isOpenEmbedding.injective (by rw [← hx', ← hy', this])
  · obtain ⟨f, hf, x', hx'⟩ := hmem x
    refine ⟨_, IsOpenImmersion.lift ι (j f) (hle f hf), inferInstance, ⟨x', ?_⟩, ?_⟩
    · apply ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]
      exact hx'
    · rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact hs f hf A (hsA f hf)

end TauCeti.AlgebraicGeometry
