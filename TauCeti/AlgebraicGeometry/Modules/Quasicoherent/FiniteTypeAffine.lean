/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.FiniteTypeImage
public import TauCeti.AlgebraicGeometry.Modules.Restriction.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Finite-type submodules over a quasi-compact open of an affine scheme

Let `X` be an affine scheme, `N` a quasi-coherent `𝒪_X`-module and `V ⊆ X` a quasi-compact open
over which `N` is of finite type. Then `N` has a finite-type quasi-coherent submodule that is all
of `N` over `V`. Cover `V` by finitely many basic opens `D(f)`; over each, finitely many
generators of the sections lie in a finite-type quasi-coherent submodule; and the finite-type
quasi-coherent submodules form a directed family. This is the input for the induction on the
number of affine opens in the proof of Stacks, Lemma 28.23.2 (01PF).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_of_fac`: a submodule containing a
  submodule that is everything over an open is everything over that open.
* `AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_isIso_restrict`: the finite-type
  submodule over a quasi-compact open of an affine scheme.

## References

* The Stacks Project, Lemma 28.23.2 (Tag 01PF).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A submodule `i : N' ⟶ N` through which a submodule `i₁ : N₁ ⟶ N` factors is an isomorphism
over every open over which `i₁` is. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_of_fac
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] {N₁ N' N : X.Modules} {i₁ : N₁ ⟶ N}
    {i : N' ⟶ N} [Mono i] (g : N₁ ⟶ N') (hg : g ≫ i = i₁)
    [IsIso ((Scheme.Modules.restrictFunctor j).map i₁)] :
    IsIso ((Scheme.Modules.restrictFunctor j).map i) := by
  have : Mono ((Scheme.Modules.restrictFunctor j).map i) :=
    Functor.map_mono (Scheme.Modules.restrictFunctor j) i
  have h := (Scheme.Modules.restrictFunctor j).map_comp g i
  rw [hg] at h
  have : Epi ((Scheme.Modules.restrictFunctor j).map i) := epi_of_epi_fac h.symm
  exact isIso_of_mono_of_epi _

/-- **Finite-type submodules over a quasi-compact open of an affine scheme.** Let `X` be affine,
`N` a quasi-coherent `𝒪_X`-module and `V ⊆ X` a quasi-compact open such that `N|_V` is of finite
type. Then there is a finite-type quasi-coherent submodule `i : N' ⟶ N` that is an isomorphism
over `V`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_isIso_restrict
    [IsAffine X] {N : X.Modules} [N.IsQuasicoherent] (V : X.Opens) (hV : IsCompact (V : Set X))
    [(N.restrict V.ι).IsFiniteType] :
    ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (_ : N'.IsFiniteType) (i : N' ⟶ N) (_ : Mono i),
      IsIso ((Scheme.Modules.restrictFunctor V.ι).map i) := by
  classical
  obtain ⟨s, hs, hsV⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen.mp ⟨hV, V.isOpen⟩
  have hle (f : Γ(X, ⊤)) (hf : f ∈ s) : X.basicOpen f ≤ V := fun x hx ↦ by
    rw [← SetLike.mem_coe, hsV]
    exact Set.mem_biUnion hf hx
  let W (f : Γ(X, ⊤)) : V.toScheme.Opens := V.ι ⁻¹ᵁ X.basicOpen f
  -- Over each basic open `D(f) ⊆ V`, seen as the open `W f` of `V`.
  have key (f : Γ(X, ⊤)) (hf : f ∈ s) :
      ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (_ : N'.IsFiniteType) (i : N' ⟶ N)
        (_ : Mono i), IsIso ((Scheme.Modules.restrictFunctor ((W f).ι ≫ V.ι)).map i) := by
    have : IsAffine (W f) := ((isAffineOpen_top X).basicOpen f).preimage_of_isOpenImmersion V.ι
      (by rw [Scheme.Opens.opensRange_ι]; exact hle f hf)
    have : ((Scheme.Modules.restrictFunctor V.ι ⋙
        Scheme.Modules.restrictFunctor (W f).ι).obj N).IsFiniteType :=
      inferInstanceAs ((N.restrict V.ι).restrict (W f).ι).IsFiniteType
    have : (N.restrict ((W f).ι ≫ V.ι)).IsFiniteType :=
      SheafOfModules.IsFiniteType.of_iso (R := (W f).toScheme.ringCatSheaf)
        ((Scheme.Modules.restrictFunctorComp (W f).ι V.ι).app N).symm
    refine Scheme.Modules.exists_isFiniteType_mono_isIso_restrict_basicOpen _ f ?_
    rw [Scheme.Hom.comp_image, Scheme.Opens.ι_image_top,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (hle f hf)]
  -- Combine finitely many of them, by directedness.
  have comb (t : Finset Γ(X, ⊤)) (ht : ∀ f ∈ t, f ∈ s) :
      ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (_ : N'.IsFiniteType) (i : N' ⟶ N)
        (_ : Mono i), ∀ f ∈ t, IsIso ((Scheme.Modules.restrictFunctor ((W f).ι ≫ V.ι)).map i) := by
    induction t using Finset.induction_on with
    | empty =>
      obtain ⟨N', h₁, h₂, i, h₃, -⟩ :=
        Scheme.Modules.exists_isFiniteType_mono_sections (N := N) (I := PEmpty.{u + 1})
          PEmpty.elim
      exact ⟨N', h₁, h₂, i, h₃, by simp⟩
    | insert a t ha ih =>
      obtain ⟨N₁, _, _, i₁, _, h₁⟩ := key a (ht a (Finset.mem_insert_self a t))
      obtain ⟨N₂, _, _, i₂, _, h₂⟩ := ih fun f hf ↦ ht f (Finset.mem_insert_of_mem hf)
      obtain ⟨N', _, _, i, _, g₁, g₂, hg₁, hg₂⟩ :=
        Scheme.Modules.exists_isFiniteType_mono_factors i₁ i₂
      refine ⟨N', inferInstance, inferInstance, i, inferInstance, fun f hf ↦ ?_⟩
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact Scheme.Modules.isIso_restrictFunctor_map_of_fac _ g₁ hg₁
      · have := h₂ f hf
        exact Scheme.Modules.isIso_restrictFunctor_map_of_fac _ g₂ hg₂
  obtain ⟨N', _, _, i, _, hi⟩ := comb hs.toFinset fun f hf ↦ hs.mem_toFinset.mp hf
  refine ⟨N', inferInstance, inferInstance, i, inferInstance, ?_⟩
  -- The opens `W f` cover `V`, and `i` is an isomorphism over each of them.
  let U : hs.toFinset → V.toScheme.Opens := fun f ↦ W f.1
  have hU : TopologicalSpace.IsOpenCover U := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    have hx : V.ι x ∈ V.ι.opensRange := ⟨x, rfl⟩
    rw [Scheme.Opens.opensRange_ι, ← SetLike.mem_coe, hsV] at hx
    obtain ⟨f, hf, hfx⟩ := Set.mem_iUnion₂.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hs.mem_toFinset.mpr hf⟩, hfx⟩
  refine (Scheme.Modules.isIso_iff_of_isOpenCover hU _).mpr fun f ↦ ?_
  have := hi f.1 f.2
  have : IsIso ((Scheme.Modules.restrictFunctor (W f.1).ι).map
      ((Scheme.Modules.restrictFunctor V.ι).map i)) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorComp (W f.1).ι V.ι) i).mp this
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback (W f.1).ι) _).mp this

end TauCeti.AlgebraicGeometry
