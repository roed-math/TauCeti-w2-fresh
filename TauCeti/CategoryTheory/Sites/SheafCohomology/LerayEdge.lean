/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import TauCeti.Lookahead.LeraySpectralSequence.Stubs

/-!
# The edge map of the Leray spectral sequence

Let `pb : Sheaf J Ab ⥤ Sheaf K Ab` be an exact additive functor between categories of abelian
sheaves on sites `(C, J)` and `(D, K)` with a right adjoint `pf`, and let `c : ℤ_K ⟶ pb ℤ_J` be a
map between the constant sheaves `ℤ`. For a morphism of sites, `pb` is the inverse image `f⁻¹`,
`pf` is the pushforward `f_*` and `c` is the canonical comparison of constant sheaves.

For an abelian sheaf `F` on `(D, K)`, the edge map `E₂^{n,0} = Hⁿ(C, f_* F) ⟶ Hⁿ(D, F)` of the
Leray spectral sequence is the pullback `Sheaf.H.pullback pb c` of cohomology to
`Hⁿ(D, f⁻¹ f_* F)` followed by the map induced by the counit `f⁻¹ f_* F ⟶ F`
(Stacks, Lemma 21.14.5 (0732) and Remark 21.14.4 (08J6)). This file defines it
(`Sheaf.H.lerayEdge`) and proves that it is natural in `F`, compatible with the connecting
homomorphisms of short exact sequences that stay exact after pushforward, and in degree zero
given by the adjunction, hence bijective when `c` is an isomorphism. It also records the input
on which the Leray spectral sequence rests: `f_*` sends injective sheaves to injective sheaves,
whose higher cohomology vanishes.

## Main declarations

* `CategoryTheory.Sheaf.H.lerayEdge`: the edge map `Hⁿ(C, f_* F) →+ Hⁿ(D, F)`.
* `CategoryTheory.Sheaf.H.lerayEdge_naturality`: naturality in `F`.
* `CategoryTheory.Sheaf.H.lerayEdge_δ`: compatibility with connecting homomorphisms.
* `CategoryTheory.Sheaf.H.addEquiv₀_lerayEdge`, `CategoryTheory.Sheaf.H.lerayEdge_zero_bijective`:
  the edge map in degree zero.
* `CategoryTheory.Sheaf.H.subsingleton_H_obj_of_injective`: `Hⁿ⁺¹(C, f_* I) = 0` for an
  injective sheaf `I`.
-/

public section

open CategoryTheory Abelian Limits AddCommGrpCat

universe w w₁ w₂

namespace CategoryTheory.Sheaf.H

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {D : Type*} [Category* D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{w₁} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w₂} (Sheaf K AddCommGrpCat.{w})]
  {pb : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}} [pb.Additive]
  [PreservesFiniteLimits pb] [PreservesFiniteColimits pb]
  {pf : Sheaf K AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w}} (adj : pb ⊣ pf)
  (c : (constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ)) ⟶
    pb.obj ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))))

noncomputable section

/-- The edge map `Hⁿ(C, f_* F) →+ Hⁿ(D, F)` of the Leray spectral sequence, for an exact functor
`pb` with right adjoint `pf` and a comparison `c : ℤ_K ⟶ pb ℤ_J` of constant sheaves: the
pullback of cohomology to `Hⁿ(D, pb (pf F))` followed by the map induced by the counit
`pb (pf F) ⟶ F`. -/
def lerayEdge (F : Sheaf K AddCommGrpCat.{w}) (n : ℕ) : H (pf.obj F) n →+ H F n :=
  (H.map (adj.counit.app F) n).comp (pullback pb c (pf.obj F) n)

lemma lerayEdge_apply {F : Sheaf K AddCommGrpCat.{w}} {n : ℕ} (x : H (pf.obj F) n) :
    lerayEdge adj c F n x = H.map (adj.counit.app F) n (pullback pb c (pf.obj F) n x) := (rfl)

/-- The edge map is natural in the coefficient sheaf. -/
lemma lerayEdge_naturality {F₁ F₂ : Sheaf K AddCommGrpCat.{w}} (φ : F₁ ⟶ F₂) {n : ℕ}
    (x : H (pf.obj F₁) n) :
    lerayEdge adj c F₂ n (H.map (pf.map φ) n x) = H.map φ n (lerayEdge adj c F₁ n x) := by
  rw [lerayEdge_apply, lerayEdge_apply, pullback_naturality, ← H.map_comp_apply,
    ← H.map_comp_apply, adj.counit_naturality φ]

/-- The edge map commutes with the connecting homomorphisms of a short exact sequence `S` of
abelian sheaves on `(D, K)` whose pushforward `pf S` is short exact. -/
lemma lerayEdge_δ [pf.PreservesZeroMorphisms] {S : ShortComplex (Sheaf K AddCommGrpCat.{w})}
    (hS : S.ShortExact) (hS' : (S.map pf).ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : H (pf.obj S.X₃) n₀) :
    lerayEdge adj c S.X₁ n₁ (H.δ hS' n₀ n₁ h x) =
      H.δ hS n₀ n₁ h (lerayEdge adj c S.X₃ n₀ x) := by
  let φ : (S.map pf).map pb ⟶ S :=
    { τ₁ := adj.counit.app S.X₁
      τ₂ := adj.counit.app S.X₂
      τ₃ := adj.counit.app S.X₃ }
  exact (congrArg (H.map (adj.counit.app S.X₁) n₁) (pullback_δ pb c hS' n₀ n₁ h x)).trans
    (H.δ_naturality n₀ n₁ h (hS'.map_of_exact pb) hS φ _).symm

/-- In degree zero, the edge map sends the class of a map `g : ℤ_J ⟶ f_* F` to its adjoint
`ℤ_K ⟶ pb ℤ_J ⟶ F`, precomposed with `c`. -/
@[simp]
lemma addEquiv₀_lerayEdge {F : Sheaf K AddCommGrpCat.{w}} (x : H (pf.obj F) 0) :
    Ext.addEquiv₀ (lerayEdge adj c F 0 x) = c ≫ (adj.homEquiv _ _).symm (Ext.addEquiv₀ x) := by
  simp [lerayEdge_apply, H.addEquiv₀_map, Adjunction.homEquiv_counit]

/-- When the comparison `c` of constant sheaves is an isomorphism, as it is for a morphism of
sites, the edge map is bijective in degree zero: both sides are the global sections of `F`. -/
lemma lerayEdge_zero_bijective [IsIso c] (F : Sheaf K AddCommGrpCat.{w}) :
    Function.Bijective (lerayEdge adj c F 0) := by
  rw [← (Ext.addEquiv₀ (X := (constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ)))
    (Y := F)).bijective.of_comp_iff']
  have h : ⇑Ext.addEquiv₀ ∘ ⇑(lerayEdge adj c F 0) =
      (c ≫ ·) ∘ (adj.homEquiv _ _).symm ∘ Ext.addEquiv₀ :=
    funext (addEquiv₀_lerayEdge adj c)
  refine h ▸ Function.Bijective.comp ⟨fun g g' hg ↦ ?_, fun g ↦ ⟨inv c ≫ g, by simp⟩⟩
    ((adj.homEquiv _ _).symm.bijective.comp Ext.addEquiv₀.bijective)
  simpa using congrArg (inv c ≫ ·) hg

end

omit [HasExt.{w₂} (Sheaf K AddCommGrpCat.{w})] in
include adj in
/-- The pushforward `pf I` of an injective sheaf `I` along a functor with an exact left adjoint is
injective, so its higher cohomology vanishes: this is the acyclicity of `f_*` of injectives on
which the Leray spectral sequence rests (Stacks, Lemma 21.14.1 (072Z)). -/
lemma subsingleton_H_obj_of_injective (I : Sheaf K AddCommGrpCat.{w}) [Injective I] (n : ℕ) :
    Subsingleton (H (pf.obj I) (n + 1)) :=
  have := Injective.injective_of_adjoint adj I
  inferInstance

end CategoryTheory.Sheaf.H
