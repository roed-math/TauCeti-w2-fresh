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
given by the adjunction, hence bijective when `c` is an isomorphism, and injective in degree one,
the first map of the five-term exact sequence. It also records the input
on which the Leray spectral sequence rests: `f_*` sends injective sheaves to injective sheaves,
whose higher cohomology vanishes.

## Main declarations

* `CategoryTheory.Sheaf.H.lerayEdge`: the edge map `Hⁿ(C, f_* F) →+ Hⁿ(D, F)`.
* `CategoryTheory.Sheaf.H.lerayEdge_naturality`: naturality in `F`.
* `CategoryTheory.Sheaf.H.lerayEdge_δ`: compatibility with connecting homomorphisms.
* `CategoryTheory.Sheaf.H.addEquiv₀_lerayEdge`, `CategoryTheory.Sheaf.H.lerayEdge_zero_bijective`:
  the edge map in degree zero.
* `CategoryTheory.Sheaf.H.lerayEdge_one_injective`: the edge map is injective in degree one.
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

/-- When the comparison `c` of constant sheaves is an isomorphism, the edge map is injective in
degree one: `H¹(C, f_* F) ⟶ H¹(D, F)` is the first map of the five-term exact sequence of the
Leray spectral sequence (Stacks, Lemma 21.14.5 (0732)). Embed `F` into an injective sheaf `I`. As
`H¹(C, f_* I) = 0`, a class of `H¹(C, f_* F)` is the connecting image of a section `y` of the
cokernel `Q` of `f_* F ⟶ f_* I`. If its edge image vanishes, the adjoint of `y` lifts along
`I ⟶ I / F`, so `y` lifts to `f_* I`, because `Q` embeds into `f_* (I / F)`. -/
lemma lerayEdge_one_injective [IsIso c] [EnoughInjectives (Sheaf K AddCommGrpCat.{w})]
    (F : Sheaf K AddCommGrpCat.{w}) : Function.Injective (lerayEdge adj c F 1) := by
  have := adj.rightAdjoint_preservesLimits
  have := adj.right_adjoint_additive
  let ι := Injective.ι F
  have hS : (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact ι
      mono_f := inferInstanceAs (Mono ι) }
  have hT : (ShortComplex.mk (pf.map ι) (cokernel.π (pf.map ι))
      (cokernel.condition (pf.map ι))).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact (pf.map ι)
      mono_f := inferInstanceAs (Mono (pf.map ι)) }
  -- The comparison `Q ⟶ f_* (I / F)` is a monomorphism, as `f_*` is left exact.
  let g₃ : cokernel (pf.map ι) ⟶ pf.obj (cokernel ι) :=
    cokernel.desc (pf.map ι) (pf.map (cokernel.π ι)) (by
      rw [← pf.map_comp, cokernel.condition, pf.map_zero])
  have : Mono g₃ :=
    (hS.exact.map_of_mono_of_preservesKernel pf hS.mono_f inferInstance).mono_cokernelDesc
  let φ : (ShortComplex.mk (pf.map ι) (cokernel.π (pf.map ι)) (cokernel.condition _)).map pb ⟶
      ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι) :=
    { τ₁ := adj.counit.app F
      τ₂ := adj.counit.app (Injective.under F)
      τ₃ := pb.map g₃ ≫ adj.counit.app (cokernel ι)
      comm₁₂ := (adj.counit.naturality ι).symm
      comm₂₃ := by
        change _ = pb.map (cokernel.π (pf.map ι)) ≫ pb.map g₃ ≫ _
        rw [← pb.map_comp_assoc, cokernel.π_desc]
        exact (adj.counit.naturality (cokernel.π ι)).symm }
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  have := subsingleton_H_obj_of_injective adj (Injective.under F) 0
  obtain ⟨y, hy⟩ := longSequence_exact₁ hT x (Subsingleton.elim (α := H (pf.obj _) 1) _ _) rfl
  have hx' : H.δ hS 0 1 rfl (H.map φ.τ₃ 0 (pullback pb c _ 0 y)) = 0 :=
    (H.δ_naturality 0 1 rfl (hT.map_of_exact pb) hS φ _).trans
      ((congrArg (H.map φ.τ₁ 1) (pullback_δ pb c hT 0 1 rfl y)).symm.trans
        ((congrArg (lerayEdge adj c F 1) hy).trans hx))
  obtain ⟨z, hz⟩ := longSequence_exact₃ hS _ rfl hx'
  have hz' := congrArg Ext.addEquiv₀ hz
  rw [H.addEquiv₀_map, H.addEquiv₀_map, addEquiv₀_pullback] at hz'
  -- The adjoint of the lift of `y` to `I / F`.
  let a : _ ⟶ pf.obj (Injective.under F) := (adj.homEquiv _ _) (inv c ≫ Ext.addEquiv₀ z)
  have ha : a ≫ cokernel.π (pf.map ι) = Ext.addEquiv₀ y := by
    rw [← cancel_mono g₃, Category.assoc, cokernel.π_desc, ← adj.homEquiv_naturality_right]
    change (adj.homEquiv _ _) (inv c ≫ Ext.addEquiv₀ z ≫ cokernel.π ι) = _
    rw [hz', Category.assoc, IsIso.inv_hom_id_assoc]
    change (adj.homEquiv _ _) (pb.map _ ≫ pb.map g₃ ≫ _) = _
    rw [← pb.map_comp_assoc, ← Adjunction.homEquiv_counit, Equiv.apply_symm_apply]
  obtain rfl : y = H.map (cokernel.π (pf.map ι)) 0 (Ext.addEquiv₀.symm a) :=
    Ext.addEquiv₀.injective (by rw [H.addEquiv₀_map, AddEquiv.apply_symm_apply, ha])
  rw [← hy]
  change ((Ext.addEquiv₀.symm a).comp (Ext.mk₀ _) (add_zero 0)).comp hT.extClass (zero_add 1) = 0
  rw [Ext.comp_assoc_of_second_deg_zero, hT.comp_extClass, Ext.comp_zero]

end CategoryTheory.Sheaf.H
