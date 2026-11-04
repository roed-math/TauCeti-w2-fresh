/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# The connecting map of a degreewise split short exact sequence

Let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence of cochain complexes in an abelian category
which splits in every degree, with splittings `σ`. Mathlib attaches to it the morphism
`CochainComplex.homOfDegreewiseSplit S σ : X₃ ⟶ X₁⟦1⟧`, given in degree `n` by
`s ≫ d ≫ r : X₃ⁿ ⟶ X₂ⁿ ⟶ X₂ⁿ⁺¹ ⟶ X₁ⁿ⁺¹`. We show that the map it induces in cohomology is the
connecting map `Hⁿ(X₃) ⟶ Hⁿ⁺¹(X₁)` of the long exact cohomology sequence
(`CochainComplex.homologyMap_homOfDegreewiseSplit`).

This is the form in which the first differential of the spectral sequence of a filtered complex
is computed when the filtration splits degreewise, as for the row filtration of the total complex
of a bicomplex.
-/

public section

open CategoryTheory Limits HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (eval C _ n)).Splitting) (hS : S.ShortExact)

/-- **The connecting map of a degreewise split short exact sequence.** For a short exact
sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of cochain complexes with degreewise splittings `σ`, the map
`Hⁿ(X₃) ⟶ Hⁿ(X₁⟦1⟧) = Hⁿ⁺¹(X₁)` induced by `homOfDegreewiseSplit S σ : X₃ ⟶ X₁⟦1⟧` is the
connecting map of the long exact cohomology sequence. -/
lemma homologyMap_homOfDegreewiseSplit (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    homologyMap (homOfDegreewiseSplit S σ) n₀ =
      hS.δ n₀ n₁ h ≫
        ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso 1 n₀ n₁ (by lia)).inv.app S.X₁ := by
  subst h
  have hsg := (σ n₀).s_g
  dsimp at hsg
  -- A cycle `z` of `X₃` lifts to `z ≫ s` in `X₂`, whose differential is `z ≫ s ≫ d ≫ r` in `X₁`.
  have hx₁ : (S.X₃.iCycles n₀ ≫ (σ n₀).s ≫ S.X₂.d n₀ (n₀ + 1) ≫ (σ (n₀ + 1)).r) ≫
      S.f.f (n₀ + 1) = (S.X₃.iCycles n₀ ≫ (σ n₀).s) ≫ S.X₂.d n₀ (n₀ + 1) := by
    have hid := (σ (n₀ + 1)).id
    dsimp at hid
    rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc,
      eq_sub_of_add_eq hid, Preadditive.comp_sub, Preadditive.comp_sub, Category.comp_id,
      ← S.g.comm_assoc, reassoc_of% hsg]
    simp
  have key := hS.δ_eq n₀ (n₀ + 1) rfl (S.X₃.iCycles n₀) (by simp) _
    (by rw [Category.assoc, hsg, Category.comp_id]) _ hx₁ (n₀ + 1 + 1) (by simp)
  refine (cancel_epi (S.X₃.homologyπ n₀)).1 ?_
  have e : S.X₃.liftCycles (S.X₃.iCycles n₀) (n₀ + 1) (by simp) (by simp) = 𝟙 _ := by
    rw [← cancel_mono (S.X₃.iCycles n₀)]
    simp
  rw [e, Category.id_comp] at key
  have e' : cyclesMap (homOfDegreewiseSplit S σ) n₀ = (S.X₁⟦(1 : ℤ)⟧).liftCycles
      (S.X₃.iCycles n₀ ≫ (homOfDegreewiseSplit S σ).f n₀) (n₀ + 1) (by simp)
      (by rw [Category.assoc, Hom.comm, iCycles_d_assoc, zero_comp]) := by
    rw [← cancel_mono ((S.X₁⟦(1 : ℤ)⟧).iCycles n₀)]
    simp
  rw [homologyπ_naturality, e', liftCycles_shift_homologyπ _ _ _ _ _ (n₀ + 1) (by lia)
    (n₀ + 1 + 1) (by simp)]
  have key' := congrArg (· ≫ ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso 1 n₀ (n₀ + 1)
    (by lia)).inv.app S.X₁) key
  refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (key'.symm.trans (Category.assoc _ _ _)))
  congr 3
  simp [cocycleOfDegreewiseSplit]

end CochainComplex
