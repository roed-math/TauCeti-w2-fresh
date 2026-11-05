/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Flat base change of power-torsion modules

Let `B` be a flat `A`-algebra and `I` an ideal of `A` such that `A ⧸ I → B ⧸ I B` is bijective.
Then `N → B ⊗[A] N`, `n ↦ 1 ⊗ n`, is bijective for every `A`-module `N` in which each element is
killed by a power of `I`.

If `I` kills `N`, then `B ⊗[A] N = (B ⧸ I B) ⊗[A] N` and `A ⊗[A] N = (A ⧸ I) ⊗[A] N`, so the claim
is the bijection `A ⧸ I → B ⧸ I B` tensored with `N`. If `I^(k+1)` kills `N`, the sequence
`0 → I N → N → N ⧸ I N → 0` reduces to the cases `I^k` and `I`, by flatness of `B` and an
elementwise five lemma. An `I`-power-torsion module is the union of the `I^k`-torsion submodules,
and flatness makes `B ⊗[A] -` preserve these inclusions.

This is the module-theoretic input of flat excision for local cohomology (Stacks, Lemma 47.9.7
(0ALZ)), since local cohomology modules are `I`-power torsion.

## Main results

* `TauCeti.bijective_rTensor_mkₐ_of_smul_eq_zero`: if `I` kills `N`, then
  `C ⊗[A] N → (C ⧸ J) ⊗[A] N` is bijective for every ideal `J ≤ I C`.
* `TauCeti.bijective_one_tmul_of_pow_smul_eq_zero`: the case of a module killed by `I^k`.
* `TauCeti.bijective_one_tmul_of_forall_exists_pow_smul_eq_zero`: the case of an `I`-power-torsion
  module.
-/

public section

universe u

open TensorProduct

namespace TauCeti

variable {A : Type u} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]

/-- If `I` kills `N`, then `C ⊗[A] N → (C ⧸ J) ⊗[A] N` is bijective for every ideal `J ≤ I C`. -/
theorem bijective_rTensor_mkₐ_of_smul_eq_zero (C : Type*) [CommRing C] [Algebra A C]
    {I : Ideal A} {J : Ideal C} (hJ : J ≤ I.map (algebraMap A C))
    (hN : ∀ r ∈ I, ∀ n : N, r • n = 0) :
    Function.Bijective ((Ideal.Quotient.mkₐ A J).toLinearMap.rTensor N) := by
  have key : ∀ c ∈ I.map (algebraMap A C), ∀ n : N, (c ⊗ₜ[A] n : C ⊗[A] N) = 0 := by
    intro c hc n
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, hr, rfl⟩ := hx
      rw [Algebra.algebraMap_eq_smul_one, smul_tmul, hN r hr n, tmul_zero]
    | zero => rw [zero_tmul]
    | add x y _ _ hx hy => rw [add_tmul, hx, hy, add_zero]
    | smul c x _ hx => rw [smul_eq_mul, ← smul_eq_mul, ← smul_tmul', hx, smul_zero]
  refine ⟨?_, LinearMap.rTensor_surjective _ (Ideal.Quotient.mkₐ_surjective A J)⟩
  have hex : Function.Exact (J.restrictScalars A).subtype (Ideal.Quotient.mkₐ A J).toLinearMap :=
    fun x ↦ by simp [Ideal.Quotient.eq_zero_iff_mem]
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (rTensor_exact N hex (Ideal.Quotient.mkₐ_surjective A J) x).mp hx
  clear hx
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => rw [map_add, hy, hz, add_zero]
  | tmul c n => exact key c (hJ c.2) n


variable {B : Type*} [CommRing B] [Algebra A B] {I : Ideal A}

/-- If `A ⧸ I → B ⧸ I B` is bijective and `I` kills `N`, then `N → B ⊗[A] N` is bijective. -/
theorem bijective_one_tmul_of_smul_eq_zero
    (hI : Function.Bijective (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
      Ideal.le_comap_map))
    (hN : ∀ r ∈ I, ∀ n : N, r • n = 0) :
    Function.Bijective (fun n : N ↦ (1 : B) ⊗ₜ[A] n) := by
  have hB := bijective_rTensor_mkₐ_of_smul_eq_zero B (J := I.map (algebraMap A B)) le_rfl hN
  have hA := bijective_rTensor_mkₐ_of_smul_eq_zero A (J := I)
    (by rw [Algebra.algebraMap_self, Ideal.map_id]) hN
  let g : (A ⧸ I) →ₗ[A] (B ⧸ I.map (algebraMap A B)) :=
    (Ideal.quotientMapₐ (I.map (algebraMap A B)) (Algebra.ofId A B) Ideal.le_comap_map).toLinearMap
  have hg : Function.Bijective (g.rTensor N) :=
    (LinearEquiv.rTensor N (LinearEquiv.ofBijective g hI)).bijective
  have key : (Ideal.Quotient.mkₐ A (I.map (algebraMap A B))).toLinearMap.rTensor N ∘
      (fun n : N ↦ (1 : B) ⊗ₜ[A] n) =
      g.rTensor N ∘ (Ideal.Quotient.mkₐ A I).toLinearMap.rTensor N ∘
        (TensorProduct.lid A N).symm := by
    funext n
    simp [g]
  exact (hB.of_comp_iff' _).mp (key ▸ hg.comp (hA.comp (TensorProduct.lid A N).symm.bijective))


/-- If `B` is flat over `A` and `A ⧸ I → B ⧸ I B` is bijective, then `N → B ⊗[A] N` is bijective
for every `A`-module `N` killed by a power of `I`. -/
theorem bijective_one_tmul_of_pow_smul_eq_zero [Module.Flat A B]
    (hI : Function.Bijective (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
      Ideal.le_comap_map)) (k : ℕ) :
    ∀ (N : Type u) [AddCommGroup N] [Module A N], (∀ r ∈ I ^ k, ∀ n : N, r • n = 0) →
      Function.Bijective (fun n : N ↦ (1 : B) ⊗ₜ[A] n) := by
  induction k with
  | zero =>
    intro N _ _ hN
    have : Subsingleton N := ⟨fun x y ↦ by
      rw [← one_smul A x, ← one_smul A y, hN 1 (by simp) x, hN 1 (by simp) y]⟩
    refine ⟨fun x y _ ↦ Subsingleton.elim x y, fun y ↦ ⟨0, ?_⟩⟩
    have : Subsingleton (B ⊗[A] N) := inferInstance
    exact Subsingleton.elim _ _
  | succ k ih =>
    intro N _ _ hN
    let N₁ : Submodule A N := I • ⊤
    have h₁ : ∀ r ∈ I ^ k, ∀ n : N₁, r • n = 0 := by
      rintro r hr ⟨n, hn⟩
      refine Subtype.ext ?_
      simp only [SetLike.mk_smul_mk, Submodule.coe_zero]
      exact Submodule.smul_induction_on (p := fun x ↦ r • x = 0) hn
        (fun s hs m _ ↦ by rw [smul_smul, hN _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hr hs)])
        (fun x y hx hy ↦ by rw [smul_add, hx, hy, add_zero])
    have h₂ : ∀ r ∈ I, ∀ n : N ⧸ N₁, r • n = 0 := by
      intro r hr n
      obtain ⟨n, rfl⟩ := N₁.mkQ_surjective n
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hr trivial
    have hb₁ := ih N₁ h₁
    have hb₂ := bijective_one_tmul_of_smul_eq_zero hI h₂
    have hinj : Function.Injective (N₁.subtype.lTensor B) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ N₁.injective_subtype
    have hex : Function.Exact (N₁.subtype.lTensor B) (N₁.mkQ.lTensor B) :=
      lTensor_exact B (LinearMap.exact_subtype_mkQ N₁) N₁.mkQ_surjective
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
    · rw [← sub_eq_zero]
      have hxy' : (1 : B) ⊗ₜ[A] (x - y) = 0 := by dsimp only at hxy; rw [tmul_sub, hxy, sub_self]
      obtain ⟨m, hm⟩ : x - y ∈ LinearMap.range N₁.subtype := by
        rw [Submodule.range_subtype, ← Submodule.Quotient.mk_eq_zero]
        apply hb₂.1
        change (1 : B) ⊗ₜ[A] N₁.mkQ (x - y) = (1 : B) ⊗ₜ[A] (0 : N ⧸ N₁)
        rw [tmul_zero, ← LinearMap.lTensor_tmul, hxy', map_zero]
      rw [← hm]
      have : (1 : B) ⊗ₜ[A] m = (1 : B) ⊗ₜ[A] (0 : N₁) := by
        apply hinj
        rw [LinearMap.lTensor_tmul, hm, hxy', tmul_zero, map_zero]
      rw [hb₁.1 this, map_zero]
    · obtain ⟨x, hx⟩ := hb₂.2 (N₁.mkQ.lTensor B y)
      obtain ⟨n, rfl⟩ := N₁.mkQ_surjective x
      obtain ⟨z, hz⟩ := (hex (y - (1 : B) ⊗ₜ[A] n)).mp (by
        rw [map_sub, ← hx, LinearMap.lTensor_tmul, sub_self])
      obtain ⟨m, rfl⟩ := hb₁.2 z
      refine ⟨n + m, ?_⟩
      dsimp only at hz ⊢
      rw [tmul_add]
      simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply] at hz
      rw [hz, add_sub_cancel]

/-- If `B` is flat over `A` and `A ⧸ I → B ⧸ I B` is bijective, then `N → B ⊗[A] N` is bijective
for every `I`-power torsion `A`-module `N`. -/
theorem bijective_one_tmul_of_forall_exists_pow_smul_eq_zero [Module.Flat A B]
    (hI : Function.Bijective (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
      Ideal.le_comap_map)) {N : Type u} [AddCommGroup N] [Module A N]
    (hN : ∀ n : N, ∃ k : ℕ, ∀ r ∈ I ^ k, r • n = 0) :
    Function.Bijective (fun n : N ↦ (1 : B) ⊗ₜ[A] n) := by
  let T (k : ℕ) : Submodule A N := Submodule.torsionBySet A N (I ^ k : Ideal A)
  have hT (k : ℕ) : Function.Bijective (fun n : T k ↦ (1 : B) ⊗ₜ[A] n) :=
    bijective_one_tmul_of_pow_smul_eq_zero hI k (T k) fun r hr n ↦
      Subtype.ext ((Submodule.mem_torsionBySet_iff _ _).mp n.2 ⟨r, hr⟩)
  have hmem (n : N) : ∃ k, n ∈ T k := by
    obtain ⟨k, hk⟩ := hN n
    exact ⟨k, (Submodule.mem_torsionBySet_iff _ _).mpr fun a ↦ hk a a.2⟩
  have hinj (k : ℕ) : Function.Injective ((T k).subtype.lTensor B) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (T k).injective_subtype
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · rw [← sub_eq_zero]
    obtain ⟨k, hk⟩ := hmem (x - y)
    have h0 : (1 : B) ⊗ₜ[A] (⟨x - y, hk⟩ : T k) = (1 : B) ⊗ₜ[A] (0 : T k) := by
      apply hinj k
      dsimp only at hxy
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, Submodule.subtype_apply, tmul_sub, hxy,
        sub_self, map_zero, tmul_zero]
    exact congrArg Subtype.val ((hT k).1 h0)
  · induction y using TensorProduct.inductionOn with
    | tmul b n =>
      obtain ⟨k, hk⟩ := hmem n
      obtain ⟨m, hm⟩ := (hT k).2 (b ⊗ₜ[A] ⟨n, hk⟩)
      refine ⟨m, ?_⟩
      have := congrArg ((T k).subtype.lTensor B) hm
      dsimp only at this ⊢
      rwa [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul] at this
    | add y z hy hz =>
      obtain ⟨n, rfl⟩ := hy
      obtain ⟨m, rfl⟩ := hz
      exact ⟨n + m, tmul_add _ _ _⟩

end TauCeti
