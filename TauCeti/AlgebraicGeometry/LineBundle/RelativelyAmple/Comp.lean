/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.RelativelyAmple

/-!
# Twisting a relatively ample line bundle by an ample one

Let `f : X ⟶ Y` be a morphism of schemes, `a` a line-bundle class on `X` that is relatively ample
for `f`, and `b` an ample line-bundle class on `Y`. Then `a · f* bⁿ` is ample on `X` for all large
`n`. Over a quasi-compact base `S`, this composes relative ampleness along `X ⟶ Y` and
`Y ⟶ S` (Stacks, Tag 0C4K).

## Main results

* `LineBundleClass.IsRelativelyAmple.exists_isAmple_mul_pullback_pow`:
  if `a` is relatively ample for `f : X ⟶ Y` and `b` is ample on `Y`, then `a · f* bⁿ` is ample
  for all large `n`.
* `LineBundleClass.IsRelativelyAmple.exists_isRelativelyAmple_comp_mul_pullback_pow`:
  over a quasi-compact base `S`, if `a` is relatively ample for `f : X ⟶ Y` and `b` for
  `g : Y ⟶ S`, then `a · f* bⁿ` is relatively ample for `f ≫ g` for all large `n`.

## References

* [The Stacks Project, Tag 0C4K](https://stacks.math.columbia.edu/tag/0C4K)
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace TauCeti.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

namespace LineBundleClass

/-- **A relatively ample class twisted by a large power of an ample one is ample**
(Stacks, Tag 0C4K, over an affine base). Let `a` be relatively ample for `f : X ⟶ Y` and `b`
ample on `Y`. Then `a · f* bⁿ` is ample on `X` for all large `n`.

Let `x ∈ X`. Some global section `s` of a line bundle `M` of class `bᵈ` has `Y_s ∋ f x` affine.
Then `a` is ample on `U = f⁻¹ Y_s`, so some section `t` over `U` of a line bundle of class `aᵉ` has
`X_t ∋ x` affine. The pullback `f* s` vanishes nowhere exactly on `U`, so `(f* s)^{⊗c} ⊗ t`
extends to a global section `ξ` for some `c > 0` (`InvertibleSheaf.exists_map_eq_tmul_sectionPow`)
and `X_{f* s ⊗ ξ} = X_t`. The global sections `(f* s)^{⊗k} ⊗ (f* s ⊗ ξ)^{⊗d}` all vanish nowhere
exactly on `X_t`; for `n ≥ d c` and `k = e n - d c`, their class is `(a · f* bⁿ)^{e d}`. Finitely
many such `X_t` cover `X`. -/
@[stacks 0C4K]
theorem IsRelativelyAmple.exists_isAmple_mul_pullback_pow {a : LineBundleClass X}
    {b : LineBundleClass Y} {f : X ⟶ Y} (ha : a.IsRelativelyAmple f) (hb : b.IsAmple) :
    ∃ N : ℕ, ∀ n, N ≤ n → (a * LineBundleClass.pullback f (b ^ n)).IsAmple := by
  have := hb.compactSpace
  have := hb.isSeparated
  have := ha.quasiCompact
  have := ha.isSeparated
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : X.IsSeparated := (Scheme.isSeparated_iff X).mpr (by
    rw [← Limits.terminal.comp_from f]
    infer_instance)
  -- Every point lies in an affine open `W` which, for all large `n`, is the nonvanishing locus of
  -- a global section of a line bundle of class a positive power of `a · f* bⁿ`.
  have key (x : X) : ∃ (N : ℕ) (W : X.Opens), x ∈ W ∧ IsAffineOpen W ∧ ∀ n, N ≤ n →
      ∃ m : ℕ, 0 < m ∧ ∃ (L : InvertibleSheaf X)
        (_ : LineBundleClass.mk L = (a * LineBundleClass.pullback f (b ^ n)) ^ m)
        (σ : Γ(L.obj, ⊤)), L.obj.nonvanishingLocus σ = W := by
    obtain ⟨d, hd, M, hM, s, hxs, hs⟩ := hb.exists_isAffineOpen_nonvanishingLocus (f x)
    let U := f ⁻¹ᵁ M.obj.nonvanishingLocus s
    obtain ⟨e, he, K, hK, t', hxt', ht'⟩ :=
      (ha.isAmple_pullback _ hs).exists_isAffineOpen_nonvanishingLocus (⟨x, hxs⟩ : U)
    obtain ⟨La, hLa⟩ := LineBundleClass.mk_surjective (a ^ e)
    obtain ⟨t, ht⟩ := InvertibleSheaf.exists_nonvanishingLocus_eq_image La (K := K) (by
      rw [hK, hLa]
      simp only [← pullbackHom_apply, map_pow]) t'
    have htU : La.obj.nonvanishingLocus t ≤ U := Scheme.Modules.nonvanishingLocus_le t
    -- The pullback `f* s` vanishes nowhere exactly on `U`.
    let P := (InvertibleSheaf.pullback f).obj M
    let s₁ : Γ(P.obj, ⊤) := f.pullbackSections M.obj ⊤ s
    have hs₁ : P.obj.nonvanishingLocus s₁ = U :=
      Scheme.Modules.nonvanishingLocus_pullbackSections f s
    have hts : La.obj.nonvanishingLocus t ≤ P.obj.nonvanishingLocus s₁ := hs₁ ▸ htU
    -- Extend `(f* s)^{⊗β} ⊗ (f* s)^{⊗α} ⊗ t` from `U` to `X`.
    obtain ⟨α, β, ξ, hξ⟩ := InvertibleSheaf.exists_map_eq_tmul_sectionPow (L := P) (F := La)
      (U := ⊤) (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ) s₁
      (La.obj.presheaf.map (homOfLE hs₁.le).op t)
    let σ := InvertibleSheaf.tmul s₁ ξ
    have hD : P.obj.nonvanishingLocus s₁ ≤ P.obj.nonvanishingLocus
        (P.obj.presheaf.map (homOfLE (Scheme.Modules.nonvanishingLocus_le s₁)).op s₁) := by
      rw [Scheme.Modules.nonvanishingLocus_map, inf_idem]
    have hσ : (P.tensorProduct ((P.tensorPow β).tensorProduct
        ((P.tensorPow α).tensorProduct La))).obj.nonvanishingLocus σ =
          La.obj.nonvanishingLocus t := by
      refine (InvertibleSheaf.nonvanishingLocus_tmul s₁ ξ).trans ?_
      have h := congrArg (Scheme.Modules.nonvanishingLocus _) hξ
      rw [Scheme.Modules.nonvanishingLocus_map, InvertibleSheaf.nonvanishingLocus_tmul,
        InvertibleSheaf.nonvanishingLocus_tmul,
        InvertibleSheaf.nonvanishingLocus_sectionPow_of_le hD,
        InvertibleSheaf.nonvanishingLocus_sectionPow_of_le hD,
        Scheme.Modules.nonvanishingLocus_map] at h
      rw [h]
      simp only [inf_eq_right.mpr hts]
    refine ⟨d * (β + 1 + α), La.obj.nonvanishingLocus t, ht ▸ ⟨⟨x, hxs⟩, hxt', rfl⟩,
      ht ▸ ht'.image_of_isOpenImmersion U.ι, fun n hn ↦ ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, e * n = d * (β + 1 + α) + k :=
      ⟨e * n - d * (β + 1 + α), by have := Nat.le_mul_of_pos_left n he; omega⟩
    obtain ⟨d', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hd.ne'
    refine ⟨e * (d' + 1), by positivity, _, ?_,
      InvertibleSheaf.tmul (InvertibleSheaf.sectionPow s₁ k)
        (InvertibleSheaf.sectionPow σ (d' + 1)), ?_⟩
    · have hP : LineBundleClass.mk P = LineBundleClass.pullback f b ^ (d' + 1) := by
        rw [← LineBundleClass.pullback_mk, hM, ← pullbackHom_apply, ← pullbackHom_apply, map_pow]
      simp only [LineBundleClass.mk_tensorProduct, LineBundleClass.mk_tensorPow, hP, hLa]
      rw [← pullbackHom_apply f (b ^ n), map_pow, pullbackHom_apply]
      generalize LineBundleClass.pullback f b = c
      generalize d' + 1 = D at hk ⊢
      simp only [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
      rw [mul_comm]
      congr 2
      rw [mul_comm n e, hk]
      ring
    · rw [InvertibleSheaf.nonvanishingLocus_tmul, InvertibleSheaf.nonvanishingLocus_sectionPow_succ,
        hσ]
      exact inf_eq_right.mpr
        (hts.trans (InvertibleSheaf.nonvanishingLocus_le_nonvanishingLocus_sectionPow s₁ k))
  choose N W hxW hW hN using key
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (W x : Set X))
    (fun x ↦ (W x).isOpen) fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxW x⟩
  refine ⟨T.sup N, fun n hn ↦ ⟨inferInstance, fun x ↦ ?_⟩⟩
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ x))
  obtain ⟨m, hm, L, hL, σ, hσ⟩ := hN z n ((Finset.le_sup hz).trans hn)
  exact ⟨m, hm, L, hL, σ, hσ ▸ hxz, hσ ▸ hW z⟩

/-- **Relative ampleness composes** (Stacks, Tag 0C4K). Let `f : X ⟶ Y` and `g : Y ⟶ S` be
morphisms with `S` quasi-compact, `a` relatively ample for `f` and `b` relatively ample for `g`.
Then `a · f* bⁿ` is relatively ample for `f ≫ g` for all large `n`. Over an affine open `V` of
`S`, the class `b` is ample on `g⁻¹ V` and `a` is relatively ample for `f⁻¹ (g⁻¹ V) ⟶ g⁻¹ V`, so
`a · f* bⁿ` is ample on `f⁻¹ (g⁻¹ V)` for all large `n`
(`LineBundleClass.IsRelativelyAmple.exists_isAmple_mul_pullback_pow`). Finitely many affine opens
cover `S`, and relative ampleness is local on the base. -/
@[stacks 0C4K]
theorem IsRelativelyAmple.exists_isRelativelyAmple_comp_mul_pullback_pow {S : Scheme.{u}}
    [CompactSpace S] {a : LineBundleClass X} {b : LineBundleClass Y} {f : X ⟶ Y} {g : Y ⟶ S}
    (ha : a.IsRelativelyAmple f) (hb : b.IsRelativelyAmple g) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      (a * LineBundleClass.pullback f (b ^ n)).IsRelativelyAmple (f ≫ g) := by
  have key (V : S.affineOpens) : ∃ N : ℕ, ∀ n, N ≤ n →
      (LineBundleClass.pullback ((f ≫ g) ⁻¹ᵁ V).ι
        (a * LineBundleClass.pullback f (b ^ n))).IsRelativelyAmple ((f ≫ g) ∣_ V) := by
    have : IsAffine V := V.2
    obtain ⟨N, hN⟩ := (ha.restrict (g ⁻¹ᵁ V)).exists_isAmple_mul_pullback_pow
      (hb.isAmple_pullback V V.2)
    refine ⟨N, fun n hn ↦ (isRelativelyAmple_iff_isAmple _ _).mpr ?_⟩
    -- `(f ≫ g) ⁻¹ᵁ V` is `f ⁻¹ᵁ g ⁻¹ᵁ V` by definition (`Scheme.Hom.comp_preimage`).
    change (LineBundleClass.pullback (f ⁻¹ᵁ g ⁻¹ᵁ V).ι
      (a * LineBundleClass.pullback f (b ^ n))).IsAmple
    convert hN n hn using 1
    rw [pullback_mul, ← pullbackHom_apply (g ⁻¹ᵁ V).ι, ← map_pow, pullbackHom_apply,
      pullback_comp, pullback_comp, morphismRestrict_ι]
  choose N hN using key
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun V : S.affineOpens ↦ (V : Set S))
    (fun V ↦ V.1.isOpen) fun x _ ↦ by
      obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩
  refine ⟨T.sup N, fun n hn ↦ isRelativelyAmple_of_iSup_eq_top (fun V : T ↦ (V.1 : S.Opens))
    (eq_top_iff.mpr fun x _ ↦ ?_) fun V ↦ hN V n ((Finset.le_sup V.2).trans hn)⟩
  obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩

end LineBundleClass

end TauCeti.AlgebraicGeometry
