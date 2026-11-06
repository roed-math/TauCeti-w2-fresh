/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Free complements of rank one over a local ring

Let `R` be a local ring and `N` a submodule of an `R`-module `M` such that `M ⧸ N` is finite and
flat of rank one at the closed point. Then `M ⧸ N` is free of rank one, and lifting a basis
vector gives `s : M` with `M = N ⊕ R s` and `R ⟶ R s` injective.

This is how a line bundle quotient of a filtration is split by a single element after
localising, e.g. the choice of the Weierstrass coordinates `x` and `y` in the pole filtration of
an elliptic curve.

## Main results

* `TauCeti.IsLocalRing.exists_isCompl_span_singleton_of_rankAtStalk_eq_one`: a submodule whose
  quotient is finite flat of rank one has a complement spanned by one linearly independent
  element.
-/

public section

namespace TauCeti.IsLocalRing

variable {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]

/-- Over a local ring `R`, a submodule `N` of `M` whose quotient `M ⧸ N` is finite and flat of
rank one at the closed point has a complement `R ∙ s` spanned by a linearly independent element:
`M = N ⊕ R s`. -/
theorem exists_isCompl_span_singleton_of_rankAtStalk_eq_one (N : Submodule R M)
    [Module.Finite R (M ⧸ N)] [Module.Flat R (M ⧸ N)]
    (h : Module.rankAtStalk (M ⧸ N) (IsLocalRing.closedPoint R) = 1) :
    ∃ s : M, IsCompl N (R ∙ s) ∧ LinearIndependent R ![s] := by
  have := Module.free_of_flat_of_isLocalRing (R := R) (P := M ⧸ N)
  have hr : Module.finrank R (M ⧸ N) = 1 := by
    rw [← h, Module.rankAtStalk_eq_finrank_of_free]
    rfl
  let b := Module.finBasisOfFinrankEq R (M ⧸ N) hr
  obtain ⟨s, hs⟩ := N.mkQ_surjective (b 0)
  have hmk (x : M) : N.mkQ x = b.repr (N.mkQ x) 0 • b 0 := by
    conv_lhs => rw [← b.sum_repr (N.mkQ x)]
    simp
  have hind (r : R) (hr : r • s ∈ N) : r = 0 := by
    have : b.repr (r • b 0) 0 = r := by simp
    rw [← this, ← hs, ← map_smul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 hr]
    simp
  refine ⟨s, ⟨?_, ?_⟩, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxN hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [hind r hxN, zero_smul]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [← sub_add_cancel x (b.repr (N.mkQ x) 0 • s)]
    refine Submodule.add_mem_sup ?_
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self s))
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      ← Submodule.mkQ_apply, ← Submodule.mkQ_apply, hs, ← hmk, sub_self]
  · have hb : N.mkQ ∘ ![s] = b := by
      ext i
      fin_cases i
      simp [hs]
    exact .of_comp N.mkQ (hb ▸ b.linearIndependent)

end TauCeti.IsLocalRing
