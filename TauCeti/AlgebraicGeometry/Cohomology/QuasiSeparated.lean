/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.FiniteCover
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# Uniform vanishing of quasi-coherent cohomology on quasi-compact quasi-separated schemes

On a quasi-compact and quasi-separated scheme `X` there is a bound `N`, depending only on `X`,
such that `Hⁿ(X, F) = 0` for every quasi-coherent `F` and every `n ≥ N`. Consequently, for a
quasi-compact and quasi-separated morphism `f : X ⟶ S` to an affine scheme, the cohomology of
quasi-coherent modules on `X` vanishes in a range depending only on `f`.

The proof follows the Stacks Project. A quasi-compact open `W` of an affine open `U` is a finite
union of `r` basic opens of `U`; their finite intersections are again basic opens, hence affine,
so Serre's vanishing theorem and the bound for finite Leray covers give `Hⁿ(W, F) = 0` for
`n ≥ r`. A quasi-compact open of a quasi-separated scheme is a finite union of affine opens. If
`Hⁿ(W, F)` vanishes for `n ≥ N₁` and `Hⁿ(W ⊓ U, F)` for `n ≥ N₂`, where `U` is an affine open,
then the Mayer–Vietoris sequence makes `Hⁿ(W ⊔ U, F)` vanish for `n ≥ max N₁ (N₂ + 1)`.
Quasi-separation makes `W ⊓ U` a quasi-compact open of the affine open `U`, which is the first
case.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.Modules.exists_subsingleton_cohomologyOn_of_le_isAffineOpen`:
  a uniform vanishing bound for quasi-coherent cohomology on a quasi-compact open contained in an
  affine open;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.exists_subsingleton_cohomologyOn_of_isCompact`: a
  uniform vanishing bound on a quasi-compact open of a quasi-separated scheme;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.exists_subsingleton_cohomology`: a uniform vanishing
  bound on a quasi-compact quasi-separated scheme;
* `TauCeti.QCoh.higherDirectImage_vanishing`: the bound for the source of a quasi-compact
  quasi-separated morphism to an affine scheme.

## References

* The Stacks Project, Lemmas 30.4.2–30.4.6 (tag 01XH).
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

namespace TauCeti

namespace AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **Uniform vanishing on a quasi-compact open of an affine open.** Let `W` be a quasi-compact
open contained in an affine open `U` of a scheme `X`. Then there is a bound `N`, independent of
the coefficients, such that `Hⁿ(W, M) = 0` for every quasi-coherent `M` and every `n ≥ N`: one can
take for `N` the number of basic opens of `U` needed to cover `W`. Stacks, Lemma 30.4.2 (01XD). -/
theorem exists_subsingleton_cohomologyOn_of_le_isAffineOpen {U W : X.Opens} (hU : IsAffineOpen U)
    (hW : IsCompact (W : Set X)) (hWU : W ≤ U) :
    ∃ N : ℕ, ∀ (M : X.Modules) [M.IsQuasicoherent] (n : ℕ), N ≤ n →
      Subsingleton (cohomologyOn M n W) := by
  classical
  -- Cover `W` by finitely many basic opens of `U` contained in `W`.
  let ι := {f : Γ(X, U) // X.basicOpen f ≤ W}
  obtain ⟨s, hs⟩ := hW.elim_finite_subcover (fun i : ι ↦ (X.basicOpen i.1 : Set X))
    (fun i ↦ (X.basicOpen i.1).isOpen) fun x hx ↦ by
      obtain ⟨f, hf, hxf⟩ := hU.exists_basicOpen_le ⟨x, hx⟩ (hWU hx)
      exact Set.mem_iUnion.mpr ⟨⟨f, hf⟩, hxf⟩
  have hsW : s.sup (fun i : ι ↦ X.basicOpen i.1) = W := by
    refine le_antisymm (Finset.sup_le fun i _ ↦ i.2) fun x hx ↦ ?_
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact (Finset.le_sup (f := fun i : ι ↦ X.basicOpen i.1) hi) hxi
  rcases s.eq_empty_or_nonempty with rfl | hne
  · -- The empty open is affine.
    refine ⟨1, fun M _ n hn ↦ ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [← hsW, Finset.sup_empty]
    exact subsingleton_cohomologyOn_succ_of_isAffineOpen M (isAffineOpen_bot X) m
  refine ⟨s.card, fun M _ n hn ↦ ?_⟩
  rw [← hsW]
  refine subsingleton_cohomologyOn_sup_of_card_le M hne _ (fun t _ ht i ↦ ?_) n hn
  -- A nonempty finite intersection of basic opens of `U` is a basic open of `U`, hence affine.
  obtain ⟨f, hf⟩ : t.inf (fun i : ι ↦ X.basicOpen i.1) ∈
      Set.range fun f : Γ(X, U) ↦ X.basicOpen f := by
    rw [← Finset.inf'_eq_inf ht]
    exact Finset.inf'_mem _ Scheme.inf_mem_range_basicOpen _ ht _ fun i _ ↦ ⟨i.1, rfl⟩
  rw [← hf]
  exact subsingleton_cohomologyOn_succ_of_isAffineOpen M (hU.basicOpen f) i

/-- **Uniform vanishing on a quasi-compact open of a quasi-separated scheme.** If `W` is a
quasi-compact open of a quasi-separated scheme `X`, there is a bound `N`, independent of the
coefficients, such that `Hⁿ(W, M) = 0` for every quasi-coherent `M` and every `n ≥ N`. Stacks,
Section 30.4 (01XH). -/
theorem exists_subsingleton_cohomologyOn_of_isCompact [QuasiSeparatedSpace X] {W : X.Opens}
    (hW : IsCompact (W : Set X)) :
    ∃ N : ℕ, ∀ (M : X.Modules) [M.IsQuasicoherent] (n : ℕ), N ≤ n →
      Subsingleton (cohomologyOn M n W) := by
  refine compact_open_induction_on W hW
    (exists_subsingleton_cohomologyOn_of_le_isAffineOpen (isAffineOpen_bot X) isCompact_empty
      le_rfl) fun W hW U ih ↦ ?_
  obtain ⟨N₁, hN₁⟩ := ih
  -- By quasi-separation, `W ⊓ U` is a quasi-compact open of the affine open `U`.
  obtain ⟨N₂, hN₂⟩ := exists_subsingleton_cohomologyOn_of_le_isAffineOpen U.2
    (hW.inter_of_isOpen U.2.isCompact W.isOpen U.1.isOpen) (inf_le_right : W ⊓ U.1 ≤ U.1)
  refine ⟨max N₁ (N₂ + 1), fun M _ n hn ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact subsingleton_cohomologyOn_sup_succ M m (hN₂ M m (by omega)) (hN₁ M (m + 1) (by omega))
    (subsingleton_cohomologyOn_succ_of_isAffineOpen M U.2 m)

/-- **Uniform vanishing on a quasi-compact quasi-separated scheme.** On a quasi-compact and
quasi-separated scheme `X` there is a bound `N` such that `Hⁿ(X, M) = 0` for every quasi-coherent
`M` and every `n ≥ N`. Stacks, Section 30.4 (01XH). -/
theorem exists_subsingleton_cohomology (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ N : ℕ, ∀ (M : X.Modules) [M.IsQuasicoherent] (n : ℕ), N ≤ n →
      Subsingleton (Cohomology M n) := by
  obtain ⟨N, hN⟩ := exists_subsingleton_cohomologyOn_of_isCompact (X := X) (W := ⊤)
    isCompact_univ
  exact ⟨N, fun M _ n hn ↦ have := hN M n hn
    (cohomologyOnTopIso M n).symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton⟩

end AlgebraicGeometry.Scheme.Modules

namespace QCoh

open _root_.TauCeti.AlgebraicGeometry.Scheme.Modules

/-- **Uniform vanishing over an affine base.** For a quasi-compact and quasi-separated morphism
`f : X ⟶ S` to an affine scheme, the cohomology of quasi-coherent modules on `X` vanishes in a
range depending only on `f`. Over a base that is not affine no uniform bound need exist. Stacks,
Lemmas 30.4.1–30.4.6 (01XH). -/
theorem higherDirectImage_vanishing {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] [IsAffine S] :
    ∃ N : ℕ, ∀ (F : X.Modules) [F.IsQuasicoherent] (p : ℕ), N ≤ p →
      Subsingleton (Cohomology F p) := by
  have := QuasiCompact.compactSpace_of_compactSpace f
  have := quasiSeparatedSpace_of_quasiSeparated f
  exact exists_subsingleton_cohomology X

end QCoh

end TauCeti
