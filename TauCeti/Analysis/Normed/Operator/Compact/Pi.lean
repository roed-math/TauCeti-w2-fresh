/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compact operators into finite products

A map into a finite product is a compact operator when each of its components is, and a finite
product of compact operators is compact. The compact sets are products of compact sets
(Tychonoff), and finitely many neighbourhoods of zero intersect to a neighbourhood of zero.

Čech cochains over a finite cover are finite products of spaces of sections, and restriction of
cochains to a relatively compact refinement is the product of the restrictions on the members of
the cover; these lemmas show that it is compact when each of these restrictions is.

## Main results

* `IsCompactOperator.pi`: a map into a finite product whose components are compact operators is a
  compact operator.
* `IsCompactOperator.piMap`: a finite product of compact operators is a compact operator.
-/

public section

open Filter Set
open scoped Topology

namespace IsCompactOperator

variable {ι : Type*} [Finite ι] {N : ι → Type*} [∀ i, TopologicalSpace (N i)]

/-- A map into a finite product is a compact operator if each of its components is. -/
theorem pi {M : Type*} [Zero M] [TopologicalSpace M] {f : ∀ i, M → N i}
    (hf : ∀ i, IsCompactOperator (f i)) : IsCompactOperator fun x i ↦ f i x := by
  choose K hK hKf using hf
  refine ⟨univ.pi K, isCompact_univ_pi hK, ?_⟩
  have : (fun x i ↦ f i x) ⁻¹' univ.pi K = ⋂ i, f i ⁻¹' K i := by
    ext
    simp
  rw [this]
  exact iInter_mem.2 hKf

/-- A finite product of compact operators is a compact operator. -/
theorem piMap {M : ι → Type*} [∀ i, Zero (M i)] [∀ i, TopologicalSpace (M i)]
    {f : ∀ i, M i → N i} (hf : ∀ i, IsCompactOperator (f i)) :
    IsCompactOperator (Pi.map f) := by
  choose K hK hKf using hf
  refine ⟨univ.pi K, isCompact_univ_pi hK, ?_⟩
  have : Pi.map f ⁻¹' univ.pi K = univ.pi fun i ↦ f i ⁻¹' K i := by
    ext
    simp
  rw [this]
  exact set_pi_mem_nhds finite_univ fun i _ ↦ hKf i

end IsCompactOperator
