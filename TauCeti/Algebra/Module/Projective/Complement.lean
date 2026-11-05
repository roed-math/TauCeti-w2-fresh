/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Projection

/-!
# Submodules with projective quotient are complemented

Let `p` be a submodule of an `R`-module `M`. If the quotient `M ⧸ p` is projective, the quotient
map `M ⟶ M ⧸ p` has a linear section `s`, and `x ↦ x - s (x mod p)` is a projection of `M` onto
`p`. Its kernel is a complement of `p`.

## Main results

* `Submodule.exists_isCompl_of_projective_quotient`: a submodule with projective quotient has a
  complement.
-/

public section

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- **A submodule with projective quotient is complemented.** If `M ⧸ p` is a projective
`R`-module, then `p` has a complement in `M`. -/
theorem exists_isCompl_of_projective_quotient (p : Submodule R M) [Module.Projective R (M ⧸ p)] :
    ∃ q : Submodule R M, IsCompl p q := by
  -- a section `s` of the quotient map
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p.mkQ LinearMap.id p.mkQ_surjective
  have hs' (y : M ⧸ p) : p.mkQ (s y) = y := LinearMap.congr_fun hs y
  have hmem (x : M) : (LinearMap.id - s ∘ₗ p.mkQ : M →ₗ[R] M) x ∈ p := by
    rw [← Quotient.mk_eq_zero, ← mkQ_apply, LinearMap.sub_apply, map_sub, LinearMap.comp_apply,
      hs', LinearMap.id_apply, sub_self]
  -- `x ↦ x - s (x mod p)` is a projection onto `p`
  refine ⟨LinearMap.ker ((LinearMap.id - s ∘ₗ p.mkQ : M →ₗ[R] M).codRestrict p hmem),
    LinearMap.isCompl_of_proj fun x ↦ ?_⟩
  ext
  simp [(p.mkQ_apply x).trans ((Quotient.mk_eq_zero p).mpr x.2)]

end Submodule
