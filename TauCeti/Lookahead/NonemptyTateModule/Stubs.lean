/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Projective

set_option warningAsError false

/-!
# Lookahead stubs for `nonempty-tate-module`

These are lookahead stubs for the supplier slug `projective-ker-of-is-zero-res`
(ClassFieldTheory, Layer 0, item 4), to be replaced by the landed declarations. The stub restates
the pinned statement of
`TauCetiRoadmap.ClassFieldTheory.TateCohomology.projective_ker_of_isZero_res`
against `main`, in the form of the supplier's open pull request #13553, which states it as
`Rep.projective_ker_of_isZero_res` in
`TauCeti.RepresentationTheory.Homological.TateCohomology.NakayamaRim`, beside its landed siblings
`Rep.projective_of_isZero_res` and `Rep.isZero_res_of_exact`.
-/

public section

universe u

open CategoryTheory Limits

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

/-- **Nakayama–Rim: cohomological triviality is projective dimension at most one** (Rim, Ann. of
Math. 69 (1959); Brown, *Cohomology of Groups*, VI §8). If `A` is cohomologically trivial, the
kernel of every surjection onto it from a projective `k[G]`-module is projective.

Lookahead stub for `projective-ker-of-is-zero-res`. -/
theorem projective_ker_of_isZero_res [Finite G] [IsDomain k] [IsPrincipalIdealRing k]
    [CharZero k]
    (hk : ∀ p : ℕ, p.Prime → IsUnit (p : k) ∨ (Ideal.span {(p : k)}).IsMaximal)
    (A : Rep k G)
    (hA : ∀ (S : Subgroup G) [Fintype S] (n : ℤ),
      IsZero (tateCohomology (res S.subtype A) n))
    {P : Type*} [AddCommGroup P] [Module (MonoidAlgebra k G) P]
    [Module.Projective (MonoidAlgebra k G) P]
    (f : P →ₗ[MonoidAlgebra k G] A.ρ.asModule) (hf : Function.Surjective f) :
    Module.Projective (MonoidAlgebra k G) (LinearMap.ker f) :=
  sorry

end Rep
