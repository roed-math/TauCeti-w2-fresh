/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.SupportedCohomology
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Cohomology with supports in the whole space

Let `F` be a sheaf of abelian groups on a topological space `X` and let `W` be an open subset.
With supports in the closed subset `X` itself, cohomology with supports is ordinary cohomology:
`W ∖ X` is empty, the free abelian sheaf `ℤ_∅` on the empty open is zero (every sheaf has zero
sections over `∅`), so `ℤ_W ⟶ ℤ_{W, W ∖ X}` is an isomorphism and the map
`H_Xⁿ(W, F) ⟶ Hⁿ(W, F)` of the support sequence is bijective (Stacks, Section 20.34 (0G6Y)).
Together with `CategoryTheory.Sheaf.subsingleton_supportedH_of_le_compl` (supports in `∅`
give `0`) this is the pair of boundary cases of cohomology with supports.

## Main declarations

* `TauCeti.CategoryTheory.isZero_freeYonedaSheafFunctor_obj_bot`: the free abelian sheaf on the
  empty open is zero;
* `TauCeti.CategoryTheory.supportedHTopEquiv`: `H_Xⁿ(W, F) ≃+ Hⁿ(W, F)`, given by the map
  `CategoryTheory.Sheaf.relativeH'.toH'` of the support sequence.
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TauCeti.CategoryTheory

/-- The free abelian sheaf on the empty open is zero: it corepresents the sections over `∅`,
which vanish for every sheaf. -/
theorem isZero_freeYonedaSheafFunctor_obj_bot (X : TopCat.{u}) :
    IsZero ((freeYonedaSheafFunctor (Opens.grothendieckTopology X)).obj ⊥) := by
  rw [IsZero.iff_id_eq_zero]
  apply (freeYonedaSheafSectionsEquiv _ ⊥ _).injective
  exact (AddCommGrpCat.subsingleton_of_isZero
    (TopCat.Sheaf.isTerminalOfEmpty (C := AddCommGrpCat.{u}) _).isZero).elim _ _

variable {X : TopCat.{u}} (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

noncomputable section

/-- With supports in the whole space, the projection `ℤ_W ⟶ ℤ_{W, W ∖ X}` onto the relative free
sheaf is an isomorphism, since `ℤ_{W ∖ X} = ℤ_∅` is zero. -/
instance isIso_cokernel_π_complInclusion_top (W : Opens X) :
    IsIso (cokernel.π ((freeYonedaSheafFunctor (Opens.grothendieckTopology X)).map
      ((⊤ : Closeds X).complInclusion W))) :=
  cokernel.π_of_zero <| IsZero.eq_of_src ((isZero_freeYonedaSheafFunctor_obj_bot X).of_iso
    (eqToIso (congrArg (freeYonedaSheafFunctor _).obj (Opens.ext (by simp))))) _ _

/-- Cohomology with supports in the whole space is ordinary cohomology:
`H_Xⁿ(W, F) ≃+ Hⁿ(W, F)`, via the map `CategoryTheory.Sheaf.relativeH'.toH'` of the support
sequence (see `TauCeti.CategoryTheory.supportedHTopEquiv_apply`). -/
def supportedHTopEquiv (W : Opens X) (n : ℕ) : F.supportedH ⊤ W n ≃+ F.H' n W :=
  (TauCeti.extAddEquivOfIso (asIso (cokernel.π ((freeYonedaSheafFunctor _).map
    ((⊤ : Closeds X).complInclusion W)))).symm (Iso.refl F) n).trans (F.H'AddEquivExt n W).symm

@[simp]
lemma supportedHTopEquiv_apply (W : Opens X) {n : ℕ} (x : F.supportedH ⊤ W n) :
    supportedHTopEquiv F W n x =
      Sheaf.relativeH'.toH' F ((⊤ : Closeds X).complInclusion W) n x := by
  apply (F.H'AddEquivExt n W).injective
  simp [supportedHTopEquiv, Sheaf.relativeH'.H'AddEquivExt_toH']

/-- With supports in the whole space, the map `H_Xⁿ(W, F) ⟶ Hⁿ(W, F)` of the support sequence is
bijective. -/
theorem toH'_complInclusion_top_bijective (W : Opens X) (n : ℕ) :
    Function.Bijective (Sheaf.relativeH'.toH' F ((⊤ : Closeds X).complInclusion W) n) := by
  convert (supportedHTopEquiv F W n).bijective
  ext x
  exact (supportedHTopEquiv_apply F W x).symm

end

end TauCeti.CategoryTheory
