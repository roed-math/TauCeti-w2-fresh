/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.GradedAlgebra.Veronese
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Veronese

/-!
# The charts of the relative `Proj` of a Veronese subalgebra

Let `A = ⨁ₙ Aₙ` be a graded algebra on a scheme `X`, `d ≠ 0`, and `A^{(d)} = ⨁ₖ A_{dk}` its
Veronese subalgebra (`CategoryTheory.CommMon.veronese`). Over an open `U` of `X`, the graded
sections of `A^{(d)}` are the Veronese subalgebra of the graded sections of `A`
(`CategoryTheory.CommMon.veroneseSectionsEquiv`), so the charts of the relative `Proj`s agree:
`Proj (⨁ₖ Γ(A_{dk}, U)) ≅ Proj (⨁ₙ Γ(Aₙ, U))` (`AlgebraicGeometry.Proj.veroneseIso`). These are
the charts of `Proj_X(A^{(d)}) ≅ Proj_X(A)` (Stacks, Lemma 27.11.8 (0B5J)) over the affine opens
of `X`.

## Main definitions

* `CategoryTheory.CommMon.veroneseSectionsGradedHom`,
  `CategoryTheory.CommMon.veroneseSectionsGradedHomInv`: `veroneseSectionsEquiv` and its inverse,
  as graded ring maps.
* `CategoryTheory.CommMon.projVeroneseSectionsIso`: the isomorphism
  `Proj (⨁ₖ Γ(A_{dk}, U)) ≅ Proj (⨁ₙ Γ(Aₙ, U))`.

## Main results

* `CategoryTheory.CommMon.restrict_comp_veroneseSectionsGradedHomInv`: the identification of
  graded sections commutes with restriction.

## References

* [The Stacks Project, Lemma 27.11.8 (0B5J)](https://stacks.math.columbia.edu/tag/0B5J)
-/

@[expose] public section

open CategoryTheory

namespace TauCeti

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}} (A : CommMon (GradedObject ℕ X.Modules)) (d : ℕ) [NeZero d]

/-- The graded ring isomorphism `veroneseSectionsEquiv`, from the graded sections of the
Veronese subalgebra `A^{(d)}` to the Veronese subalgebra of the graded sections of `A`. -/
def _root_.CategoryTheory.CommMon.veroneseSectionsGradedHom (U : X.Opens) :
    (A.veronese d).gradedSectionsGrading U →+*ᵍ
      GradedAlgebra.veroneseGrading (A.gradedSectionsGrading U) d where
  toRingHom := (A.veroneseSectionsEquiv d U (NeZero.ne d)).toRingEquiv.toRingHom
  map_mem hx := A.veroneseSectionsEquiv_mem_veroneseGrading d U (NeZero.ne d) hx

/-- The inverse of `CategoryTheory.CommMon.veroneseSectionsGradedHom`. -/
def _root_.CategoryTheory.CommMon.veroneseSectionsGradedHomInv (U : X.Opens) :
    GradedAlgebra.veroneseGrading (A.gradedSectionsGrading U) d →+*ᵍ
      (A.veronese d).gradedSectionsGrading U where
  toRingHom := (A.veroneseSectionsEquiv d U (NeZero.ne d)).symm.toRingEquiv.toRingHom
  map_mem {k x} hx := by
    obtain ⟨y, hy, rfl⟩ :=
      (A.map_veroneseSectionsEquiv_gradedSectionsGrading d U (NeZero.ne d) k).ge hx
    change (A.veroneseSectionsEquiv d U (NeZero.ne d)).symm
      (A.veroneseSectionsEquiv d U (NeZero.ne d) y) ∈ _
    rwa [AlgEquiv.symm_apply_apply]

/-- `CategoryTheory.CommMon.veroneseSectionsGradedHomInv` is the inverse of
`CategoryTheory.CommMon.veroneseSectionsEquiv`. -/
theorem _root_.CategoryTheory.CommMon.veroneseSectionsGradedHomInv_apply (U : X.Opens)
    (x : GradedAlgebra.veronese (A.gradedSectionsGrading U) d) :
    A.veroneseSectionsGradedHomInv d U x = (A.veroneseSectionsEquiv d U (NeZero.ne d)).symm x :=
  rfl

/-- Over an open `U`, the `Proj` of the graded sections of `A^{(d)}` is the `Proj` of the graded
sections of `A`. -/
def _root_.CategoryTheory.CommMon.projVeroneseSectionsIso (U : X.Opens) :
    Proj ((A.veronese d).gradedSectionsGrading U) ≅ Proj (A.gradedSectionsGrading U) :=
  Proj.mapIso (A.veroneseSectionsGradedHomInv d U) (A.veroneseSectionsGradedHom d U)
    (fun x ↦ (A.veroneseSectionsEquiv d U (NeZero.ne d)).symm_apply_apply x)
    (fun x ↦ (A.veroneseSectionsEquiv d U (NeZero.ne d)).apply_symm_apply x) ≪≫
  Proj.veroneseIso _ d

variable {U V : X.Opens} (i : V ⟶ U)

/-- The inverse of `veroneseSectionsEquiv` commutes with restriction of sections: restricting the
graded sections of `A^{(d)}` is restricting the Veronese subalgebra of the graded sections of
`A`. -/
theorem _root_.CategoryTheory.CommMon.restrict_comp_veroneseSectionsGradedHomInv :
    ((A.veronese d).restrictGradedSectionsGradedHom i).comp (A.veroneseSectionsGradedHomInv d U) =
      (A.veroneseSectionsGradedHomInv d V).comp
        (GradedAlgebra.veroneseMap d (A.restrictGradedSectionsGradedHom i)) := by
  refine GradedRingHom.ext fun x ↦ ?_
  apply (A.veroneseSectionsEquiv d V (NeZero.ne d)).injective
  apply Subtype.ext
  simp only [GradedRingHom.comp_apply, CommMon.veroneseSectionsGradedHomInv_apply,
    AlgEquiv.apply_symm_apply, GradedAlgebra.coe_veroneseMap_apply,
    CommMon.coe_veroneseSectionsEquiv, CommMon.restrictGradedSectionsGradedHom_apply]
  rw [CommMon.veroneseSectionsAlgHom_restrictGradedSections,
    ← A.coe_veroneseSectionsEquiv d U (NeZero.ne d), AlgEquiv.apply_symm_apply]

end

end TauCeti
