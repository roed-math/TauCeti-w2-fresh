/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.GradedAlgebra.Veronese
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Veronese
public import TauCeti.AlgebraicGeometry.RelativeProj.Basic

/-!
# The relative `Proj` of a Veronese subalgebra

Let `A = ⨁ₙ Aₙ` be a graded algebra on a scheme `X`, `d ≠ 0`, and `A^{(d)} = ⨁ₖ A_{dk}` its
Veronese subalgebra (`CategoryTheory.CommMon.veronese`). Over an open `U` of `X`, the graded
sections of `A^{(d)}` are the Veronese subalgebra of the graded sections of `A`
(`CategoryTheory.CommMon.veroneseSectionsEquiv`), so the charts of the relative `Proj`s agree:
`Proj (⨁ₖ Γ(A_{dk}, U)) ≅ Proj (⨁ₙ Γ(Aₙ, U))` (`AlgebraicGeometry.Proj.veroneseIso`). These
isomorphisms are compatible with restriction and with the coefficient projections, so they glue
to `Proj_X(A^{(d)}) ≅ Proj_X(A)` over `X` (Stacks, Lemma 27.11.8 (0B5J)).

## Main definitions

* `CategoryTheory.CommMon.veroneseSectionsGradedHom`,
  `CategoryTheory.CommMon.veroneseSectionsGradedHomInv`: `veroneseSectionsEquiv` and its inverse,
  as graded ring maps.
* `CategoryTheory.CommMon.projVeroneseSectionsIso`: the isomorphism
  `Proj (⨁ₖ Γ(A_{dk}, U)) ≅ Proj (⨁ₙ Γ(Aₙ, U))`.
* `CategoryTheory.CommMon.relativeProjFunctorVeroneseIso`: these isomorphisms over the affine
  opens of `X`, as an isomorphism of gluing diagrams.
* `CategoryTheory.CommMon.relativeProjVeroneseIso`: the isomorphism
  `Proj_X(A^{(d)}) ≅ Proj_X(A)`.

## Main results

* `CategoryTheory.CommMon.restrict_comp_veroneseSectionsGradedHomInv`: the identification of
  graded sections commutes with restriction.
* `CategoryTheory.CommMon.map_restrict_projVeroneseSectionsIso_hom`: so does
  `projVeroneseSectionsIso`.
* `CategoryTheory.CommMon.projVeroneseSectionsIso_hom_toSpecCoeff`: `projVeroneseSectionsIso`
  lies over `Spec Γ(X, U)`.
* `CategoryTheory.CommMon.relativeProjVeroneseIso_hom_relativeProjToBase`:
  `relativeProjVeroneseIso` lies over `X`.

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

/-- `CategoryTheory.CommMon.projVeroneseSectionsIso` is `Proj.map` of the inverse of
`veroneseSectionsEquiv`, followed by `Proj.veroneseIso`. -/
theorem _root_.CategoryTheory.CommMon.projVeroneseSectionsIso_hom (U : X.Opens) :
    (A.projVeroneseSectionsIso d U).hom =
      Proj.map (A.veroneseSectionsGradedHomInv d U)
        (HomogeneousIdeal.irrelevant_le_map_of_surjective _
          (A.veroneseSectionsEquiv d U (NeZero.ne d)).symm.surjective) ≫
        (Proj.veroneseIso _ d).hom :=
  (Iso.trans_hom _ _).trans (congrArg (· ≫ _) (Proj.mapIso_hom _ _ _ _))

/-- The isomorphism `projVeroneseSectionsIso` lies over `Spec Γ(X, U)`. -/
theorem _root_.CategoryTheory.CommMon.projVeroneseSectionsIso_hom_toSpecCoeff (U : X.Opens) :
    (A.projVeroneseSectionsIso d U).hom ≫ Proj.toSpecCoeff (A.gradedSectionsGrading U) =
      Proj.toSpecCoeff ((A.veronese d).gradedSectionsGrading U) :=
  (congrArg (· ≫ _) (A.projVeroneseSectionsIso_hom d U)).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (Proj.veroneseIso_hom_toSpecCoeff _ d)).trans <|
      Proj.map_toSpecCoeff _ (A.veroneseSectionsGradedHomInv d U) _ fun r ↦
        Subtype.ext (by exact (A.veroneseSectionsEquiv d U (NeZero.ne d)).symm.commutes r)

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

/-- The isomorphisms `projVeroneseSectionsIso` commute with the morphisms of projective spectra
induced by restriction of sections. -/
theorem _root_.CategoryTheory.CommMon.map_restrict_projVeroneseSectionsIso_hom
    (h : HomogeneousIdeal.irrelevant ((A.veronese d).gradedSectionsGrading V) ≤
      (HomogeneousIdeal.irrelevant ((A.veronese d).gradedSectionsGrading U)).map
        ((A.veronese d).restrictGradedSectionsGradedHom i))
    (h' : HomogeneousIdeal.irrelevant (A.gradedSectionsGrading V) ≤
      (HomogeneousIdeal.irrelevant (A.gradedSectionsGrading U)).map
        (A.restrictGradedSectionsGradedHom i)) :
    Proj.map ((A.veronese d).restrictGradedSectionsGradedHom i) h ≫
        (A.projVeroneseSectionsIso d U).hom =
      (A.projVeroneseSectionsIso d V).hom ≫ Proj.map (A.restrictGradedSectionsGradedHom i) h' := by
  have hU := HomogeneousIdeal.irrelevant_le_map_of_surjective
    (A.veroneseSectionsGradedHomInv d U) (A.veroneseSectionsEquiv d U (NeZero.ne d)).symm.surjective
  have hV := HomogeneousIdeal.irrelevant_le_map_of_surjective
    (A.veroneseSectionsGradedHomInv d V) (A.veroneseSectionsEquiv d V (NeZero.ne d)).symm.surjective
  have hV' := HomogeneousIdeal.irrelevant_le_map_of_surjective
    (A.veroneseSectionsGradedHom d V) (A.veroneseSectionsEquiv d V (NeZero.ne d)).surjective
  -- the restriction of the Veronese subalgebras is `veroneseSectionsEquiv` conjugate to the
  -- restriction of the graded sections of `A^{(d)}`
  have hcomp : (A.veroneseSectionsGradedHom d V).comp ((A.veroneseSectionsGradedHomInv d V).comp
      (GradedAlgebra.veroneseMap d (A.restrictGradedSectionsGradedHom i))) =
        GradedAlgebra.veroneseMap d (A.restrictGradedSectionsGradedHom i) :=
    GradedRingHom.ext fun x ↦ (A.veroneseSectionsEquiv d V (NeZero.ne d)).apply_symm_apply _
  have hres := HomogeneousIdeal.irrelevant_le_map_comp hU h
  rw [A.restrict_comp_veroneseSectionsGradedHomInv d i] at hres
  have hfd :
      HomogeneousIdeal.irrelevant (GradedAlgebra.veroneseGrading (A.gradedSectionsGrading V) d) ≤
        (HomogeneousIdeal.irrelevant
          (GradedAlgebra.veroneseGrading (A.gradedSectionsGrading U) d)).map
            (GradedAlgebra.veroneseMap d (A.restrictGradedSectionsGradedHom i)) :=
    (HomogeneousIdeal.irrelevant_le_map_comp hres hV').trans_eq
      (congrArg (fun φ ↦ (HomogeneousIdeal.irrelevant
        (GradedAlgebra.veroneseGrading (A.gradedSectionsGrading U) d)).map φ) hcomp)
  -- the rewrites time out on these instances of `Proj.map`, so the chain is spelled out
  refine (congrArg (_ ≫ ·) (A.projVeroneseSectionsIso_hom d U)).trans <|
    (Category.assoc _ _ _).symm.trans <| ((congrArg (· ≫ (Proj.veroneseIso _ d).hom) <|
      (Proj.map_comp _ _ hU h).symm.trans <|
        (Proj.map_congr (A.restrict_comp_veroneseSectionsGradedHomInv d i) _
          (HomogeneousIdeal.irrelevant_le_map_comp hfd hV)).trans
        (Proj.map_comp _ _ hfd hV)).trans <| (Category.assoc _ _ _).trans <|
      (congrArg (Proj.map _ hV ≫ ·) (Proj.map_veroneseMap_veroneseIso_hom _ h' hfd)).trans <|
        (Category.assoc _ _ _).symm.trans ?_)
  exact congrArg (· ≫ Proj.map _ h') (A.projVeroneseSectionsIso_hom d V).symm

section Gluing

open Scheme.AffineZariskiSite

variable [∀ n, (A.X n).IsQuasicoherent]

/-- The isomorphisms `projVeroneseSectionsIso` over the affine opens of `X`, as an isomorphism of
the gluing diagrams of the relative `Proj`s of `A^{(d)}` and `A`. -/
def _root_.CategoryTheory.CommMon.relativeProjFunctorVeroneseIso :
    (A.veronese d).relativeProjFunctor ≅ A.relativeProjFunctor :=
  NatIso.ofComponents (fun U ↦ A.projVeroneseSectionsIso d U.toOpens) fun i ↦
    A.map_restrict_projVeroneseSectionsIso_hom d ((toOpensFunctor X).map i)
      ((A.veronese d).irrelevant_le_map_restrictGradedSectionsGradedHom_toOpensFunctor i)
      (A.irrelevant_le_map_restrictGradedSectionsGradedHom_toOpensFunctor i)

/-- **The relative `Proj` of a Veronese subalgebra.** For `d ≠ 0`, the relative `Proj` of the
Veronese subalgebra `A^{(d)} = ⨁ₖ A_{dk}` is the relative `Proj` of `A`. -/
@[stacks 0B5J]
def _root_.CategoryTheory.CommMon.relativeProjVeroneseIso :
    (A.veronese d).relativeProj ≅ A.relativeProj :=
  Limits.HasColimit.isoOfNatIso (A.relativeProjFunctorVeroneseIso d)

/-- On the chart over an affine open `U`, the isomorphism `relativeProjVeroneseIso` is
`projVeroneseSectionsIso`. -/
theorem _root_.CategoryTheory.CommMon.relativeProjCover_f_relativeProjVeroneseIso_hom
    (U : X.AffineZariskiSite) :
    (A.veronese d).relativeProjCover.f U ≫ (A.relativeProjVeroneseIso d).hom =
      (A.projVeroneseSectionsIso d U.toOpens).hom ≫ A.relativeProjCover.f U :=
  Limits.HasColimit.ι_isoOfNatIso_hom _ U

/-- **The isomorphism `relativeProjVeroneseIso` lies over `X`.** -/
@[reassoc (attr := simp)]
theorem _root_.CategoryTheory.CommMon.relativeProjVeroneseIso_hom_relativeProjToBase :
    (A.relativeProjVeroneseIso d).hom ≫ A.relativeProjToBase =
      (A.veronese d).relativeProjToBase :=
  (A.veronese d).relativeProjCover.hom_ext _ _ fun (U : X.AffineZariskiSite) ↦
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) (A.relativeProjCover_f_relativeProjVeroneseIso_hom d U)).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (A.relativeProjCover_f_relativeProjToBase U)).trans <|
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ U.2.fromSpec) (A.projVeroneseSectionsIso_hom_toSpecCoeff d U.toOpens))).trans
      ((A.veronese d).relativeProjCover_f_relativeProjToBase U).symm

end Gluing

end

end TauCeti
