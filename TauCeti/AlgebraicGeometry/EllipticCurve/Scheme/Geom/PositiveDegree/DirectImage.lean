/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.GlobalSections
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.PositiveDegree
public import TauCeti.AlgebraicGeometry.LineBundle.BaseChange

/-!
# `R¹π_*M` vanishes for a line bundle of positive fibre degree on an elliptic curve

Let `E` be an elliptic curve over a scheme `S`, with structure morphism `π : E ⟶ S`, and let `M`
be an invertible sheaf on `E` whose restriction to every geometric fibre `Spec Ω ×_S E` has
positive degree. This file shows that `R¹π_*M = 0`
(`EllipticCurveGeom.isZero_higherDirectImage_one_of_forall_eulerDegree_pos`).
This is the first clause of the positive-degree theorem used by elliptic autoduality.

Over a pointed Weierstrass chart `c` of `E`, with coefficient ring `R`, the restriction of `E` is
the projective model of an elliptic Weierstrass curve over `R`. Its fibre over a prime `p` of `R`
is the projective model over the residue field `κ(p)`, and after the further base change to an
algebraic closure `Ω` of `κ(p)` it is the geometric fibre of `E` over the composite point
`Spec Ω ⟶ Spec κ(p) ⟶ Spec R ⟶ S`. Since the degree of a line bundle does not change under
extension of the ground field (`TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_pullback`),
the degree of `M` on the fibre of the chart over `p` is a geometric fibre degree of `M`
(`EllipticCurveGeom.exists_eulerDegree_pullback_projModelBaseChange_eq`).
So the restriction of `M` to the chart has positive degree on every fibre, and its first cohomology
vanishes (`WeierstrassCurve.subsingleton_cohomology_one_of_forall_eulerDegree_pos`). The images of
the charts of an atlas, restricted to the affine opens of their bases, form a basis of `S`, and a
higher direct image vanishes when the cohomology of the preimages of the members of a basis does.

## Main results

* `EllipticCurveGeom.exists_eulerDegree_pullback_projModelBaseChange_eq`:
  the fibre degrees of `M` on a chart are geometric fibre degrees of `M`.
* `EllipticCurveGeom.eulerDegree_pullback_projModelBaseChange_pos`: such an `M` has positive
  degree on the fibres of the Weierstrass model of every chart.
* `EllipticCurveGeom.subsingleton_cohomologyOn_one_of_forall_eulerDegree_pos`:
  over the image `U` of the base of a chart, `H¹(π⁻¹(U), M) = 0`.
* `EllipticCurveGeom.isZero_higherDirectImage_one_of_forall_eulerDegree_pos`:
  `R¹π_*M = 0`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- **A field-valued point factors through a chart.** Every morphism `Spec K ⟶ S` from the
spectrum of a field factors through the base `Spec R` of some chart of a pointed Weierstrass atlas,
as `Spec K ⟶ Spec R ≅ base ⟶ S` with the first map induced by a ring homomorphism `R →+* K`. -/
theorem PointedWeierstrassAtlas.exists_eq_specMap_comp_baseMap {S X : Scheme.{u}} {π : X ⟶ S}
    {zero : S ⟶ X} (A : PointedWeierstrassAtlas π zero) {K : Type u} [Field K]
    (ξ : Spec (.of K) ⟶ S) :
    ∃ (i : A.index) (f : (A.chart i).ring →+* K),
      ξ = Spec.map (CommRingCat.ofHom f) ≫ (A.chart i).baseIso.inv ≫ (A.chart i).baseMap := by
  obtain ⟨i, x, hx⟩ := A.covers (ξ.base (IsLocalRing.closedPoint K))
  have h : Set.range ξ.base ⊆ Set.range (A.chart i).baseMap.base := by
    rintro _ ⟨y, rfl⟩
    exact ⟨x, by rw [hx, Subsingleton.elim y (IsLocalRing.closedPoint K)]⟩
  refine ⟨i, (Spec.preimage (IsOpenImmersion.lift _ ξ h ≫ (A.chart i).baseIso.hom)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, Category.assoc, Iso.hom_inv_id_assoc,
    IsOpenImmersion.lift_fac]

namespace EllipticCurveGeom

open Scheme.Modules

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- **The fibres of `E` over the points of a chart are projective Weierstrass models.** Let `c` be
a pointed Weierstrass chart of `E`, with coefficient ring `R`, and `f : R →+* K` a ring homomorphism
to a field. The degree of a line-bundle class `a` on the fibre of `E` over the point
`Spec K ⟶ Spec R ≅ base ⟶ S` is the degree over `K` of its pullback to the projective model of the
equation of `c` over `K`. -/
theorem eulerDegree_pullback_snd_specMap_comp
    (c : PointedWeierstrassChart E.structureMap E.zero) {K : Type u} [Field K]
    (f : c.ring →+* K) (a : LineBundleClass E.carrier) :
    letI : (pullback (Spec.map (CommRingCat.ofHom f) ≫ c.baseIso.inv ≫ c.baseMap)
        E.structureMap).Over (Spec (.of K)) := ⟨pullback.fst _ _⟩
    LineBundleClass.eulerDegree K (LineBundleClass.pullback
        (pullback.snd (Spec.map (CommRingCat.ofHom f) ≫ c.baseIso.inv ≫ c.baseMap)
          E.structureMap) a) =
      LineBundleClass.eulerDegree K (LineBundleClass.pullback (c.equation.projModelBaseChange f)
        (LineBundleClass.pullback (c.modelIso.inv ≫ c.toTotal) a)) := by
  let H := (c.equation.isPullback_projModelBaseChange f).paste_horiz
    c.isPullback_modelIso_inv_toTotal
  let : (pullback (Spec.map (CommRingCat.ofHom f) ≫ c.baseIso.inv ≫ c.baseMap)
      E.structureMap).Over (Spec (.of K)) := ⟨pullback.fst _ _⟩
  have he : H.flip.isoPullback.inv ≫ ((c.equation.map f).projModel ↘ Spec (.of K)) =
      pullback.fst _ E.structureMap := by
    rw [WeierstrassCurve.over_projModel, Iso.inv_comp_eq, IsPullback.isoPullback_hom_fst]
  have hsnd : H.flip.isoPullback.inv ≫ c.equation.projModelBaseChange f ≫
      c.modelIso.inv ≫ c.toTotal = pullback.snd _ E.structureMap := by
    rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_snd]
  rw [← LineBundleClass.eulerDegree_pullback_of_isIso _ he, LineBundleClass.pullback_comp,
    LineBundleClass.pullback_comp, Category.assoc, hsnd]

/-- **The fibre degrees of a line bundle on a chart are geometric fibre degrees.** Let `c` be a
pointed Weierstrass chart of `E`, with coefficient ring `R`, and `p` a prime of `R`. The degree
over `κ(p)` of the restriction of `M` to the fibre over `p` of the projective model of the chart is
the degree of `M` on the geometric fibre of `E` over some point `Spec Ω ⟶ S`, where `Ω` is an
algebraic closure of `κ(p)`. -/
theorem exists_eulerDegree_pullback_projModelBaseChange_eq
    (c : PointedWeierstrassChart E.structureMap E.zero) (M : InvertibleSheaf E.carrier)
    (p : PrimeSpectrum c.ring) :
    ∃ ξ : Spec (.of (AlgebraicClosure p.asIdeal.ResidueField)) ⟶ S,
      ((InvertibleSheaf.pullback
        (c.equation.projModelBaseChange (algebraMap c.ring p.asIdeal.ResidueField))).obj
          ((InvertibleSheaf.pullback (c.modelIso.inv ≫ c.toTotal)).obj M)).eulerDegree
            p.asIdeal.ResidueField =
        letI : (pullback ξ E.structureMap).Over
            (Spec (.of (AlgebraicClosure p.asIdeal.ResidueField))) := ⟨pullback.fst _ _⟩
        LineBundleClass.eulerDegree (AlgebraicClosure p.asIdeal.ResidueField)
          (LineBundleClass.pullback (pullback.snd ξ E.structureMap) (.mk M)) := by
  -- the projective model of the chart is the base change of `E` to `Spec R`
  have hC : IsPullback (c.modelIso.inv ≫ c.toTotal) (c.equation.projModel ↘ Spec (.of c.ring))
      E.structureMap (c.baseIso.inv ≫ c.baseMap) := by
    rw [WeierstrassCurve.over_projModel]
    exact c.isPullback_modelIso_inv_toTotal
  -- so its base change to `Ω` is the geometric fibre of `E` over the composite point
  let H := (WeierstrassCurve.isPullback_projModelBaseChange_over
    (c.equation.map (algebraMap c.ring p.asIdeal.ResidueField))
    (R' := AlgebraicClosure p.asIdeal.ResidueField)).paste_horiz
      ((c.equation.isPullback_projModelBaseChange_over
        (R' := p.asIdeal.ResidueField)).paste_horiz hC)
  let ξ : Spec (.of (AlgebraicClosure p.asIdeal.ResidueField)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap p.asIdeal.ResidueField
      (AlgebraicClosure p.asIdeal.ResidueField))) ≫ Spec.map (CommRingCat.ofHom
        (algebraMap c.ring p.asIdeal.ResidueField)) ≫ c.baseIso.inv ≫ c.baseMap
  refine ⟨ξ, ?_⟩
  let : (pullback ξ E.structureMap).Over
      (Spec (.of (AlgebraicClosure p.asIdeal.ResidueField))) := ⟨pullback.fst _ _⟩
  have he : H.flip.isoPullback.inv ≫ (_ ↘ Spec (.of (AlgebraicClosure p.asIdeal.ResidueField))) =
      pullback.fst ξ E.structureMap := by
    rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_fst]
  have hsnd : H.flip.isoPullback.inv ≫ (c.equation.map _).projModelBaseChange
      (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)) ≫
        c.equation.projModelBaseChange (algebraMap c.ring p.asIdeal.ResidueField) ≫
          c.modelIso.inv ≫ c.toTotal = pullback.snd ξ E.structureMap := by
    rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_snd]
  rw [← LineBundleClass.eulerDegree_mk, ← LineBundleClass.pullback_mk,
    ← LineBundleClass.pullback_mk, LineBundleClass.pullback_comp,
    ← LineBundleClass.eulerDegree_pullback
      (WeierstrassCurve.isPullback_projModelBaseChange_over
        (c.equation.map (algebraMap c.ring p.asIdeal.ResidueField))
        (R' := AlgebraicClosure p.asIdeal.ResidueField)),
    LineBundleClass.pullback_comp, ← LineBundleClass.eulerDegree_pullback_of_isIso _ he,
    LineBundleClass.pullback_comp, hsnd]

variable {E} {M : InvertibleSheaf E.carrier}
  (hM : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ξ : Spec (.of Ω) ⟶ S),
    letI : (pullback ξ E.structureMap).Over (Spec (.of Ω)) := ⟨pullback.fst _ _⟩
    0 < LineBundleClass.eulerDegree Ω
      (LineBundleClass.pullback (pullback.snd ξ E.structureMap) (.mk M)))
include hM

/-- **A line bundle of positive geometric fibre degree has positive degree on the fibres of every
chart.** For a pointed Weierstrass chart `c` of `E` with coefficient ring `R`, the restriction of
`M` to the projective model of the equation of `c` has positive degree on its fibre over every
prime of `R`. This is the hypothesis of the positive-degree theorem on a Weierstrass model. -/
theorem eulerDegree_pullback_projModelBaseChange_pos
    (c : PointedWeierstrassChart E.structureMap E.zero) (p : PrimeSpectrum c.ring) :
    0 < ((InvertibleSheaf.pullback
      (c.equation.projModelBaseChange (algebraMap c.ring p.asIdeal.ResidueField))).obj
        ((InvertibleSheaf.pullback (c.modelIso.inv ≫ c.toTotal)).obj M)).eulerDegree
          p.asIdeal.ResidueField := by
  obtain ⟨ξ, hξ⟩ := E.exists_eulerDegree_pullback_projModelBaseChange_eq c M p
  rw [hξ]
  exact hM _ ξ

/-- **`H¹` of a line bundle of positive fibre degree vanishes over a chart.** Over the image `U`
of the base of a pointed Weierstrass chart of `E`, `H¹(π⁻¹(U), M) = 0` for an invertible sheaf `M`
of positive degree on every geometric fibre of `E`: `π⁻¹(U)` is the projective model of an
elliptic Weierstrass curve, on which `M` has positive degree on every fibre. -/
theorem subsingleton_cohomologyOn_one_of_forall_eulerDegree_pos
    (c : PointedWeierstrassChart E.structureMap E.zero) :
    Subsingleton (cohomologyOn M.obj 1 (E.structureMap ⁻¹ᵁ c.baseMap.opensRange)) := by
  have : Subsingleton ((cohomologyFunctor _ 1).obj
      ((InvertibleSheaf.pullback (c.modelIso.inv ≫ c.toTotal)).obj M).obj) := by
    exact WeierstrassCurve.subsingleton_cohomology_one_of_forall_eulerDegree_pos
      (eulerDegree_pullback_projModelBaseChange_pos hM c)
  let e : M.obj.restrict (c.modelIso.inv ≫ c.toTotal) ≅
      ((InvertibleSheaf.pullback (c.modelIso.inv ≫ c.toTotal)).obj M).obj :=
    (restrictFunctorIsoPullback _).app _ ≪≫ eqToIso (InvertibleSheaf.pullback_obj_obj _ _).symm
  rw [← c.opensRange_toTotal, ← Scheme.Hom.opensRange_comp_of_isIso c.modelIso.inv]
  exact ((cohomologyOnOpensRangeIso _ _ 1 ≪≫
    (cohomologyFunctor _ 1).mapIso e).addCommGroupIsoToAddEquiv).subsingleton

/-- **`R¹π_*M = 0` for a line bundle of positive fibre degree.** For an elliptic curve
`π : E ⟶ S` and an invertible sheaf `M` on `E` of positive degree on every geometric fibre
`Spec Ω ×_S E`, the first higher direct image of `M` vanishes. -/
theorem isZero_higherDirectImage_one_of_forall_eulerDegree_pos :
    IsZero ((E.structureMap.higherDirectImage 1).obj M.obj) := by
  obtain ⟨A⟩ := E.localModel
  refine E.structureMap.isZero_higherDirectImage_succ_of_isBasis _ 0
    A.isBasis_range_opensRange_restrict ?_
  rintro _ ⟨p, rfl⟩
  exact subsingleton_cohomologyOn_one_of_forall_eulerDegree_pos hM ((A.chart p.1).restrict p.2)

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
