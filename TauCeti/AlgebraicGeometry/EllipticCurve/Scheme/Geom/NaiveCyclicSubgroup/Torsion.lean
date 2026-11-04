/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.SubgroupDescent
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Basic
import TauCeti.CategoryTheory.Monoidal.Mon

/-!
# Naive cyclic subgroups as closed subgroup schemes of `E[N]`

A naive cyclic subgroup of order `N` of an elliptic curve `E` over `S`
(`EllipticCurveGeom.IsNaiveCyclicSubgroup`) is given by an ideal sheaf on `E`. It lies in the
`N`-torsion `E[N]` (`EllipticCurveGeom.IsNaiveCyclicSubgroup.ker_torsionι_le`), so it is a closed
subgroup scheme of `E[N]`, finite locally free of rank `N` over `S`. This is the form in which a
naive `[Γ₀(N)]`-structure is a point of the parameter scheme of rank-`N` subgroup schemes of
`E[N]` (the roadmap's Layer 0G, applied to `G = E[N]`).

Conversely, a closed subgroup scheme `C` of `E[N]` has an ideal sheaf on `E`, the kernel of
`C ⟶ E[N] ⟶ E` (`EllipticCurveGeom.torsionSubgroupIdeal`). The two passages are inverse to each
other: naive cyclic subgroups of order `N` of `E` are exactly the closed subgroup schemes of
`E[N]` whose ideal sheaf on `E` cuts out a naive cyclic subgroup of order `N`. On points, this is
the cyclic locus of the subgroup parameter scheme of `E[N]`.

## Main definitions

* `EllipticCurveGeom.IsNaiveCyclicSubgroup.toGrp`: the group scheme over `S` underlying a naive
  cyclic subgroup.
* `EllipticCurveGeom.IsNaiveCyclicSubgroup.toTorsion`: its inclusion into `E[N]`, a closed
  immersion of group schemes.
* `EllipticCurveGeom.IsNaiveCyclicSubgroup.closedSubgroup`: the closed subgroup scheme of `E[N]`.
* `EllipticCurveGeom.torsionSubgroupIdeal`: the ideal sheaf on `E` of a closed subgroup scheme of
  `E[N]`.

## Main results

* `EllipticCurveGeom.IsNaiveCyclicSubgroup.isFinite_toGrp`, `flat_toGrp`,
  `locallyOfFinitePresentation_toGrp`, `finrank_toGrp`: the closed subgroup scheme is finite
  locally free of rank `N` over `S`.
* `EllipticCurveGeom.IsNaiveCyclicSubgroup.torsionSubgroupIdeal_closedSubgroup` and
  `EllipticCurveGeom.IsNaiveCyclicSubgroup.closedSubgroup_torsionSubgroupIdeal`: the two passages
  are inverse to each other.
* `EllipticCurveGeom.IsNaiveCyclicSubgroup.eq_of_closedSubgroup_eq`: a naive cyclic subgroup is
  determined by its closed subgroup scheme of `E[N]`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1 and §3.7.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} {E : EllipticCurveGeom S} {N : ℕ} [NeZero N]
  {I : E.carrier.IdealSheafData}

namespace IsNaiveCyclicSubgroup

/-- The group scheme over `S` underlying a naive cyclic subgroup of `E`: the closed subscheme cut
out by its ideal sheaf, with the group law restricted from `E`. It is `@[expose]` so that its
underlying scheme is visibly the closed subscheme. -/
@[expose] noncomputable def toGrp (h : E.IsNaiveCyclicSubgroup I N) : Grp (Over S) :=
  @Grp.mk _ _ _ (Over.mk (I.subschemeι ≫ E.structureMap)) h.exists_grpObj_isMonHom.choose

omit [NeZero N] in
/-- The underlying object of `IsNaiveCyclicSubgroup.toGrp` is the closed subscheme over `S`. -/
@[simp]
theorem toGrp_X (h : E.IsNaiveCyclicSubgroup I N) :
    h.toGrp.X = Over.mk (I.subschemeι ≫ E.structureMap) := (rfl)

/-- The inclusion of a naive cyclic subgroup into `E[N]`, as a morphism of schemes over `S`. -/
noncomputable def toTorsionHom (h : E.IsNaiveCyclicSubgroup I N) :
    h.toGrp.X ⟶ (E.torsion N).X :=
  Over.homMk (U := Over.mk (I.subschemeι ≫ E.structureMap)) (V := (E.torsion N).X)
    (IsClosedImmersion.lift (E.torsionι N).left I.subschemeι
      (I.ker_subschemeι.symm ▸ h.ker_torsionι_le)) (by
    rw [← Over.w (E.torsionι N), ← Category.assoc, IsClosedImmersion.lift_fac]
    rfl)

/-- The inclusion of a naive cyclic subgroup into `E[N]`, followed by the inclusion of `E[N]` into
`E`, is the inclusion of the closed subscheme. -/
@[reassoc (attr := simp)]
theorem toTorsionHom_left_comp_torsionι_left (h : E.IsNaiveCyclicSubgroup I N) :
    h.toTorsionHom.left ≫ (E.torsionι N).left = I.subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

/-- The inclusion of a naive cyclic subgroup into `E[N]` is a homomorphism: its composite with the
monomorphism `E[N] ⟶ E` is the inclusion of the subgroup into `E`, which is a homomorphism. -/
instance isMonHom_toTorsionHom (h : E.IsNaiveCyclicSubgroup I N) :
    IsMonHom h.toTorsionHom := by
  have hι : h.toTorsionHom ≫ E.torsionι N =
      (Over.homMk I.subschemeι : Over.mk (I.subschemeι ≫ E.structureMap) ⟶
        Over.mk E.structureMap) := by
    ext1
    exact h.toTorsionHom_left_comp_torsionι_left
  have : IsMonHom (h.toTorsionHom ≫ E.torsionι N) := hι ▸ h.exists_grpObj_isMonHom.choose_spec
  exact isMonHom_of_comp_mono _ (E.torsionι N)

/-- The inclusion of a naive cyclic subgroup into `E[N]`, as a morphism of group schemes. -/
noncomputable def toTorsion (h : E.IsNaiveCyclicSubgroup I N) : h.toGrp ⟶ E.torsion N :=
  Grp.homMk h.toTorsionHom

/-- The underlying morphism over `S` of `IsNaiveCyclicSubgroup.toTorsion`. -/
@[simp]
theorem toTorsion_hom_hom (h : E.IsNaiveCyclicSubgroup I N) :
    h.toTorsion.hom.hom = h.toTorsionHom :=
  Grp.homMk_hom_hom _

/-- The inclusion of a naive cyclic subgroup into `E[N]` is a closed immersion. -/
instance isClosedImmersion_toTorsion (h : E.IsNaiveCyclicSubgroup I N) :
    IsClosedImmersion h.toTorsion.hom.hom.left := by
  have : IsClosedImmersion (h.toTorsionHom.left ≫ (E.torsionι N).left) := by
    rw [toTorsionHom_left_comp_torsionι_left]
    exact inferInstanceAs (IsClosedImmersion I.subschemeι)
  rw [toTorsion_hom_hom]
  exact IsClosedImmersion.of_comp_isClosedImmersion h.toTorsionHom.left (E.torsionι N).left

/-- **A naive cyclic subgroup of order `N` is a closed subgroup scheme of `E[N]`.** -/
noncomputable def closedSubgroup (h : E.IsNaiveCyclicSubgroup I N) :
    ClosedSubgroupScheme (E.torsion N) :=
  .mk h.toTorsion

/-- The subobject underlying `IsNaiveCyclicSubgroup.closedSubgroup` is represented by the
inclusion into `E[N]`. -/
theorem coe_closedSubgroup (h : E.IsNaiveCyclicSubgroup I N) :
    h.closedSubgroup.1 = Subobject.mk h.toTorsion :=
  ClosedSubgroupScheme.coe_mk _

omit [NeZero N] in
/-- The closed subgroup scheme of a naive cyclic subgroup is finite over `S`. -/
theorem isFinite_toGrp (h : E.IsNaiveCyclicSubgroup I N) : IsFinite h.toGrp.X.hom :=
  h.isFinite

omit [NeZero N] in
/-- The closed subgroup scheme of a naive cyclic subgroup is flat over `S`. -/
theorem flat_toGrp (h : E.IsNaiveCyclicSubgroup I N) : Flat h.toGrp.X.hom :=
  h.flat

omit [NeZero N] in
/-- The closed subgroup scheme of a naive cyclic subgroup is locally of finite presentation over
`S`. -/
theorem locallyOfFinitePresentation_toGrp (h : E.IsNaiveCyclicSubgroup I N) :
    LocallyOfFinitePresentation h.toGrp.X.hom :=
  h.locallyOfFinitePresentation

omit [NeZero N] in
/-- The closed subgroup scheme of a naive cyclic subgroup of order `N` has rank `N` over every
point of `S`. -/
theorem finrank_toGrp (h : E.IsNaiveCyclicSubgroup I N) (s : S) :
    h.toGrp.X.hom.finrank s = N :=
  h.finrank_eq s

end IsNaiveCyclicSubgroup

omit [NeZero N] in
variable (E) in
/-- The ideal sheaf on `E` of a closed subgroup scheme `C` of `E[N]`: the kernel of the composite
`C ⟶ E[N] ⟶ E`. -/
noncomputable def torsionSubgroupIdeal (C : ClosedSubgroupScheme (E.torsion N)) :
    E.carrier.IdealSheafData :=
  (C.1.arrow.hom.hom.left ≫ (E.torsionι N).left).ker

namespace IsNaiveCyclicSubgroup

/-- **A naive cyclic subgroup is recovered from its closed subgroup scheme of `E[N]`**: the ideal
sheaf on `E` of `IsNaiveCyclicSubgroup.closedSubgroup` is the ideal sheaf of the subgroup. -/
@[simp]
theorem torsionSubgroupIdeal_closedSubgroup (h : E.IsNaiveCyclicSubgroup I N) :
    E.torsionSubgroupIdeal h.closedSubgroup = I := by
  have : IsIso (Subobject.underlyingIso h.toTorsion).hom.hom.hom.left :=
    ((Grp.forget _ ⋙ Over.forget _).mapIso (Subobject.underlyingIso h.toTorsion)).isIso_hom
  rw [torsionSubgroupIdeal, coe_closedSubgroup, ← Subobject.underlyingIso_hom_comp_eq_mk]
  simp only [Grp.comp_hom_hom, Over.comp_left, toTorsion_hom_hom, Category.assoc,
    toTorsionHom_left_comp_torsionι_left]
  exact (Scheme.Hom.ker_comp_of_isIso _ _).trans I.ker_subschemeι

/-- **A naive cyclic subgroup is determined by its closed subgroup scheme of `E[N]`.** -/
theorem eq_of_closedSubgroup_eq {J : E.carrier.IdealSheafData} (h : E.IsNaiveCyclicSubgroup I N)
    (h' : E.IsNaiveCyclicSubgroup J N) (hIJ : h.closedSubgroup = h'.closedSubgroup) :
    I = J := by
  rw [← h.torsionSubgroupIdeal_closedSubgroup, hIJ, h'.torsionSubgroupIdeal_closedSubgroup]

/-- **Every closed subgroup scheme of `E[N]` cutting out a naive cyclic subgroup is the closed
subgroup scheme of that naive cyclic subgroup.** The composite `C ⟶ E[N] ⟶ E` is a closed
immersion, so `C` is isomorphic to the closed subscheme cut out by its ideal sheaf, compatibly
with the inclusions into `E[N]`. -/
theorem closedSubgroup_torsionSubgroupIdeal {C : ClosedSubgroupScheme (E.torsion N)}
    (h : E.IsNaiveCyclicSubgroup (E.torsionSubgroupIdeal C) N) : h.closedSubgroup = C := by
  obtain ⟨P, hP⟩ := C
  have : IsClosedImmersion P.arrow.hom.hom.left := (closedSubgroupMorphismProperty_iff _ _).mp hP
  have : Mono P.arrow.hom.hom := Over.mono_of_mono_left _
  -- `C` is the closed subscheme `V(ker c)` of `c : C ⟶ E[N] ⟶ E`, through `t = c.toImage`.
  let t := (P.arrow.hom.hom.left ≫ (E.torsionι N).left).toImage
  have : IsClosedImmersion (P.arrow.hom.hom.left ≫ (E.torsionι N).left) := inferInstance
  have ht : IsIso t := inferInstanceAs (IsIso (Scheme.Hom.toImage _))
  have hc : t ≫ h.toTorsionHom.left ≫ (E.torsionι N).left =
      P.arrow.hom.hom.left ≫ (E.torsionι N).left :=
    (congrArg _ h.toTorsionHom_left_comp_torsionι_left).trans (Scheme.Hom.toImage_imageι _)
  have hfac : inv t ≫ P.arrow.hom.hom.left = h.toTorsionHom.left :=
    (cancel_mono (E.torsionι N).left).mp
      ((Category.assoc _ _ _).trans ((IsIso.inv_comp_eq _).mpr hc.symm))
  have hw : (P : Grp (Over S)).X.hom = t ≫ h.toGrp.X.hom :=
    calc (P : Grp (Over S)).X.hom = P.arrow.hom.hom.left ≫ (E.torsion N).X.hom :=
          (Over.w _).symm
      _ = P.arrow.hom.hom.left ≫ (E.torsionι N).left ≫ E.structureMap :=
          congrArg (_ ≫ ·) (Over.w (E.torsionι N)).symm
      _ = t ≫ h.toTorsionHom.left ≫ (E.torsionι N).left ≫ E.structureMap :=
          ((reassoc_of% hc) E.structureMap).symm
      _ = t ≫ h.toGrp.X.hom :=
          congrArg (t ≫ ·) ((congrArg (h.toTorsionHom.left ≫ ·) (Over.w (E.torsionι N))).trans
            (Over.w h.toTorsionHom))
  let e : h.toGrp.X ≅ (P : Grp (Over S)).X :=
    Over.isoMk (f := h.toGrp.X) (g := (P : Grp (Over S)).X) (@asIso _ _ _ _ t ht).symm
      ((@IsIso.inv_comp_eq _ _ _ _ _ t ht _ _).mpr hw)
  have he : e.hom ≫ P.arrow.hom.hom = h.toTorsionHom := by
    ext1
    exact hfac
  have : IsMonHom (e.hom ≫ P.arrow.hom.hom) := he ▸ inferInstance
  have : IsMonHom e.hom := isMonHom_of_comp_mono e.hom P.arrow.hom.hom
  exact Subtype.ext ((coe_closedSubgroup h).trans
    ((Subobject.mk_eq_mk_of_comm _ _ (Grp.mkIso e (IsMonHom.one_hom e.hom) (IsMonHom.mul_hom e.hom))
      (Grp.hom_ext _ _ (by simpa using he))).trans (Subobject.mk_arrow P)))

end IsNaiveCyclicSubgroup

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
