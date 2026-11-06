/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Ordinary
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Prestable

/-!
# Prestable models from their special fibre

Let `R` be a discrete valuation ring with fraction field `K` and residue field `k`, and let `M` be
a proper model over `R` of a prestable curve `C ⟶ Spec K`, for instance a smooth proper
geometrically connected curve (`TauCeti.AlgebraicGeometry.PrestableFamily.of_smooth`). This file
shows that `M` is a prestable model as soon as its special fibre `X_k` is geometrically connected
and, after some field extension `k ⟶ L` such as an algebraic closure of `k`, every point of
`X_L` is a smooth point or an ordinary node, in the étale-local sense of
`TauCeti.AlgebraicGeometry.IsOrdinaryNodeOrSmoothAt`. Alternatively, the extension may be chosen
point by point among finite separable extensions of `k`.

Geometric reducedness of the special fibre is not assumed separately, and the geometric
irreducible components need not be smooth: a component may cross itself at an ordinary
node.

## Main results

* `TauCeti.Model.prestableFamily_toBase_of_specialFiber`: a proper model of a prestable curve
  whose special fibre is geometrically connected with only ordinary nodes after a field extension
  is a prestable model.
* `TauCeti.Model.prestableFamily_toBase_of_specialFiber_of_isSeparable`: the same, with a finite
  separable residue extension chosen separately at each point.

## References

* [The Stacks Project, Section 55.18, Semistable reduction](https://stacks.math.columbia.edu/tag/0CDL)
* [The Stacks Project, Section 53.19, Tag 0C46](https://stacks.math.columbia.edu/tag/0C46)
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry

namespace TauCeti

universe u

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- **The prestable criterion.** A proper model of a prestable curve over a discrete valuation
ring is a prestable model when its special fibre is geometrically connected and, after a field
extension `L` of the residue field (for instance an algebraic closure), each point of the base
changed special fibre is a smooth point or an ordinary node. -/
theorem prestableFamily_toBase_of_specialFiber (M : Model R K C toK) [M.IsProper]
    [PrestableFamily toK] [GeometricallyConnected (specialFiber R M.toBase).hom]
    (L : Type u) [Field L] [Algebra (IsLocalRing.ResidueField R) L]
    (h : ∀ x, IsOrdinaryNodeOrSmoothAt
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) L)))
        (specialFiber R M.toBase).hom) x) :
    PrestableFamily M.toBase := by
  refine M.prestableFamily_toBase_iff.mpr ⟨‹_›, ‹_›, ?_⟩
  have : AlgebraicGeometry.IsProper (specialFiber R M.toBase).hom :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsProper)
      (isPullback_specialFiber R M.toBase) inferInstance
  exact
    { atWorstNodalOfRelativeDimensionOne :=
        AtWorstNodalOfRelativeDimensionOne.of_baseChange_isOrdinaryNodeOrSmoothAt L _ h }

/-- **The prestable criterion with finite separable residue extensions.** A proper model of a
prestable curve over a discrete valuation ring is a prestable model when its special fibre is
geometrically connected and each point of the special fibre has, after some finite separable
extension `L` of the residue field depending on the point, a point above it that is a smooth point
or an ordinary node. -/
theorem prestableFamily_toBase_of_specialFiber_of_isSeparable (M : Model R K C toK)
    [M.IsProper] [PrestableFamily toK] [GeometricallyConnected (specialFiber R M.toBase).hom]
    (h : ∀ x, ∃ (L : Type u) (_ : Field L) (_ : Algebra (IsLocalRing.ResidueField R) L)
      (_ : FiniteDimensional (IsLocalRing.ResidueField R) L)
      (_ : Algebra.IsSeparable (IsLocalRing.ResidueField R) L)
      (y : ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) L)))
        (specialFiber R M.toBase).hom)),
      pullback.snd _ (specialFiber R M.toBase).hom y = x ∧
        IsOrdinaryNodeOrSmoothAt (pullback.fst _ (specialFiber R M.toBase).hom) y) :
    PrestableFamily M.toBase := by
  refine M.prestableFamily_toBase_iff.mpr ⟨‹_›, ‹_›, ?_⟩
  have : AlgebraicGeometry.IsProper (specialFiber R M.toBase).hom :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsProper)
      (isPullback_specialFiber R M.toBase) inferInstance
  exact
    { atWorstNodalOfRelativeDimensionOne :=
        AtWorstNodalOfRelativeDimensionOne.of_forall_exists_isSeparable _ h }

end Model

end TauCeti
