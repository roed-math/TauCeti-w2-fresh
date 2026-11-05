/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftSheaf.Affine
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.Lifts
public import TauCeti.RingTheory.Derivation.FormallyEtale

/-!
# Changing the chart of the torsor of lifts

Let `a ≫ f = i ≫ h` be a commutative square with `i : T ⟶ T'` a first-order thickening, and let
`W ⊆ T'`, `U' ⊆ U ⊆ X` and `V ⊆ S` be affine opens with `a (i⁻¹ W) ⊆ U'` and `f U ⊆ V`, `h W ⊆ V`.
The sections over `W` of the sheaf of lifts `liftSheaf f i a h` are read as lifts in the square
restricted to `U` and in the square restricted to `U'`, and each reading makes them a torsor:
under `Der_{Γ(V)}(Γ(U), I)` and under `Der_{Γ(V)}(Γ(U'), I)` respectively, where `I` is the ideal
of `i ∣_ W` in `Γ(W)`. Since `Γ(U) → Γ(U')` is formally étale, restriction of derivations along it
is a bijection `Der_{Γ(V)}(Γ(U'), I) ≃ Der_{Γ(V)}(Γ(U), I)` (`Derivation.compAlgebraMapEquiv`),
and the two torsor structures correspond under it: the torsor of lifts over `W` does not depend
on the affine chart of `X` through which its sections are read.

## Main results

* `TauCeti.AlgebraicGeometry.liftSheafObjEquivLiftStruct_vsub_homOfLE`: the derivation by which
  two sections differ, read through `U`, is the one read through `U'` restricted along
  `Γ(U) → Γ(U')`.
* `TauCeti.AlgebraicGeometry.liftSheafObjEquivLiftStruct_symm_vadd_homOfLE`: acting on a section
  by a derivation of `Γ(U')` is acting by its restriction to `Γ(U)`.
* `TauCeti.AlgebraicGeometry.liftSheafObjEquivLiftStruct_symm_vadd_eq_compAlgebraMapEquiv_symm`:
  acting on a section by a derivation of `Γ(U)` is acting by its unique extension to `Γ(U')`.

For `f` smooth these torsors are nonempty (`hasLift_commSq_resLE`), and the affine opens `W` with
such charts form a basis of `T'` (`exists_affine_chart`).

The algebra behind these is `formallyEtale_homOfLE_appTop` (`Γ(U) → Γ(U')` is formally étale),
with the compatibilities `isScalarTower_resLE_homOfLE` and
`isScalarTower_quotientKerAppTopAlgebra_homOfLE` of the algebra structures in play.

## References

* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace TauCeti.AlgebraicGeometry

variable {X S T T' : Scheme.{u}} {f : X ⟶ S} {i : T ⟶ T'} {a : T ⟶ X} {h : T' ⟶ S}
  {W : T'.Opens} {U U' : X.Opens} {V : S.Opens}

/-- For opens `U' ⊆ U ⊆ f⁻¹ V`, the algebra structures on `Γ(U, ⊤)` and on `Γ(U', ⊤)` over
`Γ(V, ⊤)` given by `f` are compatible with the restriction `Γ(U, ⊤) ⟶ Γ(U', ⊤)`. -/
theorem isScalarTower_resLE_homOfLE (hUV : U ≤ f ⁻¹ᵁ V) (e : U' ≤ U) :
    letI := (f.resLE V U hUV).appTop.hom.toAlgebra
    letI := (f.resLE V U' (e.trans hUV)).appTop.hom.toAlgebra
    letI := (X.homOfLE e).appTop.hom.toAlgebra
    IsScalarTower Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤) Γ(U'.toScheme, ⊤) := by
  let := (f.resLE V U hUV).appTop.hom.toAlgebra
  let := (f.resLE V U' (e.trans hUV)).appTop.hom.toAlgebra
  let := (X.homOfLE e).appTop.hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
  change (f.resLE V U' (e.trans hUV)).appTop r = (X.homOfLE e).appTop ((f.resLE V U hUV).appTop r)
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Scheme.Hom.map_resLE]

/-- For opens `U' ⊆ U` of `X` with `a (i⁻¹ W) ⊆ U'`, the algebra structures
`quotientKerAppTopAlgebra` on `Γ(W, ⊤) ⧸ ker (i ∣_ W).appTop` over `Γ(U, ⊤)` and over `Γ(U', ⊤)`
are compatible with the restriction `Γ(U, ⊤) ⟶ Γ(U', ⊤)`. -/
theorem isScalarTower_quotientKerAppTopAlgebra_homOfLE [IsClosedImmersion i]
    [IsAffine W.toScheme] (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (hU' : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U') (e : U' ≤ U) :
    letI := (X.homOfLE e).appTop.hom.toAlgebra
    letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
    letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U' (i ⁻¹ᵁ W) hU')
    IsScalarTower Γ(U.toScheme, ⊤) Γ(U'.toScheme, ⊤)
      (Γ(W.toScheme, ⊤) ⧸ RingHom.ker (i ∣_ W).appTop.hom) := by
  let := (X.homOfLE e).appTop.hom.toAlgebra
  let := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
  let := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U' (i ⁻¹ᵁ W) hU')
  refine IsScalarTower.of_algebraMap_eq fun x ↦ (RingHom.quotientKerEquivOfSurjective
    (IsClosedImmersion.isAffine_surjective_of_isAffine (i ∣_ W)).2).injective ?_
  rw [quotientKerAppTopAlgebra_algebraMap]
  change _ = RingHom.quotientKerEquivOfSurjective _
    (algebraMap Γ(U'.toScheme, ⊤) _ ((X.homOfLE e).appTop x))
  rw [quotientKerAppTopAlgebra_algebraMap, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    Scheme.Hom.resLE_map]

variable [IsFirstOrderThickening i] [IsAffine W.toScheme] [IsAffine U.toScheme]
  [IsAffine U'.toScheme] [IsAffine V.toScheme]

/-- For `f` smooth, the commutative square restricted over affine opens `W ⊆ T'`, `U ⊆ X`,
`V ⊆ S` has a lift, so that the sections of the sheaf of lifts over `W` form a torsor
(`liftStructAddTorsor`). -/
instance hasLift_commSq_resLE [Smooth f] (w : a ≫ f = i ≫ h) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V) : (commSq_resLE w hU hV hUV).HasLift :=
  have := FormallySmooth.of_smooth_of_isAffine (f.resLE V U hUV)
  inferInstance

/-- The derivation by which two sections of the sheaf of lifts over an affine open `W` differ,
read through an affine open `U ⊆ X`, is the derivation read through a smaller affine open
`U' ⊆ U` restricted along `Γ(U, ⊤) ⟶ Γ(U', ⊤)`. -/
theorem liftSheafObjEquivLiftStruct_vsub_homOfLE (w : a ≫ f = i ≫ h) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (hU' : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U') (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V) (e : U' ≤ U)
    [(commSq_resLE w hU hV hUV).HasLift] [(commSq_resLE w hU' hV (e.trans hUV)).HasLift]
    (l₁ l₂ : (liftSheaf f i a h).obj.obj (op W)) :
    letI := (f.resLE V U hUV).appTop.hom.toAlgebra
    letI := (f.resLE V U' (e.trans hUV)).appTop.hom.toAlgebra
    letI := (h.resLE V W hV).appTop.hom.toAlgebra
    letI := (X.homOfLE e).appTop.hom.toAlgebra
    letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
    letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U' (i ⁻¹ᵁ W) hU')
    letI := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
    letI := Ideal.moduleOfSqEqBot Γ(U'.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
    letI := isScalarTower_resLE_homOfLE hUV e
    letI := isScalarTower_quotientKerAppTopAlgebra_homOfLE hU hU' e
    letI := Ideal.isScalarTower_moduleOfSqEqBot (A := Γ(U.toScheme, ⊤)) Γ(U'.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
    letI := liftStructAddTorsor (commSq_resLE w hU hV hUV)
    letI := liftStructAddTorsor (commSq_resLE w hU' hV (e.trans hUV))
    liftSheafObjEquivLiftStruct w hU hV hUV l₁ -ᵥ liftSheafObjEquivLiftStruct w hU hV hUV l₂ =
      (liftSheafObjEquivLiftStruct w hU' hV (e.trans hUV) l₁ -ᵥ
        liftSheafObjEquivLiftStruct w hU' hV (e.trans hUV) l₂).compAlgebraMap
          Γ(U.toScheme, ⊤) := by
  let := (f.resLE V U hUV).appTop.hom.toAlgebra
  let := (h.resLE V W hV).appTop.hom.toAlgebra
  let := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
  let := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
    (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
  refine Derivation.ext fun x ↦ Subtype.ext ?_
  exact liftSheafObjEquivLiftStruct_vsub_apply_homOfLE w hU hV hUV hU' hV (e.trans hUV) e l₁ l₂ x

/-- Acting on a section of the sheaf of lifts over an affine open `W` by a derivation of
`Γ(U', ⊤)`, through the torsor of lifts read in an affine open `U' ⊆ X`, is acting by its
restriction to `Γ(U, ⊤)` through the torsor of lifts read in an affine open `U ⊇ U'`. -/
theorem liftSheafObjEquivLiftStruct_symm_vadd_homOfLE (w : a ≫ f = i ≫ h)
    (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (hU' : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U') (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V)
    (e : U' ≤ U) [(commSq_resLE w hU hV hUV).HasLift]
    [(commSq_resLE w hU' hV (e.trans hUV)).HasLift]
    (d : letI := (f.resLE V U' (e.trans hUV)).appTop.hom.toAlgebra
      letI := (h.resLE V W hV).appTop.hom.toAlgebra
      letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U' (i ⁻¹ᵁ W) hU')
      letI := Ideal.moduleOfSqEqBot Γ(U'.toScheme, ⊤)
        (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
      Derivation Γ(V.toScheme, ⊤) Γ(U'.toScheme, ⊤) (RingHom.ker (i ∣_ W).appTop.hom))
    (l : (liftSheaf f i a h).obj.obj (op W)) :
    letI := (f.resLE V U hUV).appTop.hom.toAlgebra
    letI := (f.resLE V U' (e.trans hUV)).appTop.hom.toAlgebra
    letI := (h.resLE V W hV).appTop.hom.toAlgebra
    letI := (X.homOfLE e).appTop.hom.toAlgebra
    letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
    letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U' (i ⁻¹ᵁ W) hU')
    letI := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
    letI := Ideal.moduleOfSqEqBot Γ(U'.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
    letI := isScalarTower_resLE_homOfLE hUV e
    letI := isScalarTower_quotientKerAppTopAlgebra_homOfLE hU hU' e
    letI := Ideal.isScalarTower_moduleOfSqEqBot (A := Γ(U.toScheme, ⊤)) Γ(U'.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
    letI := liftStructAddTorsor (commSq_resLE w hU hV hUV)
    letI := liftStructAddTorsor (commSq_resLE w hU' hV (e.trans hUV))
    (liftSheafObjEquivLiftStruct w hU hV hUV).symm
        (d.compAlgebraMap Γ(U.toScheme, ⊤) +ᵥ liftSheafObjEquivLiftStruct w hU hV hUV l) =
      (liftSheafObjEquivLiftStruct w hU' hV (e.trans hUV)).symm
        (d +ᵥ liftSheafObjEquivLiftStruct w hU' hV (e.trans hUV) l) := by
  let := liftStructAddTorsor (commSq_resLE w hU hV hUV)
  let := liftStructAddTorsor (commSq_resLE w hU' hV (e.trans hUV))
  rw [Equiv.symm_apply_eq, eq_comm, eq_vadd_iff_vsub_eq,
    liftSheafObjEquivLiftStruct_vsub_homOfLE w hU hU' hV hUV e, Equiv.apply_symm_apply,
    vadd_vsub]

/-- Acting on a section of the sheaf of lifts over an affine open `W` by a derivation `d` of
`Γ(U, ⊤)`, through the torsor of lifts read in an affine open `U`, is acting through the torsor of
lifts read in an affine open `U' ⊆ U` by the unique extension of `d` to `Γ(U', ⊤)`
(`Derivation.compAlgebraMapEquiv`, as `Γ(U, ⊤) ⟶ Γ(U', ⊤)` is formally étale). -/
theorem liftSheafObjEquivLiftStruct_symm_vadd_eq_compAlgebraMapEquiv_symm (w : a ≫ f = i ≫ h)
    (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (hU' : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U') (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V)
    (e : U' ≤ U) [(commSq_resLE w hU hV hUV).HasLift]
    [(commSq_resLE w hU' hV (e.trans hUV)).HasLift]
    (d : letI := (f.resLE V U hUV).appTop.hom.toAlgebra
      letI := (h.resLE V W hV).appTop.hom.toAlgebra
      letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
      letI := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
        (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
      Derivation Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤) (RingHom.ker (i ∣_ W).appTop.hom))
    (l : (liftSheaf f i a h).obj.obj (op W)) :
    letI := (f.resLE V U hUV).appTop.hom.toAlgebra
    letI := (f.resLE V U' (e.trans hUV)).appTop.hom.toAlgebra
    letI := (h.resLE V W hV).appTop.hom.toAlgebra
    letI := (X.homOfLE e).appTop.hom.toAlgebra
    letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
    letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U' (i ⁻¹ᵁ W) hU')
    letI := isScalarTower_quotientKerAppTopAlgebra (commSq_resLE w hU hV hUV)
    letI := isScalarTower_quotientKerAppTopAlgebra (commSq_resLE w hU' hV (e.trans hUV))
    letI := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
    letI := Ideal.moduleOfSqEqBot Γ(U'.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
    letI := isScalarTower_resLE_homOfLE hUV e
    letI := isScalarTower_quotientKerAppTopAlgebra_homOfLE hU hU' e
    letI := Ideal.isScalarTower_moduleOfSqEqBot (A := Γ(U.toScheme, ⊤)) Γ(U'.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
    letI : IsScalarTower Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤) (RingHom.ker (i ∣_ W).appTop.hom) :=
      Ideal.isScalarTower_of_sq_eq_bot (IsFirstOrderThickening.ker_appTop_sq_eq_bot _)
    letI : IsScalarTower Γ(V.toScheme, ⊤) Γ(U'.toScheme, ⊤) (RingHom.ker (i ∣_ W).appTop.hom) :=
      Ideal.isScalarTower_of_sq_eq_bot (IsFirstOrderThickening.ker_appTop_sq_eq_bot _)
    letI := formallyEtale_homOfLE_appTop e
    letI := liftStructAddTorsor (commSq_resLE w hU hV hUV)
    letI := liftStructAddTorsor (commSq_resLE w hU' hV (e.trans hUV))
    (liftSheafObjEquivLiftStruct w hU hV hUV).symm
        (d +ᵥ liftSheafObjEquivLiftStruct w hU hV hUV l) =
      (liftSheafObjEquivLiftStruct w hU' hV (e.trans hUV)).symm
        ((Derivation.compAlgebraMapEquiv Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤) Γ(U'.toScheme, ⊤)
            (RingHom.ker (i ∣_ W).appTop.hom)).symm d +ᵥ
          liftSheafObjEquivLiftStruct w hU' hV (e.trans hUV) l) := by
  refine Eq.trans ?_ (liftSheafObjEquivLiftStruct_symm_vadd_homOfLE w hU hU' hV hUV e _ l)
  rw [Derivation.compAlgebraMap_compAlgebraMapEquiv_symm]

end TauCeti.AlgebraicGeometry
