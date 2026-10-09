/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZMod.SMulCommClass
public import TauCeti.Data.ZMod.TrivialAction
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.FieldTheory.GaloisCohomology.EquivariantKummer
public import TauCeti.NumberTheory.ClassFieldTheory.FiniteQuotient
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousMulEquiv
public import TauCeti.RepresentationTheory.Homological.ContCohomology.H1.ZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.FiniteQuotient
public import TauCeti.RepresentationTheory.Induction.FiniteDimensional.Basic

set_option warningAsError false

/-!
# Lookahead stubs for the mixed-characteristic Euler characteristic

These are the declarations consumed from the supplier targets
`euler-characteristic-shapiro` and `kummer-equiv-mixed-equivariant`. They are to be replaced by
the landed declarations before the target is submitted.
-/

public noncomputable section

namespace TauCeti

open ContCohomology

universe u v

/-! ## Equivariant Kummer -/

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

local instance : DistribMulAction (AbsoluteGaloisGroup K) (ZMod n) :=
  trivialZModAction n (AbsoluteGaloisGroup K)

local instance : ContinuousSMul (AbsoluteGaloisGroup K) (ZMod n) :=
  ⟨continuous_snd⟩

section FiniteGalois

variable [Normal K L] (sigma : L →ₐ[K] SeparableClosure K) (n : ℕ)

/-- Equivariant Kummer theory with constant coefficients. -/
def kummerEquiv_mixed {ell : ℕ} [Fact ell.Prime]
    (hn : IsUnit (ell : K))
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K ell, g • xi = xi) :
    (kummerH1FiniteRepresentation sigma ell).Equiv
      ((kummerCoeffFiniteRepresentation sigma ell hN).dual.tprod
        (powerClassRepresentation (K := K) (L := L) ell)) :=
  sorry

end FiniteGalois

namespace ClassFieldTheory

open CategoryTheory

/-! ## Shapiro comparison -/

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]
  (sigma : L →ₐ[K] SeparableClosure K)

variable (n : ℕ) {V : OpenNormalSubgroup (Field.absoluteGaloisGroup K)}
  {C : Subgroup (Field.absoluteGaloisGroup K ⧸ V.toSubgroup)}
  (hσ : (absoluteGaloisGroupExtend K L sigma).range =
    C.comap (QuotientGroup.mk' V.toSubgroup))

/-- A representation of `C` read as a Galois representation of its fixed field. -/
def shapiroGalRep (sigma : L →ₐ[K] SeparableClosure K) (n : ℕ)
    {V : OpenNormalSubgroup (Field.absoluteGaloisGroup K)}
    {C : Subgroup (Field.absoluteGaloisGroup K ⧸ V.toSubgroup)}
    (hσ : (absoluteGaloisGroupExtend K L sigma).range =
      C.comap (QuotientGroup.mk' V.toSubgroup))
    (B : Rep (ZMod n) C) : GalRep n L :=
  sorry

variable (B : Rep (ZMod n) C)

instance : DiscreteTopology (shapiroGalRep sigma n hσ B).V :=
  sorry

instance [Finite B] : Finite (shapiroGalRep sigma n hσ B).V :=
  sorry

instance : Fact (IsSmoothDiscrete (ZMod n) (shapiroGalRep sigma n hσ B)) :=
  sorry

/-- Shapiro's lemma for the local Euler characteristic. -/
theorem localEulerCharacteristic_galRepOfQuotient_ind
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (hn : (n : K) ≠ 0) [Finite B] :
    localEulerCharacteristic hn ((galRepOfQuotient n K V).obj (Rep.ind C.subtype B)) =
      localEulerCharacteristic
        (map_natCast (algebraMap K L) n ▸ (map_ne_zero (algebraMap K L)).2 hn)
        (shapiroGalRep sigma n hσ B) :=
  sorry

/-- Shapiro's lemma for the normalized coefficient order. -/
theorem localCardNorm_galRepOfQuotient_ind (p : ℕ) [Fact p.Prime]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [FinitePadicExtension K p] [FinitePadicExtension L p]
    [IsScalarTower ℚ_[p] K L] [Finite B] :
    localCardNorm p ((galRepOfQuotient n K V).obj (Rep.ind C.subtype B)) =
      localCardNorm p (shapiroGalRep sigma n hσ B) :=
  sorry

end ClassFieldTheory

end TauCeti
