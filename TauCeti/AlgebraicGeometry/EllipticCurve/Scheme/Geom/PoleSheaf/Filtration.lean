/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Inclusion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PoleSheaf

/-!
# The pole filtration of an elliptic curve

Let `E` be an elliptic curve over a scheme `S`, with structure morphism `π : E ⟶ S`. For `m ≤ n`
the divisor `n[0]` contains `m[0]`, so the pole sheaf `ℒ_m = 𝒪_E(m[0])` includes into
`ℒ_n = 𝒪_E(n[0])` (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleSheafMap`), the dual of the
inclusion `𝒪_E(-n[0]) ⊆ 𝒪_E(-m[0])` of ideal sheaves. These inclusions are monomorphisms,
compatible with composition. The direct image is a right adjoint, so they stay monomorphisms
after pushing forward along `π`: this is the **pole filtration**
`π_*ℒ_1 ⊆ π_*ℒ_2 ⊆ ⋯ ⊆ π_*ℒ_n` of the locally free sheaf `π_*ℒ_n` of rank `n`.

## Main declarations

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleSheafMap`: the inclusion `ℒ_m ⟶ ℒ_n` for
  `m ≤ n`, a monomorphism (`mono_poleSheafMap_hom`), with `poleSheafMap_refl` and
  `poleSheafMap_comp`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mono_pushforward_map_poleSheafMap`: the induced
  map `π_*ℒ_m ⟶ π_*ℒ_n` is a monomorphism.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1 and 2.2.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- The divisor `n[0]` contains `m[0]` for `m ≤ n`: its ideal sheaf `𝒪_E(-n[0])` is contained in
`𝒪_E(-m[0])`. -/
theorem zeroDivisor_pow_le_pow {m n : ℕ} (h : m ≤ n) : E.zeroDivisor ^ n ≤ E.zeroDivisor ^ m :=
  pow_le_pow_right_of_le_one' le_top h

/-- The **pole filtration**: the inclusion `ℒ_m ⟶ ℒ_n` of pole sheaves for `m ≤ n`, the dual of
the inclusion `𝒪_E(-n[0]) ⊆ 𝒪_E(-m[0])` of ideal sheaves. -/
noncomputable def poleSheafMap {m n : ℕ} (h : m ≤ n) : E.poleSheaf m ⟶ E.poleSheaf n :=
  eqToHom (E.poleSheaf_def m) ≫
    Scheme.IdealSheafData.IsEffectiveCartier.dualMap
      (E.isRelativeEffectiveCartier_zeroDivisor_pow m).isEffectiveCartier
      (E.isRelativeEffectiveCartier_zeroDivisor_pow n).isEffectiveCartier
      (E.zeroDivisor_pow_le_pow h) ≫
    eqToHom (E.poleSheaf_def n).symm

/-- Through `poleSheaf_def`, `poleSheafMap` is the dual of the inclusion of ideal sheaves. -/
theorem poleSheafMap_def {m n : ℕ} (h : m ≤ n) :
    E.poleSheafMap h = eqToHom (E.poleSheaf_def m) ≫
      Scheme.IdealSheafData.IsEffectiveCartier.dualMap
        (E.isRelativeEffectiveCartier_zeroDivisor_pow m).isEffectiveCartier
        (E.isRelativeEffectiveCartier_zeroDivisor_pow n).isEffectiveCartier
        (E.zeroDivisor_pow_le_pow h) ≫
      eqToHom (E.poleSheaf_def n).symm :=
  (rfl)

/-- The inclusion `ℒ_m ⟶ ℒ_n` is a monomorphism of sheaves. -/
instance mono_poleSheafMap_hom {m n : ℕ} (h : m ≤ n) : Mono (E.poleSheafMap h).hom := by
  rw [poleSheafMap_def, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.eqToHom_hom, ObjectProperty.eqToHom_hom]
  infer_instance

/-- The inclusion of `ℒ_n` into itself is the identity. -/
@[simp]
theorem poleSheafMap_refl (n : ℕ) : E.poleSheafMap (le_refl n) = 𝟙 _ := by
  simp [poleSheafMap_def]

/-- The inclusions of the pole filtration compose. -/
@[reassoc (attr := simp)]
theorem poleSheafMap_comp {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) :
    E.poleSheafMap h₁ ≫ E.poleSheafMap h₂ = E.poleSheafMap (h₁.trans h₂) := by
  simp [poleSheafMap_def]

/-- **The pole filtration of `π_*ℒ_n`**: for `m ≤ n`, the inclusion `ℒ_m ⟶ ℒ_n` pushes forward to
a monomorphism `π_*ℒ_m ⟶ π_*ℒ_n`. -/
theorem mono_pushforward_map_poleSheafMap {m n : ℕ} (h : m ≤ n) :
    Mono ((Scheme.Modules.pushforward E.structureMap).map (E.poleSheafMap h).hom) :=
  inferInstance

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
