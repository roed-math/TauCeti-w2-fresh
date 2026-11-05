/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.IdealSheaf.Inclusion
public import TauCeti.AlgebraicGeometry.LineBundle.Dual.Map

/-!
# Inclusions of effective Cartier divisors and their line bundles

Let `D' ≤ D` be effective Cartier divisors on a scheme `X`, with invertible ideal sheaves
`𝒪(-D) ⊆ 𝒪(-D')`. The inclusion is a monomorphism of line bundles
(`Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheafMap`), and its dual is the inclusion
`𝒪(D') ⟶ 𝒪(D)` of the line bundles of the divisors
(`Scheme.IdealSheafData.IsEffectiveCartier.dualMap`), again a monomorphism of sheaves. Both are
functorial in the inequality.

## Main declarations

* `Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheafMap`: the inclusion `𝒪(-D) ⟶ 𝒪(-D')`
  of invertible ideal sheaves;
* `Scheme.IdealSheafData.IsEffectiveCartier.dualMap`: the inclusion `𝒪(D') ⟶ 𝒪(D)` of their duals,
  a monomorphism of sheaves (`Scheme.IdealSheafData.IsEffectiveCartier.mono_dualMap_hom`).
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

noncomputable section

variable {X : Scheme.{u}} {I J K : X.IdealSheafData}

/-- For effective Cartier ideal sheaves `J ≤ I`, the inclusion `J ⟶ I` as a morphism of invertible
sheaves. -/
def toInvertibleSheafMap (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier) (h : J ≤ I) :
    hJ.toInvertibleSheaf ⟶ hI.toInvertibleSheaf :=
  ObjectProperty.homMk (eqToHom hJ.toInvertibleSheaf_obj ≫ sheafOfLE h ≫
    eqToHom hI.toInvertibleSheaf_obj.symm)

/-- The underlying sheaf map of `toInvertibleSheafMap` is the inclusion of ideal sheaves. -/
lemma toInvertibleSheafMap_hom (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
    (h : J ≤ I) :
    (toInvertibleSheafMap hI hJ h).hom = eqToHom hJ.toInvertibleSheaf_obj ≫ sheafOfLE h ≫
      eqToHom hI.toInvertibleSheaf_obj.symm :=
  (rfl)

instance mono_toInvertibleSheafMap_hom (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
    (h : J ≤ I) : Mono (toInvertibleSheafMap hI hJ h).hom := by
  rw [toInvertibleSheafMap_hom]
  infer_instance

/-- The inclusion of an invertible ideal sheaf into itself is the identity. -/
@[simp]
lemma toInvertibleSheafMap_refl (hI : I.IsEffectiveCartier) :
    toInvertibleSheafMap hI hI le_rfl = 𝟙 _ := by
  ext1
  simp only [toInvertibleSheafMap_hom, sheafOfLE_refl, ObjectProperty.FullSubcategory.id_hom,
    Category.id_comp, eqToHom_trans, eqToHom_refl]

/-- The inclusions of invertible ideal sheaves compose. -/
@[reassoc (attr := simp)]
lemma toInvertibleSheafMap_comp (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
    (hK : K.IsEffectiveCartier) (h₁ : K ≤ J) (h₂ : J ≤ I) :
    toInvertibleSheafMap hJ hK h₁ ≫ toInvertibleSheafMap hI hJ h₂ =
      toInvertibleSheafMap hI hK (h₁.trans h₂) := by
  ext1
  simp only [toInvertibleSheafMap_hom, ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, sheafOfLE_comp_assoc]

/-- For effective Cartier divisors `D' ≤ D` with ideal sheaves `I = 𝒪(-D') ⊇ J = 𝒪(-D)`, the
inclusion `𝒪(D') ⟶ 𝒪(D)` of their line bundles: the dual of the inclusion `J ⟶ I`. -/
def dualMap (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier) (h : J ≤ I) :
    InvertibleSheaf.dual hI.toInvertibleSheaf ⟶ InvertibleSheaf.dual hJ.toInvertibleSheaf :=
  InvertibleSheaf.dualMap (toInvertibleSheafMap hI hJ h)

/-- **The inclusion `𝒪(D') ⟶ 𝒪(D)` is a monomorphism of sheaves.** -/
instance mono_dualMap_hom (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier) (h : J ≤ I) :
    Mono (dualMap hI hJ h).hom :=
  InvertibleSheaf.mono_dualMap_hom _

/-- The inclusion of `𝒪(D)` into itself is the identity. -/
@[simp]
lemma dualMap_refl (hI : I.IsEffectiveCartier) : dualMap hI hI le_rfl = 𝟙 _ := by
  rw [dualMap, toInvertibleSheafMap_refl, InvertibleSheaf.dualMap_id]

/-- The inclusions `𝒪(D'') ⟶ 𝒪(D') ⟶ 𝒪(D)` compose. -/
@[reassoc (attr := simp)]
lemma dualMap_comp (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
    (hK : K.IsEffectiveCartier) (h₁ : K ≤ J) (h₂ : J ≤ I) :
    dualMap hI hJ h₂ ≫ dualMap hJ hK h₁ = dualMap hI hK (h₁.trans h₂) := by
  rw [dualMap, dualMap, dualMap, ← InvertibleSheaf.dualMap_comp, toInvertibleSheafMap_comp]

end

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
