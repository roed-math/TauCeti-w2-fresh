/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Extension.Presentation.Core
public import TauCeti.CategoryTheory.Limits.ConcreteCategory.Filtered

/-!
# Finitely presented algebras over filtered colimits of rings

Let `A = colim Aᵢ` be a filtered colimit of commutative rings. Every finitely presented
`A`-algebra `B` descends to some stage: there are an index `i` and a finitely presented
`Aᵢ`-algebra `Bᵢ` with `B ≅ A ⊗[Aᵢ] Bᵢ` (Stacks, Lemma 10.127.6 (00QO)). Indeed, the finitely many
coefficients of the relations of a finite presentation of `B` lie in the image of a single `Aᵢ`,
and `Bᵢ` is the quotient of the polynomial ring over `Aᵢ` by lifts of the relations, Mathlib's
`Algebra.Presentation.ModelOfHasCoeffs`.

## Main declarations

* `TauCeti.CommRingCat.exists_isPushout_of_isColimit`: a ring map of finite presentation out of a
  filtered colimit of rings is the base change of one out of some stage.
-/

public section

universe u

open CategoryTheory Limits TensorProduct

namespace TauCeti.CommRingCat

variable {I : Type u} [SmallCategory I] [IsFiltered I] {F : I ⥤ CommRingCat.{u}}
  {c : Cocone F} (hc : IsColimit c)

include hc in
/-- Let `A = colim Aᵢ` be a filtered colimit of commutative rings. Every ring map `A → B` of
finite presentation is the base change of a ring map `Aᵢ → Bᵢ` of finite presentation for some
stage `Aᵢ`, that is, `B ≅ A ⊗[Aᵢ] Bᵢ`. Stacks, Lemma 10.127.6 (00QO). -/
theorem exists_isPushout_of_isColimit {B : CommRingCat.{u}} (φ : c.pt ⟶ B)
    (hφ : φ.hom.FinitePresentation) :
    ∃ (i : I) (B₀ : CommRingCat.{u}) (g : F.obj i ⟶ B₀) (h : B₀ ⟶ B),
      g.hom.FinitePresentation ∧ IsPushout g (c.ι.app i) h φ := by
  algebraize [φ.hom]
  let P := Algebra.Presentation.ofFinitePresentation c.pt B
  obtain ⟨i, hi⟩ := TauCeti.CategoryTheory.Limits.Concrete.exists_subset_range_of_isColimit hc
    P.finite_coeffs
  let : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
  let : Algebra (F.obj i) B := (c.ι.app i ≫ φ).hom.toAlgebra
  have : IsScalarTower (F.obj i) c.pt B := .of_algebraMap_eq' rfl
  have : P.HasCoeffs (F.obj i) := ⟨hi⟩
  let B₀ := P.ModelOfHasCoeffs (F.obj i)
  refine ⟨i, .of B₀, CommRingCat.ofHom (algebraMap (F.obj i) B₀),
    CommRingCat.ofHom ((P.tensorModelOfHasCoeffsEquiv (F.obj i)).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := F.obj i) (A := c.pt)).toRingHom),
    RingHom.finitePresentation_algebraMap.mpr inferInstance, ?_⟩
  refine (CommRingCat.isPushout_tensorProduct (F.obj i) c.pt B₀).flip.of_iso (Iso.refl _)
    (Iso.refl _) (Iso.refl _)
    (P.tensorModelOfHasCoeffsEquiv (F.obj i)).toRingEquiv.toCommRingCatIso rfl rfl rfl ?_
  ext x
  rw [CommRingCat.comp_apply]
  exact (P.tensorModelOfHasCoeffsEquiv_tmul (F.obj i) x 1).trans
    (by simp [RingHom.algebraMap_toAlgebra])

end TauCeti.CommRingCat
