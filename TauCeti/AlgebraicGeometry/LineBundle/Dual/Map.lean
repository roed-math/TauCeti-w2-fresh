/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Dual
public import TauCeti.AlgebraicGeometry.Modules.Dual
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.FinitePresentation

/-!
# Duals of morphisms of line bundles

A morphism `f : K ⟶ L` of invertible sheaves induces the morphism `L^∨ ⟶ K^∨` of dual line bundles
given by precomposition with `f` (`InvertibleSheaf.dualMap`). This is contravariantly functorial.

Duality reverses monomorphisms as well: if `f` is a monomorphism of sheaves, so is its dual
(`InvertibleSheaf.mono_dualMap_hom`). For instance, an inclusion `J ⊆ I` of invertible ideal
sheaves, the ideal sheaves of effective Cartier divisors `D ≥ D'`, dualises to the inclusion
`𝒪(D') ⟶ 𝒪(D)`. The proof uses only that line bundles are invertible for the tensor product:
tensoring with a line bundle preserves and reflects monomorphisms
(`InvertibleSheaf.mono_whiskerLeft_dual`, `InvertibleSheaf.mono_of_mono_whiskerLeft`), and
`K ⊗ (dualMap f)` is `f ⊗ L^∨` up to the evaluation isomorphisms `K ⊗ K^∨ ≅ 𝒪 ≅ L ⊗ L^∨`.

## Main declarations

* `InvertibleSheaf.dualMap`: the dual of a morphism of line bundles, with `dualMap_id` and
  `dualMap_comp`;
* `InvertibleSheaf.mono_dualMap_hom`: the dual of a monomorphism is a monomorphism.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace InvertibleSheaf

variable {X : Scheme.{u}}

/-- The underlying sheaf of the dual line bundle is the internal-Hom dual in `X.Modules`. -/
lemma dual_obj_eq_ihom (L : InvertibleSheaf X) :
    (dual L).obj = (ihom L.obj).obj (𝟙_ X.Modules) := by
  rw [dual_obj]
  rfl

/-- The dual `L^∨ ⟶ K^∨` of a morphism `f : K ⟶ L` of line bundles: precomposition with `f`. -/
def dualMap {K L : InvertibleSheaf X} (f : K ⟶ L) : dual L ⟶ dual K :=
  ObjectProperty.homMk (eqToHom (dual_obj_eq_ihom L) ≫ (pre f.hom).app (𝟙_ X.Modules) ≫
    eqToHom (dual_obj_eq_ihom K).symm)

/-- The underlying sheaf map of `dualMap f` is the internal-Hom map induced by precomposition with
`f`, transported to the underlying sheaves of the dual line bundles. -/
lemma dualMap_hom {K L : InvertibleSheaf X} (f : K ⟶ L) :
    (dualMap f).hom = eqToHom (dual_obj_eq_ihom L) ≫ (pre f.hom).app (𝟙_ X.Modules) ≫
      eqToHom (dual_obj_eq_ihom K).symm :=
  (rfl)

/-- The dual of the identity is the identity. -/
@[simp]
lemma dualMap_id (L : InvertibleSheaf X) : dualMap (𝟙 L) = 𝟙 (dual L) := by
  ext1
  simp only [dualMap_hom, ObjectProperty.FullSubcategory.id_hom, pre_id, NatTrans.id_app,
    Category.id_comp, eqToHom_trans, eqToHom_refl]

/-- Duality reverses composition. -/
@[simp]
lemma dualMap_comp {K L M : InvertibleSheaf X} (f : K ⟶ L) (g : L ⟶ M) :
    dualMap (f ≫ g) = dualMap g ≫ dualMap f := by
  ext1
  simp only [dualMap_hom, ObjectProperty.FullSubcategory.comp_hom, pre_map, NatTrans.comp_app,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- Tensoring with the dual of a line bundle preserves monomorphisms: it is the internal Hom out of
the line bundle, a right adjoint. -/
theorem mono_whiskerLeft_dual (L : InvertibleSheaf X) {A B : X.Modules} (g : A ⟶ B) [Mono g] :
    Mono ((ihom L.obj).obj (𝟙_ X.Modules) ◁ g) := by
  have : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
  -- Instance search does not unfold `X.Modules`, so the sheaf is rebound with the type of sheaves
  -- of modules to find local freeness and finite type.
  let F : _root_.SheafOfModules X.ringCatSheaf := L.obj
  have : L.obj.IsLocallyFree := inferInstanceAs F.IsLocallyFree
  have : L.obj.IsFiniteType := inferInstanceAs F.IsFiniteType
  have : Mono ((ihom L.obj).map g) := (ihom L.obj).map_mono g
  have : Mono ((ihom L.obj).obj (𝟙_ X.Modules) ◁ g ≫ (dualTensorIhom L.obj).app B) := by
    rw [show (ihom L.obj).obj (𝟙_ X.Modules) ◁ g = (tensorLeft _).map g from rfl,
      (dualTensorIhom L.obj).naturality g]
    infer_instance
  exact mono_of_mono _ ((dualTensorIhom L.obj).app B)

/-- Tensoring with a line bundle reflects monomorphisms: `L^∨ ⊗ L ≅ 𝒪_X`, so `g` is
`L^∨ ⊗ (L ⊗ g)` up to isomorphism. -/
theorem mono_of_mono_whiskerLeft (L : InvertibleSheaf X) {A B : X.Modules} (g : A ⟶ B)
    [Mono (L.obj ◁ g)] : Mono g := by
  have : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
  have : IsIso ((ihom.ev L.obj).app (𝟙_ X.Modules)) :=
    _root_.SheafOfModules.isIso_evaluation_dual_of_isInvertible (R := X.sheaf) L.obj
  let e : (ihom L.obj).obj (𝟙_ X.Modules) ⊗ L.obj ≅ 𝟙_ X.Modules :=
    β_ _ _ ≪≫ asIso ((ihom.ev L.obj).app (𝟙_ X.Modules))
  let φ : ∀ Z : X.Modules, (ihom L.obj).obj (𝟙_ X.Modules) ⊗ L.obj ⊗ Z ≅ Z := fun Z ↦
    (α_ _ _ _).symm ≪≫ whiskerRightIso e Z ≪≫ λ_ Z
  have : Mono ((ihom L.obj).obj (𝟙_ X.Modules) ◁ L.obj ◁ g) := mono_whiskerLeft_dual L _
  have h : g = (φ A).inv ≫ (ihom L.obj).obj (𝟙_ X.Modules) ◁ L.obj ◁ g ≫ (φ B).hom := by
    rw [Iso.eq_inv_comp]
    simp only [φ, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, Category.assoc,
      associator_inv_naturality_right_assoc, whisker_exchange_assoc, leftUnitor_naturality]
  rw [h]
  infer_instance

/-- **The dual of a monomorphism of line bundles is a monomorphism.** -/
instance mono_dualMap_hom {K L : InvertibleSheaf X} (f : K ⟶ L) [Mono f.hom] :
    Mono (dualMap f).hom := by
  have : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) K.obj := K.property
  have : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
  have : IsIso ((ihom.ev K.obj).app (𝟙_ X.Modules)) :=
    _root_.SheafOfModules.isIso_evaluation_dual_of_isInvertible (R := X.sheaf) K.obj
  have : IsIso ((ihom.ev L.obj).app (𝟙_ X.Modules)) :=
    _root_.SheafOfModules.isIso_evaluation_dual_of_isInvertible (R := X.sheaf) L.obj
  -- `f ⊗ L^∨` is a monomorphism, as `L^∨ ⊗ f` is.
  have : Mono (f.hom ▷ (ihom L.obj).obj (𝟙_ X.Modules)) := by
    have : Mono (f.hom ▷ (ihom L.obj).obj (𝟙_ X.Modules) ≫ (β_ _ _).hom) := by
      rw [BraidedCategory.braiding_naturality_left]
      have := mono_whiskerLeft_dual L f.hom
      infer_instance
    exact mono_of_mono _ (β_ _ _).hom
  -- Up to the evaluation isomorphisms, `K ⊗ dualMap f` is `f ⊗ L^∨`.
  have : Mono (K.obj ◁ (pre f.hom).app (𝟙_ X.Modules)) := by
    have : Mono (K.obj ◁ (pre f.hom).app (𝟙_ X.Modules) ≫ (ihom.ev K.obj).app (𝟙_ X.Modules)) := by
      rw [id_tensor_pre_app_comp_ev]
      infer_instance
    exact mono_of_mono _ ((ihom.ev K.obj).app (𝟙_ X.Modules))
  have := mono_of_mono_whiskerLeft K ((pre f.hom).app (𝟙_ X.Modules))
  rw [dualMap_hom]
  infer_instance

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
