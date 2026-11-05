/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Inclusion
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
public import TauCeti.AlgebraicGeometry.LineBundle.Class
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent

/-!
# Pullback of inclusions of effective Cartier divisors

Let `D' ≤ D` be effective Cartier divisors on a scheme `Y`, with ideal sheaves `J ⊆ I`, and let
`g : X ⟶ Y` be a morphism along which both inverse images are again effective Cartier, for instance
the base change of relative effective Cartier divisors. Pulling back along `g` is not left exact,
so it need not preserve monomorphisms. It does preserve the inclusions of these divisors:
the pullback of `J ⟶ I` is the inclusion `J.comap g ⟶ I.comap g` up to the comparison
isomorphisms `g^* I ≅ I.comap g`
(`Scheme.IdealSheafData.pullback_map_sheafOfLE_comp_pullbackSheafHom`), hence a monomorphism.
Dually, the pullback of the inclusion `𝒪(D') ⟶ 𝒪(D)` of line bundles is a monomorphism
(`Scheme.IdealSheafData.IsEffectiveCartier.mono_pullback_map_dualMap_hom`).

The dual statement holds for every morphism `f : K ⟶ L` of line bundles: if `g^* f` is a
monomorphism, so is `g^*` of the dual `L^∨ ⟶ K^∨` of `f`
(`InvertibleSheaf.mono_pullback_map_dualMap_hom`). As in `InvertibleSheaf.mono_dualMap_hom`, the
proof uses only that pullback is monoidal on quasicoherent sheaves and that tensoring with a line
bundle preserves and reflects monomorphisms (`InvertibleSheaf.mono_whiskerLeft`).

## Main declarations

* `InvertibleSheaf.mono_whiskerLeft`, `InvertibleSheaf.mono_whiskerRight`: tensoring with a line
  bundle preserves monomorphisms;
* `InvertibleSheaf.mono_pullback_map_dualMap_hom`: pullback preserves the monomorphisms dual to
  those it preserves;
* `Scheme.IdealSheafData.IsEffectiveCartier.mono_pullback_map_toInvertibleSheafMap_hom` and
  `Scheme.IdealSheafData.IsEffectiveCartier.mono_pullback_map_dualMap_hom`: pullback preserves the
  inclusions `𝒪(-D) ⟶ 𝒪(-D')` and `𝒪(D') ⟶ 𝒪(D)` when the inverse images are effective Cartier.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Functor.OplaxMonoidal AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

variable {X Y : Scheme.{u}}

/-- Tensoring with a line bundle preserves monomorphisms: a line bundle is the dual of its dual,
and tensoring with a dual is a right adjoint. -/
theorem mono_whiskerLeft (N : InvertibleSheaf X) {A B : X.Modules} (h : A ⟶ B) [Mono h] :
    Mono (N.obj ◁ h) := by
  obtain ⟨e⟩ := LineBundleClass.mk_eq_mk_iff.mp
    (by rw [← LineBundleClass.inv_mk, ← LineBundleClass.inv_mk, inv_inv] :
      LineBundleClass.mk (dual (dual N)) = LineBundleClass.mk N)
  have : Mono ((dual (dual N)).obj ◁ h) := by
    rw [dual_obj_eq_ihom (dual N)]
    exact mono_whiskerLeft_dual _ h
  have he : N.obj ◁ h = e.inv ▷ A ≫ (dual (dual N)).obj ◁ h ≫ e.hom ▷ B := by
    rw [← whisker_exchange_assoc, ← comp_whiskerRight, e.inv_hom_id, id_whiskerRight,
      Category.comp_id]
  rw [he]
  infer_instance

/-- Tensoring with a line bundle on the right preserves monomorphisms. -/
theorem mono_whiskerRight (N : InvertibleSheaf X) {A B : X.Modules} (h : A ⟶ B) [Mono h] :
    Mono (h ▷ N.obj) := by
  have := mono_whiskerLeft N h
  have : Mono (h ▷ N.obj ≫ (β_ B N.obj).hom) := by
    rw [BraidedCategory.braiding_naturality_left]
    infer_instance
  exact mono_of_mono _ (β_ B N.obj).hom

/-- **Pullback preserves the duals of the monomorphisms it preserves.** If the pullback along `g`
of a morphism `f : K ⟶ L` of line bundles is a monomorphism, so is the pullback of its dual
`L^∨ ⟶ K^∨`. -/
theorem mono_pullback_map_dualMap_hom (g : X ⟶ Y) {K L : InvertibleSheaf Y} (f : K ⟶ L)
    [Mono ((Scheme.Modules.pullback g).map f.hom)] :
    Mono ((Scheme.Modules.pullback g).map (dualMap f).hom) := by
  let G := Scheme.Modules.pullback g
  have : IsIso ((ihom.ev K.obj).app (𝟙_ Y.Modules)) :=
    _root_.SheafOfModules.isIso_evaluation_dual_of_isInvertible (R := Y.sheaf) K.obj
  have : IsIso ((ihom.ev L.obj).app (𝟙_ Y.Modules)) :=
    _root_.SheafOfModules.isIso_evaluation_dual_of_isInvertible (R := Y.sheaf) L.obj
  -- `g^*(f ⊗ L^∨)` is `g^* f ⊗ g^* L^∨` up to the tensor comparisons, a monomorphism.
  have : Mono (G.map (f.hom ▷ (ihom L.obj).obj (𝟙_ Y.Modules))) := by
    have : Mono (G.map f.hom ▷ G.obj ((ihom L.obj).obj (𝟙_ Y.Modules))) := by
      have := mono_whiskerRight ((pullback g).obj (dual L)) (G.map f.hom)
      rwa [pullback_obj_obj, dual_obj_eq_ihom] at this
    have : Mono (G.map (f.hom ▷ (ihom L.obj).obj (𝟙_ Y.Modules)) ≫ δ G L.obj _) := by
      rw [← δ_natural_left]
      infer_instance
    exact mono_of_mono _ (δ G L.obj _)
  -- Up to the evaluation isomorphisms, `g^*(K ⊗ dualMap f)` is `g^*(f ⊗ L^∨)`.
  have : Mono (G.map (K.obj ◁ (pre f.hom).app (𝟙_ Y.Modules))) := by
    have : Mono (G.map (K.obj ◁ (pre f.hom).app (𝟙_ Y.Modules)) ≫
        G.map ((ihom.ev K.obj).app (𝟙_ Y.Modules))) := by
      rw [← Functor.map_comp, id_tensor_pre_app_comp_ev, Functor.map_comp]
      infer_instance
    exact mono_of_mono _ (G.map ((ihom.ev K.obj).app (𝟙_ Y.Modules)))
  have : Mono (G.obj K.obj ◁ G.map ((pre f.hom).app (𝟙_ Y.Modules))) := by
    have : Mono (δ G K.obj _ ≫ G.obj K.obj ◁ G.map ((pre f.hom).app (𝟙_ Y.Modules))) := by
      rw [δ_natural_right]
      infer_instance
    have he : G.obj K.obj ◁ G.map ((pre f.hom).app (𝟙_ Y.Modules)) = inv (δ G K.obj _) ≫
        δ G K.obj _ ≫ G.obj K.obj ◁ G.map ((pre f.hom).app (𝟙_ Y.Modules)) := by
      rw [IsIso.inv_hom_id_assoc]
    rw [he]
    infer_instance
  have : Mono (((pullback g).obj K).obj ◁ G.map ((pre f.hom).app (𝟙_ Y.Modules))) := this
  have := mono_of_mono_whiskerLeft ((pullback g).obj K) (G.map ((pre f.hom).app (𝟙_ Y.Modules)))
  rw [dualMap_hom, Functor.map_comp, Functor.map_comp]
  infer_instance

end TauCeti.AlgebraicGeometry.InvertibleSheaf

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} {I J : Y.IdealSheafData} (g : X ⟶ Y)

/-- The pullback of the inclusion `J ⟶ I` of ideal sheaves is the inclusion
`J.comap g ⟶ I.comap g`, up to the comparison morphisms `g^* I ⟶ I.comap g`. -/
@[reassoc]
lemma pullback_map_sheafOfLE_comp_pullbackSheafHom (h : J ≤ I) :
    (Scheme.Modules.pullback g).map (sheafOfLE h) ≫ I.pullbackSheafHom g =
      J.pullbackSheafHom g ≫ sheafOfLE (comap_mono g h) := by
  rw [← cancel_mono (I.comap g).sheafι]
  -- The associativity is that of `X.Modules`, which `Category.assoc` does not find unaided.
  refine (Category.assoc (obj := X.Modules) _ _ _).trans
    (Eq.trans ?_ (Category.assoc (obj := X.Modules) _ _ _).symm)
  rw [pullbackSheafHom_sheafι, sheafOfLE_sheafι, pullbackSheafHom_sheafι]
  exact (Category.assoc (obj := X.Modules) _ _ _).symm.trans
    (congrArg (· ≫ _) (((Scheme.Modules.pullback g).map_comp _ _).symm.trans
      (congrArg _ (sheafOfLE_sheafι h))))

namespace IsEffectiveCartier

variable {g}
variable (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
  (hI' : (I.comap g).IsEffectiveCartier) (hJ' : (J.comap g).IsEffectiveCartier) (h : J ≤ I)

include hI hJ hI' hJ' in
/-- **Pullback preserves inclusions of effective Cartier divisors**: if `J ≤ I` are effective
Cartier and so are their inverse images along `g`, the pullback of `J ⟶ I` is a monomorphism. -/
theorem mono_pullback_map_sheafOfLE :
    Mono ((Scheme.Modules.pullback g).map (sheafOfLE h)) := by
  have := isIso_pullbackSheafHom I g hI hI'
  have := isIso_pullbackSheafHom J g hJ hJ'
  have : Mono ((Scheme.Modules.pullback g).map (sheafOfLE h) ≫ I.pullbackSheafHom g) := by
    rw [pullback_map_sheafOfLE_comp_pullbackSheafHom]
    infer_instance
  exact mono_of_mono _ (I.pullbackSheafHom g)

include hI' hJ' in
/-- The pullback of the inclusion `𝒪(-D) ⟶ 𝒪(-D')` of invertible ideal sheaves is a monomorphism
when the inverse images of the divisors are effective Cartier. -/
theorem mono_pullback_map_toInvertibleSheafMap_hom :
    Mono ((Scheme.Modules.pullback g).map (toInvertibleSheafMap hI hJ h).hom) := by
  have := mono_pullback_map_sheafOfLE hI hJ hI' hJ' h
  rw [toInvertibleSheafMap_hom, Functor.map_comp, Functor.map_comp]
  infer_instance

include hI' hJ' in
/-- **Pullback preserves the inclusion `𝒪(D') ⟶ 𝒪(D)`** of the line bundles of effective Cartier
divisors `D' ≤ D` whose inverse images are effective Cartier. -/
theorem mono_pullback_map_dualMap_hom :
    Mono ((Scheme.Modules.pullback g).map (dualMap hI hJ h).hom) := by
  have := mono_pullback_map_toInvertibleSheafMap_hom hI hJ hI' hJ' h
  rw [dualMap_def]
  exact TauCeti.AlgebraicGeometry.InvertibleSheaf.mono_pullback_map_dualMap_hom g
    (toInvertibleSheafMap hI hJ h)

end IsEffectiveCartier

end AlgebraicGeometry.Scheme.IdealSheafData
