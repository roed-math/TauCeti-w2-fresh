/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PositiveDegree.DirectImage
public import TauCeti.AlgebraicGeometry.Modules.Pushforward.BaseChange
import TauCeti.AlgebraicGeometry.Cohomology.FlatBaseChange
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.BaseChange
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.RingTheory.TensorProduct.IsBaseChange.BijectiveAlgebraMap

/-!
# `π_*M` commutes with base change for a line bundle `M` of positive fibre degree

Let `E` be an elliptic curve over a scheme `S`, with structure morphism `π : E ⟶ S`, let
`f : S' ⟶ S` be a morphism of schemes and let `E'` over `S'` be the base change of `E` along `f`,
given by a pullback square `hg` with projection `g : E' ⟶ E`. Let `M` be an invertible sheaf on `E`
of positive degree on every geometric fibre. This file shows that the base change morphism
`f^* π_* M ⟶ π'_* g^* M` is an isomorphism
(`EllipticCurveGeom.isIso_pushforwardBaseChange_app_of_forall_eulerDegree_pos`), so the formation
of `π_* M` commutes with arbitrary base change. This is the base change clause of the
positive-degree theorem used by elliptic autoduality.

It suffices to check bijectivity on sections over a basis of affine opens, and over an affine
open `V` lying over an affine open `U` it suffices that pulling back sections exhibits the
sections of `g^* M` over `π'⁻¹ V` as a base change of those of `M` over `π⁻¹ U`
(`AlgebraicGeometry.Scheme.Modules.bijective_pushforwardBaseChange_app_app_of_isBaseChange`).
We use the images `V` of the bases of the pointed Weierstrass charts `k` of `E'` whose bases map
over `f` into the base `U` of a chart `c` of `E`. Over such a pair the restrictions of `E` and `E'`
are the projective models of the chart equations, the second the base change of the first
(`TauCeti.AlgebraicGeometry.PointedWeierstrassChart.isPullback_modelMap`). The restriction of `M`
to the model of `c` has positive degree on every fibre
(`EllipticCurveGeom.eulerDegree_pullback_projModelBaseChange_pos`), so the base change property
is cohomology and base change for its `H⁰`
(`WeierstrassCurve.bijective_cohomologyBaseChange_zero_of_forall_eulerDegree_pos`). The rings of
the charts are identified with the functions on `U` and `V`, and
`IsBaseChange.restrictScalars_of_bijective` transports the base change statement along these
identifications.

## Main results

* `EllipticCurveGeom.isIso_pushforwardBaseChange_app_of_forall_eulerDegree_pos`: for `M` of
  positive degree on every geometric fibre, the base change morphism of `π_* M` along any morphism
  of schemes is an isomorphism.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

open Scheme.Modules

/-- The functions on `U` inside the image of an open immersion `j` are the functions on an open
equal to `j⁻¹ U`. -/
private lemma bijective_appLE {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] {U : Y.Opens}
    (hU : U ≤ j.opensRange) {V : X.Opens} (hV : V ≤ j ⁻¹ᵁ U) (hV' : j ⁻¹ᵁ U ≤ V) :
    Function.Bijective (j.appLE U V hV) := by
  have := j.isIso_app U hU
  have h : homOfLE hV = eqToHom (le_antisymm hV hV') := Subsingleton.elim _ _
  rw [Scheme.Hom.appLE, h]
  exact ConcreteCategory.bijective_of_isIso _

namespace PointedWeierstrassChart

variable {S X : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X}

/-- The image of the projective model of the equation of a chart in `X` is the inverse image of
the image of the base. -/
private lemma opensRange_modelIso_inv_toTotal (c : PointedWeierstrassChart π zero) :
    (c.modelIso.inv ≫ c.toTotal).opensRange = π ⁻¹ᵁ c.baseMap.opensRange := by
  rw [Scheme.Hom.opensRange_comp_of_isIso, c.opensRange_toTotal]

private lemma top_le_preimage_modelIso_inv_toTotal (c : PointedWeierstrassChart π zero) :
    ⊤ ≤ (c.modelIso.inv ≫ c.toTotal) ⁻¹ᵁ (π ⁻¹ᵁ c.baseMap.opensRange) := by
  rw [← opensRange_modelIso_inv_toTotal, Scheme.Hom.preimage_opensRange]

variable {S' X' : Scheme.{u}} {π' : X' ⟶ S'} {zero' : S' ⟶ X'} {g : X' ⟶ X} {f : S' ⟶ S}
  (hg : IsPullback g π' π f) {k : PointedWeierstrassChart π' zero'}
  {c : PointedWeierstrassChart π zero} {h : k.base ⟶ c.base}
  (hh : h ≫ c.baseMap = k.baseMap ≫ f)

include hh in
private lemma opensRange_le_preimage_opensRange :
    k.baseMap.opensRange ≤ f ⁻¹ᵁ c.baseMap.opensRange := by
  rintro _ ⟨x, rfl⟩
  exact ⟨h x, by rw [← Scheme.Hom.comp_apply, hh, Scheme.Hom.comp_apply]⟩

include hg hh in
private lemma preimage_le_preimage_preimage :
    π' ⁻¹ᵁ k.baseMap.opensRange ≤ g ⁻¹ᵁ π ⁻¹ᵁ c.baseMap.opensRange := by
  rw [← Scheme.Hom.comp_preimage, hg.w, Scheme.Hom.comp_preimage]
  exact fun x hx ↦ opensRange_le_preimage_opensRange hh hx

private lemma modelMap_comp_modelIso_inv_toTotal :
    modelMap hg hh ≫ c.modelIso.inv ≫ c.toTotal = (k.modelIso.inv ≫ k.toTotal) ≫ g := by
  rw [← cancel_epi k.modelIso.hom]
  simp [modelIso_hom_modelMap_assoc]

/-- The ring map underlying `modelMap hg hh` on global functions, read through the structure
morphisms and the inclusions of the models: `Γ(S, U) → Γ(S', V) → Γ(E'_V) → Γ(model of k)` agrees
with `Γ(S, U) → Γ(E_U) → Γ(model of c) → Γ(model of k)`. -/
private lemma appLE_comp_app_comp_appLE :
    f.appLE _ _ (opensRange_le_preimage_opensRange hh) ≫ π'.app k.baseMap.opensRange ≫
        (k.modelIso.inv ≫ k.toTotal).appLE _ ⊤ k.top_le_preimage_modelIso_inv_toTotal =
      π.app c.baseMap.opensRange ≫
        (c.modelIso.inv ≫ c.toTotal).appLE _ ⊤ c.top_le_preimage_modelIso_inv_toTotal ≫
          (modelMap hg hh).appTop := by
  have hw : modelMap hg hh ≫ (c.modelIso.inv ≫ c.toTotal) ≫ π =
      (k.modelIso.inv ≫ k.toTotal) ≫ π' ≫ f := by
    rw [← Category.assoc, modelMap_comp_modelIso_inv_toTotal hg hh, Category.assoc, hg.w]
  rw [Scheme.Hom.app_eq_appLE π', ← Category.assoc, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE]
  refine (Scheme.Hom.congr_appLE _ hw.symm _ ⊤ _ (by
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
    exact fun x _ ↦ c.top_le_preimage_modelIso_inv_toTotal
      (show modelMap hg hh x ∈ (⊤ : Opens _) from trivial))).trans ?_
  have r1 := Scheme.Hom.comp_appLE (c.modelIso.inv ≫ c.toTotal) π c.baseMap.opensRange ⊤ (by
    rw [Scheme.Hom.comp_preimage]; exact c.top_le_preimage_modelIso_inv_toTotal)
  have r2 := Scheme.Hom.appLE_comp_appLE (modelMap hg hh) ((c.modelIso.inv ≫ c.toTotal) ≫ π)
    c.baseMap.opensRange ⊤ ⊤ (by
      rw [Scheme.Hom.comp_preimage]; exact c.top_le_preimage_modelIso_inv_toTotal) le_top
  rw [← r2, r1, Category.assoc]
  rfl

/-- The ring map of `g` over the image of the base of `c` is that of `f`, read through the
structure morphisms. -/
private lemma app_comp_appLE :
    π.app c.baseMap.opensRange ≫ g.appLE _ _ (preimage_le_preimage_preimage hg hh) =
      f.appLE _ _ (opensRange_le_preimage_opensRange hh) ≫ π'.app k.baseMap.opensRange := by
  have e1 := Scheme.Hom.comp_appLE g π c.baseMap.opensRange (π' ⁻¹ᵁ k.baseMap.opensRange) (by
    rw [Scheme.Hom.comp_preimage]; exact preimage_le_preimage_preimage hg hh)
  have e2 := Scheme.Hom.appLE_comp_appLE π' f c.baseMap.opensRange k.baseMap.opensRange
    (π' ⁻¹ᵁ k.baseMap.opensRange) (opensRange_le_preimage_opensRange hh) le_rfl
  have e3 := Scheme.Hom.congr_appLE _ hg.w c.baseMap.opensRange (π' ⁻¹ᵁ k.baseMap.opensRange)
    (by rw [Scheme.Hom.comp_preimage]; exact preimage_le_preimage_preimage hg hh)
    (by rw [Scheme.Hom.comp_preimage]
        exact fun x hx ↦ opensRange_le_preimage_opensRange hh hx)
  rw [Scheme.Hom.app_eq_appLE π']
  exact e1.symm.trans (e3.trans e2.symm)

/-- The projective model of the equation of `k` is the base change of that of `c` along the ring
map `c.ring ⟶ k.ring` of the bases, as schemes over the spectra of these rings. -/
private lemma isPullback_modelMap_over :
    letI := (Spec.preimage (k.baseIso.inv ≫ h ≫ c.baseIso.hom)).hom.toAlgebra
    IsPullback (modelMap hg hh) (k.equation.projModel ↘ Spec (.of k.ring))
      (c.equation.projModel ↘ Spec (.of c.ring))
      (Spec.map (CommRingCat.ofHom (algebraMap c.ring k.ring))) := by
  rw [WeierstrassCurve.over_projModel, WeierstrassCurve.over_projModel]
  convert isPullback_modelMap hg hh
  exact Spec.map_preimage _

variable {M : X.Modules} {N : c.equation.projModel.Modules}

/-- Given an identification `θ` of the restriction of `M` to the model of `c` with `N`, the
identification of the restriction of `g^* M` to the model of `k` with the pullback of `N` along
`modelMap hg hh`. -/
private noncomputable def pullbackModelIso (θ : (Scheme.Modules.pullback
      (c.modelIso.inv ≫ c.toTotal)).obj M ≅ N) :
    (Scheme.Modules.pullback (k.modelIso.inv ≫ k.toTotal)).obj
        ((Scheme.Modules.pullback g).obj M) ≅
      (Scheme.Modules.pullback (modelMap hg hh)).obj N :=
  (pullbackComp _ g).app M ≪≫
    (pullbackCongr (modelMap_comp_modelIso_inv_toTotal hg hh).symm).app M ≪≫
      ((pullbackComp (modelMap hg hh) _).app M).symm ≪≫
        (Scheme.Modules.pullback (modelMap hg hh)).mapIso θ

/-- `pullbackModelIso` carries the pullback along `g` of a section over the image of the base
of `c` to the pullback along `modelMap hg hh` of its restriction to the model of `c`. -/
private lemma pullbackModelIso_hom_app_pullbackSectionsLE
    (θ : (Scheme.Modules.pullback (c.modelIso.inv ≫ c.toTotal)).obj M ≅ N)
    (s : Γ(M, π ⁻¹ᵁ c.baseMap.opensRange)) :
    (pullbackModelIso hg hh θ).hom.app ⊤
        ((k.modelIso.inv ≫ k.toTotal).pullbackSectionsLE _ _ ⊤
          k.top_le_preimage_modelIso_inv_toTotal
          (g.pullbackSectionsLE M _ _ (preimage_le_preimage_preimage hg hh) s)) =
      (modelMap hg hh).pullbackSections N ⊤
        (θ.hom.app ⊤ ((c.modelIso.inv ≫ c.toTotal).pullbackSectionsLE M _ ⊤
          c.top_le_preimage_modelIso_inv_toTotal s)) := by
  have hj := c.top_le_preimage_modelIso_inv_toTotal
  have h1 := Scheme.Hom.pullbackSectionsLE_comp_hom g M _ (k.modelIso.inv ≫ k.toTotal) _
    (preimage_le_preimage_preimage hg hh) k.top_le_preimage_modelIso_inv_toTotal s
  have h2 := Scheme.Hom.pullbackSectionsLE_congr ((k.modelIso.inv ≫ k.toTotal) ≫ g) M _ ⊤
    (k.top_le_preimage_modelIso_inv_toTotal.trans
      (Scheme.Hom.preimage_mono _ (preimage_le_preimage_preimage hg hh)))
    (modelMap_comp_modelIso_inv_toTotal hg hh).symm s
  have h3 := Scheme.Hom.pullbackSectionsLE_comp (c.modelIso.inv ≫ c.toTotal) M _
    (modelMap hg hh) ⊤ hj (W := ⊤)
    (fun x _ ↦ show modelMap hg hh x ∈ (⊤ : Opens _) from trivial) s
  have h4 := Scheme.Hom.pullbackSectionsLE_naturality (modelMap hg hh)
    ((Scheme.Modules.pullback (c.modelIso.inv ≫ c.toTotal)).obj M) ⊤ ⊤
    (fun x _ ↦ show modelMap hg hh x ∈ (⊤ : Opens _) from trivial) θ.hom
    ((c.modelIso.inv ≫ c.toTotal).pullbackSectionsLE M _ ⊤ hj s)
  have h5 := Scheme.Hom.pullbackSectionsLE_self (modelMap hg hh) N ⊤
    (θ.hom.app ⊤ ((c.modelIso.inv ≫ c.toTotal).pullbackSectionsLE M _ ⊤ hj s))
  exact ((congrArg (((Scheme.Modules.pullback (modelMap hg hh)).map θ.hom).app ⊤)
    (congrArg (((pullbackComp (modelMap hg hh) _).inv.app M).app ⊤)
      (congrArg (((pullbackCongr (modelMap_comp_modelIso_inv_toTotal hg hh).symm).hom.app M).app
        ⊤) h1 |>.trans h2) |>.trans h3)).trans h4).trans h5

end PointedWeierstrassChart

namespace EllipticCurveGeom

variable {S S' : Scheme.{u}} {E : EllipticCurveGeom S} {E' : EllipticCurveGeom S'}
  {g : E'.carrier ⟶ E.carrier} {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f)
  {k : PointedWeierstrassChart E'.structureMap E'.zero}
  {c : PointedWeierstrassChart E.structureMap E.zero} {h : k.base ⟶ c.base}
  (hh : h ≫ c.baseMap = k.baseMap ≫ f) {M : InvertibleSheaf E.carrier}
  (hM : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ξ : Spec (.of Ω) ⟶ S),
    letI : (Limits.pullback ξ E.structureMap).Over (Spec (.of Ω)) := ⟨Limits.pullback.fst _ _⟩
    0 < LineBundleClass.eulerDegree Ω
      (LineBundleClass.pullback (Limits.pullback.snd ξ E.structureMap) (.mk M)))

include hh hM in
open PointedWeierstrassChart in
/-- **Base change for a line bundle of positive fibre degree over a pair of charts.** Let `k` and
`c` be pointed Weierstrass charts of `E'` and `E` whose bases are related by `h` over `f`, with
image `V` of the base of `k`. For an invertible sheaf `M` on `E` of positive degree on every
geometric fibre, the base change morphism of `π_* M` is bijective on the sections over `V`.
Through the charts this is cohomology and base change for `H⁰` of the restriction of `M` to the
model of `c`. -/
private theorem bijective_pushforwardBaseChange_app_app_of_forall_eulerDegree_pos :
    Function.Bijective (((pushforwardBaseChange hg.toCommSq).app M.obj).app
      k.baseMap.opensRange) := by
  have : M.obj.IsQuasicoherent :=
    inferInstanceAs ((InvertibleSheaf.toFiniteLocallyFree _).obj M).obj.IsQuasicoherent
  let G := modelMap hg hh
  let j := c.modelIso.inv ≫ c.toTotal
  let j' := k.modelIso.inv ≫ k.toTotal
  let U := c.baseMap.opensRange
  let V := k.baseMap.opensRange
  let Uc := E.structureMap ⁻¹ᵁ U
  let V' := E'.structureMap ⁻¹ᵁ V
  have hj := c.top_le_preimage_modelIso_inv_toTotal
  have hj' := k.top_le_preimage_modelIso_inv_toTotal
  have hψ := preimage_le_preimage_preimage hg hh
  -- the model base change square and cohomology and base change for its pole sheaf
  let φ : c.ring ⟶ k.ring := Spec.preimage (k.baseIso.inv ≫ h ≫ c.baseIso.hom)
  let _ : Algebra c.ring k.ring := φ.hom.toAlgebra
  have H : IsPullback G (k.equation.projModel ↘ Spec (.of k.ring))
      (c.equation.projModel ↘ Spec (.of c.ring))
      (Spec.map (CommRingCat.ofHom (algebraMap c.ring k.ring))) := isPullback_modelMap_over hg hh
  have hCBC := WeierstrassCurve.bijective_cohomologyBaseChange_zero_of_forall_eulerDegree_pos
    (eulerDegree_pullback_projModelBaseChange_pos hM c) H
  let θ : (pullback j).obj M.obj ≅ ((InvertibleSheaf.pullback j).obj M).obj := Iso.refl _
  let ℒ := M.obj
  let ℒW := ((InvertibleSheaf.pullback j).obj M).obj
  let Ξ := pullbackModelIso hg hh θ
  -- the rings of the charts are the functions on `U` and `V`
  let A := Γ(S, U)
  let B := Γ(S', V)
  let α : A →+* Γ(c.equation.projModel, ⊤) := (E.structureMap.app U ≫ j.appLE Uc ⊤ hj).hom
  let β : B →+* Γ(k.equation.projModel, ⊤) := (E'.structureMap.app V ≫ j'.appLE V' ⊤ hj').hom
  have hα : Function.Bijective α :=
    (bijective_appLE j (opensRange_modelIso_inv_toTotal c).ge hj (by simp)).comp
      (ConcreteCategory.bijective_of_isIso _)
  have hβ : Function.Bijective β :=
    (bijective_appLE j' (opensRange_modelIso_inv_toTotal k).ge hj' (by simp)).comp
      (ConcreteCategory.bijective_of_isIso _)
  let eR := RingEquiv.ofBijective _ c.equation.bijective_baseRingToGlobalSections
  let eR' := RingEquiv.ofBijective _ k.equation.bijective_baseRingToGlobalSections
  let a : A →+* c.ring := eR.symm.toRingHom.comp α
  let b : B →+* k.ring := eR'.symm.toRingHom.comp β
  let φAB := (f.appLE U V (opensRange_le_preimage_opensRange hh)).hom
  have hab (r : A) : b (φAB r) = φ.hom (a r) := by
    apply eR'.injective
    change eR' (eR'.symm (β (φAB r))) = baseRingToGlobalSections k.ring _ (φ.hom (a r))
    rw [RingEquiv.apply_symm_apply]
    refine Eq.trans ?_ (appTop_baseRingToGlobalSections_of_isPullback H (a r))
    change _ = G.appTop (eR (eR.symm (α r)))
    rw [RingEquiv.apply_symm_apply]
    exact congrArg (fun φ ↦ φ.hom r) (appLE_comp_app_comp_appLE hg hh)
  -- the module structures over `A → B` and `c.ring → k.ring`
  let : Algebra A B := φAB.toAlgebra
  let : Algebra A c.ring := a.toAlgebra
  let : Algebra B k.ring := b.toAlgebra
  let : Algebra A k.ring := (b.comp φAB).toAlgebra
  have : IsScalarTower A B k.ring := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A c.ring k.ring := .of_algebraMap_eq hab
  let M₀ := Cohomology ℒW 0
  let N₀ := Cohomology ((pullback G).obj ℒW) 0
  let : Module A M₀ := Module.compHom M₀ a
  have : IsScalarTower A c.ring M₀ := .of_algebraMap_smul fun _ _ ↦ rfl
  let : Module c.ring N₀ := Module.compHom N₀ φ.hom
  have : IsScalarTower c.ring k.ring N₀ := .of_algebraMap_smul fun _ _ ↦ rfl
  let : Module B N₀ := Module.compHom N₀ b
  have : IsScalarTower B k.ring N₀ := .of_algebraMap_smul fun _ _ ↦ rfl
  let : Module A N₀ := Module.compHom N₀ (b.comp φAB)
  have : IsScalarTower A k.ring N₀ := .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower A B N₀ := .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower A c.ring N₀ := .of_algebraMap_smul fun r x ↦ by
    change φ.hom (a r) • x = b (φAB r) • x
    rw [hab]
  let M := Γ((pushforward E.structureMap).obj ℒ, U)
  let N := Γ((pushforward E'.structureMap).obj ((pullback g).obj ℒ), V)
  let : Module A N := Module.compHom N φAB
  have : IsScalarTower A B N := .of_algebraMap_smul fun _ _ ↦ rfl
  -- the model statement, over `A → B`
  let f₀ : M₀ →ₗ[c.ring] N₀ := (cohomologyBaseChange H ℒW 0).restrictScalars c.ring ∘ₗ
    TensorProduct.mk c.ring k.ring M₀ 1
  have hf₀ : IsBaseChange k.ring f₀ :=
    IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hCBC) fun _ ↦ rfl
  have hB : IsBaseChange B (f₀.restrictScalars A) :=
    IsBaseChange.restrictScalars_of_bijective (eR.symm.bijective.comp hα)
      (eR'.symm.bijective.comp hβ) hf₀
  -- the pullback of sections along `g`
  let ψ : M →ₗ[A] N :=
    { toFun := g.pullbackSectionsLE ℒ Uc V' hψ
      map_add' := map_add _
      map_smul' r s := by
        change g.pullbackSectionsLE ℒ Uc V' hψ
            (E.structureMap.app U r • (show Γ(ℒ, Uc) from s)) =
          E'.structureMap.app V (φAB r) • g.pullbackSectionsLE ℒ Uc V' hψ s
        rw [map_smulₛₗ]
        exact congrArg (· • _) (congrArg (fun φ ↦ φ.hom r) (app_comp_appLE hg hh)) }
  -- the identifications of its source and target with `H⁰` of the models
  have hsm₁ (r : A) (x : M₀) : r • x = α r • x := by
    change baseRingToGlobalSections c.ring c.equation.projModel (eR.symm (α r)) • x = _
    rw [show baseRingToGlobalSections c.ring _ (eR.symm (α r)) = α r from
      eR.apply_symm_apply (α r)]
  have hsm₂ (r : B) (x : N₀) : r • x = β r • x := by
    change baseRingToGlobalSections k.ring k.equation.projModel (eR'.symm (β r)) • x = _
    rw [show baseRingToGlobalSections k.ring _ (eR'.symm (β r)) = β r from
      eR'.apply_symm_apply (β r)]
  let e₁ : M ≃ₗ[A] M₀ :=
    { (AddEquiv.ofBijective (j.pullbackSectionsLE ℒ Uc ⊤ hj).toAddMonoidHom
        (j.bijective_pullbackSectionsLE_of_isOpenImmersion ℒ
          (opensRange_modelIso_inv_toTotal c).ge hj (by simp))).trans
          ((sectionsLinearEquiv θ ⊤).toAddEquiv.trans
            (cohomologyZeroLinearEquiv ℒW).symm.toAddEquiv) with
      map_smul' r s := by
        rw [RingHom.id_apply, hsm₁]
        change (cohomologyZeroLinearEquiv ℒW).symm (sectionsLinearEquiv θ ⊤
          (j.pullbackSectionsLE ℒ Uc ⊤ hj
            (E.structureMap.app U r • (show Γ(ℒ, Uc) from s)))) = _
        rw [map_smulₛₗ, LinearEquiv.map_smul, LinearEquiv.map_smul]
        rfl }
  let e₂ : N ≃ₗ[B] N₀ :=
    { (AddEquiv.ofBijective (j'.pullbackSectionsLE ((pullback g).obj ℒ) V' ⊤ hj').toAddMonoidHom
        (j'.bijective_pullbackSectionsLE_of_isOpenImmersion ((pullback g).obj ℒ)
          (opensRange_modelIso_inv_toTotal k).ge hj' (by simp))).trans
          ((sectionsLinearEquiv Ξ ⊤).toAddEquiv.trans
            (cohomologyZeroLinearEquiv ((pullback G).obj ℒW)).symm.toAddEquiv) with
      map_smul' r x := by
        rw [RingHom.id_apply, hsm₂]
        change (cohomologyZeroLinearEquiv _).symm (sectionsLinearEquiv Ξ ⊤
          (j'.pullbackSectionsLE ((pullback g).obj ℒ) V' ⊤ hj'
            (E'.structureMap.app V r • (show Γ((pullback g).obj ℒ, V') from x)))) = _
        rw [map_smulₛₗ, LinearEquiv.map_smul, LinearEquiv.map_smul]
        rfl }
  have he₁ (s : M) : cohomologyZeroLinearEquiv ℒW (e₁ s) =
      sectionsLinearEquiv θ ⊤ (j.pullbackSectionsLE ℒ Uc ⊤ hj s) :=
    (cohomologyZeroLinearEquiv ℒW).apply_symm_apply _
  have he₂ (x : N) : cohomologyZeroLinearEquiv _ (e₂ x) =
      sectionsLinearEquiv Ξ ⊤ (j'.pullbackSectionsLE _ V' ⊤ hj' x) :=
    (cohomologyZeroLinearEquiv _).apply_symm_apply _
  have hf₀' (x : M₀) : f₀ x = G.cohomologyPullback ℒW 0 x :=
    (cohomologyBaseChange_tmul H ℒW 0 1 x).trans (one_smul _ _)
  have hc (s : M) : f₀ (e₁ s) = e₂ (ψ s) := by
    refine (cohomologyZeroLinearEquiv ((pullback G).obj ℒW)).injective ?_
    rw [he₂, hf₀', cohomologyZeroLinearEquiv_apply,
      Scheme.Hom.cohomologyZeroEquiv_cohomologyPullback, ← cohomologyZeroLinearEquiv_apply, he₁,
      sectionsLinearEquiv_apply, sectionsLinearEquiv_apply]
    exact (pullbackModelIso_hom_app_pullbackSectionsLE hg hh θ s).symm
  have hψB : IsBaseChange B ψ :=
    (IsBaseChange.iff_of_equiv_comm e₁ e₂ (LinearMap.ext hc)).mpr hB
  exact bijective_pushforwardBaseChange_app_app_of_isBaseChange hg.toCommSq ℒ
    (isAffineOpen_opensRange _) (isAffineOpen_opensRange _)
    (opensRange_le_preimage_opensRange hh) rfl ψ (fun _ ↦ rfl) hψB

include hM in
/-- **`π_*M` commutes with base change for a line bundle `M` of positive fibre degree.** Let `E'`
over `S'` be the base change of the elliptic curve `E` over `S` along `f : S' ⟶ S`, with
projection `g : E' ⟶ E`. For an invertible sheaf `M` on `E` of positive degree on every geometric
fibre, the base change morphism `f^* π_* M ⟶ π'_* g^* M` is an isomorphism. -/
theorem isIso_pushforwardBaseChange_app_of_forall_eulerDegree_pos :
    IsIso ((pushforwardBaseChange hg.toCommSq).app M.obj) := by
  -- the pairs of charts of `E'` and `E` whose bases are related over `f`
  let ι := Σ' (k : PointedWeierstrassChart E'.structureMap E'.zero)
    (c : PointedWeierstrassChart E.structureMap E.zero) (h : k.base ⟶ c.base),
    h ≫ c.baseMap = k.baseMap ≫ f
  have hB : Opens.IsBasis (Set.range fun p : ι ↦ p.1.baseMap.opensRange) := by
    refine Opens.isBasis_iff_nbhd.mpr fun {O s} hs ↦ ?_
    obtain ⟨k, c, h, hh, x, rfl⟩ := E.exists_chart_comp_baseMap E' f s
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩ :=
      k.base.isBasis_affineOpens.exists_subset_of_mem_open
        (k.baseMap.mem_preimage.mpr hs) (k.baseMap ⁻¹ᵁ O).isOpen
    -- the image of the restriction of `k` to `W` is the image of `W`
    have hrange (t : S') : t ∈ (k.restrict ⟨W, hW⟩).baseMap.opensRange ↔
        t ∈ k.baseMap '' W := by
      rw [Scheme.Hom.mem_opensRange, ← Set.mem_range, ← PointedWeierstrassChart.restrictι_baseMap,
        Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        PointedWeierstrassChart.range_restrictι]
    refine ⟨_, ⟨⟨k.restrict ⟨W, hW⟩, c, k.restrictι ⟨W, hW⟩ ≫ h, by
      rw [Category.assoc, hh, ← Category.assoc, PointedWeierstrassChart.restrictι_baseMap]⟩, rfl⟩,
      (hrange _).mpr ⟨x, hxW, rfl⟩, fun t ht ↦ ?_⟩
    obtain ⟨y, hy, rfl⟩ := (hrange t).mp ht
    exact hWO hy
  exact Hom.isIso_of_isBasis _ hB fun p ↦ (ConcreteCategory.isIso_iff_bijective _).mpr
    (bijective_pushforwardBaseChange_app_app_of_forall_eulerDegree_pos hg p.2.2.2 hM)


end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
