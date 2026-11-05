/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Abelian.Injective.CartanEilenberg.Basic

/-!
# Morphisms of Cartan–Eilenberg double complexes

A morphism of cochain complexes `φ : K ⟶ K'` maps the short exact sequences
`0 ⟶ Zᵠ ⟶ Kᵠ ⟶ Kᵠ / Zᵠ ⟶ 0` and `0 ⟶ Kᵠ / Zᵠ ⟶ Zᵠ⁺¹ ⟶ Hᵠ⁺¹ ⟶ 0` of `K` to those of `K'`
(`CochainComplex.cyclesShortComplexMap`, `CochainComplex.boundariesShortComplexMap`). Lifting
`φ` on the chosen resolutions of `Z⁰`, of the objects `Kᵠ / Zᵠ` and of the objects `Hᵠ⁺¹`, the
horseshoe lemma for morphisms (`CategoryTheory.InjectiveResolution.horseshoeMap`) gives chain maps
`J(Zᵠ) ⟶ J(Z'ᵠ)` and `J(Kᵠ) ⟶ J(K'ᵠ)` lifting `φ`, which commute with the chain maps of the
horseshoes and hence with the vertical differentials. Together they form a morphism of
Cartan–Eilenberg double complexes `CochainComplex.cartanEilenbergMap φ`, compatible with the
augmentations and with the maps `J(Zᵠ) ⟶ J(Hᵠ)` to the chosen resolutions of the cohomology.

The chain maps `J(Hᵠ) ⟶ J(H'ᵠ)` (`CochainComplex.homologyResolutionMap`) lift `Hᵠ(φ)`
(`CochainComplex.homologyResolution_ι₀_comp_homologyResolutionMap_f`), and after an additive functor
`G` the identifications `cartanEilenbergRowHomologyIso` of the cohomology of the rows of `G(J)`
with `G(J(Hᵠ))` are natural
(`CochainComplex.homologyMap_cartanEilenbergRowMap_cartanEilenbergRowHomologyIso_hom`).

Such a lift is not unique (only up to homotopy), so `CochainComplex.cartanEilenbergMap φ` is one
choice of morphism of Cartan–Eilenberg double complexes lifting `φ`.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Lemma 5.7.2.
-/

@[expose] public section

open CategoryTheory Category Limits

universe v u

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]

@[reassoc (attr := simp)]
lemma ι₀_comp_desc_f_zero {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y)
    (J : InjectiveResolution Z) : J.ι₀ ≫ (desc f I J).f 0 = f ≫ I.ι₀ :=
  desc_commutes_zero f I J

end CategoryTheory.InjectiveResolution

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {K K' : CochainComplex C ℕ} (φ : K ⟶ K')

/-- The map `Kᵠ / Zᵠ ⟶ K'ᵠ / Z'ᵠ` induced by a morphism of cochain complexes. -/
noncomputable def cokernelCyclesMap (q : ℕ) : cokernel (K.iCycles q) ⟶ cokernel (K'.iCycles q) :=
  cokernel.map _ _ (HomologicalComplex.cyclesMap φ q) (φ.f q)
    (HomologicalComplex.cyclesMap_i φ q).symm

@[reassoc (attr := simp)]
lemma π_cokernelCyclesMap (q : ℕ) :
    cokernel.π (K.iCycles q) ≫ cokernelCyclesMap φ q = φ.f q ≫ cokernel.π (K'.iCycles q) :=
  cokernel.π_desc _ _ _

/-- The morphism of short complexes `(Zᵠ ⟶ Kᵠ ⟶ Kᵠ / Zᵠ) ⟶ (Z'ᵠ ⟶ K'ᵠ ⟶ K'ᵠ / Z'ᵠ)` induced by a
morphism of cochain complexes. -/
@[simps]
noncomputable def cyclesShortComplexMap (q : ℕ) :
    K.cyclesShortComplex q ⟶ K'.cyclesShortComplex q where
  τ₁ := HomologicalComplex.cyclesMap φ q
  τ₂ := φ.f q
  τ₃ := cokernelCyclesMap φ q
  comm₁₂ := HomologicalComplex.cyclesMap_i φ q
  comm₂₃ := (π_cokernelCyclesMap φ q).symm

@[reassoc (attr := simp)]
lemma cokernelCyclesToCycles_cyclesMap (q : ℕ) :
    K.cokernelCyclesToCycles q ≫ HomologicalComplex.cyclesMap φ (q + 1) =
      cokernelCyclesMap φ q ≫ K'.cokernelCyclesToCycles q := by
  rw [← cancel_epi (cokernel.π (K.iCycles q)), π_cokernelCyclesToCycles_assoc,
    π_cokernelCyclesMap_assoc, π_cokernelCyclesToCycles, ← cancel_mono (K'.iCycles (q + 1))]
  simp

/-- The morphism of short complexes `(Kᵠ / Zᵠ ⟶ Zᵠ⁺¹ ⟶ Hᵠ⁺¹) ⟶ (K'ᵠ / Z'ᵠ ⟶ Z'ᵠ⁺¹ ⟶ H'ᵠ⁺¹)`
induced by a morphism of cochain complexes. -/
@[simps]
noncomputable def boundariesShortComplexMap (q : ℕ) :
    K.boundariesShortComplex q ⟶ K'.boundariesShortComplex q where
  τ₁ := cokernelCyclesMap φ q
  τ₂ := HomologicalComplex.cyclesMap φ (q + 1)
  τ₃ := HomologicalComplex.homologyMap φ (q + 1)
  comm₁₂ := (cokernelCyclesToCycles_cyclesMap φ q).symm
  comm₂₃ := (HomologicalComplex.homologyπ_naturality φ (q + 1)).symm

variable [HasInjectiveResolutions C]

/-- The chain map `J(Kᵠ / Zᵠ) ⟶ J(K'ᵠ / Z'ᵠ)` between the chosen injective resolutions, lifting
`cokernelCyclesMap φ q`. -/
noncomputable def cokernelCyclesResolutionMap (q : ℕ) :
    (injectiveResolution (cokernel (K.iCycles q))).cocomplex ⟶
      (injectiveResolution (cokernel (K'.iCycles q))).cocomplex :=
  InjectiveResolution.desc (cokernelCyclesMap φ q) _ _

/-- The chain map `J(Zᵠ) ⟶ J(Z'ᵠ)` lifting the map induced by `φ` on cycles: an arbitrary lift
in degree `0`, and in degree `q + 1` the morphism of horseshoes. -/
noncomputable def cyclesResolutionMap : (q : ℕ) →
    (K.cyclesResolution q).cocomplex ⟶ (K'.cyclesResolution q).cocomplex
  | 0 => InjectiveResolution.desc (HomologicalComplex.cyclesMap φ 0) _ _
  | q + 1 => InjectiveResolution.horseshoeMap (K.boundariesShortComplex_shortExact q)
      (K'.boundariesShortComplex_shortExact q) (boundariesShortComplexMap φ q)
      (cokernelCyclesResolutionMap φ q)
      (InjectiveResolution.desc (HomologicalComplex.homologyMap φ (q + 1)) _ _)
      (InjectiveResolution.ι₀_comp_desc_f_zero _ _ _)
      (InjectiveResolution.ι₀_comp_desc_f_zero _ _ _)

@[reassoc (attr := simp)]
lemma cyclesResolution_ι₀_comp_cyclesResolutionMap_f (q : ℕ) :
    (K.cyclesResolution q).ι₀ ≫ (cyclesResolutionMap φ q).f 0 =
      HomologicalComplex.cyclesMap φ q ≫ (K'.cyclesResolution q).ι₀ := by
  cases q with
  | zero => exact InjectiveResolution.ι₀_comp_desc_f_zero _ _ _
  | succ q => exact InjectiveResolution.horseshoe_ι₀_comp_horseshoeMap_f_zero _ _ _ _ _ _ _

/-- The chain map `J(Kᵠ) ⟶ J(K'ᵠ)` between the columns of the Cartan–Eilenberg double complexes
lifting `φ.f q`: the morphism of the horseshoes of `0 ⟶ Zᵠ ⟶ Kᵠ ⟶ Kᵠ / Zᵠ ⟶ 0`. -/
noncomputable def cartanEilenbergResolutionMap (q : ℕ) :
    (K.cartanEilenbergResolution q).cocomplex ⟶ (K'.cartanEilenbergResolution q).cocomplex :=
  InjectiveResolution.horseshoeMap (K.cyclesShortComplex_shortExact q)
    (K'.cyclesShortComplex_shortExact q) (cyclesShortComplexMap φ q) (cyclesResolutionMap φ q)
    (cokernelCyclesResolutionMap φ q) (cyclesResolution_ι₀_comp_cyclesResolutionMap_f φ q)
    (InjectiveResolution.ι₀_comp_desc_f_zero _ _ _)

/-- The chain map `J(Kᵠ) ⟶ J(K'ᵠ)` lifts `φ.f q`. -/
@[reassoc (attr := simp)]
lemma cartanEilenbergResolution_ι₀_comp_cartanEilenbergResolutionMap_f (q : ℕ) :
    (K.cartanEilenbergResolution q).ι₀ ≫ (cartanEilenbergResolutionMap φ q).f 0 =
      φ.f q ≫ (K'.cartanEilenbergResolution q).ι₀ :=
  InjectiveResolution.horseshoe_ι₀_comp_horseshoeMap_f_zero _ _ _ _ _ _ _

@[reassoc (attr := simp)]
lemma cyclesResolutionInl_cartanEilenbergResolutionMap (q : ℕ) :
    K.cyclesResolutionInl q ≫ cartanEilenbergResolutionMap φ q =
      cyclesResolutionMap φ q ≫ K'.cyclesResolutionInl q :=
  InjectiveResolution.horseshoeInl_comp_horseshoeMap _ _ _ _ _ _ _

@[reassoc (attr := simp)]
lemma cartanEilenbergResolutionMap_cartanEilenbergResolutionSnd (q : ℕ) :
    cartanEilenbergResolutionMap φ q ≫ K'.cartanEilenbergResolutionSnd q =
      K.cartanEilenbergResolutionSnd q ≫ cokernelCyclesResolutionMap φ q :=
  InjectiveResolution.horseshoeMap_comp_horseshoeSnd _ _ _ _ _ _ _

@[reassoc (attr := simp)]
lemma cokernelCyclesResolutionInl_cyclesResolutionMap (q : ℕ) :
    K.cokernelCyclesResolutionInl q ≫ cyclesResolutionMap φ (q + 1) =
      cokernelCyclesResolutionMap φ q ≫ K'.cokernelCyclesResolutionInl q :=
  InjectiveResolution.horseshoeInl_comp_horseshoeMap _ _ _ _ _ _ _

/-- The chain maps `J(Kᵠ) ⟶ J(K'ᵠ)` commute with the lifts of the differentials. -/
@[reassoc (attr := simp)]
lemma cartanEilenbergD_cartanEilenbergResolutionMap (q : ℕ) :
    K.cartanEilenbergD q ≫ cartanEilenbergResolutionMap φ (q + 1) =
      cartanEilenbergResolutionMap φ q ≫ K'.cartanEilenbergD q := by
  simp [cartanEilenbergD]

/-- **A morphism of Cartan–Eilenberg double complexes** lifting a morphism `φ : K ⟶ K'` of cochain
complexes: in column `q`, the chain map `J(Kᵠ) ⟶ J(K'ᵠ)` lifting `φ.f q`. -/
noncomputable def cartanEilenbergMap : K.cartanEilenberg ⟶ K'.cartanEilenberg :=
  CochainComplex.ofHom (cartanEilenbergResolutionMap φ) fun q ↦ by
    rw [cartanEilenberg_d, cartanEilenberg_d]
    exact (cartanEilenbergD_cartanEilenbergResolutionMap φ q).symm

lemma cartanEilenbergMap_f (q : ℕ) :
    (cartanEilenbergMap φ).f q = cartanEilenbergResolutionMap φ q := rfl

/-- The chain map `J(Hᵠ) ⟶ J(H'ᵠ)` between the chosen injective resolutions of the cohomology,
lifting the map induced by `φ` in cohomology: `cyclesResolutionMap φ 0` in degree `0`, and an
arbitrary lift in degree `q + 1`, as in the horseshoe defining `cyclesResolutionMap φ (q + 1)`. -/
noncomputable def homologyResolutionMap : (q : ℕ) →
    (K.homologyResolution q).cocomplex ⟶ (K'.homologyResolution q).cocomplex
  | 0 => cyclesResolutionMap φ 0
  | q + 1 => InjectiveResolution.desc (HomologicalComplex.homologyMap φ (q + 1)) _ _

/-- The chain maps `J(Zᵠ) ⟶ J(Hᵠ)` commute with the maps induced by `φ`. -/
@[reassoc (attr := simp)]
lemma cyclesResolutionSnd_homologyResolutionMap (q : ℕ) :
    K.cyclesResolutionSnd q ≫ homologyResolutionMap φ q =
      cyclesResolutionMap φ q ≫ K'.cyclesResolutionSnd q := by
  cases q with
  | zero => exact (id_comp (cyclesResolutionMap φ 0)).trans (comp_id _).symm
  | succ q =>
    exact (InjectiveResolution.horseshoeMap_comp_horseshoeSnd
      (K.boundariesShortComplex_shortExact q) (K'.boundariesShortComplex_shortExact q)
      (boundariesShortComplexMap φ q) _ _ _ _).symm

/-- The augmentation of `J(H⁰)` is that of `J(Z⁰)` through `Z⁰ ≅ H⁰`. -/
lemma homologyResolution_zero_ι₀ (K : CochainComplex C ℕ) :
    (K.homologyResolution 0).ι₀ = K.isoHomologyπ₀.inv ≫ (K.cyclesResolution 0).ι₀ :=
  (K.cyclesResolution 0).ofIso_ι₀ _

/-- The chain map `J(Hᵠ) ⟶ J(H'ᵠ)` lifts the map induced by `φ` in cohomology. -/
@[reassoc (attr := simp)]
lemma homologyResolution_ι₀_comp_homologyResolutionMap_f (q : ℕ) :
    (K.homologyResolution q).ι₀ ≫ (homologyResolutionMap φ q).f 0 =
      HomologicalComplex.homologyMap φ q ≫ (K'.homologyResolution q).ι₀ := by
  cases q with
  | zero =>
    rw [homologyResolution_zero_ι₀, homologyResolution_zero_ι₀]
    exact (assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (cyclesResolution_ι₀_comp_cyclesResolutionMap_f φ 0)).trans
        ((isoHomologyπ₀_inv_naturality_assoc φ _).symm))
  | succ q => exact CategoryTheory.InjectiveResolution.ι₀_comp_desc_f_zero _ _ _

variable {D : Type*} [Category* D] [Abelian D] (G : C ⥤ D) [G.Additive]

/-- The morphism `G(J(Kᵠ)ᵖ) ⟶ G(J(K'ᵠ)ᵖ)` of the rows `p` of the Cartan–Eilenberg double complexes
after `G`, induced by `cartanEilenbergMap φ`. -/
noncomputable abbrev cartanEilenbergRowMap (p : ℕ) :
    K.cartanEilenbergRow G p ⟶ K'.cartanEilenbergRow G p :=
  (G.mapHomologicalComplex _).map
    (((HomologicalComplex₂.flipFunctor C _ _).map (cartanEilenbergMap φ)).f p)

@[reassoc (attr := simp)]
lemma cartanEilenbergRowι_cartanEilenbergRowMap_f (p q : ℕ) :
    K.cartanEilenbergRowι G p q ≫ (cartanEilenbergRowMap φ G p).f q =
      G.map ((cyclesResolutionMap φ q).f p) ≫ K'.cartanEilenbergRowι G p q :=
  (G.map_comp _ _).symm.trans ((congrArg G.map (HomologicalComplex.congr_hom
    (cyclesResolutionInl_cartanEilenbergResolutionMap φ q) p)).trans (G.map_comp _ _))

/-- **The cohomology of the rows of `G(J)` is natural**: under `cartanEilenbergRowHomologyIso`,
the morphism induced by `φ` on the cohomology of the rows of `G(J)` is the image under `G` of the
chain map `J(Hᵠ) ⟶ J(H'ᵠ)`. -/
@[reassoc]
theorem homologyMap_cartanEilenbergRowMap_cartanEilenbergRowHomologyIso_hom (p q : ℕ) :
    HomologicalComplex.homologyMap (cartanEilenbergRowMap φ G p) q ≫
        (K'.cartanEilenbergRowHomologyIso G p q).hom =
      (K.cartanEilenbergRowHomologyIso G p q).hom ≫ G.map ((homologyResolutionMap φ q).f p) := by
  rw [← cancel_epi ((K.cartanEilenbergRow G p).liftCycles (K.cartanEilenbergRowι G p q)
    (q + 1) (CochainComplex.next ℕ q) (K.cartanEilenbergRowι_d G p q) ≫
      (K.cartanEilenbergRow G p).homologyπ q)]
  have h : (K'.cartanEilenbergRow G p).liftCycles (K.cartanEilenbergRowι G p q ≫
        (cartanEilenbergRowMap φ G p).f q) (q + 1) (CochainComplex.next ℕ q) (by
          rw [Category.assoc, (cartanEilenbergRowMap φ G p).comm,
            cartanEilenbergRowι_d_assoc, zero_comp]) =
      G.map ((cyclesResolutionMap φ q).f p) ≫
        (K'.cartanEilenbergRow G p).liftCycles (K'.cartanEilenbergRowι G p q) (q + 1)
          (CochainComplex.next ℕ q) (K'.cartanEilenbergRowι_d G p q) := by
    rw [← cancel_mono ((K'.cartanEilenbergRow G p).iCycles q),
      HomologicalComplex.liftCycles_i, Category.assoc, HomologicalComplex.liftCycles_i,
      cartanEilenbergRowι_cartanEilenbergRowMap_f]
  simp only [Category.assoc, HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc, h,
    liftCycles_homologyπ_cartanEilenbergRowHomologyIso_hom_assoc,
    liftCycles_homologyπ_cartanEilenbergRowHomologyIso_hom]
  rw [← G.map_comp, ← G.map_comp, ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f,
    cyclesResolutionSnd_homologyResolutionMap]

end CochainComplex
