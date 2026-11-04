/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
public import TauCeti.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

/-!
# Thickenings of schemes

A *thickening* of schemes is a closed immersion `i : Z ⟶ X` that is surjective on underlying
points, so that `Z` and `X` have the same underlying space and differ only in their structure
sheaves; equivalently, the ideal sheaf of `i` consists of locally nilpotent sections. A thickening
is *first order* if the square of its ideal sheaf vanishes (Stacks, Definition 37.2.1 (04EX)).
The basic example is `Spec k ⟶ Spec k[ε]`, for the dual numbers `k[ε] = k[x] ⧸ (x²)`.

First-order thickenings are the test objects of infinitesimal deformation theory: formally smooth,
formally unramified and formally étale morphisms are defined by lifting along them, and when a
lift along a first-order thickening with ideal `I` exists, the set of such lifts is a torsor under a
module of homomorphisms into `I`.

## Main definitions

* `TauCeti.AlgebraicGeometry.IsThickening i`: `i` is a closed immersion surjective on points.
* `TauCeti.AlgebraicGeometry.IsFirstOrderThickening i`: `i` is a closed immersion whose ideal
  sheaf has square zero.

## Main results

* `TauCeti.AlgebraicGeometry.isThickening_iff_ker_le_nilradical`: a closed immersion is a
  thickening if and only if its ideal sheaf is contained in the nilradical of the target.
* `TauCeti.AlgebraicGeometry.IsThickening.SpecMap_iff`: for a surjective ring map `φ : R ⟶ S`,
  `Spec S ⟶ Spec R` is a thickening if and only if the kernel of `φ` is a nil ideal.
* `TauCeti.AlgebraicGeometry.IsFirstOrderThickening.SpecMap_iff`: for a surjective ring map
  `φ : R ⟶ S`, `Spec S ⟶ Spec R` is a first-order thickening if and only if the kernel of `φ` has
  square zero.
* Thickenings contain the isomorphisms and are stable under composition and base change;
  first-order thickenings contain the isomorphisms, respect isomorphisms and are stable under base
  change.
* `TauCeti.AlgebraicGeometry.IsFirstOrderThickening.isThickening`: a first-order thickening is a
  thickening, and `TauCeti.AlgebraicGeometry.IsThickening.isUniversalHomeomorphism`: a thickening
  is a universal homeomorphism.
* `TauCeti.AlgebraicGeometry.IsThickening.factor_firstOrder`: a thickening of order `n + 2` (its
  ideal sheaf has vanishing `(n + 3)`-rd power) factors as a thickening of order `n + 1` followed
  by a first-order thickening.
* `TauCeti.AlgebraicGeometry.IsFirstOrderThickening.ker_appTop_mul_self`: a first-order
  thickening of an affine scheme is surjective on global sections with square-zero kernel, so it is
  `Spec` of a square-zero extension; conversely `IsFirstOrderThickening.SpecMap_mk` gives the
  first-order thickening `Spec (B ⧸ I) ⟶ Spec B` of a square-zero ideal `I`.

## References

* [Stacks Project, Definition 37.2.1](https://stacks.math.columbia.edu/tag/04EX).
* [Stacks Project, Lemma 37.2.3](https://stacks.math.columbia.edu/tag/04EZ), base change of
  thickenings.
-/

public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

/-- A morphism of schemes `f : X ⟶ Y` is a *thickening* if it is a closed immersion that is
surjective on underlying points. Then `X` and `Y` have the same underlying space, and the ideal
sheaf of `f` consists of locally nilpotent sections (`isThickening_iff_ker_le_nilradical`).
Stacks, Definition 37.2.1 (04EX). -/
@[stacks 04EX, mk_iff]
class IsThickening (f : X ⟶ Y) : Prop extends IsClosedImmersion f, Surjective f

/-- Thickenings are the closed immersions that are surjective. -/
theorem isThickening_eq :
    @IsThickening.{u} = (@IsClosedImmersion ⊓ @Surjective : MorphismProperty Scheme.{u}) := by
  ext X Y f
  exact isThickening_iff f

/-- A closed immersion is a thickening if and only if its ideal sheaf is contained in the
nilradical of the target, that is, consists of locally nilpotent sections. -/
theorem isThickening_iff_ker_le_nilradical (i : Z ⟶ X) [IsClosedImmersion i] :
    IsThickening i ↔ i.ker ≤ X.nilradical := by
  -- The image of a closed immersion is closed, and it is the support of the ideal sheaf.
  have hrange : (i.ker.support : Set X) = Set.range i := by
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
  -- An ideal sheaf lies in the nilradical exactly when its support is everything.
  have hnil : i.ker ≤ X.nilradical ↔ i.ker.support = ⊤ := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_top,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal, top_le_iff]
  simp [isThickening_iff, surjective_iff, hnil, ← Set.range_eq_univ, ← hrange,
    ‹IsClosedImmersion i›]

namespace IsThickening

-- The instances for `⊓` are not found by instance search through `isThickening_eq`, so they are
-- named explicitly.
instance isMultiplicative : IsMultiplicative @IsThickening.{u} :=
  isThickening_eq ▸ IsMultiplicative.inf

instance isStableUnderComposition : IsStableUnderComposition @IsThickening.{u} :=
  isMultiplicative.toIsStableUnderComposition

instance isStableUnderBaseChange : IsStableUnderBaseChange @IsThickening.{u} :=
  isThickening_eq ▸ IsStableUnderBaseChange.inf

instance respectsIso : RespectsIso @IsThickening.{u} :=
  isThickening_eq ▸ RespectsIso.inf _ _

/-- An isomorphism is a thickening. -/
instance (priority := 100) of_isIso (i : Z ⟶ X) [IsIso i] : IsThickening i where

/-- A composite of thickenings is a thickening. -/
instance comp (i : Z ⟶ Y) (j : Y ⟶ X) [IsThickening i] [IsThickening j] :
    IsThickening (i ≫ j) where

/-- The base change of a thickening is a thickening. -/
instance pullback_fst (f : Y ⟶ X) (i : Z ⟶ X) [IsThickening i] :
    IsThickening (pullback.fst f i) where

/-- The base change of a thickening is a thickening. -/
instance pullback_snd (i : Z ⟶ X) (f : Y ⟶ X) [IsThickening i] :
    IsThickening (pullback.snd i f) where

/-- A thickening is a universal homeomorphism: it is integral and universally injective, as is
every closed immersion, and it is surjective. -/
instance (priority := 100) isUniversalHomeomorphism (i : Z ⟶ X) [IsThickening i] :
    IsUniversalHomeomorphism i :=
  (isUniversalHomeomorphism_iff_isIntegralHom_universallyInjective_surjective i).2
    ⟨inferInstance, inferInstance, inferInstance⟩

/-- For a surjective ring map `φ : R ⟶ S`, the closed immersion `Spec S ⟶ Spec R` is a thickening
if and only if the kernel of `φ` is a nil ideal. -/
theorem SpecMap_iff {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : Function.Surjective φ) :
    IsThickening (Spec.map φ) ↔ RingHom.ker φ.hom ≤ nilradical R := by
  have := IsClosedImmersion.spec_of_surjective φ hφ
  -- On points, `Spec.map φ` is the comap map of prime spectra.
  have hsurj : Surjective (Spec.map φ) ↔ Function.Surjective (PrimeSpectrum.comap φ.hom) := by
    rw [surjective_iff, funext (Spec.map_apply φ)]
    exact Iff.rfl
  rw [isThickening_iff, hsurj, ← Set.range_eq_univ, range_comap_of_surjective _ _ hφ,
    PrimeSpectrum.zeroLocus_eq_univ_iff]
  exact and_iff_right ‹_›

end IsThickening

/-- A morphism of schemes `f : X ⟶ Y` is a *first-order thickening* if it is a closed immersion
whose ideal sheaf `𝓘` satisfies `𝓘 * 𝓘 = 0`. Stacks, Definition 37.2.1 (04EX). -/
@[stacks 04EX, mk_iff]
class IsFirstOrderThickening (f : X ⟶ Y) : Prop extends IsClosedImmersion f where
  /-- The ideal sheaf of a first-order thickening has square zero. -/
  ker_mul_self : f.ker * f.ker = ⊥

namespace IsFirstOrderThickening

/-- A first-order thickening is a thickening: its ideal sheaf has square zero, so it lies in the
nilradical. -/
instance (priority := 100) isThickening (i : Z ⟶ X) [IsFirstOrderThickening i] :
    IsThickening i :=
  (isThickening_iff_ker_le_nilradical i).2 <|
    calc i.ker ≤ i.ker.radical := Scheme.IdealSheafData.le_radical _
      _ = (i.ker * i.ker).radical := by rw [Scheme.IdealSheafData.radical_mul, inf_idem]
      _ = X.nilradical := by rw [ker_mul_self, Scheme.IdealSheafData.radical_bot]

/-- An isomorphism is a first-order thickening. -/
instance (priority := 100) of_isIso (i : Z ⟶ X) [IsIso i] : IsFirstOrderThickening i where
  ker_mul_self := by rw [Scheme.Hom.ker_eq_bot_of_isIso, Scheme.IdealSheafData.bot_mul]

/-- Precomposing a first-order thickening with an isomorphism gives a first-order thickening. -/
instance comp_of_isIso (e : Y ⟶ Z) (i : Z ⟶ X) [IsIso e] [IsFirstOrderThickening i] :
    IsFirstOrderThickening (e ≫ i) where
  ker_mul_self := by rw [Scheme.Hom.ker_comp_of_isIso, ker_mul_self]

/-- The base change of a first-order thickening is a first-order thickening: its ideal sheaf is
the inverse image of the original one, and inverse images of ideal sheaves preserve products. -/
instance pullback_fst (f : Y ⟶ X) (i : Z ⟶ X) [IsFirstOrderThickening i] :
    IsFirstOrderThickening (pullback.fst f i) where
  ker_mul_self := by
    rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      ← Scheme.IdealSheafData.comap_mul, ker_mul_self, Scheme.IdealSheafData.comap_bot]

/-- The base change of a first-order thickening is a first-order thickening. -/
instance pullback_snd (i : Z ⟶ X) (f : Y ⟶ X) [IsFirstOrderThickening i] :
    IsFirstOrderThickening (pullback.snd i f) := by
  rw [← pullbackSymmetry_hom_comp_fst]
  infer_instance

/-- Postcomposing a first-order thickening with an isomorphism gives a first-order thickening. -/
instance comp_of_isIso_right (i : Z ⟶ Y) (e : Y ⟶ X) [IsFirstOrderThickening i] [IsIso e] :
    IsFirstOrderThickening (i ≫ e) := by
  -- Up to an isomorphism of sources, `i ≫ e` is the base change of `i` along `inv e`.
  rw [← IsIso.inv_hom_id_assoc (pullback.snd (inv e) i) (i ≫ e), ← pullback.condition_assoc,
    IsIso.inv_hom_id, Category.comp_id]
  infer_instance

/-- First-order thickenings are stable under composition with isomorphisms on either side. -/
instance respectsIso : RespectsIso @IsFirstOrderThickening.{u} :=
  RespectsIso.mk _ (fun e i _ ↦ comp_of_isIso e.hom i) (fun e i _ ↦ comp_of_isIso_right i e.hom)

/-- First-order thickenings are stable under base change along arbitrary pullback squares. -/
instance isStableUnderBaseChange : IsStableUnderBaseChange @IsFirstOrderThickening.{u} :=
  IsStableUnderBaseChange.mk' fun _ _ _ f i _ _ ↦ pullback_fst f i

/-- For a surjective ring map `φ : R ⟶ S`, the closed immersion `Spec S ⟶ Spec R` is a first-order
thickening if and only if the kernel of `φ` has square zero. -/
theorem SpecMap_iff {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : Function.Surjective φ) :
    IsFirstOrderThickening (Spec.map φ) ↔ RingHom.ker φ.hom * RingHom.ker φ.hom = ⊥ := by
  have := IsClosedImmersion.spec_of_surjective φ hφ
  -- The ideal sheaf of `Spec.map φ` is generated by the kernel of `φ`, read in `Γ(Spec R, ⊤)`.
  have hker : (Spec.map φ).ker * (Spec.map φ).ker = ⊥ ↔
      RingHom.ker φ.hom * RingHom.ker φ.hom = ⊥ := by
    rw [Scheme.Hom.ker_Spec_map, ← Scheme.IdealSheafData.ofIdealTop_mul, ← Ideal.map_mul,
      Scheme.IdealSheafData.ofIdealTop_eq_bot_iff, Ideal.map_eq_bot_iff_of_injective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).1]
  exact ⟨fun h ↦ hker.1 h.ker_mul_self, fun h ↦ ⟨hker.2 h⟩⟩

/-- The ideal sheaf of a first-order thickening is nilpotent. -/
theorem isNilpotent_ker (i : Z ⟶ X) [IsFirstOrderThickening i] : IsNilpotent i.ker :=
  ⟨2, (pow_two _).trans ker_mul_self⟩

/-- A first-order thickening of an affine scheme is surjective on global sections. -/
theorem appTop_surjective (i : Z ⟶ X) [IsAffine X] [IsFirstOrderThickening i] :
    Function.Surjective i.appTop :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine i).2

/-- The map on global sections of a first-order thickening of an affine scheme has square-zero
kernel. -/
theorem ker_appTop_mul_self (i : Z ⟶ X) [IsAffine X] [IsFirstOrderThickening i] :
    RingHom.ker i.appTop.hom * RingHom.ker i.appTop.hom = ⊥ := by
  have := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  -- Up to the isomorphisms `Z ≅ Spec Γ(Z, ⊤)` and `X ≅ Spec Γ(X, ⊤)`, `i` is `Spec.map i.appTop`.
  have hi : Spec.map i.appTop = Z.isoSpec.inv ≫ i ≫ X.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
  have : IsFirstOrderThickening (Spec.map i.appTop) := by
    rw [hi]
    infer_instance
  exact (SpecMap_iff _ (appTop_surjective i)).1 this

/-- For a square-zero ideal `I` of `B`, the closed immersion `Spec (B ⧸ I) ⟶ Spec B` is a
first-order thickening. -/
theorem SpecMap_mk {B : Type u} [CommRing B] (I : Ideal B) (hI : I ^ 2 = ⊥) :
    IsFirstOrderThickening (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  (SpecMap_iff _ Ideal.Quotient.mk_surjective).2 (by
    rw [CommRingCat.hom_ofHom, Ideal.mk_ker, ← pow_two, hI])

end IsFirstOrderThickening

open Scheme.IdealSheafData in
/-- A closed immersion `i` whose ideal sheaf `𝓘` satisfies `𝓘 ^ (n + 3) = 0`, a thickening of order
`n + 2`, factors through the closed subscheme cut out by `𝓘 ^ (n + 2)`: as a closed immersion whose
ideal sheaf has vanishing `(n + 2)`-nd power, a thickening of order `n + 1`, followed by a
first-order thickening. -/
theorem IsThickening.factor_firstOrder (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ)
    (hi : i.ker ^ (n + 3) = ⊥) :
    ∃ (Y : Scheme.{u}) (j : Z ⟶ Y) (k : Y ⟶ X), j ≫ k = i ∧ IsClosedImmersion j ∧
      j.ker ^ (n + 2) = ⊥ ∧ IsFirstOrderThickening k := by
  have hle : i.ker ^ (n + 2) ≤ i.ker := pow_le_of_le_one zero_le le_top (by omega)
  let k := (i.ker ^ (n + 2)).subschemeι
  let j : Z ⟶ (i.ker ^ (n + 2)).subscheme := i.toImage ≫ inclusion hle
  have hjk : j ≫ k = i := by
    simp only [j, k, Category.assoc, inclusion_subschemeι]
    exact i.toImage_imageι
  have : IsClosedImmersion (j ≫ k) := by
    rw [hjk]
    infer_instance
  have : IsClosedImmersion j := IsClosedImmersion.of_comp_isClosedImmersion j k
  -- Since `k` is a monomorphism, `j` is the base change of `i` along `k`, so its ideal sheaf is the
  -- inverse image of that of `i`.
  let φ : Z ⟶ pullback k i := pullback.lift j (𝟙 Z) (by simp [hjk])
  have hφ : φ ≫ pullback.fst k i = j := pullback.lift_fst _ _ _
  have : IsIso φ := ⟨⟨pullback.snd k i, pullback.lift_snd _ _ _, pullback.hom_ext (by
    rw [Category.assoc, hφ, Category.id_comp, ← cancel_mono k, Category.assoc, hjk,
      pullback.condition]) (by simp [φ])⟩⟩
  have hj : j.ker = i.ker.comap k := by
    rw [← ker_fst_of_isClosedImmersion, ← Scheme.Hom.ker_comp_of_isIso φ, hφ]
  refine ⟨_, j, k, hjk, inferInstance, ?_, ⟨?_⟩⟩
  · -- The inverse image along `k` of its own ideal sheaf vanishes.
    rw [hj, ← comap_pow]
    refine le_bot_iff.1 (le_map_iff_comap_le.1 ?_)
    rw [Scheme.IdealSheafData.map_bot, ker_subschemeι]
  · rw [ker_subschemeι, ← pow_add]
    exact le_bot_iff.1 (hi ▸ pow_le_pow_of_le_one zero_le le_top (by omega))

end TauCeti.AlgebraicGeometry
