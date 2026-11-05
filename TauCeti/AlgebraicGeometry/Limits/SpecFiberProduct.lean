/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import TauCeti.AlgebraicGeometry.Limits.QuasiAffine
public import TauCeti.RingTheory.Localization.Away.Pullback

/-!
# Quasi-affine models of an open as opens of the spectrum of a fibre product

Let `V` be a quasi-compact open of a quasi-compact quasi-separated scheme `X` (in the application,
`X = Spec R` is affine) and let `φ : V ⟶ Y` be a morphism to a quasi-compact quasi-separated
scheme `Y` (in the application, a quasi-affine model of `V` of finite type over `ℤ`, one member of
a cofiltered system with limit `V`). Write `P = Γ(X, ⊤) ×_{Γ(X, V)} Γ(Y, ⊤)` for the fibre product
of the restriction `Γ(X, ⊤) → Γ(X, V)` and of `φ^*`, Mathlib's `CommRingCat.pullbackCone`.
Suppose `Y` is covered by affine basic opens `D(b k)`, where each `φ^* (b k)` is the restriction
of some `g k : Γ(X, ⊤)` with `D(g k) ⊆ V`. Then `Y` is an open subscheme of `Spec P` whose preimage
in `X` is `V`; and, `Y` being of finite type over `ℤ`, the same holds for `Spec A` for every subring
`A ⊆ P` containing a suitable finite set (Stacks, Lemma 32.5.1 (01Z7)). This is the single-stage
step of Stacks, Lemma 32.5.2 (01Z9): it extends a model of `V` to a model of `X`.

The key input is that, for `V ≤ W` quasi-compact with `W` quasi-separated and `r : Γ(X, W)` with
`D(r) ⊆ V`, the restriction `Γ(X, W) → Γ(X, V)` becomes bijective after inverting `r` (both
sides are `Γ(X, D(r))` by the qcqs lemma), so that `P` localized away from `(g k, b k)` is
`Γ(Y, ⊤)_{b k} = Γ(Y, D(b k))` by `TauCeti.isLocalization_away_eqLocus_of_bijective_awayMap`.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.bijective_awayMap_presheaf_map_of_basicOpen_le`: the
  restriction `Γ(X, W)_r → Γ(X, V)_{r|V}` is bijective.
* `TauCeti.AlgebraicGeometry.Scheme.isLocalization_away_eqLocus_of_basicOpen_le`: the fibre
  product `Γ(X, W) ×_{Γ(X, V)} A` localized away from `(r, b)` is `A_b`.
* `TauCeti.AlgebraicGeometry.Scheme.isOpenImmersion_toSpecΓ_comp_SpecMap_pullbackCone_snd`: `Y`
  is an open subscheme of `Spec P`.
* `TauCeti.AlgebraicGeometry.Scheme.mem_range_toSpecΓ_comp_SpecMap_pullbackCone_snd`: the basic
  open of `(g k, b k)` in `Spec P` is contained in the image of `Y`.
* `TauCeti.AlgebraicGeometry.Scheme.opensRange_toSpecΓ_comp_SpecMap_eq_iSup`: the image of an
  open immersion `Y ⟶ Spec A` covered by such basic opens is their union.
* `TauCeti.AlgebraicGeometry.Scheme.isPullback_toSpecΓ_comp_SpecMap`: if `Y` is open in `Spec A`
  for a ring `A` mapping compatibly to `Γ(X, ⊤)` and `Γ(Y, ⊤)`, its preimage in `X` is `V`.
* `TauCeti.AlgebraicGeometry.Scheme.exists_finset_isPullback_toSpecΓ_comp_SpecMap`: the same for
  every subring of `P` containing a finite set, if `Y` is locally of finite type over `ℤ`; the
  image of `Y` in `Spec A` is then the union of the basic opens of the `(g k, b k)`, so that it
  pulls back to the image of the corresponding model under any compatible ring map.
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry TopCat.Presheaf

namespace TauCeti.AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {V W : X.Opens}

/-- For quasi-compact opens `V ≤ W` of a scheme, with `W` quasi-separated, and `r : Γ(X, W)` with
`D(r) ⊆ V`, the restriction `Γ(X, W) → Γ(X, V)` becomes bijective after inverting `r`. -/
theorem bijective_awayMap_presheaf_map_of_basicOpen_le (hVW : V ≤ W)
    (hV : IsCompact (V : Set X)) (hW : IsCompact (W : Set X))
    (hW' : IsQuasiSeparated (W : Set X)) {r : Γ(X, W)} (hr : X.basicOpen r ≤ V) :
    Function.Bijective (Localization.awayMap (X.presheaf.map (homOfLE hVW).op).hom r) := by
  have hres (a : Γ(X, W)) : (X.presheaf.map (homOfLE hVW).op).hom a = a |_ V := rfl
  have hρ : X.basicOpen ((X.presheaf.map (homOfLE hVW).op).hom r) = X.basicOpen r := by
    rw [X.basicOpen_res]
    exact inf_eq_right.mpr hr
  constructor
  · refine Localization.awayMap_injective_iff.mpr fun a ha ↦
      exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hW a r ?_
    rw [hres] at ha
    rw [← restrict_restrict hr hVW, ha]
    exact map_zero _
  · refine Localization.awayMap_surjective_iff.mpr fun c ↦ ?_
    obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X W hW hW' r
      (restrictOpen c (X.basicOpen r) hr)
    obtain ⟨k, hk⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hV
      ((X.presheaf.map (homOfLE hVW).op).hom y -
        (X.presheaf.map (homOfLE hVW).op).hom r ^ n * c)
      ((X.presheaf.map (homOfLE hVW).op).hom r) (by
        rw [← restrict_restrict hρ.le hr]
        have key : restrictOpen ((X.presheaf.map (homOfLE hVW).op).hom y -
            (X.presheaf.map (homOfLE hVW).op).hom r ^ n * c) (X.basicOpen r) hr = 0 := by
          have h₁ (a : Γ(X, W)) : (X.presheaf.map (homOfLE hr).op).hom
              ((X.presheaf.map (homOfLE hVW).op).hom a) = a |_ X.basicOpen r :=
            restrict_restrict hr hVW a
          change (X.presheaf.map (homOfLE hr).op).hom _ = 0
          rw [map_sub, map_mul, map_pow, sub_eq_zero, h₁, h₁]
          exact hy
        rw [key]
        exact map_zero _)
    refine ⟨r ^ k * y, k + n, ?_⟩
    rw [← sub_eq_zero, map_mul, map_pow, pow_add, mul_assoc, ← mul_sub, hk]

/-- For quasi-compact opens `V ≤ W` of a scheme, with `W` quasi-separated, a ring map
`h : A →+* Γ(X, V)` and `x = (r, b)` in the fibre product `Γ(X, W) ×_{Γ(X, V)} A` with
`D(r) ⊆ V`, every localization of `A` away from `b` is, through the second projection, the
localization of the fibre product away from `x`. Part of Stacks, Lemma 32.5.2 (01Z9). -/
theorem isLocalization_away_eqLocus_of_basicOpen_le (hVW : V ≤ W)
    (hV : IsCompact (V : Set X)) (hW : IsCompact (W : Set X))
    (hW' : IsQuasiSeparated (W : Set X)) {A : Type*} [CommRing A] {h : A →+* Γ(X, V)}
    (x : (((X.presheaf.map (homOfLE hVW).op).hom).comp (RingHom.fst Γ(X, W) A)).eqLocus
      (h.comp (RingHom.snd Γ(X, W) A)))
    (hx : X.basicOpen x.1.1 ≤ V) (B : Type*) [CommRing B] [Algebra A B]
    [IsLocalization.Away x.1.2 B]
    [Algebra ((((X.presheaf.map (homOfLE hVW).op).hom).comp (RingHom.fst Γ(X, W) A)).eqLocus
      (h.comp (RingHom.snd Γ(X, W) A))) B]
    (hB : algebraMap _ B = (algebraMap A B).comp ((RingHom.snd Γ(X, W) A).comp
      ((((X.presheaf.map (homOfLE hVW).op).hom).comp (RingHom.fst Γ(X, W) A)).eqLocus
        (h.comp (RingHom.snd Γ(X, W) A))).subtype)) :
    IsLocalization.Away x B :=
  isLocalization_away_eqLocus_of_bijective_awayMap x
    (bijective_awayMap_presheaf_map_of_basicOpen_le hVW hV hW hW' hx) B hB

/-- Let `V` be a quasi-compact open of a quasi-compact quasi-separated scheme `X`, and
`h : Γ(Y, ⊤) ⟶ Γ(X, V)` a ring map from the global sections of a quasi-compact quasi-separated
scheme `Y`. Suppose `Y` is covered by affine basic opens `D(b k)`, where each `h (b k)` is the
restriction of some `g k : Γ(X, ⊤)` with `D(g k) ⊆ V`. Then `Y` is an open subscheme of the
spectrum of the fibre product `Γ(X, ⊤) ×_{Γ(X, V)} Γ(Y, ⊤)`, through its second projection.
Part of Stacks, Lemma 32.5.2 (01Z9). -/
theorem isOpenImmersion_toSpecΓ_comp_SpecMap_pullbackCone_snd [CompactSpace X]
    [QuasiSeparatedSpace X] (hV : IsCompact (V : Set X)) {Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] (h : Γ(Y, ⊤) ⟶ Γ(X, V)) {ι : Type*} (g : ι → Γ(X, ⊤))
    (b : ι → Γ(Y, ⊤)) (hgb : ∀ k, h (b k) = X.presheaf.map (homOfLE le_top).op (g k))
    (hg : ∀ k, X.basicOpen (g k) ≤ V) (hb : ∀ k, IsAffineOpen (Y.basicOpen (b k)))
    (hY : ⨆ k, Y.basicOpen (b k) = ⊤) :
    IsOpenImmersion (Y.toSpecΓ ≫
      Spec.map (CommRingCat.pullbackCone (X.presheaf.map (homOfLE le_top).op) h).snd) := by
  let x (k : ι) : ((X.presheaf.map (homOfLE (le_top (a := V))).op).hom.comp
      (RingHom.fst Γ(X, ⊤) Γ(Y, ⊤))).eqLocus (h.hom.comp (RingHom.snd Γ(X, ⊤) Γ(Y, ⊤))) :=
    ⟨(g k, b k), (hgb k).symm⟩
  let xc (k : ι) : (CommRingCat.pullbackCone (X.presheaf.map (homOfLE le_top).op) h).pt := x k
  have hpre (k : ι) : (Y.toSpecΓ ≫ Spec.map
      (CommRingCat.pullbackCone (X.presheaf.map (homOfLE le_top).op) h).snd) ⁻¹ᵁ
        PrimeSpectrum.basicOpen (xc k) = Y.basicOpen (b k) :=
    Y.toSpecΓ_preimage_basicOpen (b k)
  have hloc (k : ι) : IsOpenImmersion ((Y.basicOpen (b k)).ι ≫ Y.toSpecΓ ≫
      Spec.map (CommRingCat.pullbackCone (X.presheaf.map (homOfLE le_top).op) h).snd) := by
    rw [← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top, Category.assoc,
      ← Spec.map_comp]
    let _ : Algebra (((X.presheaf.map (homOfLE (le_top (a := V))).op).hom.comp
        (RingHom.fst Γ(X, ⊤) Γ(Y, ⊤))).eqLocus (h.hom.comp (RingHom.snd Γ(X, ⊤) Γ(Y, ⊤))))
        Γ(Y, Y.basicOpen (b k)) :=
      ((CommRingCat.pullbackCone (X.presheaf.map (homOfLE le_top).op) h).snd ≫
        Y.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    have : IsLocalization.Away (x k).1.2 Γ(Y, Y.basicOpen (b k)) :=
      isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ (b k)
    have : IsLocalization.Away (x k) Γ(Y, Y.basicOpen (b k)) :=
      isLocalization_away_eqLocus_of_basicOpen_le le_top hV isCompact_univ
        isQuasiSeparated_univ (x k) (hg k) _ rfl
    exact MorphismProperty.comp_mem _ (hb k).isoSpec.hom _ inferInstance
      (IsOpenImmersion.of_isLocalization (S := Γ(Y, Y.basicOpen (b k))) (x k))
  refine IsZariskiLocalAtTarget.of_forall_source_exists_preimage _ fun y ↦ ?_
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp (hY.ge (Set.mem_univ y))
  refine ⟨PrimeSpectrum.basicOpen (xc k), (hpre k).ge hk, ?_⟩
  rw [← Y.isoOfEq_hom_ι (hpre k), Category.assoc]
  exact MorphismProperty.comp_mem _ _ _ inferInstance (hloc k)

/-- Let `V` be a quasi-compact open of a quasi-compact quasi-separated scheme `X`, and
`h : Γ(Y, ⊤) ⟶ Γ(X, V)` a ring map from the global sections of a quasi-compact quasi-separated
scheme `Y`. If `x = (g, b)` in the fibre product `P = Γ(X, ⊤) ×_{Γ(X, V)} Γ(Y, ⊤)` has
`D(g) ⊆ V` and `D(b)` affine, then the basic open `D(x) ⊆ Spec P` lies in the image of
`Y ⟶ Spec P`: it is the image of `D(b)`. Part of Stacks, Lemma 32.5.2 (01Z9). -/
theorem mem_range_toSpecΓ_comp_SpecMap_pullbackCone_snd [CompactSpace X]
    [QuasiSeparatedSpace X] (hV : IsCompact (V : Set X)) {Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] (h : Γ(Y, ⊤) ⟶ Γ(X, V)) (g : Γ(X, ⊤)) (b : Γ(Y, ⊤))
    (hgb : h b = X.presheaf.map (homOfLE le_top).op g) (hg : X.basicOpen g ≤ V)
    (hb : IsAffineOpen (Y.basicOpen b))
    (p : PrimeSpectrum (CommRingCat.pullbackCone (X.presheaf.map (homOfLE le_top).op) h).pt)
    (hp : (⟨(g, b), hgb.symm⟩ : ((X.presheaf.map (homOfLE le_top).op).hom.comp
      (RingHom.fst Γ(X, ⊤) Γ(Y, ⊤))).eqLocus (h.hom.comp (RingHom.snd Γ(X, ⊤) Γ(Y, ⊤)))) ∉
        p.asIdeal) :
    p ∈ Set.range (Y.toSpecΓ ≫
      Spec.map (CommRingCat.pullbackCone (X.presheaf.map (homOfLE le_top).op) h).snd) := by
  let c := CommRingCat.pullbackCone (X.presheaf.map (homOfLE (le_top (a := V))).op) h
  let x : ((X.presheaf.map (homOfLE (le_top (a := V))).op).hom.comp
      (RingHom.fst Γ(X, ⊤) Γ(Y, ⊤))).eqLocus (h.hom.comp (RingHom.snd Γ(X, ⊤) Γ(Y, ⊤))) :=
    ⟨(g, b), hgb.symm⟩
  let xc : c.pt := x
  let _ : Algebra (((X.presheaf.map (homOfLE (le_top (a := V))).op).hom.comp
      (RingHom.fst Γ(X, ⊤) Γ(Y, ⊤))).eqLocus (h.hom.comp (RingHom.snd Γ(X, ⊤) Γ(Y, ⊤))))
      Γ(Y, Y.basicOpen b) :=
    (c.snd ≫ Y.presheaf.map (homOfLE le_top).op).hom.toAlgebra
  have : IsLocalization.Away x.1.2 Γ(Y, Y.basicOpen b) :=
    isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ b
  have : IsLocalization.Away x Γ(Y, Y.basicOpen b) :=
    isLocalization_away_eqLocus_of_basicOpen_le le_top hV isCompact_univ
      isQuasiSeparated_univ x hg _ rfl
  obtain ⟨q, rfl⟩ := (PrimeSpectrum.localization_away_comap_range Γ(Y, Y.basicOpen b) x).ge
    ((PrimeSpectrum.mem_basicOpen xc p).mpr hp)
  refine ⟨(Y.basicOpen b).ι (hb.isoSpec.inv q), ?_⟩
  have H : (Y.basicOpen b).ι ≫ Y.toSpecΓ ≫ Spec.map c.snd =
      hb.isoSpec.hom ≫ Spec.map (c.snd ≫ Y.presheaf.map (homOfLE le_top).op) := by
    rw [← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top, Category.assoc,
      ← Spec.map_comp, IsAffineOpen.isoSpec_hom]
  rw [← Scheme.Hom.comp_apply, H]
  change (hb.isoSpec.inv ≫ hb.isoSpec.hom ≫
    Spec.map (c.snd ≫ Y.presheaf.map (homOfLE le_top).op)) q = _
  rw [Iso.inv_hom_id_assoc]
  rfl

/-- Let `V` be an open of a scheme `X` and `φ : V ⟶ Y` a morphism of schemes. Let `α`, `β` map a
ring `A` to the global sections of `X` and `Y`, compatibly over `Γ(X, V)`, such that
`Y ⟶ Spec Γ(Y, ⊤) ⟶ Spec A` is an open immersion. Suppose `Y` is covered by basic opens
`D(β (a k))` with `D(α (a k)) ⊆ V`. Then `V` is the preimage of `Y` in `X`: the square
`V ⟶ Y ⟶ Spec A`, `V ⟶ X ⟶ Spec A` is a pullback. With
`isOpenImmersion_toSpecΓ_comp_SpecMap_pullbackCone_snd` this applies to the fibre product
`A = Γ(X, ⊤) ×_{Γ(X, V)} Γ(Y, ⊤)`, and then to its subrings containing the `a k` along which
`Y` stays open (Stacks, Lemma 32.5.1 (01Z7)). Part of Stacks, Lemma 32.5.2 (01Z9). -/
theorem isPullback_toSpecΓ_comp_SpecMap {Y : Scheme.{u}} (φ : V.toScheme ⟶ Y)
    {A : CommRingCat.{u}} (α : A ⟶ Γ(X, ⊤)) (β : A ⟶ Γ(Y, ⊤))
    (hαβ : α ≫ X.presheaf.map (homOfLE le_top).op = β ≫ φ.appTop ≫ V.topIso.hom)
    [IsOpenImmersion (Y.toSpecΓ ≫ Spec.map β)] {ι : Type*} (a : ι → A)
    (hα : ∀ k, X.basicOpen (α (a k)) ≤ V) (hβ : ⨆ k, Y.basicOpen (β (a k)) = ⊤) :
    IsPullback φ V.ι (Y.toSpecΓ ≫ Spec.map β) (X.toSpecΓ ≫ Spec.map α) := by
  have H : V.ι ≫ X.toSpecΓ ≫ Spec.map α = φ ≫ Y.toSpecΓ ≫ Spec.map β := by
    rw [Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp,
      ← Spec.map_comp]
    congr 2
    have hι : V.ι.appTop = X.presheaf.map (homOfLE le_top).op ≫ V.topIso.inv := by
      rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
      exact (X.presheaf.map_comp _ _).trans rfl
    rw [hι, reassoc_of% hαβ, Iso.hom_inv_id, Category.comp_id]
  refine IsOpenImmersion.isPullback φ V.ι _ _ H (le_antisymm (fun p hp ↦ ?_) ?_)
  · obtain ⟨y, hy⟩ := hp
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp (hβ.ge (Set.mem_univ y))
    have hk' : (Y.toSpecΓ ≫ Spec.map β) y ∈ PrimeSpectrum.basicOpen (a k) :=
      (Y.toSpecΓ_preimage_basicOpen (β (a k))).ge hk
    rw [hy] at hk'
    rw [Scheme.Opens.opensRange_ι]
    exact hα k ((X.toSpecΓ_preimage_basicOpen (α (a k))).le hk')
  · rw [Scheme.Opens.opensRange_ι]
    intro p hp
    exact ⟨φ ⟨p, hp⟩, congr($H ⟨p, hp⟩).symm⟩

/-- Let `β : A ⟶ Γ(Y, ⊤)` be a ring map along which `Y ⟶ Spec A` is an open immersion, and let
`Y` be covered by the basic opens `D(β (a k))`. If each `D(a k) ⊆ Spec A` lies in the image of
`Y`, then this image is the union of the `D(a k)`. -/
theorem opensRange_toSpecΓ_comp_SpecMap_eq_iSup {Y : Scheme.{u}} {A : CommRingCat.{u}}
    (β : A ⟶ Γ(Y, ⊤)) [IsOpenImmersion (Y.toSpecΓ ≫ Spec.map β)] {ι : Type*} (a : ι → A)
    (hY : ⨆ k, Y.basicOpen (β (a k)) = ⊤)
    (ha : ∀ k, ∀ p : Spec A, a k ∉ p.asIdeal → p ∈ Set.range (Y.toSpecΓ ≫ Spec.map β)) :
    (Y.toSpecΓ ≫ Spec.map β).opensRange = ⨆ k, PrimeSpectrum.basicOpen (a k) := by
  refine le_antisymm ?_ (iSup_le fun k p hp ↦ ha k p hp)
  rintro _ ⟨y, rfl⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp (hY.ge (Set.mem_univ y))
  have hpre : (Y.toSpecΓ ≫ Spec.map β) ⁻¹ᵁ PrimeSpectrum.basicOpen (a k) =
      Y.basicOpen (β (a k)) :=
    Y.toSpecΓ_preimage_basicOpen _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hpre.ge hk⟩

/-- Let `V` be a quasi-compact open of a quasi-compact quasi-separated scheme `X`, and
`φ : V ⟶ Y` a morphism to a quasi-compact quasi-separated scheme `Y` locally of finite type over
`ℤ`. Suppose `Y` is covered by finitely many affine basic opens `D(b k)`, where each `φ^* (b k)`
is the restriction of some `g k : Γ(X, ⊤)` with `D(g k) ⊆ V`. Then there is a finite subset `s`
of `P = Γ(X, ⊤) ×_{Γ(X, V)} Γ(Y, ⊤)` such that for every subring `A ⊆ P` containing `s`, `Y` is
an open subscheme of `Spec A` whose preimage in `X` is `V`. Taking `A = ℤ[s]`, `Y` is an open
of the spectrum of a finitely generated `ℤ`-algebra mapping to `Γ(X, ⊤)`, with preimage `V`.
Moreover, the image of `Y` in `Spec A` is the union of the basic opens of the `(g k, b k)`, so it
is compatible with the maps between such rings `A`.
Part of Stacks, Lemma 32.5.2 (01Z9). -/
theorem exists_finset_isPullback_toSpecΓ_comp_SpecMap [CompactSpace X] [QuasiSeparatedSpace X]
    (hV : IsCompact (V : Set X)) {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    [LocallyOfFiniteType (terminal.from Y)] (φ : V.toScheme ⟶ Y) {ι : Type*} [Finite ι]
    (g : ι → Γ(X, ⊤)) (b : ι → Γ(Y, ⊤))
    (hgb : ∀ k, (φ.appTop ≫ V.topIso.hom) (b k) = X.presheaf.map (homOfLE le_top).op (g k))
    (hg : ∀ k, X.basicOpen (g k) ≤ V) (hb : ∀ k, IsAffineOpen (Y.basicOpen (b k)))
    (hY : ⨆ k, Y.basicOpen (b k) = ⊤) :
    ∃ s : Finset (CommRingCat.pullbackCone (X.presheaf.map (homOfLE le_top).op)
        (φ.appTop ≫ V.topIso.hom)).pt,
      ∀ A : Subalgebra ℤ (CommRingCat.pullbackCone (X.presheaf.map (homOfLE le_top).op)
        (φ.appTop ≫ V.topIso.hom)).pt,
      (s : Set (CommRingCat.pullbackCone (X.presheaf.map (homOfLE le_top).op)
        (φ.appTop ≫ V.topIso.hom)).pt) ⊆ A →
      ∃ _ : IsOpenImmersion (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom A.val.toRingHom ≫
        (CommRingCat.pullbackCone (X.presheaf.map (homOfLE le_top).op)
          (φ.appTop ≫ V.topIso.hom)).snd)),
      IsPullback φ V.ι
        (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom A.val.toRingHom ≫
          (CommRingCat.pullbackCone (X.presheaf.map (homOfLE le_top).op)
            (φ.appTop ≫ V.topIso.hom)).snd))
        (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom A.val.toRingHom ≫
          (CommRingCat.pullbackCone (X.presheaf.map (homOfLE le_top).op)
            (φ.appTop ≫ V.topIso.hom)).fst)) ∧
      ∀ a : ι → A, (∀ k, (CommRingCat.ofHom A.val.toRingHom ≫
          (CommRingCat.pullbackCone (X.presheaf.map (homOfLE le_top).op)
            (φ.appTop ≫ V.topIso.hom)).fst) (a k) = g k ∧
          (CommRingCat.ofHom A.val.toRingHom ≫
          (CommRingCat.pullbackCone (X.presheaf.map (homOfLE le_top).op)
            (φ.appTop ≫ V.topIso.hom)).snd) (a k) = b k) →
        (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom A.val.toRingHom ≫
          (CommRingCat.pullbackCone (X.presheaf.map (homOfLE le_top).op)
            (φ.appTop ≫ V.topIso.hom)).snd)).opensRange = ⨆ k, PrimeSpectrum.basicOpen (a k) := by
  classical
  cases nonempty_fintype ι
  have := isOpenImmersion_toSpecΓ_comp_SpecMap_pullbackCone_snd hV _ g b hgb hg hb hY
  set c := CommRingCat.pullbackCone (X.presheaf.map (homOfLE (le_top (a := V))).op)
    (φ.appTop ≫ V.topIso.hom)
  let x (k : ι) : c.pt := ⟨(g k, b k), (hgb k).symm⟩
  obtain ⟨s, hs⟩ := @Scheme.exists_finset_isOpenImmersion_comp_SpecMap_val c.pt _ Y
    (Y.toSpecΓ ≫ Spec.map c.snd) this _ _ (Finset.univ.image x) (by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
        forall_apply_eq_imp_iff]
      exact fun k ↦ mem_range_toSpecΓ_comp_SpecMap_pullbackCone_snd hV _ (g k) (b k) (hgb k) (hg k)
        (hb k))
  refine ⟨s ∪ Finset.univ.image x, fun A hA ↦ ?_⟩
  have hsA : (s : Set c.pt) ⊆ A := fun y hy ↦ hA (Finset.mem_coe.mpr (Finset.mem_union_left _ hy))
  have hopen : IsOpenImmersion
      (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom A.val.toRingHom ≫ c.snd)) := by
    rw [Spec.map_comp, ← Category.assoc]
    exact (hs A hsA).1
  refine ⟨hopen, isPullback_toSpecΓ_comp_SpecMap φ _ _ ?_ (fun k ↦ (⟨x k, hA
    (Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_image_of_mem x
      (Finset.mem_univ k))))⟩ : A)) hg hY, fun a ha ↦
    opensRange_toSpecΓ_comp_SpecMap_eq_iSup (CommRingCat.ofHom A.val.toRingHom ≫ c.snd) a ?_
      fun k p hk ↦ ?_⟩
  · rw [Category.assoc, Category.assoc, c.condition]
  · simpa only [(ha _).2] using hY
  · have hak : (a k : c.pt) = x k := Subtype.ext (Prod.ext (ha k).1 (ha k).2)
    have := (hs A hsA).2 (x k) (Finset.mem_image_of_mem x (Finset.mem_univ k)) (a k) p
      hak hk
    obtain ⟨w, hw⟩ := this
    refine ⟨w, ?_⟩
    rw [Spec.map_comp]
    exact hw

end TauCeti.AlgebraicGeometry.Scheme
