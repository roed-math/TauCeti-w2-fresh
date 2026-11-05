/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftSheaf.Chart
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftSheaf.ChartEquiv
public import TauCeti.RingTheory.Derivation.SquareZeroLocalization

/-!
# Quasi-coherence of the sheaf of derivations into the ideal of a thickening

Let `f : X ⟶ S` be smooth, `i : T ⟶ T'` a first-order thickening and `a : T ⟶ X`, `h : T' ⟶ S`
with `a ≫ f = i ≫ h`. The sheaf of derivations `liftDerivationModule f i a`, under which the sheaf
of lifts of `a` is a torsor, is a quasi-coherent `𝒪_{T'}`-module. Over an affine open `W` of `T'`
with affine charts `U ⊆ X`, `V ⊆ S`, its sections are the `Γ(V, ⊤)`-derivations
`Γ(U, ⊤) → ker (i ∣_ W)^♯` (`liftDerivationChartEquiv`), and over a basic open `D(g) ⊆ W` the
derivations into `ker (i ∣_ D(g))^♯`. The ideal of a closed immersion localizes
(`exists_isLocalizedModule_kerAppTop`), and so do derivations into it, as `Ω` of a smooth algebra
is finitely presented (`Ideal.exists_derivation_comp_eq_pow_mul_of_sq_eq_bot`); main's criterion
`Scheme.Modules.isQuasicoherent_of_isLocalizedModule` concludes. This is the step of Stacks,
Lemma 37.11.7 (02H6) showing that the torsor of lifts is trivial over an affine `T'`.

## Main results

* `TauCeti.AlgebraicGeometry.exists_isLocalizedModule_kerAppTop`: for a closed immersion `i` and
  an affine open `W`, the ideal of `i ∣_ D(g)` is the localization at `g` of the ideal of `i ∣_ W`.
* `TauCeti.AlgebraicGeometry.isLocalizedModule_basicOpenRestrict_liftDerivationModule`: the
  derivations over `D(g)` are the localization at `g` of the derivations over `W`.
* `TauCeti.AlgebraicGeometry.isQuasicoherent_liftDerivationModule`: for `f` smooth, the sheaf of
  derivations is quasi-coherent.

## References

* [Stacks Project, Lemma 37.11.7](https://stacks.math.columbia.edu/tag/02H6).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

variable {T T' : Scheme.{u}} {i : T ⟶ T'}

/-- For a closed immersion `i : T ⟶ T'`, an affine open `W` of `T'` and `g ∈ Γ(T', W)`, the ideal
of `i ∣_ D(g)` is the localization at `g` of the ideal of `i ∣_ W`, through restriction along
`D(g) ⟶ W`: localization commutes with kernels (`RingHom.toKerIsLocalization_isLocalizedModule`). -/
theorem exists_isLocalizedModule_kerAppTop [IsClosedImmersion i] {W : T'.Opens}
    (hW : IsAffineOpen W) (g : Γ(T', W)) :
    letI := (T'.homOfLE (T'.basicOpen_le g)).appTop.hom.toAlgebra
    ∃ ι : RingHom.ker (i ∣_ W).appTop.hom →ₗ[Γ(W.toScheme, ⊤)]
        RingHom.ker (i ∣_ T'.basicOpen g).appTop.hom,
      (∀ x, (ι x : Γ((T'.basicOpen g).toScheme, ⊤)) = (T'.homOfLE (T'.basicOpen_le g)).appTop x) ∧
      IsLocalizedModule (.powers (W.topIso.inv g)) ι := by
  set e := T'.basicOpen_le g
  let := (T'.homOfLE e).appTop.hom.toAlgebra
  let := (T.homOfLE (i.preimage_mono e)).appTop.hom.toAlgebra
  have := hW.isLocalization_away_homOfLE_appTop g rfl e
  have hP := (hW.preimage i).isLocalization_away_homOfLE_appTop (i.app W g)
    (Scheme.preimage_basicOpen i g).symm (i.preimage_mono e)
  rw [← morphismRestrict_appTop_topIso_inv] at hP
  set π := (i ∣_ W).appTop.hom
  have hT : Submonoid.map π (.powers (W.topIso.inv g)) = .powers (π (W.topIso.inv g)) :=
    Submonoid.map_powers _ _
  have key := RingHom.toKerIsLocalization_isLocalizedModule
    (S := Γ((T'.basicOpen g).toScheme, ⊤)) Γ((i ⁻¹ᵁ T'.basicOpen g).toScheme, ⊤) π hT
  have hmap : (IsLocalization.map Γ((i ⁻¹ᵁ T'.basicOpen g).toScheme, ⊤) π
      (hT.symm ▸ Submonoid.le_comap_map _) : Γ((T'.basicOpen g).toScheme, ⊤) →+* _) =
      (i ∣_ T'.basicOpen g).appTop.hom := by
    refine IsLocalization.ringHom_ext (.powers (W.topIso.inv g)) ?_
    rw [IsLocalization.map_comp]
    ext x
    change (T.homOfLE (i.preimage_mono e)).appTop ((i ∣_ W).appTop x) = (i ∣_ T'.basicOpen g).appTop
      ((T'.homOfLE e).appTop x)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, morphismRestrict_homOfLE]
  let ι := ((LinearEquiv.ofEq _ (RingHom.ker (i ∣_ T'.basicOpen g).appTop.hom)
    (congrArg RingHom.ker hmap)).restrictScalars Γ(W.toScheme, ⊤)).toLinearMap ∘ₗ
    RingHom.toKerIsLocalization Γ((T'.basicOpen g).toScheme, ⊤)
      Γ((i ⁻¹ᵁ T'.basicOpen g).toScheme, ⊤) π (hT.symm ▸ Submonoid.le_comap_map _)
  exact ⟨ι, fun x ↦ rfl, IsLocalizedModule.of_linearEquiv _ _ _⟩

variable {X S : Scheme.{u}} {f : X ⟶ S} {a : T ⟶ X} {h : T' ⟶ S} [IsFirstOrderThickening i]
  [Smooth f]

/-- The `Γ(U, ⊤)`-algebra structures on the quotients by the ideals of `i ∣_ W` and `i ∣_ W'` are
compatible with restriction along `W' ⟶ W`. -/
theorem quotientMap_algebraMap_quotientKerAppTopAlgebra {W W' : T'.Opens} {U : X.Opens}
    [IsAffine W.toScheme] [IsAffine W'.toScheme] (e : W' ≤ W) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (hII' : RingHom.ker (i ∣_ W).appTop.hom ≤
      (RingHom.ker (i ∣_ W').appTop.hom).comap (T'.homOfLE e).appTop.hom) (x : Γ(U.toScheme, ⊤)) :
    letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
    letI := quotientKerAppTopAlgebra (i ∣_ W') (a.resLE U (i ⁻¹ᵁ W') ((i.preimage_mono e).trans hU))
    Ideal.quotientMap _ (T'.homOfLE e).appTop.hom hII'
        (algebraMap Γ(U.toScheme, ⊤) (Γ(W.toScheme, ⊤) ⧸ RingHom.ker (i ∣_ W).appTop.hom) x) =
      algebraMap Γ(U.toScheme, ⊤) (Γ(W'.toScheme, ⊤) ⧸ RingHom.ker (i ∣_ W').appTop.hom) x := by
  let := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
  let := quotientKerAppTopAlgebra (i ∣_ W') (a.resLE U (i ⁻¹ᵁ W') ((i.preimage_mono e).trans hU))
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
    (algebraMap Γ(U.toScheme, ⊤) (Γ(W.toScheme, ⊤) ⧸ RingHom.ker (i ∣_ W).appTop.hom) x)
  rw [← hb, Ideal.quotientMap_mk, quotientKerAppTopAlgebra_mk_eq_algebraMap_iff]
  rw [quotientKerAppTopAlgebra_mk_eq_algebraMap_iff] at hb
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, morphismRestrict_homOfLE,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hb, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, Scheme.Hom.map_resLE]

/-- Over an affine open `W` of `T'` with affine charts `U ⊆ X`, `V ⊆ S` and `f` smooth, the
`Γ(V, ⊤)`-derivations of `Γ(U, ⊤)` into the ideal of `i ∣_ D(g)` are the localization at `g` of
those into the ideal of `i ∣_ W`: the surjectivity and injectivity halves, read in `Γ(D(g), ⊤)`. -/
private theorem chart_localization (w : a ≫ f = i ≫ h) {W : T'.Opens} {U : X.Opens}
    {V : S.Opens} [IsAffine W.toScheme] [IsAffine U.toScheme] [IsAffine V.toScheme]
    (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V) (g : Γ(T', W)) :
    haveI : IsAffine (T'.basicOpen g).toScheme :=
      IsAffineOpen.basicOpen (U := W) ‹IsAffine W.toScheme› g
    letI := (f.resLE V U hUV).appTop.hom.toAlgebra
    letI := (h.resLE V W hV).appTop.hom.toAlgebra
    letI := (h.resLE V (T'.basicOpen g) ((T'.basicOpen_le g).trans hV)).appTop.hom.toAlgebra
    letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
    letI := quotientKerAppTopAlgebra (i ∣_ T'.basicOpen g)
      (a.resLE U (i ⁻¹ᵁ T'.basicOpen g) ((i.preimage_mono (T'.basicOpen_le g)).trans hU))
    letI := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
    letI := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ T'.basicOpen g))
    (∀ d' : Derivation Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤)
        (RingHom.ker (i ∣_ T'.basicOpen g).appTop.hom), ∃ (n : ℕ)
        (d : Derivation Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤) (RingHom.ker (i ∣_ W).appTop.hom)),
        ∀ y, (T'.homOfLE (T'.basicOpen_le g)).appTop (d y) =
          (T'.homOfLE (T'.basicOpen_le g)).appTop (W.topIso.inv g ^ n) * d' y) ∧
    ∀ d₁ d₂ : Derivation Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤) (RingHom.ker (i ∣_ W).appTop.hom),
      (∀ y, (T'.homOfLE (T'.basicOpen_le g)).appTop (d₁ y) =
        (T'.homOfLE (T'.basicOpen_le g)).appTop (d₂ y)) →
      ∃ n : ℕ, ∀ y, W.topIso.inv g ^ n * (d₁ y : Γ(W.toScheme, ⊤)) = W.topIso.inv g ^ n * d₂ y := by
  have hW : IsAffineOpen W := ‹IsAffine W.toScheme›
  have : IsAffine (T'.basicOpen g).toScheme := hW.basicOpen g
  have e : T'.basicOpen g ≤ W := T'.basicOpen_le g
  have hU' : i ⁻¹ᵁ T'.basicOpen g ≤ a ⁻¹ᵁ U := (i.preimage_mono e).trans hU
  have hV' : T'.basicOpen g ≤ h ⁻¹ᵁ V := e.trans hV
  let := (f.resLE V U hUV).appTop.hom.toAlgebra
  let := (h.resLE V W hV).appTop.hom.toAlgebra
  let := (h.resLE V (T'.basicOpen g) hV').appTop.hom.toAlgebra
  let := (T'.homOfLE e).appTop.hom.toAlgebra
  have : IsScalarTower Γ(V.toScheme, ⊤) Γ(W.toScheme, ⊤) Γ((T'.basicOpen g).toScheme, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change (h.resLE V (T'.basicOpen g) hV').appTop r =
        (T'.homOfLE e).appTop ((h.resLE V W hV).appTop r)
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Scheme.Hom.map_resLE]
  let := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
  let := quotientKerAppTopAlgebra (i ∣_ T'.basicOpen g) (a.resLE U (i ⁻¹ᵁ T'.basicOpen g) hU')
  have := isScalarTower_quotientKerAppTopAlgebra (commSq_resLE w hU hV hUV)
  have := isScalarTower_quotientKerAppTopAlgebra (commSq_resLE w hU' hV' hUV)
  have : Algebra.Smooth Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤) :=
    HasRingHomProperty.appTop @Smooth (f.resLE V U hUV) inferInstance
  obtain ⟨ι, hι, hloc⟩ := exists_isLocalizedModule_kerAppTop (i := i) hW g
  have hII' : RingHom.ker (i ∣_ W).appTop.hom ≤
      (RingHom.ker (i ∣_ T'.basicOpen g).appTop.hom).comap (T'.homOfLE e).appTop.hom :=
    fun x hx ↦ Ideal.mem_comap.2 (hι ⟨x, hx⟩ ▸ (ι ⟨x, hx⟩).2)
  have hA := quotientMap_algebraMap_quotientKerAppTopAlgebra e hU hII'
  have hI := IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W)
  have hI' := IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ T'.basicOpen g)
  refine ⟨fun d' ↦ ?_, fun d₁ d₂ hd ↦ ?_⟩
  · obtain ⟨n, d, hd⟩ := Ideal.exists_derivation_comp_eq_pow_mul_of_sq_eq_bot
      (R := Γ(V.toScheme, ⊤)) hI hI' hII' hA (W.topIso.inv g) ι d'
    exact ⟨n, d, fun y ↦ (hι _).symm.trans (hd y)⟩
  · exact Ideal.exists_pow_mul_eq_of_derivation_comp_eq_of_sq_eq_bot (R := Γ(V.toScheme, ⊤)) hI hI'
      hII' hA (W.topIso.inv g) ι d₁ d₂ fun y ↦ Subtype.ext ((hι _).trans ((hd y).trans (hι _).symm))

/-- A section `t` over `O` restricted along the identity `O ⟶ O` is `t`. -/
private lemma map_homOfLE_refl_apply (O : T'.Opens) (t : Γ(T', O)) :
    T'.presheaf.map (homOfLE (le_refl O)).op t = t := by
  rw [(Subsingleton.elim _ (𝟙 O) : homOfLE (le_refl O) = 𝟙 O), op_id,
    CategoryTheory.Functor.map_id, CommRingCat.id_apply]

/-- Moving sections over `O` to `Γ(O, ⊤)` is injective. -/
private lemma topIso_inv_injective (O : T'.Opens) : Function.Injective O.topIso.inv :=
  fun s t hst ↦ by simpa only [Iso.inv_hom_id_apply] using congrArg O.topIso.hom hst

/-- Over an affine open `W` with affine charts, every derivation over the basic open `D(g)` is,
after multiplication by a power of `g`, the restriction of a derivation over `W`. -/
private theorem exists_liftDerivationSubgroupRestrict_eq_pow_smul (w : a ≫ f = i ≫ h)
    {W : T'.Opens} {U : X.Opens} {V : S.Opens} [IsAffine W.toScheme] [IsAffine U.toScheme]
    [IsAffine V.toScheme] (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V)
    (g : Γ(T', W)) (D' : liftDerivationSubgroup f i a (T'.basicOpen g)) :
    ∃ (n : ℕ) (D : liftDerivationSubgroup f i a W),
      liftDerivationSubgroupRestrict f i a (T'.basicOpen_le g) D =
        T'.presheaf.map (homOfLE (T'.basicOpen_le g)).op (g ^ n) • D' := by
  have e : T'.basicOpen g ≤ W := T'.basicOpen_le g
  have : IsAffine (T'.basicOpen g).toScheme :=
    IsAffineOpen.basicOpen (U := W) ‹IsAffine W.toScheme› g
  have hU' : i ⁻¹ᵁ T'.basicOpen g ≤ a ⁻¹ᵁ U := (i.preimage_mono e).trans hU
  have hV' : T'.basicOpen g ≤ h ⁻¹ᵁ V := e.trans hV
  obtain ⟨L⟩ := (hasLift_commSq_resLE w hU hV hUV).exists_lift
  set l₀ := (liftSheafObjEquivLiftStruct w hU hV hUV).symm L
  set l₀' := (liftSheaf f i a h).obj.map (homOfLE e).op l₀
  obtain ⟨n, d, hd⟩ :=
    (chart_localization w hU hV hUV g).1 (liftDerivationChart w hU' hV' hUV l₀' D')
  obtain ⟨D, rfl⟩ := liftDerivationChart_surjective w hU hV hUV l₀ d
  refine ⟨n, D, liftDerivationSubgroup.ext_of_isAffineOpen l₀' ‹IsAffine U.toScheme› hU'
    fun x ↦ ?_⟩
  have := hd (U.topIso.inv x)
  have h₂ := coe_liftDerivationChart_apply w hU' hV' hUV l₀' D' (U.topIso.inv x)
  rw [coe_liftDerivationChart_apply, h₂, Iso.inv_hom_id_apply,
    ← Scheme.Opens.topIso_inv_map_homOfLE, ← map_pow, ← Scheme.Opens.topIso_inv_map_homOfLE,
    ← map_mul,
    (isLiftDerivation_coe D).map_apply ⟨(U, W), le_rfl, hU⟩ _ e] at this
  have h₃ := topIso_inv_injective _ this
  rw [← map_homOfLE_refl_apply _ (T'.presheaf.map (homOfLE e).op (g ^ n))] at h₃
  rw [liftDerivationSubgroupRestrict_apply]
  exact h₃

/-- Over an affine open `W` with affine charts, two derivations over `W` with the same restriction
to the basic open `D(g)` agree after multiplication by a power of `g`. -/
private theorem exists_pow_smul_eq_of_liftDerivationSubgroupRestrict_eq (w : a ≫ f = i ≫ h)
    {W : T'.Opens} {U : X.Opens} {V : S.Opens} [IsAffine W.toScheme] [IsAffine U.toScheme]
    [IsAffine V.toScheme] (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V)
    (g : Γ(T', W)) (D₁ D₂ : liftDerivationSubgroup f i a W)
    (hD : liftDerivationSubgroupRestrict f i a (T'.basicOpen_le g) D₁ =
      liftDerivationSubgroupRestrict f i a (T'.basicOpen_le g) D₂) :
    ∃ n : ℕ, g ^ n • D₁ = g ^ n • D₂ := by
  have e : T'.basicOpen g ≤ W := T'.basicOpen_le g
  have : IsAffine (T'.basicOpen g).toScheme :=
    IsAffineOpen.basicOpen (U := W) ‹IsAffine W.toScheme› g
  have hU' : i ⁻¹ᵁ T'.basicOpen g ≤ a ⁻¹ᵁ U := (i.preimage_mono e).trans hU
  obtain ⟨L⟩ := (hasLift_commSq_resLE w hU hV hUV).exists_lift
  set l₀ := (liftSheafObjEquivLiftStruct w hU hV hUV).symm L
  obtain ⟨n, hn⟩ := (chart_localization w hU hV hUV g).2 (liftDerivationChart w hU hV hUV l₀ D₁)
    (liftDerivationChart w hU hV hUV l₀ D₂) fun y ↦ by
      have hc := congrArg (fun D : liftDerivationSubgroup f i a (T'.basicOpen g) ↦
          D.1 ⟨(U, T'.basicOpen g), le_rfl, hU'⟩ (U.topIso.hom y)) hD
      rw [liftDerivationSubgroupRestrict_apply, liftDerivationSubgroupRestrict_apply] at hc
      rw [coe_liftDerivationChart_apply w hU hV hUV l₀ D₁,
        coe_liftDerivationChart_apply w hU hV hUV l₀ D₂, ← Scheme.Opens.topIso_inv_map_homOfLE,
        ← Scheme.Opens.topIso_inv_map_homOfLE,
        (isLiftDerivation_coe D₁).map_apply ⟨(U, W), le_rfl, hU⟩ _ e,
        (isLiftDerivation_coe D₂).map_apply ⟨(U, W), le_rfl, hU⟩ _ e]
      exact congrArg _ hc
  refine ⟨n, liftDerivationSubgroup.ext_of_isAffineOpen l₀ ‹IsAffine U.toScheme› hU fun x ↦ ?_⟩
  have := hn (U.topIso.inv x)
  rw [coe_liftDerivationChart_apply w hU hV hUV l₀ D₁,
    coe_liftDerivationChart_apply w hU hV hUV l₀ D₂, Iso.inv_hom_id_apply,
    ← map_pow, ← map_mul, ← map_mul] at this
  have h₃ := topIso_inv_injective _ this
  rw [← map_homOfLE_refl_apply W (g ^ n)] at h₃
  rw [liftDerivationSubgroup.smul_apply, liftDerivationSubgroup.smul_apply]
  exact h₃

/-- **The sheaf of derivations localizes.** For `f` smooth and an affine open `W` of `T'` with
affine charts `U ⊆ X`, `V ⊆ S` (`a (i ⁻¹ W) ⊆ U`, `h W ⊆ V`, `f U ⊆ V`), the derivations over a
basic open `D(g) ⊆ W` are the localization at `g` of the derivations over `W`. -/
theorem isLocalizedModule_basicOpenRestrict_liftDerivationModule (w : a ≫ f = i ≫ h)
    {W : T'.Opens} {U : X.Opens} {V : S.Opens} (hW : IsAffineOpen W) (hUa : IsAffineOpen U)
    (hVa : IsAffineOpen V) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V)
    (g : Γ(T', W)) :
    IsLocalizedModule.Away g (Scheme.Modules.basicOpenRestrict (liftDerivationModule f i a) g) := by
  have : IsAffine W.toScheme := hW
  have : IsAffine U.toScheme := hUa
  have : IsAffine V.toScheme := hVa
  have hres (D : liftDerivationSubgroup f i a W) :
      Scheme.Modules.basicOpenRestrict (liftDerivationModule f i a) g
        (D : Γ(liftDerivationModule f i a, W)) =
        (liftDerivationSubgroupRestrict f i a (T'.basicOpen_le g) D :
          liftDerivationSubgroup f i a _) :=
    (Scheme.Modules.basicOpenRestrict_apply _ g _).trans rfl
  refine ⟨?_, fun D' ↦ ?_, fun {D₁ D₂} hD ↦ ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact ((liftDerivationModule f i a).isUnit_algebraMap_end_basicOpen g).pow n
  · obtain ⟨n, D, hD⟩ := exists_liftDerivationSubgroupRestrict_eq_pow_smul w hU hV hUV g D'
    exact ⟨⟨D, ⟨g ^ n, n, rfl⟩⟩, ((hres D).trans hD).symm⟩
  · obtain ⟨n, hn⟩ := exists_pow_smul_eq_of_liftDerivationSubgroupRestrict_eq w hU hV hUV g D₁ D₂
      ((hres D₁).symm.trans (hD.trans (hres D₂)))
    exact ⟨⟨g ^ n, n, rfl⟩, hn⟩

/-- **Quasi-coherence of the sheaf of derivations.** For `f` smooth, the sheaf of derivations of
`a⁻¹ 𝒪_X` over `𝒪_S` into the ideal of the first-order thickening `i` is a quasi-coherent
`𝒪_{T'}`-module. -/
theorem isQuasicoherent_liftDerivationModule (w : a ≫ f = i ≫ h) :
    (liftDerivationModule f i a).IsQuasicoherent := by
  choose W U V hW hU hV hxW _ hUW hVW hUV using
    fun x : T' ↦ exists_affine_chart w (O := ⊤) (Set.mem_univ x)
  refine Scheme.Modules.isQuasicoherent_of_isLocalizedModule _ W hW
    (top_le_iff.1 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩) fun x g ↦ ?_
  exact isLocalizedModule_basicOpenRestrict_liftDerivationModule w (hW x) (hU x) (hV x) (hUW x)
    (hVW x) (hUV x) g

end TauCeti.AlgebraicGeometry
