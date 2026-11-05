/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.UpNat
public import TauCeti.CategoryTheory.Abelian.RightDerived
public import TauCeti.CategoryTheory.Abelian.Injective.CartanEilenberg

/-!
# The spectral sequence of a Cartan–Eilenberg double complex

Let `K` be a cochain complex in an abelian category with enough injectives, indexed by `ℕ`, and
let `G` be an additive functor into an abelian category. Applying `G` to the Cartan–Eilenberg
double complex `J = CochainComplex.cartanEilenberg K` gives a first-quadrant cochain bicomplex
`G(J)` (`CochainComplex.mapCartanEilenberg`), whose spectral sequence filtered by the resolution
degree is `CochainComplex.cartanEilenbergSpectralSequence`. By the row property of
Cartan–Eilenberg resolutions (`CochainComplex.cartanEilenbergRowHomologyIso`), its first page at
the resolution degree `s` and the degree `k` is `G(J(Hᵏ)ˢ)`, where `J(Hᵏ)` is the chosen injective
resolution `CochainComplex.homologyResolution` of `Hᵏ(K)`, and its first differential is, up to
the sign `(-1)ᵏ`, the image under `G` of the differential of `J(Hᵏ)`. Hence its second page is

  `E₂^{s,k} = RˢG(Hᵏ(K))`

(`CochainComplex.cartanEilenbergSpectralSequencePageThreeXIso`). The spectral sequence converges
to the cohomology of the total complex of `G(J)`
(`HomologicalComplex₂.rowFiltrationUpAbutmentIso`). When `G` is left exact and every term of `K`
is `G`-acyclic, the columns of `G(J)` are resolutions of the terms of `G(K)`, so `G(K)` computes
this cohomology (`CochainComplex.quasiIso_totalCoaugmentation_mapCartanEilenberg`) and the
spectral sequence converges to the cohomology of `G(K)`
(`CochainComplex.cartanEilenbergSpectralSequenceAbutmentIso`).

## Indexing

The spectral sequence uses Mathlib's numbering `coreE₂Cohomological`, in which the first page is
numbered `2`; the object of resolution degree `s` and degree `k` sits at
`(k + 2s + 1, -(s + 1))`, as in `HomologicalComplex₂.rowFiltrationUpSpectralSequenceFirstPageXIso`.
The page numbered `3` is therefore the classical `E₂` page.

## Main definitions and results

* `CochainComplex.cartanEilenbergSpectralSequence`: the spectral sequence of `G(J)` filtered by
  the resolution degree.
* `CochainComplex.cartanEilenbergSpectralSequenceFirstPageXIso`,
  `CochainComplex.cartanEilenbergSpectralSequenceFirstPageXIso_inv_d_hom`: its first page is the
  complex `G(J(Hᵏ))`, up to the sign `(-1)ᵏ` of the differentials.
* `CochainComplex.cartanEilenbergSpectralSequencePageThreeXIso`: its second page is
  `RˢG(Hᵏ(K))`.
* `CochainComplex.cartanEilenbergSpectralSequence_page_d_eq_zero`,
  `CochainComplex.cartanEilenbergSpectralSequenceEInftyIso`,
  `CochainComplex.cartanEilenbergSpectralSequenceEInftyIsoAbutment`: when the cohomology of `K` is
  concentrated in degree `0`, the spectral sequence degenerates at `E₂` and its abutment of
  degree `s` is `RˢG(H⁰(K))`.
* `CategoryTheory.InjectiveResolution.quasiIso_of_isZero_rightDerived`: a left exact functor
  applied to an injective resolution of an acyclic object gives a resolution.
* `CochainComplex.quasiIso_totalCoaugmentation_mapCartanEilenberg`,
  `CochainComplex.cartanEilenbergSpectralSequenceAbutmentIso`: for `G` left exact and `K`
  termwise `G`-acyclic, the spectral sequence converges to the cohomology of `G(K)`.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 5.7.
* [Stacks, Section 13.21 (015G)](https://stacks.math.columbia.edu/tag/015G)
-/

@[expose] public section

open CategoryTheory Category Limits
open ComplexShape (up)

universe v u

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C] {D : Type*}
  [Category* D] [Abelian D] {X : C} (I : InjectiveResolution X) (G : C ⥤ D) [G.Additive]
  [PreservesFiniteLimits G]

/-- **A left exact functor applied to a resolution of an acyclic object.** If `G` is left exact
and `RⁿG(X) = 0` for `n > 0`, then for an injective resolution `I` of `X`, the coaugmented
complex `0 ⟶ G(X) ⟶ G(I⁰) ⟶ G(I¹) ⟶ ⋯` is exact: any cochain map from `G(X)` in degree `0` to a
complex isomorphic to `G(I)`, compatible with `G(X ⟶ I⁰)`, is a quasi-isomorphism. -/
theorem quasiIso_of_isZero_rightDerived (hX : ∀ n, IsZero ((G.rightDerived (n + 1)).obj X))
    {Y : CochainComplex D ℕ} (f : (CochainComplex.single₀ D).obj (G.obj X) ⟶ Y)
    (e : Y ≅ (G.mapHomologicalComplex _).obj I.cocomplex) (hf : f.f 0 ≫ e.hom.f 0 = G.map I.ι₀) :
    QuasiIso f := by
  rw [← quasiIso_iff_comp_right f e.hom, quasiIso_iff]
  intro n
  cases n with
  | zero =>
    have hf' : f.f 0 ≫ e.hom.f 0 = G.map (I.ι.f 0) := hf
    have hw : G.map (I.ι.f 0) ≫ G.map (I.cocomplex.d 0 1) = 0 := by
      rw [← G.map_comp]
      exact (congrArg G.map I.ι₀_comp_d).trans (G.map_zero _ _)
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso (S₂ := ShortComplex.mk _ _ hw) ?_).2 ?_
      · exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simpa using hf'.symm) (by simp)
      · rw [ShortComplex.exact_and_mono_f_iff_f_is_kernel]
        exact ⟨KernelFork.mapIsLimit _ I.isLimitKernelFork G⟩
    all_goals first
      | rfl
      | exact ((G.mapHomologicalComplex _).obj I.cocomplex).shape 0 0 (fun h ↦ by simp at h)
  | succ n =>
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _),
      HomologicalComplex.exactAt_iff_isZero_homology]
    exact (hX n).of_iso (I.isoRightDerivedObj G (n + 1)).symm

end CategoryTheory.InjectiveResolution

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  (K : CochainComplex C ℕ) {D : Type*} [Category* D] [Abelian D] (G : C ⥤ D) [G.Additive]

/-- The image `G(J)` under an additive functor `G` of the Cartan–Eilenberg double complex `J` of
`K`. -/
noncomputable abbrev mapCartanEilenberg : HomologicalComplex₂ D (up ℕ) (up ℕ) :=
  ((G.mapHomologicalComplex (up ℕ)).mapHomologicalComplex (up ℕ)).obj K.cartanEilenberg

/-- The spectral sequence of the image `G(J)` of the Cartan–Eilenberg double complex of `K`,
filtered by the resolution degree. Its second page is `RˢG(Hᵏ(K))`
(`CochainComplex.cartanEilenbergSpectralSequencePageThreeXIso`), and it converges to the
cohomology of the total complex of `G(J)`. -/
noncomputable abbrev cartanEilenbergSpectralSequence :=
  (K.mapCartanEilenberg G).rowFiltrationUpSpectralSequence

/-- The row `s` of `G(J)`, formed by the horizontal differentials, is the complex
`cartanEilenbergRow G s` of the image under `G` of the row `s` of `J`. -/
noncomputable def mapCartanEilenbergRowIso (s : ℕ) :
    ((HomologicalComplex.eval D (up ℕ) s).mapHomologicalComplex (up ℕ)).obj
      (K.mapCartanEilenberg G) ≅ K.cartanEilenbergRow G s :=
  -- The two complexes agree by definition.
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _)
    (fun _ _ _ ↦ (id_comp _).trans (comp_id _).symm)

/-- The vertical differentials of `G(J)` from the row `s` to the row `s + 1` are the images
under `G` of those of `J`. -/
lemma mapCartanEilenbergRowIso_inv_dRow_hom (s : ℕ) :
    (K.mapCartanEilenbergRowIso G s).inv ≫ (K.mapCartanEilenberg G).dRow s (s + 1) ≫
        (K.mapCartanEilenbergRowIso G (s + 1)).hom =
      (G.mapHomologicalComplex _).map (K.cartanEilenberg.flip.d s (s + 1)) := by
  ext q
  exact (id_comp _).trans (comp_id _)

/-- **The first page of the Cartan–Eilenberg spectral sequence**: its object at
`(p, -(s + 1))`, with `p = k + 2s + 1`, is `G(J(Hᵏ)ˢ)`, where `J(Hᵏ)` is the chosen injective
resolution of `Hᵏ(K)`. -/
noncomputable def cartanEilenbergSpectralSequenceFirstPageXIso (p : ℤ) (s k : ℕ)
    (hp : p = k + 2 * s + 1) :
    ((K.cartanEilenbergSpectralSequence G).page 2).X (p, -((s : ℤ) + 1)) ≅
      G.obj ((K.homologyResolution k).cocomplex.X s) :=
  (K.mapCartanEilenberg G).rowFiltrationUpSpectralSequenceFirstPageXIso p s k hp ≪≫
    HomologicalComplex.homologyMapIso (K.mapCartanEilenbergRowIso G s) k ≪≫
    K.cartanEilenbergRowHomologyIso G s k

/-- **The first differential of the Cartan–Eilenberg spectral sequence**: under the
identifications `cartanEilenbergSpectralSequenceFirstPageXIso`, the differential from the
resolution degree `s` to `s + 1` in degree `k` is `(-1)ᵏ` times the image under `G` of the
differential of the resolution `J(Hᵏ)`. -/
theorem cartanEilenbergSpectralSequenceFirstPageXIso_inv_d_hom (p p' : ℤ) (s k : ℕ)
    (hp : p = k + 2 * s + 1) (hp' : p' = k + 2 * (s + 1 : ℕ) + 1) :
    (K.cartanEilenbergSpectralSequenceFirstPageXIso G p s k hp).inv ≫
      ((K.cartanEilenbergSpectralSequence G).page 2).d (p, -((s : ℤ) + 1))
        (p', -(((s + 1 : ℕ) : ℤ) + 1)) ≫
      (K.cartanEilenbergSpectralSequenceFirstPageXIso G p' (s + 1) k hp').hom =
    ((-1) ^ k : ℤ) • G.map ((K.homologyResolution k).cocomplex.d s (s + 1)) := by
  have h := (K.mapCartanEilenberg G).rowFiltrationUpSpectralSequenceFirstPageXIso_inv_d_hom
    p p' s k hp hp'
  simp only [cartanEilenbergSpectralSequenceFirstPageXIso, Iso.trans_hom, Iso.trans_inv, assoc,
    HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyMapIso_inv]
  rw [reassoc_of% h, Linear.smul_comp, Linear.comp_smul, Linear.comp_smul]
  congr 1
  rw [← HomologicalComplex.homologyMap_comp_assoc, ← HomologicalComplex.homologyMap_comp_assoc,
    Category.assoc, mapCartanEilenbergRowIso_inv_dRow_hom]
  exact (Iso.inv_comp_eq _).2 (K.homologyMap_map_flip_d_cartanEilenbergRowHomologyIso_hom G s k)

/-- The cohomology of the first page of the Cartan–Eilenberg spectral sequence at the resolution
degree `s` and the degree `k`, computed from a morphism of short complexes from the complex
`G(J(Hᵏ))` around the degree `s`, whose first component is given and whose other two components
are the identifications `cartanEilenbergSpectralSequenceFirstPageXIso` of the first page, the
last one twisted by the sign `(-1)ᵏ` of the first differential. -/
noncomputable def cartanEilenbergSpectralSequencePageTwoHomologyIsoOfEpi (s k : ℕ)
    (i : ℤ × ℤ) (i' : ℕ)
    (hi : (ComplexShape.up' ((2, 1 - 2) : ℤ × ℤ)).prev ((k : ℤ) + 2 * s + 1, -((s : ℤ) + 1)) = i)
    (hi' : (up ℕ).prev s = i')
    (τ₁ : G.obj ((K.homologyResolution k).cocomplex.X i') ⟶
      ((K.cartanEilenbergSpectralSequence G).page 2).X i) [Epi τ₁]
    (hτ₁ : τ₁ ≫ ((K.cartanEilenbergSpectralSequence G).page 2).d i
        ((k : ℤ) + 2 * s + 1, -((s : ℤ) + 1)) =
      G.map ((K.homologyResolution k).cocomplex.d i' s) ≫
        (K.cartanEilenbergSpectralSequenceFirstPageXIso G _ s k rfl).inv) :
    ((K.cartanEilenbergSpectralSequence G).page 2).homology
        ((k : ℤ) + 2 * s + 1, -((s : ℤ) + 1)) ≅
      ((G.mapHomologicalComplex _).obj (K.homologyResolution k).cocomplex).homology s :=
  let E := (K.cartanEilenbergSpectralSequence G).page 2
  let Y := (G.mapHomologicalComplex _).obj (K.homologyResolution k).cocomplex
  let ε : ℤ := (-1) ^ k
  have hε : ε * ε = 1 := by rw [← mul_pow]; simp
  let e₃ := K.cartanEilenbergSpectralSequenceFirstPageXIso G _ (s + 1) k rfl
  let φ : Y.sc' i' s (s + 1) ⟶ E.sc' i ((k : ℤ) + 2 * s + 1, -((s : ℤ) + 1))
      ((k : ℤ) + 2 * (s + 1 : ℕ) + 1, -(((s + 1 : ℕ) : ℤ) + 1)) :=
    { τ₁ := τ₁
      τ₂ := (K.cartanEilenbergSpectralSequenceFirstPageXIso G _ s k rfl).inv
      τ₃ := ε • e₃.inv
      comm₁₂ := hτ₁.trans rfl
      comm₂₃ := by
        rw [← cancel_mono e₃.hom]
        refine (assoc _ _ _).trans
          ((K.cartanEilenbergSpectralSequenceFirstPageXIso_inv_d_hom G _ _ s k rfl rfl).trans ?_)
        rw [assoc, Linear.smul_comp, Iso.inv_hom_id, Linear.comp_smul, comp_id]
        rfl }
  have : IsSplitMono (ε • e₃.inv) := IsSplitMono.mk' ⟨ε • e₃.hom, by
    rw [Linear.smul_comp, Linear.comp_smul, smul_smul, hε, one_smul, Iso.inv_hom_id]⟩
  have : IsIso (ShortComplex.homologyMap φ) :=
    ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' φ (inferInstanceAs (Epi τ₁))
      (inferInstanceAs (IsIso (Iso.inv _))) (inferInstanceAs (Mono (ε • e₃.inv)))
  (E.homologyIsoSc' i _ _ hi (ComplexShape.next_eq' _ (by ext <;> simp <;> lia)) ≪≫
    (asIso (ShortComplex.homologyMap φ)).symm ≪≫
    (Y.homologyIsoSc' i' s (s + 1) hi' (by simp)).symm)

/-- The cohomology of the first page of the Cartan–Eilenberg spectral sequence at the resolution
degree `s` and the degree `k` is the cohomology in degree `s` of `G(J(Hᵏ))`. -/
noncomputable def cartanEilenbergSpectralSequencePageTwoHomologyIso : (s k : ℕ) →
    ((K.cartanEilenbergSpectralSequence G).page 2).homology
        ((k : ℤ) + 2 * s + 1, -((s : ℤ) + 1)) ≅
      ((G.mapHomologicalComplex _).obj (K.homologyResolution k).cocomplex).homology s
  | 0, k =>
    have hZ := (K.mapCartanEilenberg G).isZero_rowFiltrationUpSpectralSequence_page_two_X_of_nonneg
      ((k : ℤ) - 1) 0 le_rfl
    have : Epi (0 : G.obj ((K.homologyResolution k).cocomplex.X 0) ⟶
        ((K.cartanEilenbergSpectralSequence G).page 2).X ((k : ℤ) - 1, 0)) :=
      ⟨fun _ _ _ ↦ hZ.eq_of_src _ _⟩
    K.cartanEilenbergSpectralSequencePageTwoHomologyIsoOfEpi G 0 k ((k : ℤ) - 1, 0) 0
      (ComplexShape.prev_eq' _ (by ext <;> simp; lia)) (by simp) 0 (by simp)
  | s + 1, k =>
    let ε : ℤ := (-1) ^ k
    have hε : ε * ε = 1 := by rw [← mul_pow]; simp
    let e₁ := K.cartanEilenbergSpectralSequenceFirstPageXIso G _ s k rfl
    have : IsSplitEpi (ε • e₁.inv) := IsSplitEpi.mk' ⟨ε • e₁.hom, by
      rw [Linear.smul_comp, Linear.comp_smul, smul_smul, hε, one_smul, Iso.hom_inv_id]⟩
    K.cartanEilenbergSpectralSequencePageTwoHomologyIsoOfEpi G (s + 1) k _ s
      (ComplexShape.prev_eq' _ (by ext <;> simp <;> lia)) (by simp) (ε • e₁.inv) (by
        rw [← cancel_mono (K.cartanEilenbergSpectralSequenceFirstPageXIso G _ (s + 1) k rfl).hom]
        have h := K.cartanEilenbergSpectralSequenceFirstPageXIso_inv_d_hom G _ _ s k rfl rfl
        rw [assoc, Linear.smul_comp, h, smul_smul, hε, one_smul, assoc, Iso.inv_hom_id, comp_id])

/-- **The second page of the Cartan–Eilenberg spectral sequence**: its object at the resolution
degree `s` and the degree `k`, at `(k + 2s + 1, -(s + 1))` on the page numbered `3` in Mathlib's
numbering, is `RˢG(Hᵏ(K))`. -/
noncomputable def cartanEilenbergSpectralSequencePageThreeXIso (s k : ℕ) :
    ((K.cartanEilenbergSpectralSequence G).page 3).X ((k : ℤ) + 2 * s + 1, -((s : ℤ) + 1)) ≅
      (G.rightDerived s).obj (K.homology k) :=
  ((K.cartanEilenbergSpectralSequence G).iso 2 3 _).symm ≪≫
    K.cartanEilenbergSpectralSequencePageTwoHomologyIso G s k ≪≫
    ((K.homologyResolution k).isoRightDerivedObj G s).symm

/-! ### Degeneration when the cohomology is concentrated in degree `0` -/

section Degeneration

variable {K G}

/-- If the cohomology of `K` is concentrated in degree `0`, then from page `3` on the
Cartan–Eilenberg spectral sequence vanishes outside the row `E₂^{s,0} = RˢG(H⁰(K))`: its object at
`(p, q)` is zero unless `p + 2q + 1 = 0`. -/
lemma isZero_cartanEilenbergSpectralSequence_page_X
    (hK : ∀ k : ℕ, IsZero (K.homology (k + 1))) (r : ℤ) (hr : 3 ≤ r) (pq : ℤ × ℤ)
    (hpq : pq.1 + 2 * pq.2 + 1 ≠ 0) :
    IsZero (((K.cartanEilenbergSpectralSequence G).page r).X pq) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, r = 3 + m := ⟨(r - 3).toNat, by omega⟩
  induction m with
  | zero =>
    obtain ⟨p, q⟩ := pq
    dsimp only at hpq
    have hzero (h : IsZero (((K.cartanEilenbergSpectralSequence G).page 2).X (p, q))) :
        IsZero (((K.cartanEilenbergSpectralSequence G).page (3 + (0 : ℕ))).X (p, q)) :=
      (ShortComplex.isZero_homology_of_isZero_X₂ _ h).of_iso
        ((K.cartanEilenbergSpectralSequence G).iso 2 _ _ (by simp)).symm
    obtain hq | hq := le_or_gt 0 q
    · exact hzero (HomologicalComplex₂.isZero_rowFiltrationUpSpectralSequence_page_two_X_of_nonneg
        _ _ _ hq)
    obtain ⟨s, rfl⟩ : ∃ s : ℕ, q = -((s : ℤ) + 1) := ⟨(-q - 1).toNat, by omega⟩
    obtain hk | hk := lt_or_gt_of_ne hpq
    · exact hzero (HomologicalComplex₂.isZero_rowFiltrationUpSpectralSequence_page_two_X_of_lt
        _ p s (by omega))
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = ((k + 1 : ℕ) : ℤ) + 2 * s + 1 :=
        ⟨(p - 2 * s - 2).toNat, by omega⟩
      exact ((G.rightDerived s).map_isZero (hK k)).of_iso
        ((K.cartanEilenbergSpectralSequence G).pageXIsoOfEq _ _ 3 (by simp) ≪≫
          K.cartanEilenbergSpectralSequencePageThreeXIso G s (k + 1))
  | succ m ih =>
    exact (ShortComplex.isZero_homology_of_isZero_X₂ _ (ih (by omega))).of_iso
      ((K.cartanEilenbergSpectralSequence G).iso (3 + m) _ pq (by push_cast; ring)).symm

/-- **Degeneration of the Cartan–Eilenberg spectral sequence** when the cohomology of `K` is
concentrated in degree `0`: all its differentials vanish from page `3` on, since every differential
leaves or reaches an object outside the row `E₂^{s,0}`. -/
lemma cartanEilenbergSpectralSequence_page_d_eq_zero
    (hK : ∀ k : ℕ, IsZero (K.homology (k + 1))) (r : ℤ) (hr : 3 ≤ r)
    (pq pq' : ℤ × ℤ) : ((K.cartanEilenbergSpectralSequence G).page r).d pq pq' = 0 := by
  by_cases h : pq.1 + 2 * pq.2 + 1 = 0
  · by_cases hrel : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel pq pq'
    · refine (isZero_cartanEilenbergSpectralSequence_page_X hK r hr pq' ?_).eq_of_tgt _ _
      rw [← hrel, Prod.fst_add, Prod.snd_add]
      omega
    · exact ((K.cartanEilenbergSpectralSequence G).page r).shape _ _ hrel
  · exact (isZero_cartanEilenbergSpectralSequence_page_X hK r hr pq h).eq_of_src _ _

/-- When the cohomology of `K` is concentrated in degree `0`, consecutive pages of the
Cartan–Eilenberg spectral sequence agree from page `3` on, since all differentials vanish. -/
noncomputable def cartanEilenbergSpectralSequencePageSuccXIso
    (hK : ∀ k : ℕ, IsZero (K.homology (k + 1))) (r : ℤ) (hr : 3 ≤ r) (pq : ℤ × ℤ) :
    ((K.cartanEilenbergSpectralSequence G).page (r + 1)).X pq ≅
      ((K.cartanEilenbergSpectralSequence G).page r).X pq :=
  ((K.cartanEilenbergSpectralSequence G).iso r (r + 1) pq).symm ≪≫
    (((K.cartanEilenbergSpectralSequence G).page r).isoHomologyπ _ pq rfl
      (cartanEilenbergSpectralSequence_page_d_eq_zero hK r hr _ _)).symm ≪≫
    ((K.cartanEilenbergSpectralSequence G).page r).iCyclesIso pq _ rfl
      (cartanEilenbergSpectralSequence_page_d_eq_zero hK r hr _ _)

/-- When the cohomology of `K` is concentrated in degree `0`, every page `3 + m` of the
Cartan–Eilenberg spectral sequence is its page `3`. -/
noncomputable def cartanEilenbergSpectralSequencePageXIsoPageThree
    (hK : ∀ k : ℕ, IsZero (K.homology (k + 1))) : (m : ℕ) → (pq : ℤ × ℤ) →
    ((K.cartanEilenbergSpectralSequence G).page (3 + m)).X pq ≅
      ((K.cartanEilenbergSpectralSequence G).page 3).X pq
  | 0, pq => (K.cartanEilenbergSpectralSequence G).pageXIsoOfEq pq _ _
  | m + 1, pq => (K.cartanEilenbergSpectralSequence G).pageXIsoOfEq pq _ (3 + m + 1) ≪≫
      cartanEilenbergSpectralSequencePageSuccXIso hK (3 + m) (by omega) pq ≪≫
      cartanEilenbergSpectralSequencePageXIsoPageThree hK m pq

/-- **The Cartan–Eilenberg spectral sequence degenerates at `E₂`** when the cohomology of `K` is
concentrated in degree `0`: its limit object of degree `s` at the filtration index `-(s + 1)` is
`E₂^{s,0} = RˢG(H⁰(K))`. -/
noncomputable def cartanEilenbergSpectralSequenceEInftyIso
    (hK : ∀ k : ℕ, IsZero (K.homology (k + 1))) (s : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor
      (K.mapCartanEilenberg G).rowFiltrationUp
        (K.mapCartanEilenberg G).monotone_rowFiltrationUp)).EInfty
        (-((s : ℤ) + 1)) s ≅
      (G.rightDerived s).obj (K.homology 0) :=
  (CochainComplex.filtrationSpectralSequencePageXIsoEInfty _ _ (3 + s) (by omega)
      (((0 : ℕ) : ℤ) + 2 * s + 1, -((s : ℤ) + 1)) s (by push_cast; ring)
      (by
        rw [show -((s : ℤ) + 1) - (3 + s) + 2 = -((2 * s + 2 : ℕ) : ℤ) by push_cast; ring]
        exact HomologicalComplex.ExactAt.isZero_homology (ShortComplex.exact_of_isZero_X₂ _
          (HomologicalComplex₂.isZero_rowFiltrationUp_X _ (2 * s + 2) _ (by omega))))
      ((HomologicalComplex₂.rowFiltrationUp _ _).isZero_homology_cokernel_of_eq_top
        (HomologicalComplex₂.rowFiltrationUp_eq_top _ _ (by omega)) _)).symm ≪≫
    cartanEilenbergSpectralSequencePageXIsoPageThree hK s _ ≪≫
    K.cartanEilenbergSpectralSequencePageThreeXIso G s 0

/-- When the cohomology of `K` is concentrated in degree `0`, the limit objects of the
Cartan–Eilenberg spectral sequence vanish outside the row `E₂^{s,0}`: the object of degree `n` at
the filtration index `q` is zero unless `n + q + 1 = 0`. -/
lemma isZero_cartanEilenbergSpectralSequenceEInfty
    (hK : ∀ k : ℕ, IsZero (K.homology (k + 1))) (q n : ℤ) (h : n + q + 1 ≠ 0) :
    IsZero ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor
      (K.mapCartanEilenberg G).rowFiltrationUp
        (K.mapCartanEilenberg G).monotone_rowFiltrationUp)).EInfty
        q n) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = n.toNat + (-n).toNat + q.toNat + (-q).toNat + 3 :=
    ⟨n.toNat + (-n).toNat + q.toNat + (-q).toNat + 3, by push_cast; rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ, q - (3 + m) + 2 = -(s : ℤ) := ⟨(-(q - (3 + m) + 2)).toNat, by omega⟩
  refine (isZero_cartanEilenbergSpectralSequence_page_X hK (3 + m) (by omega) (n - q, q)
    (by dsimp only; omega)).of_iso
      (CochainComplex.filtrationSpectralSequencePageXIsoEInfty _ _ (3 + m) (by omega) (n - q, q) n
        (by dsimp only; ring) ?_ ?_).symm
  · rw [hs]
    exact HomologicalComplex.ExactAt.isZero_homology (ShortComplex.exact_of_isZero_X₂ _
      (HomologicalComplex₂.isZero_rowFiltrationUp_X _ s _ (by omega)))
  · exact (HomologicalComplex₂.rowFiltrationUp _ _).isZero_homology_cokernel_of_eq_top
      (HomologicalComplex₂.rowFiltrationUp_eq_top _ _ (by omega)) _

/-- When the cohomology of `K` is concentrated in degree `0`, the filtration of the abutment of
degree `n` of the Cartan–Eilenberg spectral sequence is everything from the index `-n` on: its piece
at an index `q = -j` with `j ≤ n` is the whole abutment. -/
lemma isIso_cartanEilenbergSpectralSequence_abutmentFiltrationι
    (hK : ∀ k : ℕ, IsZero (K.homology (k + 1))) (n j : ℕ) (hj : j ≤ n) (q : ℤ)
    (hq : q + j = 0) :
    IsIso (Abelian.SpectralObject.abutmentFiltrationι
      (CochainComplex.spectralObject (CochainComplex.filtrationFunctor
        (K.mapCartanEilenberg G).rowFiltrationUp
          (K.mapCartanEilenberg G).monotone_rowFiltrationUp)) q n) := by
  induction j generalizing q with
  | zero => exact HomologicalComplex₂.isIso_rowFiltrationUp_abutmentFiltrationι _ q n (by omega)
  | succ j ih =>
    have := ih (by omega) (q + 1) (by push_cast at hq; omega)
    rw [← Abelian.SpectralObject.abutmentFiltrationMap_ι]
    refine IsIso.comp_isIso' (@isIso_of_mono_of_epi _ _ _ _ _ _
      (mono_of_mono_fac (Abelian.SpectralObject.abutmentFiltrationMap_ι _ q n)) ?_) this
    exact Preadditive.epi_of_isZero_cokernel _
      ((isZero_cartanEilenbergSpectralSequenceEInfty hK q n (by push_cast at hq; omega)).of_iso
        (Abelian.SpectralObject.EInftyIsoCokernel _ q n).symm)

/-- **Collapse of the Cartan–Eilenberg spectral sequence** when the cohomology of `K` is
concentrated in degree `0`: its abutment of degree `n` is its limit object of degree `n` at the
filtration index `-(n + 1)`, the only graded piece of the filtration that does not vanish. -/
noncomputable def cartanEilenbergSpectralSequenceEInftyIsoAbutment
    (hK : ∀ k : ℕ, IsZero (K.homology (k + 1))) (n : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor
      (K.mapCartanEilenberg G).rowFiltrationUp
        (K.mapCartanEilenberg G).monotone_rowFiltrationUp)).EInfty
        (-((n : ℤ) + 1)) n ≅
      (CochainComplex.spectralObject (CochainComplex.filtrationFunctor
        (K.mapCartanEilenberg G).rowFiltrationUp
          (K.mapCartanEilenberg G).monotone_rowFiltrationUp)).abutment
        n :=
  have h₀ := HomologicalComplex₂.isZero_rowFiltrationUp_abutmentFiltration
    (K.mapCartanEilenberg G) (n + 1) n
    (by omega)
  have := isIso_cartanEilenbergSpectralSequence_abutmentFiltrationι hK n n le_rfl
    (-((n : ℤ) + 1) + 1) (by ring)
  Abelian.SpectralObject.EInftyIsoCokernel _ _ _ ≪≫
    cokernelIsoOfEq (IsZero.eq_of_src (by push_cast at h₀; exact h₀) _ _) ≪≫
    cokernelZeroIsoTarget ≪≫ @asIso _ _ _ _ _ this

end Degeneration

/-! ### The abutment -/

/-- The coaugmentation `G(K) ⟶ G(J)` of the row `0` of `G(J)` (the column `0` of the flipped
bicomplex), given by the images under `G` of the augmentations `Kᵠ ⟶ J(Kᵠ)⁰`. -/
noncomputable def mapCartanEilenbergCoaugmentation :
    (G.mapHomologicalComplex _).obj K ⟶ (K.mapCartanEilenberg G).flip.X 0 where
  f q := G.map (K.cartanEilenbergResolution q).ι₀
  comm' := by
    rintro q _ rfl
    -- The row `0` of `G(J)` is formed by the images under `G` of the lifts of the differentials.
    exact (G.map_comp _ _).symm.trans ((congrArg G.map
      ((congrArg (fun φ ↦ (K.cartanEilenbergResolution q).ι₀ ≫ φ.f 0) (K.cartanEilenberg_d q)).trans
        (K.cartanEilenbergResolution_ι₀_comp_cartanEilenbergD_f q))).trans (G.map_comp _ _))

lemma mapCartanEilenbergCoaugmentation_comp_d :
    K.mapCartanEilenbergCoaugmentation G ≫ (K.mapCartanEilenberg G).flip.d 0 1 = 0 := by
  ext q
  exact (G.map_comp _ _).symm.trans ((congrArg G.map
    (K.cartanEilenbergResolution q).ι₀_comp_d).trans (G.map_zero _ _))

variable [PreservesFiniteLimits G]

/-- **`G(K)` computes the cohomology of `Tot G(J)`**: if `G` is left exact and every term of `K` is
`G`-acyclic, the coaugmentation `G(K) ⟶ Tot G(J)` is a quasi-isomorphism. -/
theorem quasiIso_totalCoaugmentation_mapCartanEilenberg
    (hK : ∀ q n, IsZero ((G.rightDerived (n + 1)).obj (K.X q))) :
    QuasiIso ((K.mapCartanEilenberg G).flip.totalCoaugmentation
      (K.mapCartanEilenbergCoaugmentation G) (K.mapCartanEilenbergCoaugmentation_comp_d G)) := by
  refine HomologicalComplex₂.quasiIso_totalCoaugmentation _ _ _ fun q ↦
    (K.cartanEilenbergResolution q).quasiIso_of_isZero_rightDerived G (hK q) _
      -- The row `q` of the flipped bicomplex is `G(J(Kᵠ))` by definition.
      (HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _)
        (fun _ _ _ ↦ (id_comp _).trans (comp_id _).symm))
      ((comp_id _).trans (HomologicalComplex₂.rowCoaugmentation_f_zero _ _ _ q))

/-- **The abutment of the Cartan–Eilenberg spectral sequence**: if `G` is left exact and every
term of `K` is `G`-acyclic, the spectral sequence converges to the cohomology of `G(K)`. -/
noncomputable def cartanEilenbergSpectralSequenceAbutmentIso
    (hK : ∀ q n, IsZero ((G.rightDerived (n + 1)).obj (K.X q))) (n : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor
      (K.mapCartanEilenberg G).rowFiltrationUp
        (K.mapCartanEilenberg G).monotone_rowFiltrationUp)).abutment n ≅
      ((G.mapHomologicalComplex _).obj K).homology n :=
  have := K.quasiIso_totalCoaugmentation_mapCartanEilenberg G hK
  (K.mapCartanEilenberg G).rowFiltrationUpAbutmentIso n ≪≫
    HomologicalComplex.homologyMapIso
      ((K.mapCartanEilenberg G).totalFlipIso (up ℕ)).symm n ≪≫
    (isoOfQuasiIsoAt ((K.mapCartanEilenberg G).flip.totalCoaugmentation
      (K.mapCartanEilenbergCoaugmentation G) (K.mapCartanEilenbergCoaugmentation_comp_d G)) n).symm

end CochainComplex
