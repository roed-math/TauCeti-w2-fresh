/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.BasicOpen
public import TauCeti.RingTheory.GradedAlgebra.VeroneseSubalgebra

/-!
# Twisting sheaves and Veronese subalgebras

Let `A = ⨁ₙ 𝒜 n` be an `ℕ`-graded commutative `R`-algebra, `d ≠ 0`, and let
`A^{(d)} = ⨁ₖ 𝒜 (d k)` be its Veronese subalgebra (`TauCeti.GradedAlgebra.veroneseGrading`).
A homogeneous prime `q` of `A` that is relevant contracts to the relevant homogeneous prime
`q ∩ A^{(d)}` of `A^{(d)}`. This gives a continuous map
`AlgebraicGeometry.ProjectiveSpectrum.veroneseComap : Proj A → Proj A^{(d)}` on the level of
points. Mathematically it is the inverse, on points, of the isomorphism
`Proj A^{(d)} ≅ Proj A` of `AlgebraicGeometry.Proj.veroneseIso`.

Over it, a local fraction `r / s` of degree `n` for `A^{(d)}` (so `r ∈ 𝒜 (d j)`, `s ∈ 𝒜 (d i)` and
`j = i + n`) is a local fraction of degree `d n` for `A`. We construct the induced pullback of
sections of twisting sheaves

`Γ(U, 𝒪_{Proj A^{(d)}}(n)) → Γ(V, 𝒪_{Proj A}(d n))`

for `V` contained in the preimage of `U` (`AlgebraicGeometry.Proj.twistingSheaf.comapVeronese`):
it applies the maps of localizations `A^{(d)}_{q ∩ A^{(d)}} → A_q` pointwise. This is the map
underlying the identification of `𝒪(n)` on `Proj A^{(d)}` with `𝒪(d n)` on `Proj A`
(Stacks, Lemma 27.11.8 (0B5J)). Over a standard open `D₊(g)`, `g ∈ A^{(d)}` homogeneous of
positive degree, it is bijective
(`AlgebraicGeometry.Proj.twistingSheaf.bijective_comapVeronese_basicOpen`): both sides are the
fractions `r / gᵏ` with `r ∈ 𝒜 (d (k deg g + n))`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpectrum.veroneseComap 𝒜 d`: the contraction
  `Proj A → Proj A^{(d)}`, `q ↦ q ∩ A^{(d)}`, as a continuous map.
* `AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.veroneseLocalizationsMap`: the map of
  localizations `A^{(d)}_{q ∩ A^{(d)}} → A_q`.
* `AlgebraicGeometry.Proj.twistingSheaf.comapVeronese`: the pullback of sections
  `Γ(U, 𝒪_{Proj A^{(d)}}(n)) → Γ(V, 𝒪_{Proj A}(d n))`.

## Main results

* `AlgebraicGeometry.Proj.twistingSheaf.bijective_comapVeronese_basicOpen`: the pullback of
  sections over a standard open `D₊(g)` is bijective.

## References

* [Stacks, Lemma 27.11.8 (0B5J)](https://stacks.math.columbia.edu/tag/0B5J)
-/

@[expose] public section

noncomputable section

namespace AlgebraicGeometry

open CategoryTheory TopologicalSpace TauCeti.GradedAlgebra ProjectiveSpectrum.TwistingSheaf

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : ℕ) [NeZero d]

namespace ProjectiveSpectrum

/-- The contraction `q ∩ A^{(d)}` of a homogeneous prime `q` of `A` to the Veronese subalgebra:
a relevant homogeneous prime of `A^{(d)}`. -/
def veroneseComapFun (q : ProjectiveSpectrum 𝒜) : ProjectiveSpectrum (veroneseGrading 𝒜 d) where
  asHomogeneousIdeal :=
    { toSubmodule := q.asHomogeneousIdeal.toIdeal.comap (veronese 𝒜 d).val
      is_homogeneous' := by
        intro k x hx
        change ((DirectSum.decompose (veroneseGrading 𝒜 d) x k : veronese 𝒜 d) : A) ∈
          q.asHomogeneousIdeal
        rw [coe_decompose_veroneseGrading]
        exact q.asHomogeneousIdeal.2 (d * k) hx }
  isPrime := q.isPrime.comap _
  not_irrelevant_le le := q.not_irrelevant_le <| (HomogeneousIdeal.irrelevant_le _).2
    fun i hi a (ha : a ∈ 𝒜 i) ↦
    -- `a ^ d` lies in degree `i > 0` of `A^{(d)}`, hence in `q`, and `q` is prime.
    q.isPrime.mem_of_pow_mem d <| le (HomogeneousIdeal.mem_irrelevant_of_mem _ hi
      (show (⟨a ^ d, mem_veronese_of_mem (SetLike.pow_mem_graded d ha)⟩ : veronese 𝒜 d) ∈
        veroneseGrading 𝒜 d i from SetLike.pow_mem_graded d ha))

/-- **The contraction to a Veronese subalgebra** `Proj A → Proj A^{(d)}`, `q ↦ q ∩ A^{(d)}`, as a
continuous map: the preimage of the zero locus of `s ⊆ A^{(d)}` is the zero locus of `s` in `A`. -/
def veroneseComap : C(ProjectiveSpectrum 𝒜, ProjectiveSpectrum (veroneseGrading 𝒜 d)) where
  toFun := veroneseComapFun 𝒜 d
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, _root_.ProjectiveSpectrum.isClosed_iff_zeroLocus, exists_imp,
      forall_eq_apply_imp_iff]
    exact fun s ↦ ⟨Subtype.val '' s, by ext; simp [Set.image_subset_iff]; rfl⟩

/-- The ideal of the contraction `q ∩ A^{(d)}` is the preimage of the ideal of `q`. -/
@[simp]
theorem veroneseComap_asHomogeneousIdeal_toIdeal (q : ProjectiveSpectrum 𝒜) :
    (veroneseComap 𝒜 d q).asHomogeneousIdeal.toIdeal =
      q.asHomogeneousIdeal.toIdeal.comap (veronese 𝒜 d).val :=
  rfl

variable {𝒜 d}

namespace TwistingSheaf

/-- The map of localizations `A^{(d)}_{q ∩ A^{(d)}} → A_q` induced by the inclusion
`A^{(d)} → A`, at a point `q` of `Proj A`. -/
def veroneseLocalizationsMap (q : ProjectiveSpectrum 𝒜) :
    Localizations (veroneseGrading 𝒜 d) (veroneseComap 𝒜 d q) →+* Localizations 𝒜 q :=
  Localization.localRingHom _ _ (veronese 𝒜 d).val.toRingHom rfl

/-- The map of localizations sends the fraction `r / s` to the same fraction in `A_q`. -/
@[simp]
theorem veroneseLocalizationsMap_mk (q : ProjectiveSpectrum 𝒜) (r : veronese 𝒜 d)
    (s : (veroneseComap 𝒜 d q).asHomogeneousIdeal.toIdeal.primeCompl) :
    veroneseLocalizationsMap q (Localization.mk r s) =
      Localization.mk (r : A) ⟨(s : veronese 𝒜 d), s.2⟩ :=
  Localization.localRingHom_mk ..

variable {U : Opens (ProjectiveSpectrum.top (veroneseGrading 𝒜 d))}
  {V : Opens (ProjectiveSpectrum.top 𝒜)} (hUV : V.1 ⊆ veroneseComap 𝒜 d ⁻¹' U.1)

/-- The pullback of a dependent function on `U ⊆ Proj A^{(d)}` into the localizations along the
contraction: the value at `q ∈ V` is the image of the value at `q ∩ A^{(d)}` in `A_q`. -/
def comapVeroneseFun (s : ∀ x : U, Localizations (veroneseGrading 𝒜 d) x.1) (q : V) :
    Localizations 𝒜 q.1 :=
  veroneseLocalizationsMap q.1 (s ⟨veroneseComap 𝒜 d q.1, hUV q.2⟩)

variable {hUV} in
/-- The pullback of a local fraction of degree `n` over `A^{(d)}` is a local fraction of degree
`d n` over `A`. -/
theorem isLocallyFraction_comapVeroneseFun {n : ℤ}
    {s : ∀ x : U, Localizations (veroneseGrading 𝒜 d) x.1}
    (hs : (isLocallyFraction (veroneseGrading 𝒜 d) n).pred s) :
    (isLocallyFraction 𝒜 (d * n)).pred (comapVeroneseFun hUV s) := by
  rintro ⟨q, hqV⟩
  obtain ⟨W, m, iWU, i, j, h, r, t, ht, w⟩ := hs ⟨veroneseComap 𝒜 d q, hUV hqV⟩
  refine ⟨W.comap (veroneseComap 𝒜 d) ⊓ V, ⟨m, hqV⟩, homOfLE inf_le_right, d * i, d * j,
    by push_cast; rw [h]; ring, ⟨((r : veronese 𝒜 d) : A), r.2⟩,
    ⟨((t : veronese 𝒜 d) : A), t.2⟩, fun z ↦ ht ⟨veroneseComap 𝒜 d z.1, z.2.1⟩, fun z ↦ ?_⟩
  exact (congrArg (veroneseLocalizationsMap z.1) (w ⟨_, z.2.1⟩)).trans
    (veroneseLocalizationsMap_mk ..)

end TwistingSheaf

end ProjectiveSpectrum

namespace Proj

namespace twistingSheaf

variable {𝒜 d} {n : ℤ} {U : (Proj (veroneseGrading 𝒜 d)).Opens} {V : (Proj 𝒜).Opens}
  (hUV : V.1 ⊆ ProjectiveSpectrum.veroneseComap 𝒜 d ⁻¹' U.1)

/-- **Pullback of sections of twisting sheaves along the Veronese contraction**: for `V ⊆ Proj A`
contained in the preimage of `U ⊆ Proj A^{(d)}`, the map
`Γ(U, 𝒪_{Proj A^{(d)}}(n)) → Γ(V, 𝒪_{Proj A}(d n))` applying the maps of localizations
`A^{(d)}_{q ∩ A^{(d)}} → A_q` pointwise. -/
def comapVeronese :
    Γ(twistingSheaf (veroneseGrading 𝒜 d) n, U) →+ Γ(twistingSheaf 𝒜 (d * n), V) where
  toFun s := ⟨comapVeroneseFun hUV s.1, isLocallyFraction_comapVeroneseFun s.2⟩
  map_zero' := ext fun _ ↦ map_zero _
  map_add' _ _ := ext fun _ ↦ map_add _ _ _

/-- The value of a pulled-back section at `q` is the image of its value at `q ∩ A^{(d)}`. -/
@[simp]
theorem comapVeronese_apply (s : Γ(twistingSheaf (veroneseGrading 𝒜 d) n, U)) (q : V) :
    (comapVeronese hUV s).1 q =
      veroneseLocalizationsMap q.1
        (s.1 (⟨ProjectiveSpectrum.veroneseComap 𝒜 d q.1, hUV q.2⟩ : U)) :=
  (rfl)

/-- The pullback along the Veronese contraction commutes with restriction. -/
@[simp]
theorem res_comapVeronese {V' : (Proj 𝒜).Opens} (i : V' ⟶ V)
    (s : Γ(twistingSheaf (veroneseGrading 𝒜 d) n, U)) :
    (twistingSheaf 𝒜 (d * n)).presheaf.map i.op (comapVeronese hUV s) =
      comapVeronese (fun _ hy ↦ hUV (i.le hy)) s :=
  (rfl)

/-- Pulling back the restriction of a section along the Veronese contraction is pulling back the
section. -/
@[simp]
theorem comapVeronese_res {U' : (Proj (veroneseGrading 𝒜 d)).Opens} (i : U' ⟶ U)
    (hU'V : V.1 ⊆ ProjectiveSpectrum.veroneseComap 𝒜 d ⁻¹' U'.1)
    (s : Γ(twistingSheaf (veroneseGrading 𝒜 d) n, U)) :
    comapVeronese hU'V ((twistingSheaf (veroneseGrading 𝒜 d) n).presheaf.map i.op s) =
      comapVeronese (hU'V.trans fun _ hy ↦ i.le hy) s :=
  (rfl)

/-- The pullback of the fraction `r / s` of degree `n` over `A^{(d)}` is the same fraction, of
degree `d n`, over `A`. -/
@[simp]
theorem comapVeronese_const {i j : ℕ} (h : (j : ℤ) = i + n) (r s : veronese 𝒜 d)
    (hr : r ∈ veroneseGrading 𝒜 d j) (hs : s ∈ veroneseGrading 𝒜 d i)
    (hU : U ≤ ProjectiveSpectrum.basicOpen _ s) :
    comapVeronese hUV (const h r s hr hs U hU) =
      const (i := d * i) (j := d * j) (by push_cast; rw [h]; ring) (r : A) (s : A) hr hs V
        fun _ hq ↦ hU (hUV hq) := by
  refine ext fun (q : V) ↦ ?_
  simp only [comapVeronese_apply]
  exact veroneseLocalizationsMap_mk ..

/-- The pullback along the Veronese contraction is multiplicative: the product of sections of
degrees `m` and `n` over `A^{(d)}` pulls back to the product of their pullbacks, of degrees `d m`
and `d n` over `A`. -/
theorem comapVeronese_mul_apply {m : ℤ} (s : Γ(twistingSheaf (veroneseGrading 𝒜 d) m, U))
    (t : Γ(twistingSheaf (veroneseGrading 𝒜 d) n, U)) (q : V) :
    (comapVeronese hUV (mul _ U m n s t)).1 q =
      (mul 𝒜 V (d * m) (d * n) (comapVeronese hUV s) (comapVeronese hUV t)).1 q := by
  simp only [comapVeronese_apply, mul_apply, map_mul]

variable {e : ℕ} {g : veronese 𝒜 d}

variable (𝒜 d g) in
/-- The preimage of `D₊(g) ⊆ Proj A^{(d)}` under the Veronese contraction contains (in fact is)
`D₊(g) ⊆ Proj A`. -/
theorem basicOpen_subset_preimage_veroneseComap :
    (basicOpen 𝒜 (g : A)).1 ⊆
      ProjectiveSpectrum.veroneseComap 𝒜 d ⁻¹' (basicOpen (veroneseGrading 𝒜 d) g).1 :=
  fun _ hq ↦ hq

/-- **Pullback along the Veronese contraction is bijective on standard opens.** For `g ∈ A^{(d)}`
homogeneous of positive degree, the preimage of `D₊(g) ⊆ Proj A^{(d)}` is `D₊(g) ⊆ Proj A`, and
the pullback `Γ(D₊(g), 𝒪_{Proj A^{(d)}}(n)) → Γ(D₊(g), 𝒪_{Proj A}(d n))` is bijective: both sides
are the fractions `r / gᵏ` with `r ∈ 𝒜 (d (k deg g + n))`. -/
theorem bijective_comapVeronese_basicOpen (hg : g ∈ veroneseGrading 𝒜 d e) (he : 0 < e) :
    Function.Bijective (comapVeronese (n := n) (U := basicOpen (veroneseGrading 𝒜 d) g)
      (V := basicOpen 𝒜 (g : A)) (basicOpen_subset_preimage_veroneseComap 𝒜 d g)) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hgA : (g : A) ∈ 𝒜 (d * e) := hg
  have hde : 0 < d * e := Nat.mul_pos hd he
  refine ⟨(injective_iff_map_eq_zero _).2 fun s hs ↦ ?_, fun t ↦ ?_⟩
  · obtain ⟨k, j, h, r, hr, rfl⟩ := exists_eq_const_basicOpen (𝒜 := veroneseGrading 𝒜 d) hg he s
    obtain ⟨N, hN⟩ := (const_eq_zero_iff (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hde hgA) ..).1
      ((comapVeronese_const ..).symm.trans hs)
    exact (const_eq_zero_iff (HomogeneousIdeal.mem_irrelevant_of_mem _ he hg) ..).2
      ⟨N, Subtype.ext (by simpa using hN)⟩
  · obtain ⟨k, j, h, r, hr, rfl⟩ := exists_eq_const_basicOpen (𝒜 := 𝒜) hgA hde t
    -- the numerator has degree `j = d (k e + n)`, so it lies in `A^{(d)}`
    have hnn : (0 : ℤ) ≤ k * e + n := by
      have hj := Int.natCast_nonneg j
      push_cast at h
      nlinarith
    have hj' : ((k * e + n).toNat : ℤ) = k * e + n := Int.toNat_of_nonneg hnn
    have hjd : j = d * (k * e + n).toNat := by
      exact_mod_cast (show (j : ℤ) = d * (k * e + n).toNat by rw [h, hj']; push_cast; ring)
    have hr' : r ∈ 𝒜 (d * (k * e + n).toNat) := hjd ▸ hr
    have hgk : g ^ k ∈ veroneseGrading 𝒜 d (k * e) := by
      simpa [mul_comm] using SetLike.pow_mem_graded k hg
    refine ⟨const (i := k * e) (j := (k * e + n).toNat) (by rw [hj']; push_cast; ring)
      ⟨r, mem_veronese_of_mem hr'⟩ (g ^ k) hr' hgk _
      fun x hx hgk ↦ hx (x.isPrime.mem_of_pow_mem k hgk), ?_⟩
    exact (comapVeronese_const ..).trans (const_ext (by simp [mul_comm]))

end twistingSheaf

end Proj

end AlgebraicGeometry
