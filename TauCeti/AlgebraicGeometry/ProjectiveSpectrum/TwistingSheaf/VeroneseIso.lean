/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Veronese
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Veronese

/-!
# Twisting sheaves of `Proj` of a Veronese subalgebra

Let `A = ⨁ₙ 𝒜 n` be an `ℕ`-graded commutative `R`-algebra, `d ≠ 0`, and `A^{(d)} = ⨁ₖ 𝒜 (d k)`
its Veronese subalgebra. The isomorphism `Proj A^{(d)} ≅ Proj A` of
`AlgebraicGeometry.Proj.veroneseIso` is glued from affine charts. Here we identify its inverse
`AlgebraicGeometry.Proj.toVeronese` on points with the contraction `q ↦ q ∩ A^{(d)}` of
`AlgebraicGeometry.ProjectiveSpectrum.veroneseComap`, along which the twisting sheaf sections
`Γ(U, 𝒪_{Proj A^{(d)}}(n)) → Γ(V, 𝒪_{Proj A}(d n))` are pulled back.

## Main results

* `AlgebraicGeometry.Proj.toVeronese_apply`: on points, `toVeronese` is the contraction
  `q ↦ q ∩ A^{(d)}`.
* `AlgebraicGeometry.Proj.coe_toVeronese_preimage`,
  `AlgebraicGeometry.Proj.veroneseComap_fromVeronese_apply`: its consequences for preimages of
  opens and for `fromVeronese`.
* `AlgebraicGeometry.Proj.awayToSection_comp_toVeronese_appLE`: on sections over `D₊(g)`,
  `toVeronese` is the isomorphism `A^{(d)}_{(g)} ≃ A_{(g)}` of
  `TauCeti.GradedAlgebra.awayVeroneseEquiv`.

## References

* [Stacks, Lemma 27.11.8 (0B5J)](https://stacks.math.columbia.edu/tag/0B5J)
-/

@[expose] public section

open CategoryTheory TauCeti.GradedAlgebra

namespace AlgebraicGeometry.Proj

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜]

/-- On `D₊(f) ≅ Spec A_{(f)}`, the chart `AlgebraicGeometry.Proj.awayι` pulls the section
`AlgebraicGeometry.Proj.awayToSection` of `a ∈ A_{(f)}` back to the global function `a` on
`Spec A_{(f)}`. -/
theorem awayToSection_comp_awayι_appLE {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    (e : ⊤ ≤ awayι 𝒜 f f_deg hm ⁻¹ᵁ basicOpen 𝒜 f) :
    awayToSection 𝒜 f ≫ (awayι 𝒜 f f_deg hm).appLE (basicOpen 𝒜 f) ⊤ e =
      (Scheme.ΓSpecIso _).inv := by
  -- `awayToSection` is invertible, and a left inverse is `awayι` followed by `Γ(Spec -) ≅ -`
  have := (basicOpenIsoAway 𝒜 f f_deg hm).isIso_hom
  rw [basicOpenIsoAway_hom] at this
  rw [← IsIso.eq_inv_comp, Iso.eq_comp_inv]
  refine IsIso.eq_inv_of_inv_hom_id ?_
  rw [← cancel_mono (basicOpen 𝒜 f).topIso.inv]
  simp only [Category.assoc, Category.id_comp]
  rw [← basicOpenToSpec_app_top, ← basicOpenIsoSpec_hom 𝒜 f f_deg hm, Scheme.Hom.app_eq_appLE]
  -- composing the chart with `D₊(f) ≅ Spec A_{(f)}` gives the inclusion of `D₊(f)`
  refine (Scheme.Hom.appLE_comp_appLE _ (awayι 𝒜 f f_deg hm) _ ⊤ _ e le_rfl).trans ?_
  simp only [awayι, Iso.hom_inv_id_assoc]
  rfl

variable {d : ℕ} [NeZero d]

/-- **On points, `AlgebraicGeometry.Proj.toVeronese` is the contraction** `q ↦ q ∩ A^{(d)}`. Both
primes miss some homogeneous `g ∈ A^{(d)}` of positive degree, and by
`AlgebraicGeometry.Proj.toVeronese_preimage_basicOpen` they contain the same homogeneous
elements of positive degree; multiplying by `g` reduces every degree to a positive one. -/
theorem toVeronese_apply (x : Proj 𝒜) :
    toVeronese 𝒜 d x = ProjectiveSpectrum.veroneseComap 𝒜 d x := by
  obtain ⟨⟨k₀, g, hg⟩, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_basicOpen_veronese_eq_top 𝒜 d).ge (Set.mem_univ x))
  have key {k : ℕ} {a : veronese 𝒜 d} (ha : a ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) :
      a ∈ (toVeronese 𝒜 d x).asHomogeneousIdeal ↔ (a : A) ∈ x.asHomogeneousIdeal := by
    have := congrArg (x ∈ ·) (toVeronese_preimage_basicOpen ha hk)
    simp only [eq_iff_iff] at this
    exact not_iff_not.mp ((mem_basicOpen _ _ _).symm.trans (this.trans (mem_basicOpen _ _ _)))
  have hgx : (g : A) ∉ x.asHomogeneousIdeal := (mem_basicOpen _ _ _).1 hx
  have hgy : g ∉ (toVeronese 𝒜 d x).asHomogeneousIdeal := fun h ↦ hgx ((key hg k₀.pos).1 h)
  refine ProjectiveSpectrum.ext (HomogeneousIdeal.ext' fun k a ha ↦ ?_)
  have hag := key (SetLike.mul_mem_graded ha hg) (Nat.add_pos_right k k₀.pos)
  change a ∈ (toVeronese 𝒜 d x).asHomogeneousIdeal ↔ (a : A) ∈ x.asHomogeneousIdeal
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (x.isPrime.mem_or_mem (hag.1 (Ideal.mul_mem_right _ _ h))).resolve_right hgx
  · exact ((toVeronese 𝒜 d x).isPrime.mem_or_mem
      (hag.2 (Ideal.mul_mem_right (g : A) x.asHomogeneousIdeal.toIdeal h))).resolve_right hgy

/-- The preimage of an open `U ⊆ Proj A^{(d)}` under `AlgebraicGeometry.Proj.toVeronese` is its
preimage under the contraction `q ↦ q ∩ A^{(d)}`. -/
theorem coe_toVeronese_preimage (U : (Proj (veroneseGrading 𝒜 d)).Opens) :
    (toVeronese 𝒜 d ⁻¹ᵁ U).1 = ProjectiveSpectrum.veroneseComap 𝒜 d ⁻¹' U.1 :=
  Set.ext fun x ↦ show toVeronese 𝒜 d x ∈ U ↔ _ by rw [toVeronese_apply]; rfl

/-- The contraction `q ↦ q ∩ A^{(d)}` inverts `AlgebraicGeometry.Proj.fromVeronese` on
points. -/
@[simp]
theorem veroneseComap_fromVeronese_apply (p : Proj (veroneseGrading 𝒜 d)) :
    ProjectiveSpectrum.veroneseComap 𝒜 d (fromVeronese 𝒜 d p) = p := by
  rw [← toVeronese_apply, ← Scheme.Hom.comp_apply]
  exact congrArg (fun f : Proj (veroneseGrading 𝒜 d) ⟶ _ ↦ f p) (veroneseIso 𝒜 d).hom_inv_id

variable {g : veronese 𝒜 d} {k : ℕ}

/-- **On sections over `D₊(g)`, `AlgebraicGeometry.Proj.toVeronese` is
`TauCeti.GradedAlgebra.awayVeroneseEquiv`**: for `g ∈ A^{(d)}` homogeneous of positive degree,
the section of `A^{(d)}_{(g)}` over `D₊(g) ⊆ Proj A^{(d)}` pulls back to the section of its image
in `A_{(g)}` over `D₊(g) ⊆ Proj A`. This is the analogue of Mathlib's
`AlgebraicGeometry.Proj.awayToSection_comp_appLE` for the glued morphism `toVeronese`; it follows
from `AlgebraicGeometry.Proj.awayι_toVeronese` by cancelling the isomorphism `Γ(Proj A, D₊(g)) ≅
Γ(Spec A_{(g)}, ⊤)`. -/
@[reassoc]
theorem awayToSection_comp_toVeronese_appLE (hg : g ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) :
    awayToSection (veroneseGrading 𝒜 d) g ≫ (toVeronese 𝒜 d).appLE (basicOpen _ g)
        (basicOpen 𝒜 (g : A)) (toVeronese_preimage_basicOpen hg hk).ge =
      CommRingCat.ofHom (awayVeroneseEquiv hg : _ →+* _) ≫ awayToSection 𝒜 (g : A) := by
  have hg' := mem_veroneseGrading.1 hg
  have hdk := Nat.mul_pos (NeZero.pos d) hk
  have e : ⊤ ≤ awayι 𝒜 (g : A) hg' hdk ⁻¹ᵁ basicOpen 𝒜 (g : A) := by
    rw [← opensRange_awayι 𝒜 _ hg' hdk]; exact fun x _ ↦ ⟨x, rfl⟩
  have e' : ⊤ ≤ awayι (veroneseGrading 𝒜 d) g hg hk ⁻¹ᵁ basicOpen _ g := by
    rw [← opensRange_awayι _ _ hg hk]; exact fun x _ ↦ ⟨x, rfl⟩
  have := (basicOpenIsoAway 𝒜 _ hg' hdk).isIso_hom
  rw [basicOpenIsoAway_hom] at this
  have : IsIso ((awayι 𝒜 (g : A) hg' hdk).appLE (basicOpen 𝒜 (g : A)) ⊤ e) := by
    rw [(IsIso.eq_inv_comp _).2 (awayToSection_comp_awayι_appLE hg' hdk e)]
    infer_instance
  -- both sides, followed by the chart of `g` on sections, are the global functions on
  -- `Spec A_{(g)}`, by `awayι_toVeronese` and `awayToSection_comp_awayι_appLE` on both sides
  rw [← cancel_mono ((awayι 𝒜 (g : A) hg' hdk).appLE (basicOpen 𝒜 (g : A)) ⊤ e), Category.assoc,
    Category.assoc, awayToSection_comp_awayι_appLE, Scheme.Hom.appLE_comp_appLE,
    Scheme.ΓSpecIso_inv_naturality, ← awayToSection_comp_awayι_appLE hg hk e', Category.assoc]
  congr 1
  -- `rw [awayι_toVeronese]` is blocked by the inclusion proof that `appLE` carries
  have hcongr : ∀ (φ ψ : Spec (.of (HomogeneousLocalization.Away 𝒜 (g : A))) ⟶
      Proj (veroneseGrading 𝒜 d)) (h : φ = ψ) (e₁ : ⊤ ≤ φ ⁻¹ᵁ basicOpen _ g),
      φ.appLE (basicOpen _ g) ⊤ e₁ = ψ.appLE (basicOpen _ g) ⊤ (h ▸ e₁) := by
    rintro _ _ rfl _; rfl
  refine (hcongr _ _ (awayι_toVeronese hg hk) _).trans ?_
  unfold veroneseChart
  refine (Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ ⊤ e' le_rfl).symm.trans ?_
  congr 1

end AlgebraicGeometry.Proj
