/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Veronese
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Veronese
public import TauCeti.AlgebraicGeometry.Modules.Sheaf

/-!
# Twisting sheaves of `Proj` of a Veronese subalgebra

Let `A = ⨁ₙ 𝒜 n` be an `ℕ`-graded commutative `R`-algebra, `d ≠ 0`, and `A^{(d)} = ⨁ₖ 𝒜 (d k)`
its Veronese subalgebra. The isomorphism `Proj A^{(d)} ≅ Proj A` of
`AlgebraicGeometry.Proj.veroneseIso` is glued from affine charts. Here we identify its inverse
`AlgebraicGeometry.Proj.toVeronese` on points with the contraction `q ↦ q ∩ A^{(d)}` of
`AlgebraicGeometry.ProjectiveSpectrum.veroneseComap`, along which the twisting sheaf sections
`Γ(U, 𝒪_{Proj A^{(d)}}(n)) → Γ(V, 𝒪_{Proj A}(d n))` are pulled back, and deduce that
`𝒪_{Proj A^{(d)}}(n)` corresponds to `𝒪_{Proj A}(d n)`.

## Main results

* `AlgebraicGeometry.Proj.toVeronese_apply`: on points, `toVeronese` is the contraction
  `q ↦ q ∩ A^{(d)}`.
* `AlgebraicGeometry.Proj.coe_toVeronese_preimage`,
  `AlgebraicGeometry.Proj.veroneseComap_fromVeronese_apply`: its consequences for preimages of
  opens and for `fromVeronese`.
* `AlgebraicGeometry.Proj.awayToSection_comp_toVeronese_appLE`: on sections over `D₊(g)`,
  `toVeronese` is the isomorphism `A^{(d)}_{(g)} ≃ A_{(g)}` of
  `TauCeti.GradedAlgebra.awayVeroneseEquiv`.
* `AlgebraicGeometry.Proj.isBasis_basicOpen_veronese`: the `D₊(g)`, `g ∈ A^{(d)}` homogeneous of
  positive degree, form a basis of `Proj A^{(d)}`.
* `AlgebraicGeometry.Proj.val_toVeronese_appLE_apply`: on sections, `toVeronese` is pointwise the
  map of localizations `A^{(d)}_{q ∩ A^{(d)}} → A_q`.
* `AlgebraicGeometry.Proj.twistingSheafVeroneseIso`: the isomorphism
  `𝒪_{Proj A^{(d)}}(n) ≅ (toVeronese)_* 𝒪_{Proj A}(d n)`, given on sections by
  `AlgebraicGeometry.Proj.twistingSheaf.comapVeronese`.

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

variable (𝒜 d) in
/-- The `D₊(g)`, for `g ∈ A^{(d)}` homogeneous of positive degree, form a basis of the topology
of `Proj A^{(d)}`: every point lies in such a `D₊(g)` inside any given neighbourhood. -/
theorem isBasis_basicOpen_veronese :
    TopologicalSpace.Opens.IsBasis (Set.range fun g : Σ k : ℕ+, veroneseGrading 𝒜 d k ↦
      basicOpen (veroneseGrading 𝒜 d) (g.2 : veronese 𝒜 d)) := by
  refine TopologicalSpace.Opens.isBasis_iff_nbhd.2 fun {U x} hx ↦ ?_
  obtain ⟨⟨k₀, g₀, hg₀⟩, hyg₀⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_basicOpen_veronese_eq_top 𝒜 d).ge (Set.mem_univ (fromVeronese 𝒜 d x)))
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen (veroneseGrading 𝒜 d)) hx
  rw [basicOpen_eq_iSup_proj] at hxf
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxf
  refine ⟨_, ⟨⟨(⟨i + k₀, Nat.add_pos_right i k₀.pos⟩ : ℕ+), _,
    SetLike.mul_mem_graded (Submodule.coe_mem (DirectSum.decompose _ f i)) hg₀⟩, rfl⟩, ?_, ?_⟩ <;>
    dsimp only <;> rw [basicOpen_mul]
  · refine ⟨hxi, (mem_basicOpen _ _ _).2 fun h ↦ (mem_basicOpen _ _ _).1 hyg₀ ?_⟩
    rw [← veroneseComap_fromVeronese_apply x] at h
    exact h
  · exact inf_le_left.trans ((le_iSup (fun i ↦ basicOpen _ (GradedRing.proj _ i f)) i).trans
      ((basicOpen_eq_iSup_proj _ f).ge.trans hfU))

open ProjectiveSpectrum.TwistingSheaf in
/-- **On sections, `AlgebraicGeometry.Proj.toVeronese` is the map of localizations**
`A^{(d)}_{q ∩ A^{(d)}} → A_q` at every point `q`: the analogue of
`AlgebraicGeometry.Proj.val_map_appLE_apply` for the glued morphism `toVeronese`. Near `q`, a
section over `U` is the image of some `c ∈ A^{(d)}_{(g)}` on `D₊(g) ⊆ U`, and on `D₊(g)` the
morphism `toVeronese` is `TauCeti.GradedAlgebra.awayVeroneseEquiv` by
`AlgebraicGeometry.Proj.awayToSection_comp_toVeronese_appLE`. -/
theorem val_toVeronese_appLE_apply {U : (Proj (veroneseGrading 𝒜 d)).Opens}
    {V : (Proj 𝒜).Opens} (hUV : V ≤ toVeronese 𝒜 d ⁻¹ᵁ U) (a : Γ(Proj (veroneseGrading 𝒜 d), U))
    (y : V) :
    (((toVeronese 𝒜 d).appLE U V hUV a).1 y).val = veroneseLocalizationsMap y.1
      (a.1 ⟨_, (coe_toVeronese_preimage U).subset (hUV y.2)⟩).val := by
  have hxU := (coe_toVeronese_preimage U).subset (hUV y.2)
  -- a homogeneous `g ∈ A^{(d)}` of positive degree with `q ∩ A^{(d)} ∈ D₊(g) ⊆ U`
  obtain ⟨_, ⟨⟨k, g, hg⟩, rfl⟩, hxg, hgU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen_veronese 𝒜 d) hxU
  have hk := k.pos
  have hy : y.1 ∈ basicOpen 𝒜 (g : A) :=
    (toVeronese_preimage_basicOpen hg hk).le (show toVeronese 𝒜 d y.1 ∈ basicOpen _ g by
      rw [toVeronese_apply]; exact hxg)
  -- the restriction of `a` to `D₊(g)` comes from some `c ∈ A^{(d)}_{(g)}`
  have := (basicOpenIsoAway _ g hg hk).isIso_hom
  rw [basicOpenIsoAway_hom] at this
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (awayToSection _ g)).2
    ((Proj (veroneseGrading 𝒜 d)).presheaf.map (homOfLE hgU).op a)
  let W : (Proj 𝒜).Opens := V ⊓ basicOpen 𝒜 (g : A)
  have e₁ := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_map (toVeronese 𝒜 d) hUV (homOfLE (inf_le_left : W ≤ V)).op) a
  have e₂ := ConcreteCategory.congr_hom (Scheme.Hom.map_appLE (toVeronese 𝒜 d)
    (inf_le_right.trans (toVeronese_preimage_basicOpen hg hk).ge : W ≤ _) (homOfLE hgU).op) a
  have e₃ := ConcreteCategory.congr_hom (Scheme.Hom.appLE_map (toVeronese 𝒜 d)
    (toVeronese_preimage_basicOpen hg hk).ge (homOfLE (inf_le_right : W ≤ _)).op)
    (awayToSection _ g c)
  have e₄ := ConcreteCategory.congr_hom (awayToSection_comp_toVeronese_appLE hg hk) c
  simp only [ConcreteCategory.comp_apply] at e₁ e₂ e₃ e₄
  have ev {W' : (Proj 𝒜).Opens} (hW' : y.1 ∈ W') {s t : Γ(Proj 𝒜, W')} (h : s = t) :
      (s.1 ⟨y.1, hW'⟩).val = (t.1 ⟨y.1, hW'⟩).val :=
    congrArg (fun s : Γ(Proj 𝒜, W') ↦ (s.1 ⟨y.1, hW'⟩).val) h
  have res {W₁ W₂ : (Proj 𝒜).Opens} (i : W₁ ≤ W₂) (h₁ : y.1 ∈ W₁) (s : Γ(Proj 𝒜, W₂)) :
      (((Proj 𝒜).presheaf.map (homOfLE i).op s).1 ⟨y.1, h₁⟩).val = (s.1 ⟨y.1, i h₁⟩).val :=
    rfl
  have hl : (((toVeronese 𝒜 d).appLE U V hUV a).1 y).val =
      ((awayToSection 𝒜 (g : A) (awayVeroneseEquiv hg c)).1 ⟨y.1, hy⟩).val :=
    (res inf_le_left ⟨y.2, hy⟩ _).symm.trans <| (ev _ e₁).trans <|
      (ev _ (e₂.symm.trans (congrArg _ hc.symm))).trans <| (ev _ e₃.symm).trans <|
        (res inf_le_right ⟨y.2, hy⟩ _).trans (ev hy e₄)
  have hr : (a.1 ⟨_, hxU⟩).val = ((awayToSection _ g c).1 ⟨_, hxg⟩).val := by
    rw [hc]
    rfl
  rw [hl, hr]
  obtain ⟨n, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hg c
  rw [awayVeroneseEquiv_mk]
  refine (veroneseLocalizationsMap_mk (𝒜 := 𝒜) (d := d) y.1 b ⟨g ^ n, fun h ↦ ?_⟩).symm
  exact (mem_basicOpen _ _ _).1 hxg (Ideal.IsPrime.mem_of_pow_mem inferInstance n h)

namespace twistingSheaf

open ProjectiveSpectrum.TwistingSheaf

variable {n : ℤ} {U : (Proj (veroneseGrading 𝒜 d)).Opens} {V : (Proj 𝒜).Opens}

/-- **The pullback along the Veronese contraction is linear** over the map of structure sheaves
given by `AlgebraicGeometry.Proj.toVeronese`. -/
theorem comapVeronese_smul (hUV : V.1 ⊆ ProjectiveSpectrum.veroneseComap 𝒜 d ⁻¹' U.1)
    (a : Γ(Proj (veroneseGrading 𝒜 d), U)) (s : Γ(twistingSheaf (veroneseGrading 𝒜 d) n, U)) :
    comapVeronese hUV (a • s) = (toVeronese 𝒜 d).appLE U V
      (fun _ hy ↦ (coe_toVeronese_preimage U).ge (hUV hy)) a • comapVeronese hUV s := by
  refine ext fun (y : V) ↦ ?_
  simp only [comapVeronese_apply, smul_apply, map_mul, val_toVeronese_appLE_apply]
  rfl

end twistingSheaf

open twistingSheaf

variable (𝒜 d) in
/-- **The morphism of twisting sheaves along the Veronese isomorphism**: the morphism
`𝒪_{Proj A^{(d)}}(n) ⟶ (toVeronese)_* 𝒪_{Proj A}(d n)` of sheaves of modules on `Proj A^{(d)}`,
given on sections over `U` by `AlgebraicGeometry.Proj.twistingSheaf.comapVeronese`. -/
noncomputable def twistingSheafVeroneseMap (n : ℤ) :
    twistingSheaf (veroneseGrading 𝒜 d) n ⟶
      (Scheme.Modules.pushforward (toVeronese 𝒜 d)).obj (twistingSheaf 𝒜 (d * n)) where
  val :=
    { app U := ModuleCat.ofHom (X := (twistingSheaf (veroneseGrading 𝒜 d) n).val.obj U)
        (Y := ((Scheme.Modules.pushforward (toVeronese 𝒜 d)).obj
          (twistingSheaf 𝒜 (d * n))).val.obj U)
        { toFun := comapVeronese (U := U.unop) (coe_toVeronese_preimage U.unop).subset
          map_add' := map_add _
          map_smul' := comapVeronese_smul (coe_toVeronese_preimage U.unop).subset }
      naturality _ := rfl }

/-- On sections over `U`, the morphism of twisting sheaves along the Veronese isomorphism is the
pullback of sections along the contraction to the preimage of `U`. -/
@[simp]
theorem twistingSheafVeroneseMap_app (n : ℤ) (U : (Proj (veroneseGrading 𝒜 d)).Opens) :
    Scheme.Modules.Hom.app (twistingSheafVeroneseMap 𝒜 d n) U =
      AddCommGrpCat.ofHom (comapVeronese (U := U) (coe_toVeronese_preimage U).subset) :=
  (rfl)

/-- **The morphism of twisting sheaves along the Veronese isomorphism is an isomorphism**: over
each `D₊(g)`, `g ∈ A^{(d)}` homogeneous of positive degree, it is bijective by
`AlgebraicGeometry.Proj.twistingSheaf.bijective_comapVeronese_basicOpen`, and these opens form a
basis. -/
instance isIso_twistingSheafVeroneseMap (n : ℤ) : IsIso (twistingSheafVeroneseMap 𝒜 d n) := by
  refine Scheme.Modules.Hom.isIso_of_isBasis _ (isBasis_basicOpen_veronese 𝒜 d)
    fun ⟨k, g, hg⟩ ↦ ?_
  rw [twistingSheafVeroneseMap_app]
  -- the preimage of `D₊(g)` is `D₊(g)`, but not definitionally
  have key : ∀ (V : (Proj 𝒜).Opens) (_ : V = basicOpen 𝒜 (g : A))
      (hUV : V.1 ⊆ ProjectiveSpectrum.veroneseComap 𝒜 d ⁻¹' (basicOpen _ g).1),
      Function.Bijective (comapVeronese (n := n) hUV) := by
    rintro _ rfl _
    exact bijective_comapVeronese_basicOpen hg k.pos
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (key _ (toVeronese_preimage_basicOpen hg k.pos) _)

variable (𝒜 d) in
/-- **`𝒪_{Proj A^{(d)}}(n)` corresponds to `𝒪_{Proj A}(d n)`** along the Veronese isomorphism
`Proj A^{(d)} ≅ Proj A`, whose inverse is `AlgebraicGeometry.Proj.toVeronese`. -/
noncomputable def twistingSheafVeroneseIso (n : ℤ) :
    twistingSheaf (veroneseGrading 𝒜 d) n ≅
      (Scheme.Modules.pushforward (toVeronese 𝒜 d)).obj (twistingSheaf 𝒜 (d * n)) :=
  asIso (twistingSheafVeroneseMap 𝒜 d n)

end AlgebraicGeometry.Proj
