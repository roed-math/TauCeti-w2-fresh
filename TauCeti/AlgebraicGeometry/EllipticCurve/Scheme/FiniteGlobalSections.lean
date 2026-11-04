/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FiniteCohomology
public import TauCeti.RingTheory.Adjoin.Polynomial.Basic

/-!
# Finiteness of the global sections on a projective Weierstrass model

Let `W` be a Weierstrass curve over a Noetherian ring `R`. This file shows that the global
sections of a quasi-coherent sheaf `M` of finite type on the projective model of `W` form a
finitely generated `R`-module.

The proof follows the one for the projective line
(`TauCeti.AlgebraicGeometry.projectiveLine.finite_globalSections`). The projective model is covered
by the charts `D₊(Y)` and `D₊(Z)`, with affine coordinates `F = Z / Y` and `G = Y / Z` inverse to
each other on the overlap `D₊(YZ)`. The Weierstrass equation makes `X / Y` integral of degree three
over `R[F]` on `D₊(Y)`, and `X / Z` integral of degree three over `R[G]` on `D₊(Z)`
(`WeierstrassCurve.Projective.exists_eq_away_one` and
`WeierstrassCurve.Projective.exists_eq_away_two`).
So the sections of `M` over each chart are finitely generated over the polynomial algebra in its
affine coordinate. A global section is a pair of sections over the charts that agree on the
overlap. The common restriction is both an `R[F]`- and an `R[G]`-combination of finitely many
sections over the overlap, which is a finitely generated `R`-module by
`TauCeti.Algebra.fg_inf_of_mul_eq_one`. The sections over a chart vanishing on the overlap are
killed by powers of the affine coordinate, hence finitely generated over `R` by
`TauCeti.Algebra.fg_restrictScalars_of_forall_pow_smul_eq_zero`.

## Main results

* `WeierstrassCurve.finite_globalSections`: over a Noetherian ring, the global sections of a
  quasi-coherent sheaf of finite type on the projective model are finite over the global functions.
* `WeierstrassCurve.finite_cohomology_zero`: over a Noetherian ring, `H⁰(projModel W, M)` is a
  finitely generated `R`-module for every quasi-coherent sheaf `M` of finite type.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2.
-/

public section

open CategoryTheory Opposite AlgebraicGeometry HomogeneousLocalization
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

attribute [local instance] sectionsGlobalAlgebra isScalarTower_sectionsGlobalAlgebra

variable {W}

/-- On a chart `D₊(Xᵢ)` whose functions are `P₀(t) + s P₁(t) + s² P₂(t)` in two of its affine
coordinates `s = Xⱼ / Xᵢ` and `t = Xₖ / Xᵢ`, every function is `c₀ + s c₁ + s² c₂` with the `cₗ`
polynomial in `t` over the global functions. -/
private theorem exists_eq_chart {i j k : Fin 3}
    (h : ∀ a : Away W.toProjective.grading (W.toProjective.coord i), ∃ P₀ P₁ P₂ : Polynomial R,
      a = Polynomial.aeval (W.toProjective.awayCoord i k) P₀ +
        W.toProjective.awayCoord i j * Polynomial.aeval (W.toProjective.awayCoord i k) P₁ +
          W.toProjective.awayCoord i j ^ 2 * Polynomial.aeval (W.toProjective.awayCoord i k) P₂)
    (c : Γ(W.projModel, Proj.basicOpen W.toProjective.grading (W.toProjective.coord i))) :
    ∃ c₀ c₁ c₂, c₀ ∈ Algebra.adjoin Γ(W.projModel, ⊤)
        {Proj.awayToSection _ _ (W.toProjective.awayCoord i k)} ∧
      c₁ ∈ Algebra.adjoin Γ(W.projModel, ⊤)
        {Proj.awayToSection _ _ (W.toProjective.awayCoord i k)} ∧
      c₂ ∈ Algebra.adjoin Γ(W.projModel, ⊤)
        {Proj.awayToSection _ _ (W.toProjective.awayCoord i k)} ∧
      c = c₀ + Proj.awayToSection _ _ (W.toProjective.awayCoord i j) * c₁ +
        Proj.awayToSection _ _ (W.toProjective.awayCoord i j) ^ 2 * c₂ := by
  let σ := Proj.awayToSection W.toProjective.grading (W.toProjective.coord i)
  have hσ : Function.Surjective σ :=
    (Proj.basicOpenIsoAway W.toProjective.grading _ (W.toProjective.coord_mem_grading i)
      one_pos).commRingCatIsoToRingEquiv.surjective
  let A := Algebra.adjoin Γ(W.projModel, ⊤) {σ (W.toProjective.awayCoord i k)}
  have haeval (P : Polynomial R) : σ (Polynomial.aeval (W.toProjective.awayCoord i k) P) ∈ A := by
    induction P using Polynomial.induction_on with
    | C a =>
      rw [Polynomial.aeval_C, W.awayToSection_algebraMap (W.toProjective.coord_mem_grading i)
        one_pos, Scheme.baseRingToStructurePresheaf_app]
      exact Subalgebra.algebraMap_mem A _
    | add p q hp hq => rw [map_add, map_add]; exact A.add_mem hp hq
    | monomial n a ih =>
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, map_mul]
      exact A.mul_mem ih (Algebra.subset_adjoin rfl)
  obtain ⟨a, rfl⟩ := hσ c
  obtain ⟨P₀, P₁, P₂, rfl⟩ := h a
  exact ⟨_, _, _, haeval P₀, haeval P₁, haeval P₂, by simp only [map_add, map_mul, map_pow]; rfl⟩

/-- On a chart as in `exists_eq_chart`, the sections of a quasi-coherent sheaf of finite type are
finitely generated over the algebra of polynomials in `t` over the global functions. -/
private theorem exists_finite_span_eq_top (M : W.projModel.Modules) [M.IsQuasicoherent]
    [M.IsFiniteType] {i j k : Fin 3}
    (h : ∀ a : Away W.toProjective.grading (W.toProjective.coord i), ∃ P₀ P₁ P₂ : Polynomial R,
      a = Polynomial.aeval (W.toProjective.awayCoord i k) P₀ +
        W.toProjective.awayCoord i j * Polynomial.aeval (W.toProjective.awayCoord i k) P₁ +
          W.toProjective.awayCoord i j ^ 2 * Polynomial.aeval (W.toProjective.awayCoord i k) P₂) :
    ∃ T : Set Γ(M, Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)), T.Finite ∧
      Submodule.span (Algebra.adjoin Γ(W.projModel, ⊤)
        {Proj.awayToSection _ _ (W.toProjective.awayCoord i k)}) T = ⊤ := by
  have := Scheme.Modules.finite_sections_of_isAffineOpen M _
    (Proj.isAffineOpen_basicOpen _ _ (W.toProjective.coord_mem_grading i) one_pos)
  obtain ⟨S₁, hS₁⟩ := Module.Finite.fg_top
    (R := Γ(W.projModel, Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)))
    (M := Γ(M, Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)))
  let x := Proj.awayToSection W.toProjective.grading _ (W.toProjective.awayCoord i j)
  let A := Algebra.adjoin Γ(W.projModel, ⊤)
    {Proj.awayToSection W.toProjective.grading _ (W.toProjective.awayCoord i k)}
  let T := (fun p : ℕ × Γ(M, Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)) ↦
    x ^ p.1 • p.2) '' (Set.Iio 3 ×ˢ ↑S₁)
  refine ⟨T, ((Set.finite_Iio 3).prod S₁.finite_toSet).image _, ?_⟩
  -- every function times a generator is an `A`-combination of the `xˡ s`
  have key₀ : ∀ s ∈ S₁, ∀ c : Γ(W.projModel, Proj.basicOpen W.toProjective.grading
      (W.toProjective.coord i)), c • s ∈ Submodule.span A T := by
    intro s hs c
    obtain ⟨c₀, c₁, c₂, hc₀, hc₁, hc₂, rfl⟩ := exists_eq_chart h c
    have hmem (l : ℕ) (hl : l < 3) (c) (hc : c ∈ A) : (c * x ^ l) • s ∈ Submodule.span A T := by
      rw [mul_smul]
      exact Submodule.smul_mem _ (⟨c, hc⟩ : A) (Submodule.subset_span ⟨(l, s), ⟨hl, hs⟩, rfl⟩)
    have : c₀ + x * c₁ + x ^ 2 * c₂ = c₀ * x ^ 0 + c₁ * x ^ 1 + c₂ * x ^ 2 := by ring
    rw [this, add_smul, add_smul]
    exact add_mem (add_mem (hmem 0 (by norm_num) c₀ hc₀) (hmem 1 (by norm_num) c₁ hc₁))
      (hmem 2 (by norm_num) c₂ hc₂)
  have key : ∀ y ∈ Submodule.span Γ(W.projModel,
      Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)) (S₁ : Set _),
      ∀ c : Γ(W.projModel, Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)),
        c • y ∈ Submodule.span A T := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem s hs => exact key₀ s hs
    | zero => intro c; rw [smul_zero]; exact zero_mem _
    | add y z _ _ hy hz => intro c; rw [smul_add]; exact add_mem (hy c) (hz c)
    | smul c y _ hy => intro c'; rw [smul_smul]; exact hy _
  refine eq_top_iff.mpr fun m _ ↦ ?_
  simpa using key m (hS₁ ▸ Submodule.mem_top) 1

/-- Restricting to an open `O` of a chart as in `exists_eq_chart`, the sections over the chart
become combinations of the restrictions of finitely many sections, with coefficients polynomial in
the restriction of `t`. -/
private theorem range_le_span_adjoin (M : W.projModel.Modules) {i : Fin 3} {t : Γ(W.projModel,
      Proj.basicOpen W.toProjective.grading (W.toProjective.coord i))} {O : W.projModel.Opens}
    (hO : O ≤ Proj.basicOpen W.toProjective.grading (W.toProjective.coord i))
    {T : Set Γ(M, Proj.basicOpen W.toProjective.grading (W.toProjective.coord i))}
    (hT : Submodule.span (Algebra.adjoin Γ(W.projModel, ⊤) {t}) T = ⊤) :
    LinearMap.range (sectionsRestrictionLinear M (homOfLE hO)) ≤
      (Submodule.span
        (Algebra.adjoin Γ(W.projModel, ⊤) {W.projModel.presheaf.map (homOfLE hO).op t})
        (M.presheaf.map (homOfLE hO).op '' T)).restrictScalars Γ(W.projModel, ⊤) := by
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ Submodule.span (Algebra.adjoin Γ(W.projModel, ⊤) {t}) T := hT ▸ Submodule.mem_top
  rw [sectionsRestrictionLinear_apply, Submodule.restrictScalars_mem]
  induction hy using Submodule.span_induction with
  | mem s hs => exact Submodule.subset_span ⟨s, hs, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [Subalgebra.smul_def, M.map_smul]
    exact Submodule.smul_mem _
      (⟨_, map_mem_adjoin_singleton (homOfLE hO) a.2⟩ : Algebra.adjoin _ _) hy

/-- Over a Noetherian ring, the global functions on the projective model form a Noetherian ring. -/
private theorem isNoetherianRing_globalSections [IsNoetherianRing R] :
    IsNoetherianRing Γ(W.projModel, ⊤) :=
  isNoetherianRing_of_surjective R _ _ W.surjective_baseRingToStructurePresheaf_app_top

/-- On a chart as in `exists_eq_chart`, the sections of a quasi-coherent sheaf of finite type that
vanish on the basic open of `t` form a finitely generated module over the global functions, over a
Noetherian ring: they are finitely generated over the polynomials in `t`, and killed by powers of
`t`. -/
private theorem fg_ker_sectionsRestrictionLinear [IsNoetherianRing R] (M : W.projModel.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] {i j k : Fin 3}
    (h : ∀ a : Away W.toProjective.grading (W.toProjective.coord i), ∃ P₀ P₁ P₂ : Polynomial R,
      a = Polynomial.aeval (W.toProjective.awayCoord i k) P₀ +
        W.toProjective.awayCoord i j * Polynomial.aeval (W.toProjective.awayCoord i k) P₁ +
          W.toProjective.awayCoord i j ^ 2 * Polynomial.aeval (W.toProjective.awayCoord i k) P₂)
    {O : W.projModel.Opens}
    (hO : W.projModel.basicOpen (Proj.awayToSection _ _ (W.toProjective.awayCoord i k)) = O)
    (hOU : O ≤ Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)) :
    (LinearMap.ker (sectionsRestrictionLinear M (homOfLE hOU))).FG := by
  subst hO
  have := W.isNoetherianRing_globalSections
  let t := Proj.awayToSection W.toProjective.grading _ (W.toProjective.awayCoord i k)
  let A := Algebra.adjoin Γ(W.projModel, ⊤) {t}
  have : IsNoetherianRing A := by
    have hsurj : Function.Surjective (Polynomial.aeval (R := Γ(W.projModel, ⊤))
        (⟨t, Algebra.self_mem_adjoin_singleton _ t⟩ : A)) := by
      rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
      have h := Algebra.adjoin_adjoin_coe_preimage (R := Γ(W.projModel, ⊤)) (s := {t})
      convert h using 2
      ext ⟨z, hz⟩
      simp [Subtype.ext_iff]
    exact isNoetherianRing_of_surjective _ _ _ hsurj
  obtain ⟨T, hTfin, hT⟩ := exists_finite_span_eq_top M h
  have : Module.Finite A Γ(M, Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)) :=
    ⟨⟨hTfin.toFinset, by rw [Set.Finite.coe_toFinset]; exact hT⟩⟩
  -- the same sections, as a submodule over the polynomials in `t`
  let K : Submodule A Γ(M, Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)) :=
    { carrier := {y | M.presheaf.map (homOfLE hOU).op y = 0}
      add_mem' := fun hy hz ↦ by simp_all
      zero_mem' := by simp
      smul_mem' := fun a y hy ↦ by
        simp only [Set.mem_ofPred_eq, Subalgebra.smul_def, M.map_smul] at hy ⊢
        rw [hy, smul_zero] }
  have hK := TauCeti.Algebra.fg_restrictScalars_of_forall_pow_smul_eq_zero (R := Γ(W.projModel, ⊤))
    (c := (⟨t, Algebra.self_mem_adjoin_singleton _ t⟩ : A)) (by
      have h := Algebra.adjoin_adjoin_coe_preimage (R := Γ(W.projModel, ⊤)) (s := {t})
      convert h using 2
      ext ⟨z, hz⟩
      simp [Subtype.ext_iff]) (IsNoetherian.noetherian K) fun y hy ↦ by
    obtain ⟨n, hn⟩ := M.exists_pow_smul_eq_zero_of_isCompact
      (Proj.isAffineOpen_basicOpen _ _ (W.toProjective.coord_mem_grading i) one_pos).isCompact t y
      (by rw [Scheme.Modules.basicOpenRestrict_apply]; exact hy)
    exact ⟨n, by rw [Subalgebra.smul_def, SubmonoidClass.coe_pow]; exact hn⟩
  convert hK using 1
  ext y
  simp only [LinearMap.mem_ker, sectionsRestrictionLinear_apply, Submodule.restrictScalars_mem]
  exact Iff.rfl

/-- **The global sections of a quasi-coherent sheaf of finite type on the projective Weierstrass
model form a finitely generated module** over the global functions, over a Noetherian ring. -/
theorem finite_globalSections [IsNoetherianRing R] (M : W.projModel.Modules) [M.IsQuasicoherent]
    [M.IsFiniteType] : Module.Finite Γ(W.projModel, ⊤) Γ(M, ⊤) := by
  have := W.isNoetherianRing_globalSections
  have hUV : Proj.basicOpen W.toProjective.grading (W.toProjective.coord 1) ⊔
      Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2) = ⊤ := by
    simpa using W.opensRange_chartι_one_sup_opensRange_chartι_two
  -- global sections are the pairs of sections over the charts that agree on the overlap
  suffices h : (LinearMap.ker (mayerVietorisSectionsDifferenceLinear M
      (Proj.basicOpen W.toProjective.grading (W.toProjective.coord 1))
      (Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2)))).FG by
    rw [LinearMap.exact_iff.mp (exact_mayerVietorisSectionsRestrictionLinear M _ _ hUV)] at h
    have := Module.Finite.iff_fg.mpr h
    exact Module.Finite.equiv (LinearEquiv.ofInjective _
      (mayerVietorisSectionsRestrictionLinear_injective M _ _ hUV)).symm
  -- the overlap is `D₊(YZ)`, where the affine coordinates of the charts are defined
  suffices h : ∀ (O : W.projModel.Opens) (_ : Proj.basicOpen W.toProjective.grading
      (W.toProjective.coord 1 * W.toProjective.coord 2) = O)
      (h₀ : O ≤ Proj.basicOpen W.toProjective.grading (W.toProjective.coord 1))
      (h₁ : O ≤ Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2)),
      (LinearMap.ker ((sectionsRestrictionLinear M (homOfLE h₀)).comp (LinearMap.fst _ _ _) -
        (sectionsRestrictionLinear M (homOfLE h₁)).comp (LinearMap.snd _ _ _))).FG by
    convert h _ (Proj.basicOpen_mul _ _ _) inf_le_left inf_le_right using 1
    ext ⟨s, t⟩
    simp only [LinearMap.mem_ker, mayerVietorisSectionsDifferenceLinear_apply,
      mayerVietorisSectionsDifference_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, sectionsRestrictionLinear_apply]
    exact Iff.rfl
  intro O hO h₀ h₁
  have hbasic₀ : W.projModel.basicOpen
      (Proj.awayToSection _ _ (W.toProjective.awayCoord 1 2)) = O :=
    (Proj.basicOpen_awayToSection_mk _ _ _ _).trans hO
  have hbasic₁ : W.projModel.basicOpen
      (Proj.awayToSection _ _ (W.toProjective.awayCoord 2 1)) = O := by
    rw [Proj.basicOpen_awayToSection_mk, mul_comm]
    exact hO
  have hFG : W.projModel.presheaf.map (homOfLE h₀).op
        (Proj.awayToSection _ _ (W.toProjective.awayCoord 1 2)) *
      W.projModel.presheaf.map (homOfLE h₁).op
        (Proj.awayToSection _ _ (W.toProjective.awayCoord 2 1)) = 1 := by
    subst hO
    exact W.map_awayCoord_mul_map_awayCoord h₀ h₁
  obtain ⟨T₁, hT₁fin, hT₁⟩ := exists_finite_span_eq_top M W.toProjective.exists_eq_away_one
  obtain ⟨T₂, hT₂fin, hT₂⟩ := exists_finite_span_eq_top M W.toProjective.exists_eq_away_two
  -- the common restriction of a global section extends to both charts
  have hrange := (TauCeti.Algebra.fg_inf_of_mul_eq_one hFG
    ((hT₁fin.image _).union (hT₂fin.image _))).of_le
    (inf_le_inf ((range_le_span_adjoin M h₀ hT₁).trans
      (Submodule.restrictScalars_mono _ (Submodule.span_mono Set.subset_union_left)))
      ((range_le_span_adjoin M h₁ hT₂).trans
      (Submodule.restrictScalars_mono _ (Submodule.span_mono Set.subset_union_right))))
  -- a pair agreeing on the overlap is determined by the common restriction, up to sections
  -- vanishing on the overlap
  refine Submodule.fg_of_fg_map_of_fg_inf_ker
    ((sectionsRestrictionLinear M (homOfLE h₀)).comp (LinearMap.fst _ _ _))
    (hrange.of_le ?_)
    (((fg_ker_sectionsRestrictionLinear M W.toProjective.exists_eq_away_one hbasic₀ h₀).prod
      (fg_ker_sectionsRestrictionLinear M W.toProjective.exists_eq_away_two hbasic₁ h₁)).of_le ?_)
  · rintro _ ⟨⟨a, b⟩, hab, rfl⟩
    exact ⟨⟨a, rfl⟩, ⟨b, (sub_eq_zero.mp hab).symm⟩⟩
  · rintro ⟨a, b⟩ ⟨hab, ha⟩
    exact ⟨ha, (sub_eq_zero.mp hab).symm.trans ha⟩

/-- **The global sections of a quasi-coherent sheaf of finite type on the projective Weierstrass
model form a finitely generated module** over a Noetherian base ring `R`: `H⁰(projModel W, M)` is
finite over `R`. -/
theorem finite_cohomology_zero [IsNoetherianRing R] (M : W.projModel.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] : Module.Finite R (Cohomology M 0) := by
  have := W.finite_globalSections M
  have : Module.Finite Γ(W.projModel, ⊤) (Cohomology M 0) :=
    Module.Finite.equiv (cohomologyZeroLinearEquiv M).symm
  exact W.finite_cohomology_of_finite M 0

end WeierstrassCurve
