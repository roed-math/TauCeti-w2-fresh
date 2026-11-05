/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Inclusion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.PoleSheaf.Cohomology

/-!
# The pole filtration of a projective Weierstrass model

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`. For `m ≤ n` the divisor
`n[0]` contains `m[0]`, so the ideal sheaf `𝒪(-n[0])` is contained in `𝒪(-m[0])`, and dually the
pole sheaf `𝒪(m[0])` includes into `𝒪(n[0])` (`WeierstrassCurve.poleSheafMap`). These inclusions
are monomorphisms of sheaves, compatible with composition, and they make the pole sheaves into the
**pole filtration** `𝒪 = 𝒪(0[0]) ⊆ 𝒪([0]) ⊆ 𝒪(2[0]) ⊆ ⋯`: the sections of `𝒪(n[0])` are the
functions with a pole of order at most `n` along the zero section.

On cohomology, the filtration is a chain of injections
`H⁰(𝒪(m[0])) ↪ H⁰(𝒪(n[0]))`. Over a field `K` the spaces `H⁰(𝒪(n[0]))` have dimension `n` for
`n > 0` by Riemann–Roch, and `H⁰(𝒪(0[0])) = H⁰(𝒪) = K`. So the first step
`H⁰(𝒪) ↪ H⁰(𝒪([0]))` is bijective (every section of `𝒪([0])` is constant), and each later step
`H⁰(𝒪(n[0])) ↪ H⁰(𝒪((n + 1)[0]))`, `n > 0`, has a one-dimensional cokernel: the successive
quotients of the pole filtration are lines.

## Main declarations

* `WeierstrassCurve.poleSheafMap`: the inclusion `𝒪(m[0]) ⟶ 𝒪(n[0])` for `m ≤ n`, a monomorphism
  of sheaves (`WeierstrassCurve.mono_poleSheafMap_hom`), with `poleSheafMap_refl` and
  `poleSheafMap_comp`.
* `WeierstrassCurve.injective_cohomologyMapBaseLinear_poleSheafMap`: the inclusion is injective on
  `H⁰`.
* `WeierstrassCurve.finrank_cohomology_zero_poleSheaf_zero`: over a field,
  `dim H⁰(𝒪(0[0])) = 1`.
* `WeierstrassCurve.bijective_cohomologyMapBaseLinear_poleSheafMap_zero_one`: over a field,
  `H⁰(𝒪) ⟶ H⁰(𝒪([0]))` is bijective.
* `WeierstrassCurve.finrank_quotient_range_cohomologyMapBaseLinear_poleSheafMap`: over a field,
  `H⁰(𝒪((n + 1)[0])) / H⁰(𝒪(n[0]))` is one-dimensional for `n > 0`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, III.3.1.
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules
open Module (finrank)

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

omit [W.IsElliptic] in
/-- The divisor `n[0]` contains `m[0]` for `m ≤ n`: its ideal sheaf `𝒪(-n[0])` is contained in
`𝒪(-m[0])`. -/
theorem zeroSectionDivisor_pow_le_pow {m n : ℕ} (h : m ≤ n) :
    W.zeroSectionDivisor ^ n ≤ W.zeroSectionDivisor ^ m :=
  pow_le_pow_right_of_le_one' le_top h

/-- The **pole filtration**: the inclusion `𝒪(m[0]) ⟶ 𝒪(n[0])` of pole sheaves for `m ≤ n`, the
dual of the inclusion `𝒪(-n[0]) ⊆ 𝒪(-m[0])` of ideal sheaves. -/
noncomputable def poleSheafMap {m n : ℕ} (h : m ≤ n) : W.poleSheaf m ⟶ W.poleSheaf n :=
  eqToHom (W.poleSheaf_def m) ≫
    Scheme.IdealSheafData.IsEffectiveCartier.dualMap
      (W.isRelativeEffectiveCartier_zeroSectionDivisor_pow m).isEffectiveCartier
      (W.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
      (W.zeroSectionDivisor_pow_le_pow h) ≫
    eqToHom (W.poleSheaf_def n).symm

/-- Through `poleSheaf_def`, `poleSheafMap` is the dual of the inclusion of ideal sheaves. -/
theorem poleSheafMap_def {m n : ℕ} (h : m ≤ n) :
    W.poleSheafMap h = eqToHom (W.poleSheaf_def m) ≫
      Scheme.IdealSheafData.IsEffectiveCartier.dualMap
        (W.isRelativeEffectiveCartier_zeroSectionDivisor_pow m).isEffectiveCartier
        (W.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
        (W.zeroSectionDivisor_pow_le_pow h) ≫
      eqToHom (W.poleSheaf_def n).symm :=
  (rfl)

/-- The inclusion `𝒪(m[0]) ⟶ 𝒪(n[0])` is a monomorphism of sheaves. -/
instance mono_poleSheafMap_hom {m n : ℕ} (h : m ≤ n) : Mono (W.poleSheafMap h).hom := by
  rw [poleSheafMap_def, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.eqToHom_hom, ObjectProperty.eqToHom_hom]
  infer_instance

/-- The inclusion of `𝒪(n[0])` into itself is the identity. -/
@[simp]
theorem poleSheafMap_refl (n : ℕ) : W.poleSheafMap (le_refl n) = 𝟙 _ := by
  simp [poleSheafMap_def]

/-- The inclusions of the pole filtration compose. -/
@[reassoc (attr := simp)]
theorem poleSheafMap_comp {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) :
    W.poleSheafMap h₁ ≫ W.poleSheafMap h₂ = W.poleSheafMap (h₁.trans h₂) := by
  simp [poleSheafMap_def]

/-- **The pole filtration on `H⁰`**: the inclusion `𝒪(m[0]) ⟶ 𝒪(n[0])` is injective on `H⁰`. -/
theorem injective_cohomologyMapBaseLinear_poleSheafMap {m n : ℕ} (h : m ≤ n) :
    Function.Injective (cohomologyMapBaseLinear R W.projModel (W.poleSheafMap h).hom 0) := by
  simpa only [coe_cohomologyMapBaseLinear] using cohomologyMap_injective (W.poleSheafMap h).hom

/-- **The successive quotients of the pole filtration are lines**: over a field `K`, the quotient
of `H⁰(𝒪((n + 1)[0]))` by the image of `H⁰(𝒪(n[0]))` is one-dimensional for `n > 0`. -/
theorem finrank_quotient_range_cohomologyMapBaseLinear_poleSheafMap {K : Type u} [Field K]
    (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ} (hn : 0 < n) :
    finrank K (Cohomology (W.poleSheaf (n + 1)).obj 0 ⧸
      LinearMap.range (cohomologyMapBaseLinear K W.projModel
        (W.poleSheafMap (n.le_add_right 1)).hom 0)) = 1 := by
  have hn₁ := W.finrank_cohomology_zero_poleSheaf (n := n + 1) (by omega)
  have hn₀ := W.finrank_cohomology_zero_poleSheaf hn
  have : FiniteDimensional K (Cohomology (W.poleSheaf (n + 1)).obj 0) :=
    Module.finite_of_finrank_pos (by omega)
  have hr := Submodule.finrank_quotient_add_finrank (LinearMap.range
    (cohomologyMapBaseLinear K W.projModel (W.poleSheafMap (n.le_add_right 1)).hom 0))
  rw [LinearMap.finrank_range_of_inj (W.injective_cohomologyMapBaseLinear_poleSheafMap _), hn₀,
    hn₁] at hr
  omega

section Field

variable {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

omit [W.IsElliptic] in
/-- Over a field, the global functions on the projective model are the constants:
`dim_K H⁰(projModel W, 𝒪) = 1`. -/
theorem finrank_cohomology_zero_trivial_projModel :
    finrank K (Cohomology (InvertibleSheaf.trivial W.projModel).obj 0) = 1 :=
  finrank_cohomology_zero_trivial_eq_one_of_surjective K W.bijective_baseRingToGlobalSections.2

/-- Over a field, `dim_K H⁰(projModel W, 𝒪(0[0])) = 1`: the pole sheaf `𝒪(0[0])` is trivial. -/
theorem finrank_cohomology_zero_poleSheaf_zero :
    finrank K (Cohomology (W.poleSheaf 0).obj 0) = 1 := by
  obtain ⟨e⟩ := (LineBundleClass.mk_eq_one_iff (L := W.poleSheaf 0)).mp
    (by rw [mk_poleSheaf, pow_zero])
  rw [finrank_cohomology_congr K (e ≪≫ (InvertibleSheaf.trivialObjIsoUnit _).symm),
    finrank_cohomology_zero_trivial_projModel]

/-- **Every section of `𝒪([0])` is constant**: over a field, the inclusion `𝒪 = 𝒪(0[0]) ⟶ 𝒪([0])`
is bijective on `H⁰`. This is the first step `L(0) = L(O) = K` of the pole filtration. -/
theorem bijective_cohomologyMapBaseLinear_poleSheafMap_zero_one :
    Function.Bijective
      (cohomologyMapBaseLinear K W.projModel (W.poleSheafMap zero_le_one).hom 0) := by
  have h₀ := W.finrank_cohomology_zero_poleSheaf_zero
  have h₁ := W.finrank_cohomology_zero_poleSheaf one_pos
  have : FiniteDimensional K (Cohomology (W.poleSheaf 0).obj 0) :=
    Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional K (Cohomology (W.poleSheaf 1).obj 0) :=
    Module.finite_of_finrank_pos (by omega)
  have hinj := W.injective_cohomologyMapBaseLinear_poleSheafMap zero_le_one
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (h₀.trans h₁.symm)).mp
    hinj⟩

end Field

end WeierstrassCurve
