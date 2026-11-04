/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
public import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Data.Finsupp.Multiset
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import TauCeti.Algebra.Homology.HomologicalComplex.Basic
import TauCeti.AlgebraicGeometry.Cohomology.Cech.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.BasicOpen
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent
import TauCeti.CategoryTheory.Limits.Lattice
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.MayerVietoris
import TauCeti.LinearAlgebra.Finsupp.Supported
import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison

/-!
# Higher cohomology of the twisting sheaves on projective space

Let `M` be a free `R`-module with a basis `x₀, …, xₙ` indexed by a finite type `κ`, so that
`Proj (Sym M) = ℙⁿ_R` is projective space over an arbitrary commutative ring `R`. This file proves
that the twisting sheaves `𝒪(m)` have no cohomology in the intermediate degrees `0 < q < n`, for
every `m : ℤ`, and none at all in positive degrees when `m > -n - 1`. Together with the
computation of `H⁰` (`TauCeti.SymmetricAlgebra.free_cohomology_zero_twistingSheaf`) and the
vanishing above degree `n` (`Module.Basis.subsingleton_cohomology_proj_of_card_le`), this describes
`Hᵠ(ℙⁿ_R, 𝒪(m))` in every case of Hartshorne, Theorem III.5.1, except the top cohomology
`Hⁿ(ℙⁿ_R, 𝒪(m))` for `m ≤ -n - 1`. The file computes that one too, for `n ≥ 1`: writing
`m = -j - n - 1`, the group `Hⁿ(ℙⁿ_R, 𝒪(m))` is the dual of the module of forms of degree `j`.

The proof computes Čech cohomology for the standard affine cover by the charts `D₊(xᵢ)`, following
the Stacks Project. On the chart `D₊(x_S)` of a nonempty set `S` of coordinates, with
`x_S = ∏_{i ∈ S} xᵢ`, the sections of `𝒪(m)` are the Laurent polynomials of degree `m` whose
monomials `xᵉ` have negative exponents `eᵢ < 0` only for `i ∈ S`: every section is a fraction
`r / x_Sᵏ`, and since the coordinates are nonzerodivisors two fractions agree exactly when they do
after cross-multiplication. These identifications are compatible with restriction, so the Čech
complex of `𝒪(m)` is the Čech complex of the presheaf `S ↦ {Laurent polynomials of degree m with
negative exponents only in S}` on the finite sets of coordinates.

This presheaf is the direct sum, over the sets `T` of coordinates, of the parts spanned by the
monomials `xᵉ` whose set of negative exponents is exactly `T`. For `T` missing a coordinate `c`,
the part indexed by `T` does not change when `S` is replaced by `S ∪ {c}`; its Čech complex is
therefore that of a presheaf restricted to the chart of `c`, which is a member of the cover, and it
is exact in positive degrees (`TauCeti.CategoryTheory.quasiIso_cechAugmentation_prod_of_hom`). The
part indexed by `T = κ` is zero on a set `S` of fewer than `n + 1` coordinates, so it contributes
nothing to the Čech complex in degrees `q < n`, and it vanishes altogether when `m > -n - 1`,
because a monomial with all exponents negative has degree at most `-n - 1`. Finally Leray's theorem
(`AlgebraicGeometry.Scheme.Modules.homologyCechComplexIsoCohomology`) identifies Čech cohomology
with the cohomology of `𝒪(m)`, the intersections of the charts being affine.

In the top degree `n`, the Čech complex of the part indexed by `T = κ` is zero in degree `n - 1`,
so its cohomology is the group of cocycles. Its terms in degree `n` are indexed by the tuples
`a` of `n + 1` coordinates, and only the bijective tuples contribute. The cocycle condition for a
tuple of `n + 2` coordinates repeating one entry two places apart shows that a cocycle changes sign
under each transposition of adjacent entries, so it is `a ↦ det(a) ℓ` for a Laurent polynomial `ℓ`
with all exponents negative, where `det(a)` is the determinant of the matrix of `a` in a fixed
enumeration of the coordinates. Conversely `a ↦ det(a) ℓ` is a cocycle: the alternating sum of the
determinants of the faces of a tuple of `n + 2` coordinates is the Laplace expansion of a singular
matrix. Finally, the Laurent monomials `x^{-P - 1}` of degree `-j - n - 1` correspond to the
monomials `x^P` of degree `j`, whose dual basis spans the dual of the forms of degree `j`.

## Main results

* `Module.Basis.subsingleton_cohomology_twistingSheaf_of_lt_card`:
  `Hᵠ(ℙⁿ_R, 𝒪(m)) = 0` for `0 < q < n` and every `m : ℤ`.
* `Module.Basis.subsingleton_cohomology_twistingSheaf_of_neg_card_lt`:
  `Hᵠ(ℙⁿ_R, 𝒪(m)) = 0` for every `q > 0` when `m > -n - 1`.
* `Module.Basis.cohomologyTwistingSheafTopAddEquiv`:
  `Hⁿ(ℙⁿ_R, 𝒪(-j - n - 1)) ≃+ (Sym^j Rⁿ⁺¹)^∨` for `n ≥ 1`, as abelian groups.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.1(b), (c), (d).
* [Stacks, Lemma 30.8.1 (01XS)](https://stacks.math.columbia.edu/tag/01XS), whose proof
  decomposes the Čech complex of the standard cover by the multidegree of Laurent monomials.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open _root_.SymmetricAlgebra (ι equivMvPolynomial)

namespace TauCeti.SymmetricAlgebra

universe u

variable {R : Type u} {M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]
  {κ : Type u} (b : Module.Basis κ R M)

local notation "𝒜" => homogeneousSubmodule R M

/-! ### Laurent exponents -/

section Exponents

variable [Fintype κ] [DecidableEq κ]

/-- The coordinates in which a Laurent exponent is negative. -/
private def negSupport (e : κ → ℤ) : Finset κ := {i | e i < 0}

omit [DecidableEq κ] in
private lemma mem_negSupport {e : κ → ℤ} {i : κ} : i ∈ negSupport e ↔ e i < 0 := by
  simp [negSupport]

/-- The Laurent exponents of total degree `m` which are negative only in coordinates of `S`: the
monomials of degree `m` of the localization at the product of the coordinates in `S`. -/
private def chartExponents (m : ℤ) (S : Finset κ) : Set (κ → ℤ) :=
  {e | ∑ i, e i = m ∧ negSupport e ⊆ S}

omit [DecidableEq κ] in
private lemma chartExponents_mono {m : ℤ} {S S' : Finset κ} (h : S ⊆ S') :
    chartExponents m S ⊆ chartExponents m S' :=
  fun _ he ↦ ⟨he.1, he.2.trans h⟩

omit [DecidableEq κ] in
private lemma nonneg_of_mem_chartExponents {m : ℤ} {S : Finset κ} {e : κ → ℤ}
    (he : e ∈ chartExponents m S) {i : κ} (hi : i ∉ S) : 0 ≤ e i :=
  not_lt.1 fun h ↦ hi (he.2 (mem_negSupport.2 h))

/-- The exponent of the numerator of the Laurent monomial `xᵉ` written over the denominator
`(∏_{i ∈ S} xᵢ)ʲ`. -/
private def numeratorExponent (e : κ → ℤ) (S : Finset κ) (j : ℕ) : κ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ (e i + if i ∈ S then (j : ℤ) else 0).toNat

private lemma coe_numeratorExponent {m : ℤ} {S : Finset κ} {e : κ → ℤ} (he : e ∈ chartExponents m S)
    {j : ℕ} (hj : ∀ i ∈ S, 0 ≤ e i + j) (i : κ) :
    (numeratorExponent e S j i : ℤ) = e i + if i ∈ S then (j : ℤ) else 0 := by
  simp only [numeratorExponent, Finsupp.equivFunOnFinite_symm_apply_apply]
  refine Int.toNat_of_nonneg ?_
  split_ifs with hi
  · exact hj i hi
  · simpa using nonneg_of_mem_chartExponents he hi

private lemma degree_numeratorExponent {m : ℤ} {S : Finset κ} {e : κ → ℤ}
    (he : e ∈ chartExponents m S) {j : ℕ} (hj : ∀ i ∈ S, 0 ≤ e i + j) :
    ((numeratorExponent e S j).degree : ℤ) = j * S.card + m := by
  rw [Finsupp.degree_eq_sum, Nat.cast_sum]
  simp_rw [coe_numeratorExponent he hj, Finset.sum_add_distrib, he.1, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  ring

end Exponents

/-! ### Monomials in the coordinates -/

/-- The product of the coordinates indexed by `S`. -/
private def coordProd (S : Finset κ) : _root_.SymmetricAlgebra R M := ∏ i ∈ S, ι R M (b i)

private lemma coordProd_mem (S : Finset κ) : coordProd b S ∈ 𝒜 S.card := by
  simpa [coordProd] using SetLike.prod_mem_graded 𝒜 (fun _ ↦ 1) (fun i ↦ ι R M (b i)) (F := S)
    fun i _ ↦ ι_mem_homogeneousSubmodule R M (b i)

/-- The indicator exponent of `S`. -/
private def indicatorExponent (S : Finset κ) : κ →₀ ℕ := ∑ i ∈ S, Finsupp.single i 1

variable [DecidableEq κ] in
private lemma indicatorExponent_apply (S : Finset κ) (i : κ) :
    indicatorExponent S i = if i ∈ S then 1 else 0 := by
  simp [indicatorExponent, Finsupp.single_apply]

private lemma coordProd_eq_symmetricAlgebra (S : Finset κ) :
    coordProd b S = b.symmetricAlgebra (indicatorExponent S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact (equivMvPolynomial b).injective (by simp [coordProd, indicatorExponent,
      b.equivMvPolynomial_symmetricAlgebra_apply])
  | insert a S ha ih =>
    rw [coordProd, Finset.prod_insert ha, ← coordProd, ih]
    simp only [indicatorExponent, Finset.sum_insert ha, b.symmetricAlgebra_add]
    congr 1
    rw [Module.Basis.symmetricAlgebra, Module.Basis.map_apply, MvPolynomial.coe_basisMonomials]
    exact (_root_.SymmetricAlgebra.equivMvPolynomial_symm_X b a).symm

private lemma basicOpen_coordProd (S : Finset κ) :
    Proj.basicOpen 𝒜 (coordProd b S) = S.inf fun i ↦ Proj.basicOpen 𝒜 (ι R M (b i)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.inf_empty, coordProd, Finset.prod_empty]
    ext x
    simp only [Proj.basicOpen, ProjectiveSpectrum.basicOpen_one]
    trivial
  | insert a S ha ih =>
    rw [coordProd, Finset.prod_insert ha, ← coordProd, Proj.basicOpen_mul, ih, Finset.inf_insert]

/-! ### Laurent monomials as sections over the standard charts -/

section Chart

variable [Fintype κ] [DecidableEq κ] {m : ℤ}

private instance (S : Finset κ) : DecidablePred (· ∈ chartExponents m S) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

private lemma degree_numeratorExponent_eq_toNat {S : Finset κ} {e : κ → ℤ}
    (he : e ∈ chartExponents m S) {j : ℕ} (hj : ∀ i ∈ S, 0 ≤ e i + j) :
    (numeratorExponent e S j).degree = ((j : ℤ) * S.card + m).toNat := by
  have := degree_numeratorExponent he hj
  omega

omit [Fintype κ] [DecidableEq κ] in
private lemma basicOpen_le_basicOpen_pow (S : Finset κ) (j : ℕ) :
    Proj.basicOpen 𝒜 (coordProd b S) ≤ Proj.basicOpen 𝒜 (coordProd b S ^ j) :=
  fun x hx hpow ↦ hx (x.isPrime.mem_of_pow_mem j hpow)

variable (m) in
/-- The section `c xᵉ` of `𝒪(m)` over the standard open `D₊(∏_{i ∈ S} xᵢ)`, for a Laurent
exponent `e` of degree `m` that is negative only in coordinates of `S`, written as the fraction
`c x^{e + j 1_S} / (∏_{i ∈ S} xᵢ)ʲ`. -/
private def chartSection (S : Finset κ) {e : κ → ℤ} (he : e ∈ chartExponents m S) (j : ℕ)
    (hj : ∀ i ∈ S, 0 ≤ e i + j) (c : R) :
    Γ(Proj.twistingSheaf 𝒜 m, Proj.basicOpen 𝒜 (coordProd b S)) :=
  Proj.twistingSheaf.const (i := j * S.card) (j := ((j : ℤ) * S.card + m).toNat)
    (by have := degree_numeratorExponent he hj; push_cast; omega)
    (c • b.symmetricAlgebra (numeratorExponent e S j)) (coordProd b S ^ j)
    (Submodule.smul_mem _ c
      (degree_numeratorExponent_eq_toNat he hj ▸ b.symmetricAlgebra_mem_homogeneousSubmodule _))
    (by simpa [mul_comm] using SetLike.pow_mem_graded j (coordProd_mem b S))
    _ (basicOpen_le_basicOpen_pow b S j)

/-- The two ways of writing the Laurent monomial `xᵉ` as a fraction with denominators the powers of
coordinate products agree after cross-multiplication. -/
private lemma coordProd_pow_mul_symmetricAlgebra {S S' : Finset κ} {e : κ → ℤ}
    (he : e ∈ chartExponents m S) (he' : e ∈ chartExponents m S') {j j' : ℕ}
    (hj : ∀ i ∈ S, 0 ≤ e i + j) (hj' : ∀ i ∈ S', 0 ≤ e i + j') (c : R) :
    coordProd b S' ^ j' * (c • b.symmetricAlgebra (numeratorExponent e S j)) =
      coordProd b S ^ j * (c • b.symmetricAlgebra (numeratorExponent e S' j')) := by
  rw [coordProd_eq_symmetricAlgebra, coordProd_eq_symmetricAlgebra, b.symmetricAlgebra_pow,
    b.symmetricAlgebra_pow, mul_smul_comm, mul_smul_comm, ← b.symmetricAlgebra_add,
    ← b.symmetricAlgebra_add]
  congr 2
  ext i
  refine Nat.cast_injective (R := ℤ) ?_
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Nat.cast_add, Nat.cast_mul, indicatorExponent_apply, coe_numeratorExponent he hj,
    coe_numeratorExponent he' hj']
  split_ifs <;> push_cast <;> ring

/-- The restriction of the Laurent monomial `c xᵉ` from one standard open to a smaller one is
the same Laurent monomial, whatever denominators are used to write it. -/
private lemma res_chartSection {S S' : Finset κ}
    (h : Proj.basicOpen 𝒜 (coordProd b S') ≤ Proj.basicOpen 𝒜 (coordProd b S)) {e : κ → ℤ}
    (he : e ∈ chartExponents m S) (he' : e ∈ chartExponents m S') {j j' : ℕ}
    (hj : ∀ i ∈ S, 0 ≤ e i + j) (hj' : ∀ i ∈ S', 0 ≤ e i + j') (c : R) :
    (Proj.twistingSheaf 𝒜 m).presheaf.map (homOfLE h).op (chartSection b m S he j hj c) =
      chartSection b m S' he' j' hj' c := by
  rw [chartSection, Proj.twistingSheaf.res_const]
  exact Proj.twistingSheaf.const_ext (coordProd_pow_mul_symmetricAlgebra b he he' hj hj' c)

/-- The Laurent monomial `c xᵉ` does not depend on the power of the coordinate product used as
its denominator. -/
private lemma chartSection_congr {S : Finset κ} {e : κ → ℤ} (he : e ∈ chartExponents m S) {j j' : ℕ}
    (hj : ∀ i ∈ S, 0 ≤ e i + j) (hj' : ∀ i ∈ S, 0 ≤ e i + j') (c : R) :
    chartSection b m S he j hj c = chartSection b m S he j' hj' c :=
  Proj.twistingSheaf.const_ext (coordProd_pow_mul_symmetricAlgebra b he he hj hj' c)

omit [DecidableEq κ] in
/-- A denominator exponent making every entry of `e + j 1_S` nonnegative. -/
private def exponentBound (e : κ → ℤ) : ℕ := ∑ i, (-e i).toNat

omit [DecidableEq κ] in
private lemma le_exponentBound (e : κ → ℤ) (i : κ) : 0 ≤ e i + exponentBound e := by
  have : (-e i).toNat ≤ exponentBound e :=
    Finset.single_le_sum (f := fun i ↦ (-e i).toNat) (by simp) (Finset.mem_univ i)
  omega

variable (m) in
/-- The additive map `c ↦ c xᵉ` into the sections of `𝒪(m)` over `D₊(∏_{i ∈ S} xᵢ)`, which
vanishes unless `e` is a Laurent exponent of degree `m` negative only in coordinates of `S`. -/
private def chartSectionHom (S : Finset κ) (e : κ → ℤ) :
    R →+ Γ(Proj.twistingSheaf 𝒜 m, Proj.basicOpen 𝒜 (coordProd b S)) :=
  if he : e ∈ chartExponents m S then
    { toFun := chartSection b m S he (exponentBound e) fun i _ ↦ le_exponentBound e i
      map_zero' := Proj.twistingSheaf.ext fun x ↦ by simp [chartSection]
      map_add' c c' := by
        rw [chartSection, chartSection, chartSection, Proj.twistingSheaf.const_add]
        exact Proj.twistingSheaf.const_ext (by rw [add_smul]) }
  else 0

private lemma chartSectionHom_apply {S : Finset κ} {e : κ → ℤ} (he : e ∈ chartExponents m S) {j : ℕ}
    (hj : ∀ i ∈ S, 0 ≤ e i + j) (c : R) :
    chartSectionHom b m S e c = chartSection b m S he j hj c := by
  simp only [chartSectionHom, he, ↓reduceDIte, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact chartSection_congr b he _ hj c

variable (m) in
/-- The additive map from the Laurent polynomials of degree `m` whose monomials are negative only
in coordinates of `S` to the sections of `𝒪(m)` over `D₊(∏_{i ∈ S} xᵢ)`. -/
private def chartSectionsHom (S : Finset κ) :
    Finsupp.supported R R (chartExponents m S) →+
      Γ(Proj.twistingSheaf 𝒜 m, Proj.basicOpen 𝒜 (coordProd b S)) :=
  (Finsupp.liftAddHom (chartSectionHom b m S)).comp
    (Finsupp.supported R R (chartExponents m S)).subtype.toAddMonoidHom

private lemma chartSectionsHom_eq_sum {S : Finset κ}
    (f : Finsupp.supported R R (chartExponents m S)) :
    chartSectionsHom b m S f = ∑ e ∈ f.1.support, chartSectionHom b m S e (f.1 e) :=
  Finsupp.liftAddHom_apply _ _

private lemma chartSectionsHom_eq_const {S : Finset κ}
    (f : Finsupp.supported R R (chartExponents m S))
    {j : ℕ} (hj : ∀ e ∈ f.1.support, ∀ i ∈ S, 0 ≤ e i + j) (hjm : 0 ≤ (j : ℤ) * S.card + m) :
    chartSectionsHom b m S f =
      Proj.twistingSheaf.const (i := j * S.card) (j := ((j : ℤ) * S.card + m).toNat)
        (by push_cast; omega)
        (∑ e ∈ f.1.support, f.1 e • b.symmetricAlgebra (numeratorExponent e S j))
        (coordProd b S ^ j)
        (Submodule.sum_mem _ fun e he ↦ Submodule.smul_mem _ _
          (degree_numeratorExponent_eq_toNat ((Finsupp.mem_supported R f.1).1 f.2 he)
            (hj e he) ▸ b.symmetricAlgebra_mem_homogeneousSubmodule _))
        (by simpa [mul_comm] using SetLike.pow_mem_graded j (coordProd_mem b S)) _
        (basicOpen_le_basicOpen_pow b S j) := by
  refine Proj.twistingSheaf.ext fun x ↦ ?_
  rw [chartSectionsHom_eq_sum]
  refine (Proj.twistingSheaf.sum_apply _ _ x).trans <| (Finset.sum_congr rfl fun e he ↦ ?_).trans <|
    (Localization.mk_sum _ _ _).symm.trans (Proj.twistingSheaf.const_apply _ _ _ _ _ _ x).symm
  rw [chartSectionHom_apply b ((Finsupp.mem_supported R f.1).1 f.2 he) (hj e he), chartSection]
  exact Proj.twistingSheaf.const_apply _ _ _ _ _ _ x

/-- On a nonempty chart, distinct Laurent monomials give linearly independent sections: the
coordinates are nonzerodivisors, so clearing denominators loses nothing. -/
private lemma chartSectionsHom_injective {S : Finset κ} (hS : S.Nonempty) :
    Function.Injective (chartSectionsHom b m S) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf ↦ ?_
  have hcard : 0 < S.card := Finset.card_pos.2 hS
  set j := (∑ e ∈ f.1.support, exponentBound e) + m.natAbs with hjdef
  have hj : ∀ e ∈ f.1.support, ∀ i ∈ S, 0 ≤ e i + j := fun e he i _ ↦ by
    have h1 := le_exponentBound e i
    have h2 : exponentBound e ≤ ∑ e ∈ f.1.support, exponentBound e :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) he
    omega
  have hjm : 0 ≤ (j : ℤ) * S.card + m := by
    have h1 : (j : ℤ) ≤ j * S.card := by exact_mod_cast Nat.le_mul_of_pos_right j hcard
    omega
  rw [chartSectionsHom_eq_const b f hj hjm, Proj.twistingSheaf.const_eq_zero_iff
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hcard (coordProd_mem b S))] at hf
  obtain ⟨N, hN⟩ := hf
  -- clear the denominators: the numerators form a polynomial killed by a power of `∏_{i ∈ S} xᵢ`
  have hP := congrArg (equivMvPolynomial b) hN
  simp only [map_mul, map_pow, map_sum, map_smul, map_zero, coordProd_eq_symmetricAlgebra,
    b.equivMvPolynomial_symmetricAlgebra_apply, MvPolynomial.monomial_pow, one_pow, Finset.mul_sum,
    mul_smul_comm, MvPolynomial.monomial_mul_monomial, mul_one] at hP
  have hmem : ∀ e ∈ f.1.support, e ∈ chartExponents m S :=
    fun e he ↦ (Finsupp.mem_supported R f.1).1 f.2 he
  refine Subtype.ext (Finsupp.ext fun e₀ ↦ ?_)
  by_cases he₀ : e₀ ∈ f.1.support
  · have hc := congrArg (fun q : MvPolynomial κ R ↦
      q.coeff (N • indicatorExponent S + numeratorExponent e₀ S j)) hP
    rw [MvPolynomial.coeff_sum, AddMonoidAlgebra.coeff_zero, Finset.sum_eq_single e₀] at hc
    · simpa [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial] using hc
    · intro e he hne
      have hD : N • indicatorExponent S + numeratorExponent e S j ≠
          N • indicatorExponent S + numeratorExponent e₀ S j := fun h ↦ hne <| funext fun i ↦ by
        have := congrArg (fun d : κ →₀ ℕ ↦ (d i : ℤ)) h
        simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Nat.cast_add, coe_numeratorExponent (hmem e he) (hj e he),
          coe_numeratorExponent (hmem e₀ he₀) (hj e₀ he₀)] at this
        omega
      simp [MvPolynomial.coeff_monomial, hD]
    · exact fun h ↦ (h he₀).elim
  · simpa using he₀

/-- The Laurent exponent `d - k 1_S` of the monomial `xᵈ / (∏_{i ∈ S} xᵢ)ᵏ`. -/
private def shiftExponent (S : Finset κ) (k : ℕ) (d : κ →₀ ℕ) : κ → ℤ :=
  fun i ↦ d i - if i ∈ S then (k : ℤ) else 0

private lemma shiftExponent_mem_chartExponents {S : Finset κ} {k : ℕ} {d : κ →₀ ℕ}
    (hd : (d.degree : ℤ) = (k * S.card : ℕ) + m) : shiftExponent S k d ∈ chartExponents m S := by
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [Finsupp.degree_eq_sum, Nat.cast_sum] at hd
    simp only [shiftExponent, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul, hd]
    push_cast
    ring
  · by_contra hiS
    have := mem_negSupport.1 hi
    simp only [shiftExponent, hiS, ite_false, sub_zero] at this
    omega

omit [Fintype κ] in
private lemma add_shiftExponent_nonneg (S : Finset κ) (k : ℕ) (d : κ →₀ ℕ) :
    ∀ i ∈ S, 0 ≤ shiftExponent S k d i + k := fun i hi ↦ by
  simp [shiftExponent, hi]

private lemma numeratorExponent_shiftExponent {S : Finset κ} {k : ℕ} {d : κ →₀ ℕ}
    (hd : (d.degree : ℤ) = (k * S.card : ℕ) + m) :
    numeratorExponent (shiftExponent S k d) S k = d := by
  ext i
  refine Nat.cast_injective (R := ℤ) ?_
  rw [coe_numeratorExponent (shiftExponent_mem_chartExponents hd)
    (add_shiftExponent_nonneg S k d)]
  simp only [shiftExponent]
  split_ifs <;> ring

/-- On a nonempty chart, every section of `𝒪(m)` is a Laurent polynomial. -/
private lemma chartSectionsHom_surjective {S : Finset κ} (hS : S.Nonempty) :
    Function.Surjective (chartSectionsHom b m S) := by
  intro s
  obtain ⟨k, J, hJ, r, hr, rfl⟩ := Proj.twistingSheaf.exists_eq_const_basicOpen
    (coordProd_mem b S) (Finset.card_pos.2 hS) s
  set p := equivMvPolynomial b r with hpdef
  have hp : p.IsHomogeneous J :=
    (_root_.SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff R M b J r).2 hr
  have hdeg (d : κ →₀ ℕ) (hd : d ∈ p.support) : (d.degree : ℤ) = (k * S.card : ℕ) + m := by
    rw [← hJ, Finsupp.degree_eq_weight_one]
    exact_mod_cast hp (MvPolynomial.mem_support_iff.1 hd)
  -- the section `r / (∏_{i ∈ S} xᵢ)ᵏ` is the sum of the Laurent monomials `xᵈ / (∏_{i ∈ S} xᵢ)ᵏ`
  let f : (κ → ℤ) →₀ R := ∑ d ∈ p.support, Finsupp.single (shiftExponent S k d) (p.coeff d)
  have hf : f ∈ Finsupp.supported R R (chartExponents m S) :=
    Submodule.sum_mem _ fun d hd ↦
      Finsupp.single_mem_supported R _ (shiftExponent_mem_chartExponents (hdeg d hd))
  refine ⟨⟨f, hf⟩, ?_⟩
  have h : chartSectionsHom b m S ⟨f, hf⟩ =
      ∑ d ∈ p.support, chartSectionHom b m S (shiftExponent S k d) (p.coeff d) := by
    simp [chartSectionsHom, f, map_sum]
  have hr' : r = ∑ d ∈ p.support, p.coeff d • b.symmetricAlgebra d := by
    refine (equivMvPolynomial b).injective ?_
    rw [← hpdef]
    simp only [map_sum, map_smul, b.equivMvPolynomial_symmetricAlgebra_apply,
      MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    exact MvPolynomial.as_sum p
  refine Proj.twistingSheaf.ext fun x ↦ ?_
  rw [h]
  refine (Proj.twistingSheaf.sum_apply _ _ x).trans <| (Finset.sum_congr rfl fun d hd ↦ ?_).trans <|
    (Localization.mk_sum _ _ _).symm.trans <| (congrArg (Localization.mk · _) hr'.symm).trans
      (Proj.twistingSheaf.const_apply _ _ _ _ _ _ x).symm
  rw [chartSectionHom_apply b (shiftExponent_mem_chartExponents (hdeg d hd))
    (add_shiftExponent_nonneg S k d), chartSection]
  refine (Proj.twistingSheaf.const_apply _ _ _ _ _ _ x).trans ?_
  rw [numeratorExponent_shiftExponent (hdeg d hd)]

end Chart

/-! ### Determinants of tuples of coordinates -/

section Determinant

open Matrix Equiv

variable {N : ℕ}

/-- The matrix whose column `t` is the basis vector of the coordinate `a t`, in an enumeration
`e` of the coordinates. Its determinant is the sign of `a` when `a` is a bijection, and zero
otherwise. -/
private def coordMatrix (e : Fin N ≃ κ) {ι : Type*} (a : ι → κ) : Matrix (Fin N) ι ℤ :=
  Matrix.of fun s t ↦ if e.symm (a t) = s then 1 else 0

private lemma det_coordMatrix_of_not_surjective (e : Fin N ≃ κ) {a : Fin N → κ}
    (ha : ¬ Function.Surjective a) : (coordMatrix e a).det = 0 := by
  obtain ⟨c, hc⟩ := not_forall.1 ha
  refine det_eq_zero_of_row_eq_zero (e.symm c) fun t ↦ ?_
  simp only [coordMatrix, of_apply, e.symm_apply_eq, Equiv.apply_symm_apply, ite_eq_right_iff]
  exact fun h ↦ (hc ⟨t, h⟩).elim

private lemma det_coordMatrix_self (e : Fin N ≃ κ) : (coordMatrix e e).det = 1 := by
  have : coordMatrix e e = 1 := by
    ext s t
    simp [coordMatrix, Matrix.one_apply, eq_comm]
  rw [this, det_one]

private lemma det_coordMatrix_comp (e : Fin N ≃ κ) (a : Fin N → κ) (σ : Perm (Fin N)) :
    (coordMatrix e (a ∘ σ)).det = Perm.sign σ * (coordMatrix e a).det :=
  det_permute' σ (coordMatrix e a)

/-- The alternating sum of the determinants of the faces of a tuple of `N + 1` coordinates
vanishes: it is the Laplace expansion along a row of ones of a matrix whose first row is the sum
of the others. -/
private lemma sum_det_coordMatrix (e : Fin N ≃ κ) (k : Fin (N + 1) → κ) :
    ∑ m : Fin (N + 1), (-1 : ℤ) ^ (m : ℕ) * (coordMatrix e (k ∘ m.succAbove)).det = 0 := by
  let B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ :=
    Matrix.of fun i t ↦ Fin.cases (1 : ℤ) (fun s ↦ coordMatrix e k s t) i
  have hB : B.det = 0 := by
    refine exists_vecMul_eq_zero_iff.1 ⟨Fin.cons 1 fun _ ↦ -1, fun h ↦ by
      simpa using congrFun h 0, funext fun t ↦ ?_⟩
    simp [B, vecMul, dotProduct, Fin.sum_univ_succ, coordMatrix]
  rw [det_succ_row_zero] at hB
  simpa [B, coordMatrix, Matrix.submatrix] using hB

private lemma val_succAbove {n : ℕ} (m : Fin (n + 1)) (t : Fin n) :
    (m.succAbove t : ℕ) = if (t : ℕ) < m then (t : ℕ) else (t : ℕ) + 1 := by
  rcases lt_or_ge (t : ℕ) m with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    simp [h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)]
    simp only [Fin.val_succ]
    split_ifs <;> omega

/-- The map `Fin (n + 2) → Fin (n + 1)` which repeats the entry `p + 1` at position `p`. -/
private def dupAt {n : ℕ} (p : Fin n) (t : Fin (n + 2)) : Fin (n + 1) :=
  ⟨if (t : ℕ) = p then p + 1 else if (t : ℕ) < p then t else t - 1, by
    have := p.2; have := t.2; split_ifs <;> omega⟩

private lemma dupAt_comp_succAbove_left {n : ℕ} (p : Fin n) :
    dupAt p ∘ (⟨p, by omega⟩ : Fin (n + 2)).succAbove = id := by
  funext t
  ext
  simp only [dupAt, Function.comp_apply, val_succAbove, id_eq]
  split_ifs <;> omega

private lemma dupAt_comp_succAbove_right {n : ℕ} (p : Fin n) :
    dupAt p ∘ (⟨p + 2, by omega⟩ : Fin (n + 2)).succAbove = swap p.castSucc p.succ := by
  funext t
  rw [Function.comp_apply, swap_apply_def]
  split_ifs with h₁ h₂ <;> ext <;>
    simp only [dupAt, val_succAbove, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at * <;>
    split_ifs <;> omega

private lemma not_injective_dupAt_comp_succAbove {n : ℕ} (p : Fin n) (m : Fin (n + 2))
    (h₁ : (m : ℕ) ≠ p) (h₂ : (m : ℕ) ≠ p + 2) :
    ¬ Function.Injective (dupAt p ∘ m.succAbove) := by
  intro hinj
  obtain ⟨x, hx⟩ := Fin.exists_succAbove_eq (x := ⟨p, by omega⟩) (y := m)
    (by simp [Fin.ext_iff]; omega)
  obtain ⟨y, hy⟩ := Fin.exists_succAbove_eq (x := ⟨p + 2, by omega⟩) (y := m)
    (by simp [Fin.ext_iff]; omega)
  have hxy : x ≠ y := by
    rintro rfl
    rw [hx] at hy
    simp [Fin.ext_iff] at hy
  refine hxy (hinj ?_)
  simp only [Function.comp_apply, hx, hy]
  ext
  simp [dupAt]

open Limits OrderDual in
open scoped Classical in
/-- The product of the charts of the coordinates `a 0, …, a n` is the intersection of all the
charts exactly when every coordinate occurs in `a`. -/
private lemma ofDual_pi_eq_univ_iff [Fintype κ] {n : ℕ} (a : Fin (n + 1) → κ) :
    ofDual (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ)) = Finset.univ ↔ Function.Surjective a := by
  rw [CompleteLattice.finite_product_eq_finset_image_inf
    (fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)) a, Finset.ofDual_inf,
    show (Finset.univ.image a).sup (ofDual ∘ fun i ↦ toDual {i}) = Finset.univ.image a from
      Finset.sup_singleton_eq_self _, Finset.eq_univ_iff_forall]
  simp [Function.Surjective, eq_comm]

end Determinant

/-! ### The Čech complex of the standard cover -/

section Cech

open Limits Opposite OrderDual TauCeti.CategoryTheory

variable [Fintype κ] [DecidableEq κ] (m : ℤ)

/-- The standard opens `D₊(∏_{i ∈ S} xᵢ)`, as a functor on the finite sets of coordinates ordered
by reverse inclusion; the empty set goes to the whole space. -/
private def chartFunctor : (Finset κ)ᵒᵈ ⥤ (Proj 𝒜).Opens :=
  Monotone.functor (f := fun S ↦ Proj.basicOpen 𝒜 (coordProd b (ofDual S))) fun S S' h ↦ by
    simp only [basicOpen_coordProd]
    exact Finset.inf_mono h

/-- The Laurent polynomials of degree `m` whose monomials are negative only in coordinates of `S`,
as a presheaf on the finite sets of coordinates ordered by reverse inclusion. -/
private def laurentPresheaf : ((Finset κ)ᵒᵈ)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj S := AddCommGrpCat.of (Finsupp.supported R R (chartExponents m (ofDual S.unop)))
  map f := AddCommGrpCat.ofHom (Submodule.inclusion
    (Finsupp.supported_mono (chartExponents_mono (leOfHom f.unop)))).toAddMonoidHom

/-- The sections of `𝒪(m)` as a presheaf of abelian groups. -/
private abbrev sectionsPresheaf : (Proj 𝒜).Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ((SheafOfModules.toSheaf (Proj 𝒜).ringCatSheaf).obj (Proj.twistingSheaf 𝒜 m)).obj

/-- Laurent polynomials as sections of `𝒪(m)` over the standard opens. -/
private def laurentToSections :
    laurentPresheaf (R := R) (κ := κ) m ⟶
      (chartFunctor b).op ⋙ sectionsPresheaf (R := R) (M := M) m where
  app S := AddCommGrpCat.ofHom (chartSectionsHom b m (ofDual S.unop))
  naturality S S' f := by
    ext ⟨g, hg⟩
    have hmem : ∀ e ∈ g.support, e ∈ chartExponents m (ofDual S.unop) :=
      fun e he ↦ (Finsupp.mem_supported R g).1 hg he
    -- the maps of `laurentPresheaf` are inclusions, which do not change the Laurent polynomial
    let φ := ((sectionsPresheaf (R := R) (M := M) m).map ((chartFunctor b).map f.unop).op).hom
    refine (chartSectionsHom_eq_sum b (S := ofDual S'.unop) ⟨g, _⟩).trans <|
      (Finset.sum_congr rfl fun e he ↦ ?_).trans <| (map_sum φ _ _).symm.trans
        (congrArg φ (chartSectionsHom_eq_sum b ⟨g, hg⟩).symm)
    have he' : e ∈ chartExponents m (ofDual S'.unop) :=
      chartExponents_mono (leOfHom f.unop) (hmem e he)
    rw [chartSectionHom_apply b (hmem e he) (fun i _ ↦ le_exponentBound e i),
      chartSectionHom_apply b he' (fun i _ ↦ le_exponentBound e i)]
    exact (res_chartSection b (leOfHom ((chartFunctor b).map f.unop)) (hmem e he) he' _ _ _).symm

omit [Fintype κ] [DecidableEq κ] in
private lemma chartFunctor_obj (S : (Finset κ)ᵒᵈ) :
    (chartFunctor b).obj S = Proj.basicOpen 𝒜 (coordProd b (ofDual S)) :=
  rfl

omit [Fintype κ] [DecidableEq κ] in
private lemma chartFunctor_obj_singleton (i : κ) :
    (chartFunctor b).obj (toDual {i}) = Proj.basicOpen 𝒜 (ι R M (b i)) := by
  simp [chartFunctor_obj, coordProd]

omit [Fintype κ] in
/-- The product of the charts of the coordinates `a 0, …, a n` in the category of finite sets of
coordinates is the set of these coordinates, by
`CategoryTheory.Limits.CompleteLattice.finite_product_eq_finset_image_inf`. -/
private lemma ofDual_pi_toDual_singleton {n : ℕ} (a : Fin (n + 1) → κ) :
    ofDual (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ)) = Finset.univ.image a := by
  rw [CompleteLattice.finite_product_eq_finset_image_inf (fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ))
    a, Finset.ofDual_inf]
  exact Finset.sup_singleton_eq_self _

omit [Fintype κ] [DecidableEq κ] in
private lemma isAffineOpen_inf_chartFunctor_obj_singleton (s : Finset κ) (hs : s.Nonempty) :
    IsAffineOpen (s.inf fun i ↦ (chartFunctor b).obj (toDual {i})) := by
  have : (s.inf fun i ↦ (chartFunctor b).obj (toDual {i})) = Proj.basicOpen 𝒜 (coordProd b s) := by
    rw [basicOpen_coordProd]
    exact Finset.inf_congr rfl fun i _ ↦ chartFunctor_obj_singleton b i
  rw [this]
  exact Proj.isAffineOpen_basicOpen 𝒜 _ (coordProd_mem b s) (Finset.card_pos.2 hs)

omit [Fintype κ] [DecidableEq κ] in
private lemma iSup_chartFunctor_obj_singleton : ⨆ i, (chartFunctor b).obj (toDual {i}) = ⊤ := by
  simp_rw [chartFunctor_obj_singleton]
  exact iSup_basicOpen_ι_eq_top R M b b.span_eq

private lemma isIso_laurentToSections_app {S : (Finset κ)ᵒᵈ} (hS : (ofDual S).Nonempty) :
    IsIso ((laurentToSections b m).app (op S)) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    ⟨chartSectionsHom_injective b hS, chartSectionsHom_surjective b hS⟩

private lemma isIso_cechComplexFunctor_map_laurentToSections :
    IsIso ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
      (laurentToSections b m)) := by
  have (n : ℕ) : IsIso (((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
      (laurentToSections b m)).f n) := by
    have (a : Fin (n + 1) → κ) : IsIso ((laurentToSections b m).app
        (op (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ)))) :=
      isIso_laurentToSections_app b m
        ⟨a 0, Finset.singleton_subset_iff.1
          (leOfHom (Pi.π (fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ)) 0))⟩
    rw [cechComplexFunctor_map_f]
    exact Pi.map_isIso _
  exact HomologicalComplex.Hom.isIso_of_components _

/-! ### Splitting Laurent polynomials by negative support -/

/-- The projection onto the Laurent monomials with negative support exactly `T`. -/
private def negSupportProj (T : Finset κ) :
    laurentPresheaf (R := R) (κ := κ) m ⟶ laurentPresheaf (R := R) (κ := κ) m where
  app _ := AddCommGrpCat.ofHom
    (LinearMap.toAddMonoidHom (Finsupp.filterSupported (negSupport · = T) fun _ he _ ↦ he))
  -- restriction is an inclusion, so both composites filter the same Laurent polynomial
  naturality _ _ f := AddCommGrpCat.hom_ext (congrArg LinearMap.toAddMonoidHom
    ((Finsupp.filterSupported_comp_inclusion (negSupport · = T)
      (chartExponents_mono (leOfHom f.unop)) fun _ he _ ↦ he).trans
      (Finsupp.inclusion_comp_filterSupported (negSupport · = T) (fun _ he _ ↦ he)
        (chartExponents_mono (leOfHom f.unop))).symm))

omit [DecidableEq κ] in
private lemma sum_filterSupported_negSupport [DecidableEq κ] {s : Set (κ → ℤ)}
    (f : Finsupp.supported R R s) :
    ∑ T : Finset κ, Finsupp.filterSupported (negSupport · = T) (fun _ he _ ↦ he) f = f := by
  refine Subtype.ext (Finsupp.ext fun e ↦ ?_)
  simp [Finsupp.finsetSum_apply, Finsupp.filter_apply]

private lemma sum_negSupportProj :
    ∑ T : Finset κ, negSupportProj (R := R) (κ := κ) m T = 𝟙 _ := by
  refine NatTrans.ext (funext fun S ↦ ?_)
  rw [NatTrans.app_sum, NatTrans.id_app]
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun f ↦ ?_)
  -- a morphism of abelian groups acts through `AddCommGrpCat.homAddEquiv`, which is additive
  change AddCommGrpCat.homAddEquiv (∑ T : Finset κ, (negSupportProj (R := R) m T).app S) f = f
  rw [map_sum, AddMonoidHom.finsetSum_apply]
  exact sum_filterSupported_negSupport f

/-- Restriction of Laurent polynomials to the intersection with the chart of `c`. -/
private def restrictToChart (c : κ) :
    laurentPresheaf (R := R) (κ := κ) m ⟶
      (prod.functor.obj (toDual {c})).op ⋙ laurentPresheaf (R := R) (κ := κ) m where
  app S := (laurentPresheaf m).map (prod.snd : toDual {c} ⨯ S.unop ⟶ S.unop).op
  naturality _ _ _ := rfl

/-- A Laurent monomial with negative support `T` which is negative only in coordinates of
`{c} ∪ S`, for a coordinate `c ∉ T`, is negative only in coordinates of `S`. -/
private lemma mem_chartExponents_of_subset_union {c : κ} {T : Finset κ} (hc : c ∉ T)
    {S S' : Finset κ} (h : S' ⊆ {c} ∪ S) :
    ∀ e ∈ chartExponents m S', negSupport e = T → e ∈ chartExponents m S :=
  fun e he heT ↦ ⟨he.1, fun i hi ↦ by
    have hi' := Finset.mem_union.1 (h (he.2 hi))
    rw [Finset.mem_singleton] at hi'
    exact hi'.resolve_left fun h ↦ hc (h ▸ heT ▸ hi)⟩

/-- On the monomials with negative support `T`, a Laurent polynomial on the intersection with the
chart of a coordinate `c ∉ T` is already a Laurent polynomial on the original chart. -/
private def extendFromChart {c : κ} {T : Finset κ} (hc : c ∉ T) :
    (prod.functor.obj (toDual {c})).op ⋙ laurentPresheaf (R := R) (κ := κ) m ⟶
      laurentPresheaf (R := R) (κ := κ) m where
  -- a binary product of finite sets of coordinates is their union
  app S := AddCommGrpCat.ofHom (LinearMap.toAddMonoidHom (Finsupp.filterSupported (negSupport · = T)
    (mem_chartExponents_of_subset_union m hc (CompleteLattice.prod_eq_inf (toDual {c}) S.unop).ge)))
  -- restriction is an inclusion, so both composites filter the same Laurent polynomial
  naturality X Y f := AddCommGrpCat.hom_ext (congrArg LinearMap.toAddMonoidHom
    ((Finsupp.filterSupported_comp_inclusion (negSupport · = T)
      (chartExponents_mono (leOfHom ((prod.functor.obj (toDual ({c} : Finset κ))).map f.unop)))
      (mem_chartExponents_of_subset_union m hc
        (CompleteLattice.prod_eq_inf (toDual {c}) Y.unop).ge)).trans
      (Finsupp.inclusion_comp_filterSupported (negSupport · = T)
        (mem_chartExponents_of_subset_union m hc
          (CompleteLattice.prod_eq_inf (toDual {c}) X.unop).ge)
        (chartExponents_mono (leOfHom f.unop))).symm))

private lemma restrictToChart_comp_extendFromChart {c : κ} {T : Finset κ} (hc : c ∉ T) :
    restrictToChart (R := R) (κ := κ) m c ≫ extendFromChart (R := R) m hc =
      negSupportProj (R := R) m T :=
  -- restriction is an inclusion and both sides filter the same Laurent polynomial
  NatTrans.ext (funext fun S ↦ AddCommGrpCat.hom_ext (congrArg LinearMap.toAddMonoidHom
    (Finsupp.filterSupported_comp_inclusion (negSupport · = T)
      (chartExponents_mono (leOfHom (prod.snd : toDual {c} ⨯ S.unop ⟶ S.unop)))
      (mem_chartExponents_of_subset_union m hc
        (CompleteLattice.prod_eq_inf (toDual {c}) S.unop).ge))))

/-! ### Vanishing of the Čech cohomology -/

/-- The Čech complex of Laurent polynomials for the cover of the standard charts. -/
private abbrev laurentCech : CochainComplex AddCommGrpCat.{u} ℕ :=
  (cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).obj
    (laurentPresheaf (R := R) (κ := κ) m)

/-- The monomials with negative support `T ∌ c` contribute nothing to Čech cohomology in positive
degrees: they come from the chart of `c`, on which the cover has a member equal to the whole
chart. -/
private lemma homologyMap_negSupportProj_of_notMem {c : κ} {T : Finset κ} (hc : c ∉ T) (q : ℕ) :
    HomologicalComplex.homologyMap
      ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (negSupportProj (R := R) m T)) (q + 1) = 0 := by
  have hex := ((quasiIso_cechAugmentation_iff _ isTerminalTop _).1
    (quasiIso_cechAugmentation_prod_of_hom (fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ))
      isTerminalTop (laurentPresheaf (R := R) (κ := κ) m) (toDual {c}) (𝟙 _))).2 q
  rw [← restrictToChart_comp_extendFromChart m hc, Functor.map_comp,
    HomologicalComplex.homologyMap_comp, hex.isZero_homology.eq_of_tgt
      (HomologicalComplex.homologyMap _ _) 0, zero_comp]

/-- The monomials with all exponents negative contribute nothing to Čech cohomology in degree `q`
when `q + 1` coordinates do not suffice to cover all coordinates, or when there are no such
monomials of degree `m`. -/
private lemma homologyMap_negSupportProj_univ {q : ℕ}
    (h : q + 1 < Fintype.card κ ∨ -(Fintype.card κ : ℤ) < m) :
    HomologicalComplex.homologyMap
      ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (negSupportProj (R := R) m Finset.univ)) q = 0 := by
  refine HomologicalComplex.homologyMap_eq_zero_of_f_eq_zero _ _ ?_
  rw [cechComplexFunctor_map_f]
  refine Pi.hom_ext _ _ fun a ↦ (Pi.map_π _ a).trans (Eq.trans ?_ zero_comp.symm)
  -- no Laurent monomial over a product of `q + 1` charts has all exponents negative
  have hno : ∀ e ∈ chartExponents m (ofDual (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ))),
      negSupport e ≠ Finset.univ := by
    rintro e ⟨hsum, hneg⟩ huniv
    rcases h with h | h
    · have := (Finset.card_le_card (hneg.trans (ofDual_pi_toDual_singleton (n := q) a).le)).trans
        Finset.card_image_le
      rw [huniv, Finset.card_univ, Finset.card_fin] at this
      omega
    · have hlt : ∀ i, e i ≤ -1 := fun i ↦ by
        have := mem_negSupport.1 (huniv ▸ Finset.mem_univ i : i ∈ negSupport e)
        omega
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hlt i
      rw [hsum, Finset.sum_const, Finset.card_univ] at this
      simp only [nsmul_eq_mul, mul_neg, mul_one] at this
      omega
  have hzero : (negSupportProj (R := R) m Finset.univ).app
      (op (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ))) = 0 := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun f ↦ Subtype.ext ?_)
    -- the projection is the filter on the underlying Laurent polynomial
    refine (Finsupp.filterSupported_apply _ _ f).trans ?_
    exact (Finsupp.filter_eq_zero_iff _ _).2 fun e he ↦ Finsupp.notMem_support_iff.1 fun hf ↦
      hno e ((Finsupp.mem_supported R f.1).1 f.2 hf) he
  rw [hzero]
  exact comp_zero

private lemma isZero_homology_laurentCech {q : ℕ} (hq : 0 < q)
    (h : q + 1 < Fintype.card κ ∨ -(Fintype.card κ : ℤ) < m) :
    IsZero ((laurentCech (R := R) (κ := κ) m).homology q) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hq
  rw [zero_add] at h ⊢
  have hsum : ∑ T : Finset κ, (cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
      (negSupportProj (R := R) m T) = 𝟙 (laurentCech (R := R) (κ := κ) m) := by
    rw [← Functor.map_sum, sum_negSupportProj, CategoryTheory.Functor.map_id]
  rw [IsZero.iff_id_eq_zero, ← HomologicalComplex.homologyMap_id, ← hsum,
    ← HomologicalComplex.homologyFunctor_map, Functor.map_sum]
  refine Finset.sum_eq_zero fun T _ ↦ ?_
  rw [HomologicalComplex.homologyFunctor_map]
  by_cases hT : T = Finset.univ
  · subst hT
    exact homologyMap_negSupportProj_univ m h
  · obtain ⟨c, hc⟩ : ∃ c, c ∉ T := by
      by_contra! hall
      exact hT (Finset.eq_univ_iff_forall.2 hall)
    exact homologyMap_negSupportProj_of_notMem m hc q

/-! ### The top degree

On projective space of dimension `n + 1`, the Čech complex of the standard cover has a last
interesting degree `n + 1`, whose terms are indexed by the tuples of `n + 2` coordinates. Fix an
enumeration `e` of the coordinates. Its Čech cohomology is the module of Laurent polynomials of
degree `m` all of whose exponents are negative: a cocycle with all exponents negative is
alternating in the tuple of coordinates, so it is determined by its value at `e`, and the
cocycle `a ↦ det(a) xᵉ` realizes every such Laurent polynomial, with `det(a)` the determinant of
the matrix of the tuple `a` in the enumeration `e`. -/

/-- The Laurent exponents of degree `m` all of whose entries are negative. -/
private def topExponents : Set (κ → ℤ) :=
  {e : κ → ℤ | ∑ i : κ, e i = m ∧ ∀ i, e i < 0}

omit [DecidableEq κ] in
private lemma negSupport_eq_univ_iff {e : κ → ℤ} : negSupport e = Finset.univ ↔ ∀ i, e i < 0 := by
  simp [Finset.eq_univ_iff_forall, mem_negSupport]

/-- The part of a Laurent polynomial on a chart all of whose exponents are negative. -/
private def topPart (S : Finset κ) :
    Finsupp.supported R R (chartExponents m S) →ₗ[R]
      Finsupp.supported R R (topExponents (κ := κ) m) :=
  Finsupp.filterSupported (negSupport · = Finset.univ) fun _ he h ↦
    ⟨he.1, negSupport_eq_univ_iff.1 h⟩

/-- A Laurent polynomial all of whose exponents are negative, as a Laurent polynomial on a chart:
it is zero unless the chart is the intersection of all the standard charts. -/
private def fromTop (S : Finset κ) :
    Finsupp.supported R R (topExponents (κ := κ) m) →ₗ[R]
      Finsupp.supported R R (chartExponents m S) :=
  Finsupp.filterSupported (negSupport · ⊆ S) fun _ he h ↦ ⟨he.1, h⟩

/-- `topPart` as a morphism of abelian groups. -/
private abbrev topPartHom (S : Finset κ) :
    AddCommGrpCat.of (Finsupp.supported R R (chartExponents m S)) ⟶
      AddCommGrpCat.of (Finsupp.supported R R (topExponents (κ := κ) m)) :=
  AddCommGrpCat.ofHom (topPart m S).toAddMonoidHom

/-- `fromTop` as a morphism of abelian groups. -/
private abbrev fromTopHom (S : Finset κ) :
    AddCommGrpCat.of (Finsupp.supported R R (topExponents (κ := κ) m)) ⟶
      AddCommGrpCat.of (Finsupp.supported R R (chartExponents m S)) :=
  AddCommGrpCat.ofHom (fromTop m S).toAddMonoidHom

private lemma coe_fromTopHom_apply (S : Finset κ)
    (ℓ : Finsupp.supported R R (topExponents (κ := κ) m)) :
    ((fromTopHom (R := R) m S ℓ : Finsupp.supported R R (chartExponents m S)) : (κ → ℤ) →₀ R) =
      Finsupp.filter (negSupport · ⊆ S) (ℓ : (κ → ℤ) →₀ R) :=
  Finsupp.filterSupported_apply _ _ ℓ

private lemma coe_topPartHom_apply (S : Finset κ)
    (x : Finsupp.supported R R (chartExponents m S)) :
    ((topPartHom (R := R) m S x : Finsupp.supported R R (topExponents (κ := κ) m)) :
      (κ → ℤ) →₀ R) = Finsupp.filter (negSupport · = Finset.univ) (x : (κ → ℤ) →₀ R) :=
  Finsupp.filterSupported_apply _ _ x

omit [DecidableEq κ] in
private lemma val_laurentPresheaf_map_apply {X Y : ((Finset κ)ᵒᵈ)ᵒᵖ} (g : X ⟶ Y)
    (x : (laurentPresheaf (R := R) m).obj X) :
    ((laurentPresheaf (R := R) m).map g x).1 = x.1 :=
  rfl

private lemma filter_eq_zero_of_ne_univ {S : Finset κ} (hS : S ≠ Finset.univ)
    (x : Finsupp.supported R R (chartExponents m S)) :
    Finsupp.filter (negSupport · = Finset.univ) x.1 = 0 :=
  (Finsupp.filter_eq_zero_iff _ _).2 fun _ he ↦ Finsupp.notMem_support_iff.1 fun hx ↦
    hS (Finset.univ_subset_iff.1 (he ▸ ((Finsupp.mem_supported R x.1).1 x.2 hx).2))

private lemma filter_subset_univ (x : Finsupp.supported R R (topExponents (κ := κ) m)) :
    Finsupp.filter (negSupport · ⊆ Finset.univ) x.1 = x.1 :=
  (Finsupp.filter_eq_self_iff _ _).2 fun _ _ ↦ Finset.subset_univ _

private lemma filter_subset_eq_self {S : Finset κ} (hS : S = Finset.univ)
    (x : Finsupp.supported R R (topExponents (κ := κ) m)) :
    Finsupp.filter (negSupport · ⊆ S) x.1 = x.1 := by
  subst hS
  exact filter_subset_univ m x

variable {n : ℕ} (e : Fin (n + 1 + 1) ≃ κ)

/-- The degree `n + 1` cochain `a ↦ det(a) ℓ`, a cocycle by Laplace expansion. -/
private def topCochain : AddCommGrpCat.of (Finsupp.supported R R (topExponents (κ := κ) m)) ⟶
    (laurentCech (R := R) (κ := κ) m).X (n + 1) :=
  Pi.lift fun a ↦ (coordMatrix e a).det • fromTopHom (R := R) m _

/-- The value at `e` of a degree `n + 1` cochain, restricted to the monomials all of whose
exponents are negative. -/
private def evalTop : (laurentCech (R := R) (κ := κ) m).X (n + 1) ⟶
    AddCommGrpCat.of (Finsupp.supported R R (topExponents (κ := κ) m)) :=
  Pi.π _ (⇑e) ≫ topPartHom (R := R) m _

omit [Fintype κ] [DecidableEq κ] in
private lemma hom_sum_apply {A B : AddCommGrpCat.{u}} {ι : Type*} (s : Finset ι)
    (f : ι → (A ⟶ B)) (x : A) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  change AddCommGrpCat.homAddEquiv (∑ i ∈ s, f i) x = _
  rw [map_sum, AddMonoidHom.finsetSum_apply]
  rfl

omit [Fintype κ] in
private lemma map_comp_topPart [Fintype κ] {X Y : ((Finset κ)ᵒᵈ)ᵒᵖ} (g : X ⟶ Y)
    (h : ofDual X.unop ≠ Finset.univ) :
    (laurentPresheaf (R := R) m).map g ≫
      topPartHom (R := R) m (ofDual Y.unop) = 0 := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ Subtype.ext ?_)
  exact (coe_topPartHom_apply m _ _).trans (filter_eq_zero_of_ne_univ m h x)

private lemma fromTopHom_comp_map {X Y : ((Finset κ)ᵒᵈ)ᵒᵖ} (g : X ⟶ Y)
    (hX : ofDual X.unop = Finset.univ) :
    fromTopHom (R := R) m (ofDual X.unop) ≫ (laurentPresheaf (R := R) m).map g =
      fromTopHom (R := R) m (ofDual Y.unop) := by
  have hY : ofDual Y.unop = Finset.univ :=
    Finset.univ_subset_iff.1 (hX ▸ (leOfHom g.unop : Y.unop ≤ X.unop))
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun ℓ ↦ Subtype.ext ?_)
  refine (val_laurentPresheaf_map_apply m g (fromTopHom (R := R) m _ ℓ)).trans ?_
  exact ((coe_fromTopHom_apply m _ ℓ).trans (filter_subset_eq_self m hX ℓ)).trans
    ((coe_fromTopHom_apply m _ ℓ).trans (filter_subset_eq_self m hY ℓ)).symm

private lemma d_comp_evalTop :
    (laurentCech (R := R) (κ := κ) m).d n (n + 1) ≫ evalTop m e = 0 := by
  unfold evalTop
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (cechComplexFunctor_obj_d_comp_π (fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ))
      (laurentPresheaf (R := R) m) n ⇑e))).trans
    ((Preadditive.sum_comp _ _ _).trans
      (Finset.sum_eq_zero fun i _ ↦ (Preadditive.zsmul_comp _ _ _).trans ?_))
  refine (congrArg _ ((Category.assoc _ _ _).trans ?_)).trans (zsmul_zero _)
  refine (congrArg _ (map_comp_topPart m _ fun h ↦ ?_)).trans comp_zero
  obtain ⟨c, hc⟩ := ((ofDual_pi_eq_univ_iff (⇑e ∘ i.succAbove)).1 h) (e i)
  exact Fin.succAbove_ne i c (e.injective hc)

private lemma topCochain_comp_π_comp_map (k : Fin (n + 1 + 1 + 1) → κ) (i : Fin (n + 1 + 1 + 1)) :
    topCochain m e ≫ Pi.π _ (k ∘ i.succAbove) ≫ (laurentPresheaf (R := R) m).map
        (Pi.lift fun x ↦ Pi.π (fun j ↦ (toDual {k j} : (Finset κ)ᵒᵈ)) (i.succAbove x)).op =
      (coordMatrix e (k ∘ i.succAbove)).det •
        fromTopHom (R := R) m (ofDual (∏ᶜ fun j ↦ (toDual {k j} : (Finset κ)ᵒᵈ))) := by
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (Pi.lift_comp_π _ _)).trans
    ((Preadditive.zsmul_comp _ _ _).trans ?_))
  by_cases hk : Function.Surjective (k ∘ i.succAbove)
  · refine congrArg _ ?_
    exact fromTopHom_comp_map m _ ((ofDual_pi_eq_univ_iff _).2 hk)
  · rw [det_coordMatrix_of_not_surjective e hk]
    exact (zero_smul _ _).trans (zero_smul _ _).symm

private lemma topCochain_comp_d :
    topCochain m e ≫ (laurentCech (R := R) (κ := κ) m).d (n + 1) (n + 1 + 1) = 0 := by
  refine Pi.hom_ext _ _ fun k ↦ (Category.assoc _ _ _).trans <|
    (congrArg _ (cechComplexFunctor_obj_d_comp_π (fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ))
      (laurentPresheaf (R := R) m) (n + 1) k)).trans <|
      (Preadditive.comp_sum _ _ _).trans (Eq.trans ?_ zero_comp.symm)
  refine (Finset.sum_congr rfl fun i _ ↦ (Preadditive.comp_zsmul _ _ _).trans
    ((congrArg _ (topCochain_comp_π_comp_map m e k i)).trans (smul_smul _ _ _))).trans ?_
  exact Finset.sum_smul.symm.trans ((congrArg (· • _) (sum_det_coordMatrix e k)).trans
    (zero_smul _ _))

private lemma fromTopHom_comp_topPartHom {S : Finset κ} (hS : S = Finset.univ) :
    fromTopHom (R := R) m S ≫ topPartHom (R := R) m S = 𝟙 _ := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun ℓ ↦ Subtype.ext ?_)
  refine (coe_topPartHom_apply m S (fromTopHom (R := R) m S ℓ)).trans ?_
  rw [coe_fromTopHom_apply, filter_subset_eq_self m hS]
  exact (Finsupp.filter_eq_self_iff _ _).2 fun x hx ↦ negSupport_eq_univ_iff.2
    ((Finsupp.mem_supported R _).1 ℓ.2 (Finsupp.mem_support_iff.2 hx)).2

private lemma topCochain_comp_evalTop : topCochain (R := R) m e ≫ evalTop m e = 𝟙 _ := by
  unfold evalTop
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (Pi.lift_comp_π _ _)).trans ?_)
  refine (congrArg (· ≫ _) ((congrArg (· • _) (det_coordMatrix_self e)).trans
    (one_smul _ _))).trans ?_
  exact fromTopHom_comp_topPartHom m ((ofDual_pi_eq_univ_iff _).2 e.surjective)

private lemma topPartHom_eq_zero {S : Finset κ} (hS : S ≠ Finset.univ) :
    topPartHom (R := R) m S = 0 :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦
    Subtype.ext ((coe_topPartHom_apply m _ _).trans (filter_eq_zero_of_ne_univ m hS x)))

private lemma map_comp_topPartHom {X Y : ((Finset κ)ᵒᵈ)ᵒᵖ} (g : X ⟶ Y) :
    (laurentPresheaf (R := R) m).map g ≫ topPartHom (R := R) m (ofDual Y.unop) =
      topPartHom (R := R) m (ofDual X.unop) :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ Subtype.ext
    (((coe_topPartHom_apply m _ _).trans (congrArg _ (val_laurentPresheaf_map_apply m g x))).trans
      (coe_topPartHom_apply m _ x).symm))

variable (n) in
/-- The component at a tuple `b` of a degree `n + 1` cocycle, restricted to the monomials all of
whose exponents are negative. -/
private def topComponent (b : Fin (n + 1 + 1) → κ) :
    (laurentCech (R := R) (κ := κ) m).cycles (n + 1) ⟶
      AddCommGrpCat.of (Finsupp.supported R R (topExponents (κ := κ) m)) :=
  (laurentCech (R := R) (κ := κ) m).iCycles (n + 1) ≫ Pi.π _ b ≫ topPartHom (R := R) m _

private lemma topComponent_eq_zero {b : Fin (n + 1 + 1) → κ} (hb : ¬ Function.Surjective b) :
    topComponent (R := R) m n b = 0 := by
  have h : topPartHom (R := R) m (ofDual (∏ᶜ fun j ↦ (toDual {b j} : (Finset κ)ᵒᵈ))) = 0 :=
    topPartHom_eq_zero m (mt (ofDual_pi_eq_univ_iff b).1 hb)
  exact (congrArg (fun f ↦ (laurentCech (R := R) (κ := κ) m).iCycles (n + 1) ≫ Pi.π _ b ≫ f)
    h).trans ((congrArg _ comp_zero).trans comp_zero)

/-- The cocycle condition on the components with all exponents negative. -/
private lemma sum_topComponent (k : Fin (n + 1 + 1 + 1) → κ) :
    ∑ i : Fin (n + 1 + 1 + 1), (-1 : ℤ) ^ (i : ℕ) • topComponent (R := R) m n (k ∘ i.succAbove) =
      0 := by
  have h0 : (laurentCech (R := R) (κ := κ) m).iCycles (n + 1) ≫
      ((laurentCech (R := R) (κ := κ) m).d (n + 1) (n + 1 + 1) ≫ Pi.π _ k) ≫
        topPartHom (R := R) m (ofDual (∏ᶜ fun j ↦ (toDual {k j} : (Finset κ)ᵒᵈ))) = 0 :=
    (congrArg _ (Category.assoc _ _ _)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (HomologicalComplex.iCycles_d _ _ _)).trans zero_comp))
  refine Eq.trans ?_ h0
  refine Eq.symm ((congrArg (fun f ↦ _ ≫ f ≫ _)
    (cechComplexFunctor_obj_d_comp_π (fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ))
      (laurentPresheaf (R := R) m) (n + 1) k)).trans ?_)
  refine (congrArg _ (Preadditive.sum_comp _ _ _)).trans ((Preadditive.comp_sum _ _ _).trans
    (Finset.sum_congr rfl fun i _ ↦ ?_))
  refine (congrArg _ (Preadditive.zsmul_comp _ _ _)).trans ((Preadditive.comp_zsmul _ _ _).trans
    (congrArg _ ?_))
  exact congrArg _ ((Category.assoc _ _ _).trans (congrArg _ (map_comp_topPartHom m _)))

include e in
private lemma topComponent_comp_swap (a : Fin (n + 1 + 1) → κ) (p : Fin (n + 1)) :
    topComponent (R := R) m n (a ∘ Equiv.swap p.castSucc p.succ) =
      -topComponent (R := R) m n a := by
  have h := sum_topComponent (R := R) m (n := n) (a ∘ dupAt p)
  rw [Fintype.sum_eq_add (⟨p, by omega⟩ : Fin (n + 1 + 1 + 1)) ⟨p + 2, by omega⟩
    (by simp [Fin.ext_iff])] at h
  · have h₁ : a ∘ dupAt p ∘ (⟨p, by omega⟩ : Fin (n + 1 + 1 + 1)).succAbove = a := by
      rw [dupAt_comp_succAbove_left]; rfl
    have h₂ : a ∘ dupAt p ∘ (⟨p + 2, by omega⟩ : Fin (n + 1 + 1 + 1)).succAbove =
        a ∘ Equiv.swap p.castSucc p.succ := by
      rw [dupAt_comp_succAbove_right]
    change (-1 : ℤ) ^ (p : ℕ) • topComponent m n (a ∘ dupAt p ∘ Fin.succAbove _) +
      (-1 : ℤ) ^ ((p : ℕ) + 2) • topComponent m n (a ∘ dupAt p ∘ Fin.succAbove _) = 0 at h
    rw [h₁, h₂, pow_add, neg_one_sq, mul_one, ← smul_add] at h
    have h' := congrArg (fun f ↦ (-1 : ℤ) ^ (p : ℕ) • f) h
    simp only [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul,
      smul_zero] at h'
    exact eq_neg_of_add_eq_zero_right h'
  · rintro i ⟨hi₁, hi₂⟩
    refine (congrArg _ (topComponent_eq_zero m fun hs ↦ ?_)).trans (smul_zero _)
    refine not_injective_dupAt_comp_succAbove p i (fun h ↦ hi₁ (Fin.ext h))
      (fun h ↦ hi₂ (Fin.ext h)) fun x y hxy ↦ ?_
    exact ((Finite.injective_iff_surjective_of_equiv e).2 hs) (congrArg a hxy)

include e in
private lemma topComponent_comp_perm (σ : Equiv.Perm (Fin (n + 1 + 1))) :
    ∀ a : Fin (n + 1 + 1) → κ,
      topComponent (R := R) m n (a ∘ σ) = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • topComponent m n a := by
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin (n + 1) ↦
      Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    trivial
  induction hσ using Submonoid.closure_induction with
  | mem τ hτ =>
    obtain ⟨p, rfl⟩ := hτ
    intro a
    rw [topComponent_comp_swap m e a p, Equiv.Perm.sign_swap (Fin.castSucc_lt_succ (i := p)).ne]
    simp
  | one => intro a; simp
  | mul σ τ _ _ hσ hτ =>
    intro a
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hτ, hσ, smul_smul, Equiv.Perm.sign_mul,
      Units.val_mul, mul_comm]

private lemma topComponent_eq_det_smul (a : Fin (n + 1 + 1) → κ) :
    topComponent (R := R) m n a = (coordMatrix e a).det • topComponent m n ⇑e := by
  by_cases ha : Function.Surjective a
  · let σ : Equiv.Perm (Fin (n + 1 + 1)) := Equiv.ofBijective (e.symm ∘ a)
      ⟨e.symm.injective.comp ((Finite.injective_iff_surjective_of_equiv e).2 ha),
        e.symm.surjective.comp ha⟩
    have haσ : a = ⇑e ∘ ⇑σ := funext fun t ↦ (e.apply_symm_apply (a t)).symm
    rw [haσ, topComponent_comp_perm m e σ, det_coordMatrix_comp, det_coordMatrix_self, mul_one]
  · rw [topComponent_eq_zero m ha, det_coordMatrix_of_not_surjective e ha, zero_smul]

omit [Fintype κ] [DecidableEq κ] in
private lemma homologyMap_eq_of_iCycles_comp {K L : CochainComplex AddCommGrpCat.{u} ℕ}
    {f g : K ⟶ L} {i : ℕ} (h : K.iCycles i ≫ f.f i = K.iCycles i ≫ g.f i) :
    HomologicalComplex.homologyMap f i = HomologicalComplex.homologyMap g i := by
  rw [← cancel_epi (K.homologyπ i), HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.homologyπ_naturality]
  congr 1
  rw [← cancel_mono (L.iCycles i), HomologicalComplex.cyclesMap_i,
    HomologicalComplex.cyclesMap_i, h]

private lemma negSupportProj_univ_app (X : ((Finset κ)ᵒᵈ)ᵒᵖ) :
    (negSupportProj (R := R) m Finset.univ).app X =
      topPartHom (R := R) m (ofDual X.unop) ≫ fromTopHom (R := R) m (ofDual X.unop) := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ Subtype.ext ?_)
  refine (Finsupp.filterSupported_apply _ _ x).trans ?_
  refine Eq.symm ((coe_fromTopHom_apply m _ _).trans ?_)
  refine (congrArg _ (coe_topPartHom_apply m _ x)).trans ?_
  refine (Finsupp.filter_eq_self_iff _ _).2 fun e' he' ↦ ?_
  rw [Finsupp.filter_apply] at he'
  split_ifs at he' with h
  · exact ((Finsupp.mem_supported R _).1 x.2 (Finsupp.mem_support_iff.2 he')).2
  · exact (he' rfl).elim

private lemma iCycles_comp_negSupportProj_univ :
    (laurentCech (R := R) (κ := κ) m).iCycles (n + 1) ≫
        ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
          (negSupportProj (R := R) m Finset.univ)).f (n + 1) =
      (laurentCech (R := R) (κ := κ) m).iCycles (n + 1) ≫ evalTop m e ≫ topCochain m e := by
  refine Pi.hom_ext _ _ fun a ↦ ?_
  refine (Category.assoc _ _ _).trans ((congrArg _ (cechComplexFunctor_map_f_π _ _ _ _ a)).trans
    ?_)
  refine (congrArg (fun f ↦ _ ≫ _ ≫ f) (negSupportProj_univ_app m _)).trans ?_
  refine ((congrArg _ (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm).trans ?_
  refine (congrArg (· ≫ _) (topComponent_eq_det_smul m e a)).trans ?_
  refine (Preadditive.zsmul_comp _ _ _).trans ?_
  refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg _ (Category.assoc _ _ _)).trans
    ((congrArg (fun f ↦ _ ≫ _ ≫ f) (Pi.lift_comp_π _ _)).trans ?_)))
  refine (congrArg _ (Preadditive.comp_zsmul _ _ _)).trans ((Preadditive.comp_zsmul _ _ _).trans
    (congrArg _ ?_))
  exact (Category.assoc _ _ _).symm

private lemma homologyMap_negSupportProj_univ_top :
    HomologicalComplex.homologyMap
      ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (negSupportProj (R := R) m Finset.univ)) (n + 1) = 𝟙 _ := by
  have hsum : ∑ T : Finset κ, (cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
      (negSupportProj (R := R) m T) = 𝟙 (laurentCech (R := R) (κ := κ) m) := by
    rw [← Functor.map_sum, sum_negSupportProj, CategoryTheory.Functor.map_id]
  have hmap : HomologicalComplex.homologyMap (∑ T : Finset κ,
      (cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (negSupportProj (R := R) m T)) (n + 1) = ∑ T : Finset κ, HomologicalComplex.homologyMap
          ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
            (negSupportProj (R := R) m T)) (n + 1) :=
    Functor.map_sum (HomologicalComplex.homologyFunctor _ _ (n + 1)) _ _
  refine Eq.symm ((HomologicalComplex.homologyMap_id _ _).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · (n + 1)) hsum.symm).trans
      (hmap.trans (Finset.sum_eq_single Finset.univ ?_ ?_))))
  · intro T _ hT
    obtain ⟨c, hc⟩ : ∃ c, c ∉ T := by
      by_contra! hall
      exact hT (Finset.eq_univ_iff_forall.2 hall)
    exact homologyMap_negSupportProj_of_notMem m hc n
  · exact fun h ↦ (h (Finset.mem_univ _)).elim

/-- `evalTop` as a map to the complex with the Laurent polynomials with all exponents negative in
degree `n + 1`. -/
private def toSingleTop : laurentCech (R := R) (κ := κ) m ⟶
    (HomologicalComplex.single AddCommGrpCat.{u} (ComplexShape.up ℕ) (n + 1)).obj
      (AddCommGrpCat.of (Finsupp.supported R R (topExponents (κ := κ) m))) :=
  HomologicalComplex.mkHomToSingle (evalTop m e) fun i hi ↦ by
    obtain rfl : i = n := by simpa using hi
    exact d_comp_evalTop m e

/-- `topCochain` as a map from the complex with the Laurent polynomials with all exponents
negative in degree `n + 1`. -/
private def fromSingleTop :
    (HomologicalComplex.single AddCommGrpCat.{u} (ComplexShape.up ℕ) (n + 1)).obj
      (AddCommGrpCat.of (Finsupp.supported R R (topExponents (κ := κ) m))) ⟶
      laurentCech (R := R) (κ := κ) m :=
  HomologicalComplex.mkHomFromSingle (topCochain m e) fun k hk ↦ by
    obtain rfl : k = n + 1 + 1 := by simpa using hk.symm
    exact topCochain_comp_d m e

/-- **The top Čech cohomology of the Laurent polynomials**: in degree `n + 1`, the Čech
cohomology of the standard cover of projective space of dimension `n + 1` is the group of
Laurent polynomials of degree `m` all of whose exponents are negative. -/
private def homologyLaurentCechTopIso :
    (laurentCech (R := R) (κ := κ) m).homology (n + 1) ≅
      AddCommGrpCat.of (Finsupp.supported R R (topExponents (κ := κ) m)) where
  hom := HomologicalComplex.homologyMap (toSingleTop m e) (n + 1) ≫
    (HomologicalComplex.singleObjHomologySelfIso _ _ _).hom
  inv := (HomologicalComplex.singleObjHomologySelfIso _ _ _).inv ≫
    HomologicalComplex.homologyMap (fromSingleTop m e) (n + 1)
  hom_inv_id := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← HomologicalComplex.homologyMap_comp,
      ← homologyMap_negSupportProj_univ_top m (n := n)]
    refine homologyMap_eq_of_iCycles_comp ?_
    rw [iCycles_comp_negSupportProj_univ m e, HomologicalComplex.comp_f, toSingleTop,
      fromSingleTop, HomologicalComplex.mkHomToSingle_f, HomologicalComplex.mkHomFromSingle_f,
      Category.assoc, Iso.inv_hom_id_assoc]
  inv_hom_id := by
    have h : fromSingleTop (R := R) m e ≫ toSingleTop m e = 𝟙 _ := by
      ext
      rw [HomologicalComplex.comp_f, toSingleTop, fromSingleTop,
        HomologicalComplex.mkHomToSingle_f, HomologicalComplex.mkHomFromSingle_f,
        Category.assoc, ← Category.assoc (topCochain m e), topCochain_comp_evalTop,
        Category.id_comp, Iso.hom_inv_id, HomologicalComplex.id_f]
    rw [Category.assoc, ← Category.assoc (HomologicalComplex.homologyMap _ _),
      ← HomologicalComplex.homologyMap_comp, h, HomologicalComplex.homologyMap_id,
      Category.id_comp, Iso.inv_hom_id]

end Cech

open Limits OrderDual TauCeti.CategoryTheory in
open scoped Classical in
/-- The product of the charts of the coordinates `a j` lies in the chart of their product. -/
private lemma nonempty_pi_chartFunctor_obj_hom (n : ℕ) (a : Fin (n + 1) → κ) :
    Nonempty ((∏ᶜ fun j ↦ (chartFunctor b).obj (toDual {a j})) ⟶
      (chartFunctor b).obj (∏ᶜ fun j ↦ toDual {a j})) := by
  refine ⟨homOfLE ?_⟩
  rw [chartFunctor_obj, basicOpen_coordProd, ofDual_pi_toDual_singleton]
  refine Finset.le_inf fun i hi ↦ ?_
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hi
  exact (leOfHom (Pi.π _ j)).trans (chartFunctor_obj_singleton b (a j)).le

open Limits OrderDual TauCeti.CategoryTheory TauCeti.AlgebraicGeometry.Scheme.Modules in
/-- Leray's comparison of the cohomology of `𝒪(m)` with the Čech cohomology of the Laurent
polynomials for the standard cover, for an index type in the universe of the ring. -/
private def cohomologyIsoHomologyLaurentCech [Fintype κ] [DecidableEq κ] (m : ℤ) (q : ℕ) :
    AddCommGrpCat.of (Cohomology (Proj.twistingSheaf 𝒜 m) q) ≅
      (laurentCech (R := R) (κ := κ) m).homology q :=
  have := isIso_cechComplexFunctor_map_laurentToSections b m
  (AlgebraicGeometry.Scheme.Modules.homologyCechComplexIsoCohomology
      (fun i : κ ↦ (chartFunctor b).obj (toDual {i}))
      (isAffineOpen_inf_chartFunctor_obj_singleton b) (iSup_chartFunctor_obj_singleton b)
      (Proj.twistingSheaf 𝒜 m) q).symm ≪≫
    HomologicalComplex.homologyMapIso (cechComplexCompIso (chartFunctor b)
      (fun i : κ ↦ toDual {i}) (sectionsPresheaf (R := R) (M := M) m)
      (nonempty_pi_chartFunctor_obj_hom b)) q ≪≫
    (HomologicalComplex.homologyMapIso
      (asIso ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (laurentToSections b m))) q).symm

include b in
/-- The cohomology of `𝒪(m)` in degree `q > 0` vanishes when `q < n` or `m > -n - 1`, for an index
type in the universe of the ring. -/
private theorem subsingleton_cohomology_twistingSheaf_aux [Fintype κ] {m : ℤ} {q : ℕ} (hq : 0 < q)
    (h : q + 1 < Fintype.card κ ∨ -(Fintype.card κ : ℤ) < m) :
    Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m) q) := by
  classical
  exact (AddCommGrpCat.isZero_iff_subsingleton (G := AddCommGrpCat.of (Cohomology _ q))).1
    ((isZero_homology_laurentCech (R := R) (κ := κ) m hq h).of_iso
      (cohomologyIsoHomologyLaurentCech b m q))

/-- **The top cohomology of `𝒪(m)` on projective space**, as an abelian group, for an index type
in the universe of the ring: it is the group of Laurent polynomials of degree `m` all of whose
exponents are negative. -/
private def cohomologyTopAddEquivAux [Fintype κ] [DecidableEq κ] (m : ℤ) {n : ℕ}
    (e : Fin (n + 1 + 1) ≃ κ) :
    Cohomology (Proj.twistingSheaf 𝒜 m) (n + 1) ≃+
      Finsupp.supported R R {e : κ → ℤ | ∑ i, e i = m ∧ ∀ i, e i < 0} :=
  (cohomologyIsoHomologyLaurentCech b m (n + 1) ≪≫
    homologyLaurentCechTopIso (R := R) m e).addCommGroupIsoToAddEquiv

/-! ### Main results -/

/-- The cohomology of `𝒪(m)` on projective space vanishes in degree `q > 0` when `q < n` or
`m > -n - 1`, for a basis indexed by a finite type in any universe. -/
private theorem subsingleton_cohomology_twistingSheaf_of_or {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R M) (m : ℤ) {q : ℕ} (hq : 0 < q)
    (h : q + 1 < Fintype.card κ ∨ -(Fintype.card κ : ℤ) < m) :
    Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m) q) := by
  -- reindexing by `ULift (Fin n)` puts the index type in the universe of the ring
  let e : κ ≃ ULift.{u} (Fin (Fintype.card κ)) := (Fintype.equivFin κ).trans Equiv.ulift.symm
  exact subsingleton_cohomology_twistingSheaf_aux (b.reindex e) hq (by simpa using h)

/-! ### Laurent polynomials with negative exponents and the dual of the forms -/

section Dual

variable [Fintype κ] [DecidableEq κ]

/-- The exponents `P` of the monomials of degree `j` correspond to the Laurent exponents
`-P - 1` of degree `-j - N`, all of whose entries are negative, where `N` is the number of
coordinates. -/
private def negExponentEquiv {N : ℕ} (hN : Fintype.card κ = N) (j : ℕ) :
    {P : κ → ℕ // ∑ i, P i = j} ≃ topExponents (κ := κ) (-((j + N : ℕ) : ℤ)) where
  toFun P := ⟨fun i ↦ -((P.1 i : ℤ) + 1), by
    refine ⟨?_, fun i ↦ by simp only; omega⟩
    simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      hN, nsmul_eq_mul, mul_one]
    rw [← Nat.cast_sum, P.2]
    push_cast
    ring⟩
  invFun e := ⟨fun i ↦ (-e.1 i - 1).toNat, by
    have he := e.2.1
    have hlt := e.2.2
    refine Nat.cast_injective (R := ℤ) ?_
    rw [Nat.cast_sum]
    have : ∀ i, (((-e.1 i - 1).toNat : ℕ) : ℤ) = -e.1 i - 1 := fun i ↦ by
      have := hlt i
      omega
    simp only [this, Finset.sum_sub_distrib, Finset.sum_neg_distrib, he, Finset.sum_const,
      Finset.card_univ, hN, nsmul_eq_mul, mul_one]
    push_cast
    ring⟩
  left_inv P := Subtype.ext (funext fun i ↦ by simp)
  right_inv e := Subtype.ext (funext fun i ↦ by
    have := e.2.2 i
    simp only
    omega)

/-- The Laurent polynomials of degree `-j - N` all of whose exponents are negative form the dual
of the module of forms of degree `j`: the Laurent monomial `x^{-P - 1}` corresponds to the
coordinate function of the monomial `x^P`. -/
private def topLaurentLinearEquivDual (b : Module.Basis κ R M) {N : ℕ}
    (hN : Fintype.card κ = N) (j : ℕ) :
    Finsupp.supported R R (topExponents (κ := κ) (-((j + N : ℕ) : ℤ))) ≃ₗ[R]
      Module.Dual R (𝒜 j) :=
  (Finsupp.supportedEquivFinsupp _).trans <|
    (Finsupp.domLCongr ((negExponentEquiv hN j).symm.trans
      (Sym.equivNatSumOfFintype κ j).symm)).trans
      (b.symmetricAlgebraHomogeneous j).dualBasis.repr.symm

end Dual

/-- **The top cohomology of the twisting sheaves on projective space is the dual of the forms**,
as abelian groups: `Hⁿ⁺¹(Proj (Sym M), 𝒪(-j - n - 2))` is the dual of the module of forms of
degree `j`, for `M` free of rank `n + 2`. -/
private def cohomologyTopAddEquivDual {κ : Type*} [Fintype κ] (b : Module.Basis κ R M) {n : ℕ}
    (hκ : Fintype.card κ = n + 2) (j : ℕ) :
    Cohomology (Proj.twistingSheaf 𝒜 (-((j + (n + 2) : ℕ) : ℤ))) (n + 1) ≃+
      Module.Dual R (𝒜 j) :=
  -- reindexing by `ULift (Fin (n + 2))` puts the index type in the universe of the ring
  let e : κ ≃ ULift.{u} (Fin (n + 1 + 1)) := (Fintype.equivFinOfCardEq hκ).trans Equiv.ulift.symm
  (cohomologyTopAddEquivAux (b.reindex e) _ Equiv.ulift.symm).trans
    (topLaurentLinearEquivDual (b.reindex e) (by simp) j).toAddEquiv

end TauCeti.SymmetricAlgebra

namespace Module.Basis

open TauCeti.SymmetricAlgebra (subsingleton_cohomology_twistingSheaf_of_or)
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

variable {R : Type u} {M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]

local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule R M

/-- **The intermediate cohomology of the twisting sheaves on projective space vanishes.** Let `M`
be a free `R`-module with a finite basis indexed by `κ`, so that `Proj (Sym M)` is projective space
of dimension `n = card κ - 1` over `R`. Then `Hᵠ(Proj (Sym M), 𝒪(m)) = 0` for `0 < q < n` and every
`m : ℤ`, over any commutative ring `R`. -/
theorem subsingleton_cohomology_twistingSheaf_of_lt_card {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R M) (m : ℤ) {q : ℕ} (hq : 0 < q) (hqκ : q + 1 < Fintype.card κ) :
    Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m) q) :=
  subsingleton_cohomology_twistingSheaf_of_or b m hq (.inl hqκ)

/-- **The twisting sheaves `𝒪(m)` with `m ≥ -n` on projective space have no higher cohomology.**
Let `M` be a free `R`-module with a finite basis indexed by `κ`, so that `Proj (Sym M)` is
projective space of dimension `n = card κ - 1` over `R`. If `m > -n - 1`, then
`Hᵠ(Proj (Sym M), 𝒪(m)) = 0` for every `q > 0`, over any commutative ring `R`. -/
theorem subsingleton_cohomology_twistingSheaf_of_neg_card_lt {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R M) {m : ℤ} (hm : -(Fintype.card κ : ℤ) < m) {q : ℕ} (hq : 0 < q) :
    Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m) q) :=
  subsingleton_cohomology_twistingSheaf_of_or b m hq (.inr hm)

/-- **The top cohomology of the twisting sheaves on projective space is dual to the forms.** Let
`M` be a free `R`-module with a basis indexed by a type `κ` with `n + 2` elements, so that
`Proj (Sym M)` is projective space of dimension `n + 1` over `R`. Then
`Hⁿ⁺¹(Proj (Sym M), 𝒪(-j - n - 2))` is isomorphic, as an abelian group, to the dual of the module
of forms of degree `j`, over any commutative ring `R`. The isomorphism sends the class of the
Čech cocycle given by a Laurent monomial `x^{-P - 1}` on the intersection of all the standard
charts to the coordinate function of the monomial `x^P`, up to the orientation of the cover. -/
noncomputable def cohomologyTwistingSheafTopAddEquiv {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R M) {n : ℕ} (hκ : Fintype.card κ = n + 2) (j : ℕ) :
    Cohomology (Proj.twistingSheaf 𝒜 (-((j + (n + 2) : ℕ) : ℤ))) (n + 1) ≃+
      Module.Dual R (𝒜 j) :=
  TauCeti.SymmetricAlgebra.cohomologyTopAddEquivDual b hκ j

end Module.Basis
