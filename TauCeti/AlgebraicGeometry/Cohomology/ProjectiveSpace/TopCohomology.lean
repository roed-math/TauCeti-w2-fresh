/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
import Mathlib.Data.Finsupp.Multiset
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.GlobalSections

/-!
# The top cohomology of the twisting sheaves on projective space

Let `M` be a free `R`-module with a basis `x₀, …, xₙ` indexed by a finite type `κ`, so that
`Proj (Sym M) = ℙⁿ_R` is projective space over an arbitrary commutative ring `R`, and let `n ≥ 1`.
This file computes the top cohomology `Hⁿ(ℙⁿ_R, 𝒪(m))`: writing `m = -j - n - 1`, it is the dual
of the module of forms of degree `j`, as an `R`-module. Together with
`TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology` this completes the
computation of the cohomology of the twisting sheaves on projective space.

The cohomology of `𝒪(m)` is the Čech cohomology of the presheaf of Laurent polynomials on the
finite sets of coordinates (`TauCeti.SymmetricAlgebra.cohomologyIsoHomologyLaurentCech`). In the
top degree `n`, the Čech complex of the part of the Laurent polynomials with all exponents
negative is zero in degree `n - 1`, so its cohomology is the group of cocycles, and the other
parts contribute nothing. The terms in degree `n` are indexed by the tuples `a` of `n + 1`
coordinates, and only the bijective tuples contribute. The cocycle condition for a tuple of
`n + 2` coordinates repeating one entry two places apart shows that a cocycle changes sign under
each transposition of adjacent entries, so it is `a ↦ det(a) ℓ` for a Laurent polynomial `ℓ` with
all exponents negative, where `det(a)` is the determinant of the matrix of `a` in a fixed
enumeration of the coordinates. Conversely `a ↦ det(a) ℓ` is a cocycle: the alternating sum of the
determinants of the faces of a tuple of `n + 2` coordinates is the Laplace expansion of a singular
matrix. Finally, the Laurent monomials `x^{-P - 1}` of degree `-j - n - 1` correspond to the
monomials `x^P` of degree `j`, whose dual basis spans the dual of the forms of degree `j`.

All the identifications are compatible with multiplication by an element `c` of the base ring:
on the sections of `𝒪(m)` it is multiplication by the global function `c`, which is the action
defining the `R`-module structure on cohomology, and on Laurent polynomials it is multiplication
of the coefficients.

## Main definitions

* `TauCeti.SymmetricAlgebra.cohomologyTopTwistingSheafLinearEquiv`:
  `Hⁿ(ℙⁿ_R, 𝒪(-j - n - 1)) ≃ₗ[R] (Sym^j Rⁿ⁺¹)^∨` for `n ≥ 1`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.1(c).
* [Stacks, Lemma 30.8.1 (01XS)](https://stacks.math.columbia.edu/tag/01XS)
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

namespace TauCeti.SymmetricAlgebra

universe u

variable {R : Type u} {M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]
  {κ : Type u} (b : Module.Basis κ R M)

local notation "𝒜" => homogeneousSubmodule R M

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

/-! ### Linearity over the base ring on the standard charts -/

section Chart

variable [Fintype κ] [DecidableEq κ] {m : ℤ}

/-- The global function `c` of `Proj (Sym M)` given by an element of the base ring, restricted to
an open `U`. -/
private abbrev baseFunction (c : R) (U : (Proj 𝒜).Opens) : Γ(Proj 𝒜, U) :=
  (Proj 𝒜).presheaf.map U.leTop.op
    (AlgebraicGeometry.Scheme.Modules.baseRingToGlobalSections R (Proj 𝒜) c)

private lemma val_baseFunction_apply (c : R) {U : (Proj 𝒜).Opens} (x : U) :
    ((baseFunction c U).1 x).val =
      Localization.mk (algebraMap R (_root_.SymmetricAlgebra R M) c) 1 :=
  val_baseRingToGlobalSections_apply c ⟨x.1, trivial⟩

private lemma chartSectionHom_smul (S : Finset κ) (e : κ → ℤ) (c r : R) :
    chartSectionHom b m S e (c * r) =
      baseFunction (M := M) c (Proj.basicOpen 𝒜 (coordProd b S)) • chartSectionHom b m S e r := by
  by_cases he : e ∈ chartExponents m S
  · rw [chartSectionHom_apply b he (fun i _ ↦ le_exponentBound e i),
      chartSectionHom_apply b he (fun i _ ↦ le_exponentBound e i)]
    refine Proj.twistingSheaf.ext fun x ↦ Eq.trans ?_ (Proj.twistingSheaf.smul_apply _ _ x).symm
    refine (Proj.twistingSheaf.const_apply _ _ _ _ _ _ x).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (val_baseFunction_apply (M := M) c x).symm
        (Proj.twistingSheaf.const_apply _ _ _ _ _ _ x).symm))
    rw [Localization.mk_mul, mul_smul, Algebra.smul_def c]
    congr 1
    exact Subtype.ext (one_mul _).symm
  · simp [chartSectionHom, he]

private lemma chartSectionsHom_smul (S : Finset κ) (c : R)
    (f : Finsupp.supported R R (chartExponents m S)) :
    chartSectionsHom b m S (c • f) =
      baseFunction (M := M) c (Proj.basicOpen 𝒜 (coordProd b S)) • chartSectionsHom b m S f := by
  rw [chartSectionsHom_eq_sum, chartSectionsHom_eq_sum]
  change ((c • f.1).sum fun e r ↦ chartSectionHom b m S e r) =
    baseFunction (M := M) c (Proj.basicOpen 𝒜 (coordProd b S)) •
      (f.1.sum fun e r ↦ chartSectionHom b m S e r)
  rw [Finsupp.sum_smul_index' (fun e ↦ map_zero _), Finsupp.smul_sum]
  exact Finset.sum_congr rfl fun e _ ↦ chartSectionHom_smul b S e c _

end Chart

/-! ### The Čech complex in the top degree -/

section Cech

open Limits Opposite OrderDual TauCeti.CategoryTheory

variable [Fintype κ] [DecidableEq κ] (m : ℤ)

/-- Multiplication by an element of the base ring on the Laurent polynomials. -/
private def laurentSmul (c : R) :
    laurentPresheaf (R := R) (κ := κ) m ⟶ laurentPresheaf (R := R) (κ := κ) m where
  app _ := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom _ c)
  naturality X Y g := by
    have h : (c • LinearMap.id).comp (Submodule.inclusion (Finsupp.supported_mono (M := R)
        (R := R) (chartExponents_mono (m := m) (leOfHom g.unop)))) =
        (Submodule.inclusion (Finsupp.supported_mono (chartExponents_mono (leOfHom g.unop)))).comp
          (c • LinearMap.id) := by
      rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id]
    exact AddCommGrpCat.hom_ext (congrArg LinearMap.toAddMonoidHom h)

/-- Multiplication by an element of the base ring on the sections of `𝒪(m)`. -/
private abbrev sectionsSmul (c : R) :
    sectionsPresheaf (R := R) (M := M) m ⟶ sectionsPresheaf (R := R) (M := M) m :=
  ((SheafOfModules.toSheaf (Proj 𝒜).ringCatSheaf).map ((Proj.twistingSheaf 𝒜 m).globalSectionsSmul
    (AlgebraicGeometry.Scheme.Modules.baseRingToGlobalSections R (Proj 𝒜) c))).hom

omit [Fintype κ] [DecidableEq κ] in
private lemma sectionsSmul_app_apply (c : R) (U : (Proj 𝒜).Opens)
    (s : Γ(Proj.twistingSheaf 𝒜 m, U)) :
    (sectionsSmul (R := R) (M := M) m c).app (Opposite.op U) s = baseFunction (M := M) c U • s := by
  refine Eq.trans ?_ ((Proj.twistingSheaf 𝒜 m).smul_apply (baseFunction (M := M) c U) s)
  rw [← AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_app]
  rfl

/-- The identification of Laurent polynomials with sections of `𝒪(m)` is linear over the base
ring. -/
private lemma laurentSmul_comp_laurentToSections (c : R) :
    laurentSmul (R := R) (κ := κ) m c ≫ laurentToSections b m =
      laurentToSections b m ≫ Functor.whiskerLeft (chartFunctor b).op (sectionsSmul m c) := by
  ext S f
  exact (chartSectionsHom_smul b (ofDual S.unop) c f).trans
    (sectionsSmul_app_apply m c _ _).symm

/-! #### The top degree

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

/-- Multiplication by an element of the base ring on the Laurent polynomials with all exponents
negative. -/
private abbrev topSmul (c : R) :
    AddCommGrpCat.of (Finsupp.supported R R (topExponents (κ := κ) m)) ⟶
      AddCommGrpCat.of (Finsupp.supported R R (topExponents (κ := κ) m)) :=
  AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom _ c)

private lemma laurentSmul_app_comp_topPartHom (c : R) (X : ((Finset κ)ᵒᵈ)ᵒᵖ) :
    (laurentSmul (R := R) m c).app X ≫ topPartHom (R := R) m (ofDual X.unop) =
      topPartHom (R := R) m (ofDual X.unop) ≫ topSmul m c :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ (topPart m _).map_smul c x)

private lemma cechComplexFunctor_map_laurentSmul_comp_evalTop (c : R) :
    ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (laurentSmul (R := R) m c)).f (n + 1) ≫ evalTop m e = evalTop m e ≫ topSmul m c := by
  unfold evalTop
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (cechComplexFunctor_map_f_π _ _ _ _ ⇑e)).trans ?_)
  exact (Category.assoc _ _ _).trans ((congrArg _ (laurentSmul_app_comp_topPartHom m c _)).trans
    (Category.assoc _ _ _).symm)

private lemma cechComplexFunctor_map_laurentSmul_comp_toSingleTop (c : R) :
    (cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (laurentSmul (R := R) m c) ≫ toSingleTop m e =
      toSingleTop m e ≫ (HomologicalComplex.single AddCommGrpCat.{u} (ComplexShape.up ℕ)
        (n + 1)).map (topSmul m c) := by
  ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, toSingleTop,
    HomologicalComplex.mkHomToSingle_f, HomologicalComplex.single_map_f_self,
    Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
    cechComplexFunctor_map_laurentSmul_comp_evalTop, Category.assoc]

private lemma homologyMap_laurentSmul_comp_homologyLaurentCechTopIso_hom (c : R) :
    HomologicalComplex.homologyMap ((cechComplexFunctor fun i : κ ↦
        (toDual {i} : (Finset κ)ᵒᵈ)).map (laurentSmul (R := R) m c)) (n + 1) ≫
        (homologyLaurentCechTopIso m e).hom =
      (homologyLaurentCechTopIso m e).hom ≫ topSmul m c := by
  simp only [homologyLaurentCechTopIso]
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    cechComplexFunctor_map_laurentSmul_comp_toSingleTop, HomologicalComplex.homologyMap_comp,
    Category.assoc, HomologicalComplex.singleObjHomologySelfIso_hom_naturality, Category.assoc]

end Cech

open Limits OrderDual TauCeti.CategoryTheory in
/-- Leray's comparison for `𝒪(m)` carries multiplication by an element of the base ring to
multiplication of the Laurent polynomials. -/
private lemma cohomologyMap_comp_cohomologyIsoHomologyLaurentCech_hom [Fintype κ] [DecidableEq κ]
    (m : ℤ) (q : ℕ) (c : R) :
    (cohomologyFunctor (Proj 𝒜) q).map ((Proj.twistingSheaf 𝒜 m).globalSectionsSmul
        (AlgebraicGeometry.Scheme.Modules.baseRingToGlobalSections R (Proj 𝒜) c)) ≫
        (cohomologyIsoHomologyLaurentCech b m q).hom =
      (cohomologyIsoHomologyLaurentCech b m q).hom ≫ HomologicalComplex.homologyMap
        ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
          (laurentSmul (R := R) m c)) q := by
  have := isIso_cechComplexFunctor_map_laurentToSections b m
  have h1 := AlgebraicGeometry.Scheme.Modules.homologyMap_comp_homologyCechComplexIsoCohomology_hom
    (fun i : κ ↦ (chartFunctor b).obj (toDual {i}))
    (isAffineOpen_inf_chartFunctor_obj_singleton b) (iSup_chartFunctor_obj_singleton b)
    ((Proj.twistingSheaf 𝒜 m).globalSectionsSmul
      (AlgebraicGeometry.Scheme.Modules.baseRingToGlobalSections R (Proj 𝒜) c)) q
  have hA : (cohomologyFunctor (Proj 𝒜) q).map ((Proj.twistingSheaf 𝒜 m).globalSectionsSmul
        (AlgebraicGeometry.Scheme.Modules.baseRingToGlobalSections R (Proj 𝒜) c)) ≫
        (AlgebraicGeometry.Scheme.Modules.homologyCechComplexIsoCohomology
          (fun i : κ ↦ (chartFunctor b).obj (toDual {i}))
          (isAffineOpen_inf_chartFunctor_obj_singleton b) (iSup_chartFunctor_obj_singleton b)
          (Proj.twistingSheaf 𝒜 m) q).inv =
      (AlgebraicGeometry.Scheme.Modules.homologyCechComplexIsoCohomology
          (fun i : κ ↦ (chartFunctor b).obj (toDual {i}))
          (isAffineOpen_inf_chartFunctor_obj_singleton b) (iSup_chartFunctor_obj_singleton b)
          (Proj.twistingSheaf 𝒜 m) q).inv ≫
        HomologicalComplex.homologyMap ((cechComplexFunctor fun i : κ ↦
          (chartFunctor b).obj (toDual {i})).map (sectionsSmul (M := M) m c)) q :=
    (Iso.comp_inv_eq _).2 (((Category.assoc _ _ _).trans (congrArg _ h1)).trans
      (Iso.inv_hom_id_assoc _ _)).symm
  have hS := (((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map_comp _ _).symm.trans
      ((congrArg (cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (laurentSmul_comp_laurentToSections b m c)).trans
        ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map_comp _ _)))
  have hC : (cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (Functor.whiskerLeft (chartFunctor b).op (sectionsSmul m c)) ≫
        inv ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
          (laurentToSections b m)) =
      inv ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
          (laurentToSections b m)) ≫
        (cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
          (laurentSmul (R := R) m c) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← hS, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hB := (HomologicalComplex.homologyMap_comp _ _ q).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · q)
      (cechComplexFunctor_map_comp_cechComplexCompIso_hom (chartFunctor b)
        (fun i : κ ↦ toDual {i}) (sectionsPresheaf (R := R) (M := M) m)
        (nonempty_pi_chartFunctor_obj_hom b) (sectionsSmul (M := M) m c))).trans
      (HomologicalComplex.homologyMap_comp _ _ q))
  have hC' := (HomologicalComplex.homologyMap_comp _ _ q).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · q) hC).trans
      (HomologicalComplex.homologyMap_comp _ _ q))
  simp only [cohomologyIsoHomologyLaurentCech, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyMapIso_inv, asIso_inv,
    Category.assoc]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hA).trans ((Category.assoc _ _ _).trans
    (congrArg _ ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hB).trans
      ((Category.assoc _ _ _).trans (congrArg _ hC')))))))

/-- **The top cohomology of `𝒪(m)` on projective space**, for an index type in the universe of
the ring: it is the module of Laurent polynomials of degree `m` all of whose exponents are
negative. -/
private def cohomologyTopLinearEquivAux [Fintype κ] [DecidableEq κ] (m : ℤ) {n : ℕ}
    (e : Fin (n + 1 + 1) ≃ κ) :
    Cohomology (Proj.twistingSheaf 𝒜 m) (n + 1) ≃ₗ[R]
      Finsupp.supported R R (topExponents (κ := κ) m) where
  toAddEquiv := (cohomologyIsoHomologyLaurentCech b m (n + 1) ≪≫
    homologyLaurentCechTopIso (R := R) m e).addCommGroupIsoToAddEquiv
  map_smul' c y := by
    have key := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      (cohomologyMap_comp_cohomologyIsoHomologyLaurentCech_hom b m (n + 1) c)).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (homologyMap_laurentSmul_comp_homologyLaurentCechTopIso_hom m e c)).trans
        (Category.assoc _ _ _).symm)))
    have h := ConcreteCategory.congr_hom key y
    change (cohomologyIsoHomologyLaurentCech b m (n + 1) ≪≫
      homologyLaurentCechTopIso (R := R) m e).hom (c • y) =
        c • (cohomologyIsoHomologyLaurentCech b m (n + 1) ≪≫
          homologyLaurentCechTopIso (R := R) m e).hom y
    rw [Scheme.Modules.base_smul_cohomology, Scheme.Modules.cohomology_smul]
    exact h

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

/-- **The top cohomology of the twisting sheaves on projective space is dual to the forms.** Let
`M` be a free `R`-module with a basis indexed by a type `κ` with `n + 2` elements, so that
`Proj (Sym M)` is projective space of dimension `n + 1` over `R`. Then
`Hⁿ⁺¹(Proj (Sym M), 𝒪(-j - n - 2))` is isomorphic, as an `R`-module, to the dual of the module
of forms of degree `j`, over any commutative ring `R`. The isomorphism sends the class of the
Čech cocycle given by a Laurent monomial `x^{-P - 1}` on the intersection of all the standard
charts to the coordinate function of the monomial `x^P`, up to the orientation of the cover. -/
def cohomologyTopTwistingSheafLinearEquiv {κ : Type*} [Fintype κ] (b : Module.Basis κ R M)
    {n : ℕ} (hκ : Fintype.card κ = n + 2) (j : ℕ) :
    Cohomology (Proj.twistingSheaf 𝒜 (-((j + (n + 2) : ℕ) : ℤ))) (n + 1) ≃ₗ[R]
      Module.Dual R (𝒜 j) :=
  -- reindexing by `ULift (Fin (n + 2))` puts the index type in the universe of the ring
  let e : κ ≃ ULift.{u} (Fin (n + 1 + 1)) := (Fintype.equivFinOfCardEq hκ).trans Equiv.ulift.symm
  (cohomologyTopLinearEquivAux (b.reindex e) _ Equiv.ulift.symm).trans
    (topLaurentLinearEquivDual (b.reindex e) (by simp) j)

end TauCeti.SymmetricAlgebra
