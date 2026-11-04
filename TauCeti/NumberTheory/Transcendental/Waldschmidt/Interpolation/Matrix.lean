/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.Data
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.MvPolynomial.PDeriv
import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# The interpolation matrix of Waldschmidt's linear forms estimate

Waldschmidt's interpolation matrix has a row for each auxiliary function
`F(z) exp(t (z₀ + λ₁ z₁ + ⋯ + λ_{m-1} z_{m-1}))`, with `F` a polynomial of total degree at most
`T₀` and `|t| ≤ T₁`, and a column for each differential operator `P(∂/∂z₀)` and grid point `s · y`;
its entries are the coefficient-field factors `TauCeti.waldschmidtOperatorEntry`. With the
monomials `z^τ` as the polynomials `F` there are `L_m = (T₀ + m choose m) (2 T₁ + 1)` rows, the
first factor being the dimension `TauCeti.finrank_restrictTotalDegree` of the polynomials of total
degree at most `T₀` in `m` variables.

In the rank argument of the proof, the grid points are confined to a subspace: one takes the
columns with `s` in a subspace `V ⊆ Kᵐ` of dimension `d` containing the coefficient vector
`(β₁, …, β_{m-1}, -1)` of the normalized linear form. The grid points `s · y`, `s ∈ V`, together
with the direction `e₀` of the derivatives then span a subspace `W` of dimension at most `d`.
The restriction to `W` of a polynomial of total degree at most `T₀` is a polynomial of total
degree at most `T₀` in `d` coordinates, and `∂/∂z₀` is a derivative along `W`, so each row of the
matrix on these columns is determined by such a restricted polynomial and by `t`. Hence these
columns span a space of dimension at most

`L_d = (T₀ + d choose d) (2 T₁ + 1)`

when `|t| ≤ T₁`; the dimension of `W` is exactly `d`. This file proves this upper bound on the
rank, for arbitrary families of rows and columns. That, for the monomial rows, the bound `L_d` is
attained exactly when the conclusion of a zero estimate holds is proved in
`TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.Rank`.

## Main definitions

* `TauCeti.waldschmidtInterpolationMatrix α b F t P s`: the matrix of entries
  `waldschmidtOperatorEntry α b (t r) (s c) (F r) (P c)`.

## Main results

* `TauCeti.rank_waldschmidtInterpolationMatrix_le_of_mem`: if the grid points and `e₀` lie in a
  subspace `W`, the rank is at most `(T₀ + dim W choose dim W) · #{t}`.
* `TauCeti.finrank_map_waldschmidtPointMap_sup`: if `V` contains the coefficient vector, the grid
  points `s · y`, `s ∈ V`, and `e₀` span a subspace of dimension `dim V`.
* `TauCeti.rank_waldschmidtInterpolationMatrix_le`: if the column indices `s` lie in a subspace
  `V` containing the coefficient vector, the rank is at most `(T₀ + dim V choose dim V) · #{t}`,
  that is, at most `L_d` with `d = dim V` when `|t| ≤ T₁`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §§9.2.1, 9.2.3.
-/

public section

open Finset Function MvPolynomial Module

namespace TauCeti

variable {n : ℕ} {K : Type*} [Field K]

/-- Waldschmidt's interpolation matrix: the row `r` is the auxiliary function with polynomial
`F r` and exponent `t r`, the column `c` is the differential operator `(P c)(∂/∂z₀)` at the grid
point `s c · y`, and the entry is the coefficient-field factor
`TauCeti.waldschmidtOperatorEntry α b (t r) (s c) (F r) (P c)`. -/
noncomputable def waldschmidtInterpolationMatrix {ι κ : Type*} (α b : Fin (n + 1) → K)
    (F : ι → MvPolynomial (Fin (n + 1)) K) (t : ι → ℤ) (P : κ → Polynomial K)
    (s : κ → Fin (n + 1) → ℤ) : Matrix ι κ K :=
  Matrix.of fun r c ↦ waldschmidtOperatorEntry α b (t r) (s c) (F r) (P c)

@[simp]
theorem waldschmidtInterpolationMatrix_apply {ι κ : Type*} (α b : Fin (n + 1) → K)
    (F : ι → MvPolynomial (Fin (n + 1)) K) (t : ι → ℤ) (P : κ → Polynomial K)
    (s : κ → Fin (n + 1) → ℤ) (r : ι) (c : κ) :
    waldschmidtInterpolationMatrix α b F t P s r c =
      waldschmidtOperatorEntry α b (t r) (s c) (F r) (P c) :=
  (rfl)

/-- On columns whose grid points lie in a subspace `W` containing `e₀`, the row of the interpolation
matrix with polynomial `F` and exponent `t'` is the image under a linear map `Φ t'` of the
restriction of `F` to `W`, a polynomial of total degree at most `T₀` in `dim W` coordinates. -/
private theorem exists_row_waldschmidtInterpolationMatrix_mem_map {ι κ : Type*}
    (α b : Fin (n + 1) → K) {F : ι → MvPolynomial (Fin (n + 1)) K} (t : ι → ℤ)
    (P : κ → Polynomial K) {s : κ → Fin (n + 1) → ℤ} {T₀ : ℕ}
    (hF : ∀ r, F r ∈ restrictTotalDegree (Fin (n + 1)) K T₀)
    {W : Submodule K (Fin (n + 1) → K)} (hW : Pi.single 0 1 ∈ W)
    (hs : ∀ c, waldschmidtPoint b (s c) ∈ W) :
    ∃ Φ : ℤ → MvPolynomial (Fin (finrank K W)) K →ₗ[K] κ → K, ∀ r,
      (waldschmidtInterpolationMatrix α b F t P s).row r ∈
        (restrictTotalDegree (Fin (finrank K W)) K T₀).map (Φ (t r)) := by
  classical
  set d := finrank K W
  -- Coordinates on `W`: `ψ` is a basis of `W`, and substituting `f` restricts polynomials to `W`.
  let ψ := Module.finBasis K W
  let f : Fin (n + 1) → MvPolynomial (Fin d) K := fun i ↦ ∑ j, C ((ψ j : Fin (n + 1) → K) i) * X j
  have hf (i : Fin (n + 1)) : (f i).totalDegree ≤ 1 :=
    totalDegree_finsetSum_le fun j _ ↦ (totalDegree_mul _ _).trans (by simp)
  have hrepr (w : W) (i : Fin (n + 1)) :
      ∑ j, ψ.repr w j * (ψ j : Fin (n + 1) → K) i = (w : Fin (n + 1) → K) i := by
    have h := congrArg (fun v : W ↦ (v : Fin (n + 1) → K) i) (ψ.sum_repr w)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] using h
  -- The derivative `∂/∂z₀` becomes the derivative `D` of `W` in the direction `e₀`.
  let a := ψ.repr ⟨Pi.single 0 1, hW⟩
  let D : Derivation K (MvPolynomial (Fin d) K) (MvPolynomial (Fin d) K) := ∑ j, a j • pderiv j
  have hD (G : MvPolynomial (Fin (n + 1)) K) : D (aeval f G) = aeval f (pderiv 0 G) := by
    have hfj (i : Fin (n + 1)) (j : Fin d) : pderiv j (f i) = C ((ψ j : Fin (n + 1) → K) i) := by
      simp [f, pderiv_X, Pi.single_apply]
    calc D (aeval f G) = ∑ i, aeval f (pderiv i G) * C (∑ j, a j * (ψ j : Fin (n + 1) → K) i) := by
          simp only [_root_.sum_apply, FunLike.coe_smul, Pi.smul_apply, pderiv_aeval, hfj,
            smul_sum, map_sum, C_mul, mul_sum, D]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          rw [smul_eq_C_mul]
          ring
      _ = aeval f (pderiv 0 G) := by
          simp_rw [a, hrepr]
          simp [Pi.single_apply]
  have hDk (k : ℕ) (G : MvPolynomial (Fin (n + 1)) K) :
      (⇑D)^[k] (aeval f G) = aeval f ((pderiv 0)^[k] G) := by
    induction k generalizing G with
    | zero => rfl
    | succ k ih => rw [iterate_succ_apply, iterate_succ_apply, hD, ih]
  -- Evaluation at the grid points factors through the restriction to `W`.
  let u : κ → Fin d → K := fun c ↦ ψ.repr ⟨_, hs c⟩
  have heval (c : κ) (G : MvPolynomial (Fin (n + 1)) K) :
      eval (u c) (aeval f G) = eval (waldschmidtPoint b (s c)) G := by
    have hpt : (fun i ↦ eval (u c) (f i)) = waldschmidtPoint b (s c) := by
      funext i
      simpa [f, u, mul_comm] using hrepr ⟨_, hs c⟩ i
    rw [← hpt]
    simpa only [aeval_eq_eval] using comp_aeval_apply (f := f) (aeval (u c)) G
  -- The rows with exponent `t'`, as a linear map of the restricted polynomial.
  refine ⟨fun t' ↦ LinearMap.pi fun c ↦ (∏ j, α j ^ (t' * s c j)) •
    ∑ k ∈ range ((P c).natDegree + 1), (Polynomial.hasseDeriv k (P c)).eval (t' : K) •
      ((aeval (u c)).toLinearMap ∘ₗ D.toLinearMap ^ k), fun r ↦ ?_⟩
  refine ⟨aeval f (F r), aeval_mem_restrictTotalDegree hf (hF r), ?_⟩
  ext c
  simp [waldschmidtOperatorEntry_eq_sum_hasseDeriv, pow_apply_eq_iterate, hDk, heval, mul_comm]

/-- **Rank of the interpolation matrix on a subspace.** Let the polynomials `F r` have total degree
at most `T₀` and the exponents `t r` lie in a finite set `T`. If the grid points `s c · y` of the
columns lie in a subspace `W ⊆ Kᵐ` containing the direction `e₀` of the derivatives, then the
interpolation matrix has rank at most `(T₀ + dim W choose dim W) · #T`: each row is determined by
`t r` and by the restriction of `F r` to `W`, a polynomial of total degree at most `T₀` in
`dim W` coordinates. -/
theorem rank_waldschmidtInterpolationMatrix_le_of_mem {ι κ : Type*} [Finite ι] [Fintype κ]
    (α b : Fin (n + 1) → K) {F : ι → MvPolynomial (Fin (n + 1)) K} {t : ι → ℤ}
    (P : κ → Polynomial K) {s : κ → Fin (n + 1) → ℤ} {T₀ : ℕ} {T : Finset ℤ}
    (hF : ∀ r, F r ∈ restrictTotalDegree (Fin (n + 1)) K T₀) (ht : ∀ r, t r ∈ T)
    {W : Submodule K (Fin (n + 1) → K)} (hW : Pi.single 0 1 ∈ W)
    (hs : ∀ c, waldschmidtPoint b (s c) ∈ W) :
    (waldschmidtInterpolationMatrix α b F t P s).rank ≤
      (T₀ + finrank K W).choose (finrank K W) * #T := by
  classical
  obtain ⟨Φ, hΦ⟩ := exists_row_waldschmidtInterpolationMatrix_mem_map α b t P hF hW hs
  set U : ℤ → Submodule K (κ → K) := fun t' ↦ (restrictTotalDegree _ K T₀).map (Φ t')
  have hle : Submodule.span K (Set.range (waldschmidtInterpolationMatrix α b F t P s).row) ≤
      T.sup U := by
    rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    exact Finset.le_sup (f := U) (ht r) (hΦ r)
  -- Each `U t'` has dimension at most `(T₀ + dim W choose dim W)`, so their supremum over
  -- `t' ∈ T` has dimension at most `#T` times this.
  have hsup (T' : Finset ℤ) :
      finrank K ↥(T'.sup U) ≤ (T₀ + finrank K W).choose (finrank K W) * #T' := by
    induction T' using Finset.induction_on with
    | empty => simp
    | insert x T' hx ih =>
      rw [Finset.sup_insert, Finset.card_insert_of_notMem hx]
      have hx' : finrank K (U x) ≤ (T₀ + finrank K W).choose (finrank K W) := by
        simpa using (Submodule.finrank_map_le (Φ x) _).trans
          (finrank_restrictTotalDegree (Fin (finrank K W)) K T₀).le
      refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
      rw [mul_add_one]
      lia
  rw [Matrix.rank_eq_finrank_span_row]
  exact (Submodule.finrank_mono hle).trans (hsup T)

/-- The grid points `s · y` of the indices `s` in a subspace `V ⊆ Kᵐ` containing the coefficient
vector `c = (β₁, …, β_{m-1}, -1)`, together with the direction `e₀` of the derivatives, span a
subspace `W = Y(V) + K e₀` of the same dimension as `V`, where `Y` is the grid point map. If
`β₀ ≠ 0`, then `Y` is injective and `e₀ ∈ Y(V)`; if `β₀ = 0`, then `Y` has kernel `K c` and
`e₀ ∉ Y(V)`. -/
theorem finrank_map_waldschmidtPointMap_sup (b : Fin (n + 1) → K)
    {V : Submodule K (Fin (n + 1) → K)} (hV : Fin.snoc (fun k : Fin n ↦ b k.succ) (-1) ∈ V) :
    finrank K ↥(V.map (waldschmidtPointMap b) ⊔ K ∙ Pi.single 0 1) = finrank K V := by
  set Y := waldschmidtPointMap b
  set e₀ : Fin (n + 1) → K := Pi.single 0 1
  set c : Fin (n + 1) → K := Fin.snoc (fun k : Fin n ↦ b k.succ) (-1)
  -- A vector in the kernel of `Y` is a multiple of the coefficient vector.
  have hker (v : Fin (n + 1) → K) (hv : Y v = 0) : v = -v (Fin.last n) • c := by
    ext i
    induction i using Fin.lastCases with
    | last => simp [c]
    | cast k =>
      have := congrFun hv k.succ
      simp only [Y, waldschmidtPointMap_apply_succ, Pi.zero_apply] at this
      simp [c, Fin.snoc_castSucc]
      linear_combination this
  have hc := waldschmidtPointMap_snoc b
  by_cases hb : b 0 = 0
  · -- `Y(V)` meets the line `K e₀` only in `0`, and loses at most the line `K c` of `V`.
    have hinf : V.map Y ⊓ K ∙ e₀ = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun x ⟨⟨v, _, hvx⟩, hx⟩ ↦ ?_
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
      have := congrFun hvx 0
      simp [Y, e₀, hb] at this
      simp [this]
    have he₀ : e₀ ≠ 0 := by simp [e₀]
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (V.map Y) (K ∙ e₀)
    rw [hinf, finrank_bot, finrank_span_singleton he₀] at hsup
    have hrank := LinearMap.finrank_range_add_finrank_ker (Y ∘ₗ V.subtype)
    rw [LinearMap.range_comp, Submodule.range_subtype] at hrank
    have hker₁ : finrank K (LinearMap.ker (Y ∘ₗ V.subtype)) ≤ 1 := by
      rw [← Submodule.finrank_map_subtype_eq]
      have hc0 : c ≠ 0 := fun h ↦ by simpa [c] using congrFun h (Fin.last n)
      refine (Submodule.finrank_mono (s := _) (t := K ∙ c) ?_).trans
        (finrank_span_singleton hc0).le
      rintro _ ⟨v, hv, rfl⟩
      rw [Submodule.subtype_apply, hker v (LinearMap.mem_ker.1 hv)]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c)
    have hker₂ : 1 ≤ finrank K (LinearMap.ker (Y ∘ₗ V.subtype)) := by
      rw [hb, neg_zero, Pi.single_zero] at hc
      refine Submodule.one_le_finrank_iff.2 ((Submodule.ne_bot_iff _).2
        ⟨⟨c, hV⟩, by simpa using hc, fun h ↦ ?_⟩)
      have := congrFun (congrArg Subtype.val h) (Fin.last n)
      simp [c] at this
    lia
  · -- `Y` is injective and `e₀ ∈ Y(V)`, so `Y(V) ⊔ K e₀ = Y(V) ≃ V`.
    have he₀ : e₀ ∈ V.map Y := by
      refine ⟨(-b 0)⁻¹ • c, V.smul_mem _ hV, ?_⟩
      rw [map_smul, hc, ← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ (neg_ne_zero.2 hb)]
    have hinj : Injective Y := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro v hv
      have h0 := congrFun (LinearMap.mem_ker.1 hv) 0
      simp only [Y, waldschmidtPointMap_apply_zero, Pi.zero_apply, mul_eq_zero, hb,
        or_false] at h0
      rw [hker v hv, h0, neg_zero, zero_smul]
    rw [sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 he₀)]
    exact (Submodule.equivMapOfInjective Y hinj V).finrank_eq.symm

/-- **Rank of the interpolation matrix on a residual subspace.** Let the polynomials `F r` have
total degree at most `T₀` and the exponents `t r` lie in a finite set `T`. If the column indices
`s c` lie in a subspace `V ⊆ Kᵐ` containing the coefficient vector `(β₁, …, β_{m-1}, -1)` of the
normalized linear form, then the interpolation matrix has rank at most
`(T₀ + d choose d) · #T` with `d = dim V`; for `T = [-T₁, T₁]` this is
`L_d = (T₀ + d choose d) (2 T₁ + 1)`. -/
theorem rank_waldschmidtInterpolationMatrix_le {ι κ : Type*} [Finite ι] [Fintype κ]
    (α b : Fin (n + 1) → K) {F : ι → MvPolynomial (Fin (n + 1)) K} {t : ι → ℤ}
    (P : κ → Polynomial K) {s : κ → Fin (n + 1) → ℤ} {T₀ : ℕ} {T : Finset ℤ}
    (hF : ∀ r, F r ∈ restrictTotalDegree (Fin (n + 1)) K T₀) (ht : ∀ r, t r ∈ T)
    {V : Submodule K (Fin (n + 1) → K)} (hV : Fin.snoc (fun k : Fin n ↦ b k.succ) (-1) ∈ V)
    (hs : ∀ c, (fun i ↦ (s c i : K)) ∈ V) :
    (waldschmidtInterpolationMatrix α b F t P s).rank ≤
      (T₀ + finrank K V).choose (finrank K V) * #T := by
  -- The grid points and `e₀` span `W = Y(V) + K e₀`, of dimension `dim V`.
  rw [← finrank_map_waldschmidtPointMap_sup b hV]
  refine rank_waldschmidtInterpolationMatrix_le_of_mem α b P hF ht
    (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)) fun c ↦ ?_
  rw [← waldschmidtPointMap_intCast]
  exact Submodule.mem_sup_left (Submodule.mem_map_of_mem (hs c))

end TauCeti
