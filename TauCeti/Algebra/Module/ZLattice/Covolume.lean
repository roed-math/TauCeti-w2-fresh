/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Algebra.Module.ZLattice.Dual
public import TauCeti.LinearAlgebra.Matrix.BilinearForm

/-!
# The covolume of a lattice in an inner product space

In a finite-dimensional real inner product space, equipped with the volume measure of its inner
product, the square of the covolume of a `ℤ`-lattice is the determinant of the Gram matrix of any
of its `ℤ`-bases. This is the metric form of `ZLattice.covolume_eq_det`, which computes the
covolume in the coordinate space `ι → ℝ` as the absolute determinant of a basis.

The Gram determinant is computed from inner products alone, so this identity expresses the
covolume, a measure-theoretic invariant of the lattice, through the metric data of any of its
bases. In particular the covolume does not depend on a choice of coordinates, and two lattices
with the same Gram matrix in some bases have the same covolume.

The covolume of the dual lattice `L^∨ = ZLattice.dual L` is the inverse of the covolume of `L`
(`ZLattice.covolume_dual`): in an `ℤ`-basis of `L` and the dual basis of `L^∨`, the Gram matrices
are inverse to each other.

Pulling a lattice back along a linear automorphism `A` divides its covolume by `|det A|`, for any
Haar measure (`ZLattice.covolume_comap_continuousLinearEquiv`). Since the `ℤ`-span of an
orthonormal basis has covolume one, every full lattice `L` is the image of that standard lattice
`ℤⁿ` under an automorphism `A` with `|det A| = covolume L`, and the adjoint of `A⁻¹` carries `ℤⁿ`
onto `L^∨` (`ZLattice.exists_comap_eq_span_orthonormalBasis`). This is the change of coordinates
that transports Fourier analysis on `ℤⁿ`, such as Poisson summation, to an arbitrary full lattice
and its dual.

## Main results

* `ZLattice.covolume_sq_eq_det_gram`: `covolume L ^ 2` is the determinant of the Gram matrix of
  any `ℤ`-basis of `L`.
* `ZLattice.covolume_dual`: `covolume L^∨ = (covolume L)⁻¹`.
* `ZLattice.covolume_comap_continuousLinearEquiv`: `covolume (A⁻¹ L) = |det A|⁻¹ * covolume L`.
* `ZLattice.covolume_span_orthonormalBasis`: the `ℤ`-span of an orthonormal basis has covolume
  one.
* `ZLattice.exists_comap_eq_span_orthonormalBasis`: a full lattice and its dual are the images of
  `ℤⁿ` under an automorphism `A` with `|det A| = covolume L` and under the adjoint of `A⁻¹`.
-/

public section

open Module MeasureTheory Submodule
open LinearMap (BilinForm)

namespace TauCeti

section LinearEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Pulling a full lattice back along a linear automorphism `A` divides its covolume by `|det A|`,
for any Haar measure: in terms of images, `covolume (A L) = |det A| * covolume L`. -/
theorem _root_.ZLattice.covolume_comap_continuousLinearEquiv (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (μ : Measure E) [μ.IsAddHaarMeasure] (A : E ≃L[ℝ] E) :
    ZLattice.covolume (ZLattice.comap ℝ L A.toLinearMap) μ =
      |A.toLinearEquiv.toLinearMap.det|⁻¹ * ZLattice.covolume L μ := by
  classical
  let b := Free.chooseBasis ℤ L
  let b₀ := b.ofZLatticeBasis ℝ L
  -- The pulled-back lattice has the `ℤ`-basis `A⁻¹ ∘ b`.
  have hb : ((↑) ∘ b.ofZLatticeComap ℝ L A.toLinearEquiv : _ → E) =
      A.symm.toLinearEquiv.toLinearMap ∘ ((↑) ∘ b) := by
    ext i
    simp
  rw [ZLattice.covolume_eq_det_mul_measureReal _ μ (b.ofZLatticeComap ℝ L A.toLinearEquiv) b₀,
    ZLattice.covolume_eq_det_mul_measureReal L μ b b₀, hb, Basis.det_comp, abs_mul, mul_assoc,
    ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.det_coe_symm, abs_inv]

end LinearEquiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The `ℤ`-span of an orthonormal basis has covolume one. -/
@[simp]
theorem _root_.ZLattice.covolume_span_orthonormalBasis {ι : Type*} [Fintype ι]
    (o : OrthonormalBasis ι ℝ E) : ZLattice.covolume (span ℤ (Set.range o)) = 1 := by
  rw [← o.coe_toBasis, ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (ZSpan.isAddFundamentalDomain o.toBasis volume),
    measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    OrthonormalBasis.coe_toBasis, measureReal_def, o.volume_parallelepiped, ENNReal.toReal_one]

/-- The square of the covolume of a lattice in a finite-dimensional real inner product space is
the determinant of the Gram matrix of any `ℤ`-basis of the lattice. -/
theorem _root_.ZLattice.covolume_sq_eq_det_gram (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    ZLattice.covolume L ^ 2 = (Matrix.gram ℝ fun i ↦ (b i : E)).det := by
  have hcard : finrank ℝ E = Fintype.card ι := by
    rw [← ZLattice.rank ℝ L, finrank_eq_card_basis b]
  let o : OrthonormalBasis ι ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex (Fintype.equivFinOfCardEq hcard.symm).symm
  -- The fundamental parallelepiped of an orthonormal basis has volume `1`.
  have hvol : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [← ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (ZSpan.isAddFundamentalDomain o.toBasis volume), o.coe_toBasis,
      ZLattice.covolume_span_orthonormalBasis]
  -- The Gram matrix is `Mᵀ M`, where `M` is the matrix of the lattice basis in orthonormal
  -- coordinates.
  have hM : o.toBasis.toMatrix ((↑) ∘ b) = Matrix.of fun i j ↦ o.repr (b j : E) i := by
    ext i j
    simp [Basis.toMatrix_apply]
  have hgram : (Matrix.gram ℝ fun i ↦ (b i : E)).det = o.toBasis.det ((↑) ∘ b) ^ 2 := by
    rw [Matrix.gram_eq_conjTranspose_mul o, Matrix.det_mul, Matrix.det_conjTranspose,
      star_trivial, Basis.det_apply, hM, sq]
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis, hvol, hgram, mul_one, sq_abs]

/-- The covolume of the dual of a full lattice is the inverse of the covolume of the lattice. -/
@[simp]
theorem _root_.ZLattice.covolume_dual (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume (ZLattice.dual L) = (ZLattice.covolume L)⁻¹ := by
  classical
  let b := Free.chooseBasis ℤ L
  let B := b.ofZLatticeBasis ℝ L
  let D := BilinForm.dualBasis (innerₗ E) nondegenerate_inner B
  -- The dual lattice is the `ℤ`-span of the dual basis `D`, so `D` is a `ℤ`-basis of it.
  have hdual : span ℤ (Set.range D) = ZLattice.dual L := by
    conv_rhs => rw [← b.ofZLatticeBasis_span ℝ L]
    rw [ZLattice.dual_span_basis]
  let bD : Basis _ ℤ (ZLattice.dual L) :=
    (Basis.span (D.linearIndependent.restrict_scalars' ℤ)).map (LinearEquiv.ofEq _ _ hdual)
  have hB : (fun i ↦ (b i : E)) = ⇑B := funext fun i ↦ (b.ofZLatticeBasis_apply ℝ L i).symm
  have hD : (fun i ↦ (bD i : E)) = ⇑D := funext fun i ↦ by simp [bD, Basis.span_apply]
  have hgram (v : Basis (Free.ChooseBasisIndex ℤ L) ℝ E) :
      Matrix.gram ℝ ⇑v = BilinForm.toMatrix v (innerₗ E) := by
    ext i j
    simp [BilinForm.toMatrix_apply, Matrix.gram_apply]
  -- The squared covolumes are the Gram determinants of `D` and `B`, which are inverse.
  have hsq : (ZLattice.covolume (ZLattice.dual L) * ZLattice.covolume L) ^ 2 = 1 := by
    rw [mul_pow, ZLattice.covolume_sq_eq_det_gram _ bD, ZLattice.covolume_sq_eq_det_gram L b, hB,
      hD, hgram, hgram]
    exact BilinForm.det_toMatrix_dualBasis_mul_det_toMatrix _ _ B
  have hpos := mul_pos (ZLattice.covolume_pos (ZLattice.dual L) volume)
    (ZLattice.covolume_pos L volume)
  exact eq_inv_of_mul_eq_one_left ((pow_eq_one_iff_of_nonneg hpos.le two_ne_zero).mp hsq)

/-- A full lattice `L` is the image of the `ℤ`-span of any orthonormal basis `o` (a copy of `ℤⁿ`)
under a linear automorphism `A` with `|det A| = covolume L`, and its dual `L^∨` is the image of
the same span under the adjoint of `A⁻¹`. -/
theorem _root_.ZLattice.exists_comap_eq_span_orthonormalBasis (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] {ι : Type*} [Fintype ι] (o : OrthonormalBasis ι ℝ E) :
    ∃ A : E ≃L[ℝ] E, ZLattice.comap ℝ L A.toLinearMap = span ℤ (Set.range o) ∧
      ZLattice.comap ℝ (ZLattice.dual L)
          (ContinuousLinearMap.adjoint (A.symm : E →L[ℝ] E)).toLinearMap =
        span ℤ (Set.range o) ∧
      |A.toLinearEquiv.toLinearMap.det| = ZLattice.covolume L := by
  classical
  -- A `ℤ`-basis of `L` indexed by `ι`, which has the right cardinality.
  have hcard : Fintype.card ι = Fintype.card (Free.ChooseBasisIndex ℤ L) := by
    rw [← finrank_eq_card_basis o.toBasis, ← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  let b : Basis ι ℤ L := (Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq hcard).symm
  -- `A` sends `o i` to the `i`-th vector of `b`.
  let A : E ≃L[ℝ] E :=
    (o.toBasis.equiv (b.ofZLatticeBasis ℝ L) (Equiv.refl ι)).toContinuousLinearEquiv
  -- `L` is the `ℤ`-span of `A '' range o`, so its pull-back along `A` is the span of `range o`.
  have hL : span ℤ ((A.toLinearMap.restrictScalars ℤ) '' Set.range o) = L := by
    conv_rhs => rw [← b.ofZLatticeBasis_span ℝ L]
    rw [← Set.range_comp]
    congr 2
    ext i
    simp only [A, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_toContinuousLinearEquiv, LinearEquiv.coe_coe]
    rw [← o.coe_toBasis, Basis.equiv_apply, Equiv.refl_apply]
  have hA : ZLattice.comap ℝ L A.toLinearMap = span ℤ (Set.range o) := by
    ext x
    rw [ZLattice.mem_comap, ← hL]
    exact apply_mem_span_image_iff_mem_span A.injective
  refine ⟨A, hA, ?_, ?_⟩
  · rw [← ZLattice.dual_comap_continuousLinearEquiv, hA, ZLattice.dual_span_orthonormalBasis]
  · have h := ZLattice.covolume_comap_continuousLinearEquiv L volume A
    rw [hA, ZLattice.covolume_span_orthonormalBasis] at h
    exact (inv_mul_eq_one₀ (abs_ne_zero.mpr A.toLinearEquiv.isUnit_det'.ne_zero)).mp h.symm

end TauCeti
