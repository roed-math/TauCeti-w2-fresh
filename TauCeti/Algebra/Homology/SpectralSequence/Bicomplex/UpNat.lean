/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.FirstPage
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Stabilization
public import TauCeti.Algebra.Homology.TotalComplex.UpNat

/-!
# The spectral sequence of a first-quadrant cochain bicomplex filtered by rows

Let `K` be a first-quadrant bicomplex with cohomological differentials (both of shape
`ComplexShape.up ℕ`) in an abelian category. Its row `q` is the complex
`(K.X 0).X q ⟶ (K.X 1).X q ⟶ ⋯` formed by the horizontal differentials. The vertical differentials
raise the row index, so the rows `≥ s` span a subcomplex of the total complex, and these
subcomplexes form a decreasing filtration whose graded pieces are the rows. This file constructs
the spectral sequence of that filtration (`HomologicalComplex₂.rowFiltrationUpSpectralSequence`):
its first page is the cohomology of the rows, and it converges to the cohomology of the total
complex. Applied to the flipped bicomplex `K.flip`, whose rows are the columns `K.X p` of `K`, it
gives the spectral sequence `HomologicalComplex₂.columnFiltrationUpSpectralSequence` whose first
page is the vertical cohomology of `K` and which converges to the cohomology of the total complex
of `K`. This is the cohomological counterpart of
`TauCeti.Algebra.Homology.SpectralSequence.Bicomplex`.

The subcomplex of the rows `≥ s` is built by induction on `s`: it is the total complex of the rows
`≥ s` (`HomologicalComplex₂.totalRowsGEUp`), obtained from the total complex of the rows `≥ s - 1`
of the bicomplex `HomologicalComplex₂.rowsSuccUp K` of the rows `≥ 1` of `K`, placed one degree
higher. The degreewise split short exact sequences `Tot (rows ≥ s + 1) ⟶ Tot (rows ≥ s) ⟶ row s`
(`HomologicalComplex₂.totalRowUpShortComplex_shortExact`) come from
`HomologicalComplex₂.rowsSuccUpShortComplex_shortExact`, and identify the graded pieces of the
filtration with the rows (`HomologicalComplex₂.rowFiltrationUpGradedIso`).

## Indexing

The spectral sequences of filtered complexes in `TauCeti.Algebra.Homology.SpectralSequence.Filtered`
are those of increasing filtrations of cochain complexes indexed by `ℤ`, with Mathlib's numbering
`coreE₂Cohomological`, in which the first page is numbered `2`. The total complex is extended to a
cochain complex indexed by `ℤ` along `ComplexShape.embeddingUpNat`, and its rows `≥ s` are the
`(-s)`th term of the increasing filtration `HomologicalComplex₂.rowFiltrationUp`. The object at
`(p, -(s + 1))` on the first page is then the cohomology of the row `s` in degree `k`, where
`p = k + 2s + 1` (`HomologicalComplex₂.rowFiltrationUpSpectralSequenceFirstPageXIso`), and the first
page vanishes outside this range. The abutment in degree `n` is the cohomology of the total complex
in degree `n` (`HomologicalComplex₂.rowFiltrationUpAbutmentIso`). The filtration is finite in each
degree, so each object stabilizes after finitely many pages to the corresponding graded piece of
the abutment (`HomologicalComplex₂.rowFiltrationUpSpectralSequencePageXIsoEInfty`).

## Main definitions and results

* `HomologicalComplex₂.rowFiltrationUp`: the filtration of the total complex by the rows `≥ s`.
* `HomologicalComplex₂.rowFiltrationUpGradedIso`: its graded pieces are the rows.
* `HomologicalComplex₂.rowFiltrationUpSpectralSequence`: its spectral sequence.
* `HomologicalComplex₂.rowFiltrationUpSpectralSequenceFirstPageXIso`: the first page is the
  cohomology of the rows.
* `HomologicalComplex₂.rowFiltrationUpSpectralSequence_page_two_d`: the first differential is the
  connecting map of `Tot (rows ≥ s + 1) ⟶ Tot (rows ≥ s) ⟶ row s` followed by the projection
  onto the row `s + 1`.
* `HomologicalComplex₂.columnFiltrationUpSpectralSequenceFirstPageXIso`: the first page of the row
  filtration of the flipped bicomplex is the cohomology of the original columns.
* `HomologicalComplex₂.isZero_rowFiltrationUpSpectralSequence_page_two_X_of_lt`,
  `HomologicalComplex₂.isZero_rowFiltrationUpSpectralSequence_page_two_X_of_nonneg`: the first
  page vanishes outside the range of the rows.
* `HomologicalComplex₂.rowFiltrationUpAbutmentIso`,
  `HomologicalComplex₂.columnFiltrationUpAbutmentIso`,
  `HomologicalComplex₂.rowFiltrationUpSpectralSequencePageXIsoEInfty`,
  `HomologicalComplex₂.isZero_rowFiltrationUp_abutmentFiltration`,
  `HomologicalComplex₂.isIso_rowFiltrationUp_abutmentFiltrationι`: convergence to the cohomology of
  the total complex.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Section 5.6.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 2.15.
-/

public section

noncomputable section

open CategoryTheory Limits ComplexShape

namespace HomologicalComplex₂

section Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteCoproducts C] [HasZeroObject C]

/-- The total complex of the rows `≥ s` of `K`, placed in the degrees they occupy in the total
complex of `K`. It is the subcomplex of the total complex of `K` spanned by its rows `≥ s`. It is
an abbreviation so that, for `s + 1`, it is reducibly the extension of the total complex of the
rows `≥ s` of `K.rowsSuccUp`, which lets `simp` compose the maps out of it. -/
abbrev totalRowsGEUp (K : HomologicalComplex₂ C (up ℕ) (up ℕ)) : ℕ → CochainComplex C ℕ
  | 0 => K.total (up ℕ)
  | s + 1 => (totalRowsGEUp K.rowsSuccUp s).extend (embeddingUpNatAdd 1)

/-- The inclusion of the total complex of the rows `≥ s` into the total complex of `K`. -/
def totalRowsGEUpι (K : HomologicalComplex₂ C (up ℕ) (up ℕ)) :
    (s : ℕ) → K.totalRowsGEUp s ⟶ K.total (up ℕ)
  | 0 => 𝟙 _
  | s + 1 => HomologicalComplex.extendMap (totalRowsGEUpι K.rowsSuccUp s) (embeddingUpNatAdd 1) ≫
      K.rowsSuccUpι

/-- The inclusion of the total complex of the rows `≥ s + 1` into that of the rows `≥ s`. -/
def totalRowsGEUpMap (K : HomologicalComplex₂ C (up ℕ) (up ℕ)) :
    (s : ℕ) → K.totalRowsGEUp (s + 1) ⟶ K.totalRowsGEUp s
  | 0 => K.rowsSuccUpι
  | s + 1 => HomologicalComplex.extendMap (totalRowsGEUpMap K.rowsSuccUp s) (embeddingUpNatAdd 1)

/-- The row `s` of `K`, placed in the degrees it occupies in the total complex of `K`: its term
in degree `p + s` is `(K.X p).X s`. It is an abbreviation for the same reason as
`HomologicalComplex₂.totalRowsGEUp`. -/
abbrev totalRowUp (K : HomologicalComplex₂ C (up ℕ) (up ℕ)) : ℕ → CochainComplex C ℕ
  | 0 => ((HomologicalComplex.eval C (up ℕ) 0).mapHomologicalComplex (up ℕ)).obj K
  | s + 1 => (totalRowUp K.rowsSuccUp s).extend (embeddingUpNatAdd 1)

/-- The projection of the total complex of the rows `≥ s` onto its bottom row `s`. -/
def totalRowUpπ (K : HomologicalComplex₂ C (up ℕ) (up ℕ)) :
    (s : ℕ) → K.totalRowsGEUp s ⟶ K.totalRowUp s
  | 0 => K.rowZeroUpπ
  | s + 1 => HomologicalComplex.extendMap (totalRowUpπ K.rowsSuccUp s) (embeddingUpNatAdd 1)

variable (K : HomologicalComplex₂ C (up ℕ) (up ℕ))

/-- The inclusion of the total complex of the rows `≥ 0` is the identity. -/
@[simp]
lemma totalRowsGEUpι_zero : K.totalRowsGEUpι 0 = 𝟙 _ := (rfl)

/-- The inclusions of the total complexes of the rows `≥ s + 1` and `≥ s` are compatible. -/
@[reassoc (attr := simp)]
lemma totalRowsGEUpMap_totalRowsGEUpι (s : ℕ) :
    K.totalRowsGEUpMap s ≫ K.totalRowsGEUpι s = K.totalRowsGEUpι (s + 1) := by
  induction s generalizing K with
  | zero => simp [totalRowsGEUpMap, totalRowsGEUpι, HomologicalComplex.extendMap_id]
  | succ s ih =>
    simp only [totalRowsGEUpMap, totalRowsGEUpι]
    rw [← HomologicalComplex.extendMap_comp_assoc, ih]
    -- Both sides are the inclusion of the rows `≥ s + 2`, unfolded one step further on the right.
    rfl

/-- The row `s` is the quotient of the rows `≥ s` by the rows `≥ s + 1`. -/
@[reassoc (attr := simp)]
lemma totalRowsGEUpMap_totalRowUpπ (s : ℕ) :
    K.totalRowsGEUpMap s ≫ K.totalRowUpπ s = 0 := by
  induction s generalizing K with
  | zero => exact K.rowsSuccUpι_rowZeroUpπ
  | succ s ih => simp [totalRowsGEUpMap, totalRowUpπ, ← HomologicalComplex.extendMap_comp, ih]

/-- The total complex of the rows `≥ s` vanishes below degree `s`. -/
lemma isZero_totalRowsGEUp_X (s n : ℕ) (hn : n < s) : IsZero ((K.totalRowsGEUp s).X n) := by
  induction s generalizing K n with
  | zero => omega
  | succ s ih =>
    rcases n with _ | n
    · exact (K.rowsSuccUp.totalRowsGEUp s).isZero_extend_X (embeddingUpNatAdd 1) 0
        (fun _ ↦ by simp)
    · exact (ih K.rowsSuccUp n (by omega)).of_iso
        ((K.rowsSuccUp.totalRowsGEUp s).extendXIso (embeddingUpNatAdd 1) (by simp))

/-- The short complex `Tot (rows ≥ s + 1) ⟶ Tot (rows ≥ s) ⟶ row s`. -/
abbrev totalRowUpShortComplex (s : ℕ) : ShortComplex (CochainComplex C ℕ) :=
  ShortComplex.mk (K.totalRowsGEUpMap s) (K.totalRowUpπ s) (K.totalRowsGEUpMap_totalRowUpπ s)

end Preadditive

section Abelian

variable {C : Type*} [Category* C] [Abelian C] (K : HomologicalComplex₂ C (up ℕ) (up ℕ))

/-- The short complex `Tot (rows ≥ s + 1) ⟶ Tot (rows ≥ s) ⟶ row s` is short exact; it is split
in each degree. -/
lemma totalRowUpShortComplex_shortExact (s : ℕ) : (K.totalRowUpShortComplex s).ShortExact := by
  induction s generalizing K with
  | zero => exact K.rowsSuccUpShortComplex_shortExact
  | succ s ih => exact (ih K.rowsSuccUp).extend (embeddingUpNatAdd 1)

/-- The total complex of the rows `≥ s` is a subcomplex of the total complex. -/
instance mono_totalRowsGEUpι (s : ℕ) : Mono (K.totalRowsGEUpι s) := by
  induction s with
  | zero => rw [totalRowsGEUpι_zero]; infer_instance
  | succ s ih =>
    have := (K.totalRowUpShortComplex_shortExact s).mono_f
    rw [← totalRowsGEUpMap_totalRowsGEUpι]
    infer_instance

/-- The total complex of the rows `≥ s + 1` is a subcomplex of that of the rows `≥ s`. -/
instance mono_totalRowsGEUpMap (s : ℕ) : Mono (K.totalRowsGEUpMap s) :=
  (K.totalRowUpShortComplex_shortExact s).mono_f

/-- The cohomology of the row `s` placed in the degrees of the total complex: in degree `k + s` it
is the cohomology of the row `s` in degree `k`. -/
def totalRowUpHomologyIso (K : HomologicalComplex₂ C (up ℕ) (up ℕ)) : (s k : ℕ) →
    (K.totalRowUp s).homology (k + s) ≅
      (((HomologicalComplex.eval C (up ℕ) s).mapHomologicalComplex (up ℕ)).obj K).homology k
  | 0, _ => Iso.refl _
  | s + 1, k =>
    -- The row `s` of `K.rowsSuccUp` is the row `s + 1` of `K` by definition.
    (K.rowsSuccUp.totalRowUp s).extendHomologyIso (embeddingUpNatAdd 1) (j := k + s) rfl ≪≫
      totalRowUpHomologyIso K.rowsSuccUp s k

/-- The row `s` placed in the degrees of the total complex has no cohomology below degree `s`. -/
lemma isZero_totalRowUp_homology (s n : ℕ) (hn : n < s) :
    IsZero ((K.totalRowUp s).homology n) := by
  induction s generalizing K n with
  | zero => omega
  | succ s ih =>
    rcases n with _ | n
    · exact ((K.rowsSuccUp.totalRowUp s).extend_exactAt (embeddingUpNatAdd 1) 0
        (fun _ ↦ by simp)).isZero_homology
    · exact (ih K.rowsSuccUp n (by omega)).of_iso
        ((K.rowsSuccUp.totalRowUp s).extendHomologyIso (embeddingUpNatAdd 1) (j := n) (by simp))

/-! ### The row filtration of the total complex -/

/-- The filtration of the total complex of `K` by its rows `≥ -i`, a subcomplex since the vertical
differentials raise the row index. The total complex is regarded as a cochain complex indexed by
`ℤ`, and the filtration is indexed so as to be increasing, as for the spectral sequences of
filtered complexes; it is everything for `0 ≤ i`. -/
def rowFiltrationUp (i : ℤ) : Subobject ((K.total (up ℕ)).extend embeddingUpNat) :=
  Subobject.mk (HomologicalComplex.extendMap (K.totalRowsGEUpι (-i).toNat) embeddingUpNat)

/-- The term of index `i` of the row filtration is the subcomplex of the rows `≥ s` for
`s = max (-i) 0`; for instance the term of index `-s` of the rows `≥ s`. -/
lemma rowFiltrationUp_eq (i : ℤ) (s : ℕ) (h : (-i).toNat = s) :
    K.rowFiltrationUp i =
      Subobject.mk (HomologicalComplex.extendMap (K.totalRowsGEUpι s) embeddingUpNat) := by
  subst h
  rfl

/-- The term of index `-(s + 1)` of the row filtration is the subcomplex of the rows `≥ s + 1`,
whose inclusion factors through that of the rows `≥ s`. -/
lemma rowFiltrationUp_eq_succ (i : ℤ) (s : ℕ) (h : i = -(s + 1)) :
    K.rowFiltrationUp i =
      Subobject.mk (HomologicalComplex.extendMap (K.totalRowsGEUpMap s) embeddingUpNat ≫
        HomologicalComplex.extendMap (K.totalRowsGEUpι s) embeddingUpNat) := by
  simp only [← HomologicalComplex.extendMap_comp, totalRowsGEUpMap_totalRowsGEUpι]
  exact K.rowFiltrationUp_eq i (s + 1) (by omega)

/-- The row filtration is increasing. -/
lemma monotone_rowFiltrationUp : Monotone K.rowFiltrationUp := by
  have : Antitone fun s : ℕ ↦
      Subobject.mk (HomologicalComplex.extendMap (K.totalRowsGEUpι s) embeddingUpNat) :=
    antitone_nat_of_succ_le fun s ↦ Subobject.mk_le_mk_of_comm
      (HomologicalComplex.extendMap (K.totalRowsGEUpMap s) embeddingUpNat) (by
        rw [← HomologicalComplex.extendMap_comp, totalRowsGEUpMap_totalRowsGEUpι])
  exact fun _ _ h ↦ this (Int.toNat_le_toNat (by omega))

/-- The row filtration is everything in the indices `≥ 0`. -/
lemma rowFiltrationUp_eq_top (i : ℤ) (hi : 0 ≤ i) : K.rowFiltrationUp i = ⊤ := by
  have : IsIso (HomologicalComplex.extendMap (K.totalRowsGEUpι 0) embeddingUpNat) := by
    rw [totalRowsGEUpι_zero, HomologicalComplex.extendMap_id]
    infer_instance
  rw [K.rowFiltrationUp_eq i 0 (by omega)]
  exact Subobject.mk_eq_top_of_isIso _

/-- The term of index `-s` of the row filtration vanishes in the degrees `< s`. -/
lemma isZero_rowFiltrationUp_X (s : ℕ) (m : ℤ) (hm : m < s) :
    IsZero ((K.rowFiltrationUp (-s) : CochainComplex C ℤ).X m) := by
  rw [K.rowFiltrationUp_eq (-s) s (by omega)]
  refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (up ℤ) m).mapIso
    (Subobject.underlyingIso _))
  by_cases hm' : 0 ≤ m
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n := ⟨m.toNat, by omega⟩
    exact (K.isZero_totalRowsGEUp_X s n (by omega)).of_iso
      ((K.totalRowsGEUp s).extendXIso embeddingUpNat (by simp))
  · exact (K.totalRowsGEUp s).isZero_extend_X embeddingUpNat m (fun n hn ↦ by simp at hn; omega)

/-- The term of index `i = -s` of the row filtration, as a complex, is the total complex of the
rows `≥ s`, extended to a complex indexed by `ℤ`. -/
def rowFiltrationUpObjIso (s : ℕ) (i : ℤ) (hi : i = -s) :
    (CochainComplex.filtrationFunctor K.rowFiltrationUp K.monotone_rowFiltrationUp).obj i ≅
      (K.totalRowsGEUp s).extend embeddingUpNat :=
  CochainComplex.filtrationFunctorObjIso _ _ _ ≪≫ Subobject.isoOfEq _ _ (by
      rw [CochainComplex.filtrationEInt_coe, K.rowFiltrationUp_eq _ s (by omega)]) ≪≫
    Subobject.underlyingIso _

/-- The identification `HomologicalComplex₂.rowFiltrationUpObjIso` is compatible with the
inclusions into the total complex. -/
@[reassoc (attr := simp)]
lemma rowFiltrationUpObjIso_hom_extendMap_totalRowsGEUpι (s : ℕ) (i : ℤ) (hi : i = -s) :
    (K.rowFiltrationUpObjIso s i hi).hom ≫
        HomologicalComplex.extendMap (K.totalRowsGEUpι s) embeddingUpNat =
      CochainComplex.filtrationFunctorArrow _ _ i := by
  simp [rowFiltrationUpObjIso]

/-- Under `HomologicalComplex₂.rowFiltrationUpObjIso`, the inclusion of the term of index `i₁`
of the row filtration into that of index `i₁ + 1` is the inclusion of the rows `≥ s + 1` into the
rows `≥ s`, for `i₁ = -(s + 1)`. -/
@[reassoc]
lemma filtrationFunctor_map_rowFiltrationUpObjIso_hom (s : ℕ) (i₁ i₂ : ℤ)
    (hi₁ : i₁ = -(s + 1)) (hi₂ : i₂ = i₁ + 1) :
    (CochainComplex.filtrationFunctor K.rowFiltrationUp K.monotone_rowFiltrationUp).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : i₁ = i₁) hi₂)) ≫
        (K.rowFiltrationUpObjIso s i₂ (by omega)).hom =
      (K.rowFiltrationUpObjIso (s + 1) i₁ (by omega)).hom ≫
        HomologicalComplex.extendMap (K.totalRowsGEUpMap s) embeddingUpNat := by
  rw [← cancel_mono (HomologicalComplex.extendMap (K.totalRowsGEUpι s) embeddingUpNat)]
  simp [← HomologicalComplex.extendMap_comp]

/-- The quotient of the rows `≥ s` by the rows `≥ s + 1` of the total complex of `K`, that is, the
cokernel of the inclusion of the term of index `i₁ = -(s + 1)` of the row filtration into that of
index `i₁ + 1`, is the row `s`, placed in the degrees it occupies in the total complex. -/
def rowFiltrationUpGradedIso (s : ℕ) (i₁ i₂ : ℤ) (hi₁ : i₁ = -(s + 1)) (hi₂ : i₂ = i₁ + 1) :
    cokernel ((CochainComplex.filtrationFunctor K.rowFiltrationUp K.monotone_rowFiltrationUp).map
      (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : i₁ = i₁) hi₂))) ≅
      (K.totalRowUp s).extend embeddingUpNat :=
  cokernel.mapIso _ ((K.totalRowUpShortComplex s).map (embeddingUpNat.extendFunctor C)).f
      (K.rowFiltrationUpObjIso (s + 1) i₁ (by omega))
      (K.rowFiltrationUpObjIso s i₂ (by omega))
      (K.filtrationFunctor_map_rowFiltrationUpObjIso_hom s i₁ i₂ hi₁ hi₂) ≪≫
    (cokernelIsCokernel _).coconePointUniqueUpToIso
      ((K.totalRowUpShortComplex_shortExact s).extend embeddingUpNat).gIsCokernel

/-- The identification `HomologicalComplex₂.rowFiltrationUpGradedIso` of the graded piece with the
row `s` is induced by the projection of the rows `≥ s` onto their bottom row `s`. -/
@[reassoc (attr := simp)]
lemma π_rowFiltrationUpGradedIso_hom (s : ℕ) (i₁ i₂ : ℤ) (hi₁ : i₁ = -(s + 1))
    (hi₂ : i₂ = i₁ + 1) :
    cokernel.π ((CochainComplex.filtrationFunctor K.rowFiltrationUp
        K.monotone_rowFiltrationUp).map
          (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : i₁ = i₁) hi₂))) ≫
        (K.rowFiltrationUpGradedIso s i₁ i₂ hi₁ hi₂).hom =
      (K.rowFiltrationUpObjIso s i₂ (by omega)).hom ≫
        HomologicalComplex.extendMap (K.totalRowUpπ s) embeddingUpNat := by
  have h : cokernel.π ((K.totalRowUpShortComplex s).map (embeddingUpNat.extendFunctor C)).f ≫
      ((cokernelIsCokernel _).coconePointUniqueUpToIso
        ((K.totalRowUpShortComplex_shortExact s).extend embeddingUpNat).gIsCokernel).hom =
      HomologicalComplex.extendMap (K.totalRowUpπ s) embeddingUpNat :=
    (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one
  dsimp only [rowFiltrationUpGradedIso, Iso.trans, cokernel.mapIso, cokernel.map]
  rw [cokernel.π_desc_assoc, Category.assoc]
  exact congrArg ((K.rowFiltrationUpObjIso s i₂ (by omega)).hom ≫ ·) h

/-! ### The spectral sequence -/

/-- The spectral sequence of the filtration of the total complex of `K` by its rows. It uses
Mathlib's cohomological indexing, in which the first page is numbered `2`: its object at
`(p, -(s + 1))` is `Hᵏ` of the row `s` with `p = k + 2s + 1`
(`HomologicalComplex₂.rowFiltrationUpSpectralSequenceFirstPageXIso`). -/
abbrev rowFiltrationUpSpectralSequence :=
  CochainComplex.spectralSequence
    (CochainComplex.filtrationFunctor K.rowFiltrationUp K.monotone_rowFiltrationUp)

/-- The object at `pq = (p, q)` on the first page (numbered `2`) of the spectral sequence of the
row filtration, for `q = -(s + 1)`, is the cohomology in degree `n = p + q` of the row `s`, placed
in the degrees it occupies in the total complex. The indices `i₁ = q` and `i₂ = q + 1` of the
filtration steps are given up to equality, as in
`CochainComplex.spectralSequenceFirstPageXIsoCokernel`. -/
def rowFiltrationUpSpectralSequenceFirstPageXIsoTotalRow (pq : ℤ × ℤ) (i₁ i₂ : ℤ)
    (hi₁ : i₁ = pq.2) (hi₂ : i₂ = pq.2 + 1) (s : ℕ) (hs : i₁ = -(s + 1)) (n : ℤ)
    (hn : n = pq.1 + pq.2) :
    (K.rowFiltrationUpSpectralSequence.page 2).X pq ≅
      ((K.totalRowUp s).extend embeddingUpNat).homology n :=
  CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq i₁ i₂ hi₁ hi₂ n hn ≪≫
    HomologicalComplex.homologyMapIso (K.rowFiltrationUpGradedIso s i₁ i₂ hs (by omega)) n

/-- **The first differential of the spectral sequence of the row filtration.** Under the
identifications of the first page with the cohomology of the rows, the differential from
`(p, q)` to `(p + 2, q - 1)`, for `q = -(s + 1)`, is the connecting map
`Hⁿ(row s) ⟶ Hⁿ⁺¹(Tot (rows ≥ s + 1))` of the short exact sequence
`Tot (rows ≥ s + 1) ⟶ Tot (rows ≥ s) ⟶ row s`, followed by the projection of the rows `≥ s + 1`
onto the row `s + 1`. -/
theorem rowFiltrationUpSpectralSequence_page_two_d (p q : ℤ) (s : ℕ) (hq : q = -(s + 1)) :
    (K.rowFiltrationUpSpectralSequence.page 2).d (p, q) (p + 2, q - 1) =
      (K.rowFiltrationUpSpectralSequenceFirstPageXIsoTotalRow (p, q) q (q + 1) rfl rfl s hq
          (p + q) rfl).hom ≫
        ((K.totalRowUpShortComplex_shortExact s).extend embeddingUpNat).δ
          (p + q) (p + q + 1) (ComplexShape.up_mk _ _ rfl) ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap (K.totalRowUpπ (s + 1)) embeddingUpNat) (p + q + 1) ≫
        (K.rowFiltrationUpSpectralSequenceFirstPageXIsoTotalRow (p + 2, q - 1) (q - 1) q rfl
          (by lia) (s + 1) (by push_cast; omega) (p + q + 1) (by lia)).inv := by
  -- The morphism from `F_q ⟶ F_{q+1} ⟶ F_{q+1}/F_q` to the extended sequence
  -- `Tot (rows ≥ s + 1) ⟶ Tot (rows ≥ s) ⟶ row s`.
  let ψ : ShortComplex.cokernelSequence
      ((CochainComplex.filtrationFunctor K.rowFiltrationUp K.monotone_rowFiltrationUp).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : q = q) rfl))) ⟶
      (K.totalRowUpShortComplex s).map (embeddingUpNat.extendFunctor C) :=
    { τ₁ := (K.rowFiltrationUpObjIso (s + 1) q (by omega)).hom
      τ₂ := (K.rowFiltrationUpObjIso s (q + 1) (by omega)).hom
      τ₃ := (K.rowFiltrationUpGradedIso s q (q + 1) hq rfl).hom
      comm₁₂ := (K.filtrationFunctor_map_rowFiltrationUpObjIso_hom s q (q + 1) hq rfl).symm
      comm₂₃ := (K.π_rowFiltrationUpGradedIso_hom s q (q + 1) hq rfl).symm }
  have hnat := HomologicalComplex.HomologySequence.δ_naturality ψ
    (TauCeti.cokernelSequence_shortExact _)
    ((K.totalRowUpShortComplex_shortExact s).extend embeddingUpNat) (p + q) (p + q + 1)
    (ComplexShape.up_mk _ _ rfl)
  have hπ := K.π_rowFiltrationUpGradedIso_hom (s + 1) (q - 1) q (by push_cast; omega) (by lia)
  rw [CochainComplex.spectralSequence_first_page_d_eq_δ_comp_homologyMap_π]
  simp only [rowFiltrationUpSpectralSequenceFirstPageXIsoTotalRow, Iso.trans_hom, Iso.trans_inv,
    HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyMapIso_inv, Category.assoc]
  congr 1
  dsimp only [ψ] at hnat
  have hH : HomologicalComplex.homologyMap (cokernel.π
      ((CochainComplex.filtrationFunctor K.rowFiltrationUp K.monotone_rowFiltrationUp).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : q - 1 = q - 1)
          (by lia : q = q - 1 + 1))))) (p + q + 1) =
      HomologicalComplex.homologyMap (K.rowFiltrationUpObjIso (s + 1) q (by omega)).hom
          (p + q + 1) ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap (K.totalRowUpπ (s + 1)) embeddingUpNat) (p + q + 1) ≫
        HomologicalComplex.homologyMap (K.rowFiltrationUpGradedIso (s + 1) (q - 1) q
          (by push_cast; omega) (by lia)).inv (p + q + 1) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← reassoc_of% hπ, Iso.hom_inv_id, Category.comp_id]
  rw [hH]
  -- Reassociate by hand: the connecting maps are typed through `ShortComplex.cokernelSequence`,
  -- which `rw` and `simp` do not see through.
  exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans <| (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) hnat).trans <| (Category.assoc _ _ _).trans <|
      congrArg (_ ≫ _ ≫ ·) (Category.assoc _ _ _)

/-- **The first page of the spectral sequence of the row filtration** is the cohomology of the
rows: its object at `(p, -(s + 1))`, with `p = k + 2s + 1`, is the cohomology in degree `k` of the
row `s` `(K.X 0).X s ⟶ (K.X 1).X s ⟶ ⋯` of `K`, formed by the horizontal differentials. -/
def rowFiltrationUpSpectralSequenceFirstPageXIso (p : ℤ) (s k : ℕ) (hp : p = k + 2 * s + 1) :
    (K.rowFiltrationUpSpectralSequence.page 2).X (p, -((s : ℤ) + 1)) ≅
      (((HomologicalComplex.eval C (up ℕ) s).mapHomologicalComplex (up ℕ)).obj K).homology k :=
  K.rowFiltrationUpSpectralSequenceFirstPageXIsoTotalRow (p, -((s : ℤ) + 1)) _ _ rfl rfl s rfl
      _ rfl ≪≫
    (K.totalRowUp s).extendHomologyIso embeddingUpNat (j := k + s) (by simp; omega) ≪≫
    K.totalRowUpHomologyIso s k

/-- The first page of the spectral sequence of the row filtration vanishes at `(p, -(s + 1))` when
`p < 2s + 1`: the row `s` contributes nothing in total degree `p - (s + 1) < s`. -/
lemma isZero_rowFiltrationUpSpectralSequence_page_two_X_of_lt (p : ℤ) (s : ℕ)
    (h : p < 2 * s + 1) :
    IsZero ((K.rowFiltrationUpSpectralSequence.page 2).X (p, -((s : ℤ) + 1))) := by
  refine IsZero.of_iso ?_ (K.rowFiltrationUpSpectralSequenceFirstPageXIsoTotalRow
    (p, -((s : ℤ) + 1)) _ _ rfl rfl s rfl _ rfl)
  by_cases hps : 0 ≤ p + -((s : ℤ) + 1)
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, p + -((s : ℤ) + 1) = n := ⟨(p + -((s : ℤ) + 1)).toNat, by omega⟩
    exact (K.isZero_totalRowUp_homology s n (by omega)).of_iso
      ((K.totalRowUp s).extendHomologyIso embeddingUpNat (by simp; omega))
  · exact ((K.totalRowUp s).extend_exactAt embeddingUpNat _
      (fun n hn ↦ by simp at hn; omega)).isZero_homology

/-- The first page of the spectral sequence of the row filtration vanishes in the columns `≥ 0`
of its indexing, where the filtration is constant. -/
lemma isZero_rowFiltrationUpSpectralSequence_page_two_X_of_nonneg (p q : ℤ) (hq : 0 ≤ q) :
    IsZero ((K.rowFiltrationUpSpectralSequence.page 2).X (p, q)) := by
  have hiso (a : ℤ) (ha : 0 ≤ a) : IsIso (CochainComplex.filtrationFunctorArrow
      K.rowFiltrationUp K.monotone_rowFiltrationUp a) := by
    have : IsIso (CochainComplex.filtrationEInt K.rowFiltrationUp a).arrow := by
      rw [CochainComplex.filtrationEInt_coe, K.rowFiltrationUp_eq_top a ha]
      infer_instance
    infer_instance
  have := hiso q hq
  have := hiso (q + 1) (by omega)
  have := IsIso.of_isIso_fac_right (CochainComplex.filtrationFunctor_map_comp_arrow
    K.rowFiltrationUp K.monotone_rowFiltrationUp
      (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : q = q) rfl)))
  exact ((HomologicalComplex.homologyFunctor C (up ℤ) (p + q)).map_isZero
    (isZero_cokernel_of_epi _)).of_iso
    (CochainComplex.spectralSequenceFirstPageXIsoCokernel _ (p, q) q (q + 1) rfl rfl (p + q) rfl)

/-- The abutment of the spectral sequence of the row filtration in degree `n` is the cohomology of
the total complex of `K` in degree `n`. -/
def rowFiltrationUpAbutmentIso (n : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor K.rowFiltrationUp
      K.monotone_rowFiltrationUp)).abutment n ≅ (K.total (up ℕ)).homology n :=
  CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
    (K.total (up ℕ)).extendHomologyIso embeddingUpNat (by simp)

/-! ### Convergence -/

/-- **Convergence of the spectral sequence of the row filtration.** On every page `r ≥ 2` with
`p + 2q + 3 < r`, `q + 2 ≤ r` and `1 ≤ q + r`, the object at `(p, q)` is the limit object
`E^{p+q}(⊥ ≤ q ≤ q + 1 ≤ ⊤)`, which is the `q`th graded piece of the filtration of the abutment
(`CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel`). In particular the object at a
fixed position stabilizes after finitely many pages. -/
def rowFiltrationUpSpectralSequencePageXIsoEInfty (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (h₀ : pq.1 + 2 * pq.2 + 3 < r) (h₁ : pq.2 + 2 ≤ r) (h₃ : 1 ≤ pq.2 + r) :
    (K.rowFiltrationUpSpectralSequence.page r).X pq ≅
      (CochainComplex.spectralObject (CochainComplex.filtrationFunctor K.rowFiltrationUp
        K.monotone_rowFiltrationUp)).EInfty pq.2 (pq.1 + pq.2) :=
  CochainComplex.filtrationSpectralSequencePageXIsoEInfty _ _ r hr pq _ rfl
    (by
      obtain ⟨s, hs⟩ : ∃ s : ℕ, pq.2 - r + 2 = -s := ⟨(-(pq.2 - r + 2)).toNat, by omega⟩
      rw [hs]
      exact HomologicalComplex.ExactAt.isZero_homology
        (ShortComplex.exact_of_isZero_X₂ _ (K.isZero_rowFiltrationUp_X s _ (by omega))))
    ((K.rowFiltrationUp _).isZero_homology_cokernel_of_eq_top
      (K.rowFiltrationUp_eq_top _ (by omega)) _)

/-- The filtration of the abutment of the spectral sequence of the row filtration vanishes in
degree `n` at `-s` for `n < s`. -/
lemma isZero_rowFiltrationUp_abutmentFiltration (s : ℕ) (n : ℤ) (hn : n < s) :
    IsZero ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor K.rowFiltrationUp
      K.monotone_rowFiltrationUp)).abutmentFiltration (-s : ℤ) n) :=
  Abelian.SpectralObject.isZero_abutmentFiltration _
    (CochainComplex.isZero_spectralObject_H_bot _ _ _ _
      (HomologicalComplex.ExactAt.isZero_homology
        (ShortComplex.exact_of_isZero_X₂ _ (K.isZero_rowFiltrationUp_X s _ hn))))

/-- The filtration of the abutment of the spectral sequence of the row filtration is everything
at the indices `≥ 0`. -/
lemma isIso_rowFiltrationUp_abutmentFiltrationι (b n : ℤ) (hb : 0 ≤ b) :
    IsIso ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor K.rowFiltrationUp
      K.monotone_rowFiltrationUp)).abutmentFiltrationι b n) :=
  CochainComplex.isIso_filtrationAbutmentFiltrationι _ _ (K.rowFiltrationUp_eq_top b hb) n

/-! ### The column filtration -/

/-- The spectral sequence obtained by applying the row filtration to the flipped bicomplex. Its
first page is the vertical cohomology of the original bicomplex. -/
abbrev columnFiltrationUpSpectralSequence := K.flip.rowFiltrationUpSpectralSequence

/-- **The first page of the column-filtration spectral sequence** is the vertical cohomology of the
columns: its object at `(k + 2p + 1, -(p + 1))` is the degree-`k` cohomology of the column
`K.X p`. -/
def columnFiltrationUpSpectralSequenceFirstPageXIso (p k : ℕ) :
    (K.columnFiltrationUpSpectralSequence.page 2).X ((k : ℤ) + 2 * p + 1, -((p : ℤ) + 1)) ≅
      (K.X p).homology k :=
  -- A row of the flipped bicomplex is the corresponding column of `K` by definition.
  K.flip.rowFiltrationUpSpectralSequenceFirstPageXIso _ p k rfl

/-- The abutment of the column-filtration spectral sequence is the cohomology of the original
total complex. The comparison incorporates the Koszul sign of the total-complex flip. -/
def columnFiltrationUpAbutmentIso (n : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor K.flip.rowFiltrationUp
      K.flip.monotone_rowFiltrationUp)).abutment n ≅ (K.total (up ℕ)).homology n :=
  K.flip.rowFiltrationUpAbutmentIso n ≪≫
    HomologicalComplex.homologyMapIso (K.totalFlipIso (up ℕ)) n

end Abelian

end HomologicalComplex₂
