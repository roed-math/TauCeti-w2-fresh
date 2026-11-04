/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.UpNat
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.DoubleComplex

/-!
# The Čech-to-cohomology spectral sequence

Let `(C, J)` be a site with finite products and a terminal object `T`, let `U : ι → C` be a family
whose maps to `T` generate a covering sieve, and let `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` be an injective
resolution of an abelian sheaf `F`. Filtering the total complex of the Čech double complex
`Čᵖ(U, Kᵠ)` by the Čech degree gives a spectral sequence
(`TauCeti.CategoryTheory.cechToCohomologySpectralSequence`), the spectral sequence of the cochain
bicomplex filtered by its columns
(`HomologicalComplex₂.columnFiltrationUpSpectralSequence`). Its first page is the group of Čech
cochains `Čᵖ(U, Hᵠ(F)) = ∏ₐ Hᵠ(U (a 0) × ⋯ × U (a p), F)` of the cohomology presheaf
(`TauCeti.CategoryTheory.cechToCohomologySpectralSequenceFirstPageAddEquiv`), and it converges to
the sheaf cohomology `Hⁿ(T, F)` (`TauCeti.CategoryTheory.cechToCohomologyAbutmentAddEquiv`, with
the stabilization `HomologicalComplex₂.rowFiltrationUpSpectralSequencePageXIsoEInfty`).

## Indexing

The spectral sequence uses Mathlib's cohomological indexing of spectral sequences of filtered
complexes, in which the first page is numbered `2` and filtrations are increasing: the Čech
`p`-cochains of `Hᵠ(F)` sit at `(q + 2p + 1, -(p + 1))`, in total degree `p + q`. See
`TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.UpNat`.

## Main definitions

* `TauCeti.CategoryTheory.cechToCohomologySpectralSequence U K`: the spectral sequence of the
  Čech double complex of `K` filtered by Čech degree.
* `TauCeti.CategoryTheory.cechToCohomologySpectralSequenceFirstPageAddEquiv`: its first page is
  `Čᵖ(U, Hᵠ(F))`.
* `TauCeti.CategoryTheory.cechToCohomologyAbutmentAddEquiv`: its abutment is `Hⁿ(T, F)`.

## References

* [Stacks: Tag 03AV](https://stacks.math.columbia.edu/tag/03AV), Section 21.10 on Čech cohomology
  and cohomology.
-/

public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {J : GrothendieckTopology C}
  {ι : Type v} (U : ι → C) (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ)

/-- The **Čech-to-cohomology spectral sequence** of the family `U` with coefficients in the
cochain complex `K` of abelian sheaves: the spectral sequence of the total complex of the Čech
double complex `Čᵖ(U, Kᵠ)` filtered by the Čech degree `p`. For an injective resolution `K` of an
abelian sheaf `F` and a covering family `U`, it goes from `Čᵖ(U, Hᵠ(F))` to `Hᵖ⁺ᵠ(T, F)`. -/
abbrev cechToCohomologySpectralSequence :=
  (cechDoubleComplex U K).columnFiltrationUpSpectralSequence

/-- The spectral object of the filtration of the total Čech complex by Čech degree, whose
abutment is the target of the Čech-to-cohomology spectral sequence. -/
abbrev cechToCohomologySpectralObject :=
  CochainComplex.spectralObject (CochainComplex.filtrationFunctor
    (cechDoubleComplex U K).flip.rowFiltrationUp
    (cechDoubleComplex U K).flip.monotone_rowFiltrationUp)

variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
  {F : Sheaf J AddCommGrpCat.{v}} {K} (ε : F ⟶ K.X 0) [Mono ε] (hε : ε ≫ K.d 0 1 = 0)
  (hε' : (ShortComplex.mk ε (K.d 0 1) hε).Exact) (hK : ∀ j, K.ExactAt (j + 1))

/-- **The first page of the Čech-to-cohomology spectral sequence.** For a resolution
`0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` of an abelian sheaf `F` whose terms have no cohomology in positive degrees
on the finite products of members of `U` (for instance an injective resolution), the object of the
first page at `(q + 2p + 1, -(p + 1))` is the group `∏ₐ Hᵠ(U (a 0) × ⋯ × U (a p), F)` of Čech
`p`-cochains of the cohomology presheaf `Hᵠ(-, F)`. -/
@[stacks 03AV "The first page of the Čech-to-cohomology spectral sequence."]
def cechToCohomologySpectralSequenceFirstPageAddEquiv
    (hKU : ∀ (m : ℕ) (a : Fin (m + 1) → ι) j k,
      Subsingleton ((K.X j).H' (k + 1) (∏ᶜ fun i ↦ U (a i)))) (p q : ℕ) :
    ((cechToCohomologySpectralSequence U K).page 2).X ((q : ℤ) + 2 * p + 1, -((p : ℤ) + 1)) ≃+
      ∀ a : Fin (p + 1) → ι, F.H' q (∏ᶜ fun j ↦ U (a j)) :=
  ((cechDoubleComplex U K).columnFiltrationUpSpectralSequenceFirstPageXIso p
    q).addCommGroupIsoToAddEquiv.trans (cechDoubleComplexHomologyAddEquiv U ε hε hε' hK hKU p q)

/-- **The abutment of the Čech-to-cohomology spectral sequence.** For an injective resolution
`0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` of an abelian sheaf `F` and a family `U` whose maps to the terminal object
`T` generate a covering sieve, the abutment of the spectral sequence in degree `n` is the sheaf
cohomology `Hⁿ(T, F)`. -/
@[stacks 03AV "The abutment of the Čech-to-cohomology spectral sequence."]
def cechToCohomologyAbutmentAddEquiv {T : C} (hT : IsTerminal T)
    (hU : Sieve.ofArrows U (fun i ↦ hT.from (U i)) ∈ J T) [∀ q, Injective (K.X q)] (n : ℕ) :
    (cechToCohomologySpectralObject U K).abutment n ≃+ F.H' n T :=
  ((cechDoubleComplex U K).columnFiltrationUpAbutmentIso n).addCommGroupIsoToAddEquiv.trans
    (homologyTotalCechDoubleComplexAddEquiv U hT ε hε hε' hK hU n)

end TauCeti.CategoryTheory
