/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.SpectralSequenceMap
public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.UpNat
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Comparison

/-!
# Morphisms of spectral sequences of first-quadrant cochain bicomplexes

A morphism `f : K ⟶ L` of first-quadrant cochain bicomplexes induces morphisms between the total
complexes of their rows `≥ s` (`HomologicalComplex₂.totalRowsGEUpMapOfHom`), compatible with the
inclusions into the total complexes (`HomologicalComplex₂.totalRowsGEUpMapOfHom_totalRowsGEUpι`).
Hence the morphism of total complexes respects the row filtrations, and induces a morphism of
the spectral sequences of the row filtrations
(`HomologicalComplex₂.rowFiltrationUpSpectralSequenceMap`). On the first pages, identified with
the cohomology of the rows, it is the map induced in the cohomology of the rows
(`HomologicalComplex₂.rowFiltrationUpSpectralSequenceMap_hom_f_firstPageXIso_hom`).

## Main definitions

* `HomologicalComplex₂.rowsSuccUpMap`: the morphism of the bicomplexes of rows `≥ 1`.
* `HomologicalComplex₂.totalRowsGEUpMapOfHom`: the morphism of the total complexes of the rows
  `≥ s`.
* `HomologicalComplex₂.rowFiltrationUpSpectralSequenceMap`: the morphism of row-filtration
  spectral sequences.

## Main results

* `HomologicalComplex₂.rowFiltrationUpSpectralSequenceMap_hom_f_firstPageXIso_hom`: its value on
  the first page.
* `HomologicalComplex₂.spectralObjectMap_rowFiltrationUpMap_hom_app_rowFiltrationUpAbutmentIso_hom`:
  on the abutments, the map induced in the cohomology of the total complexes.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape

namespace HomologicalComplex₂

section Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteCoproducts C] [HasZeroObject C]
  {K L : HomologicalComplex₂ C (up ℕ) (up ℕ)}

/-- The morphism of the bicomplexes of rows `≥ 1` induced by a morphism of bicomplexes. -/
@[simps]
def rowsSuccUpMap (f : K ⟶ L) : K.rowsSuccUp ⟶ L.rowsSuccUp where
  f p :=
    { f q := (f.f p).f (q + 1)
      comm' q q' _ := (f.f p).comm (q + 1) (q' + 1) }
  comm' p p' _ := by
    ext q
    exact HomologicalComplex.congr_hom (f.comm p p') (q + 1)

/-- The inclusions of the total complexes of the rows `≥ 1` are natural. -/
@[reassoc]
lemma rowsSuccUpι_naturality (f : K ⟶ L) :
    HomologicalComplex.extendMap (total.map (rowsSuccUpMap f) (up ℕ))
        (embeddingUpNatAdd 1) ≫ L.rowsSuccUpι =
      K.rowsSuccUpι ≫ total.map f (up ℕ) := by
  ext n : 1
  rcases n with _ | n
  · exact (HomologicalComplex.isZero_extend_X _ _ 0 fun i ↦ by simp).eq_of_src _ _
  · rw [← cancel_epi ((K.rowsSuccUp.total (up ℕ)).extendXIso (embeddingUpNatAdd 1)
      (embeddingUpNatAdd_f 1 n)).inv]
    refine HomologicalComplex₂.total.hom_ext _ fun p q h ↦ ?_
    simp only [HomologicalComplex.comp_f, HomologicalComplex.extendMap_f _ _
      (embeddingUpNatAdd_f 1 n), Category.assoc, Iso.inv_hom_id_assoc]
    rw [ιTotal_map_assoc, ιTotal_rowsSuccUpι_f, ιTotal_rowsSuccUpι_f_assoc, ιTotal_map]
    rfl

/-- The morphism of the total complexes of the rows `≥ s` induced by a morphism of
bicomplexes. -/
noncomputable def totalRowsGEUpMapOfHom : (s : ℕ) → {K L : HomologicalComplex₂ C (up ℕ) (up ℕ)} →
    (f : K ⟶ L) → K.totalRowsGEUp s ⟶ L.totalRowsGEUp s
  | 0, _, _, f => total.map f (up ℕ)
  | s + 1, _, _, f => HomologicalComplex.extendMap (totalRowsGEUpMapOfHom s (rowsSuccUpMap f))
      (embeddingUpNatAdd 1)

/-- The morphisms of the total complexes of the rows `≥ s` commute with the inclusions into the
total complexes. -/
@[reassoc (attr := simp)]
lemma totalRowsGEUpMapOfHom_totalRowsGEUpι (s : ℕ) (f : K ⟶ L) :
    totalRowsGEUpMapOfHom s f ≫ L.totalRowsGEUpι s =
      K.totalRowsGEUpι s ≫ total.map f (up ℕ) := by
  induction s generalizing K L with
  | zero =>
    rw [totalRowsGEUpι_zero, totalRowsGEUpι_zero, Category.comp_id, Category.id_comp]
    rfl
  | succ s ih =>
    rw [totalRowsGEUpMapOfHom, totalRowsGEUpι_succ, totalRowsGEUpι_succ,
      ← HomologicalComplex.extendMap_comp_assoc, ih, HomologicalComplex.extendMap_comp_assoc,
      rowsSuccUpι_naturality, Category.assoc]

/-- The morphism of the rows `s`, placed in the degrees of the total complexes, induced by a
morphism of bicomplexes. -/
noncomputable def totalRowUpMapOfHom : (s : ℕ) → {K L : HomologicalComplex₂ C (up ℕ) (up ℕ)} →
    (f : K ⟶ L) → K.totalRowUp s ⟶ L.totalRowUp s
  | 0, _, _, f => ((HomologicalComplex.eval C (up ℕ) 0).mapHomologicalComplex (up ℕ)).map f
  | s + 1, _, _, f => HomologicalComplex.extendMap (totalRowUpMapOfHom s (rowsSuccUpMap f))
      (embeddingUpNatAdd 1)

omit [HasZeroObject C] in
/-- The projections of the total complexes onto their rows `0` are natural. -/
@[reassoc]
lemma rowZeroUpπ_naturality (f : K ⟶ L) :
    total.map f (up ℕ) ≫ L.rowZeroUpπ =
      K.rowZeroUpπ ≫ ((HomologicalComplex.eval C (up ℕ) 0).mapHomologicalComplex (up ℕ)).map f := by
  ext n : 1
  refine HomologicalComplex₂.total.hom_ext _ fun p q h ↦ ?_
  rcases q with _ | q
  · obtain rfl : p = n := by simpa using h
    simp [ιTotal_rowZeroUpπ_f_zero_assoc, XXIsoOfEq_rfl]
  · simp

/-- The projections of the total complexes of the rows `≥ s` onto their rows `s` are natural. -/
@[reassoc]
lemma totalRowsGEUpMapOfHom_totalRowUpπ (s : ℕ) (f : K ⟶ L) :
    totalRowsGEUpMapOfHom s f ≫ L.totalRowUpπ s = K.totalRowUpπ s ≫ totalRowUpMapOfHom s f := by
  induction s generalizing K L with
  | zero =>
    rw [totalRowUpπ_zero, totalRowUpπ_zero]
    exact rowZeroUpπ_naturality f
  | succ s ih =>
    rw [totalRowUpπ_succ, totalRowUpπ_succ, totalRowsGEUpMapOfHom, totalRowUpMapOfHom,
      ← HomologicalComplex.extendMap_comp, ih, HomologicalComplex.extendMap_comp]

end Preadditive

section Abelian

variable {C : Type*} [Category* C] [Abelian C] {K L : HomologicalComplex₂ C (up ℕ) (up ℕ)}
  (f : K ⟶ L)

/-- The morphism of total complexes induced by a morphism of bicomplexes respects the row
filtrations. -/
lemma factors_rowFiltrationUp (i : ℤ) :
    (L.rowFiltrationUp i).Factors ((K.rowFiltrationUp i).arrow ≫
      HomologicalComplex.extendMap (total.map f (up ℕ)) embeddingUpNat) := by
  rw [K.rowFiltrationUp_eq i _ rfl, L.rowFiltrationUp_eq i _ rfl]
  have h : (Subobject.mk (HomologicalComplex.extendMap (K.totalRowsGEUpι (-i).toNat)
      embeddingUpNat)).arrow ≫ HomologicalComplex.extendMap (total.map f (up ℕ)) embeddingUpNat =
      ((Subobject.underlyingIso _).hom ≫ HomologicalComplex.extendMap
        (totalRowsGEUpMapOfHom (-i).toNat f) embeddingUpNat ≫ (Subobject.underlyingIso _).inv) ≫
        (Subobject.mk (HomologicalComplex.extendMap (L.totalRowsGEUpι (-i).toNat)
          embeddingUpNat)).arrow := by
    rw [Category.assoc, Category.assoc, Subobject.underlyingIso_arrow,
      ← HomologicalComplex.extendMap_comp, totalRowsGEUpMapOfHom_totalRowsGEUpι,
      HomologicalComplex.extendMap_comp, ← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
  rw [h]
  exact Subobject.factors_comp_arrow _

/-- **The morphism of row-filtration spectral sequences** induced by a morphism of first-quadrant
cochain bicomplexes. -/
noncomputable def rowFiltrationUpSpectralSequenceMap :
    K.rowFiltrationUpSpectralSequence ⟶ L.rowFiltrationUpSpectralSequence :=
  Abelian.SpectralObject.spectralSequenceMap _ (CochainComplex.spectralObjectMap
    (CochainComplex.filtrationFunctorMap K.monotone_rowFiltrationUp L.monotone_rowFiltrationUp
      _ (factors_rowFiltrationUp f)))

/-- The morphism of filtration functors induced by a morphism of bicomplexes. -/
noncomputable abbrev rowFiltrationUpMap :=
  CochainComplex.filtrationFunctorMap K.monotone_rowFiltrationUp L.monotone_rowFiltrationUp
    _ (factors_rowFiltrationUp f)

/-- The identifications of the terms of the row filtrations with the total complexes of the rows
`≥ s` are natural. -/
@[reassoc]
lemma rowFiltrationUpObjIso_hom_naturality (s : ℕ) (i : ℤ) (hi : i = -s) :
    (K.rowFiltrationUpObjIso s i hi).hom ≫
        HomologicalComplex.extendMap (totalRowsGEUpMapOfHom s f) embeddingUpNat =
      (rowFiltrationUpMap f).app i ≫ (L.rowFiltrationUpObjIso s i hi).hom := by
  rw [← cancel_mono (HomologicalComplex.extendMap (L.totalRowsGEUpι s) embeddingUpNat),
    Category.assoc, Category.assoc, ← HomologicalComplex.extendMap_comp,
    totalRowsGEUpMapOfHom_totalRowsGEUpι, HomologicalComplex.extendMap_comp,
    rowFiltrationUpObjIso_hom_extendMap_totalRowsGEUpι_assoc,
    rowFiltrationUpObjIso_hom_extendMap_totalRowsGEUpι, CochainComplex.filtrationFunctorArrow]
  exact (CochainComplex.filtrationFunctorMap_app_comp _ _ i).symm

/-- The identifications of the graded pieces of the row filtrations with the rows are natural. -/
@[reassoc]
lemma rowFiltrationUpGradedIso_hom_naturality (s : ℕ) (i₁ i₂ : ℤ) (hi₁ : i₁ = -(s + 1))
    (hi₂ : i₂ = i₁ + 1) :
    cokernel.map _ _ ((rowFiltrationUpMap f).app (i₁ : EInt)) ((rowFiltrationUpMap f).app i₂)
        ((rowFiltrationUpMap f).naturality _) ≫ (L.rowFiltrationUpGradedIso s i₁ i₂ hi₁ hi₂).hom =
      (K.rowFiltrationUpGradedIso s i₁ i₂ hi₁ hi₂).hom ≫
        HomologicalComplex.extendMap (totalRowUpMapOfHom s f) embeddingUpNat := by
  rw [← cancel_epi (cokernel.π _), cokernel.π_desc_assoc, Category.assoc,
    π_rowFiltrationUpGradedIso_hom, π_rowFiltrationUpGradedIso_hom_assoc,
    ← rowFiltrationUpObjIso_hom_naturality_assoc, ← HomologicalComplex.extendMap_comp,
    totalRowsGEUpMapOfHom_totalRowUpπ, HomologicalComplex.extendMap_comp]

/-- The identifications of the cohomology of the rows placed in the degrees of the total
complexes with the cohomology of the rows are natural. -/
@[reassoc]
lemma totalRowUpHomologyIso_hom_naturality (s k : ℕ) :
    HomologicalComplex.homologyMap (totalRowUpMapOfHom s f) (k + s) ≫
        (L.totalRowUpHomologyIso s k).hom =
      (K.totalRowUpHomologyIso s k).hom ≫ HomologicalComplex.homologyMap
        (((HomologicalComplex.eval C (up ℕ) s).mapHomologicalComplex (up ℕ)).map f) k := by
  induction s generalizing K L with
  | zero =>
    rw [totalRowUpHomologyIso_zero, totalRowUpHomologyIso_zero, Iso.refl_hom, Iso.refl_hom,
      Category.comp_id, Category.id_comp]
    rfl
  | succ s ih =>
    rw [totalRowUpHomologyIso_succ, totalRowUpHomologyIso_succ, Iso.trans_hom, Iso.trans_hom]
    have h₁ := HomologicalComplex.extendHomologyIso_hom_naturality
      (totalRowUpMapOfHom s (rowsSuccUpMap f)) (embeddingUpNatAdd 1) (j := k + s)
      (j' := k + (s + 1)) rfl
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ih (rowsSuccUpMap f))).trans
        (Category.assoc _ _ _).symm)))

/-- **The morphism of row-filtration spectral sequences on the first page**: under the
identifications of the first pages with the cohomology of the rows, the morphism induced by a
morphism of bicomplexes `f` is the map induced by `f` in the cohomology of the rows. -/
@[reassoc]
theorem rowFiltrationUpSpectralSequenceMap_hom_f_firstPageXIso_hom (p : ℤ) (s k : ℕ)
    (hp : p = k + 2 * s + 1) :
    ((rowFiltrationUpSpectralSequenceMap f).hom 2 le_rfl).f (p, -((s : ℤ) + 1)) ≫
        (L.rowFiltrationUpSpectralSequenceFirstPageXIso p s k hp).hom =
      (K.rowFiltrationUpSpectralSequenceFirstPageXIso p s k hp).hom ≫
        HomologicalComplex.homologyMap
          (((HomologicalComplex.eval C (up ℕ) s).mapHomologicalComplex (up ℕ)).map f) k := by
  rw [rowFiltrationUpSpectralSequenceFirstPageXIso_eq,
    rowFiltrationUpSpectralSequenceFirstPageXIso_eq,
    rowFiltrationUpSpectralSequenceFirstPageXIsoTotalRow_eq,
    rowFiltrationUpSpectralSequenceFirstPageXIsoTotalRow_eq]
  simp only [Iso.trans_hom, Category.assoc, HomologicalComplex.homologyMapIso_hom]
  rw [rowFiltrationUpSpectralSequenceMap,
    CochainComplex.spectralSequenceMap_hom_f_spectralSequenceFirstPageXIsoCokernel_hom_assoc,
    ← HomologicalComplex.homologyMap_comp_assoc, rowFiltrationUpGradedIso_hom_naturality,
    HomologicalComplex.homologyMap_comp_assoc,
    HomologicalComplex.extendHomologyIso_hom_naturality_assoc,
    totalRowUpHomologyIso_hom_naturality]

/-- **The morphism of row-filtration spectral objects on the abutments**: through the
identifications `rowFiltrationUpAbutmentIso` of the abutments with the cohomology of the total
complexes, the morphism induced by a morphism of bicomplexes `f` is the map induced by `f` in the
cohomology of the total complexes. -/
@[reassoc]
theorem spectralObjectMap_rowFiltrationUpMap_hom_app_rowFiltrationUpAbutmentIso_hom (n : ℕ) :
    ((CochainComplex.spectralObjectMap (rowFiltrationUpMap f)).hom n).app
        (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≫
        (L.rowFiltrationUpAbutmentIso n).hom =
      (K.rowFiltrationUpAbutmentIso n).hom ≫
        HomologicalComplex.homologyMap (total.map f (up ℕ)) n := by
  rw [rowFiltrationUpAbutmentIso_eq, rowFiltrationUpAbutmentIso_eq, Iso.trans_hom, Iso.trans_hom,
    CochainComplex.spectralObjectMap_filtrationFunctorMap_hom_app_filtrationAbutmentIso_hom_assoc,
    HomologicalComplex.extendHomologyIso_hom_naturality, Category.assoc]

end Abelian

end HomologicalComplex₂
