/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.CartanEilenberg

/-!
# The Grothendieck spectral sequence

Let `F : C ⥤ D` and `G : D ⥤ E` be additive functors between abelian categories with enough
injectives (for `C` and `D`), with `G` left exact, such that `F` sends injective objects to
`G`-acyclic objects. For an injective resolution `I` of an object `X` of `C`, the
Cartan–Eilenberg spectral sequence of `G` at the complex `F(I)`
(`CategoryTheory.Functor.grothendieckSpectralSequence`) is the **Grothendieck spectral
sequence**

  `E₂^{s,k} = RˢG(RᵏF(X)) ⇒ Rˢ⁺ᵏ(F ⋙ G)(X)`.

Its second page is computed by `CochainComplex.cartanEilenbergSpectralSequencePageThreeXIso`,
since the cohomology of `F(I)` is `R•F(X)`, and its abutment by
`CochainComplex.cartanEilenbergSpectralSequenceAbutmentIso`, since the terms of `F(I)` are
`G`-acyclic and `G(F(I))` computes `R•(F ⋙ G)(X)`.

## Indexing

As for `CochainComplex.cartanEilenbergSpectralSequence`, the spectral sequence uses Mathlib's
numbering `coreE₂Cohomological`, in which the first page is numbered `2`: the object
`RˢG(RᵏF(X))` sits at `(k + 2s + 1, -(s + 1))` on the page numbered `3`.

## Main definitions and results

* `CategoryTheory.Functor.grothendieckSpectralSequence`: the Grothendieck spectral sequence.
* `CategoryTheory.Functor.grothendieckSpectralSequencePageThreeXIso`: its second page is
  `RˢG(RᵏF(X))`.
* `CategoryTheory.Functor.grothendieckSpectralSequenceAbutmentIso`: it converges to
  `R•(F ⋙ G)(X)`.
* `CategoryTheory.Functor.grothendieckSpectralSequence_page_d_eq_zero`,
  `CategoryTheory.Functor.grothendieckSpectralSequenceEInftyIso`: at an `F`-acyclic object `X`
  the spectral sequence degenerates at `E₂`, and its abutment of degree `s` is
  `E₂^{s,0} = RˢG(R⁰F(X))`.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Theorem 5.8.3.
* [Stacks, Lemma 13.22.2 (015N)](https://stacks.math.columbia.edu/tag/015N)
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category* C] [Abelian C] [HasInjectiveResolutions C] [Category* D]
  [Abelian D] [HasInjectiveResolutions D] [Category* E] [Abelian E] (F : C ⥤ D) [F.Additive]
  (G : D ⥤ E) [G.Additive] {X : C} (I : InjectiveResolution X)

/-- **The Grothendieck spectral sequence** of `F ⋙ G` at an object `X` with an injective
resolution `I`: the Cartan–Eilenberg spectral sequence of `G` at the complex `F(I)`. Its second
page is `RˢG(RᵏF(X))` (`CategoryTheory.Functor.grothendieckSpectralSequencePageThreeXIso`), and
when `G` is left exact and `F` sends injective objects to `G`-acyclic objects it converges to
`R•(F ⋙ G)(X)` (`CategoryTheory.Functor.grothendieckSpectralSequenceAbutmentIso`). -/
noncomputable abbrev grothendieckSpectralSequence :=
  CochainComplex.cartanEilenbergSpectralSequence ((F.mapHomologicalComplex _).obj I.cocomplex) G

/-- **The second page of the Grothendieck spectral sequence**: its object at
`(k + 2s + 1, -(s + 1))` on the page numbered `3` in Mathlib's numbering is `RˢG(RᵏF(X))`. -/
noncomputable def grothendieckSpectralSequencePageThreeXIso (s k : ℕ) :
    ((F.grothendieckSpectralSequence G I).page 3).X ((k : ℤ) + 2 * s + 1, -((s : ℤ) + 1)) ≅
      (G.rightDerived s).obj ((F.rightDerived k).obj X) :=
  CochainComplex.cartanEilenbergSpectralSequencePageThreeXIso
      ((F.mapHomologicalComplex _).obj I.cocomplex) G s k ≪≫
    (G.rightDerived s).mapIso (I.isoRightDerivedObj F k).symm

/-- **The abutment of the Grothendieck spectral sequence**: if `G` is left exact and `F` sends
injective objects to `G`-acyclic objects, the spectral sequence converges to `R•(F ⋙ G)(X)`. -/
noncomputable def grothendieckSpectralSequenceAbutmentIso [PreservesFiniteLimits G]
    (hF : ∀ (J : C) [Injective J] (n : ℕ), IsZero ((G.rightDerived (n + 1)).obj (F.obj J)))
    (n : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor
      (CochainComplex.mapCartanEilenberg ((F.mapHomologicalComplex _).obj I.cocomplex)
        G).rowFiltrationUp (CochainComplex.mapCartanEilenberg
          ((F.mapHomologicalComplex _).obj I.cocomplex) G).monotone_rowFiltrationUp)).abutment n ≅
      ((F ⋙ G).rightDerived n).obj X :=
  CochainComplex.cartanEilenbergSpectralSequenceAbutmentIso
      ((F.mapHomologicalComplex _).obj I.cocomplex) G (fun q n ↦ hF (I.cocomplex.X q) n) n ≪≫
    HomologicalComplex.homologyMapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) _).app I.cocomplex) n ≪≫
    (I.isoRightDerivedObj (F ⋙ G) n).symm

/-! ### Degeneration at an `F`-acyclic object -/

section Degeneration

variable {F G I}

omit [HasInjectiveResolutions D] in
/-- At an `F`-acyclic object, the cohomology of `F(I)` is concentrated in degree `0`. -/
lemma isZero_homology_mapHomologicalComplex_succ
    (hX : ∀ k : ℕ, IsZero ((F.rightDerived (k + 1)).obj X)) (k : ℕ) :
    IsZero (((F.mapHomologicalComplex _).obj I.cocomplex).homology (k + 1)) :=
  (hX k).of_iso (I.isoRightDerivedObj F (k + 1)).symm

/-- **Degeneration of the Grothendieck spectral sequence** at an `F`-acyclic object: all its
differentials vanish from page `3` on. -/
lemma grothendieckSpectralSequence_page_d_eq_zero
    (hX : ∀ k : ℕ, IsZero ((F.rightDerived (k + 1)).obj X)) (r : ℤ) (hr : 3 ≤ r)
    (pq pq' : ℤ × ℤ) : ((F.grothendieckSpectralSequence G I).page r).d pq pq' = 0 :=
  CochainComplex.cartanEilenbergSpectralSequence_page_d_eq_zero
    (isZero_homology_mapHomologicalComplex_succ hX) r hr pq pq'

/-- **The Grothendieck spectral sequence of an `F`-acyclic object collapses**: its limit object
of degree `s` at the filtration index `-(s + 1)` is `E₂^{s,0} = RˢG(R⁰F(X))`, and it is the whole
abutment (`CochainComplex.cartanEilenbergSpectralSequenceEInftyIsoAbutment`). -/
noncomputable def grothendieckSpectralSequenceEInftyIso
    (hX : ∀ k : ℕ, IsZero ((F.rightDerived (k + 1)).obj X)) (s : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor
      (CochainComplex.mapCartanEilenberg ((F.mapHomologicalComplex _).obj I.cocomplex)
        G).rowFiltrationUp (CochainComplex.mapCartanEilenberg
          ((F.mapHomologicalComplex _).obj I.cocomplex) G).monotone_rowFiltrationUp)).EInfty
        (-((s : ℤ) + 1)) s ≅
      (G.rightDerived s).obj ((F.rightDerived 0).obj X) :=
  CochainComplex.cartanEilenbergSpectralSequenceEInftyIso
      (isZero_homology_mapHomologicalComplex_succ hX) s ≪≫
    (G.rightDerived s).mapIso (I.isoRightDerivedObj F 0).symm

end Degeneration

end CategoryTheory.Functor
