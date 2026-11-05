/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import TauCeti.Algebra.Homology.Ext.AcyclicResolution
public import TauCeti.Algebra.Homology.SpectralSequence.Grothendieck
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Leray.Edge

/-!
# The Leray spectral sequence

Let `pb : Sheaf J Ab ⥤ Sheaf K Ab` be a left exact functor between categories of abelian sheaves
on sites `(C, J)` and `(D, K)` with an additive right adjoint `pf`, and let
`c : ℤ_K ≅ pb ℤ_J` identify the constant sheaves `ℤ`. For a morphism of sites, `pb` is the
inverse image `f⁻¹`, `pf` is the pushforward `f_*` and `c` is the canonical comparison of
constant sheaves. For an abelian sheaf `F` on `(D, K)` with an injective resolution `I`, the
Grothendieck spectral sequence of `f_*` followed by the global sections `Hom(ℤ_J, -)`
(`CategoryTheory.Sheaf.H.leraySpectralSequence`) is the **Leray spectral sequence**

  `E₂^{p,q} = Hᵖ(C, Rᵠ f_* F) ⇒ Hᵖ⁺ᵠ(D, F)`

(Stacks, Lemma 21.14.5 (0732)): its second page is
`CategoryTheory.Sheaf.H.leraySpectralSequencePageThreeXAddEquiv`, and its abutment
`CategoryTheory.Sheaf.H.leraySpectralSequenceAbutmentAddEquiv`.

Both identifications rest on `TauCeti.CategoryTheory.rightDerivedObjAddEquivExt`: the right
derived functors of an additive functor corepresented by `P` are `Ext(P, -)`. The global
sections are corepresented by `ℤ_J`, so their right derived functors are the sheaf cohomology
`H(-, n) = Extⁿ(ℤ_J, -)`, and through the adjunction and `c` the composite `Hom(ℤ_J, f_* -)` is
corepresented by `ℤ_K`.

## Indexing

The spectral sequence uses Mathlib's numbering `coreE₂Cohomological`, in which the first page is
numbered `2`, as `CategoryTheory.Functor.grothendieckSpectralSequence` does: the object
`Hᵖ(C, Rᵠ f_* F)` sits at `(q + 2p + 1, -(p + 1))` on the page numbered `3`.

## Main declarations

* `TauCeti.CategoryTheory.rightDerivedObjAddEquivExt`: `RⁿG(F) ≃ Extⁿ(P, F)` for `G`
  corepresented by `P`.
* `CategoryTheory.Sheaf.H.leraySpectralSequence`: the Leray spectral sequence.
* `CategoryTheory.Sheaf.H.leraySpectralSequencePageThreeXAddEquiv`: its second page is
  `Hᵖ(C, Rᵠ f_* F)`.
* `CategoryTheory.Sheaf.H.leraySpectralSequenceAbutmentAddEquiv`: it converges to `H(D, F)`.
* `CategoryTheory.Sheaf.H.relativeLeraySpectralSequence`,
  `CategoryTheory.Sheaf.H.relativeLeraySpectralSequencePageThreeXIso`,
  `CategoryTheory.Sheaf.H.relativeLeraySpectralSequenceAbutmentIso`: the relative form
  `Rᵖ g_* Rᵠ f_* F ⇒ Rᵖ⁺ᵠ(g ∘ f)_* F` for a composite (Stacks, Lemma 21.14.7 (0734)).
* `CategoryTheory.Sheaf.H.relativeLeraySpectralSequenceMap`,
  `CategoryTheory.Sheaf.H.relativeLeraySpectralSequenceMap_hom_f_pageThreeXIso_hom`: the relative
  form is natural in `F` from its second page on.
* `CategoryTheory.Sheaf.H.leraySpectralSequence_page_d_eq_zero`,
  `CategoryTheory.Sheaf.H.leraySpectralSequenceEInftyAddEquiv`,
  `CategoryTheory.Sheaf.H.leraySpectralSequenceEInftyAddEquivH`: when the higher direct images
  vanish, the spectral sequence degenerates at `E₂` and collapses onto its row `Hᵖ(C, f_* F)`;
  `CategoryTheory.Sheaf.H.leraySpectralSequence_id_page_d_eq_zero`: in particular for `f = 𝟙`.

## References

* [Stacks, Lemma 21.14.5 (0732)](https://stacks.math.columbia.edu/tag/0732)
* [Stacks, Lemma 21.14.7 (0734)](https://stacks.math.columbia.edu/tag/0734)
* Charles A. Weibel, *An Introduction to Homological Algebra*, Theorem 5.8.3.
-/

@[expose] public section

open CategoryTheory Limits Opposite Abelian AddCommGrpCat

universe t w w₁ w₂ v u

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [HasInjectiveResolutions C]
  {P : C} (G : C ⥤ AddCommGrpCat.{t}) [G.Additive]
  (R : (G ⋙ forget AddCommGrpCat).CorepresentableBy P)

/-- **The right derived functors of a corepresented functor are `Ext`.** If an additive functor
`G : C ⥤ Ab` is corepresented by `P`, then `RⁿG(F) ≃ Extⁿ(P, F)`, both being computed by an
injective resolution of `F`. -/
noncomputable def rightDerivedObjAddEquivExt (F : C) (n : ℕ) :
    (G.rightDerived n).obj F ≃+ Ext P F n :=
  ((injectiveResolution F).isoRightDerivedObj G n).addCommGroupIsoToAddEquiv.trans
    (extAddEquivHomologyOfResolution G R (injectiveResolution F).ι₀
      (injectiveResolution F).ι₀_comp_d (injectiveResolution F).exact_ι₀
      (injectiveResolution F).cocomplex_exactAt_succ
      (fun _ k ↦ Ext.subsingleton_of_injective _ _ k) n).symm

end TauCeti.CategoryTheory

namespace CategoryTheory.Sheaf.H

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {D : Type*} [Category* D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{w₁} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w₂} (Sheaf K AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{w})]
  {pb : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}} [PreservesFiniteLimits pb]
  {pf : Sheaf K AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w}} [pf.Additive] (adj : pb ⊣ pf)
  (c : (constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ)) ≅
    pb.obj ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))))
  {F : Sheaf K AddCommGrpCat.{w}} (I : InjectiveResolution F)

/-- The global sections `Hom(ℤ_J, -)` of abelian sheaves are corepresented by `ℤ_J`. -/
noncomputable def globalSectionsCorepresentableBy :
    (preadditiveCoyoneda.obj (op ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ)))) ⋙
      forget AddCommGrpCat).CorepresentableBy
        ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))) where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

variable (pf) in
/-- **The Leray spectral sequence** of an abelian sheaf `F` with an injective resolution `I`:
the Grothendieck spectral sequence of `f_*` followed by the global sections `Hom(ℤ_J, -)`.
Its second page is `Hᵖ(C, Rᵠ f_* F)`
(`CategoryTheory.Sheaf.H.leraySpectralSequencePageThreeXAddEquiv`), and it converges to
`H(D, F)` (`CategoryTheory.Sheaf.H.leraySpectralSequenceAbutmentAddEquiv`). -/
noncomputable abbrev leraySpectralSequence :=
  pf.grothendieckSpectralSequence
    (preadditiveCoyoneda.obj (op ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))))) I

variable (pf) in
/-- **The second page of the Leray spectral sequence**: its object at `(q + 2p + 1, -(p + 1))`
on the page numbered `3` in Mathlib's numbering is `Hᵖ(C, Rᵠ f_* F)`. -/
noncomputable def leraySpectralSequencePageThreeXAddEquiv (p q : ℕ) :
    ((leraySpectralSequence pf I).page 3).X ((q : ℤ) + 2 * p + 1, -((p : ℤ) + 1)) ≃+
      H ((pf.rightDerived q).obj F) p :=
  (pf.grothendieckSpectralSequencePageThreeXIso _ I p q).addCommGroupIsoToAddEquiv.trans
    (TauCeti.CategoryTheory.rightDerivedObjAddEquivExt _ globalSectionsCorepresentableBy _ p)

/-- Through the adjunction `pb ⊣ pf` and the comparison `c` of constant sheaves, the global
sections of the pushforward `Hom(ℤ_J, pf -)` are corepresented by `ℤ_K`. -/
noncomputable def pushforwardGlobalSectionsCorepresentableBy :
    ((pf ⋙ preadditiveCoyoneda.obj
        (op ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))))) ⋙
      forget AddCommGrpCat).CorepresentableBy
        ((constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ))) where
  homEquiv := (c.homCongr (Iso.refl _)).trans (adj.homEquiv _ _)
  homEquiv_comp g f := by
    change adj.homEquiv _ _ (c.inv ≫ (f ≫ g) ≫ 𝟙 _) =
      adj.homEquiv _ _ (c.inv ≫ f ≫ 𝟙 _) ≫ pf.map g
    rw [← Adjunction.homEquiv_naturality_right, Category.comp_id, Category.comp_id,
      Category.assoc]

/-- **The abutment of the Leray spectral sequence** is the cohomology `H(D, F)`. -/
noncomputable def leraySpectralSequenceAbutmentAddEquiv (n : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor
      (CochainComplex.mapCartanEilenberg ((pf.mapHomologicalComplex _).obj I.cocomplex)
        (preadditiveCoyoneda.obj
          (op ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ)))))).rowFiltrationUp
      (CochainComplex.mapCartanEilenberg ((pf.mapHomologicalComplex _).obj I.cocomplex)
        (preadditiveCoyoneda.obj (op ((constantSheaf J AddCommGrpCat.{w}).obj
          (of (ULift ℤ)))))).monotone_rowFiltrationUp)).abutment n ≃+ H F n :=
  (pf.grothendieckSpectralSequenceAbutmentIso _ I (fun I' _ n ↦
      have := Injective.injective_of_adjoint adj I'
      Functor.isZero_rightDerived_obj_injective_succ _ n _) n).addCommGroupIsoToAddEquiv.trans
    (TauCeti.CategoryTheory.rightDerivedObjAddEquivExt _
      (pushforwardGlobalSectionsCorepresentableBy adj c) _ n)

/-! ### Degeneration when the higher direct images vanish -/

section Degeneration

variable {I}

omit [HasExt (Sheaf J AddCommGrpCat.{w})] [HasExt (Sheaf K AddCommGrpCat.{w})] in
/-- If the higher direct images `Rᵠ f_* F` (`q > 0`) vanish, then from page `3` on the Leray
spectral sequence vanishes outside the row `E₂^{p,0} = Hᵖ(C, R⁰ f_* F)`: its object at
`(a, b)` is zero unless `a + 2b + 1 = 0`. -/
lemma isZero_leraySpectralSequence_page_X
    (hF : ∀ q : ℕ, IsZero ((pf.rightDerived (q + 1)).obj F)) (r : ℤ) (hr : 3 ≤ r)
    (pq : ℤ × ℤ) (hpq : pq.1 + 2 * pq.2 + 1 ≠ 0) :
    IsZero (((leraySpectralSequence pf I).page r).X pq) :=
  CochainComplex.isZero_cartanEilenbergSpectralSequence_page_X
    (Functor.isZero_homology_mapHomologicalComplex_succ hF) r hr pq hpq

omit [HasExt (Sheaf J AddCommGrpCat.{w})] [HasExt (Sheaf K AddCommGrpCat.{w})] in
/-- **Degeneration of the Leray spectral sequence**: if the higher direct images `Rᵠ f_* F`
(`q > 0`) vanish, all differentials of the Leray spectral sequence vanish from page `3` on. -/
lemma leraySpectralSequence_page_d_eq_zero
    (hF : ∀ q : ℕ, IsZero ((pf.rightDerived (q + 1)).obj F)) (r : ℤ) (hr : 3 ≤ r)
    (pq pq' : ℤ × ℤ) : ((leraySpectralSequence pf I).page r).d pq pq' = 0 :=
  Functor.grothendieckSpectralSequence_page_d_eq_zero hF r hr pq pq'

/-- If the higher direct images `Rᵠ f_* F` (`q > 0`) vanish, the limit object of degree `p` of
the Leray spectral sequence, at the filtration index `-(p + 1)`, is `Hᵖ(C, f_* F)`. -/
noncomputable def leraySpectralSequenceEInftyAddEquiv
    (hF : ∀ q : ℕ, IsZero ((pf.rightDerived (q + 1)).obj F)) (p : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor
      (CochainComplex.mapCartanEilenberg ((pf.mapHomologicalComplex _).obj I.cocomplex)
        (preadditiveCoyoneda.obj
          (op ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ)))))).rowFiltrationUp
      (CochainComplex.mapCartanEilenberg ((pf.mapHomologicalComplex _).obj I.cocomplex)
        (preadditiveCoyoneda.obj (op ((constantSheaf J AddCommGrpCat.{w}).obj
          (of (ULift ℤ)))))).monotone_rowFiltrationUp)).EInfty (-((p : ℤ) + 1)) p ≃+
      H (pf.obj F) p :=
  have := adj.rightAdjoint_preservesLimits
  (Functor.grothendieckSpectralSequenceEInftyIso hF p).addCommGroupIsoToAddEquiv.trans
    ((TauCeti.CategoryTheory.rightDerivedObjAddEquivExt _ globalSectionsCorepresentableBy _
      p).trans ((functorH J p).mapIso (pf.rightDerivedZeroIsoSelf.app F)).addCommGroupIsoToAddEquiv)

/-- **Collapse of the Leray spectral sequence**: if the higher direct images `Rᵠ f_* F` (`q > 0`)
vanish, the limit object of degree `n` at the filtration index `-(n + 1)` is the whole abutment
`Hⁿ(D, F)`. Together with `CategoryTheory.Sheaf.H.leraySpectralSequenceEInftyAddEquiv`, the
spectral sequence identifies `Hⁿ(C, f_* F)` with `Hⁿ(D, F)`. -/
noncomputable def leraySpectralSequenceEInftyAddEquivH
    (hF : ∀ q : ℕ, IsZero ((pf.rightDerived (q + 1)).obj F)) (n : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor
      (CochainComplex.mapCartanEilenberg ((pf.mapHomologicalComplex _).obj I.cocomplex)
        (preadditiveCoyoneda.obj
          (op ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ)))))).rowFiltrationUp
      (CochainComplex.mapCartanEilenberg ((pf.mapHomologicalComplex _).obj I.cocomplex)
        (preadditiveCoyoneda.obj (op ((constantSheaf J AddCommGrpCat.{w}).obj
          (of (ULift ℤ)))))).monotone_rowFiltrationUp)).EInfty (-((n : ℤ) + 1)) n ≃+ H F n :=
  (CochainComplex.cartanEilenbergSpectralSequenceEInftyIsoAbutment
      (Functor.isZero_homology_mapHomologicalComplex_succ hF) n).addCommGroupIsoToAddEquiv.trans
    (leraySpectralSequenceAbutmentAddEquiv adj c I n)

end Degeneration

section Identity

omit [HasExt (Sheaf J AddCommGrpCat.{w})] [HasExt (Sheaf K AddCommGrpCat.{w})] in
/-- **The Leray spectral sequence of the identity degenerates** (the check `leray_test_identity`
of the roadmap): for `f = 𝟙`, whose pushforward is exact, all differentials vanish from page `3`
on. -/
lemma leraySpectralSequence_id_page_d_eq_zero (r : ℤ) (hr : 3 ≤ r) (pq pq' : ℤ × ℤ) :
    ((leraySpectralSequence (𝟭 (Sheaf K AddCommGrpCat.{w})) I).page r).d pq pq' = 0 :=
  leraySpectralSequence_page_d_eq_zero (fun q ↦ Functor.isZero_rightDerived_succ _ F q) r hr pq pq'

end Identity

/-! ### The relative form -/

section Relative

variable {E : Type*} [Category* E] {L : GrothendieckTopology E} [HasSheafify L AddCommGrpCat.{w}]
  {pb' : Sheaf L AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w}}
  {pg : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf L AddCommGrpCat.{w}} [pg.Additive] (adj' : pb' ⊣ pg)

variable (pf pg) in
/-- **The relative Leray spectral sequence** of an abelian sheaf `F` with an injective resolution
`I`, for a composite of morphisms of sites: the Grothendieck spectral sequence of `f_*` followed
by `g_*`, with second page `Rᵖ g_* Rᵠ f_* F`
(`CategoryTheory.Sheaf.H.relativeLeraySpectralSequencePageThreeXIso`), converging to
`R•(g ∘ f)_* F` (`CategoryTheory.Sheaf.H.relativeLeraySpectralSequenceAbutmentIso`). -/
noncomputable abbrev relativeLeraySpectralSequence :=
  pf.grothendieckSpectralSequence pg I

variable (pf pg) in
/-- **The second page of the relative Leray spectral sequence**: its object at
`(q + 2p + 1, -(p + 1))` on the page numbered `3` in Mathlib's numbering is `Rᵖ g_* Rᵠ f_* F`. -/
noncomputable def relativeLeraySpectralSequencePageThreeXIso (p q : ℕ) :
    ((relativeLeraySpectralSequence pf I pg).page 3).X ((q : ℤ) + 2 * p + 1, -((p : ℤ) + 1)) ≅
      (pg.rightDerived p).obj ((pf.rightDerived q).obj F) :=
  pf.grothendieckSpectralSequencePageThreeXIso pg I p q

/-- **The abutment of the relative Leray spectral sequence** is `R•(g ∘ f)_* F`, the right
derived functors of the composite pushforward `f_* ⋙ g_*`. -/
noncomputable def relativeLeraySpectralSequenceAbutmentIso (n : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor
      (CochainComplex.mapCartanEilenberg ((pf.mapHomologicalComplex _).obj I.cocomplex)
        pg).rowFiltrationUp
      (CochainComplex.mapCartanEilenberg ((pf.mapHomologicalComplex _).obj I.cocomplex)
        pg).monotone_rowFiltrationUp)).abutment n ≅ ((pf ⋙ pg).rightDerived n).obj F :=
  have := adj'.rightAdjoint_preservesLimits
  pf.grothendieckSpectralSequenceAbutmentIso pg I (fun I' _ n ↦
    have := Injective.injective_of_adjoint adj I'
    Functor.isZero_rightDerived_obj_injective_succ _ n _) n

variable {F' : Sheaf K AddCommGrpCat.{w}} (I' : InjectiveResolution F') (u : F ⟶ F')

variable (pf pg) in
/-- The morphism of relative Leray spectral sequences induced by a morphism `u : F ⟶ F'` of
abelian sheaves, through a chain map `I ⟶ I'` lifting `u`. -/
noncomputable abbrev relativeLeraySpectralSequenceMap :
    relativeLeraySpectralSequence pf I pg ⟶ relativeLeraySpectralSequence pf I' pg :=
  pf.grothendieckSpectralSequenceMap pg I I' u

omit [HasExt (Sheaf J AddCommGrpCat.{w})] [HasExt (Sheaf K AddCommGrpCat.{w})] in
variable (pf pg) in
/-- **The relative Leray spectral sequence is natural in `F`**: under the identifications
`relativeLeraySpectralSequencePageThreeXIso` of the second pages with `Rᵖ g_* Rᵠ f_* F`, the
morphism induced by `u : F ⟶ F'` is `Rᵖ g_* Rᵠ f_* u`. -/
@[reassoc]
theorem relativeLeraySpectralSequenceMap_hom_f_pageThreeXIso_hom (p q : ℕ) :
    ((relativeLeraySpectralSequenceMap pf I pg I' u).hom 3 (by lia)).f
        ((q : ℤ) + 2 * p + 1, -((p : ℤ) + 1)) ≫
        (relativeLeraySpectralSequencePageThreeXIso pf I' pg p q).hom =
      (relativeLeraySpectralSequencePageThreeXIso pf I pg p q).hom ≫
        (pg.rightDerived p).map ((pf.rightDerived q).map u) :=
  pf.grothendieckSpectralSequenceMap_hom_f_pageThreeXIso_hom pg I I' u p q

end Relative

end CategoryTheory.Sheaf.H
