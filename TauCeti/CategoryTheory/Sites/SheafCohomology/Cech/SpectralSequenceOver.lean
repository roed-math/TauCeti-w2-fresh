/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.SpectralSequence
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Over

/-!
# The Čech-to-cohomology spectral sequence of a covering of an object

Let `(C, J)` be a site, `V : C`, and `f i : u i ⟶ V` a family of morphisms generating a covering
sieve of `V`. On the localized site `J.over V`, the objects `Over.mk (f i)` cover the terminal
object `Over.mk (𝟙 V)`, so the Čech-to-cohomology spectral sequence of
`TauCeti.CategoryTheory.cechToCohomologySpectralSequence` applies to the restriction of an
injective resolution `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` of an abelian sheaf `F` on `C`. When restriction to
`J.over V` and its left adjoint are exact, its first page is the group of Čech cochains
`Čᵖ(U, Hᵠ(F)) = ∏ₐ Hᵠ(u (a 0) ×_V ⋯ ×_V u (a p), F)` of the cohomology presheaf of `F`, its
differential is `(-1)ᵠ` times the Čech differential, and it converges to `Hⁿ(V, F)`.

## Main definitions

* `TauCeti.CategoryTheory.cechToCohomologyOverSpectralSequence f K`: the Čech-to-cohomology
  spectral sequence of the family `f`.
* `TauCeti.CategoryTheory.cechToCohomologyOverSpectralSequenceFirstPageAddEquiv`: its first page is
  `∏ₐ Hᵠ(u (a 0) ×_V ⋯ ×_V u (a p), F)`.
* `TauCeti.CategoryTheory.cechToCohomologyOverAbutmentAddEquiv`: its abutment is `Hⁿ(V, F)`.

## Main results

* `TauCeti.CategoryTheory.ofArrows_mem_over_iff`: the family `Over.mk (f i)` covers the terminal
  object of `J.over V` if and only if the family `f` covers `V`.
* `TauCeti.CategoryTheory.injective_overPullback_obj`: restriction to `J.over V` preserves
  injective abelian sheaves.
* `TauCeti.CategoryTheory.cechToCohomologyOverSpectralSequenceFirstPageAddEquiv_d`: the
  differential of the first page is `(-1)ᵠ` times the Čech differential of `Hᵠ(-, F)`, so that the
  second page is `Ȟᵖ(U, Hᵠ(F))`.

## References

* [Stacks: Tag 03AV](https://stacks.math.columbia.edu/tag/03AV), Section 21.10 on Čech cohomology
  and cohomology.
-/

public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {V : C} {ι : Type v}
  {u : ι → C} (f : ∀ i, u i ⟶ V)

/-- The objects `Over.mk (f i)` of the localized site `J.over V` cover its terminal object
`Over.mk (𝟙 V)` if and only if the morphisms `f i : u i ⟶ V` cover `V`. -/
theorem ofArrows_mem_over_iff :
    Sieve.ofArrows (fun i ↦ Over.mk (f i)) (fun i ↦ Over.mkIdTerminal.from (Over.mk (f i))) ∈
      J.over V (Over.mk (𝟙 V)) ↔ Sieve.ofArrows u f ∈ J V := by
  have h (i : ι) : (Over.mkIdTerminal.from (Over.mk (f i))).left = f i := by simp
  rw [J.mem_over_iff, Sieve.overEquiv_ofArrows]
  simp only [Over.mk_left, h]

/-- Restriction of abelian sheaves to the localized site `J.over V` preserves injective objects
when its left adjoint, extension to the ambient site, preserves finite limits. -/
theorem injective_overPullback_obj [(J.overPullback AddCommGrpCat.{v} V).IsRightAdjoint]
    [PreservesFiniteLimits ((Over.forget V).sheafPullback AddCommGrpCat.{v} (J.over V) J)]
    (I : Sheaf J AddCommGrpCat.{v}) [Injective I] :
    Injective ((J.overPullback AddCommGrpCat.{v} V).obj I) :=
  ((Over.forget V).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over V) J).map_injective I
    inferInstance

/-- Restriction to the localized site `J.over V` preserves the exactness of a cochain complex of
abelian sheaves in positive degrees. -/
private theorem exactAt_overPullback [(J.overPullback AddCommGrpCat.{v} V).IsRightAdjoint]
    [PreservesFiniteColimits (J.overPullback AddCommGrpCat.{v} V)]
    {K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ} (hK : ∀ j, K.ExactAt (j + 1)) (j : ℕ) :
    (((J.overPullback AddCommGrpCat.{v} V).mapHomologicalComplex _).obj K).ExactAt (j + 1) := by
  have h := hK j
  rw [HomologicalComplex.exactAt_iff] at h ⊢
  exact h.map (J.overPullback AddCommGrpCat.{v} V)

variable [HasFiniteProducts (Over V)] (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ)

/-- The **Čech-to-cohomology spectral sequence** of a family of morphisms `f i : u i ⟶ V` with
coefficients in a cochain complex `K` of abelian sheaves: the Čech-to-cohomology spectral sequence
of the family `Over.mk (f i)` on the localized site `J.over V`, with coefficients in the restriction
of `K`. For an injective resolution `K` of an abelian sheaf `F` and a covering family `f`, it goes
from `Čᵖ(U, Hᵠ(F))` to `Hᵖ⁺ᵠ(V, F)`. -/
abbrev cechToCohomologyOverSpectralSequence :=
  cechToCohomologySpectralSequence (fun i ↦ Over.mk (f i))
    (((J.overPullback AddCommGrpCat.{v} V).mapHomologicalComplex _).obj K)

/-- The spectral object whose abutment is the target of
`TauCeti.CategoryTheory.cechToCohomologyOverSpectralSequence`. -/
abbrev cechToCohomologyOverSpectralObject :=
  cechToCohomologySpectralObject (fun i ↦ Over.mk (f i))
    (((J.overPullback AddCommGrpCat.{v} V).mapHomologicalComplex _).obj K)

variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
  [HasSheafify (J.over V) AddCommGrpCat.{v}] [HasExt.{v} (Sheaf (J.over V) AddCommGrpCat.{v})]
  [(J.overPullback AddCommGrpCat.{v} V).IsRightAdjoint]
  [PreservesFiniteColimits (J.overPullback AddCommGrpCat.{v} V)]
  [PreservesFiniteLimits ((Over.forget V).sheafPullback AddCommGrpCat.{v} (J.over V) J)]
  {F : Sheaf J AddCommGrpCat.{v}} {K} (ε : F ⟶ K.X 0) [Mono ε] (hε : ε ≫ K.d 0 1 = 0)
  (hε' : (ShortComplex.mk ε (K.d 0 1) hε).Exact) (hK : ∀ j, K.ExactAt (j + 1))
  [∀ q, Injective (K.X q)]

/-- **The first page of the Čech-to-cohomology spectral sequence of a covering.** For an injective
resolution `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` of an abelian sheaf `F` and a family `f i : u i ⟶ V`, the object
of the first page at `(q + 2p + 1, -(p + 1))` is the group
`∏ₐ Hᵠ(u (a 0) ×_V ⋯ ×_V u (a p), F)` of Čech `p`-cochains of the cohomology presheaf `Hᵠ(-, F)`,
the fibre products being the products of the objects `Over.mk (f i)` of `Over V`. -/
@[stacks 03AV "The first page of the Čech-to-cohomology spectral sequence."]
def cechToCohomologyOverSpectralSequenceFirstPageAddEquiv (p q : ℕ) :
    ((cechToCohomologyOverSpectralSequence f K).page 2).X
        ((q : ℤ) + 2 * p + 1, -((p : ℤ) + 1)) ≃+
      ∀ a : Fin (p + 1) → ι, F.H' q (∏ᶜ fun j ↦ Over.mk (f (a j))).left :=
  have (q : ℕ) : Injective
      ((((J.overPullback AddCommGrpCat.{v} V).mapHomologicalComplex _).obj K).X q) :=
    injective_overPullback_obj (K.X q)
  (cechToCohomologySpectralSequenceFirstPageAddEquiv (fun i ↦ Over.mk (f i))
    ((J.overPullback AddCommGrpCat.{v} V).map ε) _ (hε'.map _)
    (exactAt_overPullback hK)
    (fun _ _ _ k ↦ Abelian.Ext.subsingleton_of_injective _ _ k) p q).trans
    (AddEquiv.piCongrRight fun a ↦ (F.cohomologyPresheafObjIsoOverH' q
      (∏ᶜ fun j ↦ Over.mk (f (a j)))).symm.addCommGroupIsoToAddEquiv)

/-- **The first differential of the Čech-to-cohomology spectral sequence of a covering is the Čech
differential** of the cohomology presheaf `Hᵠ(-, F)`, up to the sign `(-1)ᵠ`: under
`cechToCohomologyOverSpectralSequenceFirstPageAddEquiv`, the differential from the Čech
`p`-cochains to the Čech `(p + 1)`-cochains of `Hᵠ(-, F)` sends `c` to `(-1)ᵠ δc`, where `(δc)(b)`
is the alternating sum of the restrictions of the `c (b ∘ m.succAbove)` along the projections
`u (b 0) ×_V ⋯ ×_V u (b (p + 1)) ⟶ u (b 0) ×_V ⋯ (omitting m) ⋯ ×_V u (b (p + 1))`. Hence the
second page is the Čech cohomology `Ȟᵖ(U, Hᵠ(F))` of the covering. -/
@[stacks 03AV "The differential of the first page of the Čech-to-cohomology spectral sequence."]
theorem cechToCohomologyOverSpectralSequenceFirstPageAddEquiv_d (p q : ℕ)
    (x : ((cechToCohomologyOverSpectralSequence f K).page 2).X
      ((q : ℤ) + 2 * p + 1, -((p : ℤ) + 1)))
    (b : Fin (p + 2) → ι) :
    cechToCohomologyOverSpectralSequenceFirstPageAddEquiv f ε hε hε' hK (p + 1) q
        (((cechToCohomologyOverSpectralSequence f K).page 2).d
          ((q : ℤ) + 2 * p + 1, -((p : ℤ) + 1))
          ((q : ℤ) + 2 * (p + 1 : ℕ) + 1, -(((p + 1 : ℕ) : ℤ) + 1)) x) b =
      (-1 : ℤ) ^ q • ∑ m : Fin (p + 2), (-1 : ℤ) ^ (m : ℕ) • (F.cohomologyPresheaf q).map
        (Pi.lift fun y ↦ Pi.π (fun j ↦ Over.mk (f (b j))) (m.succAbove y)).left.op
          (cechToCohomologyOverSpectralSequenceFirstPageAddEquiv f ε hε hε' hK p q x
            (b ∘ m.succAbove)) := by
  have (q : ℕ) : Injective
      ((((J.overPullback AddCommGrpCat.{v} V).mapHomologicalComplex _).obj K).X q) :=
    injective_overPullback_obj (K.X q)
  have hd := cechToCohomologySpectralSequenceFirstPageAddEquiv_d (fun i ↦ Over.mk (f i))
    ((J.overPullback AddCommGrpCat.{v} V).map ε) _ (hε'.map _) (exactAt_overPullback hK)
    (fun _ _ _ k ↦ Abelian.Ext.subsingleton_of_injective _ _ k) p q x b
  have h (m : Fin (p + 2)) := ConcreteCategory.congr_hom
    (F.cohomologyPresheafObjIsoOverH'_inv_naturality q
      (Pi.lift fun y ↦ Pi.π (fun j ↦ Over.mk (f (b j))) (m.succAbove y)))
  simp only [ConcreteCategory.comp_apply] at h
  simp only [cechToCohomologyOverSpectralSequenceFirstPageAddEquiv, AddEquiv.trans_apply,
    AddEquiv.piCongrRight_apply]
  rw [hd]
  simp only [Iso.addCommGroupIsoToAddEquiv_apply, Iso.symm_hom, map_zsmul, map_sum, h]
  -- The two sides differ only in `b ∘ m.succAbove` and the coercion of morphisms of groups.
  rfl

/-- **The abutment of the Čech-to-cohomology spectral sequence of a covering.** For an injective
resolution `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` of an abelian sheaf `F` and a family `f i : u i ⟶ V` generating
a covering sieve of `V`, the abutment of the spectral sequence in degree `n` is the sheaf
cohomology `Hⁿ(V, F)`. -/
@[stacks 03AV "The abutment of the Čech-to-cohomology spectral sequence."]
def cechToCohomologyOverAbutmentAddEquiv (hU : Sieve.ofArrows u f ∈ J V) (n : ℕ) :
    (cechToCohomologyOverSpectralObject f K).abutment n ≃+ F.H' n V :=
  have (q : ℕ) : Injective
      ((((J.overPullback AddCommGrpCat.{v} V).mapHomologicalComplex _).obj K).X q) :=
    injective_overPullback_obj (K.X q)
  (cechToCohomologyAbutmentAddEquiv (fun i ↦ Over.mk (f i))
    ((J.overPullback AddCommGrpCat.{v} V).map ε) _ (hε'.map _)
    (exactAt_overPullback hK) Over.mkIdTerminal
    ((ofArrows_mem_over_iff f).2 hU) n).trans
    (F.cohomologyPresheafObjIsoOverH' n (Over.mk (𝟙 V))).symm.addCommGroupIsoToAddEquiv

end TauCeti.CategoryTheory
