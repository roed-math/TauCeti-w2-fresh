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
`Čᵖ(U, Hᵠ(F)) = ∏ₐ Hᵠ(u (a 0) ×_V ⋯ ×_V u (a p), F)` of the cohomology presheaf of `F` and it
converges to `Hⁿ(V, F)`.

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
