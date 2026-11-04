/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import TauCeti.Algebra.Homology.ShortComplex.Limit
public import TauCeti.CategoryTheory.Sites.SheafCohomology.AcyclicResolution
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Leray

import Mathlib.Algebra.Category.Grp.AB

/-!
# The Čech double complex of a complex of abelian sheaves

Let `(C, J)` be a site with finite products, let `U : ι → C` be a family of objects and let `K` be
a cochain complex of abelian sheaves, typically an injective resolution of an abelian sheaf `F`.
Applying the Čech complex of `U` to every term of `K` gives a first-quadrant double complex
`TauCeti.CategoryTheory.cechDoubleComplex U K`, whose term in bidegree `(p, q)` is the group of
Čech `p`-cochains `Čᵖ(U, Kᵠ) = ∏ₐ Kᵠ(U (a 0) × ⋯ × U (a p))` of `Kᵠ`. It is the double complex
from which the Čech-to-cohomology spectral sequence `Ȟᵖ(U, Hᵠ(F)) ⇒ Hᵖ⁺ᵠ(F)` arises
([Stacks: Tag 03AV](https://stacks.math.columbia.edu/tag/03AV)). This file computes its two
families of one-variable cohomology groups.

* Its *rows* `Č•(U, Kᵠ)` (the Čech degree varies): when the maps `U i ⟶ T` to the terminal object
  generate a covering sieve and every `Kᵠ` is injective, the augmented row
  `0 ⟶ Kᵠ(T) ⟶ Č⁰(U, Kᵠ) ⟶ Č¹(U, Kᵠ) ⟶ ⋯` is exact
  (`TauCeti.CategoryTheory.quasiIso_cechAugmentation_of_injective`). Hence the total complex is
  quasi-isomorphic to the complex of global sections `K(T)`, whose cohomology is `H*(F)`.
* Its *columns* `Čᵖ(U, K•)` (the resolution degree varies): the column `p` is the product, over
  `a : Fin (p + 1) → ι`, of the complexes of sections of `K` over `U (a 0) × ⋯ × U (a p)`
  (`TauCeti.CategoryTheory.cechDoubleComplexXIsoPi`). Since products of abelian groups are exact,
  when `K` is a resolution of `F` by sheaves without higher cohomology on these finite products
  (for instance an injective resolution), the cohomology of the column `p` in degree `q` is the
  group of Čech `p`-cochains `∏ₐ Hᵠ(U (a 0) × ⋯ × U (a p), F)` of the cohomology presheaf
  (`TauCeti.CategoryTheory.cechDoubleComplexHomologyAddEquiv`): the first page of the spectral
  sequence.

## Main definitions

* `TauCeti.CategoryTheory.cechDoubleComplex U K`: the Čech double complex, with the Čech degree as
  its outer index.
* `TauCeti.CategoryTheory.cechDoubleComplexXIsoPi`: the column `p` is a product of complexes of
  sections.

## Main results

* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_of_injective`: for a covering family, the
  augmented Čech complex of an injective abelian sheaf is exact.
* `TauCeti.CategoryTheory.cechDoubleComplexHomologyAddEquiv`: the cohomology of the column `p` of
  the Čech double complex of an acyclic resolution of `F` is `∏ₐ Hᵠ(U (a 0) × ⋯ × U (a p), F)`.

## References

* [Stacks: Tag 03AV](https://stacks.math.columbia.edu/tag/03AV), Section 21.10 on Čech cohomology
  and cohomology, for the Čech double complex of an injective resolution and the spectral
  sequence it gives.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {J : GrothendieckTopology C}
  {ι : Type v} (U : ι → C)

/-! ### Rows: Čech complexes of injective sheaves -/

section Rows

variable [HasSheafify J AddCommGrpCat.{v}] {T : C} (hT : IsTerminal T)
  (hU : Sieve.ofArrows U (fun i ↦ hT.from (U i)) ∈ J T)

include hU in
/-- **The augmented Čech complex of an injective sheaf is exact.** If the maps `U i ⟶ T` to the
terminal object generate a covering sieve and `I` is an injective abelian sheaf, then
`0 ⟶ I(T) ⟶ Č⁰(U, I) ⟶ Č¹(U, I) ⟶ ⋯` is exact: in degree `0` by the sheaf condition, in positive
degrees by `exactAt_cechComplexFunctor_obj_obj_of_injective`. -/
@[stacks 03AV "The vanishing of the higher Čech cohomology of an injective sheaf."]
theorem quasiIso_cechAugmentation_of_injective (I : Sheaf J AddCommGrpCat.{v}) [Injective I] :
    QuasiIso (cechAugmentation U hT I.obj) :=
  (quasiIso_cechAugmentation_iff U hT I.obj).2
    ⟨isSheafFor_ofArrows_of_mem U hT hU I, exactAt_cechComplexFunctor_obj_obj_of_injective U I⟩

end Rows

/-! ### The Čech double complex -/

/-- The **Čech double complex** of a cochain complex `K` of abelian sheaves for a family `U`: its
term in bidegree `(p, q)` is the group `Čᵖ(U, Kᵠ)` of Čech `p`-cochains of `Kᵠ`, its horizontal
differentials are the Čech differentials and its vertical differentials are induced by those of
`K`. The outer index is the Čech degree `p`, so that `(cechDoubleComplex U K).flip.X q` is the Čech
complex `Č(U, Kᵠ)` and `(cechDoubleComplex U K).X p` is the column of `p`-cochains. -/
@[expose] def cechDoubleComplex (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) :
    HomologicalComplex₂ AddCommGrpCat.{v} (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  HomologicalComplex₂.flip (((sheafToPresheaf J AddCommGrpCat.{v} ⋙
    cechComplexFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)

variable (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ)

/-- The horizontal differentials of the Čech double complex are the Čech differentials. -/
lemma cechDoubleComplex_d_f (p p' q : ℕ) :
    ((cechDoubleComplex U K).d p p').f q = ((cechComplexFunctor U).obj (K.X q).obj).d p p' :=
  rfl

/-- The vertical differentials of the Čech double complex are induced by those of `K`. -/
lemma cechDoubleComplex_X_d (p q q' : ℕ) :
    ((cechDoubleComplex U K).X p).d q q' = ((cechComplexFunctor U).map (K.d q q').hom).f p :=
  rfl

/-! ### Columns: products of complexes of sections -/

/-- The complex of sections over `W` of a cochain complex of abelian sheaves. -/
abbrev sectionsComplex (W : C) : CochainComplex AddCommGrpCat.{v} ℕ :=
  ((sheafToPresheaf J AddCommGrpCat.{v} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op W)).mapHomologicalComplex _).obj K

/-- The column `p` of the Čech double complex is the product, over `a : Fin (p + 1) → ι`, of the
complexes of sections of `K` over `U (a 0) × ⋯ × U (a p)`. -/
def cechDoubleComplexXIsoPi (p : ℕ) :
    (cechDoubleComplex U K).X p ≅
      ∏ᶜ fun a : Fin (p + 1) → ι ↦ sectionsComplex K (∏ᶜ fun j ↦ U (a j)) :=
  (HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ PreservesProduct.iso (HomologicalComplex.eval _ _ q)
      fun a : Fin (p + 1) → ι ↦ sectionsComplex K (∏ᶜ fun j ↦ U (a j))) fun q q' _ ↦
    Pi.hom_ext _ _ fun a ↦ by
      have h := cechComplexFunctor_map_f_π U (K.X q).obj (K.d q q').hom p a
      have h₁ := piComparison_comp_π (HomologicalComplex.eval _ _ q)
        (fun a : Fin (p + 1) → ι ↦ sectionsComplex K (∏ᶜ fun j ↦ U (a j))) a
      have h₂ := piComparison_comp_π (HomologicalComplex.eval _ _ q')
        (fun a : Fin (p + 1) → ι ↦ sectionsComplex K (∏ᶜ fun j ↦ U (a j))) a
      exact (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) h).trans <|
        (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h₁).trans <|
          (HomologicalComplex.Hom.comm (Pi.π (fun a : Fin (p + 1) → ι ↦
            sectionsComplex K (∏ᶜ fun j ↦ U (a j))) a) q q').trans <|
              (congrArg (_ ≫ ·) h₂.symm).trans
            (Category.assoc _ _ _).symm).symm

/-- Under `cechDoubleComplexXIsoPi`, the projection of a product of complexes of sections to its
factor `a` is the projection of the Čech cochains to the factor `a`. -/
@[reassoc (attr := simp)]
lemma cechDoubleComplexXIsoPi_inv_f_π (p q : ℕ) (a : Fin (p + 1) → ι) :
    (cechDoubleComplexXIsoPi U K p).inv.f q ≫
        Pi.π (fun a : Fin (p + 1) → ι ↦ (K.X q).obj.obj (op (∏ᶜ fun j ↦ U (a j)))) a =
      (Pi.π (fun a : Fin (p + 1) → ι ↦ sectionsComplex K (∏ᶜ fun j ↦ U (a j))) a).f q :=
  piComparison_comp_π (HomologicalComplex.eval _ _ q) _ a

/-- The cohomology of the column `p` of the Čech double complex is the product, over
`a : Fin (p + 1) → ι`, of the cohomology of the complexes of sections of `K` over
`U (a 0) × ⋯ × U (a p)`: products of abelian groups are exact. -/
def cechDoubleComplexHomologyIsoPi (p q : ℕ) :
    ((cechDoubleComplex U K).X p).homology q ≅
      ∏ᶜ fun a : Fin (p + 1) → ι ↦ (sectionsComplex K (∏ᶜ fun j ↦ U (a j))).homology q :=
  (HomologicalComplex.homologyFunctor _ _ q).mapIso (cechDoubleComplexXIsoPi U K p) ≪≫
    PreservesProduct.iso (HomologicalComplex.homologyFunctor _ _ q) _

section Resolution

variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
  {F : Sheaf J AddCommGrpCat.{v}} {K} (ε : F ⟶ K.X 0) [Mono ε] (hε : ε ≫ K.d 0 1 = 0)
  (hε' : (ShortComplex.mk ε (K.d 0 1) hε).Exact) (hK : ∀ j, K.ExactAt (j + 1))
  (hKU : ∀ (m : ℕ) (a : Fin (m + 1) → ι) j k,
    Subsingleton ((K.X j).H' (k + 1) (∏ᶜ fun i ↦ U (a i))))

/-- **The first page of the Čech-to-cohomology spectral sequence.** Let `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯`
be a resolution of an abelian sheaf `F` whose terms have no cohomology in positive degrees on the
finite products of members of `U` (for instance an injective resolution). Then the cohomology in
degree `q` of the column `p` of the Čech double complex of `K` is the group
`∏ₐ Hᵠ(U (a 0) × ⋯ × U (a p), F)` of Čech `p`-cochains of the presheaf `Hᵠ(-, F)`. -/
@[stacks 03AV "The first page of the Čech-to-cohomology spectral sequence."]
def cechDoubleComplexHomologyAddEquiv (p q : ℕ) :
    ((cechDoubleComplex U K).X p).homology q ≃+
      ∀ a : Fin (p + 1) → ι, F.H' q (∏ᶜ fun j ↦ U (a j)) :=
  (cechDoubleComplexHomologyIsoPi U K p q ≪≫ (limit.isLimit _).conePointUniqueUpToIso
    (AddCommGrpCat.HasLimit.productLimitCone _).isLimit).addCommGroupIsoToAddEquiv.trans
    (AddEquiv.piCongrRight fun a ↦
      (Sheaf.H'.addEquivHomologyOfResolution ε hε hε' hK _ (hKU p a) q).symm)

end Resolution

end TauCeti.CategoryTheory
