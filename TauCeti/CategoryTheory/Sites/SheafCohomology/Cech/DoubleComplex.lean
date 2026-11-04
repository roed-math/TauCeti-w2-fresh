/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import TauCeti.Algebra.Homology.TotalComplex.UpNat
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
  quasi-isomorphic to the complex of global sections `K(T)`
  (`TauCeti.CategoryTheory.quasiIso_totalCoaugmentation_cechDoubleComplex`), and for an injective
  resolution of `F` its cohomology is `H*(T, F)`
  (`TauCeti.CategoryTheory.homologyTotalCechDoubleComplexAddEquiv`): the abutment of the spectral
  sequence.
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
* `TauCeti.CategoryTheory.cechDoubleComplexCoaugmentation`: the coaugmentation of the column `0` by
  the sections over the terminal object.

## Main results

* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_of_injective`: for a covering family, the
  augmented Čech complex of an injective abelian sheaf is exact.
* `TauCeti.CategoryTheory.cechDoubleComplexHomologyAddEquiv`: the cohomology of the column `p` of
  the Čech double complex of an acyclic resolution of `F` is `∏ₐ Hᵠ(U (a 0) × ⋯ × U (a p), F)`.
* `TauCeti.CategoryTheory.cechDoubleComplexHomologyAddEquiv_homologyMap_d`: under this
  identification, the horizontal differentials induce the Čech differential of the cohomology
  presheaf `Hᵠ(-, F)`.
* `TauCeti.CategoryTheory.quasiIso_totalCoaugmentation_cechDoubleComplex`: for a covering family
  and a complex of injective sheaves, the total complex is quasi-isomorphic to the sections over the
  terminal object.
* `TauCeti.CategoryTheory.homologyTotalCechDoubleComplexAddEquiv`: for an injective resolution of
  `F`, the cohomology of the total complex is `Hⁿ(T, F)`.

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
@[reassoc, simp]
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

/-- The restriction `K(W) ⟶ K(W')` of complexes of sections along `f : W' ⟶ W`. -/
abbrev sectionsComplexMap {W W' : C} (f : W' ⟶ W) : sectionsComplex K W ⟶ sectionsComplex K W' :=
  (NatTrans.mapHomologicalComplex (Functor.whiskerLeft (sheafToPresheaf J AddCommGrpCat.{v})
    ((evaluation Cᵒᵖ AddCommGrpCat.{v}).map f.op)) _).app K

/-- Under `cechDoubleComplexXIsoPi`, the projection of the Čech cochains to the factor `a` is the
projection of a product of complexes of sections to its factor `a`. -/
@[reassoc]
lemma cechDoubleComplexXIsoPi_hom_f_π_f (p q : ℕ) (a : Fin (p + 1) → ι) :
    (cechDoubleComplexXIsoPi U K p).hom.f q ≫
        (Pi.π (fun a : Fin (p + 1) → ι ↦ sectionsComplex K (∏ᶜ fun j ↦ U (a j))) a).f q =
      Pi.π (fun a : Fin (p + 1) → ι ↦ (K.X q).obj.obj (op (∏ᶜ fun j ↦ U (a j)))) a := by
  have h : (cechDoubleComplexXIsoPi U K p).hom.f q ≫ (cechDoubleComplexXIsoPi U K p).inv.f q =
      𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
  rw [← cechDoubleComplexXIsoPi_inv_f_π]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans (Category.id_comp _))

/-- The factor `b` of the horizontal differential of the Čech double complex, read on products of
complexes of sections, is the alternating sum of the restrictions along the face maps
`U (b 0) × ⋯ × U (b (p + 1)) ⟶ ∏ⱼ U (b (m.succAbove j))`. -/
lemma cechDoubleComplex_d_comp_XIsoPi_hom_π (p : ℕ) (b : Fin (p + 2) → ι) :
    (cechDoubleComplex U K).d p (p + 1) ≫ (cechDoubleComplexXIsoPi U K (p + 1)).hom ≫
        Pi.π (fun a : Fin (p + 2) → ι ↦ sectionsComplex K (∏ᶜ fun j ↦ U (a j))) b =
      ∑ m : Fin (p + 2), (-1 : ℤ) ^ (m : ℕ) • ((cechDoubleComplexXIsoPi U K p).hom ≫
        Pi.π (fun a : Fin (p + 1) → ι ↦ sectionsComplex K (∏ᶜ fun j ↦ U (a j)))
          (b ∘ m.succAbove) ≫
        sectionsComplexMap K (Pi.lift fun x ↦ Pi.π (fun j ↦ U (b j)) (m.succAbove x))) := by
  ext q : 1
  simp only [← HomologicalComplex.eval_map, Functor.map_sum, Functor.map_zsmul]
  simp only [HomologicalComplex.eval_map, HomologicalComplex.comp_f,
    cechDoubleComplexXIsoPi_hom_f_π_f, cechDoubleComplexXIsoPi_hom_f_π_f_assoc,
    cechDoubleComplex_d_f]
  exact cechComplexFunctor_obj_d_comp_π U (K.X q).obj p b

/-- The cohomology of the column `p` of the Čech double complex, followed by the projection to the
factor `a`, is the map induced by the projection of the Čech cochains to the factor `a`. -/
@[reassoc]
lemma cechDoubleComplexHomologyIsoPi_hom_π (p q : ℕ) (a : Fin (p + 1) → ι) :
    (cechDoubleComplexHomologyIsoPi U K p q).hom ≫
        Pi.π (fun a : Fin (p + 1) → ι ↦ (sectionsComplex K (∏ᶜ fun j ↦ U (a j))).homology q) a =
      HomologicalComplex.homologyMap ((cechDoubleComplexXIsoPi U K p).hom ≫
        Pi.π (fun a : Fin (p + 1) → ι ↦ sectionsComplex K (∏ᶜ fun j ↦ U (a j))) a) q :=
  -- `cechDoubleComplexHomologyIsoPi` is stated with `homology` rather than the objects of
  -- `homologyFunctor`, so `rw [Iso.trans_hom]` sees an ill-typed motive; the composite is
  -- unfolded by the term instead.
  (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
    (piComparison_comp_π (HomologicalComplex.homologyFunctor _ _ q) _ a)).trans
      (HomologicalComplex.homologyMap_comp _ _ q).symm

/-- **The horizontal differential on the column cohomology is a Čech differential**: under
`cechDoubleComplexHomologyIsoPi`, the map induced in cohomology by the horizontal differential of
the Čech double complex is the Čech differential of the presheaf `W ↦ Hᵠ(K(W))`. -/
lemma homologyMap_cechDoubleComplex_d_comp_π (p q : ℕ) (b : Fin (p + 2) → ι) :
    HomologicalComplex.homologyMap ((cechDoubleComplex U K).d p (p + 1)) q ≫
        (cechDoubleComplexHomologyIsoPi U K (p + 1) q).hom ≫
          Pi.π (fun a : Fin (p + 2) → ι ↦ (sectionsComplex K (∏ᶜ fun j ↦ U (a j))).homology q) b =
      ∑ m : Fin (p + 2), (-1 : ℤ) ^ (m : ℕ) • ((cechDoubleComplexHomologyIsoPi U K p q).hom ≫
        Pi.π (fun a : Fin (p + 1) → ι ↦ (sectionsComplex K (∏ᶜ fun j ↦ U (a j))).homology q)
          (b ∘ m.succAbove) ≫ HomologicalComplex.homologyMap
            (sectionsComplexMap K (Pi.lift fun x ↦ Pi.π (fun j ↦ U (b j)) (m.succAbove x))) q) := by
  rw [cechDoubleComplexHomologyIsoPi_hom_π, ← HomologicalComplex.homologyMap_comp,
    cechDoubleComplex_d_comp_XIsoPi_hom_π, ← HomologicalComplex.homologyFunctor_map,
    Functor.map_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Functor.map_zsmul]
  simp only [HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_comp,
    cechDoubleComplexHomologyIsoPi_hom_π_assoc, Category.assoc]
  -- the two sides differ only in writing `homology` as objects of `homologyFunctor`
  rfl

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

/-- The factor `a` of `cechDoubleComplexHomologyAddEquiv` is the identification of the cohomology
of the sections over `U (a 0) × ⋯ × U (a p)` with `Hᵠ(U (a 0) × ⋯ × U (a p), F)`. -/
lemma cechDoubleComplexHomologyAddEquiv_apply (p q : ℕ)
    (z : ((cechDoubleComplex U K).X p).homology q) (a : Fin (p + 1) → ι) :
    cechDoubleComplexHomologyAddEquiv U ε hε hε' hK hKU p q z a =
      (Sheaf.H'.addEquivHomologyOfResolution ε hε hε' hK _ (hKU p a) q).symm
        (((cechDoubleComplexHomologyIsoPi U K p q).hom ≫ Pi.π _ a) z) :=
  -- The factor `a` of an element of the explicit product of abelian groups is its image under
  -- the projection of the product cone `productLimitCone`, by definition.
  congrArg _ (ConcreteCategory.congr_hom ((limit.isLimit _).conePointUniqueUpToIso_hom_comp
    (AddCommGrpCat.HasLimit.productLimitCone _).isLimit ⟨a⟩)
      ((cechDoubleComplexHomologyIsoPi U K p q).hom z))

/-- **The horizontal differential on the column cohomology is the Čech differential** of the
cohomology presheaf: under `cechDoubleComplexHomologyAddEquiv`, the map induced in cohomology by
the horizontal differential of the Čech double complex sends a Čech `p`-cochain `c` of
`Hᵠ(-, F)` to `δc`, with `(δc)(b) = ∑ₘ (-1)ᵐ c(b ∘ m.succAbove)` restricted to
`U (b 0) × ⋯ × U (b (p + 1))`. -/
theorem cechDoubleComplexHomologyAddEquiv_homologyMap_d (p q : ℕ)
    (z : ((cechDoubleComplex U K).X p).homology q) (b : Fin (p + 2) → ι) :
    cechDoubleComplexHomologyAddEquiv U ε hε hε' hK hKU (p + 1) q
        (HomologicalComplex.homologyMap ((cechDoubleComplex U K).d p (p + 1)) q z) b =
      ∑ m : Fin (p + 2), (-1 : ℤ) ^ (m : ℕ) • (F.cohomologyPresheaf q).map
        (Pi.lift fun x ↦ Pi.π (fun j ↦ U (b j)) (m.succAbove x)).op
          (cechDoubleComplexHomologyAddEquiv U ε hε hε' hK hKU p q z (b ∘ m.succAbove)) := by
  rw [cechDoubleComplexHomologyAddEquiv_apply, AddEquiv.symm_apply_eq, map_sum]
  simp only [map_zsmul, cechDoubleComplexHomologyAddEquiv_apply, Function.comp_apply,
    Sheaf.H'.addEquivHomologyOfResolution_naturality ε hε hε' hK _ (hKU p _) (hKU (p + 1) b),
    AddEquiv.apply_symm_apply]
  refine (ConcreteCategory.congr_hom (homologyMap_cechDoubleComplex_d_comp_π U K p q b) z).trans ?_
  rw [← AddCommGrpCat.homAddEquiv_apply, map_sum, AddMonoidHom.finsetSum_apply]
  -- the summands agree once `homAddEquiv`, `zsmul` and composition of `AddCommGrpCat` morphisms
  -- are evaluated, which is how these operations are defined
  rfl

end Resolution

/-! ### The total complex: the abutment -/

section Total

variable {T : C} (hT : IsTerminal T)

/-- The coaugmentation of the column `0` of the Čech double complex by the sections over the
terminal object `T`: in resolution degree `q`, the restriction of sections of `Kᵠ` over `T` to the
members of `U`, the degree `0` part of `cechAugmentation`. -/
def cechDoubleComplexCoaugmentation : sectionsComplex K T ⟶ (cechDoubleComplex U K).X 0 where
  f q := (HomologicalComplex.singleObjXSelf _ 0 ((K.X q).obj.obj (op T))).inv ≫
    (cechAugmentation U hT (K.X q).obj).f 0
  comm' q q' _ := by
    have h := HomologicalComplex.congr_hom (cechAugmentation_naturality U hT _ (K.d q q').hom) 0
    simp only [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self] at h
    -- The terms of the column `0` and of `sectionsComplex K T` are those of the Čech complexes and
    -- of the sections by definition of `cechDoubleComplex` and `sectionsComplex`; restating the
    -- goal in those terms lets `h` rewrite it.
    change ((HomologicalComplex.singleObjXSelf _ 0 ((K.X q).obj.obj (op T))).inv ≫
        (cechAugmentation U hT (K.X q).obj).f 0) ≫
          ((cechComplexFunctor U).map (K.d q q').hom).f 0 =
      (K.d q q').hom.app (op T) ≫
        (HomologicalComplex.singleObjXSelf _ 0 ((K.X q').obj.obj (op T))).inv ≫
          (cechAugmentation U hT (K.X q').obj).f 0
    rw [Category.assoc, h]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

lemma cechDoubleComplexCoaugmentation_f (q : ℕ) :
    (cechDoubleComplexCoaugmentation U K hT).f q =
      (HomologicalComplex.singleObjXSelf _ 0 ((K.X q).obj.obj (op T))).inv ≫
        (cechAugmentation U hT (K.X q).obj).f 0 :=
  (rfl)

/-- The coaugmentation of the Čech double complex, followed by the projection of the Čech
`0`-cochains onto the factor `a : Fin 1 → ι`, restricts a section of `Kᵠ` over `T` to
`U (a 0)`, seen as a one-fold product. -/
@[reassoc, simp]
lemma cechDoubleComplexCoaugmentation_f_π (q : ℕ) (a : Fin 1 → ι) :
    (cechDoubleComplexCoaugmentation U K hT).f q ≫
        Pi.π (fun a : Fin 1 → ι ↦ (K.X q).obj.obj (op (∏ᶜ fun j ↦ U (a j)))) a =
      (K.X q).obj.map (hT.from (∏ᶜ fun j ↦ U (a j))).op := by
  -- `singleObjXSelf` is the identity of `Kᵠ(T)` up to the definition of `single₀`.
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (cechAugmentation_f_zero_comp_π U hT (K.X q).obj a)).trans (Category.id_comp _))

/-- The coaugmentation of the Čech double complex is killed by the horizontal differential. -/
lemma cechDoubleComplexCoaugmentation_comp_d :
    cechDoubleComplexCoaugmentation U K hT ≫ (cechDoubleComplex U K).d 0 1 = 0 := by
  ext q : 1
  -- The horizontal differential of the Čech double complex is the Čech differential
  -- (`cechDoubleComplex_d_f`, by definition); stated so, `Hom.comm` applies.
  change ((HomologicalComplex.singleObjXSelf _ 0 ((K.X q).obj.obj (op T))).inv ≫
    (cechAugmentation U hT (K.X q).obj).f 0) ≫
    ((cechComplexFunctor U).obj (K.X q).obj).d 0 1 = 0
  rw [Category.assoc, HomologicalComplex.Hom.comm, HomologicalComplex.single_obj_d,
    zero_comp, comp_zero]

/-- The coaugmented rows of the Čech double complex are the augmented Čech complexes
`0 ⟶ Kᵠ(T) ⟶ Č⁰(U, Kᵠ) ⟶ Č¹(U, Kᵠ) ⟶ ⋯`. -/
lemma rowCoaugmentation_cechDoubleComplexCoaugmentation (q : ℕ) :
    (cechDoubleComplex U K).rowCoaugmentation (cechDoubleComplexCoaugmentation U K hT)
      (cechDoubleComplexCoaugmentation_comp_d U K hT) q = cechAugmentation U hT (K.X q).obj :=
  HomologicalComplex.from_single_hom_ext
    ((HomologicalComplex₂.rowCoaugmentation_f_zero _ _ _ q).trans
      -- `singleObjXSelf` is the identity of `Kᵠ(T)` up to the definition of `single₀`.
      (by simp only [cechDoubleComplexCoaugmentation]; exact Category.id_comp _))

variable [HasSheafify J AddCommGrpCat.{v}]

/-- **The total Čech complex of a complex of injective sheaves computes its sections.** If the
maps `U i ⟶ T` to the terminal object generate a covering sieve and every term of `K` is
injective, the coaugmentation `K(T) ⟶ Tot Č•(U, K•)` is a quasi-isomorphism: its rows are the
augmented Čech complexes of injective sheaves, which are exact
(`quasiIso_cechAugmentation_of_injective`). -/
theorem quasiIso_totalCoaugmentation_cechDoubleComplex
    (hU : Sieve.ofArrows U (fun i ↦ hT.from (U i)) ∈ J T) [∀ q, Injective (K.X q)] :
    QuasiIso ((cechDoubleComplex U K).totalCoaugmentation (cechDoubleComplexCoaugmentation U K hT)
      (cechDoubleComplexCoaugmentation_comp_d U K hT)) :=
  HomologicalComplex₂.quasiIso_totalCoaugmentation _ _ _ fun q ↦ by
    rw [rowCoaugmentation_cechDoubleComplexCoaugmentation]
    exact quasiIso_cechAugmentation_of_injective U hT hU (K.X q)

variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] {F : Sheaf J AddCommGrpCat.{v}} {K}
  (ε : F ⟶ K.X 0) [Mono ε] (hε : ε ≫ K.d 0 1 = 0)
  (hε' : (ShortComplex.mk ε (K.d 0 1) hε).Exact) (hK : ∀ j, K.ExactAt (j + 1))

attribute [local instance] Abelian.Ext.subsingleton_of_injective in
/-- **The abutment of the Čech-to-cohomology spectral sequence.** For an injective resolution
`0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` of an abelian sheaf `F` and a family `U` whose maps to the terminal
object `T` generate a covering sieve, the cohomology of the total complex of the Čech double
complex `Čᵖ(U, Kᵠ)` is the sheaf cohomology `Hⁿ(T, F)`. -/
@[stacks 03AV "The total complex of the Čech double complex of an injective resolution."]
def homologyTotalCechDoubleComplexAddEquiv
    (hU : Sieve.ofArrows U (fun i ↦ hT.from (U i)) ∈ J T) [∀ q, Injective (K.X q)] (n : ℕ) :
    ((cechDoubleComplex U K).total (ComplexShape.up ℕ)).homology n ≃+ F.H' n T :=
  have := quasiIso_totalCoaugmentation_cechDoubleComplex U K hT hU
  ((asIso (HomologicalComplex.homologyMap ((cechDoubleComplex U K).totalCoaugmentation
    (cechDoubleComplexCoaugmentation U K hT) (cechDoubleComplexCoaugmentation_comp_d U K hT))
      n)).symm.addCommGroupIsoToAddEquiv).trans
    (Sheaf.H'.addEquivHomologyOfResolution ε hε hε' hK T
      (fun j k ↦ ((K.X j).H'AddEquivExt (k + 1) T).subsingleton) n).symm

end Total

end TauCeti.CategoryTheory
