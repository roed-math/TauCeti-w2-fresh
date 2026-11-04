/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic

/-!
# Čech complexes along a functor preserving the products of a family

Let `G : C ⥤ D` be a functor between categories with finite products, let `U : ι → C` be a family
and let `Q : Dᵒᵖ ⥤ A` be a presheaf. The Čech complex of the pulled-back presheaf `G.op ⋙ Q` for
`U` has terms `Q(G(U (a 0) × ⋯ × U (a n)))`, while the Čech complex of `Q` for the family `G ∘ U`
has terms `Q(G (U (a 0)) × ⋯ × G (U (a n)))`. If `G` preserves the finite products of members of
`U`, in the sense that the comparison maps `piComparison G (U ∘ a)` are isomorphisms, the two Čech
complexes are isomorphic (`cechComplexCompIsoOfIsIso`).

This is the version of `TauCeti.CategoryTheory.cechComplexCompIso` for a target category that need
not be thin. Its main use is for the corepresentable functor `coyoneda.obj (op W)`, which preserves
all limits: the Čech complex for `U` of the presheaf `V ↦ ℤ[Hom(W, V)]` is then the Čech complex
of the presheaf `S ↦ ℤ[S]` on types for the family of sets `Hom(W, U i)`.

## Main definitions

* `TauCeti.CategoryTheory.cechComplexCompIsoOfIsIso`: the isomorphism between the Čech complex of
  `Q` for `G ∘ U` and the Čech complex of `G.op ⋙ Q` for `U`.

## Main results

* `TauCeti.CategoryTheory.cechComplexCompIsoOfIsIso_hom_f_π`: its factors are `Q` applied to the
  comparison maps of the products.
* `TauCeti.CategoryTheory.exactAt_cechComplexFunctor_obj_comp_iff`: the Čech complex of
  `G.op ⋙ Q` for `U` is exact in a degree if and only if the one of `Q` for `G ∘ U` is.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v v' v'' u u' u''

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type u'} [Category.{v'} A]
  [Preadditive A] [HasProducts.{w} A] {ι : Type w}

/-- The degree `n` term of the Čech complex is, up to unfolding, the product of the values of `P`
on the `(n + 1)`-fold products of members. -/
private def cechXIso (U : ι → C) (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    ((cechComplexFunctor U).obj P).X n ≅
      ∏ᶜ fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j))) :=
  Iso.refl _

/-- `cechComplexFunctor_obj_d_comp_π`, stated through `cechXIso`. -/
@[reassoc]
private lemma cechComplexFunctor_obj_d_comp_cechXIso_hom_π (U : ι → C) (P : Cᵒᵖ ⥤ A) (n : ℕ)
    (k : Fin (n + 2) → ι) :
    ((cechComplexFunctor U).obj P).d n (n + 1) ≫ (cechXIso U P (n + 1)).hom ≫ Pi.π _ k =
      ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) • ((cechXIso U P n).hom ≫ Pi.π _ (k ∘ m.succAbove) ≫
        P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (m.succAbove x)).op) :=
  -- `cechXIso` is the identity
  (_ ≫= Category.id_comp _).trans <| (cechComplexFunctor_obj_d_comp_π U P n k).trans <|
    Finset.sum_congr rfl fun _ _ ↦ congrArg _ (Category.id_comp _).symm

variable {D : Type u''} [Category.{v''} D] [HasFiniteProducts D]
  (G : C ⥤ D) (U : ι → C) (Q : Dᵒᵖ ⥤ A)
  [∀ (n : ℕ) (a : Fin (n + 1) → ι), IsIso (piComparison G fun j ↦ U (a j))]

/-- The comparison isomorphism `G(U (a 0) × ⋯ × U (a n)) ≅ G (U (a 0)) × ⋯ × G (U (a n))`. -/
private def prodIso (n : ℕ) (a : Fin (n + 1) → ι) :
    G.obj (∏ᶜ fun j ↦ U (a j)) ≅ ∏ᶜ fun j ↦ G.obj (U (a j)) :=
  asIso (piComparison G fun j ↦ U (a j))

/-- The comparison isomorphisms commute with the restrictions along the coface maps. -/
@[reassoc]
private lemma prodIso_hom_comp_lift (n : ℕ) (k : Fin (n + 2) → ι) (m : Fin (n + 2)) :
    (prodIso G U (n + 1) k).hom ≫
        Pi.lift (fun x ↦ Pi.π (fun j ↦ G.obj (U (k j))) (m.succAbove x)) =
      G.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (m.succAbove x)) ≫
        (prodIso G U n (k ∘ m.succAbove)).hom := by
  refine Pi.hom_ext _ _ fun x ↦ ?_
  simp [prodIso]

/-- The degree `n` component of the isomorphism of Čech complexes. -/
private def compXIso (n : ℕ) :
    ((cechComplexFunctor (fun i ↦ G.obj (U i))).obj Q).X n ≅
      ((cechComplexFunctor U).obj (G.op ⋙ Q)).X n :=
  cechXIso _ Q n ≪≫ (Pi.mapIso fun a : Fin (n + 1) → ι ↦ Q.mapIso (prodIso G U n a).op) ≪≫
    (cechXIso U (G.op ⋙ Q) n).symm

/-- The factors of `compXIso` are given by `prodIso`. -/
private lemma compXIso_hom_π (n : ℕ) (a : Fin (n + 1) → ι) :
    (compXIso G U Q n).hom ≫ (cechXIso U (G.op ⋙ Q) n).hom ≫ Pi.π _ a =
      (cechXIso _ Q n).hom ≫ Pi.π _ a ≫ Q.map (prodIso G U n a).hom.op := by
  simp [compXIso]

/-- The components `compXIso` commute with the differentials. -/
private lemma compXIso_hom_comp_d (n : ℕ) :
    (compXIso G U Q n).hom ≫ ((cechComplexFunctor U).obj (G.op ⋙ Q)).d n (n + 1) =
      ((cechComplexFunctor (fun i ↦ G.obj (U i))).obj Q).d n (n + 1) ≫
        (compXIso G U Q (n + 1)).hom := by
  rw [← cancel_mono (cechXIso U (G.op ⋙ Q) (n + 1)).hom]
  refine Pi.hom_ext _ _ fun k ↦ ?_
  simp only [Category.assoc]
  rw [cechComplexFunctor_obj_d_comp_cechXIso_hom_π, compXIso_hom_π,
    cechComplexFunctor_obj_d_comp_cechXIso_hom_π_assoc,
    Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    ← Category.assoc (cechXIso U (G.op ⋙ Q) n).hom, ← Category.assoc (compXIso G U Q n).hom,
    compXIso_hom_π]
  simp only [Category.assoc, Functor.comp_map, Functor.op_map, ← Functor.map_comp, ← op_comp,
    Quiver.Hom.unop_op, prodIso_hom_comp_lift]

/-- **Čech complexes along a functor preserving products.** If `G` preserves the finite products
of members of `U`, the Čech complex of `Q` for the family `G ∘ U` is isomorphic to the Čech complex
of `G.op ⋙ Q` for `U`. In degree `n` it acts on the factor indexed by `a` through `Q` applied to
the comparison map `G(U (a 0) × ⋯ × U (a n)) ⟶ G (U (a 0)) × ⋯ × G (U (a n))`
(`cechComplexCompIsoOfIsIso_hom_f_π`). -/
def cechComplexCompIsoOfIsIso :
    (cechComplexFunctor (fun i ↦ G.obj (U i))).obj Q ≅ (cechComplexFunctor U).obj (G.op ⋙ Q) :=
  HomologicalComplex.Hom.isoOfComponents (compXIso G U Q) fun n _ h ↦ by
    obtain rfl : n + 1 = _ := h
    exact compXIso_hom_comp_d G U Q n

/-- The factor of `(cechComplexCompIsoOfIsIso G U Q).hom.f n` indexed by `a` is `Q` applied to
the comparison map `G(U (a 0) × ⋯ × U (a n)) ⟶ G (U (a 0)) × ⋯ × G (U (a n))`. -/
@[reassoc]
theorem cechComplexCompIsoOfIsIso_hom_f_π (n : ℕ) (a : Fin (n + 1) → ι) :
    (cechComplexCompIsoOfIsIso G U Q).hom.f n ≫ Pi.π _ a =
      Pi.π _ a ≫ Q.map (piComparison G fun j ↦ U (a j)).op :=
  -- `cechXIso` is the identity
  (_ ≫= (Category.id_comp _).symm).trans <| (compXIso_hom_π G U Q n a).trans (Category.id_comp _)

variable [CategoryWithHomology A]

/-- If `G` preserves the finite products of members of `U`, the Čech complex of `G.op ⋙ Q` for
`U` is exact in degree `n` if and only if the Čech complex of `Q` for the family `G ∘ U` is. -/
theorem exactAt_cechComplexFunctor_obj_comp_iff (n : ℕ) :
    ((cechComplexFunctor U).obj (G.op ⋙ Q)).ExactAt n ↔
      ((cechComplexFunctor (fun i ↦ G.obj (U i))).obj Q).ExactAt n :=
  (exactAt_iff_of_quasiIsoAt (cechComplexCompIsoOfIsIso G U Q).hom n).symm

end TauCeti.CategoryTheory
