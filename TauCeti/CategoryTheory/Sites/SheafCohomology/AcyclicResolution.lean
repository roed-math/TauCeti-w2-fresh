/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import TauCeti.Algebra.Homology.Ext.AcyclicResolution
public import TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence

/-!
# Sheaf cohomology from acyclic resolutions

Let `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` be a resolution of a sheaf of abelian groups `F` on a site, and let
`V` be an object of the site over which every term `Kʲ` has no cohomology in positive degrees,
for instance because each `Kʲ` is injective, or flasque on a topological space. Then the complex
of sections `K⁰(V) ⟶ K¹(V) ⟶ ⋯` computes the cohomology `Hⁿ(V, F)`
(`CategoryTheory.Sheaf.H'.addEquivHomologyOfResolution`). This is the case of the free abelian
sheaf `ℤ[V]` of `TauCeti.CategoryTheory.extAddEquivHomologyOfResolution`, which computes
`Ext(P, F)` from a resolution of `F` by objects without higher `Ext` from `P`: here
`Hⁿ(V, -) = Extⁿ(ℤ[V], -)`, and `ℤ[V]` corepresents the functor of sections over `V`
(`TauCeti.CategoryTheory.freeYonedaSheafCorepresentableBy`).

In the form used to show that derived functors vanish: if `Hⁿ⁺¹(V, F) = 0`, then the complex of
sections is exact in degree `n + 1`, so every cycle of `K(V)` in degree `n + 1` is a boundary
(`CategoryTheory.Sheaf.H'.exists_d_hom_app_eq_of_resolution`).

## Main declarations

* `CategoryTheory.Sheaf.H'.addEquivHomologyOfResolution`: if the terms of a resolution `K` of `F`
  are acyclic over `V`, then `Hⁿ(V, F)` is the cohomology of the complex of sections `K(V)`.
* `CategoryTheory.Sheaf.H'.exists_d_hom_app_eq_of_resolution`: if `Hⁿ⁺¹(V, F) = 0` and the terms
  of a resolution `K` of `F` are acyclic over `V`, then every cycle of `K(V)` in degree `n + 1` is
  a boundary.
* `CategoryTheory.Sheaf.H'.addEquivHomologyOfResolution_naturality`: the identification is
  natural in `V`: restriction in the cohomology presheaf corresponds to restriction of sections.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.1.2A.
-/

public section

open CategoryTheory Limits Opposite Abelian TauCeti.CategoryTheory

universe w v u

namespace CategoryTheory

namespace Sheaf

namespace H'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
  {F : Sheaf J AddCommGrpCat.{v}} {K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ}

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] (ι : F ⟶ K.X 0) [Mono ι] (hι : ι ≫ K.d 0 1 = 0)
  (hι' : (ShortComplex.mk ι (K.d 0 1) hι).Exact) (hK : ∀ j, K.ExactAt (j + 1)) (V : C)
  (hKV : ∀ j k, Subsingleton ((K.X j).H' (k + 1) V))

/-- **Sheaf cohomology from an acyclic resolution.** Let `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` be a resolution of
a sheaf of abelian groups `F` whose terms have no cohomology in positive degrees over an object `V`
of the site. Then `Hⁿ(V, F)` is the cohomology in degree `n` of the complex of sections
`K⁰(V) ⟶ K¹(V) ⟶ ⋯`. -/
noncomputable def addEquivHomologyOfResolution (n : ℕ) :
    F.H' n V ≃+ (((sheafToPresheaf J AddCommGrpCat.{v} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op V)).mapHomologicalComplex _).obj K).homology n :=
  (F.H'AddEquivExt n V).trans <|
    extAddEquivHomologyOfResolution (sheafToPresheaf J AddCommGrpCat.{v} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op V)) (freeYonedaSheafCorepresentableBy J V) ι hι
      hι' hK (fun j k ↦ have := hKV j k; ((K.X j).H'AddEquivExt (k + 1) V).symm.subsingleton) n

include hι' hK hKV in
/-- **Exactness of sections of an acyclic resolution**, in the form used to show that derived
functors vanish. Let `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` be a resolution of a sheaf of abelian groups `F`
whose terms have no cohomology in positive degrees over an object `V` of the site. If
`Hⁿ⁺¹(V, F) = 0`, then every section of `Kⁿ⁺¹` over `V` killed by the differential is the image
of a section of `Kⁿ` over `V`: the complex of sections `K(V)` is exact in degree `n + 1`. -/
theorem exists_d_hom_app_eq_of_resolution (n : ℕ) (hF : Subsingleton (F.H' (n + 1) V))
    (s : (K.X (n + 1)).obj.obj (op V)) (hs : (K.d (n + 1) (n + 2)).hom.app (op V) s = 0) :
    ∃ t : (K.X n).obj.obj (op V), (K.d n (n + 1)).hom.app (op V) t = s := by
  have := (addEquivHomologyOfResolution ι hι hι' hK V hKV (n + 1)).symm.subsingleton
  have hL := AddCommGrpCat.isZero_of_subsingleton (((sheafToPresheaf J AddCommGrpCat.{v} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op V)).mapHomologicalComplex _).obj K |>.homology
      (n + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff] at hL
  exact hL s hs

/-- **Naturality of sheaf cohomology from an acyclic resolution** in the object of the site: for
`i : V' ⟶ V`, the restriction map `Hⁿ(V, F) ⟶ Hⁿ(V', F)` of the cohomology presheaf corresponds to
the map induced in cohomology by restricting sections `K(V) ⟶ K(V')`. -/
theorem addEquivHomologyOfResolution_naturality {V V' : C} (i : V' ⟶ V)
    (hKV : ∀ j k, Subsingleton ((K.X j).H' (k + 1) V))
    (hKV' : ∀ j k, Subsingleton ((K.X j).H' (k + 1) V')) (n : ℕ) (x : F.H' n V) :
    addEquivHomologyOfResolution ι hι hι' hK V' hKV' n ((F.cohomologyPresheaf n).map i.op x) =
      HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex
        (Functor.whiskerLeft (sheafToPresheaf J AddCommGrpCat.{v})
          ((evaluation Cᵒᵖ AddCommGrpCat.{v}).map i.op)) _).app K) n
        (addEquivHomologyOfResolution ι hι hι' hK V hKV n x) := by
  rw [addEquivHomologyOfResolution, addEquivHomologyOfResolution, AddEquiv.trans_apply,
    AddEquiv.trans_apply, cohomologyPresheaf_map_apply]
  exact extAddEquivHomologyOfResolution_naturality (sheafToPresheaf J AddCommGrpCat.{v} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op V)) (freeYonedaSheafCorepresentableBy J V) ι hι
    hι' ((freeYonedaSheafFunctor J).map i)
    (G' := sheafToPresheaf J AddCommGrpCat.{v} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op V'))
    (freeYonedaSheafCorepresentableBy J V')
    (Functor.whiskerLeft (sheafToPresheaf J AddCommGrpCat.{v})
      ((evaluation Cᵒᵖ AddCommGrpCat.{v}).map i.op))
    (fun f ↦ by
      rw [freeYonedaSheafCorepresentableBy_homEquiv, freeYonedaSheafCorepresentableBy_homEquiv]
      exact freeYonedaSheafSectionsEquiv_naturality_left J i _ f) hK _ _ n _

end H'

end Sheaf

end CategoryTheory
