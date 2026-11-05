/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import TauCeti.AlgebraicGeometry.Sites.SmallEtaleBaseChange

/-!
# Open subschemes as schemes étale over a scheme

An open subscheme of a scheme `X` is étale over `X`, so taking an open subset to the corresponding
open subscheme is a functor `X.restrictEtaleFunctor : X.Opens ⥤ X.Etale`. A morphism of étale
`X`-schemes into an open subscheme `U` exists exactly when the image lies in `U`, and is then
unique; hence the open subsets through which an étale `X`-scheme factors contain `X` and are closed
under intersections, and `X.restrictEtaleFunctor` is representably flat. Base change along
`g : Y ⟶ X` takes the open subscheme `U` to the open subscheme `g ⁻¹ᵁ U`. This is the functor
underlying the comparison morphisms from the small étale and Nisnevich sites of `X` to its Zariski
site.

## Main declarations

* `AlgebraicGeometry.Scheme.restrictEtaleFunctor`: open subsets of `X` as schemes étale over `X`.
* `AlgebraicGeometry.Scheme.restrictEtaleFunctorLift`,
  `AlgebraicGeometry.Scheme.range_subset_of_hom_restrictEtaleFunctor_obj`: an étale `X`-scheme maps
  to the open subscheme `U` exactly when its image lies in `U`.
* `AlgebraicGeometry.Scheme.restrictEtaleFunctor_hom_ext`: such a map is unique.
* The `RepresentablyFlat` instance for `X.restrictEtaleFunctor`.
* `AlgebraicGeometry.Scheme.restrictEtaleFunctorCompEtalePullbackIso`: compatibility with base
  change.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The functor taking an open subset of `X` to the corresponding open subscheme, regarded as a
scheme étale over `X`. -/
@[expose] noncomputable def restrictEtaleFunctor : X.Opens ⥤ X.Etale :=
  MorphismProperty.Comma.lift X.restrictFunctor
    (fun U ↦ (inferInstance : AlgebraicGeometry.Etale U.ι)) (fun _ ↦ trivial) (fun _ ↦ trivial)

@[simp]
lemma restrictEtaleFunctor_obj_hom (U : X.Opens) :
    (X.restrictEtaleFunctor.obj U).hom = U.ι :=
  rfl

@[simp]
lemma restrictEtaleFunctor_map_left {U V : X.Opens} (i : U ⟶ V) :
    (X.restrictEtaleFunctor.map i).left = X.homOfLE i.le :=
  rfl

variable {X}

/-- A morphism of étale `X`-schemes into an open subscheme is determined by its source. -/
lemma restrictEtaleFunctor_hom_ext {V : X.Etale} {U : X.Opens}
    (f g : V ⟶ X.restrictEtaleFunctor.obj U) : f = g := by
  apply MorphismProperty.Over.Hom.ext
  have hf := f.w
  have hg := g.w
  simp only [Functor.id_obj, Functor.const_obj_obj, restrictEtaleFunctor_obj_hom] at hf hg
  exact (cancel_mono U.ι).mp (hf.trans hg.symm)

/-- An étale `X`-scheme whose image lies in an open subset `U` factors through `U`. -/
noncomputable def Etale.liftOpens {V : X.Etale} {U : X.Opens}
    (h : Set.range (V.left ↘ X) ⊆ U) : V.left ⟶ U :=
  IsOpenImmersion.lift U.ι (V.left ↘ X) (by simpa using h)

@[reassoc (attr := simp)]
lemma Etale.liftOpens_ι {V : X.Etale} {U : X.Opens} (h : Set.range (V.left ↘ X) ⊆ U) :
    Etale.liftOpens h ≫ U.ι = V.left ↘ X :=
  IsOpenImmersion.lift_fac _ _ _

/-- An étale `X`-scheme whose image lies in an open subset `U` maps to the open subscheme `U`. -/
noncomputable def restrictEtaleFunctorLift {V : X.Etale} {U : X.Opens}
    (h : Set.range (V.left ↘ X) ⊆ U) : V ⟶ X.restrictEtaleFunctor.obj U :=
  MorphismProperty.Over.homMk (Etale.liftOpens h) (Etale.liftOpens_ι h)

/-- The image of an étale `X`-scheme mapping to an open subscheme `U` lies in `U`. -/
lemma range_subset_of_hom_restrictEtaleFunctor_obj {V : X.Etale} {U : X.Opens}
    (f : V ⟶ X.restrictEtaleFunctor.obj U) : Set.range (V.left ↘ X) ⊆ U := by
  have hf : f.left ≫ U.ι = V.hom := by simpa using f.w
  rintro _ ⟨x, rfl⟩
  let g : V.left ⟶ U.toScheme := f.left
  have hx : U.ι (g x) = (V.left ↘ X) x := congrArg (fun φ : V.left ⟶ X ↦ φ x) hf
  rw [← hx]
  exact (g x).2

variable (X)

/-- The functor from open subsets of `X` to schemes étale over `X` is representably flat: the open
subsets through which an étale `X`-scheme factors contain `X` and are closed under intersections. -/
instance : RepresentablyFlat X.restrictEtaleFunctor where
  cofiltered V :=
    { nonempty := ⟨StructuredArrow.mk (restrictEtaleFunctorLift (U := ⊤) (by simp))⟩
      cone_objs A B :=
        ⟨StructuredArrow.mk (restrictEtaleFunctorLift (U := A.right ⊓ B.right)
            (Set.subset_inter (range_subset_of_hom_restrictEtaleFunctor_obj A.hom)
              (range_subset_of_hom_restrictEtaleFunctor_obj B.hom))),
          StructuredArrow.homMk (homOfLE inf_le_left) (restrictEtaleFunctor_hom_ext _ _),
          StructuredArrow.homMk (homOfLE inf_le_right) (restrictEtaleFunctor_hom_ext _ _), trivial⟩
      cone_maps A B f g :=
        ⟨A, 𝟙 A, by
          rw [Category.id_comp, Category.id_comp]
          ext
          exact Subsingleton.elim _ _⟩ }

/-- Base change of open subschemes: for `g : Y ⟶ X` and an open subset `U` of `X`, the base change
`U ×ₓ Y` of the open subscheme `U` is the open subscheme `g ⁻¹ᵁ U` of `Y`. -/
noncomputable def restrictEtaleFunctorCompEtalePullbackIso {Y : Scheme.{u}} (g : Y ⟶ X) :
    X.restrictEtaleFunctor ⋙ Etale.pullback g ≅
      TopologicalSpace.Opens.map g.base ⋙ Y.restrictEtaleFunctor :=
  NatIso.ofComponents
    (fun U ↦ MorphismProperty.Over.isoMk (pullbackSymmetry _ _ ≪≫ pullbackRestrictIsoRestrict g U)
      ((Category.assoc _ _ _).trans ((congrArg _ (pullbackRestrictIsoRestrict_hom_ι g U)).trans
        (pullbackSymmetry_hom_comp_fst _ _))))
    fun _ ↦ restrictEtaleFunctor_hom_ext _ _

end AlgebraicGeometry.Scheme
