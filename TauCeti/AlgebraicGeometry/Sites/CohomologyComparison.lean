/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.SmallEtaleComparison
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Pullback

/-!
# Cohomology along the comparison morphisms from the big fppf site

The comparison morphisms `ε` (big fppf to big étale over `X`), `π_X` (big étale to small étale)
and `a_X = π_X ∘ ε` (big fppf to small étale) have exact inverse images that send constant sheaves
to constant sheaves. They therefore induce pullback maps on sheaf cohomology,

* `epsilonFppfEtaleH X F n : Hⁿ((Sch/X)_ét, F) →+ Hⁿ((Sch/X)_fppf, ε⁻¹ F)`,
* `piXH X F n : Hⁿ(X_ét, F) →+ Hⁿ((Sch/X)_ét, π_X⁻¹ F)`,
* `aXH X F n : Hⁿ(X_ét, F) →+ Hⁿ((Sch/X)_fppf, a_X⁻¹ F)`,

through `CategoryTheory.Sheaf.H.pullback`. They are the maps that the comparison theorems of
Stacks, Section 59.100 (0DDK) assert to be isomorphisms. The pullback along `a_X` is the composite
of the pullbacks along `π_X` and `ε` (`aXH_apply`), and in degree zero the pullback along `π_X`
is the restriction of global sections along the unit of `π_X⁻¹ ⊣ π_{X,*}` (`equiv₀_piXH`), and
the pullback along `ε` that along the unit of `ε⁻¹ ⊣ ε_*` (`equiv₀_epsilonFppfEtaleH`); so the
pullback along `a_X` is that along the unit of `a_X⁻¹ ⊣ a_{X,*}` (`equiv₀_aXH`).

The coefficient universe `w` is arbitrary: the categories of abelian sheaves are assumed to have
`Ext` groups, and `π_X⁻¹` to be exact, which is an instance for `w = u + 1`.

## Main declarations

* `AlgebraicGeometry.Scheme.epsilonFppfEtaleH`, `piXH`, `aXH`: the pullback of cohomology along
  `ε`, `π_X` and `a_X`.
* `AlgebraicGeometry.Scheme.aXH_apply`: the pullback along `a_X` is the composite of the pullbacks
  along `π_X` and `ε`.
* `AlgebraicGeometry.Scheme.equiv₀_piXH`, `equiv₀_epsilonFppfEtaleH`, `equiv₀_aXH`: in degree
  zero, the pullbacks along `π_X`, `ε` and `a_X` are the restriction of global sections.

## References

* [Stacks Project, Section 59.100 (0DDK)](https://stacks.math.columbia.edu/tag/0DDK)
-/

public section

open CategoryTheory Limits Opposite GrothendieckTopology AddCommGrpCat

universe w w₁ w₂ w₃ u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

section Fppf

variable [HasSheafify (etaleTopology.over X) AddCommGrpCat.{w}]
  [HasSheafify (fppfTopology.over X) AddCommGrpCat.{w}]

/-- The inverse image `ε⁻¹` on abelian sheaves is additive. -/
instance : (epsilonFppfEtale X AddCommGrpCat.{w}).Additive :=
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (epsilonFppfEtale X AddCommGrpCat.{w})
  Functor.additive_of_preservesBinaryBiproducts _

variable [HasExt.{w₁} (Sheaf (etaleTopology.over X) AddCommGrpCat.{w})]
  [HasExt.{w₂} (Sheaf (fppfTopology.over X) AddCommGrpCat.{w})]

/-- The pullback `Hⁿ((Sch/X)_ét, F) →+ Hⁿ((Sch/X)_fppf, ε⁻¹ F)` of cohomology along the
comparison morphism `ε` from the big fppf site to the big étale site. -/
noncomputable def epsilonFppfEtaleH (F : Sheaf (etaleTopology.over X) AddCommGrpCat.{w})
    (n : ℕ) : F.H n →+ ((epsilonFppfEtale X AddCommGrpCat.{w}).obj F).H n :=
  Sheaf.H.pullback _
    ((constantSheafCompEpsilonFppfEtaleIso X AddCommGrpCat.{w}).inv.app (of (ULift ℤ))) F n

/-- In degree zero, the pullback of cohomology along `ε` is the restriction of global sections
`F(X) ⟶ (ε⁻¹ F)(X)` along the unit of the adjunction `ε⁻¹ ⊣ ε_*`, at the terminal object `X` of the
big site. -/
lemma equiv₀_epsilonFppfEtaleH (F : Sheaf (etaleTopology.over X) AddCommGrpCat.{w})
    (x : F.H 0) :
    Sheaf.H.equiv₀ _ (Over.mkIdTerminal (X := X)) (epsilonFppfEtaleH X F 0 x) =
      ((epsilonFppfEtaleAdjunction X _).unit.app F).hom.app (op (Over.mk (𝟙 X)))
        (Sheaf.H.equiv₀ F (Over.mkIdTerminal (X := X)) x) :=
  have : PreservesFiniteColimits (sheafInverseImage (etaleTopology.over X)
      (fppfTopology.over X) AddCommGrpCat.{w}) :=
    inferInstanceAs (PreservesFiniteColimits (epsilonFppfEtale X _))
  Sheaf.H.equiv₀_pullback_sheafInverseImage (etaleTopology_over_le_fppfTopology_over X)
    (Over.mkIdTerminal (X := X)) F x

end Fppf

section SmallEtale

variable [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{w}, (Etale.forget X).op.HasLeftKanExtension F]
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
  [HasSheafify (etaleTopology.over X) AddCommGrpCat.{w}]
  [PreservesFiniteLimits (piX X AddCommGrpCat.{w})]

/-- The inverse image `π_X⁻¹` on abelian sheaves is additive. -/
instance : (piX X AddCommGrpCat.{w}).Additive :=
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (piX X AddCommGrpCat.{w})
  Functor.additive_of_preservesBinaryBiproducts _

variable [HasExt.{w₁} (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})]
  [HasExt.{w₂} (Sheaf (etaleTopology.over X) AddCommGrpCat.{w})]

/-- The pullback `Hⁿ(X_ét, F) →+ Hⁿ((Sch/X)_ét, π_X⁻¹ F)` of cohomology along the comparison
morphism `π_X` from the big étale site to the small étale site. -/
noncomputable def piXH (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (n : ℕ) :
    F.H n →+ ((piX X AddCommGrpCat.{w}).obj F).H n :=
  Sheaf.H.pullback _ ((constantSheafCompPiXIso X AddCommGrpCat.{w}).inv.app (of (ULift ℤ))) F n

/-- In degree zero, the pullback of cohomology along `π_X` is the restriction of global sections
`F(X) ⟶ (π_X⁻¹ F)(X)` along the unit of the adjunction `π_X⁻¹ ⊣ π_{X,*}`. -/
lemma equiv₀_piXH (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (x : F.H 0) :
    Sheaf.H.equiv₀ _ Over.mkIdTerminal (piXH X F 0 x) =
      ((piXAdjunction X _).unit.app F).hom.app (op (Etale.mk (𝟙 X)))
        (Sheaf.H.equiv₀ F (@MorphismProperty.Over.mkIdTerminal _ _ @Etale X
          ⟨fun _ ↦ inferInstance⟩) x) := by
  have : PreservesFiniteLimits ((Etale.forget X).sheafPullback AddCommGrpCat.{w}
      X.smallEtaleTopology (etaleTopology.over X)) := ‹PreservesFiniteLimits (piX X _)›
  have := (piXAdjunction X AddCommGrpCat.{w}).isRightAdjoint
  have h := Sheaf.H.equiv₀_pullback_sheafPullback (K := etaleTopology.over X) (Etale.forget X)
    (@MorphismProperty.Over.mkIdTerminal _ _ @Etale X ⟨fun _ ↦ inferInstance⟩)
    Over.mkIdTerminal F x
  rw [piXH, constantSheafCompPiXIso_inv_app]
  exact h

end SmallEtale

section AX

variable [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{w}, (Etale.forget X).op.HasLeftKanExtension F]
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
  [HasSheafify (etaleTopology.over X) AddCommGrpCat.{w}]
  [HasSheafify (fppfTopology.over X) AddCommGrpCat.{w}]
  [PreservesFiniteLimits (piX X AddCommGrpCat.{w})]

/-- The inverse image `a_X⁻¹` on abelian sheaves is additive. -/
instance : (aX X AddCommGrpCat.{w}).Additive := by
  dsimp only [aX]
  infer_instance

variable [HasExt.{w₁} (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})]
  [HasExt.{w₃} (Sheaf (fppfTopology.over X) AddCommGrpCat.{w})]

/-- The pullback `Hⁿ(X_ét, F) →+ Hⁿ((Sch/X)_fppf, a_X⁻¹ F)` of cohomology along the comparison
morphism `a_X` from the big fppf site to the small étale site. -/
noncomputable def aXH (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (n : ℕ) :
    F.H n →+ ((aX X AddCommGrpCat.{w}).obj F).H n :=
  Sheaf.H.pullback _ ((constantSheafCompAXIso X AddCommGrpCat.{w}).inv.app (of (ULift ℤ))) F n

/-- **Composition of the comparison morphisms on cohomology**: the pullback along `a_X` is the
pullback along `π_X` followed by the pullback along `ε`. -/
lemma aXH_apply [HasExt.{w₂} (Sheaf (etaleTopology.over X) AddCommGrpCat.{w})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (n : ℕ) (x : F.H n) :
    aXH X F n x = epsilonFppfEtaleH X _ n (piXH X F n x) := by
  rw [aXH, constantSheafCompAXIso_inv_app]
  exact Sheaf.H.pullback_comp_apply (piX X _) _ (epsilonFppfEtale X _) _ F n x

/-- In degree zero, the pullback of cohomology along `a_X` is the restriction of global sections
`F(X) ⟶ (a_X⁻¹ F)(X)` along the unit of the adjunction `a_X⁻¹ ⊣ a_{X,*}`. -/
lemma equiv₀_aXH [HasExt.{w₂} (Sheaf (etaleTopology.over X) AddCommGrpCat.{w})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (x : F.H 0) :
    Sheaf.H.equiv₀ _ (Over.mkIdTerminal (X := X)) (aXH X F 0 x) =
      ((aXAdjunction X _).unit.app F).hom.app (op (Etale.mk (𝟙 X)))
        (Sheaf.H.equiv₀ F (@MorphismProperty.Over.mkIdTerminal _ _ @Etale X
          ⟨fun _ ↦ inferInstance⟩) x) := by
  rw [aXH_apply]
  refine (equiv₀_epsilonFppfEtaleH X _ _).trans ?_
  rw [equiv₀_piXH, aXAdjunction_unit_app]
  rfl

end AX

end AlgebraicGeometry.Scheme
