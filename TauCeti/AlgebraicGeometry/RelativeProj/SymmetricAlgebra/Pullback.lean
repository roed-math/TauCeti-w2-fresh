/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.GradedPullback
public import TauCeti.AlgebraicGeometry.RelativeProj.BaseChange
public import TauCeti.AlgebraicGeometry.RelativeProj.ClosedImmersion

/-!
# Base change of projective bundles

For a morphism of schemes `g : Y ⟶ X` and a quasicoherent sheaf `F` on `X`, the projective bundle
of the pullback is the base change of the projective bundle:

`ℙ_Y(g^* F) ≅ ℙ_X(F) ×_X Y`

over `Y` (`relativeProjGradedSymmetricAlgebraPullbackIso`). It is the isomorphism of relative
`Proj`s induced by the isomorphism `g^* (Sym F) ≅ Sym (g^* F)` of graded algebras
(`pullbackGradedSymmetricAlgebraIso`), followed by the base change of the relative `Proj`
(`GradedQuasicoherentAlgebra.relativeProjPullbackIso`).

Consequently, a quotient `g^* F ⟶ E` of a pulled-back sheaf embeds `ℙ_Y(E)` as a closed
subscheme of `ℙ_X(F) ×_X Y` over `Y`, and so does the relative `Proj` of every graded algebra on
`Y` generated in degree one whose degree-one part is such a quotient. This is the step of the
composition of projective morphisms that moves the projective bundle from `Y` down to `X`.

## Main results

* `TauCeti.AlgebraicGeometry.relativeProjGradedSymmetricAlgebraPullbackIso`: the isomorphism
  `ℙ_Y(g^* F) ≅ ℙ_X(F) ×_X Y`, lying over `Y`
  (`relativeProjGradedSymmetricAlgebraPullbackIso_hom_snd`);
* `TauCeti.AlgebraicGeometry.isPullback_relativeProjGradedSymmetricAlgebraPullback`: the square
  formed by `ℙ_Y(g^* F) ⟶ ℙ_X(F)`, the structure morphisms and `g` is cartesian;
* `TauCeti.AlgebraicGeometry.exists_isClosedImmersion_relativeProjPullback_of_epi`: an
  epimorphism `g^* F ⟶ E` gives a closed immersion `ℙ_Y(E) ⟶ ℙ_X(F) ×_X Y` over `Y`;
* `GradedQuasicoherentAlgebra.exists_isClosedImmersion_relativeProjPullback_of_epi`: for a graded
  algebra `B` on `Y` generated in degree one, an epimorphism `g^* F ⟶ B₁` gives a closed
  immersion `Proj_Y(B) ⟶ ℙ_X(F) ×_X Y` over `Y`.

## References

* The Stacks Project, [Tag 01O3](https://stacks.math.columbia.edu/tag/01O3) and
  [Tag 01OA](https://stacks.math.columbia.edu/tag/01OA).
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry GradedQuasicoherentAlgebra

universe u

noncomputable section

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (F : QuasicoherentSheaf X)

/-- **The projective bundle commutes with base change**: for `g : Y ⟶ X` and a quasicoherent sheaf
`F` on `X`, the projective bundle `ℙ_Y(g^* F)` of the pullback is `ℙ_X(F) ×_X Y`. It is the
isomorphism of relative `Proj`s induced by `g^* (Sym F) ≅ Sym (g^* F)`, followed by
`GradedQuasicoherentAlgebra.relativeProjPullbackIso`. -/
def relativeProjGradedSymmetricAlgebraPullbackIso :
    ((gradedSymmetricAlgebra Y).obj ((QuasicoherentSheaf.pullback g).obj F)).obj.relativeProj ≅
      Limits.pullback ((gradedSymmetricAlgebra X).obj F).obj.relativeProjToBase g :=
  (CommMon.relativeProjIso
      (A := ((GradedQuasicoherentAlgebra.pullback g).obj ((gradedSymmetricAlgebra X).obj F)).obj)
      (B := ((gradedSymmetricAlgebra Y).obj ((QuasicoherentSheaf.pullback g).obj F)).obj)
      ((isGradedQuasicoherentAlgebra Y).ι.mapIso (pullbackGradedSymmetricAlgebraIso g F))).symm ≪≫
    relativeProjPullbackIso g ((gradedSymmetricAlgebra X).obj F)

/-- The isomorphism `ℙ_Y(g^* F) ≅ ℙ_X(F) ×_X Y` lies over `Y`. -/
@[reassoc (attr := simp)]
theorem relativeProjGradedSymmetricAlgebraPullbackIso_hom_snd :
    (relativeProjGradedSymmetricAlgebraPullbackIso g F).hom ≫ pullback.snd _ g =
      ((gradedSymmetricAlgebra Y).obj
        ((QuasicoherentSheaf.pullback g).obj F)).obj.relativeProjToBase := by
  simp [relativeProjGradedSymmetricAlgebraPullbackIso]

/-- **`ℙ_Y(g^* F)` is the base change of `ℙ_X(F)`**: the square formed by
`ℙ_Y(g^* F) ≅ ℙ_X(F) ×_X Y ⟶ ℙ_X(F)`, the structure morphisms and `g` is cartesian. -/
theorem isPullback_relativeProjGradedSymmetricAlgebraPullback :
    IsPullback ((relativeProjGradedSymmetricAlgebraPullbackIso g F).hom ≫ pullback.fst _ _)
      ((gradedSymmetricAlgebra Y).obj
        ((QuasicoherentSheaf.pullback g).obj F)).obj.relativeProjToBase
      ((gradedSymmetricAlgebra X).obj F).obj.relativeProjToBase g :=
  IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩
    (relativeProjGradedSymmetricAlgebraPullbackIso g F) rfl
    (relativeProjGradedSymmetricAlgebraPullbackIso_hom_snd g F)

variable {g F}

/-- **A quotient of a pulled-back sheaf gives a closed subscheme of the base-changed projective
bundle**: for `g : Y ⟶ X`, a quasicoherent sheaf `F` on `X` and an epimorphism `ψ : g^* F ⟶ E` of
quasicoherent sheaves on `Y`, there is a closed immersion `ℙ_Y(E) ⟶ ℙ_X(F) ×_X Y` over `Y`: the
closed immersion `ℙ_Y(E) ⟶ ℙ_Y(g^* F)` induced by `ψ`, followed by
`relativeProjGradedSymmetricAlgebraPullbackIso`. -/
theorem exists_isClosedImmersion_relativeProjPullback_of_epi {E : QuasicoherentSheaf Y}
    (ψ : (QuasicoherentSheaf.pullback g).obj F ⟶ E) [Epi ψ.hom] :
    ∃ i : ((gradedSymmetricAlgebra Y).obj E).obj.relativeProj ⟶
        Limits.pullback ((gradedSymmetricAlgebra X).obj F).obj.relativeProjToBase g,
      IsClosedImmersion i ∧
        i ≫ pullback.snd _ g = ((gradedSymmetricAlgebra Y).obj E).obj.relativeProjToBase := by
  have hφ := CommMon.irrelevantLeMap_of_isGeneratedInDegreeOne
    ((gradedSymmetricAlgebra Y).map ψ).hom (isGeneratedInDegreeOne_gradedSymmetricAlgebra E)
    fun U hU ↦ @Scheme.Modules.Hom.app_surjective_of_epi_of_isAffineOpen _ _ _ _ _
      (inferInstanceAs (((gradedSymmetricAlgebra Y).obj
        ((QuasicoherentSheaf.pullback g).obj F)).obj.X 1).IsQuasicoherent)
      (inferInstanceAs (((gradedSymmetricAlgebra Y).obj E).obj.X 1).IsQuasicoherent) U hU
  have := isClosedImmersion_relativeProjMap_gradedSymmetricAlgebra_map ψ hφ
  exact ⟨CommMon.relativeProjMap _ hφ ≫ (relativeProjGradedSymmetricAlgebraPullbackIso g F).hom,
    inferInstance, by simp⟩

/-- **A relative `Proj` generated in degree one by a quotient of a pulled-back sheaf is a closed
subscheme of the base-changed projective bundle**: for `g : Y ⟶ X`, a quasicoherent sheaf `F` on
`X`, a graded quasicoherent algebra `B` on `Y` generated in degree one and an epimorphism
`g^* F ⟶ B₁`, there is a closed immersion `Proj_Y(B) ⟶ ℙ_X(F) ×_X Y` over `Y`: the closed
immersion `Proj_Y(B) ⟶ ℙ_Y(B₁)` induced by the counit `Sym B₁ ⟶ B`, followed by the closed
immersion of `exists_isClosedImmersion_relativeProjPullback_of_epi`. -/
theorem GradedQuasicoherentAlgebra.exists_isClosedImmersion_relativeProjPullback_of_epi
    (B : GradedQuasicoherentAlgebra Y) (hB : B.obj.IsGeneratedInDegreeOne)
    (ψ : (QuasicoherentSheaf.pullback g).obj F ⟶ degreeOne.obj B) [Epi ψ.hom] :
    ∃ i : B.obj.relativeProj ⟶
        Limits.pullback ((gradedSymmetricAlgebra X).obj F).obj.relativeProjToBase g,
      IsClosedImmersion i ∧ i ≫ pullback.snd _ g = B.obj.relativeProjToBase := by
  obtain ⟨j, hj, hjs⟩ :=
    _root_.TauCeti.AlgebraicGeometry.exists_isClosedImmersion_relativeProjPullback_of_epi ψ
  let c := ((gradedSymmetricAlgebraAdjunction Y).counit.app B).hom
  have hc := CommMon.irrelevantLeMap_of_isGeneratedInDegreeOne c hB fun _ _ ↦
    (ConcreteCategory.bijective_of_isIso ((Scheme.Modules.sectionsFunctor _).map
      (c.hom.hom 1))).2
  have := B.isClosedImmersion_relativeProjMap_counit hB hc
  exact ⟨CommMon.relativeProjMap c hc ≫ j, inferInstance,
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hjs).trans
      (CommMon.relativeProjMap_relativeProjToBase c hc))⟩

end

end TauCeti.AlgebraicGeometry
