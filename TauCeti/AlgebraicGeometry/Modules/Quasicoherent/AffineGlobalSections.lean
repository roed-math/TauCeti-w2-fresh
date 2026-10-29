/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Colimits

/-!
# Global sections detect isomorphisms of quasi-coherent modules on affine schemes

On an affine scheme `X`, a morphism of quasi-coherent modules is an isomorphism as soon as it is
bijective on global sections. Global sections are global sections on the affine chart
`Spec Γ(X, ⊤) ⟶ X`, an isomorphism, and on a spectrum they are the inverse of the tilde
equivalence on quasi-coherent modules.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_restrictFunctor_map`: restriction along an
  isomorphism of schemes reflects isomorphisms.
* `AlgebraicGeometry.Scheme.Modules.isIso_of_bijective_sectionsFunctor_map_top`: a morphism of
  quasi-coherent modules on an affine scheme that is bijective on global sections is an
  isomorphism.
* `AlgebraicGeometry.Scheme.Modules.isIso_of_mono_of_surjective_sectionsFunctor_map_top`: on an
  affine scheme, a quasi-coherent submodule containing every global section is everything.

## References

* The Stacks Project, Lemma 26.7.5 (Tag 01I7).
-/

public section

open CategoryTheory Limits

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Restriction along an isomorphism of schemes reflects isomorphisms of modules. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_restrictFunctor_map
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsIso j] {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((restrictFunctor j).map f)] : IsIso f := by
  let e : restrictFunctor j ⋙ restrictFunctor (inv j) ≅ 𝟭 X.Modules :=
    (restrictFunctorComp (inv j) j).symm ≪≫ restrictFunctorCongr (IsIso.inv_hom_id j) ≪≫
      restrictFunctorId
  exact (NatIso.isIso_map_iff e f).mp
    (inferInstanceAs (IsIso ((restrictFunctor (inv j)).map ((restrictFunctor j).map f))))

/-- On an affine scheme, a morphism of quasi-coherent modules that is bijective on global
sections is an isomorphism. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_of_bijective_sectionsFunctor_map_top
    [IsAffine X] {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    (hf : Function.Bijective ((sectionsFunctor ⊤).map f).hom) : IsIso f := by
  let hU := isAffineOpen_top X
  have := hU.isOpenImmersion_fromSpec
  have : IsIso ((sectionsFunctor ⊤).map f) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hf
  have : IsIso (moduleSpecΓFunctor.map ((restrictFunctor hU.fromSpec).map f)) :=
    (NatIso.isIso_map_iff hU.restrictFromSpecCompModuleSpecΓFunctorIso f).mpr this
  -- On the spectrum, global sections of quasi-coherent modules are the inverse of the tilde
  -- equivalence, which reflects isomorphisms.
  let P := SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf
  have hM : P ((restrictFunctor hU.fromSpec).obj M) := isQuasicoherent_restrictFunctor _ _
  have hN : P ((restrictFunctor hU.fromSpec).obj N) := isQuasicoherent_restrictFunctor _ _
  let g : (⟨_, hM⟩ : P.FullSubcategory) ⟶ ⟨_, hN⟩ :=
    ObjectProperty.homMk ((restrictFunctor hU.fromSpec).map f)
  have : IsIso ((tildeEquiv (R := Γ(X, ⊤))).inverse.map g) := by assumption
  have : IsIso g := isIso_of_reflects_iso g (tildeEquiv (R := Γ(X, ⊤))).inverse
  have : IsIso ((restrictFunctor hU.fromSpec).map f) :=
    inferInstanceAs (IsIso (P.ι.map g))
  have : IsIso hU.fromSpec := by rw [IsAffineOpen.fromSpec_top]; infer_instance
  exact Scheme.Modules.isIso_of_isIso_restrictFunctor_map hU.fromSpec f

/-- On an affine scheme, a quasi-coherent submodule of a quasi-coherent module `N` containing every
global section of `N` is all of `N`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_of_mono_of_surjective_sectionsFunctor_map_top
    [IsAffine X] {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (i : M ⟶ N) [Mono i]
    (hi : Function.Surjective ((sectionsFunctor ⊤).map i).hom) : IsIso i := by
  -- Evaluation of sheaves of modules preserves limits, hence monomorphisms. Its instances are
  -- stated for `SheafOfModules X.ringCatSheaf`, which instance search does not unfold
  -- `X.Modules` to.
  have : Mono (C := SheafOfModules X.ringCatSheaf) i := inferInstanceAs (Mono (C := X.Modules) i)
  have := (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map_mono i
  exact isIso_of_bijective_sectionsFunctor_map_top i
    ⟨(ModuleCat.mono_iff_injective _).mp this, hi⟩

end TauCeti.AlgebraicGeometry
