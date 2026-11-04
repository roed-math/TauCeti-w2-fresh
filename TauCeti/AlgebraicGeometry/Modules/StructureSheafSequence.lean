/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# The structure-sheaf sequence of a dominant morphism

For a quasi-compact, scheme-theoretically dominant morphism `f : X ⟶ Y`, the map
`𝒪_Y → f_* 𝒪_X` is injective. Together with its cokernel it forms a short exact sequence
of sheaves of modules. If `f` is affine, the cokernel is quasicoherent.

For a normalization this cokernel measures the failure of regular functions on the
normalization to descend. Its exact sequence is the input to the cohomological comparison
between a curve and its normalization. Quasi-compactness suffices for injectivity, and no
finiteness or Noetherian hypothesis is imposed on the affine cokernel result.

The sequence is Mathlib's `ShortComplex.cokernelSequence`, and its first map is Mathlib's
`SheafOfModules.unitToPushforwardObjUnit`. Its short exactness follows from the generic
`TauCeti.cokernelSequence_shortExact` applied to that monomorphism. Since sections are left exact
(`AlgebraicGeometry.Scheme.Modules.exact_app_of_exact`) and an epimorphism of quasicoherent
sheaves is surjective on sections over affine opens, the sections of the cokernel over an affine
open `U` of `Y` are the cokernel of `Γ(Y, U) → Γ(X, f ⁻¹ᵁ U)`
(`AlgebraicGeometry.Scheme.Hom.cokernelUnitToPushforwardObjUnitSectionsEquiv`).

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise IV.1.8 (the normalization sequence).
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open TauCeti.AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- For a quasi-compact scheme-theoretically dominant morphism, pullback of regular functions
is a monomorphism of sheaves of modules. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.mono_unitToPushforwardObjUnit
    [QuasiCompact f] [IsSchemeTheoreticallyDominant f] :
    Mono (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply _root_.PresheafOfModules.mono_of_injective
  intro U
  -- The component of the module-sheaf unit is the structure-presheaf map `f.app`.
  exact f.app_injective U.unop

/-- For a quasi-compact quasi-separated morphism, the direct image `f_* 𝒪_X` of the structure
sheaf is quasicoherent. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.isQuasicoherent_pushforward_obj_unit
    [QuasiCompact f] [QuasiSeparated f] :
    ((SheafOfModules.pushforward f.toRingCatSheafHom).obj
      (SheafOfModules.unit X.ringCatSheaf)).IsQuasicoherent := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    AlgebraicGeometry.isQuasicoherent_structureSheaf X
  simpa only [Scheme.Modules.pushforward] using
    Scheme.Modules.isQuasicoherent_pushforward (SheafOfModules.unit X.ringCatSheaf) f

/-- For an affine morphism the quotient of the direct image of the structure sheaf by the
image of the base's structure sheaf is quasicoherent. Injectivity is not required. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.isQuasicoherent_cokernel_unitToPushforwardObjUnit
    [IsAffineHom f] :
    (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_cokernel _

/-- **Sections of the cokernel over an affine open.** Let `f : X ⟶ Y` be affine and
scheme-theoretically dominant, and `U` an affine open of `Y`. The sections over `U` of the
cokernel of `𝒪_Y → f_* 𝒪_X` are the cokernel `Γ(X, f ⁻¹ᵁ U) / Γ(Y, U)` of `f.app U`, as
`Γ(Y, U)`-modules. -/
def _root_.AlgebraicGeometry.Scheme.Hom.cokernelUnitToPushforwardObjUnitSectionsEquiv
    [IsAffineHom f] [IsSchemeTheoreticallyDominant f] (U : Y.affineOpens) :
    letI := (f.app U).hom.toAlgebra
    (Γ(X, f ⁻¹ᵁ U) ⧸ (1 : Submodule Γ(Y, U) Γ(X, f ⁻¹ᵁ U))) ≃ₗ[Γ(Y, U)]
      Γ(cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom), U) :=
  letI := (f.app U).hom.toAlgebra
  -- The sections of `f_* 𝒪_X` over `U` are `Γ(X, f ⁻¹ᵁ U)`, with `Γ(Y, U)` acting through `f`.
  let π := cokernel.π (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
  have : Epi (C := Y.Modules) π := coequalizer.π_epi
  let g : Γ(X, f ⁻¹ᵁ U) →ₗ[Γ(Y, U)]
      Γ(cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom), U) :=
    { toFun b := Scheme.Modules.Hom.app π U b
      map_add' x y := map_add (Scheme.Modules.Hom.app π U).hom x y
      map_smul' r x := Scheme.Modules.Hom.app_smul π r x }
  have hker : LinearMap.ker g = 1 := by
    ext b
    rw [LinearMap.mem_ker, Submodule.mem_one]
    change Scheme.Modules.Hom.app π U b = 0 ↔ _
    exact Scheme.Modules.exact_app_of_exact (X := Y) (S := ShortComplex.cokernelSequence
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))
      (ShortComplex.cokernelSequence_exact _) U b
  (Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivOfSurjective
    (Scheme.Modules.Hom.app_surjective_of_epi_of_isAffineOpen π U U.2))

/-- `AlgebraicGeometry.Scheme.Hom.cokernelUnitToPushforwardObjUnitSectionsEquiv` sends the class
of `b : Γ(X, f ⁻¹ᵁ U)` to its image in the cokernel. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.cokernelUnitToPushforwardObjUnitSectionsEquiv_mk
    [IsAffineHom f] [IsSchemeTheoreticallyDominant f] (U : Y.affineOpens) (b : Γ(X, f ⁻¹ᵁ U)) :
    letI := (f.app U).hom.toAlgebra
    f.cokernelUnitToPushforwardObjUnitSectionsEquiv U (Submodule.Quotient.mk b) =
      Scheme.Modules.Hom.app
        (cokernel.π (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) U b :=
  (rfl)

end

end TauCeti
