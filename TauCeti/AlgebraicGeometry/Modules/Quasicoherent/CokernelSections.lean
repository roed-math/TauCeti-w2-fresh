/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
public import TauCeti.AlgebraicGeometry.Modules.AppLinear
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels

/-!
# Sections of a cokernel over an affine open

Sections over an open `U` are left exact: a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of
`𝒪_X`-modules gives an exact sequence `0 ⟶ Γ(M₁, U) ⟶ Γ(M₂, U) ⟶ Γ(M₃, U)`
(`AlgebraicGeometry.Scheme.Modules.exact_app_of_shortExact`). When `M₂` and `M₃` are
quasi-coherent and `U` is affine, the last map is also surjective
(`AlgebraicGeometry.Scheme.Modules.Hom.app_surjective_of_epi_of_isAffineOpen`). So for a
monomorphism `f : M ⟶ N` of quasi-coherent sheaves the sections of `cokernel f` over an affine
open `U` are the quotient of `Γ(N, U)` by the image of `Γ(M, U)`
(`AlgebraicGeometry.Scheme.Modules.cokernelSectionsEquiv`).
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **Sections are left exact.** For a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of
`𝒪_X`-modules and any open `U`, the sections of `M₁` over `U` are exactly the sections of `M₂`
over `U` that die in `M₃`. -/
theorem exact_app_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (U : X.Opens) : Function.Exact (S.f.app U) (S.g.app U) := by
  let F := SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U)
  have : F.Additive := ⟨rfl⟩
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F).mp inferInstance S hS).1

variable {M N : X.Modules} (f : M ⟶ N) [Mono f]

/-- The sections over `U` of the image of a monomorphism `f : M ⟶ N` are the sections of `N` over
`U` that die in `cokernel f`. -/
theorem range_appLinear_eq_ker_appLinear_cokernel_π (U : X.Opens) :
    LinearMap.range (f.appLinear U) = LinearMap.ker ((cokernel.π f).appLinear U) := by
  have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
    { exact := ShortComplex.exact_cokernel f }
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, Hom.appLinear_apply]
  exact (exact_app_of_shortExact hS U x).symm

variable [M.IsQuasicoherent] [N.IsQuasicoherent] {U : X.Opens}

/-- **Sections of a cokernel over an affine open.** For a monomorphism `f : M ⟶ N` of
quasi-coherent sheaves and an affine open `U`, the sections of `cokernel f` over `U` are the
quotient of `Γ(N, U)` by the image of `Γ(M, U)`, through the projection `N ⟶ cokernel f`. -/
noncomputable def cokernelSectionsEquiv (hU : IsAffineOpen U) :
    (Γ(N, U) ⧸ LinearMap.range (f.appLinear U)) ≃ₗ[Γ(X, U)] Γ(cokernel f, U) :=
  (Submodule.quotEquivOfEq _ _ (range_appLinear_eq_ker_appLinear_cokernel_π f U)).trans
    (LinearMap.quotKerEquivOfSurjective _ (by
      intro y
      obtain ⟨x, hx⟩ := Hom.app_surjective_of_epi_of_isAffineOpen (cokernel.π f) U hU y
      exact ⟨x, by rwa [Hom.appLinear_apply]⟩))

@[simp]
theorem cokernelSectionsEquiv_mk (hU : IsAffineOpen U) (x : Γ(N, U)) :
    cokernelSectionsEquiv f hU (Submodule.Quotient.mk x) = (cokernel.π f).app U x := by
  rw [cokernelSectionsEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact Hom.appLinear_apply _ _ _

end AlgebraicGeometry.Scheme.Modules
