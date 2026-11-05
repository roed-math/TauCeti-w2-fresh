/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Morphisms of sheaves of modules on sections, as linear maps

A morphism `φ : M ⟶ N` of `𝒪_X`-modules acts on sections over an open `U` by `φ.app U`, a morphism
of abelian groups which is `Γ(X, U)`-linear (`AlgebraicGeometry.Scheme.Modules.Hom.app_smul`). This
file packages it as the `Γ(X, U)`-linear map `AlgebraicGeometry.Scheme.Modules.Hom.appLinear φ U`,
so that its range and its cokernel are `Γ(X, U)`-modules.
-/

public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A morphism of `𝒪_X`-modules acts on sections over `U` by a `Γ(X, U)`-linear map. -/
def Hom.appLinear (φ : M ⟶ N) (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) where
  toFun := φ.app U
  map_add' := map_add _
  map_smul' := Hom.app_smul φ

@[simp]
lemma Hom.appLinear_apply (φ : M ⟶ N) (U : X.Opens) (x : Γ(M, U)) :
    φ.appLinear U x = φ.app U x :=
  (rfl)

end AlgebraicGeometry.Scheme.Modules

end
