/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RingHom.Unramified

/-!
# Uniqueness of lifts along nilpotent extensions for formally unramified ring homomorphisms

Mathlib states the uniqueness of infinitesimal lifts for a formally unramified algebra with algebra
homomorphisms (`Algebra.FormallyUnramified.ext'`). This file restates it for a formally unramified
ring homomorphism `φ : R →+* A`, with the structure maps as explicit ring homomorphisms; this is
the form in which it is used for morphisms of affine schemes.
-/

public section

namespace RingHom

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]

/-- For a formally unramified `φ : R →+* A`, two ring maps `A →+* B` that agree on `R` and after
composing with a ring map `π : B →+* C` with nilpotent kernel are equal. -/
theorem FormallyUnramified.ext {φ : R →+* A} (hφ : φ.FormallyUnramified) (π : B →+* C)
    (hker : IsNilpotent (RingHom.ker π)) {l₁ l₂ : A →+* B} (hφ' : l₁.comp φ = l₂.comp φ)
    (hπ : π.comp l₁ = π.comp l₂) : l₁ = l₂ := by
  algebraize [φ, l₂.comp φ]
  let g₁ : A →ₐ[R] B := { l₁ with commutes' := fun r ↦ congr($hφ' r) }
  let g₂ : A →ₐ[R] B := { l₂ with commutes' := fun _ ↦ rfl }
  exact congr(($(Algebra.FormallyUnramified.ext' π hker g₁ g₂ fun x ↦ congr($hπ x))).toRingHom)

end RingHom
