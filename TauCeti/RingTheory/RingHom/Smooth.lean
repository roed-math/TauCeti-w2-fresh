/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RingHom.Smooth

/-!
# Lifting along nilpotent extensions for formally smooth ring homomorphisms

Mathlib states the infinitesimal lifting property of a formally smooth algebra with algebra
homomorphisms (`Algebra.FormallySmooth.liftOfSurjective`). This file restates it for a formally
smooth ring homomorphism `φ : R →+* A`, with the structure maps as explicit ring homomorphisms; this
is the form in which it is used for morphisms of affine schemes.
-/

public section

namespace RingHom

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]

/-- For a formally smooth `φ : R →+* A`, a surjection `π : B →+* C` with nilpotent kernel and ring
maps `η : R →+* B`, `α : A →+* C` with `α ∘ φ = π ∘ η`, some `l : A →+* B` has `π ∘ l = α` and
`l ∘ φ = η`. -/
theorem FormallySmooth.exists_lift {φ : R →+* A} (hφ : φ.FormallySmooth) (η : R →+* B)
    (π : B →+* C) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (α : A →+* C) (h : α.comp φ = π.comp η) : ∃ l : A →+* B, π.comp l = α ∧ l.comp φ = η := by
  algebraize [φ, η]
  let : Algebra R C := (π.comp η).toAlgebra
  let π' : B →ₐ[R] C := { π with commutes' := fun _ ↦ rfl }
  let α' : A →ₐ[R] C := { α with commutes' := fun r ↦ congr($h r) }
  exact ⟨Algebra.FormallySmooth.liftOfSurjective α' π' hπ hker,
    RingHom.ext (Algebra.FormallySmooth.liftOfSurjective_apply α' π' hπ hker),
    RingHom.ext (Algebra.FormallySmooth.liftOfSurjective α' π' hπ hker).commutes⟩

end RingHom
