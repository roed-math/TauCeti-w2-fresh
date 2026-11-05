/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Order.Filter.Germ.Basic

/-!
# Algebras of germs

Germs of algebra-valued functions inherit the pointwise scalar algebra structure.
The projection from functions to germs is an algebra homomorphism. This lets subalgebras
of germs retain the same scalars as their representatives. Polynomial evaluation and finite sums
are computed pointwise on representatives.
-/

public section

namespace Filter.Germ

variable {α R A : Type*} {l : Filter α}
  [CommSemiring R] [Semiring A] [Algebra R A]

/-- The pointwise algebra structure on germs, compatible with their existing scalar action. -/
instance algebra : Algebra R (Germ l A) where
  algebraMap := (coeRingHom l).comp (algebraMap R (α → A))
  commutes' r g := inductionOn g fun f ↦
    (congrArg (fun f : α → A ↦ (f : Germ l A)) (Algebra.commutes r f))
  smul_def' r g := inductionOn g fun f ↦
    (congrArg (fun f : α → A ↦ (f : Germ l A)) (Algebra.smul_def r f))

/-- The scalar map to germs is represented by the pointwise scalar map. -/
theorem algebraMap_eq (r : R) :
    algebraMap R (Germ l A) r = (fun _ : α ↦ algebraMap R A r : Germ l A) := (rfl)

/-- Projection of algebra-valued functions to their germs. -/
def coeAlgHom (l : Filter α) : (α → A) →ₐ[R] Germ l A where
  __ := coeRingHom l
  commutes' _ := rfl

@[simp]
theorem coeAlgHom_apply (f : α → A) : coeAlgHom (R := R) l f = (f : Germ l A) := (rfl)

/-- Evaluating a polynomial at the germ of `f` gives the germ of the pointwise evaluations. -/
theorem algebra_aeval_coe (f : α → A) (p : Polynomial R) :
    Polynomial.aeval (f : Germ l A) p = (fun x ↦ Polynomial.aeval (f x) p : Germ l A) := by
  rw [← coeAlgHom_apply (R := R), Polynomial.aeval_algHom_apply, coeAlgHom_apply]
  congr 1
  ext x
  exact (Polynomial.aeval_algHom_apply (Pi.evalAlgHom R (fun _ ↦ A) x) f p).symm

end Filter.Germ

namespace Filter.Germ

variable {α ι M : Type*} {l : Filter α} [AddCommMonoid M]

/-- The germ of a finite sum of functions is the sum of their germs. -/
@[simp, norm_cast]
theorem coe_sum (s : Finset ι) (g : ι → α → M) :
    ((∑ i ∈ s, g i : α → M) : Germ l M) = ∑ i ∈ s, (g i : Germ l M) :=
  map_sum (coeAddHom l) g s

end Filter.Germ
