/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import TauCeti.RingTheory.Derivation.ToSquareZero

/-!
# Lifts along the spectrum of a square-zero extension

Let `I` be an ideal of `B` and let `A → B ⧸ I` be a map of `R`-algebras. The lifting problem of
`Spec (B ⧸ I) ⟶ Spec A` along `Spec (B ⧸ I) ⟶ Spec B` over `Spec R` is the algebraic one: its lifts
(Mathlib's `CommSq.LiftStruct`) are the `R`-algebra lifts `A →ₐ[R] B` of `A →ₐ[R] B ⧸ I`, that is,
`Ideal.LiftOfQuotient I R A`. When `I ^ 2 = ⊥` these form a torsor under `Der_R(A, I)`
(`Ideal.derivationToSquareZeroAddTorsor`), the affine case of Stacks, Lemma 37.9.5 (04FJ).

## Main definitions

* `TauCeti.AlgebraicGeometry.SpecMap_quotient_commSq`: the square of spectra of
  `R → A → B ⧸ I ← B`.
* `TauCeti.AlgebraicGeometry.SpecMap_quotient_liftStructEquiv`: its lifts are the `R`-algebra
  lifts `A →ₐ[R] B` of `A →ₐ[R] B ⧸ I`.

## References

* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ).
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (I : Ideal B) [Algebra A (B ⧸ I)] [IsScalarTower R A (B ⧸ I)]

/-- The square of spectra of the maps `R → A → B ⧸ I` and `R → B → B ⧸ I`. -/
theorem SpecMap_quotient_commSq :
    CommSq (Spec.map (CommRingCat.ofHom (algebraMap A (B ⧸ I))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  refine ⟨?_⟩
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  change algebraMap A (B ⧸ I) (algebraMap R A r) = Ideal.Quotient.mk I (algebraMap R B r)
  rw [← IsScalarTower.algebraMap_apply, Ideal.Quotient.mk_algebraMap]

/-- The lifts of `Spec (B ⧸ I) ⟶ Spec A` along `Spec (B ⧸ I) ⟶ Spec B` over `Spec R` are the
`R`-algebra lifts `A →ₐ[R] B` of `A →ₐ[R] B ⧸ I`: a lift `l` corresponds to the ring map
`Spec.preimage l`. -/
noncomputable def SpecMap_quotient_liftStructEquiv :
    (SpecMap_quotient_commSq (R := R) (A := A) I).LiftStruct ≃ Ideal.LiftOfQuotient I R A where
  toFun l := ⟨
    { (Spec.preimage l.l).hom with
      commutes' r := by
        have : CommRingCat.ofHom (algebraMap R A) ≫ Spec.preimage l.l =
            CommRingCat.ofHom (algebraMap R B) := Spec.map_injective <| by
          rw [Spec.map_comp, Spec.map_preimage]
          exact l.fac_right
        exact congr($this r) },
    AlgHom.ext fun x ↦ by
      have : Spec.preimage l.l ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) =
          CommRingCat.ofHom (algebraMap A (B ⧸ I)) := Spec.map_injective <| by
        rw [Spec.map_comp, Spec.map_preimage]
        exact l.fac_left
      exact congr($this x)⟩
  invFun f :=
    { l := Spec.map (CommRingCat.ofHom f.1.toRingHom)
      fac_left := by
        rw [← Spec.map_comp]
        congr 1
        ext x
        exact f.mk_apply x
      fac_right := by
        rw [← Spec.map_comp]
        congr 1
        ext r
        exact f.1.commutes r }
  left_inv l := CommSq.LiftStruct.ext <| by
    change Spec.map (CommRingCat.ofHom (Spec.preimage l.l).hom) = l.l
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  right_inv f := Subtype.ext <| AlgHom.ext fun x ↦ by
    change (Spec.preimage (Spec.map (CommRingCat.ofHom f.1.toRingHom))).hom x = f.1 x
    rw [Spec.preimage_map]
    rfl

@[simp]
theorem SpecMap_quotient_liftStructEquiv_apply_apply
    (l : (SpecMap_quotient_commSq (R := R) (A := A) I).LiftStruct) (x : A) :
    (SpecMap_quotient_liftStructEquiv I l).1 x = (Spec.preimage l.l).hom x :=
  (rfl)

@[simp]
theorem SpecMap_quotient_liftStructEquiv_symm_apply_l (f : Ideal.LiftOfQuotient I R A) :
    ((SpecMap_quotient_liftStructEquiv I).symm f).l =
      Spec.map (CommRingCat.ofHom f.1.toRingHom) :=
  (rfl)

end TauCeti.AlgebraicGeometry
