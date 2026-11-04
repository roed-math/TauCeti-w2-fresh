/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Defs
public import Mathlib.RingTheory.Derivation.ToSquareZero
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# The torsor of lifts along a square-zero extension

Let `I` be an ideal of `B` with `I ^ 2 = ⊥`, and let `A → B ⧸ I` be a map of `R`-algebras. The
`R`-algebra lifts `A →ₐ[R] B` of it, if there are any, form a torsor under the `R`-derivations
`A → I`: a derivation `d` sends a lift `f` to `f + d`, and two lifts differ by the derivation
`f₁ - f₂`. Here `I` is an `A`-module through `A → B ⧸ I`, as a square-zero ideal is a
`B ⧸ I`-module. Unlike Mathlib's `derivationToSquareZeroEquivLift`, no lift is singled out by an
algebra structure `A → B`; this is the form in which lifts are glued along a first-order
thickening. It is the affine case of the torsor of lifts of Stacks, Lemma 37.9.5 (04FJ), with
`Hom_A(Ω_{A/R}, I) = Der_R(A, I)`.

## Main definitions

* `Ideal.moduleOfSqEqBot`: a square-zero ideal `I` of `B` is an `A`-module through `A → B ⧸ I`.
* `Ideal.LiftOfQuotient I R A`: the lifts `A →ₐ[R] B` of the structure map `A →ₐ[R] B ⧸ I`.
* `Ideal.derivationToSquareZeroAddTorsor`: for `I ^ 2 = ⊥`, the lifts form a torsor under
  `Derivation R A I`.

## Main results

* `Ideal.nonempty_liftOfQuotient`: for `A` formally smooth over `R`, a lift exists.
* `Ideal.subsingleton_liftOfQuotient`: for `A` formally unramified over `R`, it is unique.

## References

* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ).
-/

public section

namespace Ideal

variable {B : Type*} [CommRing B] {I : Ideal B}

/-- The product of two elements of a square-zero ideal vanishes. -/
theorem coe_mul_coe_of_sq_eq_bot (hI : I ^ 2 = ⊥) (m n : I) : (m : B) * n = 0 := by
  rw [← mem_bot, ← hI, sq]
  exact mul_mem_mul m.2 n.2

/-- A square-zero ideal is annihilated by itself. -/
theorem isTorsionBySet_self_of_sq_eq_bot (hI : I ^ 2 = ⊥) : Module.IsTorsionBySet B I I :=
  fun m a ↦ Subtype.ext (coe_mul_coe_of_sq_eq_bot hI a m)

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra R B] [Algebra A (B ⧸ I)]
  [IsScalarTower R A (B ⧸ I)]

variable (A) in
/-- A square-zero ideal `I` of `B` is an `A`-module through `A → B ⧸ I`: `a` acts as multiplication
by any `b : B` with `b ≡ a` modulo `I` (`coe_smul_of_sq_eq_bot`). -/
abbrev moduleOfSqEqBot (hI : I ^ 2 = ⊥) : Module A I :=
  letI := (isTorsionBySet_self_of_sq_eq_bot hI).module
  Module.compHom I (algebraMap A (B ⧸ I))

/-- Under `moduleOfSqEqBot`, `a • m = b * m` for any `b ≡ a` modulo `I`. -/
theorem coe_smul_of_sq_eq_bot (hI : I ^ 2 = ⊥) {a : A} {b : B}
    (hb : Ideal.Quotient.mk I b = algebraMap A (B ⧸ I) a) (m : I) :
    letI := moduleOfSqEqBot A hI
    ((a • m : I) : B) = b * m := by
  let := (isTorsionBySet_self_of_sq_eq_bot hI).module
  change ((algebraMap A (B ⧸ I) a • m : I) : B) = _
  rw [← hb]
  rfl

/-- The `A`-module structure `moduleOfSqEqBot` on `I` is compatible with its `R`-module
structure. -/
theorem isScalarTower_of_sq_eq_bot (hI : I ^ 2 = ⊥) :
    letI := moduleOfSqEqBot A hI
    IsScalarTower R A I := by
  let := moduleOfSqEqBot A hI
  refine ⟨fun r a m ↦ Subtype.ext ?_⟩
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (algebraMap A (B ⧸ I) a)
  have hb' : Ideal.Quotient.mk I (algebraMap R B r * b) = algebraMap A (B ⧸ I) (r • a) := by
    rw [map_mul, hb, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
      Ideal.Quotient.mk_algebraMap]
  rw [coe_smul_of_sq_eq_bot hI hb', Submodule.coe_smul_of_tower, coe_smul_of_sq_eq_bot hI hb,
    Algebra.smul_def, mul_assoc]

variable (R A I) in
/-- The lifts `A →ₐ[R] B` of the structure map `A →ₐ[R] B ⧸ I`. -/
abbrev LiftOfQuotient :=
  { f : A →ₐ[R] B // (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I) }

/-- A lift reduces to the structure map modulo `I`. -/
theorem LiftOfQuotient.mk_apply (f : LiftOfQuotient I R A) (x : A) :
    Ideal.Quotient.mk I (f.1 x) = algebraMap A (B ⧸ I) x :=
  DFunLike.congr_fun f.2 x

/-- For a square-zero ideal `I` of `B`, the lifts `A →ₐ[R] B` of the structure map `A →ₐ[R] B ⧸ I`,
when there is one, form a torsor under the `R`-derivations `A → I`, where `I` is an `A`-module
through `B ⧸ I` (`moduleOfSqEqBot`): a derivation `d` sends a lift `f` to `f + d`, and two lifts
differ by the derivation `f₁ - f₂`. -/
@[expose, reducible]
def derivationToSquareZeroAddTorsor (hI : I ^ 2 = ⊥) [Nonempty (LiftOfQuotient I R A)] :
    letI := moduleOfSqEqBot A hI
    AddTorsor (Derivation R A I) (LiftOfQuotient I R A) :=
  letI := moduleOfSqEqBot A hI
  haveI : IsScalarTower R A I := isScalarTower_of_sq_eq_bot hI
  { vadd d f := ⟨
      { toFun x := d x + f.1 x
        map_one' := by simp
        map_mul' x y := by
          simp only [Derivation.leibniz, Submodule.coe_add, map_mul,
            coe_smul_of_sq_eq_bot hI (f.mk_apply x), coe_smul_of_sq_eq_bot hI (f.mk_apply y)]
          linear_combination (coe_mul_coe_of_sq_eq_bot hI (d x) (d y)).symm
        map_zero' := by simp
        map_add' x y := by simp [add_add_add_comm]
        commutes' r := by simp },
      AlgHom.ext fun x ↦ by
        change Ideal.Quotient.mk I ((d x : B) + f.1 x) = algebraMap A (B ⧸ I) x
        rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 (d x).2, zero_add, f.mk_apply]⟩
    zero_vadd f := Subtype.ext <| AlgHom.ext fun x ↦ by
      change ((0 : Derivation R A I) x : B) + f.1 x = f.1 x
      simp
    add_vadd d₁ d₂ f := Subtype.ext <| AlgHom.ext fun x ↦ by
      change ((d₁ + d₂) x : B) + f.1 x = d₁ x + (d₂ x + f.1 x)
      simp [add_assoc]
    vsub f₁ f₂ := Derivation.mk' (diffToIdealOfQuotientCompEq I f₁.1 f₂.1 (f₁.2.trans f₂.2.symm))
      fun x y ↦ Subtype.ext <| by
        simp only [diffToIdealOfQuotientCompEq_apply, map_mul, Submodule.coe_add,
          coe_smul_of_sq_eq_bot hI (f₁.mk_apply x), coe_smul_of_sq_eq_bot hI (f₂.mk_apply y)]
        ring
    nonempty := ‹_›
    vsub_vadd' f₁ f₂ := Subtype.ext <| AlgHom.ext fun x ↦ by
      change (f₁.1 x - f₂.1 x) + f₂.1 x = f₁.1 x
      exact sub_add_cancel _ _
    vadd_vsub' d f := Derivation.ext fun x ↦ Subtype.ext <| by
      change ((d x : B) + f.1 x) - f.1 x = d x
      exact add_sub_cancel_right _ _ }

/-- A derivation `d` acts on a lift `f` by `x ↦ d x + f x`. -/
theorem derivationToSquareZeroAddTorsor_vadd_apply (hI : I ^ 2 = ⊥)
    [Nonempty (LiftOfQuotient I R A)] (d : letI := moduleOfSqEqBot A hI; Derivation R A I)
    (f : LiftOfQuotient I R A) (x : A) :
    letI := moduleOfSqEqBot A hI
    letI : AddTorsor (Derivation R A I) (LiftOfQuotient I R A) := derivationToSquareZeroAddTorsor hI
    (d +ᵥ f : LiftOfQuotient I R A).1 x = d x + f.1 x :=
  rfl

/-- Two lifts `f₁`, `f₂` differ by the derivation `x ↦ f₁ x - f₂ x`. -/
theorem derivationToSquareZeroAddTorsor_vsub_apply (hI : I ^ 2 = ⊥)
    [Nonempty (LiftOfQuotient I R A)] (f₁ f₂ : LiftOfQuotient I R A) (x : A) :
    letI := moduleOfSqEqBot A hI
    letI : AddTorsor (Derivation R A I) (LiftOfQuotient I R A) := derivationToSquareZeroAddTorsor hI
    ((f₁ -ᵥ f₂ : Derivation R A I) x : B) = f₁.1 x - f₂.1 x :=
  rfl

/-- If `A` is formally smooth over `R`, the structure map `A →ₐ[R] B ⧸ I` lifts to `B`. -/
theorem nonempty_liftOfQuotient [Algebra.FormallySmooth R A] (hI : I ^ 2 = ⊥) :
    Nonempty (LiftOfQuotient I R A) :=
  let ⟨f, hf⟩ := Algebra.FormallySmooth.exists_lift I ⟨2, hI⟩ (IsScalarTower.toAlgHom R A (B ⧸ I))
  ⟨⟨f, hf⟩⟩

/-- If `A` is formally unramified over `R`, the structure map `A →ₐ[R] B ⧸ I` has at most one
lift to `B`. -/
theorem subsingleton_liftOfQuotient [Algebra.FormallyUnramified R A] (hI : I ^ 2 = ⊥) :
    Subsingleton (LiftOfQuotient I R A) :=
  ⟨fun f₁ f₂ ↦ Subtype.ext <| Algebra.FormallyUnramified.ext I ⟨2, hI⟩ fun x ↦ by
    rw [f₁.mk_apply, f₂.mk_apply]⟩

end Ideal
