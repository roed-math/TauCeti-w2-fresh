/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.GradedAlgebra.Sections
public import TauCeti.CategoryTheory.GradedObject.Veronese
public import TauCeti.RingTheory.GradedAlgebra.VeroneseSubalgebra

/-!
# Graded sections of the Veronese subalgebra of a graded algebra

Let `A = ⨁ₙ Aₙ` be a graded algebra on a scheme `X`, let `d : ℕ` and let
`A^{(d)} = ⨁ₖ A_{dk}` be its `d`-th Veronese subalgebra (`CategoryTheory.CommMon.veronese`).
Over an open `U` of `X`, the graded ring of sections `⨁ₖ Γ(A_{dk}, U)` of `A^{(d)}` maps to the
graded ring of sections `⨁ₙ Γ(Aₙ, U)` of `A` by placing the degree-`k` summand in degree `d k`.
For `d ≠ 0` this identifies the graded sections of `A^{(d)}` with the Veronese subalgebra of the
graded sections of `A`, degree by degree and compatibly with restriction. This is the
affine-local input for comparing the relative `Proj` of `A^{(d)}` with that of `A`
(Stacks Project, Lemma 0B5J).

## Main declarations

* `CategoryTheory.CommMon.veroneseSectionsAlgHom`: the `Γ(X, U)`-algebra homomorphism
  `⨁ₖ Γ(A_{dk}, U) → ⨁ₙ Γ(Aₙ, U)`, sending the degree-`k` summand to degree `d k`;
* `CategoryTheory.CommMon.veroneseSectionsAlgHom_restrictGradedSections`: it commutes with
  restriction of sections;
* `CategoryTheory.CommMon.veroneseSectionsEquiv`: for `d ≠ 0`, the isomorphism of
  `Γ(X, U)`-algebras from `⨁ₖ Γ(A_{dk}, U)` onto the Veronese subalgebra of `⨁ₙ Γ(Aₙ, U)`,
  carrying the degree-`k` summand onto the degree-`k` part of the Veronese grading
  (`veroneseSectionsEquiv_mem_veroneseGrading`).
-/

public section

open CategoryTheory MonoidalCategory Opposite DirectSum

namespace TauCeti

open CategoryTheory.CommMon
open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}} (A : CommMon (GradedObject ℕ X.Modules)) (d : ℕ)

/-- The components of the Veronese subalgebra of a graded algebra of quasicoherent modules are
quasicoherent. -/
instance _root_.CategoryTheory.CommMon.isQuasicoherent_veronese_X
    [∀ n, (A.X n).IsQuasicoherent] (k : ℕ) : ((A.veronese d).X k).IsQuasicoherent :=
  inferInstanceAs (A.X (d * k)).IsQuasicoherent

variable (U : X.Opens)

/-- Transporting a homogeneous section along an equality of degrees does not change it as an
element of the graded ring of sections. -/
private lemma of_eqToHom_app {m n : ℕ} (h : m = n) (x : Γ(A.X m, U)) :
    DirectSum.of (fun n ↦ Γ(A.X n, U)) n ((eqToHom (congrArg A.X h)).app U x) =
      DirectSum.of (fun n ↦ Γ(A.X n, U)) m x := by
  subst h
  rfl

/-- Placing the unit of the graded sections of the Veronese subalgebra in degree `d · 0` gives the
unit of the graded sections of `A`. -/
private lemma of_veronese_gOne :
    DirectSum.of (fun n ↦ Γ(A.X n, U)) (d * 0)
        (GradedMonoid.GOne.one (A := fun k ↦ Γ((A.veronese d).X k, U))) = 1 := by
  rw [sections_gOne_def]
  refine (congrArg (fun φ : 𝟙_ X.Modules ⟶ (A.veronese d).X 0 ↦
    DirectSum.of (fun n ↦ Γ(A.X n, U)) (d * 0)
      (φ.app U (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) 1)))
    (Mon.veronese_one A.toMon d)).trans ?_
  exact (of_eqToHom_app A U (mul_zero d).symm
    (A.toMon.one.app U (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) 1))).trans
      ((congrArg _ (sections_gOne_def A U).symm).trans (DirectSum.of_zero_one _))

/-- Placing the product of homogeneous sections of the Veronese subalgebra in degree `d (i + j)`
gives the product of the sections placed in degrees `d i` and `d j`. -/
private lemma of_veronese_gMul {i j : ℕ} (x : Γ((A.veronese d).X i, U))
    (y : Γ((A.veronese d).X j, U)) :
    DirectSum.of (fun n ↦ Γ(A.X n, U)) (d * (i + j))
        (GradedMonoid.GMul.mul (A := fun k ↦ Γ((A.veronese d).X k, U)) x y) =
      DirectSum.of (fun n ↦ Γ(A.X n, U)) (d * i) x *
        DirectSum.of (fun n ↦ Γ(A.X n, U)) (d * j) y := by
  rw [sections_gMul_def,
    DirectSum.of_mul_of (A := fun n ↦ Γ(A.X n, U)) (i := d * i) (j := d * j) x y,
    sections_gMul_def A U (i := d * i) (j := d * j) x y]
  refine (congrArg (fun φ : (A.veronese d).X i ⊗ (A.veronese d).X j ⟶ (A.veronese d).X (i + j) ↦
    DirectSum.of (fun n ↦ Γ(A.X n, U)) (d * (i + j))
      (φ.app U (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) _ _ (x ⊗ₜ y))))
    (Mon.veronese_mul A.toMon d i j)).trans ?_
  exact of_eqToHom_app A U (mul_add d i j).symm
    ((A.toMon.mul (d * i) (d * j)).app U
      (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) _ _ (x ⊗ₜ y)))

/-- The graded ring of sections of the `d`-th Veronese subalgebra maps to the graded ring of
sections of `A`, sending the degree-`k` summand `Γ(A_{dk}, U)` to degree `d k`
(`veroneseSectionsAlgHom_of`). -/
def _root_.CategoryTheory.CommMon.veroneseSectionsAlgHom :
    (⨁ k, Γ((A.veronese d).X k, U)) →ₐ[Γ(X, U)] ⨁ n, Γ(A.X n, U) :=
  DirectSum.toAlgebra _ _
    (fun k ↦ (DirectSum.lof _ ℕ (fun n ↦ Γ(A.X n, U)) (d * k) :
      Γ((A.veronese d).X k, U) →ₗ[Γ(X, U)] _))
    (of_veronese_gOne A d U) (fun {_ _} x y ↦ of_veronese_gMul A d U x y)

/-- The homomorphism `veroneseSectionsAlgHom` places a homogeneous section of degree `k` of the
Veronese subalgebra in degree `d k`. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.veroneseSectionsAlgHom_of (k : ℕ)
    (x : Γ((A.veronese d).X k, U)) :
    A.veroneseSectionsAlgHom d U (DirectSum.of (fun k ↦ Γ((A.veronese d).X k, U)) k x) =
      DirectSum.of (fun n ↦ Γ(A.X n, U)) (d * k) x :=
  DirectSum.toSemiring_of (A := fun k ↦ Γ((A.veronese d).X k, U)) _ (of_veronese_gOne A d U)
    (fun {_ _} x y ↦ of_veronese_gMul A d U x y)
    k x

/-- The degree-`d k` component of the image of `x` under `veroneseSectionsAlgHom` is the
degree-`k` component of `x`. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.veroneseSectionsAlgHom_apply_mul (hd : d ≠ 0)
    (x : ⨁ k, Γ((A.veronese d).X k, U)) (k : ℕ) :
    A.veroneseSectionsAlgHom d U x (d * k) = x k := by
  classical
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero]; rfl
  | of j y =>
    rw [veroneseSectionsAlgHom_of A d U j y]
    obtain rfl | hjk := eq_or_ne j k
    · exact (DirectSum.of_eq_same (β := fun n ↦ Γ(A.X n, U)) (d * j) y).trans
        (DirectSum.of_eq_same (β := fun k ↦ Γ((A.veronese d).X k, U)) j y).symm
    · exact (DirectSum.of_eq_of_ne (β := fun n ↦ Γ(A.X n, U)) (d * j) (d * k) y
        ((mul_right_injective₀ hd).ne hjk.symm)).trans
        (DirectSum.of_eq_of_ne (β := fun k ↦ Γ((A.veronese d).X k, U)) j k y hjk.symm).symm
  | add x y hx hy =>
    rw [map_add, DirectSum.add_apply, DirectSum.add_apply, hx, hy]
    rfl

/-- The image of `veroneseSectionsAlgHom` has no component in degrees not divisible by `d`. -/
lemma _root_.CategoryTheory.CommMon.veroneseSectionsAlgHom_apply_of_not_dvd
    (x : ⨁ k, Γ((A.veronese d).X k, U)) {n : ℕ} (hn : ¬d ∣ n) :
    A.veroneseSectionsAlgHom d U x n = 0 := by
  classical
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero]; rfl
  | of j y =>
    rw [veroneseSectionsAlgHom_of A d U j y]
    exact DirectSum.of_eq_of_ne (β := fun n ↦ Γ(A.X n, U)) (d * j) n y
      fun h ↦ hn (h ▸ dvd_mul_right d j)
  | add x y hx hy =>
    rw [map_add, DirectSum.add_apply, hx, hy]
    exact add_zero 0

/-- For `d ≠ 0`, `veroneseSectionsAlgHom` is injective. -/
lemma _root_.CategoryTheory.CommMon.injective_veroneseSectionsAlgHom (hd : d ≠ 0) :
    Function.Injective (A.veroneseSectionsAlgHom d U) := fun x y h ↦
  DFinsupp.ext fun k ↦ (A.veroneseSectionsAlgHom_apply_mul d U hd x k).symm.trans
    ((congrArg (· (d * k)) h).trans (A.veroneseSectionsAlgHom_apply_mul d U hd y k))

/-- The image of `veroneseSectionsAlgHom` is the Veronese subalgebra of the graded ring of
sections of `A`. -/
lemma _root_.CategoryTheory.CommMon.range_veroneseSectionsAlgHom :
    (A.veroneseSectionsAlgHom d U).range.toSubmodule =
      (GradedAlgebra.veronese (A.gradedSectionsGrading U) d).toSubmodule := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | of k y =>
      change A.veroneseSectionsAlgHom d U _ ∈ _
      rw [veroneseSectionsAlgHom_of]
      exact GradedAlgebra.mem_veronese_of_mem (A.of_mem_gradedSectionsGrading (d * k) y)
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · intro x hx
    induction hx using Submodule.iSup_induction' with
    | mem k x hx =>
      obtain ⟨y, rfl⟩ := DirectSum.mem_summand.mp hx
      exact ⟨DirectSum.of (fun k ↦ Γ((A.veronese d).X k, U)) k y,
        veroneseSectionsAlgHom_of A d U k y⟩
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy

/-- For `d ≠ 0`, the graded ring of sections `⨁ₖ Γ(A_{dk}, U)` of the `d`-th Veronese
subalgebra of `A` is isomorphic, as a `Γ(X, U)`-algebra, to the Veronese subalgebra of the graded
ring of sections `⨁ₙ Γ(Aₙ, U)` of `A`. -/
def _root_.CategoryTheory.CommMon.veroneseSectionsEquiv (hd : d ≠ 0) :
    (⨁ k, Γ((A.veronese d).X k, U)) ≃ₐ[Γ(X, U)]
      GradedAlgebra.veronese (A.gradedSectionsGrading U) d :=
  (AlgEquiv.ofInjective _ (A.injective_veroneseSectionsAlgHom d U hd)).trans
    (Subalgebra.equivOfEq _ _
      (Subalgebra.toSubmodule_injective (A.range_veroneseSectionsAlgHom d U)))

/-- The isomorphism `veroneseSectionsEquiv` is `veroneseSectionsAlgHom` with its codomain
restricted to the Veronese subalgebra. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.coe_veroneseSectionsEquiv (hd : d ≠ 0)
    (x : ⨁ k, Γ((A.veronese d).X k, U)) :
    (A.veroneseSectionsEquiv d U hd x : ⨁ n, Γ(A.X n, U)) = A.veroneseSectionsAlgHom d U x := by
  simp only [veroneseSectionsEquiv, AlgEquiv.trans_apply, Subalgebra.equivOfEq_apply]
  rfl

/-- The isomorphism `veroneseSectionsEquiv` carries the degree-`k` summand of the graded sections
of the Veronese subalgebra into the degree-`k` part of the Veronese grading. -/
theorem _root_.CategoryTheory.CommMon.veroneseSectionsEquiv_mem_veroneseGrading (hd : d ≠ 0)
    {k : ℕ} {x : ⨁ k, Γ((A.veronese d).X k, U)}
    (hx : x ∈ (A.veronese d).gradedSectionsGrading U k) :
    A.veroneseSectionsEquiv d U hd x ∈
      GradedAlgebra.veroneseGrading (A.gradedSectionsGrading U) d k := by
  obtain ⟨y, rfl⟩ := DirectSum.mem_summand.mp hx
  rw [GradedAlgebra.mem_veroneseGrading, coe_veroneseSectionsEquiv,
    veroneseSectionsAlgHom_of A d U k y]
  exact A.of_mem_gradedSectionsGrading (d * k) y

/-- The isomorphism `veroneseSectionsEquiv` carries the degree-`k` summand of the graded sections
of the Veronese subalgebra onto the degree-`k` part of the Veronese grading. -/
theorem _root_.CategoryTheory.CommMon.map_veroneseSectionsEquiv_gradedSectionsGrading
    (hd : d ≠ 0) (k : ℕ) :
    ((A.veronese d).gradedSectionsGrading U k).map
        (A.veroneseSectionsEquiv d U hd).toLinearEquiv.toLinearMap =
      GradedAlgebra.veroneseGrading (A.gradedSectionsGrading U) d k := by
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact A.veroneseSectionsEquiv_mem_veroneseGrading d U hd hx
  · obtain ⟨y, hy⟩ := DirectSum.mem_summand.mp hx
    refine ⟨DirectSum.of (fun k ↦ Γ((A.veronese d).X k, U)) k y,
      (A.veronese d).of_mem_gradedSectionsGrading k y, Subtype.ext ?_⟩
    exact (veroneseSectionsAlgHom_of A d U k y).trans hy

variable {U} {V : X.Opens} (f : V ⟶ U)

/-- The homomorphism `veroneseSectionsAlgHom` commutes with restriction of sections. -/
theorem _root_.CategoryTheory.CommMon.veroneseSectionsAlgHom_restrictGradedSections
    (x : ⨁ k, Γ((A.veronese d).X k, U)) :
    A.veroneseSectionsAlgHom d V ((A.veronese d).restrictGradedSections f x) =
      A.restrictGradedSections f (A.veroneseSectionsAlgHom d U x) := by
  have h : (A.veroneseSectionsAlgHom d V).toRingHom.comp
        ((A.veronese d).restrictGradedSections f) =
      (A.restrictGradedSections f).comp (A.veroneseSectionsAlgHom d U).toRingHom :=
    DirectSum.ringHom_ext fun k y ↦ by
      change A.veroneseSectionsAlgHom d V ((A.veronese d).restrictGradedSections f
          (DirectSum.of (fun k ↦ Γ((A.veronese d).X k, U)) k y)) =
        A.restrictGradedSections f (A.veroneseSectionsAlgHom d U
          (DirectSum.of (fun k ↦ Γ((A.veronese d).X k, U)) k y))
      rw [restrictGradedSections_of, veroneseSectionsAlgHom_of, veroneseSectionsAlgHom_of]
      exact (restrictGradedSections_of A f (d * k) y).symm
  exact DFunLike.congr_fun h x

end

end TauCeti
