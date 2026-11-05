/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Pullback
public import TauCeti.AlgebraicGeometry.Modules.GradedAlgebra.Sections
public import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Sections
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange

/-!
# Sections of the pullback of a graded quasicoherent algebra

Let `g : Y ⟶ X` be a morphism of schemes, `A = ⨁ₙ Aₙ` a graded quasicoherent algebra on `X` and
`U` an open of `X`. Pulling back sections along `g` in each degree is a homomorphism of graded
rings

`⨁ n, Γ(Aₙ, U) → ⨁ n, Γ((g^* A)ₙ, g⁻¹ U)`

from the graded ring of sections of `A` (`CategoryTheory.CommMon.gradedSectionsGrading`) to that
of its pullback `g^* A` (`GradedQuasicoherentAlgebra.pullback`), over `g.app U`. It is
multiplicative because the tensor comparison of pullback sends the pullback of `x ⊗ y` to
`g^* x ⊗ g^* y` (`AlgebraicGeometry.Scheme.Hom.δ_app_pullbackSections_μ`), and the homogeneous
multiplication of `g^* A` is the pullback of that of `A` after inverting this comparison.

Restricting to an open `V ⊆ g⁻¹ U` gives `pullbackGradedSectionsLE`, over `g.appLE U V`. If `U`
and `V` are affine, pulling back the sections of each quasicoherent `Aₙ` from `U` to `V` is the
extension of scalars along `Γ(X, U) → Γ(Y, V)` (the square `g ≫ 𝟙 = 𝟙 ≫ g` case of
`Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear`), so the graded ring of sections of `g^* A`
over `V` is the base change of that of `A` over `U`. By
`AlgebraicGeometry.Proj.isPullback_map_of_isBaseChange`, `Proj` of the sections of `g^* A` over
`V` is then the fibre product of `Proj` of the sections of `A` over `U` with `Spec Γ(Y, V)` over
`Spec Γ(X, U)`. This is the affine-local input for base change of relative `Proj` along an
arbitrary morphism of the base.

## Main declarations

* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullbackGradedSections` and
  `pullbackGradedSectionsGradedHom`: pullback of graded sections from `U` to `g⁻¹ U`, as a ring
  homomorphism and as a graded ring homomorphism;
* `GradedQuasicoherentAlgebra.pullbackGradedSectionsLE` and `pullbackGradedSectionsLEGradedHom`:
  the same followed by restriction to an open `V ⊆ g⁻¹ U`;
* `GradedQuasicoherentAlgebra.isPullback_proj_map_pullbackGradedSectionsLEGradedHom`: for affine
  `U` and `V`, `Proj` of the pulled-back graded sections over `V` is the base change of `Proj` of
  the graded sections over `U` along `Spec Γ(Y, V) ⟶ Spec Γ(X, U)`.
-/

public section

open CategoryTheory MonoidalCategory CategoryTheory.Limits

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry
open scoped _root_.DirectSum TensorProduct

universe u

noncomputable section

namespace GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (A : GradedQuasicoherentAlgebra X) (U : X.Opens)

/-- Pulling back a homogeneous section of degree `n` of `A` over `U` along `g`: a section of
`Aₙ` over `U` gives a section of `(g^* A)ₙ = g^* Aₙ` over `g⁻¹ U`. -/
def pullbackHomogeneousSections (n : ℕ) :
    Γ(A.obj.X n, U) →+ Γ(((pullback g).obj A).obj.X n, g ⁻¹ᵁ U) :=
  ((eqToHom (pullback_obj_obj_X g A n).symm).app (g ⁻¹ᵁ U)).hom.comp
    (g.pullbackSections (A.obj.X n) U).toAddMonoidHom

/-- A pulled-back homogeneous section is the pullback of the section, read in the degree-`n`
component of `g^* A`. -/
lemma pullbackHomogeneousSections_apply (n : ℕ) (x : Γ(A.obj.X n, U)) :
    pullbackHomogeneousSections g A U n x =
      (eqToHom (pullback_obj_obj_X g A n).symm).app (g ⁻¹ᵁ U) (g.pullbackSections _ U x) := (rfl)

/-- Pulling back homogeneous sections commutes with the structure maps
`Γ(X, U) → Γ(A₀, U)` and `Γ(Y, g⁻¹ U) → Γ((g^* A)₀, g⁻¹ U)`. -/
lemma pullbackHomogeneousSections_gAlgebra_toFun (r : Γ(X, U)) :
    pullbackHomogeneousSections g A U 0 (DirectSum.GAlgebra.toFun (R := Γ(X, U))
      (A := fun n ↦ Γ(A.obj.X n, U)) r) =
      DirectSum.GAlgebra.toFun (R := Γ(Y, g ⁻¹ᵁ U))
        (A := fun n ↦ Γ(((pullback g).obj A).obj.X n, g ⁻¹ᵁ U))
        (g.app U r) := by
  rw [CommMon.gAlgebraSections_toFun, CommMon.gAlgebraSections_toFun]
  erw [pullbackHomogeneousSections_apply]
  have h1 : g.pullbackSections (𝟙_ X.Modules) U r =
      (Scheme.Modules.pullbackObjUnitIso g).inv.app (g ⁻¹ᵁ U) (g.app U r) := by
    rw [← g.pullbackObjUnitIso_hom_app_pullbackSections U r]
    erw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id]
    rfl
  rw [Scheme.Modules.sectionsFunctor_ε, Scheme.Modules.sectionsFunctor_ε]
  erw [← g.pullbackSections_naturality]
  rw [pullback_obj_one]
  erw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ← h1]
  rfl

/-- Pulling back homogeneous sections preserves the unit. -/
lemma pullbackHomogeneousSections_gOne :
    pullbackHomogeneousSections g A U 0 (GradedMonoid.GOne.one (A := fun n ↦ Γ(A.obj.X n, U))) =
      GradedMonoid.GOne.one (A := fun n ↦ Γ(((pullback g).obj A).obj.X n, g ⁻¹ᵁ U)) := by
  rw [CommMon.sections_gOne_def, CommMon.sections_gOne_def, ← CommMon.gAlgebraSections_toFun,
    ← CommMon.gAlgebraSections_toFun, pullbackHomogeneousSections_gAlgebra_toFun, map_one]

/-- Pulling back homogeneous sections preserves the homogeneous multiplication. -/
lemma pullbackHomogeneousSections_gMul {i j : ℕ} (x : Γ(A.obj.X i, U)) (y : Γ(A.obj.X j, U)) :
    pullbackHomogeneousSections g A U (i + j)
        (GradedMonoid.GMul.mul (A := fun n ↦ Γ(A.obj.X n, U)) x y) =
      GradedMonoid.GMul.mul (A := fun n ↦ Γ(((pullback g).obj A).obj.X n, g ⁻¹ᵁ U))
        (pullbackHomogeneousSections g A U i x) (pullbackHomogeneousSections g A U j y) := by
  rw [CommMon.sections_gMul_def, CommMon.sections_gMul_def]
  have hδ := g.δ_app_pullbackSections_μ (A.obj.X i) (A.obj.X j) U x y
  have hnat := congr($(Functor.LaxMonoidal.μ_natural (Scheme.Modules.sectionsFunctor (g ⁻¹ᵁ U))
    (eqToHom (pullback_obj_obj_X g A i)) (eqToHom (pullback_obj_obj_X g A j)))
      (pullbackHomogeneousSections g A U i x ⊗ₜ pullbackHomogeneousSections g A U j y))
  have he (n : ℕ) (z : Γ((Scheme.Modules.pullback g).obj (A.obj.X n), g ⁻¹ᵁ U)) :
      (eqToHom (pullback_obj_obj_X g A n)).app (g ⁻¹ᵁ U)
        ((eqToHom (pullback_obj_obj_X g A n).symm).app (g ⁻¹ᵁ U) z) = z := by
    erw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, eqToHom_trans,
      eqToHom_refl]
    rfl
  have hnat' : Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor (g ⁻¹ᵁ U)) _ _
      (g.pullbackSections (A.obj.X i) U x ⊗ₜ g.pullbackSections (A.obj.X j) U y) =
      (eqToHom (pullback_obj_obj_X g A i) ⊗ₘ eqToHom (pullback_obj_obj_X g A j)).app (g ⁻¹ᵁ U)
        (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor (g ⁻¹ᵁ U)) _ _
          (pullbackHomogeneousSections g A U i x ⊗ₜ pullbackHomogeneousSections g A U j y)) := by
    rw [← he i (g.pullbackSections (A.obj.X i) U x), ← he j (g.pullbackSections (A.obj.X j) U y)]
    exact hnat
  have hinv (z : Γ((Scheme.Modules.pullback g).obj (A.obj.X i ⊗ A.obj.X j), g ⁻¹ᵁ U)) :
      (inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) (A.obj.X i) (A.obj.X j))).app
        (g ⁻¹ᵁ U) ((Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) (A.obj.X i)
          (A.obj.X j)).app (g ⁻¹ᵁ U) z) = z := by
    erw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, IsIso.hom_inv_id]
    rfl
  have hkey : g.pullbackSections (A.obj.X i ⊗ A.obj.X j) U
      (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) _ _ (x ⊗ₜ y)) =
      (inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) (A.obj.X i) (A.obj.X j))).app
        (g ⁻¹ᵁ U) ((eqToHom (pullback_obj_obj_X g A i) ⊗ₘ
          eqToHom (pullback_obj_obj_X g A j)).app (g ⁻¹ᵁ U)
            (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor (g ⁻¹ᵁ U)) _ _
              (pullbackHomogeneousSections g A U i x ⊗ₜ
                pullbackHomogeneousSections g A U j y))) := by
    rw [← hnat', ← hδ, hinv]
  erw [pullbackHomogeneousSections_apply]
  erw [← g.pullbackSections_naturality]
  rw [pullback_obj_mul]
  erw [hkey]
  rfl

/-- **Pullback of graded sections.** Pulling back sections along `g : Y ⟶ X`, as a ring
homomorphism from the graded ring of sections of `A` over `U` to the graded ring of sections of
`g^* A` over `g⁻¹ U`. It sends each homogeneous section to its pullback, in the same degree
(`pullbackGradedSections_of`). -/
def pullbackGradedSections :
    (⨁ n, Γ(A.obj.X n, U)) →+* ⨁ n, Γ(((pullback g).obj A).obj.X n, g ⁻¹ᵁ U) :=
  DirectSum.toSemiring
    (fun n ↦ (DirectSum.of (fun n ↦ Γ(((pullback g).obj A).obj.X n, g ⁻¹ᵁ U)) n).comp
      (pullbackHomogeneousSections g A U n))
    ((congrArg _ (pullbackHomogeneousSections_gOne g A U)).trans (DirectSum.of_zero_one _))
    (fun x y ↦ (congrArg _ (pullbackHomogeneousSections_gMul g A U x y)).trans
      (DirectSum.of_mul_of _ _).symm)

/-- The pullback of a homogeneous section is its pullback in the same degree. -/
@[simp]
lemma pullbackGradedSections_of (n : ℕ) (x : Γ(A.obj.X n, U)) :
    pullbackGradedSections g A U (DirectSum.of _ n x) =
      DirectSum.of _ n (pullbackHomogeneousSections g A U n x) :=
  DirectSum.toSemiring_of _ _ _ _ _

/-- Pullback of graded sections is compatible with the structure maps, along
`g.app U : Γ(X, U) → Γ(Y, g⁻¹ U)`. -/
lemma pullbackGradedSections_algebraMap (r : Γ(X, U)) :
    pullbackGradedSections g A U (algebraMap Γ(X, U) (⨁ n, Γ(A.obj.X n, U)) r) =
      algebraMap Γ(Y, g ⁻¹ᵁ U) (⨁ n, Γ(((pullback g).obj A).obj.X n, g ⁻¹ᵁ U)) (g.app U r) := by
  rw [DirectSum.algebraMap_apply, DirectSum.algebraMap_apply, pullbackGradedSections_of,
    pullbackHomogeneousSections_gAlgebra_toFun]

/-- Pullback of graded sections as a graded ring homomorphism. Its underlying ring homomorphism
is `pullbackGradedSections`. -/
def pullbackGradedSectionsGradedHom :
    A.obj.gradedSectionsGrading U →+*ᵍ
      ((pullback g).obj A).obj.gradedSectionsGrading (g ⁻¹ᵁ U) where
  __ := pullbackGradedSections g A U
  map_mem {n x} hx := by
    obtain ⟨x, rfl⟩ := DirectSum.mem_summand.mp hx
    simpa using ((pullback g).obj A).obj.of_mem_gradedSectionsGrading n _

/-- The graded pullback of sections is the pullback of sections. -/
@[simp]
lemma pullbackGradedSectionsGradedHom_apply (x : ⨁ n, Γ(A.obj.X n, U)) :
    pullbackGradedSectionsGradedHom g A U x = pullbackGradedSections g A U x :=
  (rfl)

section Restriction

variable {g U} {V : Y.Opens} (hV : V ≤ g ⁻¹ᵁ U)

/-- **Pullback of graded sections to an open `V ⊆ g⁻¹ U`.** Pulling back sections along `g` and
restricting them to `V`, as a ring homomorphism from the graded ring of sections of `A` over `U`
to the graded ring of sections of `g^* A` over `V`. -/
def pullbackGradedSectionsLE :
    (⨁ n, Γ(A.obj.X n, U)) →+* ⨁ n, Γ(((pullback g).obj A).obj.X n, V) :=
  (((pullback g).obj A).obj.restrictGradedSections (homOfLE hV)).comp
    (pullbackGradedSections g A U)

/-- The pullback of a homogeneous section to `V` is the restriction of its pullback, in the same
degree. -/
@[simp]
lemma pullbackGradedSectionsLE_of (n : ℕ) (x : Γ(A.obj.X n, U)) :
    pullbackGradedSectionsLE A hV (DirectSum.of _ n x) =
      DirectSum.of _ n ((((pullback g).obj A).obj.X n).presheaf.map (homOfLE hV).op
        (pullbackHomogeneousSections g A U n x)) := by
  simp [pullbackGradedSectionsLE]

/-- Pullback of graded sections to `V` is compatible with the structure maps, along
`g.appLE U V hV : Γ(X, U) → Γ(Y, V)`. -/
lemma pullbackGradedSectionsLE_algebraMap (r : Γ(X, U)) :
    pullbackGradedSectionsLE A hV (algebraMap Γ(X, U) (⨁ n, Γ(A.obj.X n, U)) r) =
      algebraMap Γ(Y, V) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) (g.appLE U V hV r) := by
  rw [pullbackGradedSectionsLE, RingHom.comp_apply, pullbackGradedSections_algebraMap,
    CommMon.restrictGradedSections_algebraMap]
  rfl

/-- Pullback of graded sections to `V` as a graded ring homomorphism. Its underlying ring
homomorphism is `pullbackGradedSectionsLE`. -/
def pullbackGradedSectionsLEGradedHom :
    A.obj.gradedSectionsGrading U →+*ᵍ ((pullback g).obj A).obj.gradedSectionsGrading V :=
  (((pullback g).obj A).obj.restrictGradedSectionsGradedHom (homOfLE hV)).comp
    (pullbackGradedSectionsGradedHom g A U)

/-- The graded pullback of sections to `V` is `pullbackGradedSectionsLE`. -/
@[simp]
lemma pullbackGradedSectionsLEGradedHom_apply (x : ⨁ n, Γ(A.obj.X n, U)) :
    pullbackGradedSectionsLEGradedHom A hV x = pullbackGradedSectionsLE A hV x := by
  rw [pullbackGradedSectionsLEGradedHom, GradedRingHom.comp_apply,
    CommMon.restrictGradedSectionsGradedHom_apply, pullbackGradedSectionsGradedHom_apply]
  rfl

end Restriction

/-- Over affine opens `U` of `X` and `V ⊆ g⁻¹ U` of `Y`, pulling back the sections of a
quasicoherent sheaf from `U` to `V` is the extension of scalars along `g.appLE U V`. This is the
cartesian square `g ≫ 𝟙 = 𝟙 ≫ g` case of `Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear`,
recorded as a linear equivalence. -/
private theorem exists_pullbackSectionsLE_equiv (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV' : IsAffineOpen V)
    (hV : V ≤ g ⁻¹ᵁ U) :
    letI : Algebra Γ(X, U) Γ(Y, V) := (g.appLE U V hV).hom.toAlgebra
    ∃ e : Γ(Y, V) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(Y, V)] Γ((Scheme.Modules.pullback g).obj M, V),
      ∀ m, e (1 ⊗ₜ m) = g.pullbackSectionsLE M U V hV m := by
  have hid (Z : Scheme.{u}) (W : Z.Opens) (e : W ≤ (𝟙 Z) ⁻¹ᵁ W) (r : Γ(Z, W)) :
      (𝟙 Z : Z ⟶ Z).appLE W W e r = r := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    change Z.presheaf.map (𝟙 (Opposite.op W)) r = r
    rw [CategoryTheory.Functor.map_id]
    rfl
  let : Algebra Γ(X, U) Γ(Y, V) := (g.appLE U V hV).hom.toAlgebra
  let : Module Γ(X, U) Γ((Scheme.Modules.pullback g).obj M, V) :=
    Module.compHom _ (g.appLE U V hV).hom
  have : IsScalarTower Γ(X, U) Γ(Y, V) Γ((Scheme.Modules.pullback g).obj M, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  -- The base change statement acts on `Γ(X, U)` and `Γ(Y, V)` through `appLE` of identities.
  have : letI : SMul Γ(X, U) Γ(X, U) := ((𝟙 X : X ⟶ X).appLE U U le_rfl).hom.toAlgebra.toSMul
      IsScalarTower Γ(X, U) Γ(X, U) Γ(M, U) := by
    let : SMul Γ(X, U) Γ(X, U) := ((𝟙 X : X ⟶ X).appLE U U le_rfl).hom.toAlgebra.toSMul
    constructor
    intro r s m
    change ((𝟙 X : X ⟶ X).appLE U U le_rfl r * s) • m = r • (s • m)
    erw [hid]
    rw [mul_smul]
  have : letI : SMul Γ(Y, V) Γ(Y, V) := ((𝟙 Y : Y ⟶ Y).appLE V V le_rfl).hom.toAlgebra.toSMul
      IsScalarTower Γ(Y, V) Γ(Y, V) Γ((Scheme.Modules.pullback g).obj M, V) := by
    let : SMul Γ(Y, V) Γ(Y, V) := ((𝟙 Y : Y ⟶ Y).appLE V V le_rfl).hom.toAlgebra.toSMul
    constructor
    intro r s m
    change ((𝟙 Y : Y ⟶ Y).appLE V V le_rfl r * s) • m = r • (s • m)
    erw [hid]
    rw [mul_smul]
  have hbc := Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear (g' := g) (M := M)
    (H := IsPullback.of_id_snd) (W := U) (W' := V) (UX := U) (UY := V) hU hV' hV le_rfl hU
    (inf_eq_right.mpr hV).symm
  refine ⟨hbc.equiv, fun m ↦ ?_⟩
  rw [hbc.equiv_tmul, one_smul]
  erw [Scheme.Hom.pullbackSectionsLEBaseLinear_apply]

variable {g U} in
/-- Over affine opens `U` of `X` and `V ⊆ g⁻¹ U` of `Y`, the pulled-back graded sections over `V`
are the base change of the graded sections of `A` over `U` along `g.appLE U V`, so `Proj` of them
is the base change of `Proj` of the graded sections of `A`. Stated as an existence statement so
that the irrelevant-ideal condition of `Proj.map` and the cartesian square share their proof. -/
private theorem exists_isPullback_proj_map (hU : IsAffineOpen U) {V : Y.Opens}
    (hV' : IsAffineOpen V) (hV : V ≤ g ⁻¹ᵁ U) :
    ∃ h : HomogeneousIdeal.irrelevant (((pullback g).obj A).obj.gradedSectionsGrading V) ≤
        (HomogeneousIdeal.irrelevant (A.obj.gradedSectionsGrading U)).map
          (pullbackGradedSectionsLEGradedHom A hV),
      IsPullback (Proj.map (pullbackGradedSectionsLEGradedHom A hV) h)
        (Proj.toSpecCoeff (((pullback g).obj A).obj.gradedSectionsGrading V))
        (Proj.toSpecCoeff (A.obj.gradedSectionsGrading U)) (Spec.map (g.appLE U V hV)) := by
  let : Algebra Γ(X, U) Γ(Y, V) := (g.appLE U V hV).hom.toAlgebra
  let : Algebra Γ(X, U) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) :=
    ((algebraMap Γ(Y, V) (⨁ n, Γ(((pullback g).obj A).obj.X n, V))).comp
      (g.appLE U V hV).hom).toAlgebra
  have : IsScalarTower Γ(X, U) Γ(Y, V) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) :=
    .of_algebraMap_eq' rfl
  have hfR (r : Γ(X, U)) : pullbackGradedSectionsLEGradedHom A hV
      (algebraMap Γ(X, U) (⨁ n, Γ(A.obj.X n, U)) r) =
      algebraMap Γ(X, U) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) r :=
    (pullbackGradedSectionsLEGradedHom_apply A hV _).trans
      (pullbackGradedSectionsLE_algebraMap A hV r)
  -- The degree-`n` component of `g^* A` is `g^* Aₙ`, up to an `eqToHom`.
  let eqv (n : ℕ) : Γ((Scheme.Modules.pullback g).obj (A.obj.X n), V) ≃ₗ[Γ(Y, V)]
      Γ(((pullback g).obj A).obj.X n, V) :=
    { toFun := (eqToHom (pullback_obj_obj_X g A n).symm).app V
      invFun := (eqToHom (pullback_obj_obj_X g A n)).app V
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _
      left_inv z := by
        erw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, eqToHom_trans,
          eqToHom_refl]
        rfl
      right_inv z := by
        erw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, eqToHom_trans,
          eqToHom_refl]
        rfl }
  choose e he using fun n ↦ exists_pullbackSectionsLE_equiv g (A.obj.X n) hU hV' hV
  have hf : IsBaseChange Γ(Y, V)
      (AlgHom.mk (pullbackGradedSectionsLEGradedHom A hV).toRingHom hfR).toLinearMap := by
    refine IsBaseChange.of_equiv ((TensorProduct.directSumRight _ _ _ _).trans
      (DirectSum.congrLinearEquiv fun n ↦ (e n).trans (eqv n))) fun x ↦ ?_
    induction x using DirectSum.induction_on with
    | zero => simp
    | of n m =>
      rw [← DirectSum.lof_eq_of Γ(X, U), LinearEquiv.trans_apply,
        TensorProduct.directSumRight_tmul_lof, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
      erw [LinearEquiv.trans_apply, he]
      rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]
      change _ = pullbackGradedSectionsLEGradedHom A hV (DirectSum.of _ n m)
      rw [pullbackGradedSectionsLEGradedHom_apply, pullbackGradedSectionsLE_of]
      congr 1
      -- Restriction commutes with the identification `(g^* A)ₙ = g^* Aₙ`.
      rw [Scheme.Hom.pullbackSectionsLE_apply, pullbackHomogeneousSections_apply]
      exact congr($((eqToHom (pullback_obj_obj_X g A n).symm).mapPresheaf.naturality
        (homOfLE hV).op) (g.pullbackSections (A.obj.X n) U m))
    | add x y hx hy =>
      simp only [TensorProduct.tmul_add, LinearEquiv.map_add, LinearMap.map_add, hx, hy]
  exact ⟨_, Proj.isPullback_map_of_isBaseChange _ _ hfR hf⟩

variable {g U} {V : Y.Opens}

/-- Over affine opens `U` of `X` and `V ⊆ g⁻¹ U` of `Y`, the irrelevant ideal of the
pulled-back graded sections over `V` is generated by the pullback of the irrelevant ideal of the
graded sections of `A` over `U`. This is the condition for `Proj.map` along
`pullbackGradedSectionsLEGradedHom`. -/
theorem irrelevant_le_map_pullbackGradedSectionsLEGradedHom (hU : IsAffineOpen U)
    (hV' : IsAffineOpen V) (hV : V ≤ g ⁻¹ᵁ U) :
    HomogeneousIdeal.irrelevant (((pullback g).obj A).obj.gradedSectionsGrading V) ≤
      (HomogeneousIdeal.irrelevant (A.obj.gradedSectionsGrading U)).map
        (pullbackGradedSectionsLEGradedHom A hV) :=
  (exists_isPullback_proj_map A hU hV' hV).1

/-- **`Proj` of graded sections commutes with pullback.** For a morphism of schemes `g : Y ⟶ X`,
affine opens `U` of `X` and `V ⊆ g⁻¹ U` of `Y`, and a graded quasicoherent algebra `A` on `X`,
the square

`Proj (⨁ n, Γ((g^* A)ₙ, V)) ⟶ Proj (⨁ n, Γ(Aₙ, U))`, `Spec Γ(Y, V) ⟶ Spec Γ(X, U)`

formed by `Proj.map` of the pullback of graded sections and the coefficient projections is
cartesian. This is the affine-local step of base change for relative `Proj`. -/
theorem isPullback_proj_map_pullbackGradedSectionsLEGradedHom (hU : IsAffineOpen U)
    (hV' : IsAffineOpen V) (hV : V ≤ g ⁻¹ᵁ U) :
    IsPullback (Proj.map (pullbackGradedSectionsLEGradedHom A hV)
        (irrelevant_le_map_pullbackGradedSectionsLEGradedHom A hU hV' hV))
      (Proj.toSpecCoeff (((pullback g).obj A).obj.gradedSectionsGrading V))
      (Proj.toSpecCoeff (A.obj.gradedSectionsGrading U)) (Spec.map (g.appLE U V hV)) :=
  (exists_isPullback_proj_map A hU hV' hV).2

end GradedQuasicoherentAlgebra

end

end AlgebraicGeometry

end TauCeti
