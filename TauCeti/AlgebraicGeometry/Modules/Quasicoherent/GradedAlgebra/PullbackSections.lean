/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.GradedAlgebra.Sections
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Pullback

/-!
# Pullback of sections of a graded quasicoherent algebra

Let `g : X ⟶ Y` be a morphism of schemes, `A = ⨁ₙ Aₙ` a graded quasicoherent algebra on `Y`, and
`V` an open of `X` with `V ≤ g⁻¹ U` for an open `U` of `Y`. Pulling back sections along `g` and
restricting them to `V` (`AlgebraicGeometry.Scheme.Hom.pullbackSectionsLE`), degree by degree, is
a homomorphism of graded rings

`⨁ n, Γ(Aₙ, U) → ⨁ n, Γ(g^* Aₙ, V)`

from the sections of `A` to those of its pullback `g^* A`
(`GradedQuasicoherentAlgebra.pullbackGradedSections`), lying over the map of functions
`Γ(Y, U) → Γ(X, V)`. Over affine opens these are the maps along which the charts
`Proj (⨁ n, Γ(g^* Aₙ, V))` of the relative `Proj` of `g^* A` map to the charts
`Proj (⨁ n, Γ(Aₙ, U))` of the relative `Proj` of `A`.

Multiplicativity is the compatibility of pulling back sections with the monoidal comparisons of
pullback: the comparison `g^* (M ⊗ N) ⟶ g^* M ⊗ g^* N` sends the pullback of `x ⊗ y` to the
tensor product of the pullbacks (`AlgebraicGeometry.Scheme.Hom.δ_app_pullbackSectionsLE`), and the
comparison `g^* 𝒪_Y ⟶ 𝒪_X` sends the pullback of a function `r` to `g^* r`
(`AlgebraicGeometry.Scheme.Hom.η_app_pullbackSectionsLE`). Both follow from the compatibility of
the pullback–pushforward adjunction with the oplax monoidal structure of pullback.

## Main declarations

* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullbackGradedSections`: the ring
  homomorphism `⨁ n, Γ(Aₙ, U) → ⨁ n, Γ(g^* Aₙ, V)`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullbackGradedSectionsGradedHom`: the
  same map, as a graded ring homomorphism;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullbackGradedSections_algebraMap`: it
  lies over `Γ(Y, U) → Γ(X, V)`;
* `GradedQuasicoherentAlgebra.restrictGradedSections_comp_pullbackGradedSections` and
  `GradedQuasicoherentAlgebra.pullbackGradedSections_comp_restrictGradedSections`: it commutes
  with restriction of sections on both sides.

## References

* [The Stacks Project, Lemma 27.16.10](https://stacks.math.columbia.edu/tag/01O3)
-/

public section

open CategoryTheory MonoidalCategory Opposite DirectSum

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- On pure tensors of sections over `g⁻¹ U`, the tensor map of pushforward is the tensor map of
sections over `g⁻¹ U`. -/
private lemma sectionsFunctor_map_pushforward_μ (P Q : X.Modules) (U : Y.Opens)
    (a : Γ(P, g ⁻¹ᵁ U)) (b : Γ(Q, g ⁻¹ᵁ U)) :
    (Scheme.Modules.sectionsFunctor U).map
        (Functor.LaxMonoidal.μ (Scheme.Modules.pushforward g) P Q)
      (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U)
        ((Scheme.Modules.pushforward g).obj P) ((Scheme.Modules.pushforward g).obj Q) (a ⊗ₜ b)) =
    Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor (g ⁻¹ᵁ U)) P Q (a ⊗ₜ b) :=
  TauCeti.SheafOfModules.pushforward_μ_app_tmul g.toRingCatSheafHom P Q (op U) a b

/-- The comparison `g^* (M ⊗ N) ⟶ g^* M ⊗ g^* N` sends the pullback of `x ⊗ y` to the tensor
product of the pullbacks of `x` and `y`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.δ_app_pullbackSections (M N : Y.Modules)
    (U : Y.Opens) (x : Γ(M, U)) (y : Γ(N, U)) :
    (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) M N).app (g ⁻¹ᵁ U)
      (g.pullbackSections (M ⊗ N) U
        (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) M N (x ⊗ₜ y))) =
    Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor (g ⁻¹ᵁ U)) _ _
      (g.pullbackSections M U x ⊗ₜ g.pullbackSections N U y) := by
  -- the units of the adjunction intertwine the comparison of pullback with the tensor map of
  -- pushforward
  have h := (Scheme.Modules.pullbackPushforwardAdjunction g).unit_app_tensor_comp_map_δ M N
  have h' := congr(((Scheme.Modules.sectionsFunctor U).map $h)
    (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) M N (x ⊗ₜ y)))
  have hn := congr($(Functor.LaxMonoidal.μ_natural (Scheme.Modules.sectionsFunctor U)
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N)) (x ⊗ₜ y))
  simp only [Functor.map_comp, ConcreteCategory.comp_apply, Functor.id_obj] at h' hn
  rw [← hn] at h'
  rw [Scheme.Hom.pullbackSections_apply g M U x, Scheme.Hom.pullbackSections_apply g N U y]
  refine (congrArg _ (Scheme.Hom.pullbackSections_apply g (M ⊗ N) U _)).trans ?_
  exact h'.trans (sectionsFunctor_map_pushforward_μ g _ _ U _ _)

variable {U : Y.Opens} {V : X.Opens} (hV : V ≤ g ⁻¹ᵁ U)

/-- The comparison `g^* (M ⊗ N) ⟶ g^* M ⊗ g^* N` sends the pullback of `x ⊗ y`, restricted to an
open `V ≤ g⁻¹ U`, to the tensor product of the restricted pullbacks of `x` and `y`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.δ_app_pullbackSectionsLE (M N : Y.Modules)
    (x : Γ(M, U)) (y : Γ(N, U)) :
    (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) M N).app V
      (g.pullbackSectionsLE (M ⊗ N) U V hV
        (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) M N (x ⊗ₜ y))) =
    Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor V) _ _
      (g.pullbackSectionsLE M U V hV x ⊗ₜ g.pullbackSectionsLE N U V hV y) := by
  let F : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
    _root_.SheafOfModules.forget _
  let _ : F.LaxMonoidal := SheafOfModules.forgetLaxMonoidal X.sheaf
  rw [Scheme.Hom.pullbackSectionsLE_apply g M U V hV x,
    Scheme.Hom.pullbackSectionsLE_apply g N U V hV y]
  refine (congrArg _ (Scheme.Hom.pullbackSectionsLE_apply g (M ⊗ N) U V hV _)).trans ?_
  -- both the comparison and the tensor map of sections commute with restriction to `V`
  have h₁ := congr($((Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) M N
    ).mapPresheaf.naturality (homOfLE hV).op) (g.pullbackSections (M ⊗ N) U
        (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) M N (x ⊗ₜ y))))
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at h₁
  have h₂ := PresheafOfModules.naturality_apply
    (Functor.LaxMonoidal.μ F ((Scheme.Modules.pullback g).obj M)
      ((Scheme.Modules.pullback g).obj N))
    (homOfLE hV).op (g.pullbackSections M U x ⊗ₜ g.pullbackSections N U y)
  refine h₁.trans ?_
  rw [Scheme.Hom.δ_app_pullbackSections]
  exact h₂.symm

/-- The comparison `g^* 𝒪_Y ⟶ 𝒪_X` sends the pullback of a function `r` on `U`, restricted to an
open `V ≤ g⁻¹ U`, to the function `g^* r` on `V`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.η_app_pullbackSectionsLE (r : Γ(Y, U)) :
    (Functor.OplaxMonoidal.η (Scheme.Modules.pullback g)).app V
      (g.pullbackSectionsLE (𝟙_ Y.Modules) U V hV
        (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) r)) =
    Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor V) (g.appLE U V hV r) := by
  -- the units of the adjunction intertwine the unit comparison of pullback with the unit map
  -- `𝒪_Y ⟶ g_* 𝒪_X` of pushforward
  have h := (Scheme.Modules.pullbackPushforwardAdjunction g).unit_app_unit_comp_map_η
  have h' := congr(((Scheme.Modules.sectionsFunctor U).map $h)
    (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) r))
  simp only [Functor.map_comp, ConcreteCategory.comp_apply] at h'
  have h₁ := congr($((Functor.OplaxMonoidal.η (Scheme.Modules.pullback g)).mapPresheaf.naturality
    (homOfLE hV).op) (g.pullbackSections (𝟙_ Y.Modules) U
        (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) r)))
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at h₁
  refine (congrArg _ (Scheme.Hom.pullbackSectionsLE_apply g _ U V hV _)).trans (h₁.trans ?_)
  have h₂ : (Functor.OplaxMonoidal.η (Scheme.Modules.pullback g)).app (g ⁻¹ᵁ U)
      (g.pullbackSections (𝟙_ Y.Modules) U
        (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) r)) =
      Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor (g ⁻¹ᵁ U)) (g.app U r) := by
    refine (congrArg _ (Scheme.Hom.pullbackSections_apply g _ U _)).trans (h'.trans ?_)
    rw [Scheme.Modules.pushforward_ε, Scheme.Modules.sectionsFunctor_ε,
      Scheme.Modules.sectionsFunctor_ε]
    rfl
  rw [h₂, Scheme.Modules.sectionsFunctor_ε, Scheme.Modules.sectionsFunctor_ε, Scheme.Hom.appLE]
  rfl

namespace GradedQuasicoherentAlgebra

variable (A : GradedQuasicoherentAlgebra Y)

/-- Pulling back a section of `Aₙ` over `U` along `g` and restricting it to `V ≤ g⁻¹ U`, as a
section over `V` of the degree-`n` component of `g^* A`, which is `g^* Aₙ`
(`pullback_obj_obj_X`). -/
def pullbackComponentSections (n : ℕ) :
    Γ(A.obj.X n, U) →ₛₗ[(g.appLE U V hV).hom] Γ(((pullback g).obj A).obj.X n, V) where
  toFun x := (eqToHom (pullback_obj_obj_X g A n).symm).app V (g.pullbackSectionsLE _ U V hV x)
  map_add' x y := by simp
  map_smul' r x := by simp

/-- `pullbackComponentSections` is the pullback of sections, transported along
`pullback_obj_obj_X`. -/
theorem pullbackComponentSections_apply (n : ℕ) (x : Γ(A.obj.X n, U)) :
    A.pullbackComponentSections g hV n x =
      (eqToHom (pullback_obj_obj_X g A n).symm).app V (g.pullbackSectionsLE _ U V hV x) :=
  (rfl)

/-- The transport of sections along `pullback_obj_obj_X` is undone by the inverse transport. -/
private lemma eqToHom_app_eqToHom_app {M N : X.Modules} (h : M = N) (x : Γ(M, V)) :
    (eqToHom h.symm).app V ((eqToHom h).app V x) = x := by
  subst h
  rfl

/-- Pulling back sections along `g` commutes with the structure maps `Γ(Y, U) → Γ(A₀, U)` and
`Γ(X, V) → Γ((g^* A)₀, V)`. -/
theorem pullbackComponentSections_gAlgebraToFun (r : Γ(Y, U)) :
    A.pullbackComponentSections g hV 0
        (GAlgebra.toFun (R := Γ(Y, U)) (A := fun n ↦ Γ(A.obj.X n, U)) r) =
      GAlgebra.toFun (R := Γ(X, V)) (A := fun n ↦ Γ(((pullback g).obj A).obj.X n, V))
        (g.appLE U V hV r) := by
  have h := g.η_app_pullbackSectionsLE hV r
  rw [Scheme.Modules.pullback_η] at h
  have h' : g.pullbackSectionsLE (𝟙_ Y.Modules) U V hV
      (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) r) =
      (Scheme.Modules.pullbackObjUnitIso g).inv.app V
        (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor V) (g.appLE U V hV r)) := by
    rw [← h, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
      Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]
  refine (congrArg (A.pullbackComponentSections g hV 0)
    (CommMon.gAlgebraSections_toFun A.obj U r)).trans ?_
  refine Eq.trans ?_ (CommMon.gAlgebraSections_toFun ((pullback g).obj A).obj V _).symm
  refine (congrArg (fun z ↦ (eqToHom (pullback_obj_obj_X g A 0).symm).app V z)
    ((Scheme.Hom.pullbackSectionsLE_naturality g _ U V hV A.obj.toMon.one _).symm.trans
      (congrArg _ h'))).trans ?_
  refine Eq.trans ?_ (congrArg (fun φ ↦ φ.app V
    (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor V) (g.appLE U V hV r)))
      (pullback_obj_one g A)).symm
  rfl

/-- Pulling back sections along `g` preserves the unit of the graded rings of sections. -/
theorem pullbackComponentSections_gOne :
    A.pullbackComponentSections g hV 0
        (GradedMonoid.GOne.one (A := fun n ↦ Γ(A.obj.X n, U))) =
      GradedMonoid.GOne.one (A := fun n ↦ Γ(((pullback g).obj A).obj.X n, V)) := by
  have h := A.pullbackComponentSections_gAlgebraToFun g hV 1
  rw [CommMon.gAlgebraSections_toFun, CommMon.gAlgebraSections_toFun] at h
  rw [CommMon.sections_gOne_def, CommMon.sections_gOne_def]
  exact h.trans (congrArg _ (congrArg _ (map_one _)))

/-- Pulling back sections along `g` preserves the homogeneous multiplications of the graded
rings of sections. -/
theorem pullbackComponentSections_gMul {i j : ℕ} (x : Γ(A.obj.X i, U)) (y : Γ(A.obj.X j, U)) :
    A.pullbackComponentSections g hV (i + j)
        (GradedMonoid.GMul.mul (A := fun n ↦ Γ(A.obj.X n, U)) x y) =
      GradedMonoid.GMul.mul (A := fun n ↦ Γ(((pullback g).obj A).obj.X n, V))
        (A.pullbackComponentSections g hV i x) (A.pullbackComponentSections g hV j y) := by
  have h' : g.pullbackSectionsLE _ U V hV
      (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) _ _ (x ⊗ₜ y)) =
      (inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) (A.obj.X i) (A.obj.X j))).app V
        (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor V) _ _
          (g.pullbackSectionsLE (A.obj.X i) U V hV x ⊗ₜ
            g.pullbackSectionsLE (A.obj.X j) U V hV y)) := by
    rw [← g.δ_app_pullbackSectionsLE hV, ← ConcreteCategory.comp_apply,
      ← Scheme.Modules.Hom.comp_app, IsIso.hom_inv_id, Scheme.Modules.Hom.id_app,
      ConcreteCategory.id_apply]
  refine (congrArg (A.pullbackComponentSections g hV (i + j))
    (CommMon.sections_gMul_def A.obj U x y)).trans ?_
  refine Eq.trans ?_ (CommMon.sections_gMul_def ((pullback g).obj A).obj V _ _).symm
  refine (congrArg (fun z ↦ (eqToHom (pullback_obj_obj_X g A (i + j)).symm).app V z)
    ((Scheme.Hom.pullbackSectionsLE_naturality g _ U V hV (A.obj.toMon.mul i j) _).symm.trans
      (congrArg _ h'))).trans ?_
  refine Eq.trans ?_ (congrArg (fun φ ↦ φ.app V
    (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor V) _ _
      (A.pullbackComponentSections g hV i x ⊗ₜ A.pullbackComponentSections g hV j y)))
    (pullback_obj_mul g A i j)).symm
  change _ = (eqToHom (pullback_obj_obj_X g A (i + j)).symm).app V
    (((Scheme.Modules.pullback g).map (A.obj.toMon.mul i j)).app V
      ((inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) (A.obj.X i) (A.obj.X j))).app V
        ((eqToHom (pullback_obj_obj_X g A i) ⊗ₘ eqToHom (pullback_obj_obj_X g A j)).app V _)))
  refine congrArg _ (congrArg _ (congrArg _ ?_))
  -- transport both factors along `pullback_obj_obj_X` and back, then use the naturality of the
  -- tensor map of sections over `V`
  have hx := eqToHom_app_eqToHom_app (pullback_obj_obj_X g A i).symm
    (g.pullbackSectionsLE (A.obj.X i) U V hV x)
  have hy := eqToHom_app_eqToHom_app (pullback_obj_obj_X g A j).symm
    (g.pullbackSectionsLE (A.obj.X j) U V hV y)
  have hμ := congr($(Functor.LaxMonoidal.μ_natural (Scheme.Modules.sectionsFunctor V)
    (eqToHom (pullback_obj_obj_X g A i)) (eqToHom (pullback_obj_obj_X g A j)))
      ((eqToHom (pullback_obj_obj_X g A i).symm).app V (g.pullbackSectionsLE (A.obj.X i) U V hV x)
        ⊗ₜ (eqToHom (pullback_obj_obj_X g A j).symm).app V
          (g.pullbackSectionsLE (A.obj.X j) U V hV y)))
  exact (congrArg _ (congrArg₂ _ hx hy)).symm.trans hμ

/-- **Pullback of sections of a graded algebra.** For an open `V ≤ g⁻¹ U`, pulling back sections
along `g` and restricting them to `V`, degree by degree, as a ring homomorphism
`⨁ n, Γ(Aₙ, U) → ⨁ n, Γ((g^* A)ₙ, V)`. It sends each homogeneous section to its pullback, in the
same degree (`pullbackGradedSections_of`). -/
def pullbackGradedSections :
    (⨁ n, Γ(A.obj.X n, U)) →+* ⨁ n, Γ(((pullback g).obj A).obj.X n, V) :=
  DirectSum.toSemiring
    (fun n ↦ (DirectSum.of (fun n ↦ Γ(((pullback g).obj A).obj.X n, V)) n).comp
      (A.pullbackComponentSections g hV n).toAddMonoidHom)
    ((congrArg _ (A.pullbackComponentSections_gOne g hV)).trans (DirectSum.of_zero_one _))
    (fun x y ↦ (congrArg _ (A.pullbackComponentSections_gMul g hV x y)).trans
      (DirectSum.of_mul_of _ _).symm)

/-- The pullback of a homogeneous section is its pullback as a section, in the same degree. -/
@[simp]
theorem pullbackGradedSections_of (n : ℕ) (x : Γ(A.obj.X n, U)) :
    A.pullbackGradedSections g hV (DirectSum.of _ n x) =
      DirectSum.of _ n (A.pullbackComponentSections g hV n x) :=
  DirectSum.toSemiring_of _ _ _ _ _

/-- Pullback of sections lies over the map `Γ(Y, U) → Γ(X, V)` of functions. -/
@[simp]
theorem pullbackGradedSections_algebraMap (r : Γ(Y, U)) :
    A.pullbackGradedSections g hV (algebraMap Γ(Y, U) (⨁ n, Γ(A.obj.X n, U)) r) =
      algebraMap Γ(X, V) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) (g.appLE U V hV r) := by
  rw [DirectSum.algebraMap_apply, DirectSum.algebraMap_apply, pullbackGradedSections_of,
    pullbackComponentSections_gAlgebraToFun]

/-- Pulling back sections of `A` over `U` to `V` and restricting them to `V' ≤ V` is pulling them
back to `V'`. -/
theorem restrictGradedSections_comp_pullbackGradedSections {V' : X.Opens} (i : V' ⟶ V) :
    (((pullback g).obj A).obj.restrictGradedSections i).comp (A.pullbackGradedSections g hV) =
      A.pullbackGradedSections g ((leOfHom i).trans hV) :=
  DirectSum.ringHom_ext fun n x ↦ by
    rw [RingHom.comp_apply, pullbackGradedSections_of, pullbackGradedSections_of]
    refine (((pullback g).obj A).obj.restrictGradedSections_of i n _).trans (congrArg _ ?_)
    rw [pullbackComponentSections_apply, pullbackComponentSections_apply]
    refine (NatTrans.naturality_apply (eqToHom (pullback_obj_obj_X g A n).symm).mapPresheaf
      i.op _).symm.trans (congrArg _ ?_)
    -- restricting from `g⁻¹ U` to `V` and then to `V'` is restricting from `g⁻¹ U` to `V'`
    refine (congrArg _ (Scheme.Hom.pullbackSectionsLE_apply g _ U V hV x)).trans ?_
    refine (((Scheme.Modules.pullback g).obj (A.obj.X n)).presheaf.map_comp_apply _ _ _).symm.trans
      ?_
    exact (Scheme.Hom.pullbackSectionsLE_apply g _ U V' _ x).symm

/-- Restricting sections of `A` from `U` to `U' ≤ U` and pulling them back to `V ≤ g⁻¹ U'` is
pulling them back from `U`. -/
theorem pullbackGradedSections_comp_restrictGradedSections {U' : Y.Opens} (j : U' ⟶ U)
    (hV' : V ≤ g ⁻¹ᵁ U') :
    (A.pullbackGradedSections g hV').comp (A.obj.restrictGradedSections j) =
      A.pullbackGradedSections g hV :=
  DirectSum.ringHom_ext fun n x ↦ by
    rw [RingHom.comp_apply, CommMon.restrictGradedSections_of, pullbackGradedSections_of,
      pullbackGradedSections_of, pullbackComponentSections_apply, pullbackComponentSections_apply,
      Scheme.Hom.pullbackSectionsLE_map]

/-- Pullback of sections, as a homomorphism of graded rings from the sections of `A` over `U`,
graded by their summands, to those of `g^* A` over `V ≤ g⁻¹ U`. Its underlying ring
homomorphism is `pullbackGradedSections` (`pullbackGradedSectionsGradedHom_toRingHom`). -/
def pullbackGradedSectionsGradedHom :
    A.obj.gradedSectionsGrading U →+*ᵍ ((pullback g).obj A).obj.gradedSectionsGrading V where
  __ := A.pullbackGradedSections g hV
  map_mem {n x} hx := by
    obtain ⟨x, rfl⟩ := DirectSum.mem_summand.mp hx
    simpa using ((pullback g).obj A).obj.of_mem_gradedSectionsGrading n _

/-- The underlying ring homomorphism of the graded pullback of sections is the pullback of
sections. -/
@[simp]
theorem pullbackGradedSectionsGradedHom_toRingHom :
    (A.pullbackGradedSectionsGradedHom g hV).toRingHom = A.pullbackGradedSections g hV :=
  (rfl)

/-- The graded pullback of sections is the pullback of sections. -/
@[simp]
theorem pullbackGradedSectionsGradedHom_apply (x : ⨁ n, Γ(A.obj.X n, U)) :
    A.pullbackGradedSectionsGradedHom g hV x = A.pullbackGradedSections g hV x :=
  (rfl)

end GradedQuasicoherentAlgebra

end

end TauCeti.AlgebraicGeometry
