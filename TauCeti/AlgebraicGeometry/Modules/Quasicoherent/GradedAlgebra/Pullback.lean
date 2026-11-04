/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Basic

/-!
# Pullback of graded quasicoherent algebras

For a morphism of schemes `g : X ⟶ Y` and a graded quasicoherent algebra `A = ⨁ₙ Aₙ` on `Y`, the
pullback `g^* A` is the graded quasicoherent algebra on `X` whose homogeneous components are the
pullbacks `g^* Aₙ`. Its unit is `𝒪_X ≅ g^* 𝒪_Y ⟶ g^* A₀` and its homogeneous multiplications are

`g^* Aᵢ ⊗ g^* Aⱼ ≅ g^* (Aᵢ ⊗ Aⱼ) ⟶ g^* Aᵢ₊ⱼ`.

These are transported along pullback, which is strong symmetric monoidal on quasicoherent sheaves
(`AlgebraicGeometry.Scheme.Modules.pullbackToModulesBraided`). In particular the degree-zero part
of `g^* A` is the pullback `g^* A₀` of the degree-zero part of `A`
(`GradedQuasicoherentAlgebra.pullback_obj_X`), as it is an `𝒪_X`-algebra in its own right.

## Main declarations

* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullback`: the pullback `g^* A`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullback_obj_X`: its homogeneous
  components are the pullbacks of those of `A`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.mul_pullback` and
  `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.one_pullback`: its multiplications and
  unit are the pullbacks of those of `A`, through the monoidal comparisons of pullback.

## References

* [The Stacks Project, Lemma 27.16.10](https://stacks.math.columbia.edu/tag/01O3), where the
  relative `Proj` of the pulled-back graded algebra is the base change of the relative `Proj`.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (A : GradedQuasicoherentAlgebra Y)

/-- Pullback from quasicoherent sheaves on `Y` to modules on `X`, the strong symmetric monoidal
functor along which the structure of `A` is transported. -/
private abbrev pullbackFunctor : QuasicoherentSheaf Y ⥤ X.Modules :=
  (ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback g

/-- The homogeneous components of `A`, as quasicoherent sheaves. -/
private abbrev component (n : ℕ) : QuasicoherentSheaf Y :=
  ⟨A.obj.X n, inferInstance⟩

/-- The unit of `A`, as a morphism of quasicoherent sheaves. -/
private def oneQ : 𝟙_ (QuasicoherentSheaf Y) ⟶ component A 0 :=
  ObjectProperty.homMk A.obj.toMon.one

/-- The homogeneous multiplications of `A`, as morphisms of quasicoherent sheaves. -/
private def mulQ (i j : ℕ) : component A i ⊗ component A j ⟶ component A (i + j) :=
  ObjectProperty.homMk (A.obj.toMon.mul i j)

private lemma eqToHom_component_hom {i j : ℕ} (h : i = j) :
    (eqToHom (congrArg (component A) h)).hom = eqToHom (congrArg A.obj.X h) := by
  subst h
  rfl

private lemma oneQ_mul (n : ℕ) :
    (oneQ A ▷ component A n) ≫ mulQ A 0 n =
      (λ_ (component A n)).hom ≫ eqToHom (congrArg (component A) (zero_add n).symm) :=
  ObjectProperty.hom_ext _ ((A.obj.toMon.one_mul n).trans
    (congrArg ((λ_ _).hom ≫ ·) (eqToHom_component_hom A (zero_add n).symm).symm))

private lemma mulQ_one (n : ℕ) :
    (component A n ◁ oneQ A) ≫ mulQ A n 0 =
      (ρ_ (component A n)).hom ≫ eqToHom (congrArg (component A) (add_zero n).symm) :=
  ObjectProperty.hom_ext _ ((A.obj.toMon.mul_one n).trans
    (congrArg ((ρ_ _).hom ≫ ·) (eqToHom_component_hom A (add_zero n).symm).symm))

private lemma mulQ_assoc (i j k : ℕ) :
    (mulQ A i j ▷ component A k) ≫ mulQ A (i + j) k =
      (α_ _ _ _).hom ≫ (component A i ◁ mulQ A j k) ≫ mulQ A i (j + k) ≫
        eqToHom (congrArg (component A) (add_assoc i j k).symm) :=
  ObjectProperty.hom_ext _ ((A.obj.toMon.mul_assoc i j k).trans
    (congrArg (fun φ ↦ (α_ _ _ _).hom ≫ (A.obj.X i ◁ A.obj.toMon.mul j k) ≫
      A.obj.toMon.mul i (j + k) ≫ φ) (eqToHom_component_hom A (add_assoc i j k).symm).symm))

private lemma mulQ_comm (i j : ℕ) :
    (β_ (component A i) (component A j)).hom ≫ mulQ A j i =
      mulQ A i j ≫ eqToHom (congrArg (component A) (add_comm i j)) :=
  ObjectProperty.hom_ext _ ((CommMon.mul_comm A.obj i j).trans
    (congrArg (A.obj.toMon.mul i j ≫ ·) (eqToHom_component_hom A (add_comm i j)).symm))

/-- The inverse tensor comparison of pullback on quasicoherent sheaves is the inverse of the
canonical comparison `g^* (M ⊗ N) ⟶ g^* M ⊗ g^* N`. -/
private lemma μ_pullbackFunctor (i j : ℕ) :
    Functor.LaxMonoidal.μ (pullbackFunctor g) (component A i) (component A j) =
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) (A.obj.X i) (A.obj.X j)) := by
  have h := Scheme.Modules.pullbackToModules_δ g (component A i) (component A j)
  refine IsIso.eq_inv_of_hom_inv_id ?_
  exact (congrArg (· ≫ _) h.symm).trans (Functor.Monoidal.δ_μ _ _ _)

/-- The inverse unit comparison of pullback on quasicoherent sheaves is the identification
`𝒪_X ≅ g^* 𝒪_Y`. -/
private lemma ε_pullbackFunctor :
    Functor.LaxMonoidal.ε (pullbackFunctor g) = (Scheme.Modules.pullbackObjUnitIso g).inv := by
  rw [← cancel_epi (Scheme.Modules.pullbackObjUnitIso g).hom, Iso.hom_inv_id,
    ← Scheme.Modules.pullbackToModules_η]
  exact Functor.Monoidal.η_ε _

/-- The homogeneous multiplications of the pullback of `A`: the pullbacks of those of `A`, through
the inverse tensor comparison `g^* Aᵢ ⊗ g^* Aⱼ ≅ g^* (Aᵢ ⊗ Aⱼ)` of pullback. -/
def pullbackMul (i j : ℕ) :
    (Scheme.Modules.pullback g).obj (A.obj.X i) ⊗ (Scheme.Modules.pullback g).obj (A.obj.X j) ⟶
      (Scheme.Modules.pullback g).obj (A.obj.X (i + j)) :=
  inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) (A.obj.X i) (A.obj.X j)) ≫
    (Scheme.Modules.pullback g).map (A.obj.toMon.mul i j)

/-- The unit of the pullback of `A`: the pullback of the unit of `A`, through the identification
`𝒪_X ≅ g^* 𝒪_Y`. -/
def pullbackOne : 𝟙_ X.Modules ⟶ (Scheme.Modules.pullback g).obj (A.obj.X 0) :=
  (Scheme.Modules.pullbackObjUnitIso g).inv ≫ (Scheme.Modules.pullback g).map A.obj.toMon.one

private lemma pullbackMul_eq (i j : ℕ) :
    pullbackMul g A i j =
      ((Iso.refl ((pullbackFunctor g).obj (component A i))).hom ⊗ₘ
          (Iso.refl ((pullbackFunctor g).obj (component A j))).hom) ≫
        Functor.LaxMonoidal.μ (pullbackFunctor g) (component A i) (component A j) ≫
          (pullbackFunctor g).map (mulQ A i j) ≫
            (Iso.refl ((pullbackFunctor g).obj (component A (i + j)))).inv := by
  simp only [Iso.refl_hom, Iso.refl_inv, tensorHom_id, id_whiskerRight, Category.id_comp,
    Category.comp_id, μ_pullbackFunctor, pullbackMul]
  rfl

private lemma pullbackOne_eq :
    pullbackOne g A =
      Functor.LaxMonoidal.ε (pullbackFunctor g) ≫ (pullbackFunctor g).map (oneQ A) ≫
        (Iso.refl ((pullbackFunctor g).obj (component A 0))).inv := by
  simp only [Iso.refl_inv, Category.comp_id, ε_pullbackFunctor, pullbackOne]
  rfl

/-- The unit of the pullback of `A` is a left unit for its multiplications. -/
theorem pullbackOne_mul (n : ℕ) :
    (pullbackOne g A ▷ _) ≫ pullbackMul g A 0 n =
      (λ_ _).hom ≫ eqToHom (congrArg (fun n ↦ (Scheme.Modules.pullback g).obj (A.obj.X n))
        (zero_add n).symm) :=
  GradedObject.one_mul_of_laxMonoidal _ _ (pullbackMul_eq g A) _ _ (pullbackOne_eq g A)
    (oneQ_mul A) n

/-- The unit of the pullback of `A` is a right unit for its multiplications. -/
theorem pullbackMul_one (n : ℕ) :
    (_ ◁ pullbackOne g A) ≫ pullbackMul g A n 0 =
      (ρ_ _).hom ≫ eqToHom (congrArg (fun n ↦ (Scheme.Modules.pullback g).obj (A.obj.X n))
        (add_zero n).symm) :=
  GradedObject.mul_one_of_laxMonoidal _ _ (pullbackMul_eq g A) _ _ (pullbackOne_eq g A)
    (mulQ_one A) n

/-- The multiplications of the pullback of `A` are associative. -/
theorem pullbackMul_assoc (i j k : ℕ) :
    (pullbackMul g A i j ▷ _) ≫ pullbackMul g A (i + j) k =
      (α_ _ _ _).hom ≫ (_ ◁ pullbackMul g A j k) ≫ pullbackMul g A i (j + k) ≫
        eqToHom (congrArg (fun n ↦ (Scheme.Modules.pullback g).obj (A.obj.X n))
          (add_assoc i j k).symm) :=
  GradedObject.mul_assoc_of_laxMonoidal _ _ (pullbackMul_eq g A) (mulQ_assoc A) i j k

/-- The multiplications of the pullback of `A` are commutative. -/
theorem pullbackMul_comm (i j : ℕ) :
    (β_ _ _).hom ≫ pullbackMul g A j i =
      pullbackMul g A i j ≫ eqToHom (congrArg (fun n ↦ (Scheme.Modules.pullback g).obj
        (A.obj.X n)) (add_comm i j)) :=
  GradedObject.mul_comm_of_laxBraided _ _ (pullbackMul_eq g A) (mulQ_comm A) i j

/-- The **pullback** `g^* A` of a graded quasicoherent algebra `A` on `Y` along `g : X ⟶ Y`: its
homogeneous components are the pullbacks `g^* Aₙ`, with the unit `pullbackOne g A` and the
homogeneous multiplications `pullbackMul g A`. -/
@[expose]
def pullback : GradedQuasicoherentAlgebra X :=
  haveI (n : ℕ) : ((Scheme.Modules.pullback g).obj (A.obj.X n)).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pullback g _
  letI := GradedObject.monObjOfHomogeneous (fun n ↦ (Scheme.Modules.pullback g).obj (A.obj.X n))
    (pullbackOne g A) (pullbackMul g A) (pullbackOne_mul g A) (pullbackMul_one g A)
    (pullbackMul_assoc g A)
  haveI := GradedObject.isCommMonObj_monObjOfHomogeneous
    (fun n ↦ (Scheme.Modules.pullback g).obj (A.obj.X n)) (pullbackOne g A) (pullbackMul g A)
    (pullbackOne_mul g A) (pullbackMul_one g A) (pullbackMul_assoc g A) (pullbackMul_comm g A)
  ⟨CommMon.mk fun n ↦ (Scheme.Modules.pullback g).obj (A.obj.X n),
    (isGradedQuasicoherentAlgebra_iff _).2 inferInstance⟩

/-- The homogeneous components of `g^* A` are the pullbacks `g^* Aₙ` of those of `A`; in
particular its degree-zero part is `g^* A₀`. -/
@[simp]
theorem pullback_obj_X (n : ℕ) :
    (pullback g A).obj.X n = (Scheme.Modules.pullback g).obj (A.obj.X n) :=
  (rfl)

/-- The homogeneous multiplications of `g^* A` are those of `A` pulled back, through the inverse
tensor comparison `g^* Aᵢ ⊗ g^* Aⱼ ≅ g^* (Aᵢ ⊗ Aⱼ)` of pullback. -/
theorem mul_pullback (i j : ℕ) :
    (pullback g A).obj.toMon.mul i j =
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) (A.obj.X i) (A.obj.X j)) ≫
        (Scheme.Modules.pullback g).map (A.obj.toMon.mul i j) :=
  Mon.mul_eq _ _ _ |>.trans
    ((GradedObject.Monoidal.ιTensorObj_mulOfHomogeneous _ (pullbackMul g A) i j (i + j)
      rfl).trans (Category.comp_id _))

/-- The unit of `g^* A` is that of `A` pulled back, through the identification `𝒪_X ≅ g^* 𝒪_Y`. -/
theorem one_pullback :
    (pullback g A).obj.toMon.one =
      (Scheme.Modules.pullbackObjUnitIso g).inv ≫ (Scheme.Modules.pullback g).map A.obj.toMon.one :=
  Mon.one_eq _ |>.trans
    ((congrArg (GradedObject.Monoidal.tensorUnit₀.inv ≫ ·)
      (GradedObject.Monoidal.oneOfDegreeZero_zero
        (fun n ↦ (Scheme.Modules.pullback g).obj (A.obj.X n)) (pullbackOne g A))).trans
        (Iso.inv_hom_id_assoc _ _))

end GradedQuasicoherentAlgebra

end

end TauCeti.AlgebraicGeometry
