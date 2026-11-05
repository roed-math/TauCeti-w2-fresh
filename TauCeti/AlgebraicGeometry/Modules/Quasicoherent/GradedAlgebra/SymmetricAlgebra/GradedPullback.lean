/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Pullback
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.Adjunction
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.Pullback

/-!
# Pullback of the graded symmetric algebra

For a morphism of schemes `f : Y ⟶ X`, forgetting the grading commutes with pullback: for a
graded quasicoherent algebra `A = ⨁ₙ Aₙ` on `X`, the direct-sum algebra `⨁ₙ f^* Aₙ` of the graded
pullback is the pullback `f^* (⨁ₙ Aₙ)` of the direct-sum algebra
(`GradedQuasicoherentAlgebra.toQuasicoherentAlgebraPullbackIso`). On the summand `f^* Aₙ` it is
the pullback of the inclusion `Aₙ ⟶ ⨁ₙ Aₙ`; it is an isomorphism because pullback is a left
adjoint, so it preserves the coproduct `⨁ₙ Aₙ`.

For a quasicoherent sheaf `F` on `X`, the pullback of the graded symmetric algebra of `F` is the
graded symmetric algebra of the pullback, as graded quasicoherent algebras:

`f^* (Sym F) ≅ Sym (f^* F)` (`pullbackGradedSymmetricAlgebraIso`).

The morphism `Sym (f^* F) ⟶ f^* (Sym F)` is the graded algebra morphism extending
`f^* F ≅ f^* (Sym¹ F)` in degree one (`gradedSymmetricAlgebraLift`). Forgetting the grading, it
becomes the inverse of the isomorphism `pullbackSymmetricAlgebraIso` of quasicoherent algebras,
followed by the comparison above, since both are algebra morphisms out of `Sym (f^* F)` agreeing
on `f^* F`. The direct-sum functor reflects isomorphisms
(`GradedQuasicoherentAlgebra.isIso_of_isIso_toQuasicoherentAlgebra_map`), because each summand is
a retract of the direct sum, so the graded morphism is an isomorphism.

## Main declarations

* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.toQuasicoherentAlgebraPullbackIso`: the
  isomorphism `⨁ₙ f^* Aₙ ≅ f^* (⨁ₙ Aₙ)` of quasicoherent algebras, described on summands by
  `ιTotal_toQuasicoherentAlgebraPullbackIso_hom`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.isIso_of_isIso_toQuasicoherentAlgebra_map`:
  a graded algebra morphism whose direct sum is an isomorphism is an isomorphism;
* `TauCeti.AlgebraicGeometry.pullbackGradedSymmetricAlgebraIso`: the isomorphism
  `f^* (Sym F) ≅ Sym (f^* F)` of graded quasicoherent algebras, which in degree one is the
  pullback of `F ≅ Sym¹ F` (`degreeOne_map_pullbackGradedSymmetricAlgebraIso_inv`).

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (A : GradedQuasicoherentAlgebra X)

/-! ### Forgetting the grading commutes with pullback -/

/-- The comparison `⨁ₙ f^* Aₙ ⟶ f^* (⨁ₙ Aₙ)` of underlying modules: on the summand `f^* Aₙ`, the
pullback of the inclusion `Aₙ ⟶ ⨁ₙ Aₙ`. -/
private def toQuasicoherentAlgebraPullbackHom :
    (toQuasicoherentAlgebra.obj ((pullback f).obj A)).obj.X ⟶
      ((QuasicoherentAlgebra.pullback f).obj (toQuasicoherentAlgebra.obj A)).obj.X :=
  Cofan.IsColimit.desc (isColimitιTotal ((pullback f).obj A)) fun n ↦
    eqToHom (pullback_obj_obj_X f A n) ≫ (Scheme.Modules.pullback f).map (ιTotal A n) ≫
      eqToHom (QuasicoherentAlgebra.pullback_obj_X f _).symm

@[reassoc]
private theorem ιTotal_toQuasicoherentAlgebraPullbackHom (n : ℕ) :
    ιTotal ((pullback f).obj A) n ≫ toQuasicoherentAlgebraPullbackHom f A =
      eqToHom (pullback_obj_obj_X f A n) ≫ (Scheme.Modules.pullback f).map (ιTotal A n) ≫
        eqToHom (QuasicoherentAlgebra.pullback_obj_X f _).symm :=
  Cofan.IsColimit.fac (isColimitιTotal ((pullback f).obj A)) _ n

/-- The comparison `f^* (⨁ₙ Aₙ) ⟶ ⨁ₙ f^* Aₙ` out of the coproduct `f^* (⨁ₙ Aₙ)` of the
`f^* Aₙ`: pullback is a left adjoint, so it preserves coproducts. -/
private def pullbackToQuasicoherentAlgebraHom :
    (Scheme.Modules.pullback f).obj (toQuasicoherentAlgebra.obj A).obj.X ⟶
      (toQuasicoherentAlgebra.obj ((pullback f).obj A)).obj.X :=
  Cofan.IsColimit.desc (isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback f) _ _
    (isColimitιTotal A)) fun n ↦
      eqToHom (pullback_obj_obj_X f A n).symm ≫ ιTotal ((pullback f).obj A) n

@[reassoc]
private theorem pullback_map_ιTotal_pullbackToQuasicoherentAlgebraHom (n : ℕ) :
    (Scheme.Modules.pullback f).map (ιTotal A n) ≫ pullbackToQuasicoherentAlgebraHom f A =
      eqToHom (pullback_obj_obj_X f A n).symm ≫ ιTotal ((pullback f).obj A) n :=
  Cofan.IsColimit.fac (isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback f) _ _
    (isColimitιTotal A)) _ n

private theorem toQuasicoherentAlgebraPullbackHom_inv :
    toQuasicoherentAlgebraPullbackHom f A ≫
        eqToHom (QuasicoherentAlgebra.pullback_obj_X f _) ≫
          pullbackToQuasicoherentAlgebraHom f A = 𝟙 _ := by
  refine toQuasicoherentAlgebra_hom_ext fun n ↦ ?_
  simp only [ιTotal_toQuasicoherentAlgebraPullbackHom_assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  erw [pullback_map_ιTotal_pullbackToQuasicoherentAlgebraHom]
  simp

private theorem toQuasicoherentAlgebraPullbackInv_hom :
    (eqToHom (QuasicoherentAlgebra.pullback_obj_X f _) ≫
        pullbackToQuasicoherentAlgebraHom f A) ≫ toQuasicoherentAlgebraPullbackHom f A = 𝟙 _ := by
  rw [Category.assoc, ← cancel_epi
    (eqToHom (QuasicoherentAlgebra.pullback_obj_X f (toQuasicoherentAlgebra.obj A)).symm),
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback f) _ _
    (isColimitιTotal A)) _ _ fun n ↦ ?_
  simp [pullback_map_ιTotal_pullbackToQuasicoherentAlgebraHom_assoc,
    ιTotal_toQuasicoherentAlgebraPullbackHom]

private theorem one_toQuasicoherentAlgebraPullbackHom :
    η[(toQuasicoherentAlgebra.obj ((pullback f).obj A)).obj.X] ≫
        toQuasicoherentAlgebraPullbackHom f A =
      η[((QuasicoherentAlgebra.pullback f).obj (toQuasicoherentAlgebra.obj A)).obj.X] := by
  have h := congrArg (· ≫ toQuasicoherentAlgebraPullbackHom f A) (one_ιTotal ((pullback f).obj A))
  refine h.symm.trans ?_
  dsimp only
  erw [Category.assoc, ιTotal_toQuasicoherentAlgebraPullbackHom, pullback_obj_one,
    QuasicoherentAlgebra.pullback_obj_one, ← one_ιTotal]
  erw [Category.assoc, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Functor.map_comp, Category.assoc]
  rfl

/-- The multiplicativity of `toQuasicoherentAlgebraPullbackHom` on the summand `f^* Aᵢ ⊗ f^* Aⱼ`,
with the identifications of the objects abstracted: it is the naturality of the tensor comparison
of pullback. -/
private lemma pullback_mul_aux {Aᵢ Aⱼ Aₖ L : X.Modules} {Pᵢ Pⱼ Pₖ R : Y.Modules}
    (hᵢ : Pᵢ = (Scheme.Modules.pullback f).obj Aᵢ) (hⱼ : Pⱼ = (Scheme.Modules.pullback f).obj Aⱼ)
    (hₖ : Pₖ = (Scheme.Modules.pullback f).obj Aₖ) (hR : R = (Scheme.Modules.pullback f).obj L)
    [IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) Aᵢ Aⱼ)]
    [IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) L L)]
    (ιᵢ : Aᵢ ⟶ L) (ιⱼ : Aⱼ ⟶ L) (ιₖ : Aₖ ⟶ L) (m : Aᵢ ⊗ Aⱼ ⟶ Aₖ) (μL : L ⊗ L ⟶ L)
    (h : m ≫ ιₖ = (ιᵢ ⊗ₘ ιⱼ) ≫ μL) :
    ((eqToHom hᵢ ⊗ₘ eqToHom hⱼ) ≫ inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) Aᵢ Aⱼ) ≫
        (Scheme.Modules.pullback f).map m ≫ eqToHom hₖ.symm) ≫
        eqToHom hₖ ≫ (Scheme.Modules.pullback f).map ιₖ ≫ eqToHom hR.symm =
      ((eqToHom hᵢ ≫ (Scheme.Modules.pullback f).map ιᵢ ≫ eqToHom hR.symm) ⊗ₘ
          (eqToHom hⱼ ≫ (Scheme.Modules.pullback f).map ιⱼ ≫ eqToHom hR.symm)) ≫
        (eqToHom hR ⊗ₘ eqToHom hR) ≫ inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) L L) ≫
          (Scheme.Modules.pullback f).map μL ≫ eqToHom hR.symm := by
  subst hᵢ hⱼ hₖ hR
  have hδ : ((Scheme.Modules.pullback f).map ιᵢ ⊗ₘ (Scheme.Modules.pullback f).map ιⱼ) ≫
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) L L) =
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) Aᵢ Aⱼ) ≫
        (Scheme.Modules.pullback f).map (ιᵢ ⊗ₘ ιⱼ) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, Functor.OplaxMonoidal.δ_natural, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, id_tensorHom_id, Category.assoc]
  rw [reassoc_of% hδ, ← Functor.map_comp, ← Functor.map_comp, h]

private theorem mul_toQuasicoherentAlgebraPullbackHom :
    μ[(toQuasicoherentAlgebra.obj ((pullback f).obj A)).obj.X] ≫
        toQuasicoherentAlgebraPullbackHom f A =
      (toQuasicoherentAlgebraPullbackHom f A ⊗ₘ toQuasicoherentAlgebraPullbackHom f A) ≫
        μ[((QuasicoherentAlgebra.pullback f).obj (toQuasicoherentAlgebra.obj A)).obj.X] := by
  refine toQuasicoherentAlgebra_tensor_hom_ext fun i j ↦ ?_
  have h := congrArg (· ≫ toQuasicoherentAlgebraPullbackHom f A)
    (mul_ιTotal ((pullback f).obj A) i j)
  refine ((Category.assoc _ _ _).symm.trans h.symm).trans ?_
  dsimp only
  erw [Category.assoc, ιTotal_toQuasicoherentAlgebraPullbackHom, pullback_obj_mul,
    tensorHom_comp_tensorHom_assoc, ιTotal_toQuasicoherentAlgebraPullbackHom,
    ιTotal_toQuasicoherentAlgebraPullbackHom, QuasicoherentAlgebra.pullback_obj_mul]
  exact pullback_mul_aux f _ _ _ _ _ _ _ _ _ (mul_ιTotal A i j)

/-- **Forgetting the grading commutes with pullback.** For a morphism of schemes `f : Y ⟶ X` and a
graded quasicoherent algebra `A = ⨁ₙ Aₙ` on `X`, the direct-sum algebra `⨁ₙ f^* Aₙ` of the graded
pullback is the pullback `f^* (⨁ₙ Aₙ)` of the direct-sum algebra of `A`, as quasicoherent
algebras. -/
def toQuasicoherentAlgebraPullbackIso :
    toQuasicoherentAlgebra.obj ((pullback f).obj A) ≅
      (QuasicoherentAlgebra.pullback f).obj (toQuasicoherentAlgebra.obj A) :=
  ObjectProperty.isoMk _ <| CommMon.mkIso
    ⟨toQuasicoherentAlgebraPullbackHom f A,
      eqToHom (QuasicoherentAlgebra.pullback_obj_X f _) ≫ pullbackToQuasicoherentAlgebraHom f A,
      toQuasicoherentAlgebraPullbackHom_inv f A, toQuasicoherentAlgebraPullbackInv_hom f A⟩
    (one_toQuasicoherentAlgebraPullbackHom f A) (mul_toQuasicoherentAlgebraPullbackHom f A)

/-- On the summand `f^* Aₙ`, the isomorphism `toQuasicoherentAlgebraPullbackIso` is the pullback of
the inclusion `Aₙ ⟶ ⨁ₙ Aₙ`. -/
@[reassoc]
theorem ιTotal_toQuasicoherentAlgebraPullbackIso_hom (n : ℕ) :
    ιTotal ((pullback f).obj A) n ≫ (toQuasicoherentAlgebraPullbackIso f A).hom.hom.hom.hom =
      eqToHom (pullback_obj_obj_X f A n) ≫ (Scheme.Modules.pullback f).map (ιTotal A n) ≫
        eqToHom (QuasicoherentAlgebra.pullback_obj_X f _).symm :=
  ιTotal_toQuasicoherentAlgebraPullbackHom f A n

/-! ### The direct-sum functor reflects isomorphisms -/

variable {A}

/-- The projection `⨁ₘ Aₘ ⟶ Aₙ` onto the summand of degree `n`. -/
private def πTotal (A : GradedQuasicoherentAlgebra X) (n : ℕ) :
    (toQuasicoherentAlgebra.obj A).obj.X ⟶ A.obj.X n :=
  Cofan.IsColimit.desc (isColimitιTotal A) fun m ↦
    if h : m = n then eqToHom (congrArg A.obj.X h) else 0

private theorem ιTotal_πTotal (A : GradedQuasicoherentAlgebra X) (m n : ℕ) :
    ιTotal A m ≫ πTotal A n = if h : m = n then eqToHom (congrArg A.obj.X h) else 0 :=
  Cofan.IsColimit.fac (isColimitιTotal A) _ m

private theorem ιTotal_πTotal_self (A : GradedQuasicoherentAlgebra X) (n : ℕ) :
    ιTotal A n ≫ πTotal A n = 𝟙 _ := by
  rw [ιTotal_πTotal]
  simp

/-- A morphism of graded quasicoherent algebras whose underlying morphism of direct-sum algebras
is an isomorphism is an isomorphism: each homogeneous component is a retract of the direct sum. -/
theorem isIso_of_isIso_toQuasicoherentAlgebra_map {B : GradedQuasicoherentAlgebra X} (g : A ⟶ B)
    [IsIso (toQuasicoherentAlgebra.map g)] : IsIso g := by
  -- The underlying isomorphism `⨁ₙ Aₙ ≅ ⨁ₙ Bₙ` of modules.
  let e := (ObjectProperty.ι _ ⋙ CommMon.forget₂Mon _ ⋙ Mon.forget _).mapIso
    (asIso (toQuasicoherentAlgebra.map g))
  have hι (m : ℕ) : ιTotal A m ≫ e.hom = g.hom.hom.hom m ≫ ιTotal B m :=
    ιTotal_toQuasicoherentAlgebra_map g m
  -- The projections intertwine the direct sum of `g` with its components.
  have hπ (n : ℕ) : e.hom ≫ πTotal B n = πTotal A n ≫ g.hom.hom.hom n := by
    refine toQuasicoherentAlgebra_hom_ext fun m ↦ ?_
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ πTotal B n) (hι m)).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ιTotal_πTotal B m n)).trans ?_)))
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans
      (congrArg (· ≫ g.hom.hom.hom n) (ιTotal_πTotal A m n))).symm
    split_ifs with h
    · subst h
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact comp_zero.trans zero_comp.symm
  have hg (n : ℕ) : IsIso (g.hom.hom.hom n) :=
    ⟨ιTotal B n ≫ e.inv ≫ πTotal A n,
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (hι n).symm).trans
        ((Category.assoc _ _ _).trans ((congrArg (ιTotal A n ≫ ·) (e.hom_inv_id_assoc _)).trans
          (ιTotal_πTotal_self A n)))),
      (Category.assoc _ _ _).trans ((congrArg (ιTotal B n ≫ ·)
        (((Category.assoc _ _ _).trans (congrArg (e.inv ≫ ·) (hπ n).symm)).trans
          (e.inv_hom_id_assoc _))).trans (ιTotal_πTotal_self B n))⟩
  have : IsIso g.hom.hom.hom := GradedObject.isIso_of_isIso_apply _
  have : IsIso ((ObjectProperty.ι _ ⋙ CommMon.forget₂Mon _ ⋙ Mon.forget _).map g) := this
  exact isIso_of_reflects_iso g (ObjectProperty.ι _ ⋙ CommMon.forget₂Mon _ ⋙ Mon.forget _)

end GradedQuasicoherentAlgebra

/-! ### The pullback of the graded symmetric algebra -/

open GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (F : QuasicoherentSheaf X)

/-- The identification `f^* F ≅ f^* (Sym¹ F)` of `f^* F` with the degree-one component of
`f^* (Sym F)`. -/
private def pullbackDegreeOneIso :
    (QuasicoherentSheaf.pullback f).obj F ≅
      degreeOne.obj
        ((GradedQuasicoherentAlgebra.pullback f).obj ((gradedSymmetricAlgebra X).obj F)) :=
  (QuasicoherentSheaf.pullback f).mapIso ((gradedSymmetricAlgebraDegreeOneIso X).app F).symm ≪≫
    ((pullbackDegreeIso f 1).app _).symm

/-- The graded algebra morphism `Sym (f^* F) ⟶ f^* (Sym F)` extending `f^* F ≅ f^* (Sym¹ F)`. -/
private def gradedSymmetricAlgebraPullbackHom :
    (gradedSymmetricAlgebra Y).obj ((QuasicoherentSheaf.pullback f).obj F) ⟶
      (GradedQuasicoherentAlgebra.pullback f).obj ((gradedSymmetricAlgebra X).obj F) :=
  gradedSymmetricAlgebraLift (pullbackDegreeOneIso f F).hom

/-- The computation on generators behind
`toQuasicoherentAlgebra_map_gradedSymmetricAlgebraPullbackHom`, with the identifications of the
objects abstracted. -/
private lemma gradedSymmetricAlgebraPullbackHom_aux {F₀ D S₁ L : X.Modules}
    {GF B₁ S₁' P₁ D' M Lp R L' : Y.Modules} (a : F₀ ⟶ D) (d : D = S₁) (j : S₁ ⟶ L)
    (b : GF ⟶ B₁) (e₁ : B₁ = S₁') (j' : S₁' ⟶ L') (Ψ : L' ⟶ Lp)
    (ψ₁ : S₁' ⟶ P₁) (jP : P₁ ⟶ Lp) (κ : Lp ⟶ R) (θ : L' ⟶ R) (dψ : B₁ ⟶ D')
    (m₁ : GF ⟶ M) (m₂ : M ⟶ D') (e₂ : P₁ = D')
    (e₃ : P₁ = (Scheme.Modules.pullback f).obj S₁) (e₄ : (Scheme.Modules.pullback f).obj L = R)
    (p : GF = (Scheme.Modules.pullback f).obj F₀) (q : (Scheme.Modules.pullback f).obj D = M)
    (r : M = D') (e₆ : GF = (Scheme.Modules.pullback f).obj F₀)
    (e₇ : (Scheme.Modules.pullback f).obj L = R)
    (h₂ : j' ≫ Ψ = ψ₁ ≫ jP)
    (h₃ : jP ≫ κ = eqToHom e₃ ≫ (Scheme.Modules.pullback f).map j ≫ eqToHom e₄)
    (h₄ : b ≫ dψ = m₁ ≫ m₂) (hdψ : dψ = eqToHom e₁ ≫ ψ₁ ≫ eqToHom e₂)
    (hm₁ : m₁ = eqToHom p ≫ (Scheme.Modules.pullback f).map a ≫ eqToHom q) (hm₂ : m₂ = eqToHom r)
    (h₇ : (b ≫ eqToHom e₁ ≫ j') ≫ θ =
      eqToHom e₆ ≫ (Scheme.Modules.pullback f).map (a ≫ eqToHom d ≫ j) ≫ eqToHom e₇) :
    (b ≫ eqToHom e₁ ≫ j') ≫ Ψ ≫ κ = (b ≫ eqToHom e₁ ≫ j') ≫ θ := by
  subst hm₁ hm₂ hdψ
  subst_vars
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at *
  rw [h₇, Category.assoc, reassoc_of% h₂, h₃, ← Category.assoc, h₄, Functor.map_comp]

/-- Forgetting the grading, the graded algebra morphism `Sym (f^* F) ⟶ f^* (Sym F)` is the inverse
of `pullbackSymmetricAlgebraIso`, followed by `toQuasicoherentAlgebraPullbackIso`. -/
private theorem toQuasicoherentAlgebra_map_gradedSymmetricAlgebraPullbackHom :
    toQuasicoherentAlgebra.map (gradedSymmetricAlgebraPullbackHom f F) ≫
        (toQuasicoherentAlgebraPullbackIso f _).hom =
      (pullbackSymmetricAlgebraIso f F).inv := by
  refine ObjectProperty.hom_ext _ (symmetricAlgebra_hom_ext ?_)
  rw [symmetricAlgebraι_def]
  refine gradedSymmetricAlgebraPullbackHom_aux f
    (a := ((gradedSymmetricAlgebraDegreeOneIso X).inv.app F).hom)
    (j := ιTotal ((gradedSymmetricAlgebra X).obj F) 1)
    (b := ((gradedSymmetricAlgebraDegreeOneIso Y).inv.app
      ((QuasicoherentSheaf.pullback f).obj F)).hom)
    (j' := ιTotal ((gradedSymmetricAlgebra Y).obj ((QuasicoherentSheaf.pullback f).obj F)) 1)
    (Ψ := (toQuasicoherentAlgebra.map (gradedSymmetricAlgebraPullbackHom f F)).hom.hom.hom)
    (θ := (pullbackSymmetricAlgebraIso f F).inv.hom.hom.hom)
    (h₂ := ιTotal_toQuasicoherentAlgebra_map _ 1)
    (h₃ := ιTotal_toQuasicoherentAlgebraPullbackIso_hom f _ 1)
    (h₄ := (ObjectProperty.FullSubcategory.comp_hom ..).symm.trans
      ((congrArg (fun φ ↦ φ.hom) (gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift
        (pullbackDegreeOneIso f F).hom)).trans (ObjectProperty.FullSubcategory.comp_hom ..)))
    (hdψ := degree_map_hom _ 1) (hm₁ := QuasicoherentSheaf.pullback_map_hom f _)
    (hm₂ := pullbackDegreeIso_inv_app_hom f 1 _) (d := degree_obj_obj _ 1)
    (e₆ := QuasicoherentSheaf.pullback_obj_obj f F)
    (e₇ := (QuasicoherentAlgebra.pullback_obj_X f _).symm) (h₇ := ?_)
  exact (congrArg (· ≫ _)
    (symmetricAlgebraι_def ((QuasicoherentSheaf.pullback f).obj F))).symm.trans
    ((symmetricAlgebraι_comp_pullbackSymmetricAlgebraIso_inv f F).trans
      (congrArg (fun s ↦ _ ≫ (Scheme.Modules.pullback f).map s ≫ _) (symmetricAlgebraι_def F)))


/-- **Pullback of the graded symmetric algebra.** For a morphism of schemes `f : Y ⟶ X` and a
quasicoherent sheaf `F` on `X`, the pullback `f^* (Sym F)` of the graded symmetric algebra of `F`
is isomorphic, as a graded quasicoherent algebra, to the graded symmetric algebra `Sym (f^* F)` of
the pullback of `F`. The inverse extends the identification `f^* F ≅ f^* (Sym¹ F)`
(`degreeOne_map_pullbackGradedSymmetricAlgebraIso_inv`). -/
def pullbackGradedSymmetricAlgebraIso :
    (GradedQuasicoherentAlgebra.pullback f).obj ((gradedSymmetricAlgebra X).obj F) ≅
      (gradedSymmetricAlgebra Y).obj ((QuasicoherentSheaf.pullback f).obj F) :=
  have h := (Iso.eq_comp_inv (toQuasicoherentAlgebraPullbackIso f _)).mpr
    (toQuasicoherentAlgebra_map_gradedSymmetricAlgebraPullbackHom f F)
  have : IsIso (toQuasicoherentAlgebra.map (gradedSymmetricAlgebraPullbackHom f F)) := by
    rw [h]
    infer_instance
  have := isIso_of_isIso_toQuasicoherentAlgebra_map (gradedSymmetricAlgebraPullbackHom f F)
  (asIso (gradedSymmetricAlgebraPullbackHom f F)).symm

/-- In degree one, the inverse of `pullbackGradedSymmetricAlgebraIso` is the pullback of the
identification `F ≅ Sym¹ F`: through `f^* F ≅ Sym¹ (f^* F)` it is
`f^* F ≅ f^* (Sym¹ F) = (f^* (Sym F))₁`. -/
@[reassoc]
theorem degreeOne_map_pullbackGradedSymmetricAlgebraIso_inv :
    (gradedSymmetricAlgebraDegreeOneIso Y).inv.app ((QuasicoherentSheaf.pullback f).obj F) ≫
        degreeOne.map (pullbackGradedSymmetricAlgebraIso f F).inv =
      (QuasicoherentSheaf.pullback f).map ((gradedSymmetricAlgebraDegreeOneIso X).inv.app F) ≫
        (pullbackDegreeIso f 1).inv.app ((gradedSymmetricAlgebra X).obj F) :=
  gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift (pullbackDegreeOneIso f F).hom

end

end AlgebraicGeometry

end TauCeti
