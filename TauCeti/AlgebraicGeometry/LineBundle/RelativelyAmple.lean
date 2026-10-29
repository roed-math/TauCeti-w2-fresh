/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.RelativeProj.Proper
public import TauCeti.Lookahead.RelativeAmpleness.Stubs

/-!
# Relatively very ample line bundles and projective morphisms

Let `f : X ⟶ S` be a morphism of schemes. A line bundle `L` on `X` is *relatively very ample* for
`f` if there are a graded quasi-coherent `𝒪_S`-algebra `A`, generated in degree one with `A₁` of
finite type, and an immersion `i : X ⟶ Proj_S(A)` over `S` with `i^* 𝒪(1) ≅ L`. The morphism `f`
is *projective* if it factors as a closed immersion into such a relative `Proj` followed by its
structure morphism. A line bundle is *relatively ample* if some positive tensor power of it is
relatively very ample.

Since `A₁` generates `A` and is of finite type, `Proj_S(A)` is a closed subscheme of
`ℙ(A₁) = Proj_S(Sym A₁)` with `𝒪(1)` pulling back to `𝒪(1)`, so these are the notions of the
Stacks Project defined through `ℙ(ℰ)` for a quasi-coherent `𝒪_S`-module `ℰ` of finite type. For
a morphism of finite type over a quasi-compact base, relative ampleness as defined here is the
Stacks Project characterization of relative ampleness by a relatively very ample tensor power.

## Main definitions

* `TauCeti.AlgebraicGeometry.InvertibleSheaf.IsRelativelyVeryAmple L f`: `L` is relatively very
  ample for `f`.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.IsRelativelyAmple L f`: some positive tensor power
  of `L` is relatively very ample for `f`.
* `TauCeti.AlgebraicGeometry.IsProjective f`: `f` is projective.

## Main results

* `TauCeti.AlgebraicGeometry.InvertibleSheaf.isRelativelyVeryAmple_relativeProjTwistingSheaf`:
  `𝒪(1)` is relatively very ample on the relative `Proj` of an algebra generated in degree one.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.IsRelativelyVeryAmple.pullback` and
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.IsRelativelyAmple.pullback`: relative (very)
  ampleness is preserved by pullback along an immersion.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.IsRelativelyAmple.of_tensorPow`: a line bundle with
  a relatively ample positive tensor power is relatively ample.
* `TauCeti.AlgebraicGeometry.IsProjective.exists_isRelativelyVeryAmple`: a projective morphism
  has a relatively very ample line bundle.
* `TauCeti.AlgebraicGeometry.IsProjective.isSeparated`: a projective morphism is separated.

## References

* The Stacks Project, Chapter *Morphisms of Schemes*, sections *Relatively ample sheaves*,
  *Very ample sheaves* and *Projective morphisms*.
* R. Hartshorne, *Algebraic Geometry*, Sections II.5 and II.7.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X Y S : Scheme.{u}}

/-- The invertible sheaf `𝒪(1)` on the relative `Proj` of a graded algebra generated in degree
one. -/
noncomputable abbrev _root_.CategoryTheory.CommMon.relativeProjTwistingSheafOne
    (A : CommMon (GradedObject ℕ S.Modules)) [∀ n, (A.X n).IsQuasicoherent]
    (hA : A.IsGeneratedInDegreeOne) : InvertibleSheaf A.relativeProj :=
  ⟨A.relativeProjTwistingSheaf 1, A.isInvertible_relativeProjTwistingSheaf_one hA⟩

namespace InvertibleSheaf

/-- A line bundle `L` on `X` is **relatively very ample** for `f : X ⟶ S` if there are a graded
quasi-coherent `𝒪_S`-algebra `A`, generated in degree one with `A₁` of finite type, and an
immersion `i : X ⟶ Proj_S(A)` over `S` such that `i^* 𝒪(1) ≅ L`. -/
def IsRelativelyVeryAmple (L : InvertibleSheaf X) (f : X ⟶ S) : Prop :=
  ∃ (A : CommMon (GradedObject ℕ S.Modules)) (_ : ∀ n, (A.X n).IsQuasicoherent)
    (_ : A.IsGeneratedInDegreeOne) (_ : (A.X 1).IsFiniteType) (i : X ⟶ A.relativeProj),
    IsImmersion i ∧ i ≫ A.relativeProjToBase = f ∧
      Nonempty ((Scheme.Modules.pullback i).obj (A.relativeProjTwistingSheaf 1) ≅ L.obj)

/-- Relative very ampleness depends only on the isomorphism class of the line bundle. -/
theorem IsRelativelyVeryAmple.of_iso {L K : InvertibleSheaf X} {f : X ⟶ S}
    (hL : L.IsRelativelyVeryAmple f) (e : L.obj ≅ K.obj) : K.IsRelativelyVeryAmple f := by
  obtain ⟨A, _, hA, h₁, i, hi, hif, ⟨e'⟩⟩ := hL
  exact ⟨A, _, hA, h₁, i, hi, hif, ⟨e' ≪≫ e⟩⟩

/-- **`𝒪(1)` is relatively very ample.** On the relative `Proj` of a graded algebra generated in
degree one by a finite type `A₁`, the twisting sheaf `𝒪(1)` is relatively very ample for the
structure morphism. -/
theorem isRelativelyVeryAmple_relativeProjTwistingSheaf (A : CommMon (GradedObject ℕ S.Modules))
    [∀ n, (A.X n).IsQuasicoherent] (hA : A.IsGeneratedInDegreeOne) [(A.X 1).IsFiniteType] :
    (A.relativeProjTwistingSheafOne hA).IsRelativelyVeryAmple A.relativeProjToBase :=
  ⟨A, inferInstance, hA, inferInstance, 𝟙 _, inferInstance, Category.id_comp _,
    ⟨(Scheme.Modules.pullbackId _).app _⟩⟩

/-- **Relative very ampleness is preserved by pullback along an immersion.** If `L` is relatively
very ample for `f` and `j : Y ⟶ X` is an immersion, then `j^* L` is relatively very ample for
`j ≫ f`. -/
theorem IsRelativelyVeryAmple.pullback {L : InvertibleSheaf X} {f : X ⟶ S}
    (hL : L.IsRelativelyVeryAmple f) (j : Y ⟶ X) [IsImmersion j] :
    ((InvertibleSheaf.pullback j).obj L).IsRelativelyVeryAmple (j ≫ f) := by
  obtain ⟨A, _, hA, h₁, i, hi, rfl, ⟨e⟩⟩ := hL
  exact ⟨A, _, hA, h₁, j ≫ i, inferInstance, Category.assoc _ _ _,
    ⟨((Scheme.Modules.pullbackComp j i).app _).symm ≪≫ (Scheme.Modules.pullback j).mapIso e⟩⟩

/-- A relatively very ample line bundle lives on a scheme separated over the base. -/
theorem IsRelativelyVeryAmple.isSeparated {L : InvertibleSheaf X} {f : X ⟶ S}
    (hL : L.IsRelativelyVeryAmple f) : IsSeparated f := by
  obtain ⟨A, _, -, -, i, hi, rfl, -⟩ := hL
  infer_instance

/-- A line bundle `L` on `X` is **relatively ample** for `f : X ⟶ S` if some positive tensor
power `L^{⊗m}` is relatively very ample for `f`. -/
def IsRelativelyAmple (L : InvertibleSheaf X) (f : X ⟶ S) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (L.tensorPow m).IsRelativelyVeryAmple f

/-- A relatively very ample line bundle is relatively ample. -/
theorem IsRelativelyVeryAmple.isRelativelyAmple {L : InvertibleSheaf X} {f : X ⟶ S}
    (hL : L.IsRelativelyVeryAmple f) : L.IsRelativelyAmple f := by
  refine ⟨1, Nat.one_pos, hL.of_iso (Classical.choice ?_)⟩
  rw [← LineBundleClass.mk_eq_mk_iff, LineBundleClass.mk_tensorPow, pow_one]

/-- If a positive tensor power `L^{⊗m}` is relatively ample for `f`, then so is `L`. -/
theorem IsRelativelyAmple.of_tensorPow {L : InvertibleSheaf X} {f : X ⟶ S} {m : ℕ} (hm : 0 < m)
    (hL : (L.tensorPow m).IsRelativelyAmple f) : L.IsRelativelyAmple f := by
  obtain ⟨n, hn, hLn⟩ := hL
  exact ⟨m * n, Nat.mul_pos hm hn, hLn.of_iso (nonempty_tensorPow_tensorPow_iso L m n).some⟩

/-- Relative ampleness depends only on the isomorphism class of the line bundle. -/
theorem IsRelativelyAmple.of_iso {L K : InvertibleSheaf X} {f : X ⟶ S}
    (hL : L.IsRelativelyAmple f) (e : L.obj ≅ K.obj) : K.IsRelativelyAmple f := by
  obtain ⟨m, hm, hLm⟩ := hL
  exact ⟨m, hm, hLm.of_iso (nonempty_tensorPow_obj_iso ⟨e⟩ m).some⟩

/-- **Relative ampleness is preserved by pullback along an immersion.** If `L` is relatively
ample for `f` and `j : Y ⟶ X` is an immersion, then `j^* L` is relatively ample for `j ≫ f`. -/
theorem IsRelativelyAmple.pullback {L : InvertibleSheaf X} {f : X ⟶ S}
    (hL : L.IsRelativelyAmple f) (j : Y ⟶ X) [IsImmersion j] :
    ((InvertibleSheaf.pullback j).obj L).IsRelativelyAmple (j ≫ f) := by
  obtain ⟨m, hm, hLm⟩ := hL
  exact ⟨m, hm, (hLm.pullback j).of_iso (nonempty_pullback_tensorPow_iso j L m).some⟩

/-- A relatively ample line bundle lives on a scheme separated over the base. -/
theorem IsRelativelyAmple.isSeparated {L : InvertibleSheaf X} {f : X ⟶ S}
    (hL : L.IsRelativelyAmple f) : IsSeparated f := by
  obtain ⟨_, -, hLm⟩ := hL
  exact hLm.isSeparated

end InvertibleSheaf

/-- A morphism `f : X ⟶ S` is **projective** if it factors as a closed immersion
`i : X ⟶ Proj_S(A)` followed by the structure morphism of the relative `Proj` of a graded
quasi-coherent `𝒪_S`-algebra `A` generated in degree one with `A₁` of finite type. -/
class IsProjective (f : X ⟶ S) : Prop where
  exists_isClosedImmersion : ∃ (A : CommMon (GradedObject ℕ S.Modules))
    (_ : ∀ n, (A.X n).IsQuasicoherent) (_ : A.IsGeneratedInDegreeOne) (_ : (A.X 1).IsFiniteType)
    (i : X ⟶ A.relativeProj), IsClosedImmersion i ∧ i ≫ A.relativeProjToBase = f

/-- The structure morphism of the relative `Proj` of a graded algebra generated in degree one by
a finite type `A₁` is projective. -/
theorem isProjective_relativeProjToBase (A : CommMon (GradedObject ℕ S.Modules))
    [∀ n, (A.X n).IsQuasicoherent] (hA : A.IsGeneratedInDegreeOne) [(A.X 1).IsFiniteType] :
    IsProjective A.relativeProjToBase :=
  ⟨A, inferInstance, hA, inferInstance, 𝟙 _, inferInstance, Category.id_comp _⟩

/-- A closed immersion followed by a projective morphism is projective. -/
instance (j : Y ⟶ X) [IsClosedImmersion j] (f : X ⟶ S) [IsProjective f] :
    IsProjective (j ≫ f) := by
  obtain ⟨A, _, hA, h₁, i, hi, rfl⟩ := IsProjective.exists_isClosedImmersion (f := f)
  exact ⟨A, _, hA, h₁, j ≫ i, inferInstance, Category.assoc _ _ _⟩

/-- **A projective morphism has a relatively very ample line bundle**: the pullback of `𝒪(1)`
along the closed immersion into the relative `Proj`. -/
theorem IsProjective.exists_isRelativelyVeryAmple (f : X ⟶ S) [IsProjective f] :
    ∃ L : InvertibleSheaf X, L.IsRelativelyVeryAmple f := by
  obtain ⟨A, _, hA, h₁, i, hi, rfl⟩ := IsProjective.exists_isClosedImmersion (f := f)
  exact ⟨(InvertibleSheaf.pullback i).obj (A.relativeProjTwistingSheafOne hA),
    A, _, hA, h₁, i, inferInstance, rfl, ⟨Iso.refl _⟩⟩

/-- A projective morphism is separated. -/
instance IsProjective.isSeparated (f : X ⟶ S) [IsProjective f] : IsSeparated f :=
  (IsProjective.exists_isRelativelyVeryAmple f).choose_spec.isSeparated

end AlgebraicGeometry

end TauCeti
