/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ModularCurve.NaiveGammaZero.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel
public import TauCeti.AlgebraicGeometry.FiniteEtale.Quotient
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.AlgebraicGeometry.Morphisms.FormallyUnramified
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# The Borel quotient of the naive `[Γ(N)]` carrier

Let a group `G` act on a relatively representable moduli problem `𝒫` over `Ell/B`, so that it acts
on every representing scheme `𝒫_{E/S}` over `S` (`ModuliProblem.RelRepData.repAction`). When `𝒫`
is finite étale over `Ell/B`, this action is a functor from `G` to finite étale `S`-schemes
(`ModuliProblem.RelRepData.repActionFunctor`), whose quotient exists
(`TauCeti.FiniteEtaleScheme.quotient`).

For the naive full level-`N` problem `[Γ(N)]`, finite étale over `Ell/B` where `N` is invertible on
`B`, and the Borel subgroup of `GL₂(ℤ/Nℤ)` of upper triangular matrices (`TauCeti.GL2Borel`),
acting through `ModuliProblem.gammaNaiveAction`, this gives the Borel action on the `[Γ(N)]`
carrier (`ModuliProblem.gammaNaiveBorelAction`). Its finite étale quotient is the **naive
`[Γ₀(N)]` carrier** (`ModuliProblem.gammaZeroNaiveCarrier`) of Katz and Mazur, §7.1. The action of
`GL₂(ℤ/Nℤ)` on naive full level structures is free, so by the constant-group case of the quotient
theorem of SGA 3, Exposé V, Théorème 4.1, the quotient map is a Borel torsor
(`ModuliProblem.isPullback_gammaZeroNaiveCarrierπ`). It is finite étale and surjective, and two
naive full level structures over a field with the same image in the carrier differ by a Borel
element (`ModuliProblem.exists_gammaNaiveAction_hom_app_eq_of_comp_gammaZeroNaiveCarrierπ_eq`).
Conversely, the naive `[Γ₀(N)]`-structure `⟨P⟩` attached to a point of the `[Γ(N)]` carrier is
constant on Borel orbits
(`ModuliProblem.gammaNaiveToGammaZeroNaive_app_homEquiv_comp_repAction_hom`), and two points of the
`[Γ(N)]` carrier with values in any `T` whose naive full level structures generate the same naive
cyclic subgroup have the same image in the `[Γ₀(N)]` carrier
(`ModuliProblem.comp_gammaZeroNaiveCarrierπ_eq_of_gammaNaiveToGammaZeroNaive_app_eq`): they differ
by a Borel element over every geometric point, and the carrier is separated and unramified.

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.repActionFunctor`: the action of a group on a
  finite étale representing scheme, as a functor to finite étale schemes.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaiveBorelAction`: the Borel action on the naive
  `[Γ(N)]` carrier.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaZeroNaiveCarrier`: its quotient, the naive
  `[Γ₀(N)]` carrier, with the quotient map `gammaZeroNaiveCarrierπ`.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.isPullback_gammaZeroNaiveCarrierπ`: the quotient map of
  the `[Γ(N)]` carrier to the naive `[Γ₀(N)]` carrier is a Borel torsor.
* `ModuliProblem.exists_gammaNaiveAction_hom_app_eq_of_comp_gammaZeroNaiveCarrierπ_eq`: points of
  the naive `[Γ₀(N)]` carrier with values in a field are Borel orbits of naive full level
  structures.
* `ModuliProblem.gammaNaiveToGammaZeroNaive_app_homEquiv_comp_repAction_hom`: the naive
  `[Γ₀(N)]`-structure of a point of the `[Γ(N)]` carrier is invariant under the Borel subgroup.
* `ModuliProblem.comp_gammaZeroNaiveCarrierπ_eq_of_gammaNaiveToGammaZeroNaive_app_eq`: points of
  the `[Γ(N)]` carrier with the same naive `[Γ₀(N)]`-structure have the same image in the naive
  `[Γ₀(N)]` carrier.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §3.7 and §7.1 (7.1.3).
* M. Demazure and A. Grothendieck, *SGA 3*, Exposé V, Théorème 4.1.
* D. Loeffler, *Modular curves*, lecture notes, Proposition 3.8.2.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace TauCeti

/-- Over a finite ring, the opposite group of the Borel subgroup of `GL₂`, which acts on the left
through the right action of `GL₂`, is finite. -/
instance {R : Type*} [CommRing R] [Finite R] : Finite (GL2Borel R)ᵐᵒᵖ :=
  Finite.of_equiv _ MulOpposite.opEquiv

namespace AlgebraicGeometry.ModuliProblem

variable {B : Scheme.{u}}

/-! ### The action on finite étale representing schemes -/

namespace RelRepData

variable {P : ModuliProblem B} (D : P.RelRepData) {G : Type*} [Monoid G] (ρ : G →* Aut P)

/-- The action of `G` on a finite étale representing scheme `𝒫_{E/S}`, as a functor from `G` to
finite étale `S`-schemes. -/
@[expose]
noncomputable def repActionFunctor (hD : D.HasProperty (@IsFinite ⊓ @Etale)) (X : EllObj B) :
    SingleObj G ⥤ FiniteEtaleScheme X.base :=
  (finiteEtaleSchemeProperty X.base).lift (SingleObj.functor (Aut.toEnd.comp (D.repAction ρ X)))
    fun _ ↦ (finiteEtaleSchemeProperty_iff _).mpr (D.hasProperty_iff.mp hD X)

/-- The finite étale scheme acted on by `repActionFunctor` is the representing scheme. -/
@[simp]
theorem repActionFunctor_obj_obj (hD : D.HasProperty (@IsFinite ⊓ @Etale)) (X : EllObj B) :
    ((D.repActionFunctor ρ hD X).obj (SingleObj.star G)).obj = D.rep X :=
  (rfl)

/-- An element `g` acts through `repActionFunctor` as the automorphism `repAction ρ X g`. -/
@[simp]
theorem repActionFunctor_map_hom (hD : D.HasProperty (@IsFinite ⊓ @Etale)) (X : EllObj B)
    (g : G) :
    ((D.repActionFunctor ρ hD X).map (X := SingleObj.star G) (Y := SingleObj.star G) g).hom =
      (D.repAction ρ X g).asIso.hom :=
  (rfl)

end RelRepData

/-! ### The Borel quotient of the naive `[Γ(N)]` carrier -/

variable {N : ℕ} [NeZero N] (hN : ∀ b : B, (N : B.residueField b) ≠ 0)

include hN in
/-- The naive `[Γ(N)]` carrier is finite étale where `N` is invertible on the base. -/
theorem hasProperty_isFinite_inf_etale_gammaNaiveRelRepData :
    (gammaNaiveRelRepData (B := B) (N := N)).HasProperty (@IsFinite ⊓ @Etale) :=
  (RelRepData.hasProperty_iff _).mpr fun X ↦
    ⟨(RelRepData.hasProperty_iff _).mp (hasProperty_isFinite_gammaNaiveRelRepData hN) X,
      (RelRepData.hasProperty_iff _).mp (hasProperty_etale_gammaNaiveRelRepData hN) X⟩

variable (B N) in
/-- The action of the Borel subgroup on the naive moduli problem `[Γ(N)]`, on the right of naive
full level structures, through `gammaNaiveAction`. -/
noncomputable def gammaNaiveBorelAction : (GL2Borel (ZMod N))ᵐᵒᵖ →* Aut (gammaNaive B N) :=
  (gammaNaiveAction B N).comp (MonoidHom.op (GL2Borel (ZMod N)).subtype)

omit [NeZero N] in
/-- An element of the Borel subgroup acts on `[Γ(N)]` as the corresponding matrix. -/
@[simp]
theorem gammaNaiveBorelAction_apply (g : (GL2Borel (ZMod N))ᵐᵒᵖ) :
    gammaNaiveBorelAction B N g = gammaNaiveAction B N (.op g.unop) :=
  (rfl)

/-- The Borel action on the naive `[Γ(N)]` carrier of an object `X = (E/S)`, where `N` is
invertible on `B`, as a functor to finite étale `S`-schemes. -/
noncomputable def gammaNaiveCarrierBorelAction (X : EllObj B) :
    SingleObj (GL2Borel (ZMod N))ᵐᵒᵖ ⥤ FiniteEtaleScheme X.base :=
  gammaNaiveRelRepData.repActionFunctor (gammaNaiveBorelAction B N)
    (hasProperty_isFinite_inf_etale_gammaNaiveRelRepData hN) X

/-- **The naive `[Γ₀(N)]` carrier** of an object `X = (E/S)` of `Ell/B`, where `N` is invertible
on `B` (Katz–Mazur, §7.1): the finite étale quotient of the naive `[Γ(N)]` carrier by the Borel
subgroup of `GL₂(ℤ/Nℤ)`. -/
noncomputable def gammaZeroNaiveCarrier (X : EllObj B) : FiniteEtaleScheme X.base :=
  FiniteEtaleScheme.quotient (gammaNaiveCarrierBorelAction hN X)

/-- The quotient map from the naive `[Γ(N)]` carrier to the naive `[Γ₀(N)]` carrier, over the base
of `X`. -/
noncomputable def gammaZeroNaiveCarrierπ (X : EllObj B) :
    (gammaNaiveRelRepData (N := N)).rep X ⟶ (gammaZeroNaiveCarrier hN X).obj :=
  (FiniteEtaleScheme.quotientπ (gammaNaiveCarrierBorelAction hN X)).hom

/-- The quotient map to the naive `[Γ₀(N)]` carrier is invariant under the Borel subgroup. -/
@[reassoc (attr := simp)]
theorem repAction_hom_gammaZeroNaiveCarrierπ (X : EllObj B)
    (g : (GL2Borel (ZMod N))ᵐᵒᵖ) :
    (gammaNaiveRelRepData.repAction (gammaNaiveBorelAction B N) X g).asIso.hom ≫
      gammaZeroNaiveCarrierπ hN X = gammaZeroNaiveCarrierπ hN X :=
  congrArg (·.hom) (FiniteEtaleScheme.map_quotientπ (gammaNaiveCarrierBorelAction hN X) g)

/-- The quotient map to the naive `[Γ₀(N)]` carrier is finite. -/
instance isFinite_gammaZeroNaiveCarrierπ_left (X : EllObj B) :
    IsFinite (gammaZeroNaiveCarrierπ hN X).left :=
  FiniteEtaleScheme.isFinite_hom_left (FiniteEtaleScheme.quotientπ _)

/-- The quotient map to the naive `[Γ₀(N)]` carrier is étale. -/
instance etale_gammaZeroNaiveCarrierπ_left (X : EllObj B) :
    Etale (gammaZeroNaiveCarrierπ hN X).left :=
  FiniteEtaleScheme.etale_hom_left (FiniteEtaleScheme.quotientπ _)

/-- The quotient map to the naive `[Γ₀(N)]` carrier is surjective. -/
instance surjective_gammaZeroNaiveCarrierπ_left (X : EllObj B) :
    Surjective (gammaZeroNaiveCarrierπ hN X).left := by
  have h₁ : Surjective (inv ((gammaNaiveCarrierBorelAction hN X).obj
    (SingleObj.star _)).obj.hom.relativeSpecFunctionsToScheme) := inferInstance
  have h₂ : Surjective (CommMon.invariantSubalgebraPresheaf (FiniteEtaleScheme.functionAlgebraAction
    (gammaNaiveCarrierBorelAction hN X))).relativeSpecπ := inferInstance
  exact (FiniteEtaleScheme.quotientπ_hom_left (gammaNaiveCarrierBorelAction hN X)).symm ▸
    ⟨h₂.surj.comp h₁.surj⟩

/-- The Borel subgroup acts on the naive `[Γ(N)]` carrier without fixed points with values in
nonempty schemes, since `GL₂(ℤ/Nℤ)` acts freely on naive full level structures over nonempty
bases. -/
theorem eq_one_of_comp_repAction_gammaNaiveBorelAction_hom_left_eq {X : EllObj B}
    {T : Scheme.{u}} [Nonempty T] {x : T ⟶ ((gammaNaiveRelRepData (N := N)).rep X).left}
    {g : (GL2Borel (ZMod N))ᵐᵒᵖ}
    (h : x ≫ (gammaNaiveRelRepData.repAction (gammaNaiveBorelAction B N) X g).asIso.hom.left =
      x) : g = 1 :=
  gammaNaiveRelRepData.eq_one_of_comp_repAction_hom_left_eq _
    (fun _ _ _ _ hα ↦ MulOpposite.unop_injective (Subtype.ext (MulOpposite.op_injective
      (eq_one_of_gammaNaiveAction_hom_app_eq_self hα)))) h

/-- **The naive `[Γ(N)]` carrier is a Borel torsor over the naive `[Γ₀(N)]` carrier**
(Katz–Mazur, 7.1.3). For the naive `[Γ(N)]` carrier `Y` of `X = (E/S)`, where `N` is invertible on
`B`, the fibre product `Y ×_{Y/Borel} Y` is the disjoint union of copies of `Y` indexed by the
Borel subgroup, the copy of `g` mapping to `(y, y g)`. -/
theorem isPullback_gammaZeroNaiveCarrierπ (X : EllObj B) :
    IsPullback (Sigma.desc fun _ : (GL2Borel (ZMod N))ᵐᵒᵖ ↦
        𝟙 ((gammaNaiveRelRepData (N := N)).rep X).left)
      (Sigma.desc fun g : (GL2Borel (ZMod N))ᵐᵒᵖ ↦
        (gammaNaiveRelRepData.repAction (gammaNaiveBorelAction B N) X g).asIso.hom.left)
      (gammaZeroNaiveCarrierπ hN X).left (gammaZeroNaiveCarrierπ hN X).left :=
  FiniteEtaleScheme.isPullback_quotientπ_of_free (gammaNaiveCarrierBorelAction hN X)
    fun _ _ _ _ h ↦ eq_one_of_comp_repAction_gammaNaiveBorelAction_hom_left_eq h

/-- **Points of the naive `[Γ₀(N)]` carrier are Borel orbits.** Two naive full level structures
on the base change of `E` to the spectrum of a field, with the same image in the naive `[Γ₀(N)]`
carrier, differ by an element of the Borel subgroup. -/
theorem exists_gammaNaiveAction_hom_app_eq_of_comp_gammaZeroNaiveCarrierπ_eq (X : EllObj B)
    {K : Type u} [Field K] {t : Spec (CommRingCat.of K) ⟶ X.base}
    {x₁ x₂ : Over.mk t ⟶ (gammaNaiveRelRepData (N := N)).rep X}
    (h : x₁ ≫ gammaZeroNaiveCarrierπ hN X = x₂ ≫ gammaZeroNaiveCarrierπ hN X) :
    ∃ g ∈ GL2Borel (ZMod N),
      (gammaNaiveAction B N (.op g)).asIso.hom.app (op (X.baseChangeFunctor.obj (Over.mk t)))
        ((gammaNaiveRelRepData.representableBy X).homEquiv x₁) =
          (gammaNaiveRelRepData.representableBy X).homEquiv x₂ := by
  obtain ⟨g, hg⟩ := FiniteEtaleScheme.exists_comp_map_eq_of_comp_quotientπ_eq
    (gammaNaiveCarrierBorelAction hN X) (x₁ := x₁.left) (x₂ := x₂.left) congr(($h).left)
  refine ⟨g.unop, g.unop.2, ?_⟩
  have hx : x₁ ≫ (gammaNaiveRelRepData.repAction (gammaNaiveBorelAction B N) X g).asIso.hom =
      x₂ := Over.OverMorphism.ext hg
  rw [← hx, RelRepData.homEquiv_comp_repAction_hom, gammaNaiveBorelAction_apply]

/-- **The naive `[Γ₀(N)]`-structure of a point of the `[Γ(N)]` carrier is Borel invariant.** For a
point `f` of the naive `[Γ(N)]` carrier with values in `T`, classifying a naive full level
structure `(P, Q)` on `E_T`, and an element `g` of the Borel subgroup, the points `f` and `f g`
give the same naive cyclic subgroup `⟨P⟩` of `E_T`. -/
theorem gammaNaiveToGammaZeroNaive_app_homEquiv_comp_repAction_hom (X : EllObj B)
    (g : (GL2Borel (ZMod N))ᵐᵒᵖ) {T : Over X.base} (f : T ⟶ (gammaNaiveRelRepData (N := N)).rep X) :
    (gammaNaiveToGammaZeroNaive B N hN).app _ ((gammaNaiveRelRepData.representableBy X).homEquiv
      (f ≫ (gammaNaiveRelRepData.repAction (gammaNaiveBorelAction B N) X g).asIso.hom)) =
        (gammaNaiveToGammaZeroNaive B N hN).app _
          ((gammaNaiveRelRepData.representableBy X).homEquiv f) := by
  rw [RelRepData.homEquiv_comp_repAction_hom, gammaNaiveBorelAction_apply]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (gammaNaiveAction_hom_comp_gammaNaiveToGammaZeroNaive hN (GL2Borel.apply_one_zero g.unop)) _) _

/-- **Bases generating the same naive cyclic subgroup have the same image in the naive
`[Γ₀(N)]` carrier.** For points `x₁` and `x₂` of the naive `[Γ(N)]` carrier with values in `T`,
classifying naive full level structures `(P₁, Q₁)` and `(P₂, Q₂)` on `E_T` with `⟨P₁⟩ = ⟨P₂⟩`,
the composites `T ⟶ Y ⟶ Y/Borel` agree. Over every geometric point of `T` the two bases differ by
a Borel matrix (`EllipticCurveGeom.IsFiberwiseInjective.exists_mem_GL2Borel_eq_comp`), so the
composites agree there; the carrier is separated and unramified over `S`, so morphisms into it
that agree on the geometric points, which jointly form a surjection onto `T`, agree. -/
theorem comp_gammaZeroNaiveCarrierπ_eq_of_gammaNaiveToGammaZeroNaive_app_eq (X : EllObj B)
    {T : Over X.base} {x₁ x₂ : T ⟶ (gammaNaiveRelRepData (N := N)).rep X}
    (h : (gammaNaiveToGammaZeroNaive B N hN).app _
        ((gammaNaiveRelRepData.representableBy X).homEquiv x₁) =
      (gammaNaiveToGammaZeroNaive B N hN).app _
        ((gammaNaiveRelRepData.representableBy X).homEquiv x₂)) :
    x₁ ≫ gammaZeroNaiveCarrierπ hN X = x₂ ≫ gammaZeroNaiveCarrierπ hN X := by
  let R := (gammaNaiveRelRepData (B := B) (N := N)).representableBy X
  -- Over the geometric point of `T` at `t`, the two bases differ by a Borel matrix.
  have hgeom (t : T.left) :
      T.left.fromSpecAlgebraicClosure t ≫ (x₁ ≫ gammaZeroNaiveCarrierπ hN X).left =
        T.left.fromSpecAlgebraicClosure t ≫ (x₂ ≫ gammaZeroNaiveCarrierπ hN X).left := by
    let L := AlgebraicClosure (T.left.residueField t)
    let T' := Over.mk (T.left.fromSpecAlgebraicClosure t ≫ T.hom)
    let t' : T' ⟶ T := Over.homMk (T.left.fromSpecAlgebraicClosure t)
    have hNL : (N : L) ≠ 0 := ((T.hom ≫ X.structureMap).natCast_residueField_ne_zero
      (x := t) (hN _)).isUnit.natCast_ne_zero_of_algebra
    obtain ⟨α₁, hα₁⟩ : ∃ α : (gammaNaive B N).obj (op (X.baseChangeFunctor.obj T')),
        R.homEquiv (t' ≫ x₁) = α := ⟨_, rfl⟩
    obtain ⟨α₂, hα₂⟩ : ∃ α : (gammaNaive B N).obj (op (X.baseChangeFunctor.obj T')),
        R.homEquiv (t' ≫ x₂) = α := ⟨_, rfl⟩
    have hα : (gammaNaiveToGammaZeroNaive B N hN).app _ α₁ =
        (gammaNaiveToGammaZeroNaive B N hN).app _ α₂ := by
      rw [← hα₁, ← hα₂, R.homEquiv_comp, R.homEquiv_comp]
      exact (NatTrans.naturality_apply _ _ _).trans
        ((congrArg _ h).trans (NatTrans.naturality_apply _ _ _).symm)
    have hdiv := congrArg (fun a ↦ (gammaZeroNaiveEquiv _ a).1) hα
    simp only [gammaZeroNaiveEquiv_gammaNaiveToGammaZeroNaive_app] at hdiv
    obtain ⟨g, hgB, hg⟩ :=
      (naiveLevelEquiv _ α₁).2.exists_mem_GL2Borel_eq_comp hNL (naiveLevelEquiv _ α₂).2 hdiv
    have hx : (t' ≫ x₁) ≫ (gammaNaiveRelRepData.repAction (gammaNaiveBorelAction B N) X
        (.op ⟨g, hgB⟩)).asIso.hom = t' ≫ x₂ := R.homEquiv.injective <| by
      rw [RelRepData.homEquiv_comp_repAction_hom, hα₁, hα₂, gammaNaiveBorelAction_apply]
      refine (naiveLevelEquiv _).injective (Subtype.ext ?_)
      rw [naiveLevelEquiv_gammaNaiveAction_hom_app]
      exact hg.symm
    have := congrArg (fun z ↦ (z ≫ gammaZeroNaiveCarrierπ hN X).left) hx
    simpa [t'] using this
  -- Morphisms into the separated unramified carrier agreeing at all geometric points agree.
  have : Surjective (Sigma.desc fun t : T.left ↦ T.left.fromSpecAlgebraicClosure t) := by
    refine ⟨fun t ↦ ?_⟩
    obtain ⟨p⟩ : Nonempty (Spec (.of (AlgebraicClosure (T.left.residueField t)))) :=
      inferInstance
    refine ⟨(Sigma.ι (fun t : T.left ↦ Spec (.of (AlgebraicClosure (T.left.residueField t)))) t) p,
      ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
    exact Scheme.fromSpecAlgebraicClosure_apply _ _ _
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated_of_formallyUnramified
    (gammaZeroNaiveCarrier hN X).obj.hom ?_
    (Sigma.desc fun t : T.left ↦ T.left.fromSpecAlgebraicClosure t) ?_)
  · rw [Over.w, Over.w]
  · exact Sigma.hom_ext _ _ fun t ↦ by simpa only [Sigma.ι_comp_desc_assoc] using hgeom t

end AlgebraicGeometry.ModuliProblem

end TauCeti
