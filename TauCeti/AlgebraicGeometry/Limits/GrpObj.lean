/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Limits.Descent
public import TauCeti.AlgebraicGeometry.Morphisms.QuasiCompact.Over
public import TauCeti.CategoryTheory.Filtered.Basic
public import TauCeti.CategoryTheory.Monoidal.Grp.Over

/-!
# Spreading out group schemes along cofiltered limits

Let `S = lim Dⱼ` be the limit of a cofiltered diagram of quasi-compact quasi-separated schemes with
affine transition maps. A scheme `X` of finite presentation over `S` is the base change of a scheme
of finite presentation over some member `Dᵢ`
(`CategoryTheory.Limits.IsLimit.exists_isPullback_of_finitePresentation`, Stacks 01ZM). This file
shows that a group law spreads out along with the scheme: a group scheme of finite presentation over
`S` is the base change of a group scheme of finite presentation over some member of the diagram, by
an isomorphism of group schemes.

Group schemes over a base are group objects in the cartesian monoidal category of schemes over it,
and base change is the monoidal functor `Over.pullback`. The unit, the multiplication and the
inverse of a group law over `S` descend to morphisms over some member `Dⱼ`
(`CategoryTheory.Limits.IsLimit.exists_liftsAlong`), and each group axiom, an
equality of morphisms over `Dⱼ` which holds over `S`, holds over some later member `Dₖ`
(`CategoryTheory.Limits.IsLimit.exists_overPullback_map_eq_map`). Over `Dₖ` the base changes of the
descended morphisms are then a group law (`CategoryTheory.Functor.grpObjObjOfMap`) whose base
change to `S` is the given one.

## Main results

* `CategoryTheory.Limits.IsLimit.exists_grpObj_overPullback`: a group law on the base change to
  `S` of a finitely presented scheme `X` over `Dᵢ` is, after replacing `Dᵢ` by some `Dⱼ`, the base
  change of a group law on the base change of `X` to `Dⱼ`.
* `CategoryTheory.Limits.IsLimit.exists_grpObj_pullback_iso`: **spreading out group schemes**. A
  group scheme of finite presentation over `S` is isomorphic, as a group scheme, to the base change
  of a group scheme of finite presentation over some `Dⱼ`.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Troisième partie, §8.8.
* The Stacks Project, [Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM) and
  [Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC).
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj CartesianMonoidalCategory
  Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped Obj

namespace CategoryTheory.Limits.IsLimit

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}

section GrpObj

variable [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] (hc : IsLimit c)
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- The unit, the multiplication and the inverse of a group law on the base change of `X` to the
cone point lift to candidate structure morphisms on the base change of `X` to some member of the
diagram. -/
private theorem exists_lifts {i : I} (X : Over (D.obj i)) [LocallyOfFinitePresentation X.hom]
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [GrpObj ((Over.pullback (c.π.app i)).obj X)] :
    ∃ (j : I) (g : j ⟶ i) (one : 𝟙_ _ ⟶ (Over.pullback (D.map g)).obj X)
      (mul : (Over.pullback (D.map g)).obj X ⊗ (Over.pullback (D.map g)).obj X ⟶
        (Over.pullback (D.map g)).obj X)
      (inv : (Over.pullback (D.map g)).obj X ⟶ (Over.pullback (D.map g)).obj X),
      (Over.pullback (c.π.app j)).map one ≫ (Over.pullbackCompIsoOfEq (c.w g)).hom.app X =
          toUnit _ ≫ η[(Over.pullback (c.π.app i)).obj X] ∧
        (Over.pullback (c.π.app j)).map mul ≫ (Over.pullbackCompIsoOfEq (c.w g)).hom.app X =
          δ (Over.pullback (c.π.app j)) ((Over.pullback (D.map g)).obj X)
            ((Over.pullback (D.map g)).obj X) ≫
            ((Over.pullbackCompIsoOfEq (c.w g)).hom.app X ⊗ₘ
              (Over.pullbackCompIsoOfEq (c.w g)).hom.app X) ≫
              μ[(Over.pullback (c.π.app i)).obj X] ∧
        (Over.pullback (c.π.app j)).map inv ≫ (Over.pullbackCompIsoOfEq (c.w g)).hom.app X =
          (Over.pullbackCompIsoOfEq (c.w g)).hom.app X ≫
            ι[(Over.pullback (c.π.app i)).obj X] := by
  -- Lift the three structure morphisms, each along some morphism to `i`, then along a common one.
  let R : Fin 3 → ∀ {k : I}, (k ⟶ i) → Prop := ![
    c.LiftsAlong (Functor.OplaxMonoidal.η (Over.pullback (c.π.app i)) ≫
      η[(Over.pullback (c.π.app i)).obj X]),
    c.LiftsAlong (δ (Over.pullback (c.π.app i)) X X ≫ μ[(Over.pullback (c.π.app i)).obj X]),
    c.LiftsAlong ι[(Over.pullback (c.π.app i)).obj X]]
  obtain ⟨j, g, hg⟩ := IsCofiltered.exists_forall_of_stable (R := R)
    (by intro n; fin_cases n <;> exact fun h hg ↦ hg.precomp h)
    (by intro n; fin_cases n <;> exact hc.exists_liftsAlong _)
  obtain ⟨vo, hvo⟩ := (Cone.liftsAlong_iff _ _).mp (hg 0)
  obtain ⟨vm, hvm⟩ := (Cone.liftsAlong_iff _ _).mp (hg 1)
  obtain ⟨vi, hvi⟩ := (Cone.liftsAlong_iff _ _).mp (hg 2)
  refine ⟨j, g, ε _ ≫ vo, Functor.LaxMonoidal.μ _ X X ≫ vm, vi, ?_, ?_, hvi⟩
  · rw [Functor.map_comp, Category.assoc, hvo, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ η[(Over.pullback (c.π.app i)).obj X]) (toUnit_unique _ _)
  · rw [Functor.map_comp, Category.assoc, hvm]
    have ht := NatTrans.IsMonoidal.tensor
      (τ := (Over.pullbackCompIsoOfEq (c.w g)).hom) X X
    dsimp only [Functor.LaxMonoidal.comp_μ] at ht
    rw [← cancel_epi (Functor.LaxMonoidal.μ (Over.pullback (c.π.app j))
      ((Over.pullback (D.map g)).obj X) ((Over.pullback (D.map g)).obj X))]
    simpa only [Category.assoc, Functor.Monoidal.μ_δ_assoc] using
      congrArg (· ≫ δ (Over.pullback (c.π.app i)) X X ≫
        μ[(Over.pullback (c.π.app i)).obj X]) ht

include hc in
/-- **Spreading out a group law.** Let `S = lim Dⱼ` be a cofiltered limit of quasi-compact
quasi-separated schemes with affine transition maps, and let `X` be a scheme of finite presentation,
quasi-compact and quasi-separated over a member `Dᵢ`. A group law on the base change `X ×_{Dᵢ} S`
over `S` is the base change of a group law on `X ×_{Dᵢ} Dⱼ` over some `Dⱼ`: the identification
`(X ×_{Dᵢ} Dⱼ) ×_{Dⱼ} S ≅ X ×_{Dᵢ} S` is an isomorphism of group schemes. -/
theorem exists_grpObj_overPullback {i : I} (X : Over (D.obj i))
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom] [QuasiSeparated X.hom]
    [GrpObj ((Over.pullback (c.π.app i)).obj X)] :
    ∃ (j : I) (f : j ⟶ i) (_ : GrpObj ((Over.pullback (D.map f)).obj X)),
      IsMonHom (M := (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map f)).obj X))
        ((Over.pullbackCompIsoOfEq (c.w f)).hom.app X) := by
  obtain ⟨j, g, one, mul, inv, h_one, h_mul, h_inv⟩ := hc.exists_lifts X
  -- The given group law, transported to the base change to the cone point of `X ×_{Dᵢ} Dⱼ`.
  let T : GrpObj ((Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X)) :=
    .ofIso ((Over.pullbackCompIsoOfEq (c.w g)).app X).symm
  -- The transported law, restated on the source of the comparison isomorphism.
  let T' : GrpObj ((Over.pullback (D.map g) ⋙ Over.pullback (c.π.app j)).obj X) := T
  -- The comparison is a homomorphism for the transported law; cancel it in each lift equation.
  have : IsMonHom (M := (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X))
      ((Over.pullbackCompIsoOfEq (c.w g)).hom.app X) :=
    inferInstanceAs (IsMonHom ((Over.pullbackCompIsoOfEq (c.w g)).app X).symm.inv)
  have h_one' : (Over.pullback (c.π.app j)).map one = Functor.OplaxMonoidal.η _ ≫
      η[(Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X)] := by
    rw [← cancel_mono ((Over.pullbackCompIsoOfEq (c.w g)).hom.app X), h_one, Category.assoc,
      IsMonHom.one_hom, toUnit_unique (toUnit _) (Functor.OplaxMonoidal.η _)]
  have h_mul' : (Over.pullback (c.π.app j)).map mul =
      δ _ _ _ ≫ μ[(Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X)] := by
    rw [← cancel_mono ((Over.pullbackCompIsoOfEq (c.w g)).hom.app X), h_mul, Category.assoc,
      IsMonHom.mul_hom]
  have h_inv' : (Over.pullback (c.π.app j)).map inv =
      ι[(Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X)] := by
    rw [← cancel_mono ((Over.pullbackCompIsoOfEq (c.w g)).hom.app X), h_inv, GrpObj.inv_hom]
  have : QuasiCompact ((Over.pullback (D.map g)).obj X).hom := by
    simpa only [Over.pullback_obj_hom] using
      (inferInstanceAs (QuasiCompact (pullback.snd X.hom (D.map g))))
  have : LocallyOfFiniteType ((Over.pullback (D.map g)).obj X).hom := by
    simpa only [Over.pullback_obj_hom] using
      (inferInstanceAs (LocallyOfFiniteType (pullback.snd X.hom (D.map g))))
  let P := TauCeti.groupLawAxiomPairs ((Over.pullback (D.map g)).obj X) one mul inv
  have (n : Fin 5) : QuasiCompact (P n).1.hom := by
    fin_cases n <;> dsimp [P, TauCeti.groupLawAxiomPairs] <;> infer_instance
  have hP : ∀ n, (Over.pullback (c.π.app j)).map (P n).2.1 =
      (Over.pullback (c.π.app j)).map (P n).2.2 := by
    intro n
    fin_cases n
    · exact (Over.pullback (c.π.app j)).map_one_mul h_one' h_mul'
    · exact (Over.pullback (c.π.app j)).map_mul_one h_one' h_mul'
    · exact (Over.pullback (c.π.app j)).map_mul_assoc h_mul'
    · exact (Over.pullback (c.π.app j)).map_left_inv
        (X := (Over.pullback (D.map g)).obj X) h_one' h_mul' h_inv'
    · exact (Over.pullback (c.π.app j)).map_right_inv
        (X := (Over.pullback (D.map g)).obj X) h_one' h_mul' h_inv'
  obtain ⟨k, h, hh⟩ := hc.exists_overPullback_map_eq_map_family
    ((Over.pullback (D.map g)).obj X) P hP
  exact ⟨k, h ≫ g, c.exists_grpObj_of_map_axioms X g h one mul inv
    (by rw [h_one', Functor.Monoidal.ε_η_assoc]) (by rw [h_mul', Functor.Monoidal.μ_δ_assoc]) hh⟩

include hc in
/-- **Spreading out group schemes.** Let `S = lim Dⱼ` be a cofiltered limit of quasi-compact
quasi-separated schemes with affine transition maps. A group scheme `G` over `S` which is of finite
presentation, quasi-compact and quasi-separated over `S` is isomorphic, as a group scheme over `S`,
to the base change of a group scheme of finite presentation, quasi-compact and quasi-separated over
some member `Dⱼ`. -/
theorem exists_grpObj_pullback_iso (G : Over c.pt) [GrpObj G]
    [LocallyOfFinitePresentation G.hom] [QuasiCompact G.hom] [QuasiSeparated G.hom] :
    ∃ (j : I) (Y : Over (D.obj j)) (_ : GrpObj Y) (e : (Over.pullback (c.π.app j)).obj Y ≅ G),
      LocallyOfFinitePresentation Y.hom ∧ QuasiCompact Y.hom ∧ QuasiSeparated Y.hom ∧
        IsMonHom e.hom := by
  obtain ⟨i, X, p, _, _, _, a, sq⟩ :=
    hc.exists_isPullback_of_finitePresentation (IsCofiltered.nonempty (C := I)).some G.hom
  let e₀ : (Over.pullback (c.π.app i)).obj (Over.mk p) ≅ G :=
    Over.isoMk sq.isoPullback.symm (by simp)
  let : GrpObj ((Over.pullback (c.π.app i)).obj (Over.mk p)) := .ofIso e₀.symm
  have : IsMonHom e₀.hom := inferInstanceAs (IsMonHom e₀.symm.inv)
  have : LocallyOfFinitePresentation (Over.mk p).hom := by
    simpa only [Over.mk_hom] using ‹LocallyOfFinitePresentation p›
  have : QuasiCompact (Over.mk p).hom := by
    simpa only [Over.mk_hom] using ‹QuasiCompact p›
  have : QuasiSeparated (Over.mk p).hom := by
    simpa only [Over.mk_hom] using ‹QuasiSeparated p›
  obtain ⟨j, f, _, hf⟩ := hc.exists_grpObj_overPullback (Over.mk p)
  have : IsMonHom (M := (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map f)).obj (Over.mk p)))
      ((Over.pullbackCompIsoOfEq (c.w f)).app (Over.mk p)).hom := hf
  exact ⟨j, (Over.pullback (D.map f)).obj (Over.mk p), inferInstance,
    (Over.pullbackCompIsoOfEq (c.w f)).app (Over.mk p) ≪≫ e₀,
    (by simpa only [Over.pullback_obj_hom, Over.mk_hom] using
      (inferInstanceAs (LocallyOfFinitePresentation (pullback.snd p (D.map f))))),
    (by simpa only [Over.pullback_obj_hom, Over.mk_hom] using
      (inferInstanceAs (QuasiCompact (pullback.snd p (D.map f))))),
    (by simpa only [Over.pullback_obj_hom, Over.mk_hom] using
      (inferInstanceAs (QuasiSeparated (pullback.snd p (D.map f))))),
    inferInstanceAs (IsMonHom (M := (Over.pullback (c.π.app j)).obj
      ((Over.pullback (D.map f)).obj (Over.mk p))) (_ ≫ e₀.hom))⟩

end GrpObj

end CategoryTheory.Limits.IsLimit
