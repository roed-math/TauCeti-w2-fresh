/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import TauCeti.Algebra.Category.Ring.FinitePresentation

/-!
# Descent of finitely presented affine schemes along cofiltered limits

Let `S = lim Sᵢ` be a cofiltered limit of affine schemes. Then `S` is affine with
`Γ(S) = colim Γ(Sᵢ)`, so a finitely presented `Γ(S)`-algebra is the base change of a finitely
presented `Γ(Sᵢ)`-algebra for some `i` (Stacks, Lemma 10.127.6 (00QO)). Geometrically: every
affine scheme of finite presentation over `S` is the base change of an affine scheme of finite
presentation over some `Sᵢ`. This is the affine case of the descent of schemes of finite
presentation (Stacks, Lemma 32.10.1 (01ZM)).

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.exists_isPullback_of_isLimit_of_isAffine`: an affine scheme
  of finite presentation over a cofiltered limit of affine schemes is the base change of an affine
  scheme of finite presentation over some member.
* `TauCeti.AlgebraicGeometry.Scheme.exists_isPullback_of_isLimit_of_isAffineOpen`: the same over
  the preimages of an affine open of a member, for a diagram with affine transition maps.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  (hc : IsLimit c)

include hc in
/-- Let `S = lim Sᵢ` be a cofiltered limit of affine schemes. Every affine scheme `X` of finite
presentation over `S` is the base change `Y ×_{Sᵢ} S` of an affine scheme `Y` of finite
presentation over some member `Sᵢ`. Stacks, Lemma 32.10.1 (01ZM), affine case. -/
theorem exists_isPullback_of_isLimit_of_isAffine [∀ i, IsAffine (D.obj i)] {X : Scheme.{u}}
    [IsAffine X] (f : X ⟶ c.pt) [LocallyOfFinitePresentation f] :
    ∃ (i : I) (Y : Scheme.{u}) (q : Y ⟶ D.obj i) (a : X ⟶ Y), IsAffine Y ∧
      LocallyOfFinitePresentation q ∧ IsPullback a f q (c.π.app i) := by
  have := Scheme.isAffine_of_isLimit c hc
  obtain ⟨hΓ⟩ := nonempty_isColimit_Γ_mapCocone D c hc
  obtain ⟨⟨i⟩, B₀, g, h, hg, H⟩ := TauCeti.CommRingCat.exists_isPushout_of_isColimit hΓ f.appTop
    (HasRingHomProperty.appTop @LocallyOfFinitePresentation f ‹_›)
  refine ⟨i, Spec B₀, (Spec.map g : Spec B₀ ⟶ Spec Γ(D.obj i, ⊤)) ≫ (D.obj i).isoSpec.inv,
    X.isoSpec.hom ≫ Spec.map h, inferInstance, ?_, ?_⟩
  · have : LocallyOfFinitePresentation (Spec.map g : Spec B₀ ⟶ Spec Γ(D.obj i, ⊤)) :=
      (LocallyOfFinitePresentation.SpecMap_iff g).mpr hg
    infer_instance
  refine (isPullback_SpecMap_of_isPushout _ _ _ _ H).of_iso X.isoSpec.symm (Iso.refl _)
    c.pt.isoSpec.symm (D.obj i).isoSpec.symm ?_ ?_ ?_ ?_
  · simp
  · exact Scheme.isoSpec_inv_naturality f
  · simp
  · exact Scheme.isoSpec_inv_naturality (X := c.pt) (c.π.app i)

include hc in
/-- Let `S = lim Dⱼ` be a cofiltered limit of schemes with affine transition maps, and let
`U ⊆ Dᵢ` be an affine open. Every affine scheme `X` of finite presentation over the preimage of
`U` in `S` is the base change of an affine scheme of finite presentation over the preimage of `U`
in some `Dⱼ`. Stacks, Lemma 32.10.1 (01ZM), affine-local case. -/
theorem exists_isPullback_of_isLimit_of_isAffineOpen [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i : I} {U : (D.obj i).Opens} (hU : IsAffineOpen U) {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ c.π.app i ⁻¹ᵁ U) [LocallyOfFinitePresentation f] :
    ∃ (j : I) (hji : j ⟶ i) (Y : Scheme.{u}) (q : Y ⟶ D.map hji ⁻¹ᵁ U) (a : X ⟶ Y), IsAffine Y ∧
      LocallyOfFinitePresentation q ∧
        IsPullback a f q ((c.π.app j).resLE _ _ (by rw [← Scheme.Hom.comp_preimage, c.w])) := by
  have (j : Over i) : IsAffine ((opensDiagram D i U).obj j) := hU.preimage _
  let f' : X ⟶ (opensCone D c i U).pt := f
  have : LocallyOfFinitePresentation f' := ‹_›
  obtain ⟨j, Y, q, a, hY, hq, H⟩ :=
    exists_isPullback_of_isLimit_of_isAffine (isLimitOpensCone D c hc i U) f'
  exact ⟨j.left, j.hom, Y, q, a, hY, hq, H⟩

end TauCeti.AlgebraicGeometry.Scheme
