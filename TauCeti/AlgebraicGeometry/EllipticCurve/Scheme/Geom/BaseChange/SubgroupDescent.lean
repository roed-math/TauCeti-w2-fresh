/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Points
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveCyclicSubgroup
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.Finiteness.Descent
import TauCeti.AlgebraicGeometry.Descent.MorphismProperty
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Descent
import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Criterion
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.FlatLocality

/-!
# Closed subgroup schemes and naive cyclic subgroups descend along fppf base change

Let `g : E' ⟶ E` be the base change of an elliptic curve `E/S` along a flat surjective morphism
`f : S' ⟶ S`, locally of finite presentation (for instance an étale surjection). A closed
subscheme of `E` whose inverse image along `g` is a subgroup scheme of `E'` is a subgroup scheme
of `E` (`EllipticCurveGeom.exists_grpObj_isMonHom_of_comap`). This is the converse of
`EllipticCurveGeom.exists_grpObj_isMonHom_comap`.

By the closed-subgroup criterion (`TauCeti.GroupScheme.exists_grpObj_isMonHom_iff_ker_le`), being a
subgroup scheme says that the zero section, the negation and the sum of two points of the closed
subscheme factor through it. Each of these morphisms `h : Z ⟶ E` is covered by the corresponding
morphism `h' : Z' ⟶ E'` for the subgroup scheme of `E'`, along an fppf covering `Z' ⟶ Z`, and
factorization through a closed subscheme descends along effective epimorphisms
(`AlgebraicGeometry.Scheme.IdealSheafData.le_ker_of_comap_le_ker`).

For `f` a quasi-compact étale surjection, for instance a finite étale surjection, the remaining
conditions on a naive cyclic subgroup descend too
(`EllipticCurveGeom.IsNaiveCyclicSubgroup.of_comap`): finiteness, flatness and finite
presentation satisfy fpqc descent, the rank is read off on the fibres of `f`, and the étale-local
generator of the inverse image is an étale-local generator over `S` after composing with `f`. This
is the input used to descend a naive `[Γ₀(N)]`-structure along the finite étale cover of the naive
`[Γ₀(N)]` carrier by the naive `[Γ(N)]` carrier. Containment of closed subschemes descends in
the same way, so a naive cyclic subgroup of order `N`, étale-locally the divisor of the multiples
of a point killed by `N`, lies in `E[N]`
(`EllipticCurveGeom.IsNaiveCyclicSubgroup.ker_torsionι_le`).

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_grpObj_isMonHom_of_comap`: closed subgroup
  schemes of elliptic curves descend along fppf base change.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsNaiveCyclicSubgroup.of_comap`: naive cyclic
  subgroups descend along quasi-compact étale surjective base change.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsNaiveCyclicSubgroup.ker_torsionι_le`: a naive
  cyclic subgroup of order `N` lies in `E[N]`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §3.7.
* The Stacks Project, Section 35.23 (properties of morphisms local in the fpqc topology).
-/
public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S S' : Scheme.{u}} {E : EllipticCurveGeom S} {E' : EllipticCurveGeom S'}
  {g : E'.carrier ⟶ E.carrier} {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f)
  (h0 : E'.zero ≫ g = f ≫ E.zero)

include hg h0 in
/-- **Closed subgroup schemes descend along fppf base change.** Let `g : E' ⟶ E` be a morphism of
elliptic curves lying over a flat surjective morphism `f : S' ⟶ S`, locally of finite
presentation, forming a pullback square with the structure morphisms and carrying the zero section
of `E'` to that of `E`. If the inverse image along `g` of the closed subscheme of `E` cut out by
`D` is a subgroup scheme of `E'`, then that closed subscheme is a subgroup scheme of `E`. -/
theorem exists_grpObj_isMonHom_of_comap [Flat f] [Surjective f] [LocallyOfFinitePresentation f]
    (D : E.carrier.IdealSheafData)
    (hD : ∃ _ : GrpObj (Over.mk ((D.comap g).subschemeι ≫ E'.structureMap)),
      IsMonHom (Over.homMk (D.comap g).subschemeι :
        Over.mk ((D.comap g).subschemeι ≫ E'.structureMap) ⟶ Over.mk E'.structureMap)) :
    ∃ _ : GrpObj (Over.mk (D.subschemeι ≫ E.structureMap)),
      IsMonHom (Over.homMk D.subschemeι :
        Over.mk (D.subschemeι ≫ E.structureMap) ⟶ Over.mk E.structureMap) := by
  let A := Over.mk (D.subschemeι ≫ E.structureMap)
  let A' := Over.mk ((D.comap g).subschemeι ≫ E'.structureMap)
  let i : A ⟶ Over.mk E.structureMap := Over.homMk D.subschemeι
  let i' : A' ⟶ Over.mk E'.structureMap := Over.homMk (D.comap g).subschemeι
  have : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion D.subschemeι)
  have : IsClosedImmersion i'.left := inferInstanceAs (IsClosedImmersion (D.comap g).subschemeι)
  have hi : i.left.ker = D := Scheme.IdealSheafData.ker_subschemeι _
  have hi' : i'.left.ker = D.comap g := Scheme.IdealSheafData.ker_subschemeι _
  rw [GroupScheme.exists_grpObj_isMonHom_iff_ker_le i', hi'] at hD
  rw [GroupScheme.exists_grpObj_isMonHom_iff_ker_le i, hi]
  obtain ⟨he, hm, hj⟩ := hD
  -- The closed subscheme of `D.comap g` is the base change of that of `D` along `f`.
  let ρ := Scheme.IdealSheafData.subschemeMap (D.comap g) D g (D.le_map_comap g)
  have hρ : ρ ≫ D.subschemeι = (D.comap g).subschemeι ≫ g :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  have hsub : IsPullback ρ A'.hom A.hom f := D.isPullback_subschemeMap_comap _ hg
  refine ⟨?_, ?_, ?_⟩
  · -- The zero section is covered by the zero section of `E'`, along `f`.
    refine D.le_ker_of_comap_le_ker (g := g) f (h' := E'.zero) ?_ ?_
    · rw [one_left, h0]
    · simpa only [one_left] using he
  · -- A sum of two points of the closed subscheme is covered by the sum of their base changes,
    -- along the base change of `f` to the product of two copies of the closed subscheme.
    let Z := A ⊗ A
    let q := pullback.fst Z.hom f
    let W : Over S' := Over.mk (pullback.snd Z.hom f)
    let x' : W ⟶ A' := Over.homMk (hsub.lift (q ≫ (fst A A).left) (pullback.snd Z.hom f)
      (by simp only [Category.assoc, Over.w, q, Z, pullback.condition])) (hsub.lift_snd _ _ _)
    let y' : W ⟶ A' := Over.homMk (hsub.lift (q ≫ (snd A A).left) (pullback.snd Z.hom f)
      (by simp only [Category.assoc, Over.w, q, Z, pullback.condition])) (hsub.lift_snd _ _ _)
    let Zq : Over S := Over.mk (q ≫ Z.hom)
    let r : Zq ⟶ Z := Over.homMk q
    have hx : (x' ≫ i').left ≫ g = (r ≫ fst A A ≫ i).left := by
      simp only [Over.comp_left, Over.homMk_left, x', i', i, r, Category.assoc, ← hρ,
        hsub.lift_fst_assoc]
    have hy : (y' ≫ i').left ≫ g = (r ≫ snd A A ≫ i).left := by
      simp only [Over.comp_left, Over.homMk_left, y', i', i, r, Category.assoc, ← hρ,
        hsub.lift_fst_assoc]
    refine D.le_ker_of_comap_le_ker (g := g) q
      (h' := (lift x' y').left ≫ ((i' ⊗ₘ i') ≫ μ[Over.mk E'.structureMap]).left) ?_ ?_
    · have key := mul_left_comp_eq_of_isPullback hg h0 (Z := W) (f' := q ≫ Z.hom)
        pullback.condition.symm hx hy
      simp only [← Over.comp_left, mul_eq_mul, comp_mul, lift_fst_assoc, lift_snd_assoc,
        tensorHom_fst, tensorHom_snd] at key ⊢
      rw [key, ← comp_mul]
      rfl
    · exact hm.trans (Scheme.Hom.le_ker_comp _ _)
  · -- The negation of a point of the closed subscheme is covered by the negation of its base
    -- change, along the base change `ρ` of `f`.
    have : Flat ρ := MorphismProperty.of_isPullback hsub.flip ‹_›
    have : Surjective ρ := MorphismProperty.of_isPullback hsub.flip ‹_›
    have : LocallyOfFinitePresentation ρ := MorphismProperty.of_isPullback hsub.flip ‹_›
    refine D.le_ker_of_comap_le_ker (g := g) ρ (h' := (i' ≫ ι[Over.mk E'.structureMap]).left) ?_ hj
    simp [i, i', neg_comp_of_isPullback hg h0, reassoc_of% hρ]

include hg h0 in
/-- **Naive cyclic subgroups descend along étale surjective base change.** Let `g : E' ⟶ E` be a
morphism of elliptic curves lying over a quasi-compact étale surjection `f : S' ⟶ S`, for instance
a finite étale surjection, forming a pullback square
with the structure morphisms and carrying the zero section of `E'` to that of `E`. If the inverse
image along `g` of the closed subscheme of `E` cut out by `I` is a naive cyclic subgroup of order
`N`, then so is that closed subscheme. -/
theorem IsNaiveCyclicSubgroup.of_comap [Etale f] [Surjective f] [QuasiCompact f]
    {I : E.carrier.IdealSheafData} {N : ℕ} (h : E'.IsNaiveCyclicSubgroup (I.comap g) N) :
    E.IsNaiveCyclicSubgroup I N := by
  have := h.isFinite
  have := h.flat
  have := h.locallyOfFinitePresentation
  have : MorphismProperty.DescendsAlong @LocallyOfFinitePresentation.{u}
      (@Surjective.{u} ⊓ @Flat.{u} ⊓ @QuasiCompact.{u}) :=
    HasRingHomProperty.descendsAlong_flat RingHom.FinitePresentation.codescendsAlong_faithfullyFlat
  -- The closed subscheme of `I.comap g` is the base change of that of `I` along `f`.
  have hsub := I.isPullback_subschemeMap_comap _ hg
  have hf : (@Surjective.{u} ⊓ @Flat.{u} ⊓ @QuasiCompact.{u} : MorphismProperty Scheme.{u}) f :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hfin : IsFinite (I.subschemeι ≫ E.structureMap) :=
    MorphismProperty.of_isPullback_of_descendsAlong hsub.flip hf ‹_›
  have hflat : Flat (I.subschemeι ≫ E.structureMap) :=
    MorphismProperty.of_isPullback_of_descendsAlong hsub.flip hf ‹_›
  refine
    { exists_grpObj_isMonHom := exists_grpObj_isMonHom_of_comap hg h0 I h.exists_grpObj_isMonHom
      isFinite := hfin
      flat := hflat
      locallyOfFinitePresentation :=
        MorphismProperty.of_isPullback_of_descendsAlong hsub.flip hf ‹_›
      finrank_eq s := ?_
      exists_etale := ?_ }
  · obtain ⟨s', rfl⟩ := f.surjective s
    rw [← I.finrank_comap_of_isPullback _ g _ f hg, h.finrank_eq]
  · -- Compose the étale surjection generating `I.comap g` with `f`.
    obtain ⟨T, t, ht, hts, E₁, g₁, hg₁, h0₁, P, hP, hI⟩ := h.exists_etale
    refine ⟨T, t ≫ f, inferInstance, inferInstance, E₁, g₁ ≫ g, hg₁.paste_horiz hg, ?_, P, hP, ?_⟩
    · rw [reassoc_of% h0₁, h0, Category.assoc]
    · rw [Scheme.IdealSheafData.comap_comp, hI]

/-- **A naive cyclic subgroup of order `N` lies in `E[N]`**, as the definition of a naive
`[Γ₀(N)]`-structure requires: the ideal sheaf of `E[N]` is contained in that of the subgroup.
Étale-locally the subgroup is `[P] + ⋯ + [NP]` for a point `P` of naive exact order `N`, which lies
in `E[N]`, and containment of closed subschemes descends along the étale surjection. -/
theorem IsNaiveCyclicSubgroup.ker_torsionι_le {N : ℕ} [NeZero N] {I : E.carrier.IdealSheafData}
    (h : E.IsNaiveCyclicSubgroup I N) : (E.torsionι N).left.ker ≤ I := by
  obtain ⟨T, t, ht, hts, E₁, g₁, hg₁, h0₁, P, hP, hI⟩ := h.exists_etale
  have : Etale g₁ := MorphismProperty.of_isPullback hg₁.flip ht
  have : Surjective g₁ := MorphismProperty.of_isPullback hg₁.flip hts
  rw [← Scheme.IdealSheafData.comap_le_comap_iff_of_flat_of_surjective g₁, hI,
    ← ker_torsionι_left_of_isPullback N hg₁ h0₁]
  exact hP.ker_torsionι_le_multiplesDivisor

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
