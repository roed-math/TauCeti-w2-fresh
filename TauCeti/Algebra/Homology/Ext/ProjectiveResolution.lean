/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import TauCeti.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Computing `Ext` from projective resolutions

Mathlib's `CategoryTheory.ProjectiveResolution.isoExt` computes `Extⁿ(X, Y)` from any projective
resolution `P` of `X`. When two resolutions of `X` are related by a chain map lying over the
identity of `X`, `isoExt_hom_comp_homologyMap` identifies the resulting computations.

Mathlib computes `Extⁿ(X, Y)` from a projective resolution `R` of `X` as the `n`-th cohomology of
the complex `Hom(R, Y)`: `CategoryTheory.ProjectiveResolution.extMk` builds a class from a cocycle,
`extMk_surjective` says every class arises that way, and `extMk_eq_zero_iff` identifies the
coboundaries.

This file records the degenerate case of that computation. If the two differentials of `R`
adjacent to a degree `n + 1` die against `Y` -- that is, if `d (n + 2) (n + 1) ≫ f = 0` for every
`f : Rₙ₊₁ ⟶ Y` and `d (n + 1) n ≫ g = 0` for every `g : Rₙ ⟶ Y` -- then in that degree no cocycle
condition and no coboundary survives, and `Extⁿ⁺¹(X, Y)` *is* the term `Hom(Rₙ₊₁, Y)`, linearly
over the coefficient ring.

Degree `0` is deliberately excluded: there `Ext⁰(X, Y)` is `Hom(X, Y)`, which need not be
`Hom(R₀, Y)`.

At the other extreme, a resolution whose terms vanish from degree `n` on bounds the projective
dimension of `X` by `n`.

Mathlib has two `Ext`s: the derived functor `Ext k C n` of `Mathlib.CategoryTheory.Abelian.Ext`,
computed by `isoExt`, and the derived-category `CategoryTheory.Abelian.Ext`, computed by `extMk`.
Both are the cohomology of the same complex `Hom(R, Y)`. So in positive degrees they vanish
together, and a map induced by `g : X' ⟶ X` on the first is injective once precomposition with `g`
is injective on the second. The comparison of maps rests on `Ext_map_comp_isoExt_hom`, the
naturality of `isoExt` in `X`, and on a cocycle criterion for injectivity on homology of complexes
of modules.

## Main definitions

* `CategoryTheory.ProjectiveResolution.extLinearEquiv`: the linear equivalence
  `Hom(Rₙ₊₁, Y) ≃ₗ Extⁿ⁺¹(X, Y)`, sending `f` to its class.

## Main results

* `CategoryTheory.ProjectiveResolution.isoExt_hom_comp_homologyMap`: computing `Ext` from two
  resolutions related by a chain map agrees with the induced map on cohomology.
* `CategoryTheory.ProjectiveResolution.hasProjectiveDimensionLT`: a projective resolution whose
  terms vanish from degree `n` on gives `HasProjectiveDimensionLT X n`.
* `TauCeti.ShortComplex.injective_homologyMap_moduleCat`,
  `TauCeti.HomologicalComplex.injective_homologyMap_moduleCat`: a map of complexes of modules is
  injective on homology when every cycle mapping to a boundary is a boundary.
* `TauCeti.Ext_map_comp_isoExt_hom`: `ProjectiveResolution.isoExt` is natural in the first
  argument.
* `TauCeti.injective_Ext_map_succ`: in positive degrees, a map induced on the derived-functor `Ext`
  is injective once precomposition is injective on the derived-category `Ext`.
* `TauCeti.isZero_Ext_succ_iff_subsingleton`: in positive degrees, the derived-functor `Ext` of
  `Mathlib.CategoryTheory.Abelian.Ext` vanishes exactly when the derived-category
  `CategoryTheory.Abelian.Ext` does, since both are computed by the same `Hom`-complex.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Sections 2.2 and 2.4, for independence of
  `Ext` from the resolution, and Section 2.5, for `Ext` computed from a projective resolution.
-/

public section

namespace CategoryTheory.ProjectiveResolution

open CategoryTheory.Abelian

section Comparison

variable {R : Type*} [Ring R] {D : Type*} [Category* D] [Abelian D] [Linear R D]
  [EnoughProjectives D]

/-- **`Ext` computed from two resolutions related by a chain map.** If `φ : P ⟶ Q` is a chain map
between projective resolutions of `X` lying over the identity of `X`, then computing `Extⁿ(X, Y)`
from `Q` and precomposing with `φ` gives the computation from `P`. -/
theorem isoExt_hom_comp_homologyMap {X : D} (P Q : ProjectiveResolution X)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) (n : ℕ) (Y : D) :
    (Q.isoExt n Y).hom ≫ HomologicalComplex.homologyMap
      ((HomologicalComplex.unopFunctor _ _).map
        ((((linearYoneda R D).obj Y).rightOp.mapHomologicalComplex _).map φ).op) n =
      (P.isoExt n Y).hom := by
  have h := isoLeftDerivedObj_hom_naturality (𝟙 X) P Q φ
    (comm.trans (Category.comp_id _).symm) ((linearYoneda R D).obj Y).rightOp n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  have hP := congrArg Quiver.Hom.unop ((Iso.comp_inv_eq _).2 ((Iso.eq_inv_comp _).2 h.symm))
  have hn := TauCeti.HomologicalComplex.homologyUnop_inv_naturality
    ((((linearYoneda R D).obj Y).rightOp.mapHomologicalComplex _).map φ) n
  -- `isoExt` is by definition the inverse of `isoLeftDerivedObj`, unopposed, followed by the
  -- inverse of `homologyUnop`; its two constituents are what the two naturality squares govern.
  have e : (Q.isoExt n Y).hom =
      (Q.isoLeftDerivedObj ((linearYoneda R D).obj Y).rightOp n).inv.unop ≫
        (HomologicalComplex.homologyUnop _ n).inv := rfl
  rw [e]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hn.symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hP)))

end Comparison

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Ring k] [Linear k C]
  [HasExt.{w} C] {X Y : C}

omit [Ring k] [Linear k C] in
/-- If the degree-`n` term of a projective resolution has no nonzero morphism to `Y`, then
`Extⁿ(X,Y)` vanishes. No condition on the neighboring terms is needed. -/
theorem subsingleton_ext_of_subsingleton_hom (R : ProjectiveResolution X) (n : ℕ)
    [Subsingleton (R.complex.X n ⟶ Y)] : Subsingleton (Ext.{w} X Y n) := by
  apply subsingleton_of_forall_eq 0
  intro α
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective α (n + 1) rfl
  obtain rfl : f = 0 := Subsingleton.elim _ _
  simp

omit [HasExt.{w} C] in
/-- A projective resolution of `X` whose terms vanish from degree `n` on shows that `X` has
projective dimension less than `n`. -/
theorem hasProjectiveDimensionLT (R : ProjectiveResolution X) (n : ℕ)
    (h : ∀ i, n ≤ i → Limits.IsZero (R.complex.X i)) : HasProjectiveDimensionLT X n := by
  let := HasExt.standard C
  refine HasProjectiveDimensionLT.mk fun i hi Y e ↦ ?_
  have : Subsingleton (R.complex.X i ⟶ Y) := ⟨fun f g ↦ (h i hi).eq_of_src f g⟩
  have := R.subsingleton_ext_of_subsingleton_hom (Y := Y) i
  exact Subsingleton.elim _ _

/-- If the two differentials of a projective resolution `R` of `X` adjacent to degree `n + 1`
become zero after applying `Hom(-, Y)`, then `Extⁿ⁺¹(X, Y)` is the degree `n + 1` term of that
`Hom`-complex, `k`-linearly. The class of `f` is `CategoryTheory.ProjectiveResolution.extMk f`. -/
noncomputable def extLinearEquiv (R : ProjectiveResolution X) (n : ℕ)
    (h₁ : ∀ f : R.complex.X (n + 1) ⟶ Y, R.complex.d (n + 2) (n + 1) ≫ f = 0)
    (h₂ : ∀ g : R.complex.X n ⟶ Y, R.complex.d (n + 1) n ≫ g = 0) :
    (R.complex.X (n + 1) ⟶ Y) ≃ₗ[k] Ext.{w} X Y (n + 1) := by
  refine LinearEquiv.ofBijective
    { toFun := fun f => R.extMk f (n + 2) rfl (h₁ f)
      map_add' := fun f g => (R.add_extMk f g (n + 2) rfl (h₁ f) (h₁ g)).symm
      map_smul' := fun c f => ?_ } ⟨?_, ?_⟩
  · dsimp
    rw [Ext.smul_eq_comp_mk₀, R.extMk_comp_mk₀]
    congr 1
    rw [Linear.comp_smul, Category.comp_id]
  · rw [← LinearMap.ker_eq_bot]
    ext f
    simp only [LinearMap.mem_ker, Submodule.mem_bot, LinearMap.coe_mk, AddHom.coe_mk]
    rw [R.extMk_eq_zero_iff f (n + 2) rfl (h₁ f) n rfl]
    exact ⟨fun ⟨g, hg⟩ ↦ hg ▸ h₂ g, fun hf ↦ ⟨0, by simp [hf]⟩⟩
  · intro α
    obtain ⟨f, hf, rfl⟩ := R.extMk_surjective α (n + 2) rfl
    exact ⟨f, rfl⟩

@[simp]
theorem extLinearEquiv_apply (R : ProjectiveResolution X) (n : ℕ)
    (h₁ : ∀ f : R.complex.X (n + 1) ⟶ Y, R.complex.d (n + 2) (n + 1) ≫ f = 0)
    (h₂ : ∀ g : R.complex.X n ⟶ Y, R.complex.d (n + 1) n ≫ g = 0)
    (f : R.complex.X (n + 1) ⟶ Y) :
    extLinearEquiv (k := k) R n h₁ h₂ f = R.extMk f (n + 2) rfl (h₁ f) :=
  (rfl)

end CategoryTheory.ProjectiveResolution

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

variable {C : Type*} [Category* C] [Abelian C] {k : Type*} [Ring k] [Linear k C]
  [EnoughProjectives C]

/-- In positive degrees, the derived-functor `Ext k C` vanishes exactly when the derived-category
`Ext` does: both are the cohomology of `Hom(P, Y)` for a projective resolution `P` of `X`, the
first through `ProjectiveResolution.isoExt` and the second through
`ProjectiveResolution.extMk`. -/
theorem isZero_Ext_succ_iff_subsingleton [HasExt C] (X Y : C) (p : ℕ) :
    IsZero (((_root_.Ext k C (p + 1)).obj (op X)).obj Y) ↔ Subsingleton (Ext X Y (p + 1)) := by
  let P := projectiveResolution X
  rw [(P.isoExt (p + 1) Y).isZero_iff, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  refine ⟨fun h => subsingleton_of_forall_eq 0 fun α => ?_, fun h f hf => ?_⟩
  · obtain ⟨f, hf, rfl⟩ := P.extMk_surjective α (p + 2) rfl
    exact (P.extMk_eq_zero_iff f (p + 2) rfl hf p rfl).2 (h f hf)
  · exact (P.extMk_eq_zero_iff f (p + 2) rfl hf p rfl).1 (Subsingleton.elim _ _)

/-- A morphism `φ` of short complexes of modules is injective on homology as soon as every cycle
of `S₁` whose image is a boundary of `S₂` is already a boundary of `S₁`. -/
theorem ShortComplex.injective_homologyMap_moduleCat {R : Type*} [Ring R]
    {S₁ S₂ : ShortComplex (ModuleCat R)} (φ : S₁ ⟶ S₂)
    (h : ∀ x₂ : S₁.X₂, S₁.g x₂ = 0 → (∃ y₁ : S₂.X₁, S₂.f y₁ = φ.τ₂ x₂) →
      ∃ x₁ : S₁.X₁, S₁.f x₁ = x₂) :
    Function.Injective (ShortComplex.homologyMap φ).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective S₁.homologyπ).1 inferInstance x
  have hz : S₂.homologyπ (ShortComplex.cyclesMap φ z) = 0 := by
    rw [← ModuleCat.comp_apply, ← ShortComplex.homologyπ_naturality, ModuleCat.comp_apply, hx]
  obtain ⟨y₁, hy₁⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((ShortComplex.mk _ _ S₂.toCycles_comp_homologyπ).exact_of_g_is_cokernel
      S₂.homologyIsCokernel) _ hz
  obtain ⟨x₁, hx₁⟩ := h (S₁.iCycles z) (by rw [← ModuleCat.comp_apply, S₁.iCycles_g]; rfl)
    ⟨y₁, by
      have := congrArg S₂.iCycles hy₁
      rwa [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, S₂.toCycles_i,
        ShortComplex.cyclesMap_i] at this⟩
  have : S₁.toCycles x₁ = z := (ModuleCat.mono_iff_injective S₁.iCycles).1 inferInstance
    (by rw [← ModuleCat.comp_apply, S₁.toCycles_i, hx₁])
  rw [← this, ← ModuleCat.comp_apply, S₁.toCycles_comp_homologyπ]
  rfl


/-- A morphism `ψ` of complexes of modules is injective on homology in degree `j` as soon as every
cycle of `K` whose image is a boundary of `L` is already a boundary of `K`. -/
theorem HomologicalComplex.injective_homologyMap_moduleCat {R : Type*} [Ring R] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex (ModuleCat R) c} (ψ : K ⟶ L) {i j l : ι}
    (hi : c.prev j = i) (hl : c.next j = l)
    (h : ∀ x : K.X j, K.d j l x = 0 → (∃ y : L.X i, L.d i j y = ψ.f j x) →
      ∃ x' : K.X i, K.d i j x' = x) :
    Function.Injective (HomologicalComplex.homologyMap ψ j).hom := by
  subst hi hl
  exact ShortComplex.injective_homologyMap_moduleCat _ h

/-- **`isoExt` is natural in the first argument.** If `φ : P' ⟶ P` is a chain map between
projective resolutions lying over `g : X' ⟶ X`, then computing `Ext` from `P` and `P'` turns the map
`Extⁿ(X, Y) ⟶ Extⁿ(X', Y)` induced by `g` into the map induced by `φ` on `Hom`-complexes. -/
theorem Ext_map_comp_isoExt_hom {X X' : C} (g : X' ⟶ X) (P : ProjectiveResolution X)
    (P' : ProjectiveResolution X') (φ : P'.complex ⟶ P.complex)
    (comm : φ.f 0 ≫ P.π.f 0 = P'.π.f 0 ≫ g) (n : ℕ) (Y : C) :
    ((_root_.Ext k C n).map g.op).app Y ≫ (P'.isoExt n Y).hom =
      (P.isoExt n Y).hom ≫ HomologicalComplex.homologyMap
        ((HomologicalComplex.unopFunctor _ _).map
          ((((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex _).map φ).op) n := by
  let F := ((linearYoneda k C).obj Y).rightOp
  have h : (P'.isoLeftDerivedObj F n).inv ≫ (F.leftDerived n).map g =
      (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ ≫
        (P.isoLeftDerivedObj F n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact P'.isoLeftDerivedObj_hom_naturality g P φ comm F n
  have hu : ((_root_.Ext k C n).map g.op).app Y ≫ (P'.isoLeftDerivedObj F n).inv.unop =
      (P.isoLeftDerivedObj F n).inv.unop ≫
        ((F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ).unop :=
    congrArg Quiver.Hom.unop h
  have hn := TauCeti.HomologicalComplex.homologyUnop_inv_naturality
    ((F.mapHomologicalComplex _).map φ) n
  change _ ≫ (P'.isoLeftDerivedObj F n).inv.unop ≫ (HomologicalComplex.homologyUnop _ n).inv =
    ((P.isoLeftDerivedObj F n).inv.unop ≫ (HomologicalComplex.homologyUnop _ n).inv) ≫ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hu).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) hn).trans (Category.assoc _ _ _).symm)))

/-- In positive degrees, the map `Ext k C (p + 1)` induces along `g : X' ⟶ X` is injective once
precomposition with `g` is injective on the derived-category `Ext`: both are computed by the
same `Hom`-complexes, through `ProjectiveResolution.isoExt` and `ProjectiveResolution.extMk`. -/
theorem injective_Ext_map_succ [HasExt C] {X X' : C} (g : X' ⟶ X) (Y : C) (p : ℕ)
    (h : Function.Injective fun α : Ext X Y (p + 1) => (Ext.mk₀ g).comp α (zero_add _)) :
    Function.Injective (((_root_.Ext k C (p + 1)).map g.op).app Y).hom := by
  let P := projectiveResolution X
  let P' := projectiveResolution X'
  let φ : ProjectiveResolution.Hom P' P g :=
    ⟨ProjectiveResolution.lift g P' P,
      by simpa using ProjectiveResolution.lift_commutes_zero g P' P⟩
  have sq := Ext_map_comp_isoExt_hom (k := k) g P P' φ.hom
    (ProjectiveResolution.lift_commutes_zero g P' P) (p + 1) Y
  let ψ := (HomologicalComplex.unopFunctor _ _).map
    ((((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex _).map φ.hom).op
  have hH := HomologicalComplex.injective_homologyMap_moduleCat ψ (i := p) (j := p + 1)
    (l := p + 2) ((ComplexShape.down ℕ).symm.prev_eq' rfl)
    ((ComplexShape.down ℕ).symm.next_eq' rfl)
    fun (x : P.complex.X (p + 1) ⟶ Y) (hx : P.complex.d (p + 2) (p + 1) ≫ x = 0)
      ⟨(y : P'.complex.X p ⟶ Y), (hy : P'.complex.d (p + 1) p ≫ y = φ.hom.f (p + 1) ≫ x)⟩ => by
      have h1 := (P'.extMk_eq_zero_iff (φ.hom.f (p + 1) ≫ x) (p + 2) rfl
        (by simp [← φ.hom.comm_assoc, hx]) p rfl).2 ⟨y, hy⟩
      have h2 := ProjectiveResolution.mk₀_comp_extMk x (p + 2) rfl hx φ
      exact (P.extMk_eq_zero_iff x (p + 2) rfl hx p rfl).1
        (h ((h2.trans h1).trans (Ext.comp_zero _ _ _ _ _).symm))
  have hm : Mono (HomologicalComplex.homologyMap ψ (p + 1)) :=
    (ModuleCat.mono_iff_injective _).2 hH
  have : Mono ((((_root_.Ext k C (p + 1)).map g.op).app Y) ≫ (P'.isoExt (p + 1) Y).hom) := by
    rw [sq]
    exact @mono_comp _ _ _ _ _ _ inferInstance _ hm
  exact (ModuleCat.mono_iff_injective _).1 (mono_of_mono _ (P'.isoExt (p + 1) Y).hom)

end TauCeti
