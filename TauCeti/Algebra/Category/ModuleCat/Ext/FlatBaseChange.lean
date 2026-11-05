/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Flat base change of `Ext`

Let `B` be a flat algebra over a commutative ring `A`, and write `B ⊗[A] -` for extension of
scalars `ModuleCat.extendScalars (algebraMap A B)`, an exact functor. Mapping `Ext` classes along it
gives an `A`-linear map `Ext_A^q(N, M) → Ext_B^q(B ⊗[A] N, B ⊗[A] M)`, and hence a `B`-linear base
change map `B ⊗[A] Ext_A^q(N, M) → Ext_B^q(B ⊗[A] N, B ⊗[A] M)`, `b ⊗ x ↦ b • x_B`.

When `A` is Noetherian and `N` is finite, this map is bijective in every degree. In degree zero
this is Mathlib's `Module.FinitePresentation.isBaseChange_map` (homomorphisms out of a finitely
presented module commute with flat base change). The higher degrees follow by dimension shifting
along a presentation `0 → K → A^n → N → 0`: the connecting map identifies `Ext^{q+1}(N, M)` with
the cokernel of `Ext^q(A^n, M) → Ext^q(K, M)` on both sides, `B ⊗[A] -` is right exact, and `K` is
again finite because `A` is Noetherian.

This is the input for the flat base change of local cohomology over Noetherian rings
(Stacks, Lemma 47.10.3 (0BJE)): there `N` runs over the quotients `A ⧸ Iⁿ`.

## Main results

* `TauCeti.ModuleCat.extBaseChange`: the base change map, as a morphism of `B`-modules out of
  `(extendScalars (algebraMap A B)).obj (Ext N M q)`; `extBaseChange_one_tmul` evaluates it.
* `TauCeti.ModuleCat.extBaseChange_extendScalars_map_precomp`: it commutes with precomposition by
  an `Ext` class, which is how it is compatible with connecting maps.
* `TauCeti.ModuleCat.bijective_extBaseChange`: for `A` Noetherian and `N` finite, it is bijective.
* `TauCeti.ModuleCat.extBaseChangeLinearEquiv`: the resulting `B`-linear equivalence
  `B ⊗[A] Ext_A^q(N, M) ≃ₗ[B] Ext_B^q(B ⊗[A] N, B ⊗[A] M)`.
-/

public section

universe u

open CategoryTheory Abelian Limits TensorProduct
open scoped ChangeOfRings

namespace TauCeti.ModuleCat

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Extension of scalars along a flat ring homomorphism is left exact. -/
instance [Module.Flat A B] :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr inferInstance)

variable [Module.Flat A B]

variable (B) in
/-- Mapping `Ext` classes along extension of scalars sends multiplication by `r` to multiplication
by its image in `B`. -/
lemma mapExactFunctor_smul {N M : ModuleCat.{u} A} {q : ℕ} (r : A) (x : Ext N M q) :
    (r • x).mapExactFunctor (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) =
      algebraMap A B r •
        x.mapExactFunctor (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) := by
  rw [Ext.smul_eq_comp_mk₀ x r, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    extendScalars_map_smul_id, Ext.smul_eq_comp_mk₀ (R := B)]

variable (B) in
/-- `Ext` over `A`, mapped by extension of scalars to `Ext` over `B`, as an `A`-linear map to the
restriction of scalars of the latter. -/
noncomputable def extToRestrictScalars (N M : ModuleCat.{u} A) (q : ℕ) :
    ModuleCat.of A (Ext N M q) ⟶ (ModuleCat.restrictScalars (algebraMap A B)).obj
      (ModuleCat.of B (Ext ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).obj N)
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).obj M) q)) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (algebraMap A B)).obj
      (ModuleCat.of B (Ext ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).obj N)
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).obj M) q)))
    { toFun x := x.mapExactFunctor (ModuleCat.extendScalars.{u, u, u} (algebraMap A B))
      map_add' x y :=
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapExtAddHom N M q).map_add x y
      map_smul' r x := mapExactFunctor_smul B r x }

variable (B) in
/-- The base change map `B ⊗[A] Ext_A(N, M) → Ext_B(B ⊗[A] N, B ⊗[A] M)`, `b ⊗ x ↦ b • x_B`. -/
noncomputable def extBaseChange (N M : ModuleCat.{u} A) (q : ℕ) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).obj (ModuleCat.of A (Ext N M q)) ⟶
      ModuleCat.of B (Ext ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).obj N)
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).obj M) q) :=
  ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A B)).homEquiv _ _).symm
    (extToRestrictScalars B N M q)

/-- The base change map sends `1 ⊗ x` to the image of `x` under extension of scalars. -/
@[simp]
lemma extBaseChange_one_tmul {N M : ModuleCat.{u} A} {q : ℕ} (x : Ext N M q) :
    extBaseChange B N M q ((1 : B) ⊗ₜ[A, algebraMap A B] x) =
      x.mapExactFunctor (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
  congr($((((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A B)).homEquiv _
    _).apply_symm_apply (extToRestrictScalars B N M q))) x)

/-- The base change map commutes with precomposition by an `Ext` class `α`, extended to `B` on the
target side. -/
lemma extendScalars_map_precomp_comp_extBaseChange {X Y Z : ModuleCat.{u} A} {n a b : ℕ}
    (α : Ext X Y n) (h : n + a = b) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).map
        (ModuleCat.ofHom (α.precompOfLinear A Z h)) ≫ extBaseChange B X Z b =
      extBaseChange B Y Z a ≫ ModuleCat.ofHom
        ((α.mapExactFunctor (ModuleCat.extendScalars.{u, u, u} (algebraMap A B))).precompOfLinear B
          ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).obj Z) h) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change extBaseChange B X Z b ((1 : B) ⊗ₜ[A, algebraMap A B] (α.comp x h)) =
    (α.mapExactFunctor (ModuleCat.extendScalars.{u, u, u} (algebraMap A B))).comp
      (extBaseChange B Y Z a ((1 : B) ⊗ₜ[A, algebraMap A B] x)) h
  rw [extBaseChange_one_tmul, extBaseChange_one_tmul, Ext.mapExactFunctor_comp]

/-- Elementwise form of `extendScalars_map_precomp_comp_extBaseChange`. -/
lemma extBaseChange_extendScalars_map_precomp {X Y Z : ModuleCat.{u} A} {n a b : ℕ}
    (α : Ext X Y n) (h : n + a = b) (t) :
    extBaseChange B X Z b ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).map
        (ModuleCat.ofHom (α.precompOfLinear A Z h)) t) =
      (α.mapExactFunctor (ModuleCat.extendScalars.{u, u, u} (algebraMap A B))).comp
        (extBaseChange B Y Z a t) h :=
  congr($(extendScalars_map_precomp_comp_extBaseChange (B := B) α h) t)


/-- Flat base change of `Ext` in degree zero, for a finitely presented first argument: this is
`Module.FinitePresentation.isBaseChange_map` transported along `Ext⁰ = Hom`. -/
theorem bijective_extBaseChange_zero (N M : ModuleCat.{u} A)
    [Module.FinitePresentation A N] : Function.Bijective (extBaseChange B N M 0) := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap A B)
  let E := Ext (F.obj N) (F.obj M) 0
  let : Module A E := Module.compHom E (algebraMap A B)
  have : IsScalarTower A B E := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let φ : Ext N M 0 →ₗ[A] E :=
    { toFun x := x.mapExactFunctor F
      map_add' x y := (F.mapExtAddHom N M 0).map_add x y
      map_smul' r x := mapExactFunctor_smul B r x }
  let eM : (N →ₗ[A] M) ≃ₗ[A] Ext N M 0 :=
    (ModuleCat.homLinearEquiv (S := A)).symm.trans (Ext.linearEquiv₀ (R := A)).symm
  let iN := ModuleCat.extendScalarsAlgebraMapIso (S := B) N
  let iM := ModuleCat.extendScalarsAlgebraMapIso (S := B) M
  let eN : (B ⊗[A] N →ₗ[B] B ⊗[A] M) ≃ₗ[B] E :=
    (ModuleCat.homLinearEquiv (S := B)).symm.trans
      ((Linear.homCongr B iN.symm iM.symm).trans (Ext.linearEquiv₀ (R := B)).symm)
  have hφ : IsBaseChange B φ := by
    refine (IsBaseChange.iff_of_equiv_comm eM eN (LinearMap.ext fun g ↦ ?_)).mp
      (Module.FinitePresentation.isBaseChange_map A N M B)
    change (Ext.mk₀ (ModuleCat.ofHom g)).mapExactFunctor F =
      Ext.mk₀ (iN.hom ≫ ModuleCat.ofHom (g.baseChange B) ≫ iM.inv)
    rw [Ext.mapExactFunctor_mk₀]
    congr 1
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change (1 : B) ⊗ₜ[A, algebraMap A B] g m =
      (ModuleCat.extendScalarsAlgebraMapIso (S := B) M).inv (g.baseChange B
        ((ModuleCat.extendScalarsAlgebraMapIso (S := B) N).hom
          ((1 : B) ⊗ₜ[A, algebraMap A B] m)))
    have h₁ := ModuleCat.extendScalarsAlgebraMapIso_hom_tmul (S := B) N 1 m
    have h₂ := ModuleCat.extendScalarsAlgebraMapIso_inv_tmul (S := B) M 1 (g m)
    exact h₂.symm.trans (congrArg _ ((LinearMap.baseChange_tmul g 1 m).symm.trans
      (congrArg _ h₁.symm)))
  have := ModuleCat.isIso_extendRestrictScalarsAdj_homEquiv_symm_of_isBaseChange hφ
  have key : extToRestrictScalars B N M 0 =
      ModuleCat.ofHom φ ≫ (ModuleCat.restrictScalarsAlgebraMapIso E).inv := by
    ext x
    exact (ModuleCat.restrictScalarsAlgebraMapIso_inv_apply (R := A) (S := B) E (φ x)).symm
  unfold extBaseChange
  rw [key]
  exact ConcreteCategory.bijective_of_isIso _

section Noetherian

variable [IsNoetherianRing A]

/-- The inductive step of flat base change of `Ext`: if the base change map is bijective in degree
`q` for every finite first argument, then so it is in degree `q + 1`. This shifts dimension along
a presentation `0 → K → A^n → N → 0`, which has a finite kernel since `A` is Noetherian. -/
theorem bijective_extBaseChange_succ (M : ModuleCat.{u} A) (q : ℕ)
    (ih : ∀ (N : ModuleCat.{u} A) [Module.Finite A N],
      Function.Bijective (extBaseChange B N M q))
    (N : ModuleCat.{u} A) [Module.Finite A N] :
    Function.Bijective (extBaseChange B N M (q + 1)) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A N
  let S : ShortComplex (ModuleCat.{u} A) :=
    ShortComplex.mk (ModuleCat.ofHom (LinearMap.ker π).subtype) (ModuleCat.ofHom π)
      (by ext x; exact x.2)
  have hS : S.ShortExact :=
    { exact := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
        (LinearMap.exact_subtype_ker_map π).linearMap_ker_eq.symm
      mono_f := (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker π).injective_subtype
      epi_g := (ModuleCat.epi_iff_surjective _).mpr hπ }
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap A B)
  have hS' : (S.map F).ShortExact := hS.map_of_exact F
  have : Projective S.X₂ := inferInstance
  have : Projective (S.map F).X₂ :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).map_projective _ inferInstance
  have : Module.Finite A S.X₁ := inferInstanceAs (Module.Finite A (LinearMap.ker π))
  have : Module.Finite A S.X₂ := inferInstanceAs (Module.Finite A (Fin n → A))
  have h : 1 + q = q + 1 := add_comm 1 q
  have hδ : Function.Surjective (hS.extClass.precompOfLinear A M h) := fun y ↦
    Ext.contravariant_sequence_exact₃ hS M y (Ext.eq_zero_of_projective _) h
  have hFδ : Function.Surjective (F.map (ModuleCat.ofHom
      (hS.extClass.precompOfLinear A M h))) := by
    have : Epi (ModuleCat.ofHom (hS.extClass.precompOfLinear A M h)) :=
      (ModuleCat.epi_iff_surjective _).mpr hδ
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨w, rfl⟩ := hFδ t
    rw [extBaseChange_extendScalars_map_precomp, Ext.mapExactFunctor_extClass] at ht
    obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₁ hS' _ _ h ht
    obtain ⟨u, rfl⟩ := (ih S.X₂).2 z
    have hw : F.map (ModuleCat.ofHom ((Ext.mk₀ S.f).precompOfLinear A M (zero_add q))) u =
        w := (ih S.X₁).1 (by
      rw [extBaseChange_extendScalars_map_precomp, Ext.mapExactFunctor_mk₀]
      exact hz)
    have h0 : ModuleCat.ofHom ((Ext.mk₀ S.f).precompOfLinear A M (zero_add q)) ≫
        ModuleCat.ofHom (hS.extClass.precompOfLinear A M h) = 0 := by
      ext x
      simp [ShortComplex.ShortExact.extClass_comp_assoc]
    rw [← hw, ← ConcreteCategory.comp_apply, ← F.map_comp, h0, F.map_zero]
    rfl
  · intro y
    obtain ⟨x, hx⟩ :=
      Ext.contravariant_sequence_exact₃ hS' (F.obj M) y (Ext.eq_zero_of_projective _) h
    obtain ⟨w, rfl⟩ := (ih S.X₁).2 x
    exact ⟨F.map (ModuleCat.ofHom (hS.extClass.precompOfLinear A M h)) w, by
      rw [extBaseChange_extendScalars_map_precomp, Ext.mapExactFunctor_extClass, ← hx]⟩

/-- **Flat base change of `Ext`.** Over a Noetherian ring `A`, for a flat `A`-algebra `B`, a
finite `A`-module `N`, any `A`-module `M` and every degree `q`, the base change map
`B ⊗[A] Ext_A^q(N, M) → Ext_B^q(B ⊗[A] N, B ⊗[A] M)` is bijective. -/
theorem bijective_extBaseChange (N M : ModuleCat.{u} A) [Module.Finite A N] (q : ℕ) :
    Function.Bijective (extBaseChange B N M q) := by
  induction q generalizing N with
  | zero =>
    have := Module.finitePresentation_of_finite A N
    exact bijective_extBaseChange_zero N M
  | succ q ih => exact bijective_extBaseChange_succ M q (fun N _ ↦ ih N) N

/-- Flat base change of `Ext` over a Noetherian ring, as an isomorphism of `B`-modules. -/
instance isIso_extBaseChange (N M : ModuleCat.{u} A) [Module.Finite A N] (q : ℕ) :
    IsIso (extBaseChange B N M q) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_extBaseChange N M q)

variable (B) in
/-- Flat base change of `Ext` over a Noetherian ring, as a `B`-linear equivalence
`B ⊗[A] Ext_A^q(N, M) ≃ Ext_B^q(B ⊗[A] N, B ⊗[A] M)` for a finite `A`-module `N`. -/
noncomputable def extBaseChangeLinearEquiv (N M : ModuleCat.{u} A) [Module.Finite A N]
    (q : ℕ) :
    B ⊗[A] Ext N M q ≃ₗ[B] Ext ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).obj N)
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).obj M) q :=
  ((ModuleCat.extendScalarsAlgebraMapIso (S := B) (ModuleCat.of A (Ext N M q))).symm ≪≫
    asIso (extBaseChange B N M q)).toLinearEquiv

/-- `extBaseChangeLinearEquiv` sends `b ⊗ x` to `b` times the image of `x`. -/
@[simp]
lemma extBaseChangeLinearEquiv_tmul (N M : ModuleCat.{u} A) [Module.Finite A N] (q : ℕ)
    (b : B) (x : Ext N M q) :
    extBaseChangeLinearEquiv B N M q (b ⊗ₜ x) =
      b • x.mapExactFunctor (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) := by
  have h₁ := ModuleCat.extendScalarsAlgebraMapIso_inv_tmul (S := B)
    (ModuleCat.of A (Ext N M q)) b x
  have h₂ := ModuleCat.ExtendScalars.smul_tmul (algebraMap A B)
    (M := ModuleCat.of A (Ext N M q)) b 1 x
  rw [mul_one] at h₂
  change extBaseChange B N M q ((ModuleCat.extendScalarsAlgebraMapIso (S := B)
    (ModuleCat.of A (Ext N M q))).inv (b ⊗ₜ x)) = _
  rw [h₁, ← h₂]
  exact ((extBaseChange B N M q).hom.map_smul b _).trans
    (congrArg (b • ·) (extBaseChange_one_tmul x))

end Noetherian

end TauCeti.ModuleCat
