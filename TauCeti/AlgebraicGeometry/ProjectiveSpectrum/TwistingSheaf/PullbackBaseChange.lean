/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.BaseChange
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent
public import TauCeti.AlgebraicGeometry.Modules.AffineRestriction
public import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange

/-!
# Twisting sheaves pull back along base changes of graded rings

For a graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` (with `ℬ₊ ≤ f(𝒜₊)`), the morphism of twisting
sheaves `AlgebraicGeometry.Proj.twistingSheafMap f hf n : 𝒪(n) ⟶ (Proj.map f)_* 𝒪(n)` is adjoint to
a comparison

`(Proj.map f)^* 𝒪_{Proj 𝒜}(n) ⟶ 𝒪_{Proj ℬ}(n)`

(`AlgebraicGeometry.Proj.pullbackTwistingSheafMap`), which sends the pullback of a section `s` to
its image under `twistingSheaf.comap`. This file proves that the comparison is an isomorphism for
every `n ∈ ℤ` whenever `f` is a base change in every degree along a coefficient extension `R → S`
(`AlgebraicGeometry.Proj.isIso_pullbackTwistingSheafMap_of_isBaseChange`), without assuming that
`𝒜` is generated in degree one.

Both sheaves are quasi-coherent, so it suffices to check bijectivity on the sections over the
affine opens `D₊(f a) = (Proj.map f)⁻¹ D₊(a)`, which cover `Proj ℬ`
(`AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_bijective_app`). There, both the pullback of
sections (`AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackSectionsLE`) and the pullback of
sections of twisting sheaves (`AlgebraicGeometry.Proj.twistingSheaf.isBaseChange_comap_basicOpen`)
are base changes along `Γ(D₊(a), 𝒪) → Γ(D₊(f a), 𝒪)`, and the comparison is the map between them.

## Main definitions

* `AlgebraicGeometry.Proj.pullbackTwistingSheafMap f hf n`: the comparison
  `(Proj.map f)^* 𝒪(n) ⟶ 𝒪(n)`.

## Main results

* `AlgebraicGeometry.Proj.pullbackTwistingSheafMap_app_pullbackSectionsLE`: the comparison on
  pulled-back sections.
* `AlgebraicGeometry.Proj.isIso_pullbackTwistingSheafMap_of_forall_isBaseChange`: the comparison
  is an isomorphism for a degreewise base change.
* `AlgebraicGeometry.Proj.isIso_pullbackTwistingSheafMap_of_isBaseChange`: the comparison is an
  isomorphism for a base change `B = S ⊗[R] A`, in the form of
  `AlgebraicGeometry.Proj.isPullback_map_of_isBaseChange`.

## References

* [Stacks, Lemma 27.11.6 (01N2)](https://stacks.math.columbia.edu/tag/01N2)
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Proj

universe u

section

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)

/-- **The comparison of twisting sheaves along `Proj.map`**: the morphism
`(Proj.map f hf)^* 𝒪_{Proj 𝒜}(n) ⟶ 𝒪_{Proj ℬ}(n)` adjoint to
`AlgebraicGeometry.Proj.twistingSheafMap`. -/
def pullbackTwistingSheafMap (n : ℤ) :
    (Scheme.Modules.pullback (map f hf)).obj (twistingSheaf 𝒜 n) ⟶ twistingSheaf ℬ n :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (map f hf)).homEquiv _ _).symm
    (twistingSheafMap f hf n)

/-- The comparison `pullbackTwistingSheafMap` is the transpose of `twistingSheafMap` under the
pullback–pushforward adjunction of `Proj.map f hf`. -/
theorem pullbackTwistingSheafMap_eq (n : ℤ) :
    pullbackTwistingSheafMap f hf n =
      ((Scheme.Modules.pullbackPushforwardAdjunction (map f hf)).homEquiv _ _).symm
        (twistingSheafMap f hf n) :=
  (rfl)

/-- The comparison sends the pullback of a section `s` of `𝒪_{Proj 𝒜}(n)` over `U`, restricted to
an open `V ≤ (Proj.map f)⁻¹ U`, to the pullback `twistingSheaf.comap f hf s` of `s` to `V`. -/
theorem pullbackTwistingSheafMap_app_pullbackSectionsLE (n : ℤ) (U : (Proj 𝒜).Opens)
    (V : (Proj ℬ).Opens) (hV : V ≤ map f hf ⁻¹ᵁ U) (s : Γ(twistingSheaf 𝒜 n, U)) :
    (pullbackTwistingSheafMap f hf n).app V ((map f hf).pullbackSectionsLE _ U V hV s) =
      twistingSheaf.comap f hf (fun _ hy ↦ hV hy) s := by
  have e : (Scheme.Modules.pullbackPushforwardAdjunction (map f hf)).unit.app _ ≫
      (Scheme.Modules.pushforward (map f hf)).map (pullbackTwistingSheafMap f hf n) =
        twistingSheafMap f hf n :=
    ((Scheme.Modules.pullbackPushforwardAdjunction (map f hf)).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  have hs := congr(Scheme.Modules.Hom.app $e U s)
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app, twistingSheafMap_app] at hs
  rw [Scheme.Hom.pullbackSectionsLE_apply]
  refine (congr($((pullbackTwistingSheafMap f hf n).mapPresheaf.naturality (homOfLE hV).op)
    ((map f hf).pullbackSections _ U s))).trans ?_
  rw [ConcreteCategory.comp_apply, Scheme.Hom.pullbackSections_apply]
  exact (congrArg ((twistingSheaf ℬ n).presheaf.map (homOfLE hV).op) hs).trans
    (twistingSheaf.res_comap f hf _ (homOfLE hV) s)

end

/-- A linear map between two base changes `P` and `Q` of `M` along `R → S`, compatible with the
maps from `M`, is bijective. -/
private theorem bijective_of_isBaseChange {R S M P Q : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] [Module S P]
    [IsScalarTower R S P] [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    {p : M →ₗ[R] P} {q : M →ₗ[R] Q} (hp : IsBaseChange S p) (hq : IsBaseChange S q)
    (L : P →ₗ[S] Q) (hL : ∀ m, L (p m) = q m) : Function.Bijective L := by
  have e : L ∘ₗ hp.equiv.toLinearMap = hq.equiv.toLinearMap := by
    refine TensorProduct.AlgebraTensorModule.ext fun a m ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, IsBaseChange.equiv_tmul,
      LinearMap.map_smul, hL]
  have hb : Function.Bijective (L ∘ₗ hp.equiv.toLinearMap) := by
    rw [e]
    exact hq.equiv.bijective
  exact (Function.Bijective.of_comp_iff L hp.equiv.bijective).mp hb

variable {R S A B : Type u} [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {ℬ : ℕ → Submodule S B} [GradedAlgebra ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
  (φ : ∀ j, 𝒜 j →ₗ[R] ℬ j) (hφ : ∀ j x, (φ j x : B) = f x)

include hφ in
/-- Over `D₊(f a) = (Proj.map f)⁻¹ D₊(a)`, for `a` homogeneous of positive degree, the comparison
of twisting sheaves along a degreewise base change is bijective on sections. -/
theorem bijective_pullbackTwistingSheafMap_app_basicOpen (hbc : ∀ j, IsBaseChange S (φ j))
    {a : A} {d : ℕ} (ha : a ∈ 𝒜 d) (hd : 0 < d) (n : ℤ) :
    Function.Bijective ((pullbackTwistingSheafMap f hf n).app (basicOpen ℬ (f a))) := by
  have hV : basicOpen ℬ (f a) ≤ map f hf ⁻¹ᵁ basicOpen 𝒜 a := (map_preimage_basicOpen f hf a).ge
  let := ((map f hf).appLE _ _ hV).hom.toAlgebra
  let : Module Γ(Proj 𝒜, basicOpen 𝒜 a)
      Γ((Scheme.Modules.pullback (map f hf)).obj (twistingSheaf 𝒜 n), basicOpen ℬ (f a)) :=
    Module.compHom _ (algebraMap Γ(Proj 𝒜, basicOpen 𝒜 a) Γ(Proj ℬ, basicOpen ℬ (f a)))
  have : IsScalarTower Γ(Proj 𝒜, basicOpen 𝒜 a) Γ(Proj ℬ, basicOpen ℬ (f a))
      Γ((Scheme.Modules.pullback (map f hf)).obj (twistingSheaf 𝒜 n), basicOpen ℬ (f a)) :=
    IsScalarTower.of_compHom _ _ _
  let : Module Γ(Proj 𝒜, basicOpen 𝒜 a) Γ(twistingSheaf ℬ n, basicOpen ℬ (f a)) :=
    Module.compHom _ (algebraMap Γ(Proj 𝒜, basicOpen 𝒜 a) Γ(Proj ℬ, basicOpen ℬ (f a)))
  have : IsScalarTower Γ(Proj 𝒜, basicOpen 𝒜 a) Γ(Proj ℬ, basicOpen ℬ (f a))
      Γ(twistingSheaf ℬ n, basicOpen ℬ (f a)) :=
    IsScalarTower.of_compHom _ _ _
  let p : Γ(twistingSheaf 𝒜 n, basicOpen 𝒜 a) →ₗ[Γ(Proj 𝒜, basicOpen 𝒜 a)]
      Γ((Scheme.Modules.pullback (map f hf)).obj (twistingSheaf 𝒜 n), basicOpen ℬ (f a)) :=
    { toFun := (map f hf).pullbackSectionsLE _ _ _ hV
      map_add' := map_add _
      map_smul' r s := ((map f hf).pullbackSectionsLE _ _ _ hV).map_smulₛₗ r s }
  let q : Γ(twistingSheaf 𝒜 n, basicOpen 𝒜 a) →ₗ[Γ(Proj 𝒜, basicOpen 𝒜 a)]
      Γ(twistingSheaf ℬ n, basicOpen ℬ (f a)) :=
    { toFun := twistingSheaf.comap f hf (fun _ hy ↦ hV hy)
      map_add' := map_add _
      map_smul' r s := twistingSheaf.comap_smul f hf _ r s }
  have hp := (map f hf).isBaseChange_pullbackSectionsLE (twistingSheaf 𝒜 n) hV
    (isAffineOpen_basicOpen 𝒜 a ha hd)
    (isAffineOpen_basicOpen ℬ (f a) (Graded.map_mem f ha) hd) p fun _ ↦ rfl
  have hq := twistingSheaf.isBaseChange_comap_basicOpen f hf φ hφ ha hd n (fun _ ↦ rfl) q
    (fun _ ↦ rfl) hbc
  exact bijective_of_isBaseChange hp hq
    { toFun := (pullbackTwistingSheafMap f hf n).app _
      map_add' := map_add _
      map_smul' := (pullbackTwistingSheafMap f hf n).app_smul }
    fun s ↦ pullbackTwistingSheafMap_app_pullbackSectionsLE f hf n _ _ hV s

include hφ in
/-- If the graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` exhibits each `ℬⱼ` as the base change
`S ⊗[R] 𝒜ⱼ` (through its components `φ j`), then the comparison `(Proj.map f)^* 𝒪(n) ⟶ 𝒪(n)` is an
isomorphism for every `n ∈ ℤ`. -/
theorem isIso_pullbackTwistingSheafMap_of_forall_isBaseChange (hbc : ∀ j, IsBaseChange S (φ j))
    (n : ℤ) : IsIso (pullbackTwistingSheafMap f hf n) := by
  refine (pullbackTwistingSheafMap f hf n).isIso_of_bijective_app
    (ι := {p : A × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}) (U := fun p ↦ basicOpen ℬ (f p.1.1))
    (fun p ↦ isAffineOpen_basicOpen ℬ _ (Graded.map_mem f p.2.2) p.2.1) ?_
    fun p ↦ bijective_pullbackTwistingSheafMap_app_basicOpen f hf φ hφ hbc p.2.2 p.2.1 n
  refine eq_top_iff.2 fun y _ ↦ ?_
  obtain ⟨i, hi, a, ha, hay⟩ :=
    ProjectiveSpectrum.exists_le_mem_notMem (𝒜 := 𝒜) (ProjectiveSpectrum.comap f hf y) 1
  refine Opens.mem_iSup.2 ⟨⟨(a, i), by omega, ha⟩, ?_⟩
  rw [← map_preimage_basicOpen f hf a]
  exact hay

section IsBaseChange

variable (hfR : ∀ r : R, f (algebraMap R A r) = algebraMap R B r)

include hfR in
/-- The component `𝒜ⱼ → ℬⱼ` of a graded ring homomorphism over `R → S`, as an `R`-linear map. -/
private def componentLinearMap (j : ℕ) : 𝒜 j →ₗ[R] ℬ j where
  toFun x := ⟨f x, Graded.map_mem f x.2⟩
  map_add' x y := Subtype.ext (map_add f _ _)
  map_smul' r x := Subtype.ext (by
    change f (r • (x : A)) = r • f x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hfR])

/-- If `f` exhibits `B` as the base change `S ⊗[R] A`, it does so in every degree. -/
private theorem isBaseChange_componentLinearMap
    (hf : IsBaseChange S (AlgHom.mk f.toRingHom hfR).toLinearMap) (j : ℕ) :
    IsBaseChange S (componentLinearMap f hfR j) := by
  rw [IsBaseChange.iff_liftBaseChange_bijective]
  -- in `B`, the comparison is `S ⊗[R] 𝒜ⱼ ≃ (𝒜ⱼ).baseChange S` followed by `S ⊗[R] A ≃ B`
  have e (t : S ⊗[R] 𝒜 j) : (((componentLinearMap f hfR j).liftBaseChange S t : ℬ j) : B) =
      TauCeti.GradedAlgebra.baseChangeLift 𝒜 f hfR ((𝒜 j).toBaseChange S t : S ⊗[R] A) := by
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => simp only [map_add, Submodule.coe_add, ht, ht']
    | tmul s x =>
      simp only [LinearMap.liftBaseChange_tmul, Submodule.coe_toBaseChange_tmul,
        TauCeti.GradedAlgebra.baseChangeLift_tmul]
      rfl
  refine ⟨fun t t' h ↦ DirectSum.toBaseChange_injective 𝒜 j (Subtype.ext
    ((TauCeti.GradedAlgebra.bijective_baseChangeLift hf).injective ?_)), fun b ↦ ?_⟩
  · rw [← e, ← e, h]
  · obtain ⟨t, ht⟩ := (𝒜 j).toBaseChange_surjective S
      ⟨_, (TauCeti.GradedAlgebra.baseChangeLiftInv 𝒜 f hfR hf).map_mem b.2⟩
    refine ⟨t, Subtype.ext ((e t).trans ?_)⟩
    rw [ht]
    exact TauCeti.GradedAlgebra.baseChangeLift_baseChangeLiftInv 𝒜 f hfR hf b

/-- **Twisting sheaves pull back along a base change of graded rings.** If a graded ring
homomorphism `f : 𝒜 →+*ᵍ ℬ` over the coefficient extension `R → S` exhibits `B` as the base change
`S ⊗[R] A`, then the comparison `(Proj.map f)^* 𝒪(n) ⟶ 𝒪(n)` is an isomorphism for every `n ∈ ℤ`.
This is the companion of `AlgebraicGeometry.Proj.isPullback_map_of_isBaseChange` for the twisting
sheaves. -/
theorem isIso_pullbackTwistingSheafMap_of_isBaseChange
    (hf' : IsBaseChange S (AlgHom.mk f.toRingHom hfR).toLinearMap) (n : ℤ) :
    IsIso (pullbackTwistingSheafMap f hf n) :=
  isIso_pullbackTwistingSheafMap_of_forall_isBaseChange f hf (componentLinearMap f hfR)
    (fun _ _ ↦ rfl) (isBaseChange_componentLinearMap f hfR hf') n

end IsBaseChange

end AlgebraicGeometry.Proj
