/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BoundedHolomorphic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection
import TauCeti.Analysis.Fredholm.SurjectiveCompactPerturbation
import TauCeti.Analysis.Normed.Operator.Compact.Pi

/-!
# Bounded holomorphic Čech cochains

For a family `U : ι → Opens X` of open subsets of a complex manifold, this file sets up the
Čech complex of bounded holomorphic functions in degrees `0`, `1` and `2`. The cochains live in
the products of bounded continuous functions
`BoundedCochain₀ U = Π i, (Uᵢ →ᵇ ℂ)`, `BoundedCochain₁ U = Π i j, (Uᵢ ∩ Uⱼ →ᵇ ℂ)` and
`BoundedCochain₂ U = Π i j k, (Uᵢ ∩ Uⱼ ∩ Uₖ →ᵇ ℂ)`, with the Čech coboundaries `d₀` and `d₁`
as continuous linear maps. The holomorphic cochains `cochains₀ I U` and `cochains₁ I U` and the
holomorphic `1`-cocycles `cocycles I U` are closed subspaces; when `ι` is finite they are Banach
spaces under the supremum norm, with the coboundary `d₀Cocycles I U` between them.

A second family `V` with `Vᵢ ≤ Uᵢ` for all `i` gives restriction maps commuting with the
coboundaries, and hence a restriction `restrictCocycles` of cocycles. If `V` is a finite family
relatively compact in `U` (each closure `closure Vᵢ` compact and contained in `Uᵢ`), restriction
of cocycles is a compact operator
(`TauCeti.BoundedCech.isCompactOperator_restrictCocycles`), by Montel's theorem
`TauCeti.BoundedHolomorphicSections.isCompactOperator_restrict` on each double intersection.

Together with the Schwartz theorem
`ContinuousLinearMap.finiteDimensional_quotient_range_of_surjective_coprod` this gives
`TauCeti.BoundedCech.exists_finiteDimensional_isCompl_range_d₀Cocycles`, the functional-analytic
step of Forster's proof that `H¹` of the structure sheaf of a compact Riemann surface is finite
dimensional: if every bounded holomorphic cocycle on `V` is cohomologous to the restriction of
one on `U`, then the bounded holomorphic coboundaries on `V` have a finite-dimensional
complement in the bounded holomorphic cocycles.

## Implementation notes

The holomorphic cochains are subspaces of products of bounded continuous functions, rather than
products of the spaces `TauCeti.boundedHolomorphicSections`: subspaces of subspaces of products
of complex subspaces defeat instance synthesis for their additive groups, which the
finite-dimensional complement in the main theorem needs.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer,
  1981, §14 (14.3–14.9, there with `L²` rather than supremum norms).
-/

public section

namespace TauCeti.BoundedCech

open Set TopologicalSpace BoundedContinuousFunction BoundedHolomorphicSections
open ContinuousLinearMap (pi proj)
open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {ι : Type*}

/-- Restriction of bounded continuous functions to a smaller open set. -/
noncomputable def restrictBCF {W W' : Opens X} (h : W' ≤ W) : (W →ᵇ ℂ) →L[ℂ] (W' →ᵇ ℂ) :=
  compContinuousCLM ℂ ℂ ⟨Set.inclusion h, continuous_inclusion h⟩

@[simp]
theorem restrictBCF_apply {W W' : Opens X} (h : W' ≤ W) (f : W →ᵇ ℂ) (z : W') :
    restrictBCF h f z = f ⟨z, h z.2⟩ := (rfl)

/-- Restriction of bounded continuous functions preserves holomorphy. -/
theorem restrictBCF_mem {W W' : Opens X} (h : W' ≤ W) {f : W →ᵇ ℂ}
    (hf : f ∈ boundedHolomorphicSections I ℂ W) :
    restrictBCF h f ∈ boundedHolomorphicSections I ℂ W' := by
  convert (restrict (I := I) (F := ℂ) h ⟨f, hf⟩).2 using 1
  ext z
  simp

/-- Bounded continuous Čech `0`-cochains of a family of open sets `U`. -/
abbrev BoundedCochain₀ (U : ι → Opens X) : Type _ := ∀ i, U i →ᵇ ℂ

/-- Bounded continuous Čech `1`-cochains of a family of open sets `U`. -/
abbrev BoundedCochain₁ (U : ι → Opens X) : Type _ := ∀ i j, ↥(U i ⊓ U j) →ᵇ ℂ

/-- Bounded continuous Čech `2`-cochains of a family of open sets `U`. -/
abbrev BoundedCochain₂ (U : ι → Opens X) : Type _ := ∀ i j k, ↥(U i ⊓ U j ⊓ U k) →ᵇ ℂ

variable {U V : ι → Opens X}

variable (U) in
/-- The Čech coboundary of `0`-cochains, `(d₀ f)ᵢⱼ = fⱼ - fᵢ` on `Uᵢ ∩ Uⱼ`. -/
noncomputable def d₀ : BoundedCochain₀ U →L[ℂ] BoundedCochain₁ U :=
  pi fun i => pi fun j =>
    (restrictBCF (inf_le_right : U i ⊓ U j ≤ U j)).comp (proj j) -
      (restrictBCF (inf_le_left : U i ⊓ U j ≤ U i)).comp (proj i)

@[simp]
theorem d₀_apply (f : BoundedCochain₀ U) (i j : ι) :
    d₀ U f i j = restrictBCF inf_le_right (f j) - restrictBCF inf_le_left (f i) := (rfl)

variable (U) in
/-- The Čech coboundary of `1`-cochains, `(d₁ ξ)ᵢⱼₖ = ξⱼₖ - ξᵢₖ + ξᵢⱼ` on `Uᵢ ∩ Uⱼ ∩ Uₖ`. -/
noncomputable def d₁ : BoundedCochain₁ U →L[ℂ] BoundedCochain₂ U :=
  pi fun i => pi fun j => pi fun k =>
    (restrictBCF (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        U i ⊓ U j ⊓ U k ≤ U j ⊓ U k)).comp
        ((proj k).comp (proj j) : BoundedCochain₁ U →L[ℂ] _) -
      (restrictBCF (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        U i ⊓ U j ⊓ U k ≤ U i ⊓ U k)).comp
        ((proj k).comp (proj i) : BoundedCochain₁ U →L[ℂ] _) +
      (restrictBCF (inf_le_left : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j)).comp
        ((proj j).comp (proj i) : BoundedCochain₁ U →L[ℂ] _)

@[simp]
theorem d₁_apply (ξ : BoundedCochain₁ U) (i j k : ι) :
    d₁ U ξ i j k =
      restrictBCF (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (ξ j k) -
        restrictBCF (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (ξ i k) +
        restrictBCF inf_le_left (ξ i j) := (rfl)

/-- The Čech coboundaries compose to zero. -/
@[simp]
theorem d₁_comp_d₀ : (d₁ U).comp (d₀ U) = 0 :=
  ContinuousLinearMap.ext fun f => funext fun i => funext fun j => funext fun k =>
    BoundedContinuousFunction.ext fun z => by simp

variable (I U) in
/-- The bounded holomorphic `0`-cochains: a bounded holomorphic function on each `Uᵢ`. -/
noncomputable def cochains₀ : Submodule ℂ (BoundedCochain₀ U) :=
  Submodule.pi univ fun i => boundedHolomorphicSections I ℂ (U i)

theorem mem_cochains₀_iff {f : BoundedCochain₀ U} :
    f ∈ cochains₀ I U ↔ ∀ i, f i ∈ boundedHolomorphicSections I ℂ (U i) := by
  simp [cochains₀]

variable (I U) in
/-- The bounded holomorphic `1`-cochains: a bounded holomorphic function on each `Uᵢ ∩ Uⱼ`. -/
noncomputable def cochains₁ : Submodule ℂ (BoundedCochain₁ U) :=
  Submodule.pi univ fun i => Submodule.pi univ fun j =>
    boundedHolomorphicSections I ℂ (U i ⊓ U j)

theorem mem_cochains₁_iff {ξ : BoundedCochain₁ U} :
    ξ ∈ cochains₁ I U ↔ ∀ i j, ξ i j ∈ boundedHolomorphicSections I ℂ (U i ⊓ U j) := by
  simp [cochains₁]

variable (I U) in
/-- The bounded holomorphic Čech `1`-cocycles: holomorphic `1`-cochains in the kernel of `d₁`. -/
noncomputable def cocycles : Submodule ℂ (BoundedCochain₁ U) :=
  cochains₁ I U ⊓ (d₁ U : BoundedCochain₁ U →ₗ[ℂ] BoundedCochain₂ U).ker

theorem mem_cocycles_iff {ξ : BoundedCochain₁ U} :
    ξ ∈ cocycles I U ↔ ξ ∈ cochains₁ I U ∧ d₁ U ξ = 0 :=
  Iff.rfl

/-- The coboundary of a holomorphic `0`-cochain is a holomorphic cocycle. -/
theorem d₀_mem_cocycles {f : BoundedCochain₀ U} (hf : f ∈ cochains₀ I U) :
    d₀ U f ∈ cocycles I U := by
  refine mem_cocycles_iff.mpr ⟨mem_cochains₁_iff.mpr fun i j => ?_, ?_⟩
  · rw [mem_cochains₀_iff] at hf
    exact Submodule.sub_mem _ (restrictBCF_mem _ (hf j)) (restrictBCF_mem _ (hf i))
  · rw [← ContinuousLinearMap.comp_apply, d₁_comp_d₀]
    rfl

variable (I U) in
/-- The Čech coboundary of holomorphic `0`-cochains, as a map to the holomorphic cocycles. -/
noncomputable def d₀Cocycles : cochains₀ I U →L[ℂ] cocycles I U :=
  ((d₀ U).comp (cochains₀ I U).subtypeL).codRestrict _ fun f => d₀_mem_cocycles f.2

@[simp]
theorem coe_d₀Cocycles_apply (f : cochains₀ I U) :
    (d₀Cocycles I U f : BoundedCochain₁ U) = d₀ U f := (rfl)

/-- Restriction of `0`-cochains along `Vᵢ ≤ Uᵢ`. -/
noncomputable def restrict₀ (h : ∀ i, V i ≤ U i) : BoundedCochain₀ U →L[ℂ] BoundedCochain₀ V :=
  pi fun i => (restrictBCF (h i)).comp (proj i)

@[simp]
theorem restrict₀_apply (h : ∀ i, V i ≤ U i) (f : BoundedCochain₀ U) (i : ι) :
    restrict₀ h f i = restrictBCF (h i) (f i) := (rfl)

/-- Restriction of `1`-cochains along `Vᵢ ≤ Uᵢ`. -/
noncomputable def restrict₁ (h : ∀ i, V i ≤ U i) : BoundedCochain₁ U →L[ℂ] BoundedCochain₁ V :=
  pi fun i => pi fun j =>
    (restrictBCF (inf_le_inf (h i) (h j))).comp
      ((proj j).comp (proj i) : BoundedCochain₁ U →L[ℂ] _)

@[simp]
theorem restrict₁_apply (h : ∀ i, V i ≤ U i) (ξ : BoundedCochain₁ U) (i j : ι) :
    restrict₁ h ξ i j = restrictBCF (inf_le_inf (h i) (h j)) (ξ i j) := (rfl)

/-- Restriction of `2`-cochains along `Vᵢ ≤ Uᵢ`. -/
noncomputable def restrict₂ (h : ∀ i, V i ≤ U i) : BoundedCochain₂ U →L[ℂ] BoundedCochain₂ V :=
  pi fun i => pi fun j => pi fun k =>
    (restrictBCF (inf_le_inf (inf_le_inf (h i) (h j)) (h k))).comp
      ((proj k).comp ((proj j).comp (proj i) : BoundedCochain₂ U →L[ℂ] _) :
        BoundedCochain₂ U →L[ℂ] _)

@[simp]
theorem restrict₂_apply (h : ∀ i, V i ≤ U i) (ζ : BoundedCochain₂ U) (i j k : ι) :
    restrict₂ h ζ i j k = restrictBCF (inf_le_inf (inf_le_inf (h i) (h j)) (h k)) (ζ i j k) :=
  (rfl)

/-- Restriction commutes with the coboundary of `0`-cochains. -/
theorem restrict₁_comp_d₀ (h : ∀ i, V i ≤ U i) :
    (restrict₁ h).comp (d₀ U) = (d₀ V).comp (restrict₀ h) :=
  ContinuousLinearMap.ext fun f => funext fun i => funext fun j =>
    BoundedContinuousFunction.ext fun z => by simp

/-- Restriction commutes with the coboundary of `1`-cochains. -/
theorem restrict₂_comp_d₁ (h : ∀ i, V i ≤ U i) :
    (restrict₂ h).comp (d₁ U) = (d₁ V).comp (restrict₁ h) :=
  ContinuousLinearMap.ext fun ξ => funext fun i => funext fun j => funext fun k =>
    BoundedContinuousFunction.ext fun z => by simp

/-- Restriction maps holomorphic `0`-cochains to holomorphic `0`-cochains. -/
theorem restrict₀_mem_cochains₀ (h : ∀ i, V i ≤ U i) {f : BoundedCochain₀ U}
    (hf : f ∈ cochains₀ I U) : restrict₀ h f ∈ cochains₀ I V :=
  mem_cochains₀_iff.mpr fun i => restrictBCF_mem _ (mem_cochains₀_iff.mp hf i)

/-- Restriction maps holomorphic cocycles to holomorphic cocycles. -/
theorem restrict₁_mem_cocycles (h : ∀ i, V i ≤ U i) {ξ : BoundedCochain₁ U}
    (hξ : ξ ∈ cocycles I U) : restrict₁ h ξ ∈ cocycles I V := by
  obtain ⟨hhol, hker⟩ := mem_cocycles_iff.mp hξ
  refine mem_cocycles_iff.mpr
    ⟨mem_cochains₁_iff.mpr fun i j => restrictBCF_mem _ (mem_cochains₁_iff.mp hhol i j), ?_⟩
  rw [← ContinuousLinearMap.comp_apply, ← restrict₂_comp_d₁, ContinuousLinearMap.comp_apply, hker,
    map_zero]

/-- Restriction of holomorphic `0`-cochains along `Vᵢ ≤ Uᵢ`. -/
noncomputable def restrictCochains₀ (h : ∀ i, V i ≤ U i) : cochains₀ I U →L[ℂ] cochains₀ I V :=
  ((restrict₀ h).comp (cochains₀ I U).subtypeL).codRestrict _ fun f =>
    restrict₀_mem_cochains₀ h f.2

@[simp]
theorem coe_restrictCochains₀_apply (h : ∀ i, V i ≤ U i) (f : cochains₀ I U) :
    (restrictCochains₀ h f : BoundedCochain₀ V) = restrict₀ h f := (rfl)

/-- Restriction of holomorphic cocycles along `Vᵢ ≤ Uᵢ`. -/
noncomputable def restrictCocycles (h : ∀ i, V i ≤ U i) : cocycles I U →L[ℂ] cocycles I V :=
  ((restrict₁ h).comp (cocycles I U).subtypeL).codRestrict _ fun ξ =>
    restrict₁_mem_cocycles h ξ.2

@[simp]
theorem coe_restrictCocycles_apply (h : ∀ i, V i ≤ U i) (ξ : cocycles I U) :
    (restrictCocycles h ξ : BoundedCochain₁ V) = restrict₁ h ξ := (rfl)

/-- Restriction of holomorphic cocycles commutes with the coboundary. -/
theorem restrictCocycles_comp_d₀Cocycles (h : ∀ i, V i ≤ U i) :
    (restrictCocycles h).comp (d₀Cocycles I U) = (d₀Cocycles I V).comp (restrictCochains₀ h) :=
  ContinuousLinearMap.ext fun f => Subtype.ext <| by
    simpa using congr($(restrict₁_comp_d₀ (U := U) h) f)

section Complete

variable [IsManifold I 1 X] [I.Boundaryless]

/-- The holomorphic `0`-cochains form a closed subspace. -/
theorem isClosed_cochains₀ : IsClosed (cochains₀ I U : Set (BoundedCochain₀ U)) := by
  simpa [cochains₀] using isClosed_set_pi fun i _ => isClosed_boundedHolomorphicSections (U i)

/-- The holomorphic `1`-cochains form a closed subspace. -/
theorem isClosed_cochains₁ : IsClosed (cochains₁ I U : Set (BoundedCochain₁ U)) := by
  simpa [cochains₁] using isClosed_set_pi fun i _ => isClosed_set_pi fun j _ =>
    isClosed_boundedHolomorphicSections (U i ⊓ U j)

/-- The holomorphic cocycles form a closed subspace. -/
theorem isClosed_cocycles : IsClosed (cocycles I U : Set (BoundedCochain₁ U)) :=
  isClosed_cochains₁.inter (d₁ U).isClosed_ker

instance : CompleteSpace (cochains₀ I U) :=
  isClosed_cochains₀.completeSpace_coe

instance : CompleteSpace (cocycles I U) :=
  isClosed_cocycles.completeSpace_coe

/-- **Montel's theorem for cocycles.** If `V` is a finite family and each `Vᵢ` has compact
closure contained in `Uᵢ`, restriction of holomorphic cocycles is a compact operator. -/
theorem isCompactOperator_restrictCocycles [Finite ι]
    (hV : ∀ i, IsCompact (closure (V i : Set X))) (hVU : ∀ i, closure (V i : Set X) ⊆ U i) :
    IsCompactOperator (restrictCocycles (I := I)
      fun i => SetLike.coe_subset_coe.mp (subset_closure.trans (hVU i))) := by
  refine IsCompactOperator.codRestrict ?_ _ isClosed_cocycles
  -- Each component factors through Montel's restriction `H^∞(Uᵢ ∩ Uⱼ) → H^∞(Vᵢ ∩ Vⱼ)`; the
  -- closure of `Vᵢ ∩ Vⱼ` is a closed subset of the compact set `closure Vᵢ`, and lies in
  -- `Uᵢ ∩ Uⱼ`.
  refine IsCompactOperator.pi fun i => IsCompactOperator.pi fun j => ?_
  have hsub : closure ((V i ⊓ V j : Opens X) : Set X) ⊆ closure (V i) ∩ closure (V j) :=
    closure_inter_subset_inter_closure _ _
  have hres := isCompactOperator_restrict_of_isCompact_closure (I := I) (F := ℂ)
    (W := U i ⊓ U j) (W' := V i ⊓ V j)
    ((hV i).of_isClosed_subset isClosed_closure (hsub.trans inter_subset_left))
    (hsub.trans (inter_subset_inter (hVU i) (hVU j)))
  let ev : cocycles I U →L[ℂ] boundedHolomorphicSections I ℂ (U i ⊓ U j) :=
    (((proj j).comp (proj i) : BoundedCochain₁ U →L[ℂ] _).comp
      (cocycles I U).subtypeL).codRestrict _ fun ξ =>
        mem_cochains₁_iff.mp (mem_cocycles_iff.mp ξ.2).1 i j
  convert (hres.comp_clm ev).clm_comp (boundedHolomorphicSections I ℂ (V i ⊓ V j)).subtypeL
    using 1
  ext ξ z
  -- After unfolding the restrictions, both sides evaluate `ξ i j`; `ev ξ` is `ξ i j` by
  -- definition of `ContinuousLinearMap.codRestrict`.
  simp [ev]
  rfl

/-- **Finiteness of bounded holomorphic `H¹`.** Let `V` be a finite family relatively compact in
`U`. If every bounded holomorphic cocycle on `V` is cohomologous to the restriction of one on
`U`, then the bounded holomorphic coboundaries on `V` have a finite-dimensional complement in
the bounded holomorphic cocycles. -/
theorem exists_finiteDimensional_isCompl_range_d₀Cocycles [Finite ι]
    (hV : ∀ i, IsCompact (closure (V i : Set X))) (hVU : ∀ i, closure (V i : Set X) ⊆ U i)
    (h : ∀ ξ : cocycles I V, ∃ ζ : cocycles I U, ∃ η : cochains₀ I V,
      restrictCocycles (fun i => SetLike.coe_subset_coe.mp (subset_closure.trans (hVU i))) ζ +
        d₀Cocycles I V η = ξ) :
    ∃ B : Submodule ℂ (cocycles I V), FiniteDimensional ℂ B ∧
      IsCompl (LinearMap.range (d₀Cocycles I V : cochains₀ I V →ₗ[ℂ] cocycles I V)) B := by
  have := Fintype.ofFinite ι
  have := ContinuousLinearMap.finiteDimensional_quotient_range_of_surjective_coprod
    (isCompactOperator_restrictCocycles hV hVU) fun ξ =>
      let ⟨ζ, η, hζη⟩ := h ξ
      ⟨(ζ, η), by rw [ContinuousLinearMap.coprod_apply]; exact hζη⟩
  obtain ⟨B, hB⟩ := Submodule.exists_isCompl (LinearMap.range (d₀Cocycles I V).toLinearMap)
  exact ⟨B, (Submodule.quotientEquivOfIsCompl _ B hB).finiteDimensional, hB⟩

end Complete

end TauCeti.BoundedCech
