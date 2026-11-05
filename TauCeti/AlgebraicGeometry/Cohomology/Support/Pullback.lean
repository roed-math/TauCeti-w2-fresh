/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Support
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.Modules.Pullback.ToSheaf
public import TauCeti.Topology.Sheaves.SupportedCohomology.Pullback

/-!
# Pullback of cohomology with supports of sheaves of modules

Let `g : Y ⟶ X` be a morphism of schemes, `Z ⊆ X` a closed subset and `M` a sheaf of modules on
`X`. This file constructs the pullback map

`g.cohomologyWithSupportPullback Z M q : H_Z^q(X, M) →+ H_{g⁻¹ Z}^q(Y, g^* M)`

(the README's `cohomologyWithSupport_pullback`). It is the inverse image map on cohomology with
supports of the underlying abelian sheaves (`TopCat.Hom.supportedHPullback`), followed by the map
induced by the comparison `g⁻¹ M ⟶ g^* M`
(`AlgebraicGeometry.Scheme.Hom.toSheafPullbackComparison`), exactly as
`AlgebraicGeometry.Scheme.Hom.cohomologyPullback` is built for ordinary cohomology.

The pullback map is natural in `M`, compatible with connecting maps, semilinear for the action of
global functions along `g^♯ : Γ(X, 𝒪_X) ⟶ Γ(Y, 𝒪_Y)`, and in degree zero it is the pullback of
global sections supported in `Z`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.cohomologyWithSupportPullback`: the map
  `H_Z^q(X, M) →+ H_{g⁻¹ Z}^q(Y, g^* M)`;
* `AlgebraicGeometry.Scheme.Hom.cohomologyWithSupportPullback_cohomologyWithSupportMap`:
  naturality in `M`;
* `AlgebraicGeometry.Scheme.Hom.cohomologyWithSupportPullback_cohomologyWithSupportδ`:
  compatibility with connecting maps;
* `AlgebraicGeometry.Scheme.Hom.cohomologyWithSupportPullback_smul`: semilinearity over global
  functions;
* `Scheme.Hom.coe_cohomologyWithSupportZeroLinearEquiv_cohomologyWithSupportPullback`: the
  degree-zero case.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite Abelian
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (Z : Closeds X)

/-- The pullback map `H_Z^q(X, M) →+ H_{g⁻¹ Z}^q(Y, g^* M)` on cohomology with supports of a sheaf
of modules along a morphism of schemes `g : Y ⟶ X`. -/
def cohomologyWithSupportPullback (M : X.Modules) (q : ℕ) :
    cohomologyWithSupport Z M q →+
      cohomologyWithSupport (Z.preimage g.base.hom.continuous) ((Scheme.Modules.pullback g).obj M)
        q :=
  ((Ext.mk₀ ((toSheafPullbackComparison g).app M)).postcomp _ (add_zero q)).comp
    (g.base.supportedHPullback ((toSheaf X).obj M) Z ⊤ q)

private lemma cohomologyWithSupportPullback_apply (M : X.Modules) (q : ℕ)
    (x : cohomologyWithSupport Z M q) :
    g.cohomologyWithSupportPullback Z M q x =
      (g.base.supportedHPullback ((toSheaf X).obj M) Z ⊤ q x).comp
        (Ext.mk₀ ((toSheafPullbackComparison g).app M)) (add_zero q) :=
  (rfl)

/-- The pullback map on cohomology with supports is natural in the coefficient sheaf. -/
theorem cohomologyWithSupportPullback_cohomologyWithSupportMap {M N : X.Modules} (α : M ⟶ N)
    (q : ℕ) (x : cohomologyWithSupport Z M q) :
    g.cohomologyWithSupportPullback Z N q (cohomologyWithSupportMap Z α q x) =
      cohomologyWithSupportMap _ ((Scheme.Modules.pullback g).map α) q
        (g.cohomologyWithSupportPullback Z M q x) := by
  refine (congrArg (g.cohomologyWithSupportPullback Z N q)
    (cohomologyWithSupportMap_apply Z α q x)).trans
      (Eq.trans ?_ (cohomologyWithSupportMap_apply _ _ q _).symm)
  -- restate `x` with its type in terms of `toSheaf X`, so that rewriting is type-correct
  obtain ⟨y, rfl⟩ : ∃ y : ((toSheaf X).obj M).supportedH Z ⊤ q, y = x := ⟨x, rfl⟩
  change (g.base.supportedHPullback ((toSheaf X).obj N) Z ⊤ q
      (y.comp (Ext.mk₀ ((toSheaf X).map α)) (add_zero q))).comp
        (Ext.mk₀ ((toSheafPullbackComparison g).app N)) (add_zero q) =
    ((g.base.supportedHPullback ((toSheaf X).obj M) Z ⊤ q y).comp
      (Ext.mk₀ ((toSheafPullbackComparison g).app M)) (add_zero q)).comp
        (Ext.mk₀ ((toSheaf Y).map ((Scheme.Modules.pullback g).map α))) (add_zero q)
  rw [TopCat.Hom.supportedHPullback_naturality, Ext.comp_assoc_of_third_deg_zero,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
  exact congrArg (fun φ ↦ Ext.comp _ (Ext.mk₀ φ) (add_zero q))
    ((toSheafPullbackComparison g).naturality α)

/-- The pullback map on cohomology with supports commutes with the connecting maps of a short exact
sequence `S` of sheaves of modules on `X` whose pullback to `Y` is short exact, for instance when
`g` is flat and the first two terms of `S` are quasi-coherent
(`AlgebraicGeometry.Scheme.Hom.shortExact_map_pullback_of_flat`). -/
theorem cohomologyWithSupportPullback_cohomologyWithSupportδ {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (hS' : (S.map (Scheme.Modules.pullback g)).ShortExact) {n₀ n₁ : ℕ}
    (h : n₀ + 1 = n₁) (x : cohomologyWithSupport Z S.X₃ n₀) :
    g.cohomologyWithSupportPullback Z S.X₁ n₁ (cohomologyWithSupportδ Z hS n₀ n₁ h x) =
      cohomologyWithSupportδ _ hS' n₀ n₁ h (g.cohomologyWithSupportPullback Z S.X₃ n₀ x) := by
  let φ := toSheafPullbackComparison g
  -- The comparison, as a morphism from the inverse image of the underlying short exact sequence
  -- of abelian sheaves to the underlying short exact sequence of the pullback.
  let ψ : ((S.map (toSheaf X)).map ((Opens.map g.base).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y))) ⟶
      (S.map (Scheme.Modules.pullback g)).map (toSheaf Y) :=
    { τ₁ := φ.app S.X₁
      τ₂ := φ.app S.X₂
      τ₃ := φ.app S.X₃
      comm₁₂ := (φ.naturality S.f).symm
      comm₂₃ := (φ.naturality S.g).symm }
  let pb := (Opens.map g.base).sheafPullback AddCommGrpCat.{u} (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y)
  have h₀ := g.base.supportedHPullback_comp_extClass (shortExact_map_toSheaf hS) Z ⊤ h x
  have key := ((shortExact_map_toSheaf hS).map_of_exact pb).extClass_naturality
    (shortExact_map_toSheaf hS') ψ
  have e₁ := Ext.comp_assoc_of_third_deg_zero (g.base.supportedHPullback _ Z ⊤ n₀ x)
    ((shortExact_map_toSheaf hS).map_of_exact pb).extClass (Ext.mk₀ (φ.app S.X₁)) h
  have e₂ := Ext.comp_assoc_of_second_deg_zero (g.base.supportedHPullback _ Z ⊤ n₀ x)
    (Ext.mk₀ (φ.app S.X₃)) (shortExact_map_toSheaf hS').extClass h
  exact (congrArg (g.cohomologyWithSupportPullback Z S.X₁ n₁)
    (cohomologyWithSupportδ_apply Z hS n₀ n₁ h x)).trans <|
    (cohomologyWithSupportPullback_apply g Z S.X₁ n₁ _).trans <|
    (congrArg (fun z ↦ Ext.comp z (Ext.mk₀ (φ.app S.X₁)) (add_zero n₁)) h₀).trans <|
    e₁.trans <|
    (congrArg (fun e ↦ (g.base.supportedHPullback _ Z ⊤ n₀ x).comp e h) key).trans <|
    e₂.symm.trans <|
    (congrArg (fun z ↦ Ext.comp z (shortExact_map_toSheaf hS').extClass h)
      (cohomologyWithSupportPullback_apply g Z S.X₃ n₀ x)).symm.trans
    (cohomologyWithSupportδ_apply _ hS' n₀ n₁ h _).symm

/-- The pullback map on cohomology with supports is semilinear for the action of global functions
along `g^♯ : Γ(X, 𝒪_X) ⟶ Γ(Y, 𝒪_Y)`. -/
theorem cohomologyWithSupportPullback_smul (M : X.Modules) (q : ℕ) (r : Γ(X, ⊤))
    (x : cohomologyWithSupport Z M q) :
    g.cohomologyWithSupportPullback Z M q (r • x) =
      g.appTop r • g.cohomologyWithSupportPullback Z M q x := by
  rw [smul_cohomologyWithSupport, smul_cohomologyWithSupport,
    cohomologyWithSupportPullback_cohomologyWithSupportMap,
    Scheme.Modules.pullback_map_globalSectionsSmul]

/-- In degree zero, under the identification of `H_Z⁰` with global sections supported in `Z`, the
pullback map on cohomology with supports is the pullback of global sections. -/
theorem coe_cohomologyWithSupportZeroLinearEquiv_cohomologyWithSupportPullback (M : X.Modules)
    (x : cohomologyWithSupport Z M 0) :
    (cohomologyWithSupportZeroLinearEquiv _ _ (g.cohomologyWithSupportPullback Z M 0 x)).1 =
      g.pullbackSections M ⊤ (cohomologyWithSupportZeroLinearEquiv Z M x).1 := by
  refine (coe_cohomologyWithSupportZeroLinearEquiv_apply _ _ _).trans ?_
  refine (CategoryTheory.Sheaf.coe_supportedHZeroEquiv_apply _ _ _ _).trans ?_
  refine (CategoryTheory.Sheaf.relativeH'.coe_zeroEquiv_naturality_right _ _
    (g.base.supportedHPullback ((toSheaf X).obj M) Z ⊤ 0 x)).trans ?_
  refine (congrArg _ (CategoryTheory.Sheaf.coe_supportedHZeroEquiv_apply _ _ _ _).symm).trans ?_
  refine (congrArg _
    (g.base.coe_supportedHZeroEquiv_supportedHPullback ((toSheaf X).obj M) Z ⊤ x)).trans ?_
  rw [coe_cohomologyWithSupportZeroLinearEquiv_apply]
  refine Eq.trans ?_ (g.pullbackSections_apply M ⊤ _).symm
  exact (congrArg (fun φ ↦ φ.hom.app (op ⊤) (((toSheaf X).obj M).supportedHZeroEquiv Z ⊤ x).1)
    (toSheafPullbackComparison_unit g M)).symm

end AlgebraicGeometry.Scheme.Hom
