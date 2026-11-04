/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Transposes along composite and isomorphic adjunctions

Two facts about the transpose `(adj.homEquiv _ _).symm` of a morphism `M ⟶ G P` along an
adjunction `adj : F ⊣ G`:

* along a composite adjunction `adj₁.comp adj₂`, the transpose of `θ ≫ G₁.map ψ` is the image under
  `F₂` of the transpose of `θ` followed by the transpose of `ψ`
  (`CategoryTheory.Adjunction.comp_homEquiv_symm_comp_map`);
* if the right adjoints of `adj₁ : F₁ ⊣ R₁` and `adj₂ : F₂ ⊣ R₂` are identified by `e : R₂ ≅ R₁`,
  then the transpose of `χ ≫ e.hom.app P` along `adj₁` is an isomorphism as soon as the transpose of
  `χ` along `adj₂` is one (`CategoryTheory.Adjunction.isIso_homEquiv_symm_comp_hom_app`).

Together they show that the transposes of a morphism along two factorizations of a pushforward
functor are isomorphisms simultaneously, as for the comparison maps of sheaves along a commutative
square of schemes.
-/

public section

namespace CategoryTheory.Adjunction

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- Along a composite adjunction, the transpose of `θ ≫ G.map ψ` is the image of the transpose of
`θ` followed by the transpose of `ψ`. -/
theorem comp_homEquiv_symm_comp_map {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
    (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) {M : C} {Q : D} {P : E} (θ : M ⟶ G.obj Q)
    (ψ : Q ⟶ I.obj P) :
    ((adj₁.comp adj₂).homEquiv _ _).symm (θ ≫ G.map ψ) =
      H.map ((adj₁.homEquiv _ _).symm θ) ≫ (adj₂.homEquiv _ _).symm ψ := by
  rw [comp_homEquiv, Equiv.symm_trans_apply, adj₁.homEquiv_naturality_right_symm,
    adj₂.homEquiv_naturality_left_symm]

/-- If the right adjoints of `adj₁ : F₁ ⊣ R₁` and `adj₂ : F₂ ⊣ R₂` are isomorphic through
`e : R₂ ≅ R₁`, the transpose of `χ ≫ e.hom.app P` along `adj₁` is an isomorphism when the transpose
of `χ` along `adj₂` is one: it is the latter preceded by the component of the comparison
`Adjunction.leftAdjointUniq` of the left adjoints. -/
theorem isIso_homEquiv_symm_comp_hom_app {F₁ F₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : F₁ ⊣ R₁)
    (adj₂ : F₂ ⊣ R₂) (e : R₂ ≅ R₁) {M : C} {P : D} (χ : M ⟶ R₂.obj P)
    [hχ : IsIso ((adj₂.homEquiv _ _).symm χ)] :
    IsIso ((adj₁.homEquiv _ _).symm (χ ≫ e.hom.app P)) := by
  have hχ : χ ≫ e.hom.app P = (adj₂.unit.app M ≫ e.hom.app _) ≫
      R₁.map ((adj₂.homEquiv _ _).symm χ) := by
    conv_lhs => rw [← (adj₂.homEquiv M P).apply_symm_apply χ, adj₂.homEquiv_unit]
    rw [Category.assoc, Category.assoc, e.hom.naturality]
  have hγ : (adj₁.homEquiv M (F₂.obj M)).symm (adj₂.unit.app M ≫ e.hom.app (F₂.obj M)) =
      (leftAdjointUniq adj₁ (adj₂.ofNatIsoRight e)).hom.app M := by
    rw [Equiv.symm_apply_eq, homEquiv_leftAdjointUniq_hom_app]
    simp [ofNatIsoRight]
  rw [hχ, adj₁.homEquiv_naturality_right_symm, hγ]
  infer_instance

end CategoryTheory.Adjunction
