/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Transposes along composite and isomorphic adjunctions

Facts about the transpose `(adj.homEquiv _ _).symm` of a morphism `M ⟶ G P` along an
adjunction `adj : F ⊣ G`:

* along a composite adjunction `adj₁.comp adj₂`, the transpose of `θ ≫ G₁.map ψ` is the image under
  `F₂` of the transpose of `θ` followed by the transpose of `ψ`
  (`CategoryTheory.Adjunction.comp_homEquiv_symm_comp_map`);
* if the right adjoints of `adj₁ : F₁ ⊣ R₁` and `adj₂ : F₂ ⊣ R₂` are identified by `e : R₂ ≅ R₁`,
  then the transpose of `χ ≫ e.hom.app P` along `adj₁` is an isomorphism as soon as the transpose of
  `χ` along `adj₂` is one (`CategoryTheory.Adjunction.isIso_homEquiv_symm_comp_hom_app`);
* transposes of morphisms that agree up to equalities of their source and target objects are
  isomorphisms simultaneously (`CategoryTheory.Adjunction.isIso_homEquiv_symm_of_eq`).

Together they show that the transposes of a morphism along two factorizations of a pushforward
functor are isomorphisms simultaneously, as for the comparison maps of sheaves along a commutative
square of schemes (`CategoryTheory.Adjunction.isIso_map_of_comp_eq_homEquiv_symm`).
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

/-- The transpose of `χ' : M' ⟶ G P'` is an isomorphism when the transpose of `χ : M ⟶ G P` is
one, `M = M'`, `P = P'`, and `χ'` is `χ` up to these equalities.

This lets a fact about a transpose be restated with its objects spelled differently, for instance
with a definition unfolded, without having to compare the two transposes by unfolding the
adjunction. -/
theorem isIso_homEquiv_symm_of_eq {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {M M' : C} {P P' : D}
    (hM : M = M') (hP : P = P') (χ : M ⟶ G.obj P) (χ' : M' ⟶ G.obj P') (h : HEq χ χ')
    [hχ : IsIso ((adj.homEquiv _ _).symm χ)] : IsIso ((adj.homEquiv _ _).symm χ') := by
  subst hM hP
  cases eq_of_heq h
  exact hχ

/-- Let `adjU : Lu ⊣ Ru`, `adjM : Lm ⊣ Rm`, `adjH : Lh ⊣ Rh` and `adjV : Lv ⊣ Rv` be adjunctions
whose right adjoints form a square `e : Rm ⋙ Ru ≅ Rv ⋙ Rh`. Let `φ : Lh M ⟶ N` be such that
`φ ≫ πV` is the transpose along `adjH` of `(πU ≫ Ru.map t) ≫ e.hom.app P`. If the transposes of
`πU`, `t` and `πV` are isomorphisms, then so is `Lv.map φ`.

For sheaves of modules along a commutative square of open immersions `ι_U`, `ι_V` and morphisms
`m`, `h`, this says that a morphism `h^* M ⟶ N` is an isomorphism over the image of `ι_V` as soon
as it is, after the identifications `ι_U^* M ≅ Q` and `ι_V^* N ≅ P`, the pullback of a
comparison `m^* Q ≅ P`. -/
theorem isIso_map_of_comp_eq_homEquiv_symm {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] {Lu : C₁ ⥤ C₂} {Ru : C₂ ⥤ C₁} {Lm : C₂ ⥤ C₃} {Rm : C₃ ⥤ C₂}
    {Lh : C₁ ⥤ C₄} {Rh : C₄ ⥤ C₁} {Lv : C₄ ⥤ C₃} {Rv : C₃ ⥤ C₄} (adjU : Lu ⊣ Ru)
    (adjM : Lm ⊣ Rm) (adjH : Lh ⊣ Rh) (adjV : Lv ⊣ Rv) (e : Rm ⋙ Ru ≅ Rv ⋙ Rh) {M : C₁}
    {Q : C₂} {P : C₃} {N : C₄} (πU : M ⟶ Ru.obj Q) (t : Q ⟶ Rm.obj P) (πV : N ⟶ Rv.obj P)
    (φ : Lh.obj M ⟶ N) [hπU : IsIso ((adjU.homEquiv _ _).symm πU)]
    [ht : IsIso ((adjM.homEquiv _ _).symm t)] [hπV : IsIso ((adjV.homEquiv _ _).symm πV)]
    (h : φ ≫ πV = (adjH.homEquiv M (Rv.obj P)).symm
      (CategoryStruct.comp (X := M) (Y := Ru.obj (Rm.obj P)) (Z := Rh.obj (Rv.obj P))
        (πU ≫ Ru.map t) (e.hom.app P))) :
    IsIso (Lv.map φ) := by
  have h₁ : IsIso (((adjU.comp adjM).homEquiv _ _).symm (πU ≫ Ru.map t)) := by
    rw [comp_homEquiv_symm_comp_map]
    infer_instance
  have h₂ := isIso_homEquiv_symm_comp_hom_app (adjH.comp adjV) (adjU.comp adjM) e
    (πU ≫ Ru.map t) (hχ := h₁)
  rw [comp_homEquiv, Equiv.symm_trans_apply, ← h, homEquiv_naturality_left_symm] at h₂
  exact IsIso.of_isIso_comp_right _ ((adjV.homEquiv _ _).symm πV)

end CategoryTheory.Adjunction
