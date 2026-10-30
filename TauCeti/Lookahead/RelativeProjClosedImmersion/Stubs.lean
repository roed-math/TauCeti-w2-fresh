/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Functor
public import TauCeti.AlgebraicGeometry.RelativeProj.Basic

set_option warningAsError false

/-!
# Lookahead stubs for `relative-proj-twisting-sheaf`

These are lookahead stubs of the declarations of the supplier `relative-proj-twisting-sheaf`
(SchemeAndStackFoundations, open PR #22384) consumed by `relative-proj-closed-immersion`, stated
as in that PR's diff. They are to be replaced by the landed declarations: the gluing datum of
modules and its glued module (PR #22384's `TauCeti/AlgebraicGeometry/Modules/Gluing.lean`) and the
twisting sheaves of the relative `Proj` (its
`TauCeti/AlgebraicGeometry/RelativeProj/TwistingSheaf.lean`).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace TauCeti

universe u

/-- A **gluing datum of modules** on a diagram of schemes `F : J ⥤ Scheme`: a sheaf of modules
`Mⱼ` on each `F j`, with transition morphisms `Mⱼ ⟶ (F f)_* Mᵢ` for `f : i ⟶ j`, compatible with
identities and composition on sections. -/
structure ModulesGlueData {J : Type u} [SmallCategory J] (F : J ⥤ Scheme.{u}) where
  /-- The sheaf of modules on `F j`. -/
  obj (j : J) : (F.obj j).Modules
  /-- The transition morphism `Mⱼ ⟶ (F f)_* Mᵢ` along `f : i ⟶ j`. -/
  map {i j : J} (f : i ⟶ j) : obj j ⟶ (Scheme.Modules.pushforward (F.map f)).obj (obj i)
  /-- The transition morphism along an identity is the identity on sections, up to the
  restriction along `(F (𝟙 j))⁻¹ V = V`. -/
  map_id (j : J) (V : (F.obj j).Opens) (s : Γ(obj j, V)) :
    (obj j).presheaf.map (eqToHom (show V = F.map (𝟙 j) ⁻¹ᵁ V by rw [F.map_id]; rfl)).op
      ((map (𝟙 j)).app V s) = s
  /-- The transition morphisms are compatible with composition on sections, up to the restriction
  along `(F f)⁻¹ (F g)⁻¹ V = (F (f ≫ g))⁻¹ V`. -/
  map_comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (V : (F.obj k).Opens) (s : Γ(obj k, V)) :
    (obj i).presheaf.map
        (eqToHom (show F.map f ⁻¹ᵁ F.map g ⁻¹ᵁ V = F.map (f ≫ g) ⁻¹ᵁ V by rw [F.map_comp]; rfl)).op
        ((map (f ≫ g)).app V s) =
      (map f).app (F.map g ⁻¹ᵁ V) ((map g).app V s)

namespace ModulesGlueData

noncomputable section

variable {J : Type u} [SmallCategory J] {F : J ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)] [(F ⋙ Scheme.forget).IsLocallyDirected]
  [Quiver.IsThin J]

/-- The morphism `(ιⱼ)_* Mⱼ ⟶ (ιᵢ)_* Mᵢ` induced by the transition morphism of a gluing datum
along `f : i ⟶ j`, using `F f ≫ ιⱼ = ιᵢ`. -/
def transition (D : ModulesGlueData F) {i j : J} (f : i ⟶ j) :
    (Scheme.Modules.pushforward (colimit.ι F j)).obj (D.obj j) ⟶
      (Scheme.Modules.pushforward (colimit.ι F i)).obj (D.obj i) :=
  sorry

/-- On sections over `U`, the morphism induced by a transition morphism is the transition
morphism over `ιⱼ⁻¹ U` followed by the restriction along `(F f)⁻¹ ιⱼ⁻¹ U = ιᵢ⁻¹ U`. -/
theorem transition_app_apply (D : ModulesGlueData F) {i j : J} (f : i ⟶ j)
    (U : (colimit F).Opens)
    (s : Γ((Scheme.Modules.pushforward (colimit.ι F j)).obj (D.obj j), U)) :
    (D.transition f).app U s = (D.obj i).presheaf.map
      (eqToHom (show colimit.ι F i ⁻¹ᵁ U = F.map f ⁻¹ᵁ colimit.ι F j ⁻¹ᵁ U by
        rw [← colimit.w F f]; rfl)).op ((D.map f).app (colimit.ι F j ⁻¹ᵁ U) s) :=
  sorry

/-- The **glued module** of a gluing datum of modules on `F`. -/
def glued (D : ModulesGlueData F) : (colimit F).Modules :=
  sorry

/-- The projection from the glued module to the pushforward `(ιⱼ)_* Mⱼ`. -/
def π (D : ModulesGlueData F) (j : J) :
    D.glued ⟶ (Scheme.Modules.pushforward (colimit.ι F j)).obj (D.obj j) :=
  sorry

/-- The projections from the glued module are compatible with the transition morphisms, on
sections. -/
theorem transition_app_π_app (D : ModulesGlueData F) {i j : J} (f : i ⟶ j)
    (U : (colimit F).Opens)
    (s : Γ(D.glued, U)) :
    (D.transition f).app U ((D.π j).app U s) = (D.π i).app U s :=
  sorry

/-- The morphism into the glued module from a family of morphisms `M ⟶ (ιⱼ)_* Mⱼ` compatible with
the transition morphisms. -/
def lift (D : ModulesGlueData F) {M : (colimit F).Modules}
    (g : ∀ j, M ⟶ (Scheme.Modules.pushforward (colimit.ι F j)).obj (D.obj j))
    (hg : ∀ {i j : J} (f : i ⟶ j), g j ≫ D.transition f = g i) : M ⟶ D.glued :=
  sorry

/-- The composite of the morphism into the glued module induced by a compatible family with a
projection is the corresponding member of the family. -/
@[reassoc (attr := simp)]
theorem lift_π (D : ModulesGlueData F) {M : (colimit F).Modules}
    (g : ∀ j, M ⟶ (Scheme.Modules.pushforward (colimit.ι F j)).obj (D.obj j))
    (hg : ∀ {i j : J} (f : i ⟶ j), g j ≫ D.transition f = g i) (j : J) :
    D.lift g hg ≫ D.π j = g j :=
  sorry

end

end ModulesGlueData

noncomputable section

variable {X : Scheme.{u}} (A : CommMon (GradedObject ℕ X.Modules)) [∀ n, (A.X n).IsQuasicoherent]

open Scheme.AffineZariskiSite

/-- The gluing datum of the twisting sheaves `𝒪(n)` of the charts `Proj (⨁ n, Γ(Aₙ, U))` of the
relative `Proj`, with the maps of twisting sheaves induced by restriction of sections. Its data
are PR #22384's (exposed, with `simps`); only its two proof fields are stubbed. -/
@[expose, simps]
def _root_.CategoryTheory.CommMon.relativeProjTwistingSheafGlueData (n : ℤ) :
    ModulesGlueData A.relativeProjGluingData.functor where
  obj U := Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n
  map i := Proj.twistingSheafMap (A.restrictGradedSectionsGradedHom ((toOpensFunctor X).map i))
    (A.irrelevant_le_map_restrictGradedSectionsGradedHom_toOpensFunctor i) n
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The **twisting sheaf `𝒪(n)` on the relative `Proj`** of a graded algebra `A` on `X`. -/
def _root_.CategoryTheory.CommMon.relativeProjTwistingSheaf (n : ℤ) :
    A.relativeProj.Modules :=
  sorry

/-- The twisting sheaf `𝒪(n)` on the relative `Proj` is the glued module of the gluing datum of the
twisting sheaves of the charts. -/
theorem _root_.CategoryTheory.CommMon.relativeProjTwistingSheaf_def (n : ℤ) :
    A.relativeProjTwistingSheaf n = (A.relativeProjTwistingSheafGlueData n).glued :=
  sorry

end

end TauCeti
