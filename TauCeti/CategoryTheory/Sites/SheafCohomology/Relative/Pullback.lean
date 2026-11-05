/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.Pullback
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Relative

/-!
# Pullback of relative sheaf cohomology

Let `u : C ⥤ D` be a continuous functor between sites `(C, J)` and `(D, K)` whose pushforward of
abelian sheaves has a left adjoint `u^* = u.sheafPullback`. For an object `U` of `C`, the free
abelian sheaf `ℤ_{u U}` on `D` maps to `u^* ℤ_U`: under the Yoneda equivalence
`(ℤ_{u U} ⟶ G) ≃+ G(u U)`, the map is the section of `u^* ℤ_U` over `u U` given by the unit
`ℤ_U ⟶ u_* u^* ℤ_U` evaluated at the generator of `ℤ_U(U)`. These maps are natural in `U`, so for
a morphism `i : U ⟶ V` of `C` they descend to the relative free sheaves,
`ℤ_{u V, u U} ⟶ u^* ℤ_{V, U}`.

When `u^*` is moreover exact, applying `u^*` to an extension and precomposing with this map gives
the pullback of relative cohomology

`relativeH'.pullback u F i n : Hⁿ(V, U; F) →+ Hⁿ(u V, u U; u^* F)`.

In degree zero it is the map on sections vanishing along `i` induced by the unit
`F ⟶ u_* u^* F` (`CategoryTheory.Sheaf.relativeH'.coe_zeroEquiv_pullback`). For a continuous map
of topological spaces this is the pullback of cohomology with supports
(`TauCeti.Topology.Sheaves.SupportedCohomology.Pullback`).

## Main declarations

* `TauCeti.CategoryTheory.freeYonedaSheafPullbackComparison`: the map `ℤ_{u U} ⟶ u^* ℤ_U`;
* `TauCeti.CategoryTheory.relativeFreeYonedaSheafPullbackComparison`: the induced map
  `ℤ_{u V, u U} ⟶ u^* ℤ_{V, U}`;
* `CategoryTheory.Sheaf.relativeH'.pullback`: the pullback `Hⁿ(V, U; F) →+ Hⁿ(u V, u U; u^* F)`;
* `CategoryTheory.Sheaf.relativeH'.pullback_naturality`: its naturality in the coefficient sheaf;
* `CategoryTheory.Sheaf.relativeH'.pullback_comp_extClass`: its compatibility with connecting
  maps;
* `CategoryTheory.Sheaf.relativeH'.coe_zeroEquiv_pullback`: its description in degree zero.
-/

public section

open CategoryTheory Limits Opposite Abelian

universe w v u₁ u₂

namespace TauCeti.CategoryTheory

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{v} D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  (u : C ⥤ D) [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).IsRightAdjoint]

noncomputable section

/-- The map `ℤ_{u U} ⟶ u^* ℤ_U` from the free abelian sheaf on `u U` to the pullback of the free
abelian sheaf on `U`: it corresponds to the section of `u^* ℤ_U` over `u U` given by the unit
`ℤ_U ⟶ u_* u^* ℤ_U`. -/
def freeYonedaSheafPullbackComparison (U : C) :
    (freeYonedaSheafFunctor K).obj (u.obj U) ⟶
      (u.sheafPullback AddCommGrpCat.{v} J K).obj ((freeYonedaSheafFunctor J).obj U) :=
  (freeYonedaSheafSectionsEquiv K (u.obj U) _).symm
    (freeYonedaSheafSectionsEquiv J U _
      ((u.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.app _))

/-- The section of `u^* ℤ_U` over `u U` corresponding to `freeYonedaSheafPullbackComparison` is the
section corresponding to the unit `ℤ_U ⟶ u_* u^* ℤ_U`. -/
lemma freeYonedaSheafSectionsEquiv_pullbackComparison (U : C) :
    freeYonedaSheafSectionsEquiv K (u.obj U) _ (freeYonedaSheafPullbackComparison u U) =
      freeYonedaSheafSectionsEquiv J U _
        ((u.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.app _) :=
  AddEquiv.apply_symm_apply _ _

/-- Precomposing a map `u^* ℤ_U ⟶ G` with `freeYonedaSheafPullbackComparison` corresponds to its
adjoint `ℤ_U ⟶ u_* G` under the Yoneda equivalences. -/
lemma freeYonedaSheafSectionsEquiv_pullbackComparison_comp {U : C}
    {G : Sheaf K AddCommGrpCat.{v}}
    (g : (u.sheafPullback AddCommGrpCat.{v} J K).obj ((freeYonedaSheafFunctor J).obj U) ⟶ G) :
    freeYonedaSheafSectionsEquiv K (u.obj U) G (freeYonedaSheafPullbackComparison u U ≫ g) =
      freeYonedaSheafSectionsEquiv J U ((u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj G)
        ((u.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _ g) := by
  rw [freeYonedaSheafSectionsEquiv_naturality_right,
    freeYonedaSheafSectionsEquiv_pullbackComparison, Adjunction.homEquiv_unit,
    freeYonedaSheafSectionsEquiv_naturality_right]
  rfl

/-- The maps `freeYonedaSheafPullbackComparison` are natural in the object of the site. -/
@[reassoc]
lemma freeYonedaSheafPullbackComparison_naturality {U V : C} (i : U ⟶ V) :
    (freeYonedaSheafFunctor K).map (u.map i) ≫ freeYonedaSheafPullbackComparison u V =
      freeYonedaSheafPullbackComparison u U ≫
        (u.sheafPullback AddCommGrpCat.{v} J K).map ((freeYonedaSheafFunctor J).map i) := by
  apply (freeYonedaSheafSectionsEquiv K (u.obj U) _).injective
  rw [freeYonedaSheafSectionsEquiv_naturality_left,
    freeYonedaSheafSectionsEquiv_pullbackComparison_comp, Adjunction.homEquiv_unit,
    Adjunction.unit_naturality, freeYonedaSheafSectionsEquiv_naturality_left,
    freeYonedaSheafSectionsEquiv_pullbackComparison]
  rfl

/-- The map `ℤ_{u V, u U} ⟶ u^* ℤ_{V, U}` of relative free sheaves induced by
`freeYonedaSheafPullbackComparison`, for a morphism `i : U ⟶ V` of the site. -/
def relativeFreeYonedaSheafPullbackComparison {U V : C} (i : U ⟶ V) :
    relativeFreeYonedaSheaf K (u.map i) ⟶
      (u.sheafPullback AddCommGrpCat.{v} J K).obj (relativeFreeYonedaSheaf J i) :=
  cokernel.desc _ (freeYonedaSheafPullbackComparison u V ≫
    (u.sheafPullback AddCommGrpCat.{v} J K).map (cokernel.π _)) (by
      have := (u.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).isLeftAdjoint
      rw [freeYonedaSheafPullbackComparison_naturality_assoc, ← Functor.map_comp,
        cokernel.condition, Functor.map_zero, comp_zero])

@[reassoc (attr := simp)]
lemma cokernel_π_relativeFreeYonedaSheafPullbackComparison {U V : C} (i : U ⟶ V) :
    cokernel.π _ ≫ relativeFreeYonedaSheafPullbackComparison u i =
      freeYonedaSheafPullbackComparison u V ≫
        (u.sheafPullback AddCommGrpCat.{v} J K).map (cokernel.π _) :=
  cokernel.π_desc _ _ _

/-- Under `relativeFreeYonedaSheafHomEquiv`, precomposing a map `u^* ℤ_{V, U} ⟶ G` with
`relativeFreeYonedaSheafPullbackComparison` gives the section of `G` over `u V` corresponding to its
adjoint `ℤ_{V, U} ⟶ u_* G`. -/
lemma coe_relativeFreeYonedaSheafHomEquiv_pullbackComparison_comp {U V : C} (i : U ⟶ V)
    {G : Sheaf K AddCommGrpCat.{v}}
    (g : (u.sheafPullback AddCommGrpCat.{v} J K).obj (relativeFreeYonedaSheaf J i) ⟶ G) :
    (relativeFreeYonedaSheafHomEquiv K (u.map i) G
        (relativeFreeYonedaSheafPullbackComparison u i ≫ g) : G.obj.obj (op (u.obj V))) =
      (relativeFreeYonedaSheafHomEquiv J i
        ((u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj G)
          ((u.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _ g)).1 := by
  rw [coe_relativeFreeYonedaSheafHomEquiv_apply, coe_relativeFreeYonedaSheafHomEquiv_apply,
    cokernel_π_relativeFreeYonedaSheafPullbackComparison_assoc,
    freeYonedaSheafSectionsEquiv_pullbackComparison_comp, Adjunction.homEquiv_naturality_left]

end

end TauCeti.CategoryTheory

namespace CategoryTheory.Sheaf.relativeH'

open TauCeti.CategoryTheory

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{v} D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w} (Sheaf K AddCommGrpCat.{v})]
  (u : C ⥤ D) [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).IsRightAdjoint]
  [PreservesFiniteLimits (u.sheafPullback AddCommGrpCat.{v} J K)]

local instance : (u.sheafPullback AddCommGrpCat.{v} J K).Additive :=
  Functor.additive_of_preserves_binary_products _

local instance : PreservesFiniteColimits (u.sheafPullback AddCommGrpCat.{v} J K) :=
  letI := (u.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).leftAdjoint_preservesColimits.{0, 0}
  inferInstance

noncomputable section

/-- The pullback `Hⁿ(V, U; F) →+ Hⁿ(u V, u U; u^* F)` of relative cohomology along a continuous
functor `u` with exact sheaf pullback `u^*`: a class in `Extⁿ(ℤ_{V, U}, F)` is sent to its image
under `u^*`, precomposed with the comparison `ℤ_{u V, u U} ⟶ u^* ℤ_{V, U}`. -/
def pullback (F : Sheaf J AddCommGrpCat.{v}) {U V : C} (i : U ⟶ V) (n : ℕ) :
    F.relativeH' i n →+ ((u.sheafPullback AddCommGrpCat.{v} J K).obj F).relativeH' (u.map i) n :=
  ((Ext.mk₀ (relativeFreeYonedaSheafPullbackComparison u i)).precomp _ (zero_add n)).comp
    ((u.sheafPullback AddCommGrpCat.{v} J K).mapExtAddHom _ F n)

lemma pullback_apply (F : Sheaf J AddCommGrpCat.{v}) {U V : C} (i : U ⟶ V) {n : ℕ}
    (x : F.relativeH' i n) :
    pullback u F i n x = (Ext.mk₀ (relativeFreeYonedaSheafPullbackComparison u i)).comp
      (x.mapExactFunctor (u.sheafPullback AddCommGrpCat.{v} J K)) (zero_add n) :=
  (rfl)

/-- The pullback of relative cohomology is natural in the coefficient sheaf. -/
lemma pullback_naturality {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) {U V : C} (i : U ⟶ V)
    {n : ℕ} (x : F.relativeH' i n) :
    pullback u G i n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (pullback u F i n x).comp (Ext.mk₀ ((u.sheafPullback AddCommGrpCat.{v} J K).map f))
        (add_zero n) := by
  simp [pullback_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]

/-- The pullback of relative cohomology commutes with the connecting maps of a short exact sequence
of abelian sheaves and of its image under the exact functor `u^*`. -/
lemma pullback_comp_extClass {T : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hT : T.ShortExact)
    {U V : C} (i : U ⟶ V) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : T.X₃.relativeH' i n₀) :
    pullback u T.X₁ i n₁ (x.comp hT.extClass h) =
      (pullback u T.X₃ i n₀ x).comp
        (hT.map_of_exact (u.sheafPullback AddCommGrpCat.{v} J K)).extClass h := by
  rw [pullback_apply, pullback_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n₀) h (by lia)).symm

/-- In degree zero, the pullback of relative cohomology is the map on sections vanishing along `i`
induced by the unit `F ⟶ u_* u^* F`. -/
lemma coe_zeroEquiv_pullback (F : Sheaf J AddCommGrpCat.{v}) {U V : C} (i : U ⟶ V)
    (x : F.relativeH' i 0) :
    (zeroEquiv ((u.sheafPullback AddCommGrpCat.{v} J K).obj F) (u.map i)
        (pullback u F i 0 x)).1 =
      ((u.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.app F).hom.app (op V)
        (zeroEquiv F i x).1 := by
  obtain ⟨g, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  rw [pullback_apply, Ext.addEquiv₀_symm_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀,
    coe_zeroEquiv_apply, coe_zeroEquiv_apply, ← Ext.addEquiv₀_symm_apply,
    ← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    cokernel_π_relativeFreeYonedaSheafPullbackComparison_assoc, ← Functor.map_comp,
    freeYonedaSheafSectionsEquiv_pullbackComparison_comp, Adjunction.homEquiv_unit,
    Adjunction.unit_naturality, freeYonedaSheafSectionsEquiv_naturality_right]

end

end CategoryTheory.Sheaf.relativeH'
