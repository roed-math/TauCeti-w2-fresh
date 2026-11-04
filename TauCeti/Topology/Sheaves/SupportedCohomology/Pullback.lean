/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Relative.Pullback
public import TauCeti.Topology.Sheaves.Functors
public import TauCeti.Topology.Sheaves.SupportedCohomology

/-!
# Inverse image on cohomology with supports

Let `f : X ⟶ Y` be a continuous map, `F` a sheaf of abelian groups on `Y`, `S` a closed subset and
`W` an open subset of `Y`. The inverse image functor `f⁻¹` is exact, and the preimage of the pair
`(W, W ∖ S)` is the pair `(f⁻¹ W, f⁻¹ W ∖ f⁻¹ S)`. Applying `f⁻¹` to extensions therefore gives the
inverse image map on cohomology with supports

`f.supportedHPullback F S W n : H_Sⁿ(W, F) →+ H_{f⁻¹ S}ⁿ(f⁻¹ W, f⁻¹ F)`,

the case `u = Opens.map f` of `CategoryTheory.Sheaf.relativeH'.pullback` (Stacks, Section 20.34
(0G6Y), for the functoriality of `RΓ_Z` along `f`). It is natural in `F`, and in degree zero it
is the map on sections supported in `S` given by the unit `F ⟶ f_* f⁻¹ F`.

## Main declarations

* `TopCat.Hom.supportedHPullback`: the map `H_Sⁿ(W, F) →+ H_{f⁻¹ S}ⁿ(f⁻¹ W, f⁻¹ F)`;
* `TopCat.Hom.supportedHPullback_naturality`: its naturality in `F`;
* `TopCat.Hom.coe_supportedHZeroEquiv_supportedHPullback`: its description in degree zero.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite Abelian

universe u

namespace TopCat.Hom

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

noncomputable section

/-- The inverse image map `H_Sⁿ(W, F) →+ H_{f⁻¹ S}ⁿ(f⁻¹ W, f⁻¹ F)` on cohomology with supports
along a continuous map `f : X ⟶ Y`: the pullback of relative cohomology along `Opens.map f`,
followed by the identification of `f⁻¹ (W ∖ S)` with `f⁻¹ W ∖ f⁻¹ S`. -/
def supportedHPullback (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (S : Closeds Y) (W : Opens Y) (n : ℕ) :
    F.supportedH S W n →+
      (((Opens.map f).sheafPullback AddCommGrpCat.{u} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).obj F).supportedH (S.preimage f.hom.continuous)
          ((Opens.map f).obj W) n :=
  (CategoryTheory.Sheaf.relativeH'.map _ ((Opens.map f).map (S.complInclusion W))
      ((S.preimage f.hom.continuous).complInclusion ((Opens.map f).obj W))
      (homOfLE fun _ hx ↦ hx) (𝟙 _) rfl n).comp
    (CategoryTheory.Sheaf.relativeH'.pullback (Opens.map f) F (S.complInclusion W) n)

/-- The inverse image map on cohomology with supports is natural in the coefficient sheaf. -/
lemma supportedHPullback_naturality
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}} (α : F ⟶ G)
    (S : Closeds Y) (W : Opens Y) {n : ℕ} (x : F.supportedH S W n) :
    f.supportedHPullback G S W n (x.comp (Ext.mk₀ α) (add_zero n)) =
      (f.supportedHPullback F S W n x).comp
        (Ext.mk₀ (((Opens.map f).sheafPullback AddCommGrpCat.{u} _ _).map α)) (add_zero n) := by
  simp only [supportedHPullback, AddMonoidHom.comp_apply,
    CategoryTheory.Sheaf.relativeH'.pullback_naturality,
    CategoryTheory.Sheaf.relativeH'.map_apply]
  exact (Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by lia)).symm

/-- In degree zero, the inverse image map on cohomology with supports is the map on sections
supported in `S` given by the unit `F ⟶ f_* f⁻¹ F`. -/
lemma coe_supportedHZeroEquiv_supportedHPullback
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (S : Closeds Y) (W : Opens Y) (x : F.supportedH S W 0) :
    (CategoryTheory.Sheaf.supportedHZeroEquiv _ _ _ (f.supportedHPullback F S W 0 x)).1 =
      (((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{u} (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app F).hom.app (op W)
        (F.supportedHZeroEquiv S W x).1 := by
  rw [CategoryTheory.Sheaf.coe_supportedHZeroEquiv_apply,
    CategoryTheory.Sheaf.coe_supportedHZeroEquiv_apply, supportedHPullback,
    AddMonoidHom.comp_apply, CategoryTheory.Sheaf.relativeH'.coe_zeroEquiv_map,
    CategoryTheory.Sheaf.relativeH'.coe_zeroEquiv_pullback, op_id,
    CategoryTheory.Functor.map_id]
  rfl

end

end TopCat.Hom
