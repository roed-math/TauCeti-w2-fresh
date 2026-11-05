/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Zariski
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Pullback

/-!
# Cohomology along the comparison morphisms between the small Zariski, Nisnevich and étale sites

The comparison morphisms from the small étale site of a scheme `X` to its small Nisnevich site,
and from the small Nisnevich site to the Zariski site, have exact inverse images that send constant
sheaves to constant sheaves. They therefore induce pullback maps on sheaf cohomology,

* `etaleToNisnevichH X F n : Hⁿ(X_Nis, F) →+ Hⁿ(X_ét, F^ét)`,
* `nisnevichToZariskiH X F n : Hⁿ(X_Zar, F) →+ Hⁿ(X_Nis, F^Nis)`,

through `CategoryTheory.Sheaf.H.pullback`. In degree zero the pullback from the Zariski site is the
restriction of global sections along the unit of the adjunction (`equiv₀_nisnevichToZariskiH`).

The coefficient universe `w` is arbitrary: the categories of abelian sheaves are assumed to have
`Ext` groups and the inverse image from Zariski to Nisnevich sheaves to be exact, which is an
instance for `w = u`.

## Main declarations

* `AlgebraicGeometry.Scheme.etaleToNisnevichH`, `nisnevichToZariskiH`: the pullbacks of
  cohomology.
* `AlgebraicGeometry.Scheme.equiv₀_nisnevichToZariskiH`: in degree zero, the pullback from the
  Zariski site is the restriction of global sections.
-/

public section

open CategoryTheory Limits Opposite GrothendieckTopology AddCommGrpCat

universe w w₁ w₂ u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

section Etale

variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
  [HasSheafify X.smallNisnevichTopology AddCommGrpCat.{w}]

/-- The inverse image from Nisnevich to étale abelian sheaves is additive. -/
instance : (etaleToNisnevich X AddCommGrpCat.{w}).Additive :=
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (etaleToNisnevich X AddCommGrpCat.{w})
  Functor.additive_of_preservesBinaryBiproducts _

variable [HasExt.{w₁} (Sheaf X.smallNisnevichTopology AddCommGrpCat.{w})]
  [HasExt.{w₂} (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})]

/-- The pullback `Hⁿ(X_Nis, F) →+ Hⁿ(X_ét, F^ét)` of cohomology along the comparison morphism
from the small étale site to the small Nisnevich site. -/
noncomputable def etaleToNisnevichH (F : Sheaf X.smallNisnevichTopology AddCommGrpCat.{w})
    (n : ℕ) : F.H n →+ ((etaleToNisnevich X AddCommGrpCat.{w}).obj F).H n :=
  Sheaf.H.pullback _
    ((constantSheafCompEtaleToNisnevichIso X AddCommGrpCat.{w}).inv.app (of (ULift ℤ))) F n

end Etale

section Zariski

variable [∀ F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w}, X.restrictEtaleFunctor.op.HasLeftKanExtension F]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
  [HasSheafify X.smallNisnevichTopology AddCommGrpCat.{w}]
  [PreservesFiniteLimits (nisnevichToZariski X AddCommGrpCat.{w})]

/-- The inverse image from Zariski to Nisnevich abelian sheaves is additive. -/
instance : (nisnevichToZariski X AddCommGrpCat.{w}).Additive :=
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (nisnevichToZariski X AddCommGrpCat.{w})
  Functor.additive_of_preservesBinaryBiproducts _

variable [HasExt.{w₁} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})]
  [HasExt.{w₂} (Sheaf X.smallNisnevichTopology AddCommGrpCat.{w})]

/-- The pullback `Hⁿ(X_Zar, F) →+ Hⁿ(X_Nis, F^Nis)` of cohomology along the comparison morphism
from the small Nisnevich site to the Zariski site. -/
noncomputable def nisnevichToZariskiH (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})
    (n : ℕ) : F.H n →+ ((nisnevichToZariski X AddCommGrpCat.{w}).obj F).H n :=
  Sheaf.H.pullback _
    ((constantSheafCompNisnevichToZariskiIso X AddCommGrpCat.{w}).inv.app (of (ULift ℤ))) F n

/-- In degree zero, the pullback of cohomology from the Zariski site to the small Nisnevich site is
the restriction of global sections `F(X) ⟶ F^Nis(X)` along the unit of the adjunction. -/
lemma equiv₀_nisnevichToZariskiH (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})
    (x : F.H 0) :
    Sheaf.H.equiv₀ _ (isTerminalRestrictEtaleFunctorObjTop X) (nisnevichToZariskiH X F 0 x) =
      ((nisnevichToZariskiAdjunction X _).unit.app F).hom.app (op ⊤)
        (Sheaf.H.equiv₀ F isTerminalTop x) := by
  have : PreservesFiniteLimits (X.restrictEtaleFunctor.sheafPullback AddCommGrpCat.{w}
      (Opens.grothendieckTopology X) X.smallNisnevichTopology) :=
    ‹PreservesFiniteLimits (nisnevichToZariski X _)›
  have := (nisnevichToZariskiAdjunction X AddCommGrpCat.{w}).isRightAdjoint
  have h := Sheaf.H.equiv₀_pullback_sheafPullback (K := X.smallNisnevichTopology)
    X.restrictEtaleFunctor isTerminalTop (isTerminalRestrictEtaleFunctorObjTop X) F x
  rw [nisnevichToZariskiH, constantSheafCompNisnevichToZariskiIso_inv_app]
  exact h

end Zariski

end AlgebraicGeometry.Scheme
