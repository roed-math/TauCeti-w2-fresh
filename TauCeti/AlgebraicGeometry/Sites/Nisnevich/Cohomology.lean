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

through `CategoryTheory.Sheaf.H.pullback`. In degree zero both are the restriction of global
sections along the unit of the adjunction (`equiv₀_etaleToNisnevichH`,
`equiv₀_nisnevichToZariskiH`), so the first is bijective in degree zero on Nisnevich sheaves that
are already étale sheaves (`etaleToNisnevichH_zero_bijective`), in particular on étale sheaves
(`etaleToNisnevichH_zero_bijective_of_etale`), and the second is injective in degree zero on
restrictions of Nisnevich sheaves (`nisnevichToZariskiH_zero_injective`).
Their composite is the pullback of cohomology from the Zariski site to the small étale site
(`map_etaleToNisnevichH_nisnevichToZariskiH`).

The coefficient universe `w` is arbitrary: the categories of abelian sheaves are assumed to have
`Ext` groups and the inverse image from Zariski to Nisnevich sheaves to be exact, which is an
instance for `w = u`.

## Main declarations

* `AlgebraicGeometry.Scheme.etaleToNisnevichH`, `nisnevichToZariskiH`: the pullbacks of
  cohomology.
* `AlgebraicGeometry.Scheme.equiv₀_etaleToNisnevichH`, `equiv₀_nisnevichToZariskiH`: in degree
  zero, the pullbacks are the restriction of global sections.
* `AlgebraicGeometry.Scheme.etaleToNisnevichH_zero_bijective`,
  `etaleToNisnevichH_zero_bijective_of_etale`: in degree zero, the pullback to the étale site is
  bijective on Nisnevich sheaves that are already étale sheaves.
* `AlgebraicGeometry.Scheme.nisnevichToZariskiH_zero_injective`: in degree zero, the pullback to
  the Nisnevich site is injective on restrictions of Nisnevich sheaves to the Zariski site.
* `AlgebraicGeometry.Scheme.map_etaleToNisnevichH_nisnevichToZariskiH`: the pullbacks from the
  Zariski site to the Nisnevich site and from there to the étale site compose to the pullback from
  the Zariski site to the étale site.
-/

public section

open CategoryTheory Limits Opposite GrothendieckTopology AddCommGrpCat

universe w w₁ w₂ w₃ u

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

/-- In degree zero, the pullback of cohomology from the small Nisnevich site to the small étale site
is the restriction of global sections `F(X) ⟶ F^ét(X)` along the unit of the adjunction. -/
lemma equiv₀_etaleToNisnevichH (F : Sheaf X.smallNisnevichTopology AddCommGrpCat.{w})
    (x : F.H 0) :
    Sheaf.H.equiv₀ _ (isTerminalRestrictEtaleFunctorObjTop X) (etaleToNisnevichH X F 0 x) =
      ((etaleToNisnevichAdjunction X _).unit.app F).hom.app (op (X.restrictEtaleFunctor.obj ⊤))
        (Sheaf.H.equiv₀ F (isTerminalRestrictEtaleFunctorObjTop X) x) :=
  have : PreservesFiniteColimits (sheafInverseImage X.smallNisnevichTopology
      X.smallEtaleTopology AddCommGrpCat.{w}) :=
    inferInstanceAs (PreservesFiniteColimits (etaleToNisnevich X _))
  Sheaf.H.equiv₀_pullback_sheafInverseImage (smallNisnevichTopology_le_smallEtaleTopology X)
    (isTerminalRestrictEtaleFunctorObjTop X) F x

/-- In degree zero, the pullback of cohomology from the small Nisnevich site to the small étale
site is bijective on a Nisnevich sheaf that is already an étale sheaf. -/
theorem etaleToNisnevichH_zero_bijective (F : Sheaf X.smallNisnevichTopology AddCommGrpCat.{w})
    (hF : Presheaf.IsSheaf X.smallEtaleTopology F.obj) :
    Function.Bijective (etaleToNisnevichH X F 0) :=
  have : PreservesFiniteColimits (sheafInverseImage X.smallNisnevichTopology
      X.smallEtaleTopology AddCommGrpCat.{w}) :=
    inferInstanceAs (PreservesFiniteColimits (etaleToNisnevich X _))
  Sheaf.H.pullback_sheafInverseImage_zero_bijective (smallNisnevichTopology_le_smallEtaleTopology X)
    (isTerminalRestrictEtaleFunctorObjTop X) F hF

/-- In degree zero, the pullback of cohomology from the small Nisnevich site to the small étale
site is bijective on an étale sheaf regarded as a Nisnevich sheaf. This applies to the restrictions
of the big-site sheaves `𝔾_a` and `𝔾_m` to the small étale site, and is the degree-zero case of
the comparison of their Nisnevich and étale cohomology. -/
theorem etaleToNisnevichH_zero_bijective_of_etale
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) :
    Function.Bijective (etaleToNisnevichH X ((sheafDirectImageOfLE AddCommGrpCat.{w}
      (smallNisnevichTopology_le_smallEtaleTopology X)).obj F) 0) :=
  etaleToNisnevichH_zero_bijective X _ F.property

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

/-- In degree zero, the pullback of cohomology from the Zariski site to the small Nisnevich site is
injective on the restriction of a Nisnevich sheaf `G` to the Zariski site: restricting global
sections along the unit of the adjunction and then along the counit at `G` is the identity
(`Sheaf.H.pullback_sheafPullback_zero_injective`). This applies to the restrictions of the big-site
sheaves `𝔾_a` and `𝔾_m`. -/
theorem nisnevichToZariskiH_zero_injective (G : Sheaf X.smallNisnevichTopology AddCommGrpCat.{w}) :
    Function.Injective (nisnevichToZariskiH X ((X.restrictEtaleFunctor.sheafPushforwardContinuous
      AddCommGrpCat.{w} _ X.smallNisnevichTopology).obj G) 0) := by
  have : PreservesFiniteLimits (X.restrictEtaleFunctor.sheafPullback AddCommGrpCat.{w}
      (Opens.grothendieckTopology X) X.smallNisnevichTopology) :=
    ‹PreservesFiniteLimits (nisnevichToZariski X _)›
  have := (nisnevichToZariskiAdjunction X AddCommGrpCat.{w}).isRightAdjoint
  rw [nisnevichToZariskiH, constantSheafCompNisnevichToZariskiIso_inv_app]
  exact Sheaf.H.pullback_sheafPullback_zero_injective (K := X.smallNisnevichTopology)
    X.restrictEtaleFunctor isTerminalTop (isTerminalRestrictEtaleFunctorObjTop X) G

section Etale

variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
  [HasExt.{w₃} (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})]

/-- The pullback of abelian sheaves from the Zariski site to the small étale site is exact, since
it is the composite of the exact inverse images through the small Nisnevich site. -/
instance : PreservesFiniteLimits (X.restrictEtaleFunctor.sheafPullback AddCommGrpCat.{w}
    (Opens.grothendieckTopology X) X.smallEtaleTopology) :=
  preservesFiniteLimits_of_natIso (nisnevichToZariskiCompEtaleToNisnevichIso X AddCommGrpCat.{w})

instance : (X.restrictEtaleFunctor.sheafPullback AddCommGrpCat.{w}
    (Opens.grothendieckTopology X) X.smallEtaleTopology).IsLeftAdjoint :=
  (X.restrictEtaleFunctor.sheafAdjunctionContinuous _ _ _).isLeftAdjoint

/-- The pullback of abelian sheaves from the Zariski site to the small étale site is additive. -/
instance : (X.restrictEtaleFunctor.sheafPullback AddCommGrpCat.{w}
    (Opens.grothendieckTopology X) X.smallEtaleTopology).Additive :=
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (X.restrictEtaleFunctor.sheafPullback AddCommGrpCat.{w} (Opens.grothendieckTopology X)
      X.smallEtaleTopology)
  Functor.additive_of_preservesBinaryBiproducts _

/-- **Composition of the pullbacks of cohomology**: the pullback of cohomology from the Zariski
site to the small Nisnevich site, followed by the pullback to the small étale site, is the pullback
of cohomology along the morphism of sites from the small étale site to the Zariski site, under the
identification `nisnevichToZariskiCompEtaleToNisnevichIso` of the coefficient sheaves. -/
theorem map_etaleToNisnevichH_nisnevichToZariskiH
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}) (n : ℕ) (x : F.H n) :
    Sheaf.H.map ((nisnevichToZariskiCompEtaleToNisnevichIso X AddCommGrpCat.{w}).hom.app F) n
        (etaleToNisnevichH X _ n (nisnevichToZariskiH X F n x)) =
      Sheaf.H.pullback (X.restrictEtaleFunctor.sheafPullback AddCommGrpCat.{w} _
        X.smallEtaleTopology) (X.restrictEtaleFunctor.sheafPullbackConstantSheafIso
          AddCommGrpCat.{w} _ X.smallEtaleTopology (of (ULift ℤ))).inv F n x := by
  rw [etaleToNisnevichH, nisnevichToZariskiH, ← Sheaf.H.pullback_comp_apply,
    ← Sheaf.H.pullback_natTrans_apply, Category.assoc,
    constantSheafComp_nisnevichToZariskiCompEtaleToNisnevichIso_hom_app]

end Etale

end Zariski

end AlgebraicGeometry.Scheme
