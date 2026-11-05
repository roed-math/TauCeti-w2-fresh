/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.InverseImageOfLE
public import TauCeti.Lookahead.EpsilonFppfEtale.Stubs

/-!
# The comparison morphism from the small étale site to the small Nisnevich site

On the category `X.Etale` of schemes étale over a scheme `X`, the small étale topology is finer
than the small Nisnevich topology, so the identity functor induces a morphism of topoi
`Sh(X_ét) ⥤ Sh(X_Nis)`. It is given here through its inverse image `etaleToNisnevich X A`, the
étale sheafification of a Nisnevich sheaf with values in `A`. The inverse image is left adjoint to
the direct image, which regards an étale sheaf as a Nisnevich sheaf; it is exact and it sends
constant sheaves to constant sheaves.

## Main declarations

* `AlgebraicGeometry.Scheme.etaleToNisnevich`: the inverse image from Nisnevich sheaves to étale
  sheaves.
* `AlgebraicGeometry.Scheme.etaleToNisnevichAdjunction`: its adjunction with the direct image.
* `AlgebraicGeometry.Scheme.constantSheafCompEtaleToNisnevichIso`: it sends constant sheaves to
  constant sheaves.

## References

* F. Morel and V. Voevodsky, *𝔸¹-homotopy theory of schemes*, Publ. Math. IHÉS 90 (1999), §3.1.
-/

public section

open CategoryTheory Limits GrothendieckTopology

universe w w' u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (A : Type w) [Category.{w'} A]

variable [HasWeakSheafify X.smallEtaleTopology A]

/-- The inverse image of the morphism of topoi from the small étale site to the small Nisnevich
site of `X`: the étale sheafification of a Nisnevich sheaf. -/
noncomputable def etaleToNisnevich :
    Sheaf (smallNisnevichTopology X) A ⥤ Sheaf X.smallEtaleTopology A :=
  sheafInverseImage _ _ A

/-- The inverse image of a Nisnevich sheaf is its étale sheafification. -/
@[simp]
lemma etaleToNisnevich_obj (F : Sheaf (smallNisnevichTopology X) A) :
    (etaleToNisnevich X A).obj F = (presheafToSheaf _ A).obj F.obj :=
  (rfl)

/-- The inverse image from Nisnevich sheaves to étale sheaves is left adjoint to the direct image,
which regards an étale sheaf as a Nisnevich sheaf. -/
noncomputable def etaleToNisnevichAdjunction :
    etaleToNisnevich X A ⊣
      sheafDirectImageOfLE A (smallNisnevichTopology_le_smallEtaleTopology X) :=
  sheafAdjunctionOfLE A _

instance : (etaleToNisnevich X A).IsLeftAdjoint :=
  (etaleToNisnevichAdjunction X A).isLeftAdjoint

/-- The inverse image from Nisnevich sheaves to étale sheaves is exact. -/
instance [HasFiniteLimits A] [HasSheafify X.smallEtaleTopology A] :
    PreservesFiniteLimits (etaleToNisnevich X A) := by
  dsimp only [etaleToNisnevich]
  infer_instance

/-- The inverse image from Nisnevich sheaves to étale sheaves sends the constant Nisnevich sheaf
to the constant étale sheaf. -/
noncomputable def constantSheafCompEtaleToNisnevichIso
    [HasWeakSheafify (smallNisnevichTopology X) A] :
    constantSheaf _ A ⋙ etaleToNisnevich X A ≅ constantSheaf _ A :=
  constantSheafCompSheafInverseImageIso A (smallNisnevichTopology_le_smallEtaleTopology X)

end AlgebraicGeometry.Scheme
