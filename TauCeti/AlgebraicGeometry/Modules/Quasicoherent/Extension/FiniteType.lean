/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Extension
public import TauCeti.AlgebraicGeometry.Modules.Restriction.FiniteType

/-!
# Extending finite-type quasi-coherent submodules across one more open

Let `X = U ∪ W` with `W ⊆ X` a quasi-compact open, and let `G` be a quasi-coherent
`𝒪_X`-module of finite type over `U`. A finite-type quasi-coherent submodule `H ⊆ G|_W` that is
all of `G` over `U ∩ W` extends to a finite-type quasi-coherent submodule `G' ⊆ G` that is all
of `G` over `U` and restricts to `H` over `W`. This is the gluing step of the induction on the
number of affine opens in the proof of Stacks, Lemma 28.23.2 (01PF): `G'` is the extension of
`H` along `W ⟶ X`, which changes nothing over `U`, and finite type is checked on the cover
`{U, W}`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_restrict_iso_of_sup_eq_top`: the
  gluing step.

## References

* The Stacks Project, Lemma 28.23.2 (Tag 01PF).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- **Gluing step for finite-type submodules.** Let `X = U ∪ W` with `W ⊆ X` a quasi-compact
open, `G` a quasi-coherent `𝒪_X`-module whose restriction to `U` is of finite type, and
`i : H ⟶ G|_W` a finite-type quasi-coherent submodule that is an isomorphism over `U ∩ W`. Then
there is a finite-type quasi-coherent submodule `i' : G' ⟶ G` that is an isomorphism over `U`,
together with an isomorphism `G'|_W ≅ H` carrying `i'|_W` to `i`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_restrict_iso_of_sup_eq_top
    {X : Scheme.{u}} (U W : X.Opens) (hUW : U ⊔ W = ⊤) [QuasiCompact W.ι]
    {G : X.Modules} [G.IsQuasicoherent] [(G.restrict U.ι).IsFiniteType]
    {H : W.toScheme.Modules} [H.IsQuasicoherent] [H.IsFiniteType]
    (i : H ⟶ G.restrict W.ι) [Mono i]
    (hi : IsIso ((Scheme.Modules.restrictFunctor (W.ι ⁻¹ᵁ U).ι).map i)) :
    ∃ (G' : X.Modules) (_ : G'.IsQuasicoherent) (_ : G'.IsFiniteType) (i' : G' ⟶ G)
      (_ : Mono i'), IsIso ((Scheme.Modules.restrictFunctor U.ι).map i') ∧
        ∃ e : G'.restrict W.ι ≅ H, (Scheme.Modules.restrictFunctor W.ι).map i' = e.hom ≫ i := by
  obtain ⟨G', _, i', _, e, he, hV⟩ :=
    Scheme.Modules.exists_mono_restrict_iso_of_isQuasicoherent W.ι i
  have hU := hV U hi
  refine ⟨G', inferInstance, ?_, i', inferInstance, hU, e, he⟩
  let V : ULift.{u} Bool → X.Opens := fun b ↦ cond b.down U W
  have hcover : ⨆ b, V b = ⊤ :=
    top_le_iff.mp (hUW ▸ sup_le (le_iSup V ⟨true⟩) (le_iSup V ⟨false⟩))
  refine isFiniteType_of_isFiniteType_restrict G' V hcover ?_
  rintro ⟨_ | _⟩
  · exact SheafOfModules.IsFiniteType.of_iso (R := W.toScheme.ringCatSheaf) e.symm
  · exact SheafOfModules.IsFiniteType.of_iso (R := U.toScheme.ringCatSheaf)
      (asIso ((Scheme.Modules.restrictFunctor U.ι).map i')).symm

end TauCeti.AlgebraicGeometry
