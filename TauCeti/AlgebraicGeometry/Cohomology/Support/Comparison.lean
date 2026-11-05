/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Support.LocalCohomology
import TauCeti.Algebra.Homology.LocalCohomology.Depth

/-!
# Local cohomology is cohomology with supports on `Spec R`

Let `R` be a Noetherian ring, `I` an ideal of `R` and `M` an `R`-module. This file proves that the
comparison map `H^q_I(M) ⟶ H^q_{V(I)}(Spec R, M^~)` from Mathlib's local cohomology (the colimit
of `Ext^q_R(R ⧸ Iᵏ, M)`) to cohomology with supports in `V(I)` is bijective in every degree, and
packages it as a natural `R`-linear isomorphism (Stacks, Lemma 51.2.1 (0A6T)).

The proof is dimension shifting, simultaneously for all modules. Degree zero holds for every
finitely generated ideal. Embed `M` into an injective module `J` with cokernel `N`. Both
`H^{q+1}_I(J)` and `H^{q+1}_{V(I)}(Spec R, J^~)` vanish (`J^~` is flasque because `R` is
Noetherian), so on both sides the connecting maps `H^{q+1}(N) ⟶ H^{q+2}(M)` are bijective and
`H^0(N) ⟶ H^1(M)` is surjective with kernel the image of `H^0(J)`. The comparison map commutes
with the connecting maps and is natural, which gives the induction step.

Over a non-Noetherian ring no such comparison is asserted: finite generation of `I` alone does
not identify the two derived functors.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.Modules.bijective_localCohomologyToCohomologyWithSupport`: the
  comparison map is bijective in every degree;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.localCohomologyIsoCohomologyWithSupport I q M`: the
  `R`-linear isomorphism `H^q_I(M) ≅ H^q_{V(I)}(Spec R, M^~)`;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.localCohomology_module_comparison`: the natural
  `R`-linear isomorphism, natural in `M`;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.rightDerivedPowerTorsionIsoCohomologyWithSupport`:
  with `TauCeti.Supports.localCohomologyIsoRightDerived`, the derived functors of the `I`-power
  torsion compute cohomology with supports in `V(I)` (Stacks, Lemma 47.10.1 (0955)).

## References

* [Stacks, Lemma 47.10.1 (0955)](https://stacks.math.columbia.edu/tag/0955).
* [Stacks, Lemma 51.2.1 (0A6T)](https://stacks.math.columbia.edu/tag/0A6T).
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite _root_.AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace Scheme.Modules

variable {R : CommRingCat.{u}} {I : Ideal R}

/-- **The comparison map is bijective in every degree** over a Noetherian ring (Stacks, Lemma
51.2.1 (0A6T)). By induction on the degree, simultaneously for all modules: embed `M` into an
injective module `J` with cokernel `N`. Both sides vanish on `J` in positive degrees, so their
connecting maps shift degrees, and the comparison map commutes with them. In degree one this also
uses degree zero for `J` and `N`. -/
theorem bijective_localCohomologyToCohomologyWithSupport [IsNoetherianRing R] (hI : I.FG) :
    ∀ (q : ℕ) (M : ModuleCat.{u} R),
      Function.Bijective (localCohomologyToCohomologyWithSupport hI q M)
  | 0, M => bijective_localCohomologyToCohomologyWithSupport_zero hI M
  | q + 1, M => by
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    have : Module.Injective R S.X₂ :=
      Module.injective_module_of_injective_object (inj := (inferInstance : Injective S.X₂)) R _
    have hJ (n : ℕ) : Subsingleton ((localCohomology I (n + 1)).obj S.X₂) :=
      ModuleCat.isZero_iff_subsingleton.1 (Supports.isZero_localCohomology_succ_of_injective I _ n)
    have hδ (n : ℕ) (x : (localCohomology I (n + 1)).obj S.X₁) :
        ∃ w, Supports.localCohomologyδ I hS n w = x :=
      Supports.exists_localCohomologyδ_eq I hS n x (Subsingleton.elim _ _)
    have hcomm := localCohomologyToCohomologyWithSupport_δ hI hS q
    have IH := bijective_localCohomologyToCohomologyWithSupport hI q
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨w, rfl⟩ := hδ q x
      rw [hcomm] at hx
      obtain ⟨v, hv⟩ : ∃ v, (localCohomology I q).map S.g v = w := by
        cases q with
        | zero =>
          obtain ⟨v, hv⟩ :=
            (exact_cohomologyWithSupportMap_cohomologyWithSupportδ _ (shortExact_map_tilde hS) 0 1
              rfl _).1 hx
          obtain ⟨v, rfl⟩ := (IH S.X₂).2 v
          refine ⟨v, (IH S.X₃).1 ?_⟩
          rw [localCohomologyToCohomologyWithSupport_naturality]
          exact hv
        | succ q =>
          refine ⟨0, (map_zero _).trans ((IH S.X₃).1 ?_).symm⟩
          rw [map_zero]
          exact (bijective_cohomologyWithSupportδ_tilde_succ _ hS q).1 (hx.trans (map_zero _).symm)
      rw [← hv]
      exact ConcreteCategory.congr_hom
        (Supports.localCohomology_map_g_comp_localCohomologyδ I hS q) v
    · obtain ⟨z, rfl⟩ : ∃ z, cohomologyWithSupportδ (zeroLocusCloseds I) (shortExact_map_tilde hS)
          q (q + 1) rfl z = y := by
        cases q with
        | zero => exact surjective_cohomologyWithSupportδ_tilde_zero _ hS y
        | succ q => exact (bijective_cohomologyWithSupportδ_tilde_succ _ hS q).2 y
      obtain ⟨w, rfl⟩ := (IH S.X₃).2 z
      exact ⟨_, hcomm w⟩

variable (I) in
/-- **Local cohomology is cohomology with supports** (Stacks, Lemma 51.2.1 (0A6T)): over a
Noetherian ring `R`, the comparison map is an `R`-linear isomorphism
`H^q_I(M) ≅ H^q_{V(I)}(Spec R, M^~)`, where `R` acts on the right through `R ≅ Γ(Spec R, ⊤)`. It
is natural in `M` by `localCohomologyToCohomologyWithSupport_naturality`. -/
noncomputable def localCohomologyIsoCohomologyWithSupport [IsNoetherianRing R] (q : ℕ)
    (M : ModuleCat.{u} R) :
    (localCohomology I q).obj M ≅ (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj
      (ModuleCat.of Γ(Spec R, ⊤) (cohomologyWithSupport (zeroLocusCloseds I) (tilde M) q)) :=
  have h : ⇑(localCohomologyToCohomologyWithSupportHom (IsNoetherian.noetherian I) q M).hom =
      localCohomologyToCohomologyWithSupport (IsNoetherian.noetherian I) q M :=
    funext (localCohomologyToCohomologyWithSupportHom_apply _ q M)
  (LinearEquiv.ofBijective
    (localCohomologyToCohomologyWithSupportHom (IsNoetherian.noetherian I) q M).hom
    (h ▸ bijective_localCohomologyToCohomologyWithSupport _ q M)).toModuleIso

@[simp]
lemma localCohomologyIsoCohomologyWithSupport_hom_apply [IsNoetherianRing R] (q : ℕ)
    (M : ModuleCat.{u} R) (x : (localCohomology I q).obj M) :
    (localCohomologyIsoCohomologyWithSupport I q M).hom x =
      localCohomologyToCohomologyWithSupport (IsNoetherian.noetherian I) q M x :=
  localCohomologyToCohomologyWithSupportHom_apply _ q M x

variable (I) in
/-- **The geometric comparison** `localCohomology_module_comparison` (Stacks, Lemma 51.2.1
(0A6T)): for a Noetherian ring `R`, an ideal `I` and an `R`-module `M`, the native local
cohomology `H^q_I(M)` is `R`-linearly isomorphic to the cohomology `H^q_{V(I)}(Spec R, M^~)` with
supports in `V(I)`, naturally in `M`. -/
theorem localCohomology_module_comparison [IsNoetherianRing R] (q : ℕ) :
    ∃ e : ∀ M : ModuleCat.{u} R, (localCohomology I q).obj M ≅
        (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj
          (ModuleCat.of Γ(Spec R, ⊤) (cohomologyWithSupport (zeroLocusCloseds I) (tilde M) q)),
      ∀ {M M' : ModuleCat.{u} R} (f : M ⟶ M') (x : (localCohomology I q).obj M),
        (e M').hom ((localCohomology I q).map f x) =
          cohomologyWithSupportMap (zeroLocusCloseds I) (tilde.map f) q ((e M).hom x) :=
  ⟨localCohomologyIsoCohomologyWithSupport I q, fun f x ↦
    (localCohomologyIsoCohomologyWithSupport_hom_apply q _ _).trans
      ((localCohomologyToCohomologyWithSupport_naturality _ q f x).trans
        (congrArg _ (localCohomologyIsoCohomologyWithSupport_hom_apply q _ x).symm))⟩

variable (I) in
/-- **Derived power torsion is cohomology with supports** (Stacks, Lemma 47.10.1 (0955)): over a
Noetherian ring, the right-derived functors of the `I`-power torsion `Γ_I` compute cohomology with
supports in `V(I)` on `Spec R`, `R^q Γ_I(M) ≅ H^q_{V(I)}(Spec R, M^~)`. -/
noncomputable def rightDerivedPowerTorsionIsoCohomologyWithSupport [IsNoetherianRing R] (q : ℕ)
    (M : ModuleCat.{u} R) :
    ((Supports.powerTorsionFunctor I).rightDerived q).obj M ≅
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj
        (ModuleCat.of Γ(Spec R, ⊤) (cohomologyWithSupport (zeroLocusCloseds I) (tilde M) q)) :=
  ((Supports.localCohomologyIsoRightDerived I q).app M).symm ≪≫
    localCohomologyIsoCohomologyWithSupport I q M

end Scheme.Modules

end AlgebraicGeometry

end TauCeti
