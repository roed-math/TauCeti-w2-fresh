/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeProj.Map
public import TauCeti.Lookahead.RelativeProjClosedImmersion.Stubs

/-!
# The morphism of twisting sheaves induced by a morphism of graded algebras

Let `φ : B ⟶ A` be a morphism of graded algebras on a scheme `X` with quasi-coherent homogeneous
components, inducing `Proj_X(A) ⟶ Proj_X(B)` (`CategoryTheory.CommMon.relativeProjMap`). Over
every affine open `U` of `X`, the morphism of projective spectra
`Proj (⨁ n, Γ(Aₙ, U)) ⟶ Proj (⨁ n, Γ(Bₙ, U))` induces a morphism of twisting sheaves
(`AlgebraicGeometry.Proj.twistingSheafMap`). This file pushes them forward to morphisms
`𝒪(n) ⟶ (Proj_X(A) ⟶ Proj_X(B))_* (ι_U)_* 𝒪(n)` on `Proj_X(B)`, the components from which the
morphism `(Proj_X(A) ⟶ Proj_X(B))^* 𝒪(n) ⟶ 𝒪(n)` is glued. For `φ` the graded map `Sym A₁ ⟶ A`
of an algebra generated in degree one, that morphism exhibits the pullback of `𝒪(1)` along the
closed immersion `Proj_X(A) ⟶ Proj_X(Sym A₁)` as `𝒪(1)` (Stacks, Lemma 27.11.5 (01N1), on affine
charts).

## Main definitions

* `CategoryTheory.CommMon.relativeProjTwistingSheafMapChart φ hφ n U`: over the chart above an
  affine open `U`, the morphism `𝒪(n) ⟶ (Proj_X(A) ⟶ Proj_X(B))_* (ι_U)_* 𝒪(n)` induced by the
  morphism of twisting sheaves of `Proj (⨁ n, Γ(Aₙ, U)) ⟶ Proj (⨁ n, Γ(Bₙ, U))`.

## Main results

* `CategoryTheory.CommMon.ι_relativeProjMap`: on the chart over `U`, the morphism of relative
  `Proj`s is the morphism of projective spectra, with the charts written as the coprojections of
  the gluing diagrams, as the glued modules of the twisting sheaves use them.

## References

* [The Stacks Project, Lemma 27.11.5 (01N1)](https://stacks.math.columbia.edu/tag/01N1)
* [The Stacks Project, Section 27.15, Relative Proj](https://stacks.math.columbia.edu/tag/01NS)
-/

public section

open CategoryTheory Limits

namespace TauCeti

open _root_.AlgebraicGeometry ProjectiveSpectrum.TwistingSheaf

universe u

noncomputable section

section Localizations

variable {R S T W σ τ ψ ω : Type u} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  [CommRing S] [SetLike τ S] [AddSubgroupClass τ S]
  [CommRing T] [SetLike ψ T] [AddSubgroupClass ψ T]
  [CommRing W] [SetLike ω W] [AddSubgroupClass ω W]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ} {𝒟 : ℕ → ω}
  [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞] [GradedRing 𝒟]

/-- The maps of localizations along two composites of graded ring homomorphisms that agree are
equal, on the values of a family of elements of the localizations. -/
private theorem localizationsMap_comp_comm {U : TopologicalSpace.Opens (ProjectiveSpectrum.top 𝒜)}
    {f₁ : 𝒜 →+*ᵍ ℬ} {g₁ : ℬ →+*ᵍ 𝒟} {f₂ : 𝒜 →+*ᵍ 𝒞} {g₂ : 𝒞 →+*ᵍ 𝒟}
    (hf₁ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f₁)
    (hg₁ : HomogeneousIdeal.irrelevant 𝒟 ≤ (HomogeneousIdeal.irrelevant ℬ).map g₁)
    (hf₂ : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant 𝒜).map f₂)
    (hg₂ : HomogeneousIdeal.irrelevant 𝒟 ≤ (HomogeneousIdeal.irrelevant 𝒞).map g₂)
    (e : g₁.comp f₁ = g₂.comp f₂) (s : ∀ x : U, Localizations 𝒜 x.1) (z : ProjectiveSpectrum 𝒟)
    (h₁ : ProjectiveSpectrum.comap f₁ hf₁ (ProjectiveSpectrum.comap g₁ hg₁ z) ∈ U)
    (h₂ : ProjectiveSpectrum.comap f₂ hf₂ (ProjectiveSpectrum.comap g₂ hg₂ z) ∈ U) :
    localizationsMap g₁ hg₁ z (localizationsMap f₁ hf₁ _ (s ⟨_, h₁⟩)) =
      localizationsMap g₂ hg₂ z (localizationsMap f₂ hf₂ _ (s ⟨_, h₂⟩)) := by
  have k₁ := DFunLike.congr_fun (localizationsMap_comp f₁ hf₁ g₁ hg₁ z) (s ⟨_, h₁⟩)
  have k₂ := DFunLike.congr_fun (localizationsMap_comp f₂ hf₂ g₂ hg₂ z) (s ⟨_, h₂⟩)
  -- the two composites are equal, so the maps of localizations along them agree
  have key : ∀ (h h' : 𝒜 →+*ᵍ 𝒟) (_ : h = h')
      (hh : HomogeneousIdeal.irrelevant 𝒟 ≤ (HomogeneousIdeal.irrelevant 𝒜).map h)
      (hh' : HomogeneousIdeal.irrelevant 𝒟 ≤ (HomogeneousIdeal.irrelevant 𝒜).map h')
      (p : ProjectiveSpectrum.comap h hh z ∈ U) (p' : ProjectiveSpectrum.comap h' hh' z ∈ U),
      localizationsMap h hh z (s ⟨_, p⟩) = localizationsMap h' hh' z (s ⟨_, p'⟩) := by
    rintro h _ rfl _ _ _ _
    rfl
  exact (k₁.symm.trans (key _ _ e _ _ h₁ h₂)).trans k₂

end Localizations

variable {X : Scheme.{u}} {A B : CommMon (GradedObject ℕ X.Modules)}
  [∀ n, (A.X n).IsQuasicoherent] [∀ n, (B.X n).IsQuasicoherent] (φ : B ⟶ A)
  (hφ : ∀ U : X.Opens, IsAffineOpen U →
    HomogeneousIdeal.irrelevant (A.gradedSectionsGrading U) ≤
      (HomogeneousIdeal.irrelevant (B.gradedSectionsGrading U)).map
        (CommMon.gradedSectionsGradedHom φ U)) (n : ℤ)

/-- On the chart over an affine open `U`, the morphism of relative `Proj`s induced by `φ` is the
morphism of projective spectra induced by `φ`, with the charts written as the coprojections of the
gluing diagrams. -/
theorem _root_.CategoryTheory.CommMon.ι_relativeProjMap (U : X.AffineZariskiSite) :
    colimit.ι A.relativeProjGluingData.functor U ≫ CommMon.relativeProjMap φ hφ =
      Proj.map (CommMon.gradedSectionsGradedHom φ U.toOpens) (hφ U.toOpens U.2) ≫
        colimit.ι B.relativeProjGluingData.functor U :=
  CommMon.relativeProjCover_f_relativeProjMap φ hφ U

/-- Over the chart of `Proj_X(B)` above an affine open `U` of `X`, the morphism
`𝒪(n) ⟶ (Proj_X(A) ⟶ Proj_X(B))_* (ι_U)_* 𝒪(n)` given by the morphism of twisting sheaves of
`Proj (⨁ n, Γ(Aₙ, U)) ⟶ Proj (⨁ n, Γ(Bₙ, U))`. -/
def _root_.CategoryTheory.CommMon.relativeProjTwistingSheafMapChart (U : X.AffineZariskiSite) :
    (B.relativeProjTwistingSheafGlueData n).glued ⟶
      (Scheme.Modules.pushforward (X := colimit A.relativeProjGluingData.functor)
        (Y := colimit B.relativeProjGluingData.functor) (CommMon.relativeProjMap φ hφ)).obj
        ((Scheme.Modules.pushforward (colimit.ι A.relativeProjGluingData.functor U)).obj
          (Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n)) :=
  (B.relativeProjTwistingSheafGlueData n).π U ≫
    (Scheme.Modules.pushforward (colimit.ι B.relativeProjGluingData.functor U)).map
      (Proj.twistingSheafMap (CommMon.gradedSectionsGradedHom φ U.toOpens) (hφ U.toOpens U.2) n) ≫
    (Scheme.Modules.pushforwardComp
      (Proj.map (CommMon.gradedSectionsGradedHom φ U.toOpens) (hφ U.toOpens U.2))
      (colimit.ι B.relativeProjGluingData.functor U)).hom.app
        (Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n) ≫
    (Scheme.Modules.pushforwardCongr (CommMon.ι_relativeProjMap φ hφ U).symm).hom.app
      (Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n) ≫
    (Scheme.Modules.pushforwardComp (Z := colimit B.relativeProjGluingData.functor)
      (colimit.ι A.relativeProjGluingData.functor U) (CommMon.relativeProjMap φ hφ)).inv.app
        (Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n)

end

end TauCeti
