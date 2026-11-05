/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.Pushforward.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import TauCeti.AlgebraicGeometry.AffineScheme
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
import TauCeti.AlgebraicGeometry.Modules.Sheaf
import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Flat base change for the pushforward of quasi-coherent sheaves

Consider a commutative square of schemes `g' ≫ f = f' ≫ g`, with `g' : X' ⟶ X`, `f : X ⟶ S`,
`f' : X' ⟶ S'` and `g : S' ⟶ S`, and the base change morphism `g^* f_* M ⟶ f'_* g'^* M` of sheaves
of modules (`Scheme.Modules.pushforwardBaseChange`).

When the square is cartesian, `f` is quasi-compact and quasi-separated, `g` is flat and `M` is
quasi-coherent, the base change morphism is an isomorphism
(`Scheme.Modules.isIso_pushforwardBaseChange_app`). This is flat base change for the direct image
in degree zero. It suffices to check bijectivity on sections over the affine opens `W'` of `S'`
lying over affine opens `W` of `S`, since these form a basis
(`Scheme.Hom.isBasis_range_affineOpens_le_preimage`). There the source is the base change of
`Γ(f⁻¹ W, M)` from `Γ(S, W)` to `Γ(S', W')`, because `f_* M` is quasi-coherent and `W`, `W'` are
affine (`Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear` for the identity square on `g`).
So for any commutative square the base change morphism is bijective on the sections over `W'` as
soon as pulling back sections along `g'` exhibits the target as the same base change, since it is
compatible with both identifications
(`Scheme.Modules.bijective_pushforwardBaseChange_app_app_of_isBaseChange`, through
`IsBaseChange.bijective_of_comp_eq`). Under the hypotheses above this is flat base change of
sections over the quasi-compact quasi-separated open `f⁻¹ W`
(`Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear_of_isQuasiSeparated`).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.bijective_pushforwardBaseChange_app_app_of_isBaseChange`: the
  base change morphism is bijective on the sections over an affine open lying over an affine open
  when pulling back sections there is a base change;
* `AlgebraicGeometry.Scheme.Modules.bijective_pushforwardBaseChange_app_app`: flat base change on
  the sections over an affine open lying over an affine open;
* `AlgebraicGeometry.Scheme.Modules.isIso_pushforwardBaseChange_app`: **flat base change**, the
  base change morphism `g^* f_* M ⟶ f'_* g'^* M` is an isomorphism for quasi-compact
  quasi-separated `f`, flat `g` and quasi-coherent `M`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3.
* [The Stacks Project, Lemma 30.5.2](https://stacks.math.columbia.edu/tag/02KH).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}

/-- **Base change on sections over affine opens.** For a commutative square
`g' ≫ f = f' ≫ g`, a sheaf `M` on `X` with `f_* M` quasi-coherent, and affine opens `W` of `S` and
`W' ⊆ g⁻¹ W` of `S'`, the base change morphism is bijective on the sections over `W'` as soon as
pulling back sections along `g'`, as a `Γ(S, W)`-linear map `ψ`, exhibits `Γ(f'⁻¹ W', g'^* M)` as
the base change of `Γ(f⁻¹ W, M)` from `Γ(S, W)` to `Γ(S', W')`. -/
theorem bijective_pushforwardBaseChange_app_app_of_isBaseChange (w : CommSq g' f' f g)
    (M : X.Modules) [((pushforward f).obj M).IsQuasicoherent] {W : S.Opens}
    (hW : IsAffineOpen W) {W' : S'.Opens} (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ W)
    [Algebra Γ(S, W) Γ(S', W')] (halg : algebraMap Γ(S, W) Γ(S', W') = (g.appLE W W' h).hom)
    [Module Γ(S, W) Γ((pushforward f').obj ((pullback g').obj M), W')]
    [IsScalarTower Γ(S, W) Γ(S', W') Γ((pushforward f').obj ((pullback g').obj M), W')]
    (ψ : Γ((pushforward f).obj M, W) →ₗ[Γ(S, W)]
      Γ((pushforward f').obj ((pullback g').obj M), W'))
    (hψ : ∀ s, ψ s = g'.pullbackSectionsLE M (f ⁻¹ᵁ W) (f' ⁻¹ᵁ W')
      (by rw [← Scheme.Hom.comp_preimage, w.w, Scheme.Hom.comp_preimage]
          exact f'.preimage_mono h) s)
    (hM : IsBaseChange Γ(S', W') ψ) :
    Function.Bijective (((pushforwardBaseChange w).app M).app W') := by
  obtain rfl : ‹Algebra Γ(S, W) Γ(S', W')› = (g.appLE W W' h).hom.toAlgebra :=
    Algebra.algebra_ext _ _ fun r ↦ by rw [halg]; rfl
  let : Algebra Γ(S, W) Γ(S', W') := (g.appLE W W' h).hom.toAlgebra
  -- Both sides are base changes of `Γ(f⁻¹ W, M) = Γ(W, f_* M)` from `Γ(S, W)` to `Γ(S', W')`,
  -- and the base change morphism is compatible with the two base-change maps. The target is one
  -- by hypothesis, and the source through the identity square on `g`, whose rings act through
  -- identities.
  let N := (pushforward f).obj M
  let : Module Γ(S, W) Γ((pullback g).obj N, W') := Module.compHom _ (algebraMap Γ(S, W) Γ(S', W'))
  have : IsScalarTower Γ(S, W) Γ(S', W') Γ((pullback g).obj N, W') :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  let alg₁ : Algebra Γ(S, W) Γ(S, W) := (Scheme.Hom.appLE (𝟙 S) W W le_rfl).hom.toAlgebra
  have hid (Y : Scheme.{u}) (V : Y.Opens) : Scheme.Hom.appLE (𝟙 Y) V V le_rfl = 𝟙 _ :=
    (Scheme.Hom.appLE_eq_app (𝟙 Y)).trans (Scheme.Hom.id_app V)
  have t₁ : @IsScalarTower Γ(S, W) Γ(S, W) Γ(N, W) alg₁.toSMul _ _ :=
    @IsScalarTower.of_algebraMap_smul _ _ _ _ _ alg₁ _ _ fun r n ↦ by
      rw [RingHom.algebraMap_toAlgebra, hid]
      rfl
  let alg₂ : Algebra Γ(S', W') Γ(S', W') := (Scheme.Hom.appLE (𝟙 S') W' W' le_rfl).hom.toAlgebra
  have t₂ : @IsScalarTower Γ(S', W') Γ(S', W') Γ((pullback g).obj N, W') alg₂.toSMul _ _ :=
    @IsScalarTower.of_algebraMap_smul _ _ _ _ _ alg₂ _ _ fun r n ↦ by
      rw [RingHom.algebraMap_toAlgebra, hid]
      rfl
  have hα := Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear g N
    (IsPullback.id_vert g) hW hW' h (UX := W) le_rfl hW (UY := W') (by simpa using h)
  -- The base change map on sections over `W'` is linear over `Γ(S', W')` and compatible with
  -- the two pullbacks of sections.
  let φ : Γ((pullback g).obj N, W') →ₗ[Γ(S', W')]
      Γ((pushforward f').obj ((pullback g').obj M), W') :=
    { toFun := ((pushforwardBaseChange w).app M).app W'
      map_add' := map_add _
      map_smul' := Hom.app_smul _ }
  exact IsBaseChange.bijective_of_comp_eq hα hM φ fun s ↦
    (congrArg φ (Scheme.Hom.pullbackSectionsLEBaseLinear_apply g N _ h _ _ _ s)).trans
      ((pushforwardBaseChange_app_app_pullbackSectionsLE w M W W' h s).trans (hψ s).symm)

/-- **Flat base change on sections over affine opens.** For a cartesian square
`g' ≫ f = f' ≫ g` with `f` quasi-compact and quasi-separated and `g` flat, a quasi-coherent sheaf
`M` on `X`, and affine opens `W` of `S` and `W' ⊆ g⁻¹ W` of `S'`, the base change morphism is
bijective on the sections over `W'`. -/
theorem bijective_pushforwardBaseChange_app_app (H : IsPullback g' f' f g) [QuasiCompact f]
    [QuasiSeparated f] [Flat g] (M : X.Modules) [M.IsQuasicoherent] {W : S.Opens}
    (hW : IsAffineOpen W) {W' : S'.Opens} (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ W) :
    Function.Bijective (((pushforwardBaseChange H.toCommSq).app M).app W') := by
  -- the sections of `f'_* g'^* M` over `W'` are a base change by flat base change over `W' ⟶ W`
  have hUY : f' ⁻¹ᵁ W' = g' ⁻¹ᵁ (f ⁻¹ᵁ W) ⊓ f' ⁻¹ᵁ W' := by
    refine (inf_eq_right.mpr ?_).symm
    rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
    exact f'.preimage_mono h
  let : Algebra Γ(S, W) Γ(S', W') := (g.appLE W W' h).hom.toAlgebra
  let : Module Γ(S, W) Γ(M, f ⁻¹ᵁ W) :=
    (inferInstance : Module Γ(S, W) Γ((pushforward f).obj M, W))
  let : Algebra Γ(S, W) Γ(X, f ⁻¹ᵁ W) := (f.appLE W (f ⁻¹ᵁ W) le_rfl).hom.toAlgebra
  have : IsScalarTower Γ(S, W) Γ(X, f ⁻¹ᵁ W) Γ(M, f ⁻¹ᵁ W) := .of_algebraMap_smul fun r m ↦ by
    rw [RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE_eq_app]
    rfl
  let : Module Γ(S', W') Γ((pullback g').obj M, f' ⁻¹ᵁ W') :=
    (inferInstance : Module Γ(S', W') Γ((pushforward f').obj ((pullback g').obj M), W'))
  let : Algebra Γ(S', W') Γ(X', f' ⁻¹ᵁ W') := (f'.appLE W' (f' ⁻¹ᵁ W') le_rfl).hom.toAlgebra
  have : IsScalarTower Γ(S', W') Γ(X', f' ⁻¹ᵁ W') Γ((pullback g').obj M, f' ⁻¹ᵁ W') :=
    .of_algebraMap_smul fun r m ↦ by
      rw [RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE_eq_app]
      rfl
  let : Module Γ(S, W) Γ((pushforward f').obj ((pullback g').obj M), W') :=
    Module.compHom _ (algebraMap Γ(S, W) Γ(S', W'))
  have : IsScalarTower Γ(S, W) Γ(S', W') Γ((pushforward f').obj ((pullback g').obj M), W') :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  let : Module Γ(S, W) Γ((pullback g').obj M, f' ⁻¹ᵁ W') :=
    (inferInstance : Module Γ(S, W) Γ((pushforward f').obj ((pullback g').obj M), W'))
  have : IsScalarTower Γ(S, W) Γ(S', W') Γ((pullback g').obj M, f' ⁻¹ᵁ W') :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  exact bijective_pushforwardBaseChange_app_app_of_isBaseChange H.toCommSq M hW hW' h rfl _
    (Scheme.Hom.pullbackSectionsLEBaseLinear_apply g' M _ h _ _ _)
    (Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear_of_isQuasiSeparated g' M H
      hW hW' h (UX := f ⁻¹ᵁ W) le_rfl (f.isCompact_preimage hW.isCompact)
      (f.isQuasiSeparated_preimage hW.isQuasiSeparated) hUY)

/-- **Flat base change for the direct image of a quasi-coherent sheaf.** For a cartesian square
of schemes `g' ≫ f = f' ≫ g`, with `f : X ⟶ S` quasi-compact and quasi-separated and `g : S' ⟶ S`
flat, and a quasi-coherent sheaf `M` on `X`, the base change morphism
`g^* f_* M ⟶ f'_* g'^* M` is an isomorphism. -/
theorem isIso_pushforwardBaseChange_app (H : IsPullback g' f' f g) [QuasiCompact f]
    [QuasiSeparated f] [Flat g] (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((pushforwardBaseChange H.toCommSq).app M) :=
  Hom.isIso_of_isBasis _ g.isBasis_range_affineOpens_le_preimage fun i ↦
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_pushforwardBaseChange_app_app H M i.1.2.2 i.1.1.2 i.2)

end AlgebraicGeometry.Scheme.Modules
