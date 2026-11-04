/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
import Mathlib.CategoryTheory.Adjunction.Mates
import TauCeti.AlgebraicGeometry.Modules.Sheaf

/-!
# The base change morphism of a direct image

For a commutative square of schemes

```text
  X' --g'--> X
  |          |
  π'         π
  v          v
  Y' --f---> Y
```

there is a canonical base change morphism `f^* π_* M ⟶ π'_* g'^* M` of `𝒪_{Y'}`-modules, natural
in the `𝒪_X`-module `M`. It is the mate, through the pullback–pushforward adjunctions of `g'` and
`f`, of the identification `π_* g'_* = (g' ≫ π)_* = (π' ≫ f)_* = f_* π'_*`. Saying that the
direct image of `M` *commutes with base change along `f`* means that this morphism is an
isomorphism.

On sections, the base change morphism sends the pullback along `f` of a section `s` of `π_* M`
over `U`, that is of `M` over `π⁻¹ U`, to the pullback of `s` along `g'`, restricted to
`π'⁻¹ (f⁻¹ U) ≤ g'⁻¹ (π⁻¹ U)`
(`TauCeti.AlgebraicGeometry.pushforwardBaseChange_app_pullbackSections`).

To check that it is an isomorphism one may work on a basis of opens: a morphism of sheaves of
modules is an isomorphism as soon as it is bijective on the sections over every open of a basis
(`AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_bijective_app_of_isBasis`). When `π_* M` is
quasicoherent, over an affine open `V ≤ f⁻¹ U` with `U` affine the source has sections
`Γ(Y', V) ⊗_{Γ(Y, U)} Γ(X, π⁻¹ U; M)` (`Scheme.Hom.pullbackSectionsLEEquiv`), on which the base
change morphism is `r ⊗ s ↦ r • g'^* s`. So the direct image commutes with base change along `f`
as soon as these maps are bijective for a basis of such `V`
(`TauCeti.AlgebraicGeometry.isIso_pushforwardBaseChange_app_of_bijective`). This reduces the
base change property of a direct image to a statement about sections over affine opens, where
it is computed by cohomology and base change.

## Main declarations

* `TauCeti.AlgebraicGeometry.pushforwardBaseChange`: the base change morphism
  `f^* π_* ⟶ π'_* g'^*`, as a natural transformation.
* `TauCeti.AlgebraicGeometry.pushforwardBaseChange_app_pullbackSections`: its value on pulled-back
  sections.
* `TauCeti.AlgebraicGeometry.pushforwardBaseChange_app_pullbackSectionsLEEquiv_one_tmul`: its
  value over affine opens.
* `TauCeti.AlgebraicGeometry.isIso_pushforwardBaseChange_app_of_bijective`: the direct image
  commutes with base change once it does so on the sections over a basis of affine opens.

## References

* R. Hartshorne, *Algebraic Geometry*, III.9.3 (the base change morphism).
* The Stacks Project, Tag 02N6 (base change maps).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped ChangeOfRings TensorProduct

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

open _root_.AlgebraicGeometry.Scheme.Modules

variable {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X} {π' : X' ⟶ Y'} {π : X ⟶ Y} {f : Y' ⟶ Y}

/-- The **base change morphism** `f^* π_* M ⟶ π'_* g'^* M` of a commutative square
`g' ≫ π = π' ≫ f` of schemes, natural in the `𝒪_X`-module `M`. It is the mate, for the
pullback–pushforward adjunctions of `g'` and `f`, of the canonical identification
`π_* g'_* = f_* π'_*`. The direct image of `M` commutes with base change along `f` when its
component at `M` is an isomorphism. -/
def pushforwardBaseChange (sq : CommSq g' π' π f) :
    pushforward π ⋙ pullback f ⟶ pullback g' ⋙ pushforward π' :=
  (mateEquiv (pullbackPushforwardAdjunction g') (pullbackPushforwardAdjunction f)).symm
    ((pushforwardComp g' π).hom ≫ (pushforwardCongr sq.w).hom ≫ (pushforwardComp π' f).inv)

/-- The base change morphism of a commutative square, composed after the unit of `f`, is the
direct image along `π` of the unit of `g'`, read through `π_* g'_* = f_* π'_*`. -/
theorem unit_comp_pushforward_map_pushforwardBaseChange_app (sq : CommSq g' π' π f)
    (M : X.Modules) :
    (pullbackPushforwardAdjunction f).unit.app ((pushforward π).obj M) ≫
        (pushforward f).map ((pushforwardBaseChange sq).app M) =
      (pushforward π).map ((pullbackPushforwardAdjunction g').unit.app M) ≫
        ((pushforwardComp g' π).hom ≫ (pushforwardCongr sq.w).hom ≫
          (pushforwardComp π' f).inv).app ((pullback g').obj M) :=
  (unit_mateEquiv_symm (G := pushforward π) (H := pushforward π')
    (pullbackPushforwardAdjunction g') (pullbackPushforwardAdjunction f) _ M).symm

/-- **The base change morphism on sections.** For a section `s` of `π_* M` over `U`, that is a
section of `M` over `π⁻¹ U`, the base change morphism sends the pullback of `s` along `f` to the
pullback of `s` along `g'`, restricted to `π'⁻¹ (f⁻¹ U) = g'⁻¹ (π⁻¹ U)`. -/
theorem pushforwardBaseChange_app_pullbackSections (sq : CommSq g' π' π f) (M : X.Modules)
    (U : Y.Opens) (s : Γ((pushforward π).obj M, U)) :
    ((pushforwardBaseChange sq).app M).app (f ⁻¹ᵁ U)
        (f.pullbackSections ((pushforward π).obj M) U s) =
      g'.pullbackSectionsLE M (π ⁻¹ᵁ U) (π' ⁻¹ᵁ f ⁻¹ᵁ U)
        (by rw [← Scheme.Hom.comp_preimage, ← sq.w, Scheme.Hom.comp_preimage]) s := by
  have h := congr($(unit_comp_pushforward_map_pushforwardBaseChange_app sq M).app U s)
  -- the identifications `π_* g'_* = f_* π'_*` are restrictions along equalities of opens
  erw [Scheme.Hom.pullbackSections_apply, Scheme.Hom.pullbackSectionsLE_apply,
    Scheme.Hom.pullbackSections_apply]
  exact h

/-- **The base change morphism on restricted sections.** For an open `V ≤ f⁻¹ U`, the base change
morphism sends the pullback along `f` of a section `s` of `π_* M` over `U`, restricted to `V`, to
the pullback of `s` along `g'`, restricted to `π'⁻¹ V`. -/
theorem pushforwardBaseChange_app_pullbackSectionsLE (sq : CommSq g' π' π f) (M : X.Modules)
    (U : Y.Opens) {V : Y'.Opens} (hVU : V ≤ f ⁻¹ᵁ U) (s : Γ((pushforward π).obj M, U)) :
    ((pushforwardBaseChange sq).app M).app V
        (f.pullbackSectionsLE ((pushforward π).obj M) U V hVU s) =
      g'.pullbackSectionsLE M (π ⁻¹ᵁ U) (π' ⁻¹ᵁ V)
        (by
          rw [← Scheme.Hom.comp_preimage, sq.w, Scheme.Hom.comp_preimage]
          exact fun x hx ↦ hVU hx)
        s := by
  have hn := PresheafOfModules.naturality_apply ((pushforwardBaseChange sq).app M).val
    (homOfLE hVU).op (f.pullbackSections ((pushforward π).obj M) U s)
  have h := pushforwardBaseChange_app_pullbackSections sq M U s
  erw [Scheme.Hom.pullbackSectionsLE_apply g'] at h ⊢
  rw [Scheme.Hom.pullbackSectionsLE_apply f]
  refine hn.trans ?_
  -- both sides restrict the pullback of `s` along `g'` to `π'⁻¹ V`
  change ((pullback g').obj M).presheaf.map (homOfLE _).op
    (((pushforwardBaseChange sq).app M).app (f ⁻¹ᵁ U)
      (f.pullbackSections ((pushforward π).obj M) U s)) = _
  rw [h, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- **The base change morphism over an affine open.** Let `V ≤ f⁻¹ U` be affine opens and let
`π_* M` be quasicoherent, so that the sections of `f^* π_* M` over `V` are
`Γ(Y', V) ⊗_{Γ(Y, U)} Γ(X, π⁻¹ U; M)` (`Scheme.Hom.pullbackSectionsLEEquiv`). On them the
`Γ(Y', V)`-linear base change morphism sends `1 ⊗ s` to the pullback of `s` along `g'`, restricted
to `π'⁻¹ V`. So the direct image commutes with base change along `f` over `V` exactly when the
extension `r ⊗ s ↦ r • g'^* s` of this map is bijective. -/
theorem pushforwardBaseChange_app_pullbackSectionsLEEquiv_one_tmul (sq : CommSq g' π' π f)
    (M : X.Modules) [((pushforward π).obj M).IsQuasicoherent] {U : Y.Opens} {V : Y'.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    (s : Γ((pushforward π).obj M, U)) :
    ((pushforwardBaseChange sq).app M).app V
        (f.pullbackSectionsLEEquiv ((pushforward π).obj M) hU hV hVU
          ((1 : Γ(Y', V)) ⊗ₜ[Γ(Y, U), (f.appLE U V hVU).hom] s)) =
      g'.pullbackSectionsLE M (π ⁻¹ᵁ U) (π' ⁻¹ᵁ V)
        (by
          rw [← Scheme.Hom.comp_preimage, sq.w, Scheme.Hom.comp_preimage]
          exact fun x hx ↦ hVU hx)
        s := by
  rw [Scheme.Hom.pullbackSectionsLEEquiv_one_tmul,
    pushforwardBaseChange_app_pullbackSectionsLE]

/-- **Base change of a direct image, checked over affine opens.** Let `π_* M` be quasicoherent
and let `V i ≤ f⁻¹ (U i)` be affine opens, with the `V i` forming a basis of `Y'` and the `U i`
affine. If for every `i` the `Γ(Y', V i)`-linear extension `r ⊗ s ↦ r • g'^* s` of the pullback
of sections `Γ(X, π⁻¹ (U i); M) → Γ(X', π'⁻¹ (V i); g'^* M)` along `g'` is bijective, then the
direct image of `M` commutes with base change along `f`: the base change morphism
`f^* π_* M ⟶ π'_* g'^* M` is an isomorphism. -/
theorem isIso_pushforwardBaseChange_app_of_bijective (sq : CommSq g' π' π f) (M : X.Modules)
    [((pushforward π).obj M).IsQuasicoherent] {ι : Type*} {U : ι → Y.Opens} {V : ι → Y'.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (V i)) (hVU : ∀ i, V i ≤ f ⁻¹ᵁ U i)
    (hB : TopologicalSpace.Opens.IsBasis (Set.range V))
    (Φ : ∀ i, (ModuleCat.extendScalars (f.appLE (U i) (V i) (hVU i)).hom).obj
        (.of Γ(Y, U i) Γ((pushforward π).obj M, U i)) →ₗ[Γ(Y', V i)]
      Γ((pushforward π').obj ((pullback g').obj M), V i))
    (hΦ : ∀ i s,
      Φ i ((1 : Γ(Y', V i)) ⊗ₜ[Γ(Y, U i),(f.appLE (U i) (V i) (hVU i)).hom] s) =
        g'.pullbackSectionsLE M (π ⁻¹ᵁ U i) (π' ⁻¹ᵁ V i)
          (by
            rw [← Scheme.Hom.comp_preimage, sq.w, Scheme.Hom.comp_preimage]
            exact fun x hx ↦ hVU i hx)
          s)
    (h : ∀ i, Function.Bijective (Φ i)) : IsIso ((pushforwardBaseChange sq).app M) := by
  refine Hom.isIso_of_bijective_app_of_isBasis _ hB fun i ↦ ?_
  let e := f.pullbackSectionsLEEquiv ((pushforward π).obj M) (hU i) (hV i) (hVU i)
  -- the base change morphism after `e` is a `Γ(Y', V i)`-linear map agreeing with `Φ i` on the
  -- elements `1 ⊗ s`, hence equal to it
  let Ψ : (ModuleCat.extendScalars (f.appLE (U i) (V i) (hVU i)).hom).obj
        (.of Γ(Y, U i) Γ((pushforward π).obj M, U i)) →ₗ[Γ(Y', V i)]
      Γ((pushforward π').obj ((pullback g').obj M), V i) :=
    { toFun x := ((pushforwardBaseChange sq).app M).app (V i) (e x)
      map_add' x y := by rw [map_add, map_add]
      map_smul' r x := by rw [LinearEquiv.map_smul, Hom.app_smul, RingHom.id_apply] }
  have hΨ : Φ i = Ψ := by
    have := ModuleCat.ExtendScalars.hom_ext
      (N := ModuleCat.of Γ(Y', V i) Γ((pushforward π').obj ((pullback g').obj M), V i))
      (α := ConcreteCategory.ofHom (C := ModuleCat Γ(Y', V i)) (Φ i))
      (β := ConcreteCategory.ofHom (C := ModuleCat Γ(Y', V i)) Ψ) fun s ↦ by
        change Φ i _ = ((pushforwardBaseChange sq).app M).app (V i) (e _)
        exact (hΦ i s).trans (pushforwardBaseChange_app_pullbackSectionsLEEquiv_one_tmul sq M
          (hU i) (hV i) (hVU i) s).symm
    exact congrArg (ConcreteCategory.hom (C := ModuleCat Γ(Y', V i))) this
  have hc : ⇑(((pushforwardBaseChange sq).app M).app (V i)) = Φ i ∘ e.symm := by
    funext y
    rw [hΨ]
    change _ = ((pushforwardBaseChange sq).app M).app (V i) (e (e.symm y))
    rw [LinearEquiv.apply_symm_apply]
  rw [hc]
  exact (h i).comp e.symm.bijective

end

end TauCeti.AlgebraicGeometry
