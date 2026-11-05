/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
import TauCeti.AlgebraicGeometry.Modules.Sheaf

/-!
# The base change morphism for the pushforward of modules

Consider a commutative square of schemes `g' ≫ f = f' ≫ g`, with `g' : X' ⟶ X`, `f : X ⟶ S`,
`f' : X' ⟶ S'` and `g : S' ⟶ S`. The base change morphism `g^* f_* M ⟶ f'_* g'^* M` of sheaves of
modules (`Scheme.Modules.pushforwardBaseChange`) is the mate, under the pullback-pushforward
adjunctions of `g` and `g'`, of the identification `g_* f'_* = (f' ≫ g)_* = (g' ≫ f)_* = f_* g'_*`.
On sections it sends the pullback along `g` of a section `s` of `f_* M` over an open `W` of `S`,
restricted to an open `W' ⊆ g⁻¹ W`, to the pullback of `s` along `g'` restricted to `f'⁻¹ W'`
(`Scheme.Modules.pushforwardBaseChange_app_app_pullbackSectionsLE`).

That the base change morphism is an isomorphism for quasi-coherent sheaves, a cartesian square,
quasi-compact quasi-separated `f` and flat `g` is
`Scheme.Modules.isIso_pushforwardBaseChange_app`, in
`TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.BaseChange`.

Without flatness one can still check the isomorphism over affine opens. When `f_* M` is
quasi-coherent, over affine opens `W' ≤ g⁻¹ W` the sections of `g^* f_* M` over `W'` are
`Γ(S', W') ⊗_{Γ(S, W)} Γ(X, f⁻¹ W; M)` (`Scheme.Hom.pullbackSectionsLEEquiv`), on which the base
change morphism is `r ⊗ s ↦ r • g'^* s`. So the direct image commutes with base change along `g` as
soon as these maps are bijective for a basis of such `W'`
(`Scheme.Modules.isIso_pushforwardBaseChange_app_of_bijective`).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.pushforwardBaseChange`: the base change morphism
  `g^* f_* ⟶ f'_* g'^*` of a commutative square;
* `AlgebraicGeometry.Scheme.Modules.unit_comp_pushforward_map_pushforwardBaseChange_app`: its
  characterization through the units of the adjunctions, and
  `AlgebraicGeometry.Scheme.Modules.pushforwardBaseChange_app_app_pullbackSectionsLE`, its effect on
  pulled-back sections;
* `AlgebraicGeometry.Scheme.Modules.isIso_pushforwardBaseChange_app_of_bijective`: the base change
  morphism is an isomorphism once it is bijective on the sections over a basis of affine opens.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3.
* [The Stacks Project, Lemma 30.5.2](https://stacks.math.columbia.edu/tag/02KH).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped ChangeOfRings TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}

/-- The **base change morphism** `g^* f_* M ⟶ f'_* g'^* M` of a commutative square of schemes
`g' ≫ f = f' ≫ g`: the mate, under the pullback-pushforward adjunctions of `g` and `g'`, of the
identification `f_* g'_* = (g' ≫ f)_* = (f' ≫ g)_* = g_* f'_*`. It is an isomorphism on
quasi-coherent sheaves when the square is cartesian, `f` is quasi-compact and quasi-separated and
`g` is flat (`Scheme.Modules.isIso_pushforwardBaseChange_app`). -/
def pushforwardBaseChange (w : CommSq g' f' f g) :
    pushforward f ⋙ pullback g ⟶ pullback g' ⋙ pushforward f' :=
  (mateEquiv (pullbackPushforwardAdjunction g') (pullbackPushforwardAdjunction g)).symm
    ((pushforwardComp g' f).hom ≫ (pushforwardCongr w.w).hom ≫ (pushforwardComp f' g).inv)

/-- The base change morphism is characterized by its adjunct: the unit of `g^* ⊣ g_*` followed by
`g_*` of the base change morphism is `f_*` of the unit of `g'^* ⊣ g'_*`, followed by the
identification `f_* g'_* = g_* f'_*`. -/
@[reassoc]
lemma unit_comp_pushforward_map_pushforwardBaseChange_app (w : CommSq g' f' f g) (M : X.Modules) :
    (pullbackPushforwardAdjunction g).unit.app ((pushforward f).obj M) ≫
      (pushforward g).map ((pushforwardBaseChange w).app M) =
    (pushforward f).map ((pullbackPushforwardAdjunction g').unit.app M) ≫
      ((pushforwardComp g' f).hom ≫ (pushforwardCongr w.w).hom ≫
        (pushforwardComp f' g).inv).app ((pullback g').obj M) :=
  (unit_mateEquiv_symm (G := pushforward f) (H := pushforward f')
    (pullbackPushforwardAdjunction g') (pullbackPushforwardAdjunction g)
    ((pushforwardComp g' f).hom ≫ (pushforwardCongr w.w).hom ≫ (pushforwardComp f' g).inv) M).symm

/-- On sections over the preimage of an open `W` of `S`, the base change morphism sends the
pullback along `g` of a section `s` of `f_* M` over `W` to the pullback of `s` along `g'`, read
over `(f' ≫ g)⁻¹ W = (g' ≫ f)⁻¹ W`. -/
lemma pushforwardBaseChange_app_app_pullbackSections (w : CommSq g' f' f g) (M : X.Modules)
    (W : S.Opens) (s : Γ((pushforward f).obj M, W)) :
    ((pushforwardBaseChange w).app M).app (g ⁻¹ᵁ W)
        (g.pullbackSections ((pushforward f).obj M) W s) =
      ((pullback g').obj M).presheaf.map (eqToHom (by rw [← Scheme.Hom.comp_preimage, ← w.w,
        Scheme.Hom.comp_preimage])).op (g'.pullbackSections M (f ⁻¹ᵁ W) s) := by
  have h := congr($(unit_comp_pushforward_map_pushforwardBaseChange_app w M).app W s)
  simp only [Functor.comp_obj, pushforward_obj_obj, Hom.comp_app, pushforward_map_app,
    NatTrans.comp_app, pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app,
    pushforwardComp_inv_app_app] at h
  -- `h` evaluates composites of morphisms of abelian groups, some of them identities, at `s`;
  -- the pushforward types block rewriting with `comp_apply`, and `h` is the goal after unfolding
  -- the composites and `pullbackSections`.
  exact (congrArg _ (Scheme.Hom.pullbackSections_apply g _ W s)).trans
    (h.trans (congrArg _ (Scheme.Hom.pullbackSections_apply g' M (f ⁻¹ᵁ W) s).symm))

/-- The base change morphism sends the pullback along `g` of a section `s` of `f_* M` over an open
`W` of `S`, restricted to an open `W' ⊆ g⁻¹ W` of `S'`, to the pullback of `s` along `g'` restricted
to `f'⁻¹ W'`. -/
lemma pushforwardBaseChange_app_app_pullbackSectionsLE (w : CommSq g' f' f g) (M : X.Modules)
    (W : S.Opens) (W' : S'.Opens) (h : W' ≤ g ⁻¹ᵁ W) (s : Γ((pushforward f).obj M, W)) :
    ((pushforwardBaseChange w).app M).app W'
        (g.pullbackSectionsLE ((pushforward f).obj M) W W' h s) =
      g'.pullbackSectionsLE M (f ⁻¹ᵁ W) (f' ⁻¹ᵁ W')
        (by rw [← Scheme.Hom.comp_preimage, w.w, Scheme.Hom.comp_preimage];
            exact f'.preimage_mono h) s := by
  have hn := PresheafOfModules.naturality_apply ((pushforwardBaseChange w).app M).val
    (homOfLE h).op (g.pullbackSections ((pushforward f).obj M) W s)
  refine ((congrArg _ (Scheme.Hom.pullbackSectionsLE_apply g _ W W' h s)).trans hn).trans ?_
  refine (congrArg _ (pushforwardBaseChange_app_app_pullbackSections w M W s)).trans ?_
  refine Eq.trans ?_ (Scheme.Hom.pullbackSectionsLE_apply g' M _ _ _ s).symm
  exact (((pullback g').obj M).presheaf.map_comp_apply _ _ _).symm

/-- **The base change morphism over an affine open.** Let `W' ≤ g⁻¹ W` be affine opens and let
`f_* M` be quasicoherent, so that the sections of `g^* f_* M` over `W'` are
`Γ(S', W') ⊗_{Γ(S, W)} Γ(X, f⁻¹ W; M)` (`Scheme.Hom.pullbackSectionsLEEquiv`). On them the
`Γ(S', W')`-linear base change morphism sends `1 ⊗ s` to the pullback of `s` along `g'`, restricted
to `f'⁻¹ W'`. So the direct image commutes with base change along `g` over `W'` exactly when the
extension `r ⊗ s ↦ r • g'^* s` of this map is bijective. -/
theorem pushforwardBaseChange_app_pullbackSectionsLEEquiv_one_tmul (w : CommSq g' f' f g)
    (M : X.Modules) [((pushforward f).obj M).IsQuasicoherent] {W : S.Opens} {W' : S'.Opens}
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hW'W : W' ≤ g ⁻¹ᵁ W)
    (s : Γ((pushforward f).obj M, W)) :
    ((pushforwardBaseChange w).app M).app W'
        (g.pullbackSectionsLEEquiv ((pushforward f).obj M) hW hW' hW'W
          ((1 : Γ(S', W')) ⊗ₜ[Γ(S, W), (g.appLE W W' hW'W).hom] s)) =
      g'.pullbackSectionsLE M (f ⁻¹ᵁ W) (f' ⁻¹ᵁ W')
        (by
          rw [← Scheme.Hom.comp_preimage, w.w, Scheme.Hom.comp_preimage]
          exact fun x hx ↦ hW'W hx)
        s := by
  rw [Scheme.Hom.pullbackSectionsLEEquiv_one_tmul,
    pushforwardBaseChange_app_app_pullbackSectionsLE]

/-- **Base change of a direct image, checked over affine opens.** Let `f_* M` be quasicoherent
and let `W' i ≤ g⁻¹ (W i)` be affine opens, with the `W' i` forming a basis of `S'` and the `W i`
affine. If for every `i` the `Γ(S', W' i)`-linear extension `r ⊗ s ↦ r • g'^* s` of the pullback
of sections `Γ(X, f⁻¹ (W i); M) → Γ(X', f'⁻¹ (W' i); g'^* M)` along `g'` is bijective, then the
direct image of `M` commutes with base change along `g`: the base change morphism
`g^* f_* M ⟶ f'_* g'^* M` is an isomorphism. -/
theorem isIso_pushforwardBaseChange_app_of_bijective (w : CommSq g' f' f g) (M : X.Modules)
    [((pushforward f).obj M).IsQuasicoherent] {ι : Type*} {W : ι → S.Opens} {W' : ι → S'.Opens}
    (hW : ∀ i, IsAffineOpen (W i)) (hW' : ∀ i, IsAffineOpen (W' i)) (hW'W : ∀ i, W' i ≤ g ⁻¹ᵁ W i)
    (hB : TopologicalSpace.Opens.IsBasis (Set.range W'))
    (Φ : ∀ i, (ModuleCat.extendScalars (g.appLE (W i) (W' i) (hW'W i)).hom).obj
        (.of Γ(S, W i) Γ((pushforward f).obj M, W i)) →ₗ[Γ(S', W' i)]
      Γ((pushforward f').obj ((pullback g').obj M), W' i))
    (hΦ : ∀ i s,
      Φ i ((1 : Γ(S', W' i)) ⊗ₜ[Γ(S, W i),(g.appLE (W i) (W' i) (hW'W i)).hom] s) =
        g'.pullbackSectionsLE M (f ⁻¹ᵁ W i) (f' ⁻¹ᵁ W' i)
          (by
            rw [← Scheme.Hom.comp_preimage, w.w, Scheme.Hom.comp_preimage]
            exact fun x hx ↦ hW'W i hx)
          s)
    (h : ∀ i, Function.Bijective (Φ i)) : IsIso ((pushforwardBaseChange w).app M) := by
  refine Hom.isIso_of_isBasis _ hB fun i ↦ (ConcreteCategory.isIso_iff_bijective _).mpr ?_
  let e := g.pullbackSectionsLEEquiv ((pushforward f).obj M) (hW i) (hW' i) (hW'W i)
  -- the base change morphism after `e` is a `Γ(S', W' i)`-linear map agreeing with `Φ i` on the
  -- elements `1 ⊗ s`, hence equal to it
  let Ψ : (ModuleCat.extendScalars (g.appLE (W i) (W' i) (hW'W i)).hom).obj
        (.of Γ(S, W i) Γ((pushforward f).obj M, W i)) →ₗ[Γ(S', W' i)]
      Γ((pushforward f').obj ((pullback g').obj M), W' i) :=
    { toFun x := ((pushforwardBaseChange w).app M).app (W' i) (e x)
      map_add' x y := by rw [map_add, map_add]
      map_smul' r x := by rw [LinearEquiv.map_smul, Hom.app_smul, RingHom.id_apply] }
  have hΨ : Φ i = Ψ := by
    have := ModuleCat.ExtendScalars.hom_ext
      (N := ModuleCat.of Γ(S', W' i) Γ((pushforward f').obj ((pullback g').obj M), W' i))
      (α := ConcreteCategory.ofHom (C := ModuleCat Γ(S', W' i)) (Φ i))
      (β := ConcreteCategory.ofHom (C := ModuleCat Γ(S', W' i)) Ψ) fun s ↦ by
        change Φ i _ = ((pushforwardBaseChange w).app M).app (W' i) (e _)
        exact (hΦ i s).trans (pushforwardBaseChange_app_pullbackSectionsLEEquiv_one_tmul w M
          (hW i) (hW' i) (hW'W i) s).symm
    exact congrArg (ConcreteCategory.hom (C := ModuleCat Γ(S', W' i))) this
  have hc : ⇑(((pushforwardBaseChange w).app M).app (W' i)) = Φ i ∘ e.symm := by
    funext y
    rw [hΨ]
    change _ = ((pushforwardBaseChange w).app M).app (W' i) (e (e.symm y))
    rw [LinearEquiv.apply_symm_apply]
  rw [hc]
  exact (h i).comp e.symm.bijective


end AlgebraicGeometry.Scheme.Modules
