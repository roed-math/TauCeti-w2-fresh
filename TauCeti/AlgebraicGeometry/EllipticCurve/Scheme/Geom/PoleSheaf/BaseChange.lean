/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PoleSheaf.DirectImage
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PositiveDegree.BaseChange

/-!
# `π_*𝒪_E(n[0])` commutes with base change

Let `E` be an elliptic curve over a scheme `S`, with structure morphism `π : E ⟶ S`, let
`f : S' ⟶ S` be a morphism of schemes and let `E'` over `S'` be the base change of `E` along `f`,
given by a pullback square `hg` with projection `g : E' ⟶ E`. This file shows that for `n > 0` the
base change morphism `f^* π_* 𝒪_E(n[0]) ⟶ π'_* g^* 𝒪_E(n[0])` is an isomorphism
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.isIso_pushforwardBaseChange_app_poleSheaf`).
This is the positive-degree base change theorem
`EllipticCurveGeom.isIso_pushforwardBaseChange_app_of_forall_eulerDegree_pos`
for `𝒪_E(n[0])`, which has degree `n` on every fibre
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.eulerDegree_pullback_snd_poleSheaf`).
Since `g^* 𝒪_E(n[0])` is `𝒪_{E'}(n[0])`
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.pullback_mk_poleSheaf_of_isPullback`), the formation
of `π_* 𝒪_E(n[0])` commutes with arbitrary base change.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isIso_pushforwardBaseChange_app_poleSheaf`: for
  `n > 0` the base change morphism of `π_*𝒪_E(n[0])` along any morphism of schemes is an
  isomorphism.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.nonempty_pullback_pushforward_poleSheaf_iso`:
  hence `f^* π_* 𝒪_E(n[0]) ≅ π'_* 𝒪_{E'}(n[0])`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

open Scheme.Modules

namespace EllipticCurveGeom

variable {S S' : Scheme.{u}} {E : EllipticCurveGeom S} {E' : EllipticCurveGeom S'}
  {g : E'.carrier ⟶ E.carrier} {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f)

/-- **`π_*𝒪_E(n[0])` commutes with base change.** Let `E'` over `S'` be the base change of the
elliptic curve `E` over `S` along `f : S' ⟶ S`, with projection `g : E' ⟶ E`. For `n > 0` the
base change morphism `f^* π_* 𝒪_E(n[0]) ⟶ π'_* g^* 𝒪_E(n[0])` is an isomorphism. -/
theorem isIso_pushforwardBaseChange_app_poleSheaf {n : ℕ} (hn : 0 < n) :
    IsIso ((pushforwardBaseChange hg.toCommSq).app (E.poleSheaf n).obj) :=
  isIso_pushforwardBaseChange_app_of_forall_eulerDegree_pos hg fun Ω _ _ ξ ↦ by
    rw [E.eulerDegree_pullback_snd_poleSheaf ξ n]
    exact_mod_cast hn

include hg in
/-- **`π_*𝒪_E(n[0])` commutes with base change.** Let `E'` over `S'` be the base change of the
elliptic curve `E` over `S` along `f : S' ⟶ S`, with projection `g : E' ⟶ E` compatible with the
zero sections. For `n > 0`, `f^* π_* 𝒪_E(n[0]) ≅ π'_* 𝒪_{E'}(n[0])`. -/
theorem nonempty_pullback_pushforward_poleSheaf_iso (h0 : E'.zero ≫ g = f ≫ E.zero) {n : ℕ}
    (hn : 0 < n) :
    Nonempty ((pullback f).obj ((pushforward E.structureMap).obj (E.poleSheaf n).obj) ≅
      (pushforward E'.structureMap).obj (E'.poleSheaf n).obj) := by
  have h := pullback_mk_poleSheaf_of_isPullback hg h0 n
  rw [LineBundleClass.pullback_mk, LineBundleClass.mk_eq_mk_iff] at h
  obtain ⟨e⟩ := h
  have := isIso_pushforwardBaseChange_app_poleSheaf hg hn
  exact ⟨asIso ((pushforwardBaseChange hg.toCommSq).app (E.poleSheaf n).obj) ≪≫
    (pushforward E'.structureMap).mapIso e⟩

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
