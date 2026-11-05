/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Global sections with affine basic opens on a cofiltered limit of schemes

Let `c` be a limit of a cofiltered diagram `D` of quasi-compact quasi-separated schemes with affine
transition maps. A global section `r` of the limit whose basic open `D(r)` is affine comes from a
global section `t` of some member `D i` whose basic open is affine; and finitely many such sections
whose basic opens cover the limit come from one member, with basic opens covering it. This
combines Mathlib's `exists_appTop_π_eq_of_isLimit` (global sections descend),
`exists_isAffineOpen_preimage_eq` (affine opens descend, Stacks 01Z4) and
`exists_map_preimage_eq_map_preimage` (quasi-compact opens with the same preimage agree at a finite
stage).

It supplies the quasi-affine models of Stacks, Lemma 32.5.2 (01Z9): for a quasi-compact open `V`
of an affine scheme `Spec R`, covered by basic opens `D(g k)`, a cofiltered system of models of `V`
has a member covered by affine basic opens `D(b k)` with `b k` restricting to `g k` on `V`.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.exists_appTop_π_eq_and_isAffineOpen_basicOpen`: one section.
* `TauCeti.AlgebraicGeometry.Scheme.exists_appTop_π_eq_and_iSup_basicOpen_eq_top`: a finite
  family of sections covering the limit.
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
include hc

/-- Let `c` be a limit of a cofiltered diagram of quasi-compact quasi-separated schemes with
affine transition maps. A global section `r` of the limit with `D(r)` affine is the pullback of a
global section `t` of some member with `D(t)` affine. -/
theorem exists_appTop_π_eq_and_isAffineOpen_basicOpen [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (r : Γ(c.pt, ⊤))
    (hr : IsAffineOpen (c.pt.basicOpen r)) :
    ∃ (i : I) (t : Γ(D.obj i, ⊤)),
      (c.π.app i).appTop t = r ∧ IsAffineOpen ((D.obj i).basicOpen t) := by
  obtain ⟨i, U, hU, hUr⟩ := exists_isAffineOpen_preimage_eq D c hc _ hr
  obtain ⟨j, t, rfl⟩ := exists_appTop_π_eq_of_isLimit D c hc r
  obtain ⟨k, fki, fkj, -⟩ := IsCofilteredOrEmpty.cone_objs i j
  obtain ⟨l, flk, hl⟩ := exists_map_preimage_eq_map_preimage D c hc
    (U := (D.obj k).basicOpen ((D.map fkj).appTop t)) (V := D.map fki ⁻¹ᵁ U)
    (isCompact_basicOpen _ isCompact_univ _) (hU.preimage _).isCompact (by
      rw [← Scheme.Hom.comp_preimage, c.w, hUr, Scheme.preimage_basicOpen_top,
        ← elementwise_of% Scheme.Hom.comp_appTop, c.w]
      rfl)
  refine ⟨l, (D.map (flk ≫ fkj)).appTop t, ?_, ?_⟩
  · rw [← elementwise_of% Scheme.Hom.comp_appTop, c.w]
  · rw [Functor.map_comp, elementwise_of% Scheme.Hom.comp_appTop,
      ← Scheme.preimage_basicOpen_top, hl, ← Scheme.Hom.comp_preimage, ← Functor.map_comp]
    exact hU.preimage _

/-- Let `c` be a limit of a cofiltered diagram of quasi-compact quasi-separated schemes with
affine transition maps, and let finitely many global sections `s k` of the limit have affine
`D(s k)` covering it. Then the `s k` are pullbacks of global sections `t k` of one member, whose
`D(t k)` are affine and cover it. -/
theorem exists_appTop_π_eq_and_iSup_basicOpen_eq_top [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {J : Type*} [Finite J] (s : J → Γ(c.pt, ⊤))
    (hs : ∀ k, IsAffineOpen (c.pt.basicOpen (s k))) (hcov : ⨆ k, c.pt.basicOpen (s k) = ⊤) :
    ∃ (i : I) (t : J → Γ(D.obj i, ⊤)), (∀ k, (c.π.app i).appTop (t k) = s k) ∧
      (∀ k, IsAffineOpen ((D.obj i).basicOpen (t k))) ∧ ⨆ k, (D.obj i).basicOpen (t k) = ⊤ := by
  classical
  choose i t ht ha using fun k ↦ exists_appTop_π_eq_and_isAffineOpen_basicOpen D c hc (s k) (hs k)
  cases nonempty_fintype J
  obtain ⟨j, fj⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  replace fj : ∀ k, j ⟶ i k := fun k ↦ (fj (by simp)).some
  obtain ⟨l, flj, hl⟩ := exists_map_eq_top D c hc
    (⨆ k, D.map (fj k) ⁻¹ᵁ (D.obj (i k)).basicOpen (t k)) (by
      simp_rw [Scheme.Hom.preimage_iSup, ← Scheme.Hom.comp_preimage, c.w,
        Scheme.preimage_basicOpen_top, ht]
      exact hcov)
  refine ⟨l, fun k ↦ (D.map (flj ≫ fj k)).appTop (t k), fun k ↦ ?_, fun k ↦ ?_, ?_⟩
  · rw [← elementwise_of% Scheme.Hom.comp_appTop, c.w, ht]
  · rw [← Scheme.preimage_basicOpen_top]
    exact (ha k).preimage _
  · simp_rw [← Scheme.preimage_basicOpen_top, Functor.map_comp, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_iSup]
    exact hl

end TauCeti.AlgebraicGeometry.Scheme
