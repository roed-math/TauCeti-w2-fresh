/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import TauCeti.AlgebraicGeometry.LineBundle.Class
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.TensorProduct
public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus

/-!
# Ample line bundles

An invertible sheaf `L` on a scheme `X` is *ample* if `X` is quasi-compact and every point `x` of
`X` lies in the nonvanishing locus `X_s` of a global section `s` of some positive tensor power
`L^⊗n` such that `X_s` is affine. This is the positivity notion through which projective
morphisms, relative `Proj` and the stability of curves are expressed: a stable curve is one whose
(log-)dualizing sheaf is ample on every fibre.

Ampleness depends only on the isomorphism class of `L`, and tensor powers are available on
isomorphism classes, where they are powers in the Picard group. So ampleness is defined here as a
predicate `LineBundleClass.IsAmple` on line-bundle classes; for a line bundle `L` it reads
`(LineBundleClass.mk L).IsAmple`. The nonvanishing loci of the global sections of a line bundle
depend only on its isomorphism class (`Scheme.Modules.range_nonvanishingLocus_eq_of_iso`), so in the
definition any representative of the class of `L^⊗n` may be used
(`LineBundleClass.IsAmple.exists_pos_forall_mk_eq`).

For the trivial class the definition recovers quasi-affineness: the global sections of `𝒪_X` are
the regular functions `r` on `X`, whose nonvanishing loci are the basic open sets `X_r`, so `𝒪_X` is
ample exactly when `X` is quasi-compact and covered by affine basic open sets of global functions,
that is, when `X` is quasi-affine (`LineBundleClass.isAmple_one_iff`). In particular `𝒪_X` is ample
on every affine scheme, and so is every torsion class there
(`LineBundleClass.isAmple_of_pow_eq_one`).

Ampleness is preserved by pullback along an affine morphism `e : X ⟶ Y`, for instance a closed
immersion or an isomorphism: a global section `s` of a line bundle on `Y` pulls back to a global
section on `X` with nonvanishing locus `e⁻¹ Y_s`, which is affine when `Y_s` is
(`LineBundleClass.IsAmple.pullback`). In particular ampleness is invariant under isomorphisms of
schemes (`LineBundleClass.isAmple_pullback_iff_of_isIso`).

## Main definitions

* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple a`: the line-bundle class `a` is ample.

## Main results

* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.exists_pos_forall_mk_eq`: the defining
  sections can be taken in any line bundle representing the relevant power.
* `TauCeti.AlgebraicGeometry.LineBundleClass.isAmple_pow_iff`: for `n > 0`, the power `aⁿ` is
  ample exactly when `a` is; the forward direction `IsAmple.pow` tensors a section with itself,
  whose nonvanishing locus does not change
  (`Scheme.Modules.exists_nonvanishingLocus_tensorProduct_eq_inf`).
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.mul_mk_of_isGloballyGenerated`: an ample class
  times a globally generated line bundle is ample.
* `TauCeti.AlgebraicGeometry.LineBundleClass.isAmple_one_iff`: the structure sheaf is ample
  exactly when `X` is quasi-affine.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.pullback`: ampleness is preserved by
  pullback along affine morphisms.
* `TauCeti.AlgebraicGeometry.LineBundleClass.isAmple_pullback_iff_of_isIso`: ampleness is
  invariant under pullback along isomorphisms of schemes.

## References

* [The Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS), the definition of an
  ample invertible sheaf, and the section of the same chapter on affine and quasi-affine schemes,
  where quasi-affineness is characterized by ampleness of `𝒪_X`.
* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 7.
-/

public section

open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

variable {X : Scheme.{u}}

/-- A line-bundle class `a` on `X` is **ample** if `X` is quasi-compact and every point `x` lies in
the nonvanishing locus `X_s` of a global section `s` of a line bundle of class `aⁿ`, for some
`n > 0`, such that `X_s` is affine. For a line bundle `L`, this says that `L` is ample, with
`L^⊗n` represented by any line bundle of class `(mk L)ⁿ`. -/
structure IsAmple (a : LineBundleClass X) : Prop where
  /-- A scheme carrying an ample line bundle is quasi-compact. -/
  compactSpace : CompactSpace X
  /-- Every point lies in an affine nonvanishing locus of a global section of a positive power. -/
  exists_isAffineOpen_nonvanishingLocus (x : X) :
    ∃ n : ℕ, 0 < n ∧ ∃ (L : InvertibleSheaf X) (_ : mk L = a ^ n) (s : Γ(L.obj, ⊤)),
      x ∈ L.obj.nonvanishingLocus s ∧ IsAffineOpen (L.obj.nonvanishingLocus s)

/-- The sections defining ampleness can be found in every line bundle of the relevant class: if `a`
is ample, then each point `x` has some `n > 0` such that every line bundle `L` of class `aⁿ` has a
global section `s` with `x ∈ X_s` and `X_s` affine. -/
theorem IsAmple.exists_pos_forall_mk_eq {a : LineBundleClass X} (h : a.IsAmple) (x : X) :
    ∃ n : ℕ, 0 < n ∧ ∀ L : InvertibleSheaf X, LineBundleClass.mk L = a ^ n →
      ∃ s : Γ(L.obj, ⊤),
        x ∈ L.obj.nonvanishingLocus s ∧ IsAffineOpen (L.obj.nonvanishingLocus s) := by
  obtain ⟨n, hn, L₀, hL₀, s₀, hx, hs₀⟩ := h.exists_isAffineOpen_nonvanishingLocus x
  refine ⟨n, hn, fun L hL ↦ ?_⟩
  obtain ⟨e⟩ := mk_eq_mk_iff.mp (hL₀.trans hL.symm)
  obtain ⟨s, hs⟩ : L₀.obj.nonvanishingLocus s₀ ∈
      Set.range (L.obj.nonvanishingLocus (U := ⊤)) := by
    rw [← Scheme.Modules.range_nonvanishingLocus_eq_of_iso e ⊤]
    exact ⟨s₀, rfl⟩
  exact ⟨s, hs ▸ hx, hs ▸ hs₀⟩

/-- If a positive power `aⁿ` of a line-bundle class is ample, then so is `a`. -/
theorem IsAmple.of_pow {a : LineBundleClass X} {n : ℕ} (hn : 0 < n) (h : (a ^ n).IsAmple) :
    a.IsAmple where
  compactSpace := h.compactSpace
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨m, hm, L, hL, s, hx, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus x
    exact ⟨n * m, Nat.mul_pos hn hm, L, hL.trans (pow_mul a n m).symm, s, hx, hs⟩

/-- **Positive powers of an ample class are ample.** If `a` is ample and `k > 0`, then `aᵏ` is
ample: for a global section `s` of a line bundle `L` of class `aⁿ`, the `k`-fold tensor product
`s ⊗ ⋯ ⊗ s` is a global section of a line bundle of class `(aᵏ)ⁿ` with the same nonvanishing locus
`X_s`. -/
theorem IsAmple.pow {a : LineBundleClass X} (h : a.IsAmple) {k : ℕ} (hk : 0 < k) :
    (a ^ k).IsAmple where
  compactSpace := h.compactSpace
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨n, hn, L, hL, s, hx, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus x
    -- The `(k + 1)`-fold tensor product of `s` with itself vanishes exactly where `s` does.
    have key (k : ℕ) : ∃ (L' : InvertibleSheaf X) (_ : LineBundleClass.mk L' = a ^ (n * (k + 1)))
        (s' : Γ(L'.obj, ⊤)), L'.obj.nonvanishingLocus s' = L.obj.nonvanishingLocus s := by
      induction k with
      | zero => exact ⟨L, by rw [zero_add, mul_one, hL], s, rfl⟩
      | succ k ih =>
        obtain ⟨L', hL', s', hs'⟩ := ih
        obtain ⟨u, hu⟩ := L'.exists_nonvanishingLocus_tensorProduct L s' s
        refine ⟨L'.tensorProduct L, ?_, u, by rw [hu, hs', inf_idem]⟩
        rw [mk_tensorProduct, hL', hL, ← pow_add, mul_add_one n (k + 1)]
    obtain ⟨L', hL', s', hs'⟩ := key (k - 1)
    rw [Nat.sub_add_cancel hk] at hL'
    exact ⟨n, hn, L', by rw [hL', ← pow_mul, mul_comm], s', hs' ▸ hx, hs' ▸ hs⟩

/-- For `k > 0`, the power `aᵏ` of a line-bundle class is ample exactly when `a` is. -/
@[simp]
theorem isAmple_pow_iff {a : LineBundleClass X} {k : ℕ} (hk : 0 < k) :
    (a ^ k).IsAmple ↔ a.IsAmple :=
  ⟨IsAmple.of_pow hk, fun h ↦ h.pow hk⟩

/-- **An ample class times a globally generated line bundle is ample.** If `a` is ample and `K` is
globally generated, then `a · [K]` is ample: if `s` is a global section of a line bundle of class
`aⁿ` with `X_s` affine and `t` is a global section of `K^{⊗n}` with `x ∈ X_t`, then `s ⊗ t` vanishes
nowhere exactly on `X_s ∩ X_t`, the nonvanishing locus of the restriction of `t` to the affine open
`X_s`, which is affine. -/
theorem IsAmple.mul_mk_of_isGloballyGenerated {a : LineBundleClass X} (h : a.IsAmple)
    {K : InvertibleSheaf X} (hK : K.IsGloballyGenerated) : (a * LineBundleClass.mk K).IsAmple where
  compactSpace := h.compactSpace
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨n, hn, L, hL, s, hxs, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus x
    obtain ⟨t, hxt⟩ := InvertibleSheaf.isGloballyGenerated_iff.mp (hK.tensorPow n) x
    obtain ⟨u, hu⟩ := L.exists_nonvanishingLocus_tensorProduct (K.tensorPow n) s t
    refine ⟨n, hn, L.tensorProduct (K.tensorPow n), ?_, u, hu ▸ ⟨hxs, hxt⟩, ?_⟩
    · rw [mk_tensorProduct, hL, mk_tensorPow, mul_pow]
    · -- `X_s ∩ X_t` is the nonvanishing locus of `t` restricted to `X_s`.
      rw [hu, ← Scheme.Modules.nonvanishingLocus_map
        (homOfLE (le_top : L.obj.nonvanishingLocus s ≤ ⊤)) t]
      exact hs.nonvanishingLocus _

/-- The structure sheaf `𝒪_X` is ample exactly when `X` is quasi-affine: the nonvanishing loci of
global sections of a line bundle isomorphic to `𝒪_X` are the basic open sets of global regular
functions. -/
@[simp]
theorem isAmple_one_iff : (1 : LineBundleClass X).IsAmple ↔ X.IsQuasiAffine := by
  let O : InvertibleSheaf X := ⟨SheafOfModules.unit X.ringCatSheaf, inferInstance⟩
  -- The tensor unit `𝟙_ X.Modules` is by definition the structure sheaf `SheafOfModules.unit`.
  have hO : mk O = 1 := mk_eq_one_iff.mpr ⟨Iso.refl _⟩
  -- The nonvanishing loci of global sections of a line bundle of trivial class are exactly the
  -- basic open sets of global regular functions.
  have hrange (L : InvertibleSheaf X) (hL : mk L = 1) :
      Set.range (L.obj.nonvanishingLocus (U := ⊤)) =
        Set.range (X.basicOpen (U := ⊤)) := by
    obtain ⟨e⟩ := mk_eq_mk_iff.mp (hL.trans hO.symm)
    rw [Scheme.Modules.range_nonvanishingLocus_eq_of_iso e ⊤]
    exact congrArg Set.range (funext Scheme.Modules.nonvanishingLocus_unit)
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨inferInstance, fun x ↦ ?_⟩⟩
  · have := h.compactSpace
    refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen X fun x ↦ ?_
    obtain ⟨n, -, L, hL, s, hx, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus x
    obtain ⟨r, hr⟩ : L.obj.nonvanishingLocus s ∈ Set.range (X.basicOpen (U := ⊤)) := by
      rw [← hrange L (hL.trans (one_pow n))]
      exact ⟨s, rfl⟩
    exact ⟨r, hr ▸ hs, hr ▸ hx⟩
  · obtain ⟨_, ⟨r, hr, rfl⟩, hx, -⟩ :=
      Opens.isBasis_iff_nbhd.mp (Scheme.IsQuasiAffine.isBasis_basicOpen X) (Opens.mem_top x)
    obtain ⟨s, hs⟩ :
        X.basicOpen r ∈ Set.range (O.obj.nonvanishingLocus (U := ⊤)) := by
      rw [hrange O hO]
      exact ⟨r, rfl⟩
    exact ⟨1, Nat.one_pos, O, hO.trans (one_pow 1).symm, s, hs ▸ hx, hs ▸ hr⟩

/-- On a quasi-affine scheme, in particular on an affine scheme, the structure sheaf is ample. -/
theorem isAmple_one [X.IsQuasiAffine] : (1 : LineBundleClass X).IsAmple :=
  isAmple_one_iff.mpr inferInstance

/-- On a quasi-affine scheme, in particular on an affine scheme, every torsion line-bundle class is
ample. -/
theorem isAmple_of_pow_eq_one [X.IsQuasiAffine] {a : LineBundleClass X} {n : ℕ} (hn : 0 < n)
    (h : a ^ n = 1) : a.IsAmple :=
  IsAmple.of_pow hn (h ▸ isAmple_one)

/-- **Ampleness is preserved by pullback along an affine morphism.** If `a` is ample on `Y` and
`e : X ⟶ Y` is an affine morphism, for instance a closed immersion or an isomorphism, then the
pullback of `a` to `X` is ample: the nonvanishing locus of a pulled-back global section is the
preimage of the original one (`Scheme.Modules.nonvanishingLocus_pullbackSections`), which is
affine when the original one is. -/
theorem IsAmple.pullback {Y : Scheme.{u}} {a : LineBundleClass Y} (h : a.IsAmple) (e : X ⟶ Y)
    [IsAffineHom e] : (pullback e a).IsAmple where
  compactSpace := by
    have := h.compactSpace
    exact ⟨by simpa using QuasiCompact.isCompact_preimage (f := e) _ isOpen_univ isCompact_univ⟩
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨n, hn, L, hL, s, hx, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus (e x)
    let s' : Γ(((InvertibleSheaf.pullback e).obj L).obj, ⊤) := e.pullbackSections L.obj ⊤ s
    have hs' : ((InvertibleSheaf.pullback e).obj L).obj.nonvanishingLocus s' =
        e ⁻¹ᵁ L.obj.nonvanishingLocus s :=
      Scheme.Modules.nonvanishingLocus_pullbackSections e s
    refine ⟨n, hn, (InvertibleSheaf.pullback e).obj L, ?_, s', hs' ▸ hx, hs' ▸ hs.preimage e⟩
    rw [← pullback_mk, hL, ← pullbackHom_apply, map_pow, pullbackHom_apply]

/-- **Ampleness is invariant under isomorphisms of schemes**: for an isomorphism `e : X ⟶ Y`, the
pullback of `a` to `X` is ample exactly when `a` is ample. -/
theorem isAmple_pullback_iff_of_isIso {Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e]
    (a : LineBundleClass Y) : (pullback e a).IsAmple ↔ a.IsAmple := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.pullback e⟩
  simpa using h.pullback (inv e)

end TauCeti.AlgebraicGeometry.LineBundleClass
