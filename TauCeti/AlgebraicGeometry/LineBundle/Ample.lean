/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.LineBundle.Class
public import TauCeti.AlgebraicGeometry.LineBundle.Extension
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.TensorProduct
public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
public import TauCeti.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.AlgebraicGeometry.Pullback.Affine

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
that is, when `X` is quasi-affine (`LineBundleClass.isAmple_one_iff`). Conversely, on a
quasi-affine scheme, in particular on an affine scheme, every line-bundle class is ample
(`LineBundleClass.isAmple_of_isQuasiAffine`): near each point a local generator of `L`, multiplied
by a power of a global function `r` with `X_r` affine, extends to a global section.

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
  (`Scheme.Modules.nonvanishingLocus_tmul`).
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.mul_mk_of_isGloballyGenerated`: an ample class
  times a globally generated line bundle is ample.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.mul`: a product of ample classes is ample.
* `TauCeti.AlgebraicGeometry.LineBundleClass.isAmple_of_isQuasiAffine`: every line-bundle class on a
  quasi-affine scheme is ample; its line bundles are globally generated
  (`TauCeti.AlgebraicGeometry.InvertibleSheaf.isGloballyGenerated_of_isQuasiAffine`).
* `TauCeti.AlgebraicGeometry.LineBundleClass.isAmple_one_iff`: the structure sheaf is ample
  exactly when `X` is quasi-affine.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.pullback`: ampleness is preserved by
  pullback along affine morphisms.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.exists_isAffineOpen_nonvanishingLocus_le`:
  the affine nonvanishing loci of sections of positive powers form a basis of the topology.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.pullback_of_isImmersion`: ampleness is
  preserved by pullback along immersions from quasi-compact schemes.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.isSeparated`: a scheme with an ample line
  bundle is separated, by the affine-cover criterion
  `AlgebraicGeometry.Scheme.IsSeparated.of_isAffineOpen`.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.of_iSup_basicOpen_eq_top`: on a
  quasi-compact scheme, ampleness can be checked on a cover by basic opens of global functions.
  The proof extends sections from a basic open
  (`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict_of_qcqs`), using that
  such a cover by quasi-separated opens makes the scheme quasi-separated
  (`AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_iSup_basicOpen_eq_top`).
* `TauCeti.AlgebraicGeometry.LineBundleClass.isAmple_pullback_iff_of_isIso`: ampleness is
  invariant under pullback along isomorphisms of schemes.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.pullback_mul_pullback`: over a separated
  base, the exterior product `pr₁* a · pr₂* b` of ample classes is ample on `X ×_S Y`.

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

/-- **Powers of a section.** A global section `s₀` of a line bundle `L₀` gives, in every line bundle
`L` of class `(mk L₀)ᵏ` with `k > 0`, a global section with the same nonvanishing locus: the
`k`-fold tensor product `s₀ ⊗ ⋯ ⊗ s₀`, transported along an isomorphism. -/
theorem _root_.TauCeti.AlgebraicGeometry.InvertibleSheaf.exists_nonvanishingLocus_eq_of_mk_eq_pow
    {L₀ L : InvertibleSheaf X} {k : ℕ} (hk : 0 < k) (hL : mk L = mk L₀ ^ k)
    (s₀ : Γ(L₀.obj, ⊤)) :
    ∃ s : Γ(L.obj, ⊤), L.obj.nonvanishingLocus s = L₀.obj.nonvanishingLocus s₀ := by
  -- The `(k + 1)`-fold tensor product of `s₀` with itself vanishes exactly where `s₀` does.
  have key (k : ℕ) : ∃ (L' : InvertibleSheaf X) (_ : mk L' = mk L₀ ^ (k + 1))
      (s' : Γ(L'.obj, ⊤)), L'.obj.nonvanishingLocus s' = L₀.obj.nonvanishingLocus s₀ := by
    induction k with
    | zero => exact ⟨L₀, by rw [zero_add, pow_one], s₀, rfl⟩
    | succ k ih =>
      obtain ⟨L', hL', s', hs'⟩ := ih
      exact ⟨L'.tensorProduct L₀, by rw [mk_tensorProduct, hL', ← pow_succ],
        InvertibleSheaf.tmul s' s₀, by rw [InvertibleSheaf.nonvanishingLocus_tmul, hs', inf_idem]⟩
  obtain ⟨L', hL', s', hs'⟩ := key (k - 1)
  rw [Nat.sub_add_cancel hk, ← hL] at hL'
  obtain ⟨e⟩ := mk_eq_mk_iff.mp hL'
  obtain ⟨s, hs⟩ : L'.obj.nonvanishingLocus s' ∈ Set.range (L.obj.nonvanishingLocus (U := ⊤)) := by
    rw [← Scheme.Modules.range_nonvanishingLocus_eq_of_iso e ⊤]
    exact ⟨s', rfl⟩
  exact ⟨s, hs.trans hs'⟩

/-- **Positive powers of an ample class are ample.** If `a` is ample and `k > 0`, then `aᵏ` is
ample: for a global section `s` of a line bundle `L` of class `aⁿ`, the `k`-fold tensor product
`s ⊗ ⋯ ⊗ s` is a global section of a line bundle of class `(aᵏ)ⁿ` with the same nonvanishing locus
`X_s`. -/
theorem IsAmple.pow {a : LineBundleClass X} (h : a.IsAmple) {k : ℕ} (hk : 0 < k) :
    (a ^ k).IsAmple where
  compactSpace := h.compactSpace
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨n, hn, L, hL, s, hx, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus x
    obtain ⟨L', hL'⟩ := mk_surjective ((a ^ k) ^ n)
    obtain ⟨s', hs'⟩ := InvertibleSheaf.exists_nonvanishingLocus_eq_of_mk_eq_pow hk
      (by rw [hL', hL, ← pow_mul, ← pow_mul, mul_comm]) s
    exact ⟨n, hn, L', hL', s', hs' ▸ hx, hs' ▸ hs⟩

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
    have hu := InvertibleSheaf.nonvanishingLocus_tmul s t
    refine ⟨n, hn, L.tensorProduct (K.tensorPow n), ?_, InvertibleSheaf.tmul s t,
      hu ▸ ⟨hxs, hxt⟩, ?_⟩
    · rw [mk_tensorProduct, hL, mk_tensorPow, mul_pow]
    · -- `X_s ∩ X_t` is the nonvanishing locus of `t` restricted to `X_s`.
      rw [hu, ← Scheme.Modules.nonvanishingLocus_map
        (homOfLE (le_top : L.obj.nonvanishingLocus s ≤ ⊤)) t]
      exact hs.nonvanishingLocus _

/-- **Products of ample classes are ample.** If `a` and `b` are ample, then so is `a * b`. For a
point `x`, take global sections `s` and `t` of line bundles of classes `aⁿ` and `bᵐ` that do not
vanish at `x`, with `X_s` affine. Moved to the common power `n * m`, their tensor product vanishes
nowhere exactly on `X_s ∩ X_t`, the nonvanishing locus of `t` restricted to the affine open `X_s`,
which is affine. -/
theorem IsAmple.mul {a b : LineBundleClass X} (ha : a.IsAmple) (hb : b.IsAmple) :
    (a * b).IsAmple where
  compactSpace := ha.compactSpace
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨n, hn, L, hL, s, hxs, hs⟩ := ha.exists_isAffineOpen_nonvanishingLocus x
    obtain ⟨m, hm, M, hM, t, hxt, -⟩ := hb.exists_isAffineOpen_nonvanishingLocus x
    -- Move both sections to the common power `n * m`.
    obtain ⟨L', hL'⟩ := mk_surjective (a ^ (n * m))
    obtain ⟨s', hs'⟩ := InvertibleSheaf.exists_nonvanishingLocus_eq_of_mk_eq_pow hm
      (by rw [hL', hL, ← pow_mul]) s
    obtain ⟨M', hM'⟩ := mk_surjective (b ^ (n * m))
    obtain ⟨t', ht'⟩ := InvertibleSheaf.exists_nonvanishingLocus_eq_of_mk_eq_pow hn
      (by rw [hM', hM, ← pow_mul, mul_comm m]) t
    have hu := InvertibleSheaf.nonvanishingLocus_tmul s' t'
    rw [hs', ht'] at hu
    refine ⟨n * m, Nat.mul_pos hn hm, L'.tensorProduct M', ?_, InvertibleSheaf.tmul s' t',
      hu ▸ ⟨hxs, hxt⟩, ?_⟩
    · rw [mk_tensorProduct, hL', hM', mul_pow]
    · -- `X_s ∩ X_t` is the nonvanishing locus of `t` restricted to `X_s`.
      rw [hu, ← Scheme.Modules.nonvanishingLocus_map
        (homOfLE (le_top : L.obj.nonvanishingLocus s ≤ ⊤)) t]
      exact hs.nonvanishingLocus _

end LineBundleClass

namespace InvertibleSheaf

variable {X : Scheme.{u}}

/-- **On a quasi-affine scheme, every line bundle vanishes nowhere on affine neighbourhoods.**
If `X` is quasi-affine, in particular affine, then every point `x` lies in an affine nonvanishing
locus `X_s` of a global section `s` of `L` itself. Take a trivialization of `L` near `x` and an
affine basic open `X_r ∋ x` of a global function inside it. Since `X` is quasi-compact and
separated, the generator of the trivialization, restricted to `X_r`, extends to a global section
`t` after multiplication by a power of `r`
(`Scheme.Modules.isLocalizedModule_basicOpenRestrict_of_qcqs`). Then `r • t` vanishes nowhere
exactly on `X_r`. -/
theorem exists_isAffineOpen_nonvanishingLocus_of_isQuasiAffine [X.IsQuasiAffine]
    (L : InvertibleSheaf X) (x : X) :
    ∃ s : Γ(L.obj, ⊤), x ∈ L.obj.nonvanishingLocus s ∧
      IsAffineOpen (L.obj.nonvanishingLocus s) := by
  obtain ⟨V, e, hxV⟩ := Scheme.Modules.exists_mem_trivialization L.obj x
  obtain ⟨_, ⟨r, hr, rfl⟩, hxr, hrV⟩ :=
    Opens.isBasis_iff_nbhd.mp (Scheme.IsQuasiAffine.isBasis_basicOpen X) hxV
  -- The generator of the trivialization, restricted to `X_r`, vanishes nowhere there.
  let g : Γ(L.obj, X.basicOpen r) := L.obj.presheaf.map (homOfLE hrV).op
    (Scheme.Modules.trivializationGenerator L.obj e)
  have hg : L.obj.nonvanishingLocus g = X.basicOpen r := by
    rw [Scheme.Modules.nonvanishingLocus_map,
      Scheme.Modules.nonvanishingLocus_trivializationGenerator, inf_eq_left.mpr hrV]
  -- It extends to a global section `t` after multiplication by a power of `r`.
  have := L.obj.isLocalizedModule_basicOpenRestrict_of_qcqs (U := ⊤)
    (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ) r
  obtain ⟨⟨t, _, k, rfl⟩, ht⟩ :=
    IsLocalizedModule.surj (Submonoid.powers r) (L.obj.basicOpenRestrict r) g
  have hrk : X.basicOpen r ≤ X.basicOpen (r ^ k) := by
    rcases k with _ | k
    · simp
    · rw [Scheme.basicOpen_pow _ _ k.succ_pos]
  -- On `X_r`, the section `t` vanishes nowhere.
  have ht' : X.basicOpen r ⊓ L.obj.nonvanishingLocus t = X.basicOpen r := by
    have := congrArg L.obj.nonvanishingLocus ht
    rw [Scheme.Modules.basicOpenRestrict_apply, Scheme.Modules.nonvanishingLocus_map,
      Submonoid.smul_def, Scheme.Modules.basicOpen_smul_def,
      Scheme.Modules.nonvanishingLocus_smul, Scheme.basicOpen_res, hg, inf_right_comm, inf_idem,
      inf_eq_left.mpr hrk] at this
    exact this.symm
  refine ⟨r • t, ?_, ?_⟩ <;> rw [Scheme.Modules.nonvanishingLocus_smul, ht']
  exacts [hxr, hr]

/-- **Every line bundle on a quasi-affine scheme is globally generated**, in particular every line
bundle on an affine scheme. -/
theorem isGloballyGenerated_of_isQuasiAffine [X.IsQuasiAffine] (L : InvertibleSheaf X) :
    L.IsGloballyGenerated :=
  isGloballyGenerated_iff.mpr fun x ↦
    (L.exists_isAffineOpen_nonvanishingLocus_of_isQuasiAffine x).imp fun _ h ↦ h.1

end InvertibleSheaf

namespace LineBundleClass

variable {X : Scheme.{u}}

/-- **Every line-bundle class on a quasi-affine scheme is ample**, in particular every class on an
affine scheme: each point lies in an affine nonvanishing locus of a global section of any
representative (`InvertibleSheaf.exists_isAffineOpen_nonvanishingLocus_of_isQuasiAffine`). -/
theorem isAmple_of_isQuasiAffine [X.IsQuasiAffine] (a : LineBundleClass X) : a.IsAmple where
  compactSpace := inferInstance
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨L, rfl⟩ := mk_surjective a
    obtain ⟨s, hx, hs⟩ := L.exists_isAffineOpen_nonvanishingLocus_of_isQuasiAffine x
    exact ⟨1, Nat.one_pos, L, (pow_one _).symm, s, hx, hs⟩

/-- The structure sheaf `𝒪_X` is ample exactly when `X` is quasi-affine: the nonvanishing loci of
global sections of a line bundle isomorphic to `𝒪_X` are the basic open sets of global regular
functions. -/
@[simp]
theorem isAmple_one_iff : (1 : LineBundleClass X).IsAmple ↔ X.IsQuasiAffine := by
  refine ⟨fun h ↦ ?_, fun _ ↦ isAmple_of_isQuasiAffine 1⟩
  have := h.compactSpace
  -- The tensor unit `𝟙_ X.Modules` is by definition the structure sheaf `SheafOfModules.unit`, so
  -- the nonvanishing loci of global sections of a line bundle of trivial class are exactly the
  -- basic open sets of global regular functions.
  have hrange (L : InvertibleSheaf X) (hL : mk L = 1) :
      Set.range (L.obj.nonvanishingLocus (U := ⊤)) =
        Set.range (X.basicOpen (U := ⊤)) := by
    obtain ⟨e⟩ := mk_eq_one_iff.mp hL
    rw [Scheme.Modules.range_nonvanishingLocus_eq_of_iso e ⊤]
    exact congrArg Set.range (funext Scheme.Modules.nonvanishingLocus_unit)
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen X fun x ↦ ?_
  obtain ⟨n, -, L, hL, s, hx, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus x
  obtain ⟨r, hr⟩ : L.obj.nonvanishingLocus s ∈ Set.range (X.basicOpen (U := ⊤)) := by
    rw [← hrange L (hL.trans (one_pow n))]
    exact ⟨s, rfl⟩
  exact ⟨r, hr ▸ hs, hr ▸ hx⟩

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

/-- **A scheme carrying an ample line bundle is separated.** Finitely many affine nonvanishing
loci `X_s` cover `X`, and their sections can all be taken in one line bundle `K` of class `aᴺ`
(`InvertibleSheaf.exists_nonvanishingLocus_eq_of_mk_eq_pow`). For two of them, `X_s ∩ X_t` is the
nonvanishing locus of the restriction of `t` to the affine open `X_s`, hence affine, and its
functions are generated by those on `X_s` and `X_t`
(`Scheme.Modules.sup_range_map_nonvanishingLocus_inf_eq_top`). -/
theorem IsAmple.isSeparated {a : LineBundleClass X} (h : a.IsAmple) : X.IsSeparated := by
  have := h.compactSpace
  choose n hn L hL s hx hs using h.exists_isAffineOpen_nonvanishingLocus
  -- Finitely many of the affine opens `X_{s x}` cover `X`.
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ ((L x).obj.nonvanishingLocus (s x) : Set X)) (fun x ↦ Opens.isOpen _)
    fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩
  -- Their sections give sections, with the same nonvanishing loci, of a line bundle of class `aᴺ`.
  have hN : 0 < ∏ x ∈ F, n x := Finset.prod_pos fun x _ ↦ hn x
  obtain ⟨K, hK⟩ := mk_surjective (a ^ ∏ x ∈ F, n x)
  have (x : F) : ∃ t : Γ(K.obj, ⊤),
      K.obj.nonvanishingLocus t = (L x).obj.nonvanishingLocus (s x) := by
    have hdvd : n x ∣ ∏ x ∈ F, n x := Finset.dvd_prod_of_mem n x.2
    refine InvertibleSheaf.exists_nonvanishingLocus_eq_of_mk_eq_pow
      (Nat.div_pos (Nat.le_of_dvd hN hdvd) (hn x)) ?_ (s x)
    rw [hK, hL, ← pow_mul, Nat.mul_div_cancel' hdvd]
  choose t ht using this
  have hA (x : F) : IsAffineOpen (K.obj.nonvanishingLocus (t x)) := ht x ▸ hs x
  refine Scheme.IsSeparated.of_isAffineOpen (fun x ↦ K.obj.nonvanishingLocus (t x))
    (eq_top_iff.mpr fun y _ ↦ ?_) hA (fun x y ↦ ?_)
    fun x _ ↦ Scheme.Modules.sup_range_map_nonvanishingLocus_inf_eq_top (hA x)
  · obtain ⟨x, hxF, hy⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ y))
    exact Opens.mem_iSup.mpr ⟨⟨x, hxF⟩, (ht ⟨x, hxF⟩).symm ▸ hy⟩
  · -- `X_s ∩ X_t` is the nonvanishing locus of `t` restricted to `X_s`.
    have h := (hA x).nonvanishingLocus (K.obj.presheaf.map
      (homOfLE (le_top : K.obj.nonvanishingLocus (t x) ≤ ⊤)).op (t y))
    rwa [Scheme.Modules.nonvanishingLocus_map] at h

/-- **Ample line bundles have a basis of affine nonvanishing loci.** If `a` is ample, every
neighbourhood `W` of a point `x` contains an affine nonvanishing locus `X_t ∋ x` of a global section
`t` of a line bundle of class `aⁿ`, `n > 0`. Inside an affine `X_s ∋ x`, some basic open
`D(f) ⊆ W` contains `x`; as `X` is quasi-compact and separated, `sᵇ ⊗ sᵃ ⊗ f` extends from `X_s`
to a global section `ξ` (`InvertibleSheaf.exists_map_eq_tmul_sectionPow`), and `X_{s ⊗ ξ} = D(f)`.
This is part of Stacks, Tag 01Q3. -/
theorem IsAmple.exists_isAffineOpen_nonvanishingLocus_le {a : LineBundleClass X} (h : a.IsAmple)
    {x : X} {W : X.Opens} (hx : x ∈ W) :
    ∃ n : ℕ, 0 < n ∧ ∃ (L : InvertibleSheaf X) (_ : LineBundleClass.mk L = a ^ n) (t : Γ(L.obj, ⊤)),
      x ∈ L.obj.nonvanishingLocus t ∧ L.obj.nonvanishingLocus t ≤ W ∧
        IsAffineOpen (L.obj.nonvanishingLocus t) := by
  have := h.compactSpace
  have := h.isSeparated
  obtain ⟨n, hn, L, hL, s, hxs, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus x
  -- A basic open `D(f)` of the affine open `X_s` lies in `W` and contains `x`.
  obtain ⟨f, hfW, hxf⟩ := hs.exists_basicOpen_le ⟨x, hx⟩ hxs
  have hfD : X.basicOpen f ≤ L.obj.nonvanishingLocus s := X.basicOpen_le f
  -- Extend `sᵇ ⊗ sᵃ ⊗ f` from `X_s` to `X`.
  obtain ⟨a', b, ξ, hξ⟩ := InvertibleSheaf.exists_map_eq_tmul_sectionPow
    (F := InvertibleSheaf.trivial X) (U := ⊤) (by simpa using isCompact_univ)
    (by simpa using isQuasiSeparated_univ) s
    (f • InvertibleSheaf.oneSection _)
  let t := InvertibleSheaf.tmul s ξ
  have hD : L.obj.nonvanishingLocus s ≤ L.obj.nonvanishingLocus
      (L.obj.presheaf.map (homOfLE (Scheme.Modules.nonvanishingLocus_le s)).op s) := by
    rw [Scheme.Modules.nonvanishingLocus_map, inf_idem]
  have ht : (L.tensorProduct ((L.tensorPow b).tensorProduct ((L.tensorPow a').tensorProduct
      (InvertibleSheaf.trivial X)))).obj.nonvanishingLocus t = X.basicOpen f := by
    refine (InvertibleSheaf.nonvanishingLocus_tmul s ξ).trans ?_
    have h := congrArg (Scheme.Modules.nonvanishingLocus _) hξ
    rw [Scheme.Modules.nonvanishingLocus_map, InvertibleSheaf.nonvanishingLocus_tmul,
      InvertibleSheaf.nonvanishingLocus_tmul, InvertibleSheaf.nonvanishingLocus_sectionPow_of_le hD,
      InvertibleSheaf.nonvanishingLocus_sectionPow_of_le hD, Scheme.Modules.nonvanishingLocus_smul,
      InvertibleSheaf.nonvanishingLocus_oneSection] at h
    rw [h, inf_eq_left.mpr hfD, inf_eq_right.mpr hfD, inf_eq_right.mpr hfD]
  refine ⟨n * (1 + b + a'), Nat.mul_pos hn (by omega), _, ?_, t, ht ▸ hxf, ht ▸ hfW,
    ht ▸ hs.basicOpen f⟩
  simp only [mk_tensorProduct, mk_tensorPow, mk_trivial, hL]
  rw [mul_one, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  ring_nf


/-- **Ampleness is preserved by pullback along an immersion from a quasi-compact scheme**, in
particular along a quasi-compact open immersion. The immersion `j` is a closed immersion into the
open `coborderRange j` followed by its inclusion, and ample line bundles have a basis of affine
nonvanishing loci (`IsAmple.exists_isAffineOpen_nonvanishingLocus_le`): those inside
`coborderRange j` pull back to affine opens. -/
theorem IsAmple.pullback_of_isImmersion {Y : Scheme.{u}} {a : LineBundleClass Y}
    (h : a.IsAmple) (j : X ⟶ Y) [IsImmersion j] [CompactSpace X] :
    (LineBundleClass.pullback j a).IsAmple where
  compactSpace := inferInstance
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨n, hn, L, hL, t, hx, hle, ht⟩ :=
      h.exists_isAffineOpen_nonvanishingLocus_le (W := j.coborderRange)
        (show j x ∈ coborder (Set.range j) from subset_coborder ⟨x, rfl⟩)
    let t' : Γ(((InvertibleSheaf.pullback j).obj L).obj, ⊤) := j.pullbackSections L.obj ⊤ t
    have ht' : ((InvertibleSheaf.pullback j).obj L).obj.nonvanishingLocus t' =
        j ⁻¹ᵁ L.obj.nonvanishingLocus t :=
      Scheme.Modules.nonvanishingLocus_pullbackSections j t
    -- `j` is a closed immersion into `coborderRange j` followed by its inclusion, so the preimage
    -- of an affine open contained in `coborderRange j` is affine.
    have hpre : j ⁻¹ᵁ L.obj.nonvanishingLocus t =
        j.liftCoborder ⁻¹ᵁ j.coborderRange.ι ⁻¹ᵁ L.obj.nonvanishingLocus t := by
      rw [← Scheme.Hom.comp_preimage, j.liftCoborder_ι]
    refine ⟨n, hn, (InvertibleSheaf.pullback j).obj L, ?_, t', ht' ▸ hx, ?_⟩
    · rw [← pullback_mk, hL, ← pullbackHom_apply, map_pow, pullbackHom_apply]
    · rw [ht', hpre]
      exact (ht.preimage_of_isOpenImmersion _ (by simpa using hle)).preimage _

/-- **A scheme covered by quasi-separated basic opens is quasi-separated.** If the basic opens
`X_{rᵢ}` of global functions `rᵢ` cover `X` and are quasi-separated, then so is `X`. The affine
opens contained in some `X_{rᵢ}` cover `X`. If `A ⊆ X_{rᵢ}` and `B ⊆ X_{rⱼ}` are two of them, then
`A ∩ B` is the intersection of the compact opens `A ∩ X_{rⱼ}` and `B` of the quasi-separated
`X_{rⱼ}`; the first is the affine basic open of `rⱼ` in `A`. -/
theorem _root_.AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_iSup_basicOpen_eq_top
    {ι : Type*} (r : ι → Γ(X, ⊤)) (hr : ⨆ i, X.basicOpen (r i) = ⊤)
    (h : ∀ i, QuasiSeparatedSpace (X.basicOpen (r i))) : QuasiSeparatedSpace X := by
  refine Scheme.quasiSeparatedSpace_of_isOpenCover
    (fun A : {A : X.affineOpens // ∃ i, (A : X.Opens) ≤ X.basicOpen (r i)} ↦ A.1.1)
    (IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ ?_)) (fun A ↦ A.1.2) fun A B ↦ ?_
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hr.ge (Opens.mem_top x))
    obtain ⟨A, hA, hxA, hAi⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hi
    exact Opens.mem_iSup.mpr ⟨⟨⟨A, hA⟩, i, hAi⟩, hxA⟩
  · obtain ⟨⟨A, hA⟩, -⟩ := A
    obtain ⟨⟨B, hB⟩, j, hBj⟩ := B
    -- `A ∩ X_{rⱼ}` is the basic open of the restriction of `rⱼ` to `A`.
    have hA' := hA.basicOpen (X.presheaf.map (homOfLE (le_top : A ≤ ⊤)).op (r j))
    rw [Scheme.basicOpen_res] at hA'
    have hqs :=
      (isQuasiSeparated_iff_quasiSeparatedSpace _ (X.basicOpen (r j)).isOpen).mpr (h j)
    have hAB := hqs _ _ (inf_le_right : A ⊓ X.basicOpen (r j) ≤ _) (A ⊓ _).isOpen hA'.isCompact
      hBj B.isOpen hB.isCompact
    rwa [Opens.coe_inf, Set.inter_assoc, Set.inter_eq_right.mpr hBj] at hAB

/-- **Ampleness can be checked on a cover by basic opens.** Let `X` be quasi-compact, and let `rᵢ`
be global functions whose basic opens `X_{rᵢ}` cover `X`. If the restriction of `a` to every
`X_{rᵢ}` is ample, then `a` is ample. Let `L` be a line bundle of class `aⁿ`, and `s` a section of
`L` over `X_{rᵢ}` with `X_s` affine. The scheme `X` is quasi-separated, since the `X_{rᵢ}` are. So
the sections of `L` over `X_{rᵢ}` are the localization of its global sections at `rᵢ`, and `s`
extends to a global section `t` of `L` after multiplication by a power of `rᵢ`. Then `rᵢ • t` is a
global section vanishing nowhere exactly on `X_s`. -/
theorem IsAmple.of_iSup_basicOpen_eq_top [CompactSpace X]
    {a : LineBundleClass X} {ι : Type*} (r : ι → Γ(X, ⊤)) (hr : ⨆ i, X.basicOpen (r i) = ⊤)
    (h : ∀ i, (LineBundleClass.pullback (X.basicOpen (r i)).ι a).IsAmple) : a.IsAmple where
  compactSpace := inferInstance
  exists_isAffineOpen_nonvanishingLocus x := by
    have : QuasiSeparatedSpace X := Scheme.quasiSeparatedSpace_of_iSup_basicOpen_eq_top r hr
      fun i ↦ have := (h i).isSeparated; inferInstance
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (hr.ge (Opens.mem_top x))
    let U := X.basicOpen (r i)
    obtain ⟨n, hn, K, hK, s', hxs', hs'⟩ := (h i).exists_isAffineOpen_nonvanishingLocus ⟨x, hxi⟩
    obtain ⟨L, hL⟩ := mk_surjective (a ^ n)
    -- `K` is isomorphic to the restriction `L|_U`, through `L|_U ≅ U.ι^* L`.
    obtain ⟨ψ⟩ := mk_eq_mk_iff.mp (hK.trans (by
      rw [← pullbackHom_apply, ← map_pow, pullbackHom_apply, ← hL, pullback_mk]))
    let φ := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.obj
    have : SheafOfModules.isInvertible U (L.obj.restrict U.ι) :=
      (SheafOfModules.isInvertible U).prop_of_iso φ.symm inferInstance
    -- The section `s'` of `K`, carried to `L|_U` and then to a section `s` of `L` over `U`.
    let s'' : Γ(L.obj.restrict U.ι, ⊤) := (ψ ≪≫ φ.symm).hom.app ⊤ s'
    let s : Γ(L.obj, U.ι ''ᵁ ⊤) := (L.obj.restrictAppIso U.ι ⊤).hom s''
    have hs : U.ι ⁻¹ᵁ L.obj.nonvanishingLocus s = K.obj.nonvanishingLocus s' := by
      rw [← Scheme.Modules.nonvanishingLocus_restrictAppIso_inv, Iso.hom_inv_id_apply,
        Scheme.Modules.nonvanishingLocus_hom_app]
    have hUtop : U.ι ''ᵁ ⊤ = U := by
      rw [U.ι.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
    have hsU : L.obj.nonvanishingLocus s ≤ U :=
      (Scheme.Modules.nonvanishingLocus_le s).trans hUtop.le
    -- `X_s` is the image of the affine open `K_{s'}` of `U`.
    have hsaff : IsAffineOpen (L.obj.nonvanishingLocus s) := by
      have := (hs ▸ hs').image_of_isOpenImmersion U.ι
      rwa [U.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr hsU] at this
    have hxs : x ∈ L.obj.nonvanishingLocus s := by
      rw [← hs] at hxs'
      exact hxs'
    -- Extend `s` to a global section `t` after multiplication by a power of `r i`.
    let s₀ : Γ(L.obj, U) := L.obj.presheaf.map (homOfLE hUtop.ge).op s
    have hs₀ : L.obj.nonvanishingLocus s₀ = L.obj.nonvanishingLocus s := by
      rw [Scheme.Modules.nonvanishingLocus_map, inf_eq_right.mpr hsU]
    have := L.obj.isLocalizedModule_basicOpenRestrict_of_qcqs (U := ⊤)
      (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ) (r i)
    obtain ⟨⟨t, _, k, rfl⟩, ht⟩ :=
      IsLocalizedModule.surj (Submonoid.powers (r i)) (L.obj.basicOpenRestrict (r i)) s₀
    have hUk : U ≤ X.basicOpen (r i ^ k) := by
      rcases k with _ | k
      · simp
      · rw [Scheme.basicOpen_pow _ _ k.succ_pos]
    -- On `U`, the section `t` vanishes nowhere exactly on `X_s`.
    have ht' : U ⊓ L.obj.nonvanishingLocus t = L.obj.nonvanishingLocus s := by
      have := congrArg L.obj.nonvanishingLocus ht
      rw [Scheme.Modules.basicOpenRestrict_apply, Scheme.Modules.nonvanishingLocus_map,
        Submonoid.smul_def, Scheme.Modules.basicOpen_smul_def,
        Scheme.Modules.nonvanishingLocus_smul, Scheme.basicOpen_res, hs₀,
        inf_eq_right.mpr (hsU.trans (le_inf le_rfl hUk))] at this
      exact this.symm
    refine ⟨n, hn, L, hL, r i • t, ?_, ?_⟩ <;>
      rw [Scheme.Modules.nonvanishingLocus_smul, ht']
    exacts [hxs, hsaff]

/-- **Exterior products of ample classes are ample over a separated base.** Let `P = X ×_S Y` be
a fibre product over a separated scheme `S`, with projections `q₁` and `q₂`. If `a` is ample on
`X` and `b` is ample on `Y`, then `q₁* a · q₂* b` is ample on `P`. Global sections `s` and `t` of
line bundles of classes `aᴺ` and `bᴺ`, with `X_s` and `Y_t` affine, pull back to sections
vanishing nowhere exactly on `q₁⁻¹ X_s` and `q₂⁻¹ Y_t`. So their tensor product vanishes nowhere
exactly on `X_s ×_S Y_t`, which is affine
(`AlgebraicGeometry.IsAffineOpen.preimage_inf_preimage_of_isPullback`). -/
theorem IsAmple.pullback_mul_pullback {Y S P : Scheme.{u}} [S.IsSeparated]
    {a : LineBundleClass X} {b : LineBundleClass Y} (ha : a.IsAmple) (hb : b.IsAmple)
    {f : X ⟶ S} {g : Y ⟶ S} {q₁ : P ⟶ X} {q₂ : P ⟶ Y} (h : IsPullback q₁ q₂ f g) :
    (LineBundleClass.pullback q₁ a * LineBundleClass.pullback q₂ b).IsAmple where
  compactSpace := by
    have := ha.compactSpace
    have := hb.compactSpace
    have := hb.isSeparated
    -- `f` is quasi-compact: its composite with `S ⟶ ⊤_ Scheme` is, and `S` is quasi-separated.
    have : QuasiCompact (f ≫ Limits.terminal.from S) := by
      rw [Limits.terminal.comp_from]
      exact (quasiCompact_iff_compactSpace _).mpr inferInstance
    have : QuasiCompact f := .of_comp f (Limits.terminal.from S)
    have : QuasiCompact q₂ := MorphismProperty.of_isPullback h inferInstance
    exact (quasiCompact_iff_compactSpace q₂).mp inferInstance
  exists_isAffineOpen_nonvanishingLocus z := by
    obtain ⟨n, hn, L, hL, s, hxs, hs⟩ := ha.exists_isAffineOpen_nonvanishingLocus (q₁ z)
    obtain ⟨m, hm, M, hM, t, hyt, ht⟩ := hb.exists_isAffineOpen_nonvanishingLocus (q₂ z)
    -- Move both sections to the common power `n * m`.
    obtain ⟨L', hL'⟩ := mk_surjective (a ^ (n * m))
    obtain ⟨s', hs'⟩ := InvertibleSheaf.exists_nonvanishingLocus_eq_of_mk_eq_pow hm
      (by rw [hL', hL, ← pow_mul]) s
    obtain ⟨M', hM'⟩ := mk_surjective (b ^ (n * m))
    obtain ⟨t', ht'⟩ := InvertibleSheaf.exists_nonvanishingLocus_eq_of_mk_eq_pow hn
      (by rw [hM', hM, ← pow_mul, mul_comm m]) t
    let L₁ := (InvertibleSheaf.pullback q₁).obj L'
    let M₂ := (InvertibleSheaf.pullback q₂).obj M'
    let s₁ : Γ(L₁.obj, ⊤) := q₁.pullbackSections L'.obj ⊤ s'
    let t₂ : Γ(M₂.obj, ⊤) := q₂.pullbackSections M'.obj ⊤ t'
    have h₁ : L₁.obj.nonvanishingLocus s₁ = q₁ ⁻¹ᵁ L.obj.nonvanishingLocus s := by
      rw [← hs']
      exact Scheme.Modules.nonvanishingLocus_pullbackSections q₁ s'
    have h₂ : M₂.obj.nonvanishingLocus t₂ = q₂ ⁻¹ᵁ M.obj.nonvanishingLocus t := by
      rw [← ht']
      exact Scheme.Modules.nonvanishingLocus_pullbackSections q₂ t'
    have hu := InvertibleSheaf.nonvanishingLocus_tmul s₁ t₂
    rw [h₁, h₂] at hu
    refine ⟨n * m, Nat.mul_pos hn hm, L₁.tensorProduct M₂, ?_, InvertibleSheaf.tmul s₁ t₂,
      hu ▸ ⟨hxs, hyt⟩,
      hu ▸ hs.preimage_inf_preimage_of_isPullback h ht⟩
    rw [mk_tensorProduct, ← pullback_mk, ← pullback_mk, hL', hM', mul_pow]
    simp only [← pullbackHom_apply, map_pow]

end TauCeti.AlgebraicGeometry.LineBundleClass
