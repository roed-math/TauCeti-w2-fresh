/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftSheaf.Derivation
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftSheaf.Difference

/-!
# The difference of two lifts as a derivation

Let `i : T ⟶ T'` be a first-order thickening and `l₁`, `l₂` two sections over an open `W` of `T'`
of the sheaf of lifts `liftSheaf f i a h`. Their difference `x ↦ l₁^♯ x - l₂^♯ x`
(`AlgebraicGeometry.Scheme.Hom.appLESub`), read on every open `V ⊆ W` of `T'`, is a section over
`W` of the sheaf of derivations `liftDerivationSheaf f i a` into the ideal of `i`. These
differences add up, vanish exactly on the diagonal and are compatible with restriction: this is the
difference map of the torsor of lifts of Stacks, Lemma 37.9.5 (04FJ).

## Main definitions

* `TauCeti.AlgebraicGeometry.liftSheafSub l₁ l₂`: the difference of two sections of the sheaf of
  lifts, as a derivation into the ideal of `i`.

## Main results

* `TauCeti.AlgebraicGeometry.ι_app_liftSheafSub_apply`: restricted to `W`, the difference on
  `(U, V)` is `Scheme.Hom.appLESub`.
* `TauCeti.AlgebraicGeometry.liftSheafSub_add_liftSheafSub`: the differences of three sections
  add up.
* `TauCeti.AlgebraicGeometry.liftSheafSub_left_injective`: a section is determined by its
  difference with a fixed section.
* `TauCeti.AlgebraicGeometry.liftSheafSub_map`: the difference is compatible with restriction.
* `TauCeti.AlgebraicGeometry.liftDerivation_eq_zero_of_isAffineOpen`: when `a` lifts to `W`, a
  derivation over `W` vanishing on one affine chart `U ⊇ a (i ⁻¹ W)` vanishes.
* `TauCeti.AlgebraicGeometry.liftSheafSub_eq_zero_iff`: two sections are equal if and only if
  their difference vanishes.

## References

* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

section Opens

variable {Z : Scheme.{u}} {W V : Z.Opens}

/-- For an open `V ⊆ W`, restriction `Γ(Z, V) ≅ Γ(W, W ⁻¹ V)` along the open immersion `W ⟶ Z`. -/
private noncomputable def ιAppIso (hV : V ≤ W) : Γ(Z, V) ≅ Γ(W, W.ι ⁻¹ᵁ V) :=
  haveI := W.ι.isIso_app V (by rwa [Scheme.Opens.opensRange_ι])
  asIso (W.ι.app V)

private lemma ιAppIso_hom (hV : V ≤ W) : (ιAppIso hV).hom = W.ι.app V :=
  rfl

private lemma ι_app_ιAppIso_inv (hV : V ≤ W) (s : Γ(W, W.ι ⁻¹ᵁ V)) :
    W.ι.app V ((ιAppIso hV).inv s) = s := by
  rw [← ιAppIso_hom hV, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

private lemma ι_app_injective (hV : V ≤ W) : Function.Injective (W.ι.app V) := fun s t hst ↦ by
  have := congrArg (ιAppIso hV).inv hst
  rwa [← ιAppIso_hom hV, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Iso.hom_inv_id,
    CommRingCat.id_apply, CommRingCat.id_apply] at this

end Opens

variable {X S T T' : Scheme.{u}} {f : X ⟶ S} {i : T ⟶ T'} {a : T ⟶ X} {h : T' ⟶ S}
  {W : T'.Opens}

/-- If `i ⁻¹ V ⊆ a ⁻¹ U` and `i` is surjective, every section `l` of the sheaf of lifts over `W`
maps `W ∩ V` into `U`. -/
theorem preimage_ι_le_preimage_liftSheafObjEquiv [Surjective i] {U : X.Opens} {V : T'.Opens}
    (hU : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ U) (l : (liftSheaf f i a h).obj.obj (op W)) :
    W.ι ⁻¹ᵁ V ≤ (liftSheafObjEquiv f i a h W l).1 ⁻¹ᵁ U := by
  intro y hy
  have : Surjective (i ∣_ W) := IsZariskiLocalAtTarget.restrict ‹_› W
  obtain ⟨z, rfl⟩ := (i ∣_ W).surjective y
  have hz : i z.1 ∈ V := by
    rw [← morphismRestrict_base_coe]
    exact hy
  change (liftSheafObjEquiv f i a h W l).1 ((i ∣_ W) z) ∈ U
  rw [← Scheme.Hom.comp_apply, (liftSheafObjEquiv f i a h W l).2.1, Scheme.Hom.comp_apply]
  exact hU hz

/-- The preimage of `V` under `i ∣_ W ≫ W.ι` and under `(i ⁻¹ W).ι ≫ i` agree. -/
private lemma preimage_morphismRestrict_preimage_ι (V : T'.Opens) :
    (i ∣_ W) ⁻¹ᵁ (W.ι ⁻¹ᵁ V) = (i ⁻¹ᵁ W).ι ⁻¹ᵁ (i ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, morphismRestrict_ι, Scheme.Hom.comp_preimage]

/-- Pulling a section of `T'` over `V` back along `i` and restricting to `i ⁻¹ W` is restricting
it to `W` and pulling it back along `i ∣_ W`. -/
private lemma ι_app_app (V : T'.Opens) (t : Γ(T', V)) :
    (i ⁻¹ᵁ W).ι.app (i ⁻¹ᵁ V) (i.app V t) =
      (i ∣_ W).appLE (W.ι ⁻¹ᵁ V) ((i ⁻¹ᵁ W).ι ⁻¹ᵁ (i ⁻¹ᵁ V))
        (preimage_morphismRestrict_preimage_ι V).ge (W.ι.app V t) := by
  have key (g₁ g₂ : (i ⁻¹ᵁ W).toScheme ⟶ T') (hg : g₁ = g₂) (Q : (i ⁻¹ᵁ W).toScheme.Opens)
      (e₁ : Q ≤ g₁ ⁻¹ᵁ V) (e₂ : Q ≤ g₂ ⁻¹ᵁ V) : g₁.appLE V Q e₁ = g₂.appLE V Q e₂ := by
    subst hg
    rfl
  rw [← Scheme.Hom.appLE_eq_app, ← Scheme.Hom.appLE_eq_app, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE, key _ _ (morphismRestrict_ι i W).symm _ _
      (preimage_morphismRestrict_preimage_ι V).ge,
    ← Scheme.Hom.appLE_comp_appLE _ _ V (W.ι ⁻¹ᵁ V) _ le_rfl
      (preimage_morphismRestrict_preimage_ι V).ge, CommRingCat.comp_apply,
    Scheme.Hom.appLE_eq_app]

variable [IsFirstOrderThickening i]

/-- The component on `(U, V)` of the difference of two sections of the sheaf of lifts. -/
private noncomputable def liftSheafSubHom (l₁ l₂ : (liftSheaf f i a h).obj.obj (op W))
    (p : LiftDerivationIndex i a W) : Γ(X, p.1.1) →+ Γ(T', p.1.2) :=
  (ιAppIso p.2.1).inv.hom.toAddMonoidHom.comp
    (Scheme.Hom.appLESub (liftSheafObjEquiv f i a h W l₁).1 (liftSheafObjEquiv f i a h W l₂).1
      p.1.1 (W.ι ⁻¹ᵁ p.1.2) (preimage_ι_le_preimage_liftSheafObjEquiv p.2.2 l₁)
      (preimage_ι_le_preimage_liftSheafObjEquiv p.2.2 l₂))

private lemma liftSheafSubHom_apply (l₁ l₂ : (liftSheaf f i a h).obj.obj (op W))
    (p : LiftDerivationIndex i a W) (x : Γ(X, p.1.1)) :
    liftSheafSubHom l₁ l₂ p x = (ιAppIso p.2.1).inv
      (Scheme.Hom.appLESub (liftSheafObjEquiv f i a h W l₁).1 (liftSheafObjEquiv f i a h W l₂).1
        p.1.1 (W.ι ⁻¹ᵁ p.1.2) (preimage_ι_le_preimage_liftSheafObjEquiv p.2.2 l₁)
        (preimage_ι_le_preimage_liftSheafObjEquiv p.2.2 l₂) x) :=
  rfl

/-- The pullback along `i` of the section of `T'` over `V` given by a section `l` of the sheaf of
lifts and a section `x` of `X` is `a^♯ x`. -/
private lemma app_map_appLE (l : (liftSheaf f i a h).obj.obj (op W))
    (p : LiftDerivationIndex i a W) (x : Γ(X, p.1.1)) :
    i.app p.1.2 ((ιAppIso p.2.1).inv
      ((liftSheafObjEquiv f i a h W l).1.appLE p.1.1 (W.ι ⁻¹ᵁ p.1.2)
        (preimage_ι_le_preimage_liftSheafObjEquiv p.2.2 l) x)) =
      a.appLE p.1.1 (i ⁻¹ᵁ p.1.2) p.2.2 x := by
  refine ι_app_injective (i.preimage_mono p.2.1) ?_
  rw [ι_app_app, ι_app_ιAppIso_inv, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    ← Scheme.Hom.appLE_eq_app, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  simp only [(liftSheafObjEquiv f i a h W l).2.1]

private lemma app_liftSheafSubHom (l₁ l₂ : (liftSheaf f i a h).obj.obj (op W))
    (p : LiftDerivationIndex i a W) (x : Γ(X, p.1.1)) :
    i.app p.1.2 (liftSheafSubHom l₁ l₂ p x) = 0 := by
  refine ι_app_injective (i.preimage_mono p.2.1) ?_
  rw [map_zero, liftSheafSubHom_apply, ι_app_app, ι_app_ιAppIso_inv]
  exact Scheme.Hom.appLE_appLESub_eq_zero (morphismRestrict_comp_liftSheafObjEquiv l₁ l₂) _ _ _ x

/-- The difference of two sections `l₁`, `l₂` of the sheaf of lifts over `W`, along a first-order
thickening `i`: on an open `U` of `X` and an open `V ⊆ W` of `T'` with `i ⁻¹ V ⊆ a ⁻¹ U`, the map
`x ↦ l₁^♯ x - l₂^♯ x` from `Γ(X, U)` to `Γ(T', V)`. It is a derivation into the ideal of `i`. -/
noncomputable def liftSheafSub (l₁ l₂ : (liftSheaf f i a h).obj.obj (op W)) :
    liftDerivationSubgroup f i a W :=
  ⟨liftSheafSubHom l₁ l₂, mem_liftDerivationSubgroup.2
    { map_apply p V' hV x := by
        refine ι_app_injective (hV.trans p.2.1) ?_
        rw [liftSheafSubHom_apply, liftSheafSubHom_apply, ι_app_ιAppIso_inv,
          ← CommRingCat.comp_apply (g := W.ι.app V'), Scheme.Hom.naturality,
          CommRingCat.comp_apply, ι_app_ιAppIso_inv]
        exact Scheme.Hom.appLESub_map _ _ (W.ι.preimage_mono hV) x
      apply_map p U' hU e x := by
        rw [liftSheafSubHom_apply, liftSheafSubHom_apply, Scheme.Hom.map_appLESub]
      app_apply p x := app_liftSheafSubHom l₁ l₂ p x
      apply_appLE p O e s := by
        rw [liftSheafSubHom_apply,
          Scheme.Hom.appLESub_appLE_eq_zero (liftSheafObjEquiv_comp l₁ l₂), map_zero]
      map_mul p x y z w hz hw := by
        -- Replace `l₁^♯ x` and `l₁^♯ y` by the lifts `z` and `w`: they differ by elements of the
        -- square-zero ideal of `i`.
        have hrepl (z : Γ(T', p.1.2)) (x y : Γ(X, p.1.1))
            (hz : i.app p.1.2 z = a.appLE p.1.1 (i ⁻¹ᵁ p.1.2) p.2.2 x) :
            (ιAppIso p.2.1).inv
                ((liftSheafObjEquiv f i a h W l₁).1.appLE p.1.1 (W.ι ⁻¹ᵁ p.1.2)
                  (preimage_ι_le_preimage_liftSheafObjEquiv p.2.2 l₁) x) *
                liftSheafSubHom l₁ l₂ p y =
              z * liftSheafSubHom l₁ l₂ p y := by
          rw [← sub_eq_zero, ← sub_mul]
          refine IsFirstOrderThickening.mul_eq_zero_of_app_eq_zero i ?_
            (app_liftSheafSubHom l₁ l₂ p y)
          rw [map_sub, app_map_appLE, hz, sub_self]
        rw [liftSheafSubHom_apply, Scheme.Hom.appLESub_mul_of_isFirstOrderThickening
            (morphismRestrict_comp_liftSheafObjEquiv l₁ l₂), map_add, map_mul, map_mul,
          ← liftSheafSubHom_apply, ← liftSheafSubHom_apply, hrepl z x y hz, hrepl w y x hw] }⟩

/-- On an open `V ⊆ W` of `T'`, the difference of two sections `l₁`, `l₂` of the sheaf of lifts,
restricted to `W`, is `x ↦ l₁^♯ x - l₂^♯ x`. -/
theorem ι_app_liftSheafSub_apply (l₁ l₂ : (liftSheaf f i a h).obj.obj (op W))
    (p : LiftDerivationIndex i a W) (x : Γ(X, p.1.1)) :
    W.ι.app p.1.2 ((liftSheafSub l₁ l₂).1 p x) =
      Scheme.Hom.appLESub (liftSheafObjEquiv f i a h W l₁).1 (liftSheafObjEquiv f i a h W l₂).1
        p.1.1 (W.ι ⁻¹ᵁ p.1.2) (preimage_ι_le_preimage_liftSheafObjEquiv p.2.2 l₁)
        (preimage_ι_le_preimage_liftSheafObjEquiv p.2.2 l₂) x :=
  ι_app_ιAppIso_inv p.2.1 _

/-- The difference of two sections of the sheaf of lifts on `(U, V)` is determined by its
restriction to `W`. -/
theorem liftSheafSub_apply_eq_iff (l₁ l₂ : (liftSheaf f i a h).obj.obj (op W))
    (p : LiftDerivationIndex i a W) (x : Γ(X, p.1.1)) (t : Γ(T', p.1.2)) :
    (liftSheafSub l₁ l₂).1 p x = t ↔
      Scheme.Hom.appLESub (liftSheafObjEquiv f i a h W l₁).1 (liftSheafObjEquiv f i a h W l₂).1
        p.1.1 (W.ι ⁻¹ᵁ p.1.2) (preimage_ι_le_preimage_liftSheafObjEquiv p.2.2 l₁)
        (preimage_ι_le_preimage_liftSheafObjEquiv p.2.2 l₂) x = W.ι.app p.1.2 t := by
  rw [← ι_app_liftSheafSub_apply]
  exact (ι_app_injective p.2.1).eq_iff.symm

/-- The differences of three sections of the sheaf of lifts add up. -/
theorem liftSheafSub_add_liftSheafSub (l₁ l₂ l₃ : (liftSheaf f i a h).obj.obj (op W)) :
    liftSheafSub l₁ l₂ + liftSheafSub l₂ l₃ = liftSheafSub l₁ l₃ :=
  Subtype.ext <| funext fun p ↦ AddMonoidHom.ext fun x ↦ by
    rw [AddSubgroup.coe_add, Pi.add_apply, AddMonoidHom.add_apply, eq_comm,
      liftSheafSub_apply_eq_iff, map_add, ι_app_liftSheafSub_apply, ι_app_liftSheafSub_apply,
      ← AddMonoidHom.add_apply, Scheme.Hom.appLESub_add_appLESub]

/-- The difference of a section of the sheaf of lifts with itself vanishes. -/
@[simp]
theorem liftSheafSub_self (l : (liftSheaf f i a h).obj.obj (op W)) : liftSheafSub l l = 0 :=
  Subtype.ext <| funext fun p ↦ AddMonoidHom.ext fun x ↦ by
    rw [AddSubgroup.coe_zero, Pi.zero_apply, AddMonoidHom.zero_apply, liftSheafSub_apply_eq_iff,
      map_zero, Scheme.Hom.appLESub_self, AddMonoidHom.zero_apply]

/-- Two sections of the sheaf of lifts are equal if and only if their difference vanishes. -/
theorem liftSheafSub_eq_zero_iff {l₁ l₂ : (liftSheaf f i a h).obj.obj (op W)} :
    liftSheafSub l₁ l₂ = 0 ↔ l₁ = l₂ := by
  refine ⟨fun H ↦ liftSheaf_ext_iff.2 fun U ↦ AddMonoidHom.ext fun x ↦ ?_,
    fun H ↦ H ▸ liftSheafSub_self l₁⟩
  -- Read the difference on the open `V` of `T'` underlying `l₂ ⁻¹ U`.
  let V := W.ι ''ᵁ ((liftSheafObjEquiv f i a h W l₂).1 ⁻¹ᵁ U)
  have hV : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ U := fun t ht ↦ by
    have htW : i t ∈ W := Scheme.Opens.ι_image_le _ _ ht
    let t' : (i ⁻¹ᵁ W).toScheme := ⟨t, htW⟩
    have hy : (i ∣_ W) t' = ⟨i t, htW⟩ := Subtype.ext (morphismRestrict_base_coe i W t')
    have hat : a t = (liftSheafObjEquiv f i a h W l₂).1 ⟨i t, htW⟩ := by
      rw [← hy, ← Scheme.Hom.comp_apply, (liftSheafObjEquiv f i a h W l₂).2.1,
        Scheme.Hom.comp_apply]
      rfl
    change a t ∈ U
    rw [hat]
    exact (Scheme.Opens.mem_ι_image_iff (x := (⟨i t, htW⟩ : W.toScheme))).1 ht
  let p : LiftDerivationIndex i a W := ⟨(U, V), Scheme.Opens.ι_image_le _ _, hV⟩
  have h0 := ι_app_liftSheafSub_apply l₁ l₂ p x
  rw [H, AddSubgroup.coe_zero, Pi.zero_apply, AddMonoidHom.zero_apply, map_zero] at h0
  rw [AddMonoidHom.zero_apply, ← Scheme.Hom.appLESub_map
    (preimage_ι_le_preimage_liftSheafObjEquiv hV l₁)
    (preimage_ι_le_preimage_liftSheafObjEquiv hV l₂) (Scheme.Hom.preimage_image_eq _ _).ge, ← h0,
    map_zero]

/-- Swapping two sections of the sheaf of lifts negates their difference. -/
theorem neg_liftSheafSub (l₁ l₂ : (liftSheaf f i a h).obj.obj (op W)) :
    -liftSheafSub l₁ l₂ = liftSheafSub l₂ l₁ :=
  neg_eq_of_add_eq_zero_right <| (liftSheafSub_add_liftSheafSub l₁ l₂ l₁).trans
    (liftSheafSub_self l₁)

/-- A section of the sheaf of lifts is determined by its difference with a fixed section. -/
theorem liftSheafSub_left_injective (l : (liftSheaf f i a h).obj.obj (op W)) :
    Function.Injective fun l' ↦ liftSheafSub l' l := fun l₁ l₂ H ↦ by
  have H : liftSheafSub l₁ l = liftSheafSub l₂ l := H
  rw [← liftSheafSub_eq_zero_iff, ← liftSheafSub_add_liftSheafSub l₁ l l₂, H,
    liftSheafSub_add_liftSheafSub, liftSheafSub_self]

/-- The difference of two sections of the sheaf of lifts is compatible with restriction to a
smaller open `W' ⊆ W`. -/
theorem liftSheafSub_map {W' : T'.Opens} (e : W' ≤ W)
    (l₁ l₂ : (liftSheaf f i a h).obj.obj (op W)) :
    liftDerivationSubgroupRestrict f i a e (liftSheafSub l₁ l₂) =
      liftSheafSub ((liftSheaf f i a h).obj.map (homOfLE e).op l₁)
        ((liftSheaf f i a h).obj.map (homOfLE e).op l₂) :=
  Subtype.ext <| funext fun q ↦ AddMonoidHom.ext fun x ↦ by
    have hle : W'.ι ⁻¹ᵁ q.1.2 ≤ T'.homOfLE e ⁻¹ᵁ (W.ι ⁻¹ᵁ q.1.2) := by
      rw [← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι]
    rw [liftDerivationSubgroupRestrict_apply, eq_comm, liftSheafSub_apply_eq_iff]
    simp only [coe_liftSheafObjEquiv_map]
    rw [Scheme.Hom.appLESub_comp (T'.homOfLE e)
        (preimage_ι_le_preimage_liftSheafObjEquiv (W := W) q.2.2 l₁)
        (preimage_ι_le_preimage_liftSheafObjEquiv q.2.2 l₂) hle,
      ← ι_app_liftSheafSub_apply l₁ l₂ ⟨q.1, q.2.1.trans e, q.2.2⟩ x,
      ← Scheme.Hom.appLE_eq_app (f := W.ι), ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    simp only [Scheme.homOfLE_ι, Scheme.Hom.appLE_eq_app]

/-- A derivation over `W` is determined by one affine chart: if `a` lifts to `W`, `U` is an affine
open of `X` with `a (i ⁻¹ W) ⊆ U` and `D` vanishes on `Γ(X, U)` over every open `V ⊆ W`, then `D`
vanishes. Over a basic open `D(g) ⊆ U`, every section is `x' / g ^ n`, and the Leibniz rule along
the lifts given by the lift of `a` shows that `D` kills it. -/
theorem liftDerivation_eq_zero_of_isAffineOpen (l₀ : (liftSheaf f i a h).obj.obj (op W))
    {U : X.Opens} (hUa : IsAffineOpen U) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (D : liftDerivationSubgroup f i a W)
    (hD : ∀ (V : T'.Opens) (hV : V ≤ W) (x : Γ(X, U)),
      D.1 ⟨(U, V), hV, (i.preimage_mono hV).trans hU⟩ x = 0) :
    D = 0 := by
  refine Subtype.ext <| funext fun p ↦ AddMonoidHom.ext fun x ↦ ?_
  rw [AddSubgroup.coe_zero, Pi.zero_apply, AddMonoidHom.zero_apply]
  set m := (liftSheafObjEquiv f i a h W l₀).1
  refine T'.IsSheaf.section_ext fun t ht ↦ ?_
  have htW : t ∈ W := p.2.1 ht
  have hyU : m ⟨t, htW⟩ ∈ U :=
    preimage_ι_le_preimage_liftSheafObjEquiv hU l₀ (show ⟨t, htW⟩ ∈ W.ι ⁻¹ᵁ W from htW)
  have hyU'' : m ⟨t, htW⟩ ∈ p.1.1 :=
    preimage_ι_le_preimage_liftSheafObjEquiv p.2.2 l₀ (show ⟨t, htW⟩ ∈ W.ι ⁻¹ᵁ p.1.2 from ht)
  obtain ⟨g, hg, hyg⟩ := hUa.exists_basicOpen_le ⟨_, hyU''⟩ hyU
  -- The open `V₃ ∋ t` of `T'` that `l₀` maps into the basic open `D(g) ⊆ U ∩ U''`.
  set V₃ := p.1.2 ⊓ W.ι ''ᵁ (m ⁻¹ᵁ X.basicOpen g)
  have hV₃ : i ⁻¹ᵁ V₃ ≤ a ⁻¹ᵁ X.basicOpen g := fun s hs ↦ by
    have hsW : i s ∈ W := Scheme.Opens.ι_image_le _ _ hs.2
    let s' : (i ⁻¹ᵁ W).toScheme := ⟨s, hsW⟩
    have hy : (i ∣_ W) s' = ⟨i s, hsW⟩ := Subtype.ext (morphismRestrict_base_coe i W s')
    have has : a s = m ⟨i s, hsW⟩ := by
      rw [← hy, ← Scheme.Hom.comp_apply, (liftSheafObjEquiv f i a h W l₀).2.1,
        Scheme.Hom.comp_apply]
      rfl
    change a s ∈ X.basicOpen g
    rw [has]
    exact (Scheme.Opens.mem_ι_image_iff (x := (⟨i s, hsW⟩ : W.toScheme))).1 hs.2
  refine ⟨V₃, inf_le_left,
    ⟨ht, (Scheme.Opens.mem_ι_image_iff (x := (⟨t, htW⟩ : W.toScheme))).2 hyg⟩, ?_⟩
  rw [map_zero, (isLiftDerivation_coe D).map_apply,
    ← (isLiftDerivation_coe D).apply_map (p.shrink i a V₃ inf_le_left) (X.basicOpen g) hV₃ hg
      x]
  have hV₃W : V₃ ≤ W := inf_le_left.trans p.2.1
  let q : LiftDerivationIndex i a W := ⟨(U, V₃), hV₃W, (i.preimage_mono hV₃W).trans hU⟩
  let q₃ : LiftDerivationIndex i a W := ⟨(X.basicOpen g, V₃), hV₃W, hV₃⟩
  change D.1 q₃ (X.presheaf.map (homOfLE hg).op x) = 0
  have hq (y : Γ(X, U)) : D.1 q₃ (X.presheaf.map (homOfLE (X.basicOpen_le g)).op y) = 0 :=
    ((isLiftDerivation_coe D).apply_map q _ hV₃ (X.basicOpen_le g) y).trans (hD V₃ hV₃W y)
  -- Write the restriction of `x` to `D(g)` as `x' / g ^ n`.
  have := hUa.isLocalization_basicOpen g
  obtain ⟨⟨x', _, ⟨n, rfl⟩⟩, hx'⟩ :=
    IsLocalization.surj (Submonoid.powers g) (X.presheaf.map (homOfLE hg).op x)
  -- The lifts of `a^♯ y` along `l₀`.
  let lift : Γ(X, X.basicOpen g) →+* Γ(T', V₃) := (ιAppIso hV₃W).inv.hom.comp
    (m.appLE (X.basicOpen g) (W.ι ⁻¹ᵁ V₃) (preimage_ι_le_preimage_liftSheafObjEquiv hV₃ l₀)).hom
  have hlift (y : Γ(X, X.basicOpen g)) :
      i.app V₃ (lift y) = a.appLE (X.basicOpen g) (i ⁻¹ᵁ V₃) hV₃ y :=
    app_map_appLE l₀ q₃ y
  have hg₃ : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen g) g) :=
    X.toRingedSpace.isUnit_res_basicOpen g
  have hunit : IsUnit (lift (algebraMap Γ(X, U) Γ(X, X.basicOpen g) (g ^ n))) := by
    rw [map_pow, map_pow]
    exact (hg₃.map lift).pow n
  have hmul := (isLiftDerivation_coe D).map_mul q₃ (X.presheaf.map (homOfLE hg).op x)
    (algebraMap Γ(X, U) Γ(X, X.basicOpen g) (g ^ n)) _ _ (hlift _) (hlift _)
  have h₁ : D.1 q₃ (algebraMap Γ(X, U) Γ(X, X.basicOpen g) x') = 0 := hq x'
  have h₂ : D.1 q₃ (algebraMap Γ(X, U) Γ(X, X.basicOpen g) (g ^ n)) = 0 := hq (g ^ n)
  rw [hx', h₁, h₂, mul_zero, zero_add] at hmul
  rw [← hunit.mul_right_eq_zero]
  exact hmul.symm

end TauCeti.AlgebraicGeometry
