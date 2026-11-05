/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftSheaf.Derivation
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftSheaf.Difference

/-!
# The difference of two lifts as a derivation, and the torsor of lifts

Let `i : T ⟶ T'` be a first-order thickening and `l₁`, `l₂` two sections over an open `W` of `T'`
of the sheaf of lifts `liftSheaf f i a h`. Their difference `x ↦ l₁^♯ x - l₂^♯ x`
(`AlgebraicGeometry.Scheme.Hom.appLESub`), read on every open `V ⊆ W` of `T'`, is a section over
`W` of the sheaf of derivations `liftDerivationSheaf f i a` into the ideal of `i`. These
differences add up, vanish exactly on the diagonal and are compatible with restriction: this is the
difference map of the torsor of lifts of Stacks, Lemma 37.9.5 (04FJ).

Conversely every derivation over `W` is the difference of a section with a given one, so the sheaf
of derivations acts simply transitively on the sheaf of lifts. Over an affine `W` inside affine
charts `U ⊆ X`, `V ⊆ S`, the component of the derivation on `(U, W)` is a derivation of the affine
torsor `liftStructAddTorsor`, by which the given section is moved; that the difference of the new
section with the given one is the derivation everywhere, not only on the chart `U`, is
`liftDerivation_eq_zero_of_isAffineOpen`. In general the local solutions glue.

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
* `TauCeti.AlgebraicGeometry.exists_liftSheafSub_eq`: every derivation over `W` is the difference
  of a section of the sheaf of lifts with a given one.
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
  -- Membership in a preimage is membership of the image point.
  change (liftSheafObjEquiv f i a h W l).1 ((i ∣_ W) z) ∈ U
  rw [← Scheme.Hom.comp_apply, (liftSheafObjEquiv f i a h W l).2.1, Scheme.Hom.comp_apply]
  exact hU hz

/-- If `i` is surjective, `a` maps the points of `T` over the image in `T'` of `l ⁻¹ U` into `U`,
for every section `l` of the sheaf of lifts over `W`. -/
theorem preimage_ι_image_preimage_liftSheafObjEquiv_le (l : (liftSheaf f i a h).obj.obj (op W))
    (U : X.Opens) :
    i ⁻¹ᵁ (W.ι ''ᵁ ((liftSheafObjEquiv f i a h W l).1 ⁻¹ᵁ U)) ≤ a ⁻¹ᵁ U := fun s hs ↦ by
  have hsW : i s ∈ W := Scheme.Opens.ι_image_le _ _ hs
  let s' : (i ⁻¹ᵁ W).toScheme := ⟨s, hsW⟩
  have hy : (i ∣_ W) s' = ⟨i s, hsW⟩ := Subtype.ext (morphismRestrict_base_coe i W s')
  have has : a s = (liftSheafObjEquiv f i a h W l).1 ⟨i s, hsW⟩ := by
    rw [← hy, ← Scheme.Hom.comp_apply, (liftSheafObjEquiv f i a h W l).2.1,
      Scheme.Hom.comp_apply]
    rfl
  -- Membership in a preimage is membership of the image point.
  change a s ∈ U
  rw [has]
  exact (Scheme.Opens.mem_ι_image_iff (x := (⟨i s, hsW⟩ : W.toScheme))).1 hs

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
  liftDerivationSubgroup.ext fun p x ↦ by
    rw [AddSubgroup.coe_add, Pi.add_apply, AddMonoidHom.add_apply, eq_comm,
      liftSheafSub_apply_eq_iff, map_add, ι_app_liftSheafSub_apply, ι_app_liftSheafSub_apply,
      ← AddMonoidHom.add_apply, Scheme.Hom.appLESub_add_appLESub]

/-- The difference of a section of the sheaf of lifts with itself vanishes. -/
@[simp]
theorem liftSheafSub_self (l : (liftSheaf f i a h).obj.obj (op W)) : liftSheafSub l l = 0 :=
  liftDerivationSubgroup.ext fun p x ↦ by
    rw [AddSubgroup.coe_zero, Pi.zero_apply, AddMonoidHom.zero_apply, liftSheafSub_apply_eq_iff,
      map_zero, Scheme.Hom.appLESub_self, AddMonoidHom.zero_apply]

/-- Two sections of the sheaf of lifts are equal if and only if their difference vanishes. -/
theorem liftSheafSub_eq_zero_iff {l₁ l₂ : (liftSheaf f i a h).obj.obj (op W)} :
    liftSheafSub l₁ l₂ = 0 ↔ l₁ = l₂ := by
  refine ⟨fun H ↦ liftSheaf_ext_iff.2 fun U ↦ AddMonoidHom.ext fun x ↦ ?_,
    fun H ↦ H ▸ liftSheafSub_self l₁⟩
  -- Read the difference on the open `V` of `T'` underlying `l₂ ⁻¹ U`.
  let V := W.ι ''ᵁ ((liftSheafObjEquiv f i a h W l₂).1 ⁻¹ᵁ U)
  have hV : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ U := preimage_ι_image_preimage_liftSheafObjEquiv_le l₂ U
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
  liftDerivationSubgroup.ext fun q x ↦ by
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
  refine liftDerivationSubgroup.ext fun p x ↦ ?_
  rw [AddSubgroup.coe_zero, Pi.zero_apply, AddMonoidHom.zero_apply]
  set m := (liftSheafObjEquiv f i a h W l₀).1
  refine T'.IsSheaf.section_ext fun t ht ↦ ?_
  have htW : t ∈ W := p.2.1 ht
  -- `l₀` maps `t` into `U` and into `U''`.
  have hyU : m ⟨t, htW⟩ ∈ U := preimage_ι_le_preimage_liftSheafObjEquiv hU l₀ (x := ⟨t, htW⟩) htW
  have hyU'' : m ⟨t, htW⟩ ∈ p.1.1 :=
    preimage_ι_le_preimage_liftSheafObjEquiv p.2.2 l₀ (x := ⟨t, htW⟩) ht
  obtain ⟨g, hg, hyg⟩ := hUa.exists_basicOpen_le ⟨_, hyU''⟩ hyU
  -- The open `V₃ ∋ t` of `T'` that `l₀` maps into the basic open `D(g) ⊆ U ∩ U''`.
  set V₃ := p.1.2 ⊓ W.ι ''ᵁ (m ⁻¹ᵁ X.basicOpen g)
  have hV₃ : i ⁻¹ᵁ V₃ ≤ a ⁻¹ᵁ X.basicOpen g := (i.preimage_mono inf_le_right).trans
    (preimage_ι_image_preimage_liftSheafObjEquiv_le l₀ _)
  refine ⟨V₃, inf_le_left,
    ⟨ht, (Scheme.Opens.mem_ι_image_iff (x := (⟨t, htW⟩ : W.toScheme))).2 hyg⟩, ?_⟩
  rw [map_zero, (isLiftDerivation_coe D).map_apply,
    ← (isLiftDerivation_coe D).apply_map (p.shrink i a V₃ inf_le_left) (X.basicOpen g) hV₃ hg
      x]
  have hV₃W : V₃ ≤ W := inf_le_left.trans p.2.1
  let q : LiftDerivationIndex i a W := ⟨(U, V₃), hV₃W, (i.preimage_mono hV₃W).trans hU⟩
  let q₃ : LiftDerivationIndex i a W := ⟨(X.basicOpen g, V₃), hV₃W, hV₃⟩
  -- The index produced by `apply_map` is `q₃`.
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

section Action

/-- The restriction `Γ(Z, U) ⟶ Γ(U, ⊤)` along `U.ι` is the inverse of `U.topIso`. -/
private lemma ι_appLE_top {Z : Scheme.{u}} (U : Z.Opens) (e : ⊤ ≤ U.ι ⁻¹ᵁ U) :
    U.ι.appLE U ⊤ e = U.topIso.inv := by
  rw [Scheme.Opens.topIso_inv, Scheme.Hom.appLE, Scheme.Opens.ι_app]
  exact (Z.presheaf.map_comp _ _).symm.trans (congrArg Z.presheaf.map (Subsingleton.elim _ _))

/-- `Scheme.Hom.appTop` as an `appLE`. -/
private lemma appTop_eq_appLE {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    g.appTop = g.appLE ⊤ ⊤ (Scheme.Hom.preimage_top g).ge :=
  Scheme.Hom.app_eq_appLE g

/-- `Scheme.Hom.appLE_comp_appLE` with an arbitrary proof of the inclusion. -/
private lemma appLE_comp_appLE' {A B C : Scheme.{u}} (g₁ : A ⟶ B) (g₂ : B ⟶ C) {O : C.Opens}
    {O' : B.Opens} {O'' : A.Opens} (e₂ : O' ≤ g₂ ⁻¹ᵁ O) (e₁ : O'' ≤ g₁ ⁻¹ᵁ O')
    (e : O'' ≤ (g₁ ≫ g₂) ⁻¹ᵁ O) :
    g₂.appLE O O' e₂ ≫ g₁.appLE O' O'' e₁ = (g₁ ≫ g₂).appLE O O'' e :=
  Scheme.Hom.appLE_comp_appLE g₁ g₂ O O' O'' e₂ e₁

/-- Equal morphisms induce equal maps on sections. -/
private lemma appLE_congr_hom {A B : Scheme.{u}} {g₁ g₂ : A ⟶ B} (hg : g₁ = g₂) {O : B.Opens}
    {O' : A.Opens} (e₁ : O' ≤ g₁ ⁻¹ᵁ O) (e₂ : O' ≤ g₂ ⁻¹ᵁ O) :
    g₁.appLE O O' e₁ = g₂.appLE O O' e₂ := by
  subst hg
  rfl

/-- `Scheme.Hom.resLE_app_top`, stated with `appTop`. -/
private lemma resLE_appTop {Y Z : Scheme.{u}} (g : Y ⟶ Z) {O : Z.Opens} {O' : Y.Opens}
    (e : O' ≤ g ⁻¹ᵁ O) :
    (g.resLE O O' e).appTop = O.topIso.hom ≫ g.appLE O O' e ≫ O'.topIso.inv :=
  Scheme.Hom.resLE_app_top g e

omit [IsFirstOrderThickening i] in
/-- Restricting a section of `T'` over `W` to `W` and pulling it back along `i ∣_ W` is pulling
it back along `i` and restricting to `i ⁻¹ W`. -/
private lemma morphismRestrict_appTop_topIso_inv (t : Γ(T', W)) :
    (i ∣_ W).appTop (W.topIso.inv t) = (i ⁻¹ᵁ W).topIso.inv (i.app W t) := by
  have H : W.topIso.inv ≫ (i ∣_ W).appTop = i.app W ≫ (i ⁻¹ᵁ W).topIso.inv := by
    have h₁ : (⊤ : (i ⁻¹ᵁ W).toScheme.Opens) ≤ (i ∣_ W ≫ W.ι) ⁻¹ᵁ W := by simp
    have h₂ : (⊤ : (i ⁻¹ᵁ W).toScheme.Opens) ≤ ((i ⁻¹ᵁ W).ι ≫ i) ⁻¹ᵁ W := by simp
    rw [← ι_appLE_top W (by simp), ← ι_appLE_top (i ⁻¹ᵁ W) (by simp), appTop_eq_appLE,
      Scheme.Hom.app_eq_appLE i, appLE_comp_appLE' _ _ _ _ h₁, appLE_comp_appLE' _ _ _ _ h₂]
    exact appLE_congr_hom (morphismRestrict_ι i W) _ _
  rw [← CommRingCat.comp_apply, H, CommRingCat.comp_apply]

variable {U : X.Opens} {V : S.Opens}

/-- A lift of `a^♯ x` to `Γ(T', W)`, given by a section `l₀` of the sheaf of lifts. -/
private noncomputable def chartLift (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (l₀ : (liftSheaf f i a h).obj.obj (op W)) (x : Γ(X, U)) : Γ(T', W) :=
  (ιAppIso le_rfl).inv ((liftSheafObjEquiv f i a h W l₀).1.appLE U (W.ι ⁻¹ᵁ W)
    (preimage_ι_le_preimage_liftSheafObjEquiv hU l₀) x)

private lemma app_chartLift (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (l₀ : (liftSheaf f i a h).obj.obj (op W))
    (x : Γ(X, U)) : i.app W (chartLift hU l₀ x) = a.appLE U (i ⁻¹ᵁ W) hU x :=
  app_map_appLE l₀ ⟨(U, W), le_rfl, hU⟩ x

/-- The component on `(U, W)` of a derivation `D` over `W`, read on `Γ(U, ⊤)` and `Γ(W, ⊤)`. -/
private noncomputable def chartFun (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (D : liftDerivationSubgroup f i a W)
    (y : Γ(U.toScheme, ⊤)) : Γ(W.toScheme, ⊤) :=
  W.topIso.inv (D.1 ⟨(U, W), le_rfl, hU⟩ (U.topIso.hom y))

omit [IsFirstOrderThickening i] in
private lemma chartFun_add (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (D : liftDerivationSubgroup f i a W)
    (y₁ y₂ : Γ(U.toScheme, ⊤)) :
    chartFun hU D (y₁ + y₂) = chartFun hU D y₁ + chartFun hU D y₂ := by
  simp only [chartFun, map_add]

omit [IsFirstOrderThickening i] in
private lemma appTop_chartFun (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (D : liftDerivationSubgroup f i a W)
    (y : Γ(U.toScheme, ⊤)) : (i ∣_ W).appTop (chartFun hU D y) = 0 := by
  rw [chartFun, morphismRestrict_appTop_topIso_inv]
  exact (congrArg _ ((isLiftDerivation_coe D).app_apply ⟨(U, W), le_rfl, hU⟩ _)).trans
    (map_zero _)

/-- The Leibniz rule of `chartFun`, along the lifts given by `l₀`. -/
private lemma chartFun_mul (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (l₀ : (liftSheaf f i a h).obj.obj (op W))
    (D : liftDerivationSubgroup f i a W) (y₁ y₂ : Γ(U.toScheme, ⊤)) :
    chartFun hU D (y₁ * y₂) =
      W.topIso.inv (chartLift hU l₀ (U.topIso.hom y₁)) * chartFun hU D y₂ +
        W.topIso.inv (chartLift hU l₀ (U.topIso.hom y₂)) * chartFun hU D y₁ := by
  rw [chartFun, chartFun, chartFun, map_mul, (isLiftDerivation_coe D).map_mul
    ⟨(U, W), le_rfl, hU⟩ _ _ _ _ (app_chartLift hU l₀ _) (app_chartLift hU l₀ _), map_add,
    map_mul, map_mul]

/-- `chartFun` is linear over `Γ(V, ⊤)`. -/
private lemma chartFun_appTop_mul (w : a ≫ f = i ≫ h) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V) (l₀ : (liftSheaf f i a h).obj.obj (op W))
    (D : liftDerivationSubgroup f i a W) (r : Γ(V.toScheme, ⊤)) (y : Γ(U.toScheme, ⊤)) :
    chartFun hU D ((f.resLE V U hUV).appTop r * y) =
      (h.resLE V W hV).appTop r * chartFun hU D y := by
  have hlift : i.app W (h.appLE V W hV (V.topIso.hom r)) =
      a.appLE U (i ⁻¹ᵁ W) hU (f.appLE V U hUV (V.topIso.hom r)) := by
    have H : h.appLE V W hV ≫ i.app W = f.appLE V U hUV ≫ a.appLE U (i ⁻¹ᵁ W) hU := by
      have h₁ : i ⁻¹ᵁ W ≤ (i ≫ h) ⁻¹ᵁ V := i.preimage_mono hV
      have h₂ : i ⁻¹ᵁ W ≤ (a ≫ f) ⁻¹ᵁ V := hU.trans (a.preimage_mono hUV)
      rw [Scheme.Hom.app_eq_appLE, appLE_comp_appLE' _ _ _ _ h₁, appLE_comp_appLE' _ _ _ _ h₂]
      exact appLE_congr_hom w.symm _ _
    rw [← CommRingCat.comp_apply, H, CommRingCat.comp_apply]
  rw [chartFun, chartFun, resLE_appTop, resLE_appTop, CommRingCat.comp_apply,
    CommRingCat.comp_apply, map_mul, Iso.inv_hom_id_apply, (isLiftDerivation_coe D).map_mul
      ⟨(U, W), le_rfl, hU⟩ _ _ _ _ hlift (app_chartLift hU l₀ _),
    (isLiftDerivation_coe D).apply_appLE, mul_zero, add_zero, map_mul, CommRingCat.comp_apply,
    CommRingCat.comp_apply]

/-- The lifts `chartLift` of `a^♯ y` reduce to `y` modulo the kernel of `(i ∣_ W)^♯`. -/
private lemma mk_chartLift [IsAffine W.toScheme] (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (l₀ : (liftSheaf f i a h).obj.obj (op W)) (y : Γ(U.toScheme, ⊤)) :
    letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
    Ideal.Quotient.mk (RingHom.ker (i ∣_ W).appTop.hom)
        (W.topIso.inv (chartLift hU l₀ (U.topIso.hom y))) =
      algebraMap Γ(U.toScheme, ⊤) _ y := by
  let := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
  rw [quotientKerAppTopAlgebra_mk_eq_algebraMap_iff, morphismRestrict_appTop_topIso_inv,
    app_chartLift, resLE_appTop, CommRingCat.comp_apply, CommRingCat.comp_apply]

/-- The derivation `Γ(U, ⊤) → ker (i ∣_ W)^♯` of the affine torsor of lifts given by the component
of a derivation `D` over `W` on the chart `(U, W)`. -/
private noncomputable def chartDerivation [IsAffine W.toScheme] (w : a ≫ f = i ≫ h)
    (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U) (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V)
    (l₀ : (liftSheaf f i a h).obj.obj (op W))
    (D : liftDerivationSubgroup f i a W) :
    letI := (f.resLE V U hUV).appTop.hom.toAlgebra
    letI := (h.resLE V W hV).appTop.hom.toAlgebra
    letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
    letI := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
      (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
    Derivation Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤) (RingHom.ker (i ∣_ W).appTop.hom) :=
  letI := (f.resLE V U hUV).appTop.hom.toAlgebra
  letI := (h.resLE V W hV).appTop.hom.toAlgebra
  letI := quotientKerAppTopAlgebra (i ∣_ W) (a.resLE U (i ⁻¹ᵁ W) hU)
  letI := Ideal.moduleOfSqEqBot Γ(U.toScheme, ⊤)
    (IsFirstOrderThickening.ker_appTop_sq_eq_bot (i ∣_ W))
  Derivation.mk'
    { toFun y := ⟨chartFun hU D y, appTop_chartFun hU D y⟩
      map_add' y₁ y₂ := Subtype.ext (chartFun_add hU D y₁ y₂)
      map_smul' r y := Subtype.ext (chartFun_appTop_mul w hU hV hUV l₀ D r y) }
    fun y₁ y₂ ↦ Subtype.ext <| (chartFun_mul hU l₀ D y₁ y₂).trans <| by
      rw [Submodule.coe_add, Ideal.coe_smul_of_sq_eq_bot _ (mk_chartLift hU l₀ y₁),
        Ideal.coe_smul_of_sq_eq_bot _ (mk_chartLift hU l₀ y₂)]
      rfl

/-- Restriction between two opens that contain each other is injective. -/
private lemma map_homOfLE_injective {Z : Scheme.{u}} {A B : Z.Opens} (h₁ : B ≤ A) (h₂ : A ≤ B) :
    Function.Injective (Z.presheaf.map (homOfLE h₁).op) := fun s t hst ↦ by
  have := congrArg (Z.presheaf.map (homOfLE h₂).op) hst
  rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
    (Subsingleton.elim _ (𝟙 _) : (homOfLE h₁).op ≫ (homOfLE h₂).op = 𝟙 _),
    CategoryTheory.Functor.map_id, CommRingCat.id_apply, CommRingCat.id_apply] at this

/-- Over an affine open `W` of `T'` with affine charts `U ⊆ X`, `V ⊆ S` (`a (i ⁻¹ W) ⊆ U`,
`h W ⊆ V`, `f U ⊆ V`), every derivation `D` over `W` is the difference `liftSheafSub l l₀` of a
section `l` of the sheaf of lifts with a given section `l₀`: the local half of the torsor
structure of Stacks, Lemma 37.9.5 (04FJ). -/
theorem exists_liftSheafSub_eq_of_isAffine [IsAffine W.toScheme] [IsAffine U.toScheme]
    [IsAffine V.toScheme] (w : a ≫ f = i ≫ h) (hU : i ⁻¹ᵁ W ≤ a ⁻¹ᵁ U)
    (hV : W ≤ h ⁻¹ᵁ V) (hUV : U ≤ f ⁻¹ᵁ V) (l₀ : (liftSheaf f i a h).obj.obj (op W))
    (D : liftDerivationSubgroup f i a W) : ∃ l, liftSheafSub l l₀ = D := by
  have : (commSq_resLE w hU hV hUV).HasLift := ⟨⟨liftSheafObjEquivLiftStruct w hU hV hUV l₀⟩⟩
  let := liftStructAddTorsor (commSq_resLE w hU hV hUV)
  set e := liftSheafObjEquivLiftStruct w hU hV hUV
  set d := chartDerivation w hU hV hUV l₀ D
  refine ⟨e.symm (d +ᵥ e l₀), ?_⟩
  set l := e.symm (d +ᵥ e l₀)
  rw [← sub_eq_zero]
  refine liftDerivation_eq_zero_of_isAffineOpen l₀ (inferInstance : IsAffine U.toScheme) hU _
    fun V' hV' x ↦ ?_
  -- The component on `(U, V')` is the restriction of the component on `(U, W)`.
  have hE := (isLiftDerivation_coe (liftSheafSub l l₀ - D)).map_apply ⟨(U, W), le_rfl, hU⟩ V'
    hV' x
  refine hE.symm.trans ?_
  suffices h0 : (liftSheafSub l l₀ - D).1 ⟨(U, W), le_rfl, hU⟩ x = 0 by rw [h0, map_zero]
  rw [AddSubgroup.coe_sub, Pi.sub_apply, AddMonoidHom.sub_apply, sub_eq_zero,
    liftSheafSub_apply_eq_iff]
  -- Compare both sides on `⊤ = W ⁻¹ W`.
  have hrange (l' : (liftSheaf f i a h).obj.obj (op W)) :
      ⊤ ≤ (liftSheafObjEquiv f i a h W l').1 ⁻¹ᵁ U :=
    (Scheme.Opens.ι_preimage_self W).ge.trans (preimage_ι_le_preimage_liftSheafObjEquiv hU l')
  refine map_homOfLE_injective (Z := W.toScheme) (Scheme.Opens.ι_preimage_self W).ge le_top ?_
  rw [Scheme.Hom.appLESub_map, ← CommRingCat.comp_apply, ← Scheme.Hom.appLE,
    ι_appLE_top, ← liftSheafObjEquivLiftStruct_vsub_apply_eq_appLESub w hU hV hUV l l₀
      (hrange l) (hrange l₀) x, Equiv.apply_symm_apply, vadd_vsub]
  change chartFun hU D (U.ι.appLE U ⊤ _ x) = _
  rw [chartFun, ι_appLE_top, Iso.inv_hom_id_apply]

omit [IsFirstOrderThickening i] in
/-- Restricting a section of the sheaf of lifts twice is restricting it once. -/
private lemma liftSheaf_map_map {W' W'' : T'.Opens} (e : W' ≤ W) (e' : W'' ≤ W')
    (l : (liftSheaf f i a h).obj.obj (op W)) :
    (liftSheaf f i a h).obj.map (homOfLE e').op ((liftSheaf f i a h).obj.map (homOfLE e).op l) =
      (liftSheaf f i a h).obj.map (homOfLE (e'.trans e)).op l :=
  (liftSheafObjEquiv f i a h W'').injective <| Subtype.ext <| by
    simp only [coe_liftSheafObjEquiv_map, Scheme.homOfLE_homOfLE_assoc]

/-- Every derivation `D` over `W` is the difference `liftSheafSub l l₀` of a section `l` of the
sheaf of lifts with a given section `l₀`: the sheaf of derivations acts simply transitively on the
sheaf of lifts (Stacks, Lemma 37.9.5 (04FJ)). Locally on affine charts this is
`exists_liftSheafSub_eq_of_isAffine`; the local solutions agree on overlaps by
`liftSheafSub_left_injective` and glue. -/
theorem exists_liftSheafSub_eq (w : a ≫ f = i ≫ h) (l₀ : (liftSheaf f i a h).obj.obj (op W))
    (D : liftDerivationSubgroup f i a W) : ∃ l, liftSheafSub l l₀ = D := by
  choose W' U V hW' hU' hV' hxW' hW'W hUW' hVW' hUV' using
    fun x : W ↦ exists_affine_chart w (O := W) x.2
  have hcover : W ≤ ⨆ x, W' x := fun t ht ↦ Opens.mem_iSup.2 ⟨⟨t, ht⟩, hxW' _⟩
  let res (x : W) := (liftSheaf f i a h).obj.map (homOfLE (hW'W x)).op
  have hloc (x : W) : ∃ l, liftSheafSub l (res x l₀) =
      liftDerivationSubgroupRestrict f i a (hW'W x) D := by
    have : IsAffine (W' x).toScheme := hW' x
    have : IsAffine (U x).toScheme := hU' x
    have : IsAffine (V x).toScheme := hV' x
    exact exists_liftSheafSub_eq_of_isAffine w (hUW' x) (hVW' x) (hUV' x) _ _
  choose L hL using hloc
  -- On `W' x ⊓ W' y`, both local solutions differ from `l₀` by the restriction of `D`.
  have hres (x y : W) {O : T'.Opens} (hO : O ≤ W' x) :
      liftSheafSub ((liftSheaf f i a h).obj.map (homOfLE hO).op (L x))
          ((liftSheaf f i a h).obj.map (homOfLE (hO.trans (hW'W x))).op l₀) =
        liftDerivationSubgroupRestrict f i a (hO.trans (hW'W x)) D := by
    rw [← liftSheaf_map_map (hW'W x) hO, ← liftSheafSub_map, hL,
      liftDerivationSubgroupRestrict_restrict]
  obtain ⟨l, hl, -⟩ := (liftSheaf f i a h).existsUnique_gluing' (U := W') W
    (fun x ↦ homOfLE (hW'W x)) hcover L fun x y ↦
      liftSheafSub_left_injective _ ((hres x y inf_le_left).trans (hres y x inf_le_right).symm)
  refine ⟨l, liftDerivationSubgroup.ext_of_le_iSup W' hW'W hcover fun x ↦ ?_⟩
  rw [liftSheafSub_map, hl x, hL]

end Action

end TauCeti.AlgebraicGeometry
