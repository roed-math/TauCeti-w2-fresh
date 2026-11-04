/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Limits.AffineProperties

/-!
# Properties inherited from a finite stage: reduction to affine members

Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact schemes with affine transition maps, and
`P` a property of morphisms that is local at the target and stable under base change. If `P` is
inherited from a finite stage over cofiltered limits of affine schemes, then it is inherited over
`S`: for `Y` over a member `Sᵢ`, if `Y ×_{Sᵢ} S ⟶ S` has `P`, then so does `Y ×_{Sᵢ} Sⱼ ⟶ Sⱼ` for
some `j`. The structure morphism of `Y` may be required to have any property `Q` stable under base
change, such as finite type or finite presentation. Indeed, over an affine open `U ⊆ Sᵢ` the
preimages of `U` form a cofiltered diagram of affine schemes with limit the preimage of `U` in `S`
(`AlgebraicGeometry.isLimitOpensCone`), and finitely many affine opens cover `Sᵢ`.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.exists_pullback_fst_of_isLimit_of_isZariskiLocalAtTarget`:
  the reduction to affine members.
* `TauCeti.AlgebraicGeometry.Scheme.exists_isClosedImmersion_pullback_fst_of_isLimit`,
  `TauCeti.AlgebraicGeometry.Scheme.exists_isFinite_pullback_fst_of_isLimit`: closed immersions
  and finite morphisms are inherited from a finite stage (Stacks, Lemmas 32.8.5 (01ZP) and
  32.8.3 (01ZO)).
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)] {c : Cone D}
  (hc : IsLimit c)

include hc in
/-- Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact schemes with affine transition maps,
`P` a property of morphisms local at the target and stable under base change, and `Q` a property
stable under base change. Suppose that `P` is inherited from a finite stage over every cofiltered
limit of affine schemes by base changes of quasi-compact quasi-separated morphisms `q` to a member
with `Q q`. Then the same holds over `S`: if `Y ×_{Sᵢ} S ⟶ S` has `P`, then so does
`Y ×_{Sᵢ} Sⱼ ⟶ Sⱼ` for some `j`. -/
theorem exists_pullback_fst_of_isLimit_of_isZariskiLocalAtTarget
    (P Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange]
    [Q.IsStableUnderBaseChange]
    (H : ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (E : J ⥤ Scheme.{u})
      [∀ j, IsAffine (E.obj j)] (e : Cone E), IsLimit e → ∀ {j : J} {Y : Scheme.{u}}
      (q : Y ⟶ E.obj j) [QuasiCompact q] [QuasiSeparated q], Q q →
      P (pullback.fst (e.π.app j) q) → ∃ (k : J) (hkj : k ⟶ j), P (pullback.fst (E.map hkj) q))
    {i : I} {Y : Scheme.{u}} (q : Y ⟶ D.obj i) [QuasiCompact q] [QuasiSeparated q] (hQ : Q q)
    (hq : P (pullback.fst (c.π.app i) q)) :
    ∃ (j : I) (hji : j ⟶ i), P (pullback.fst (D.map hji) q) := by
  -- `good l U`: the base change of `Y` to the preimage of `U` in `Sₗ` has `P`.
  let good (l : Over i) (U : (D.obj i).Opens) : Prop :=
    P (pullback.fst ((opensDiagramι D i U).app l ≫ D.map l.hom) q)
  have ι_comp {l m : Over i} (f : m ⟶ l) (U : (D.obj i).Opens) :
      (opensDiagram D i U).map f ≫ (opensDiagramι D i U).app l =
        (opensDiagramι D i U).app m ≫ D.map f.left :=
    (opensDiagramι D i U).naturality f
  have mono {l m : Over i} (f : m ⟶ l) (U : (D.obj i).Opens) : good l U → good m U :=
    P.pullback_fst_of_comp_eq _ _ ((opensDiagram D i U).map f) (by
      rw [reassoc_of% ι_comp f U, ← D.map_comp, Over.w f])
  have one (U : (D.obj i).Opens) (hU : IsAffineOpen U) : ∃ l, good l U := by
    have (l : Over i) : IsAffine ((opensDiagram D i U).obj l) := hU.preimage _
    let b : Over i := Over.mk (𝟙 i)
    obtain ⟨k, hkb, hk⟩ := H (opensDiagram D i U) (opensCone D c i U) (isLimitOpensCone D c hc i U)
      (j := b) (pullback.fst ((opensDiagramι D i U).app b) q) (Q.pullback_fst _ _ hQ) <| by
        refine (P.pullback_fst_pullback_fst_iff _ _ _ (a := (c.π.app i ⁻¹ᵁ U).ι ≫ c.π.app i)
          ?_).mpr ((P.pullback_fst_pullback_fst_iff _ _ _ rfl).mp (P.pullback_fst _ _ hq))
        exact Scheme.Hom.resLE_comp_ι _ _
    refine ⟨k, (P.pullback_fst_pullback_fst_iff _ _ _ ?_).mp hk⟩
    rw [ι_comp hkb U, ← Over.w hkb]
    simp [b]
  -- Finitely many affine opens lie in a common `good l`.
  have fin (t : Finset (D.obj i).Opens) : (∀ U ∈ t, IsAffineOpen U) → ∃ l, ∀ U ∈ t, good l U := by
    classical
    induction t using Finset.induction_on with
    | empty => exact fun _ ↦ ⟨Over.mk (𝟙 i), by simp⟩
    | insert U t _ ih =>
      intro ht
      obtain ⟨l, hl⟩ := ih fun V hV ↦ ht V (Finset.mem_insert_of_mem hV)
      obtain ⟨l', hl'⟩ := one U (ht U (Finset.mem_insert_self U t))
      exact ⟨IsCofiltered.min l l', Finset.forall_mem_insert _ _ _ |>.mpr
        ⟨mono (IsCofiltered.minToRight l l') U hl',
          fun V hV ↦ mono (IsCofiltered.minToLeft l l') V (hl V hV)⟩⟩
  -- Finitely many affine opens cover `Sᵢ`, and `P` is local at the target.
  obtain ⟨s, hs, hsf, hsU⟩ :=
    (D.obj i).isBasis_affineOpens.exists_finite_of_isCompact (U := ⊤) isCompact_univ
  obtain ⟨l, hl⟩ := fin hsf.toFinset fun U hU ↦ hs (hsf.mem_toFinset.mp hU)
  refine ⟨l.left, l.hom,
    IsZariskiLocalAtTarget.of_iSup_eq_top (fun U : s ↦ D.map l.hom ⁻¹ᵁ U.1) ?_ fun U ↦ ?_⟩
  · rw [← Scheme.Hom.preimage_iSup, ← sSup_eq_iSup', ← hsU, Scheme.Hom.preimage_top]
  · have h := (P.pullback_fst_pullback_fst_iff ((opensDiagramι D i U.1).app l) _ _ rfl).mpr
      (hl U.1 (hsf.mem_toFinset.mpr U.2))
    rw [← (isPullback_morphismRestrict _ _).isoPullback_hom_fst, P.cancel_left_of_respectsIso]
    exact h

include hc in
/-- Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact schemes with affine transition maps,
and `Y` a scheme of finite type, quasi-compact and quasi-separated over a member
`Sᵢ`. If the base change `Y ×_{Sᵢ} S ⟶ S` is a closed immersion, then so is `Y ×_{Sᵢ} Sⱼ ⟶ Sⱼ`
for some `j`. Stacks, Lemma 32.8.5 (01ZP). -/
theorem exists_isClosedImmersion_pullback_fst_of_isLimit {i : I} {Y : Scheme.{u}}
    (q : Y ⟶ D.obj i) [QuasiCompact q] [QuasiSeparated q] [LocallyOfFiniteType q]
    [IsClosedImmersion (pullback.fst (c.π.app i) q)] :
    ∃ (j : I) (hji : j ⟶ i), IsClosedImmersion (pullback.fst (D.map hji) q) :=
  exists_pullback_fst_of_isLimit_of_isZariskiLocalAtTarget hc @IsClosedImmersion
    @LocallyOfFiniteType
    (by
      intro _ _ _ _ _ _ he _ _ q _ _ hq' hq
      have := hq
      have := hq'
      exact exists_isClosedImmersion_pullback_fst_of_isLimit_of_forall_isAffine he q) q ‹_› ‹_›

include hc in
/-- Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact schemes with affine transition maps,
and `Y` a scheme of finite type, quasi-compact and quasi-separated over a member
`Sᵢ`. If the base change `Y ×_{Sᵢ} S ⟶ S` is finite, then so is `Y ×_{Sᵢ} Sⱼ ⟶ Sⱼ` for some `j`.
Stacks, Lemma 32.8.3 (01ZO). -/
theorem exists_isFinite_pullback_fst_of_isLimit {i : I} {Y : Scheme.{u}}
    (q : Y ⟶ D.obj i) [QuasiCompact q] [QuasiSeparated q] [LocallyOfFiniteType q]
    [IsFinite (pullback.fst (c.π.app i) q)] :
    ∃ (j : I) (hji : j ⟶ i), IsFinite (pullback.fst (D.map hji) q) := by
  observe h : HasAffineProperty @IsFinite.{u}
    (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom)
  have : IsZariskiLocalAtTarget @IsFinite.{u} := @HasAffineProperty.instIsZariskiLocalAtTarget _ _ h
  exact exists_pullback_fst_of_isLimit_of_isZariskiLocalAtTarget hc @IsFinite @LocallyOfFiniteType
    (by
      intro _ _ _ _ _ _ he _ _ q _ _ hq' hq
      have := hq
      have := hq'
      exact exists_isFinite_pullback_fst_of_isLimit_of_forall_isAffine he q) q ‹_› ‹_›

end TauCeti.AlgebraicGeometry.Scheme
