/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Gluing.Pushout

/-!
# Morphisms between gluings of two schemes along opens

Let `X = U ∪_W V` and `X' = U' ∪_{W'} V'` be gluings along open immersions
(`TauCeti.AlgebraicGeometry.Scheme.isPushout_opens_of_sup_eq_top` and the instances of
`TauCeti/AlgebraicGeometry/Gluing/Pushout.lean`), and let `u : U' ⟶ U`, `v : V' ⟶ V` be compatible
with `w : W' ⟶ W`. If `W'` is the preimage of `W` both in `U'` and in `V'`, then the preimage of
`U` in `X'` is `U'` and the preimage of `V` is `V'`: the induced `pushout.map` is `u` over `U` and
`v` over `V`. Hence it has every property local at the target that `u` and `v` have. For spans
`Uf ⟵ Vf ⟶ Sf` of functors whose components are open immersions, the gluings form a functor
`pushoutFunctor`, whose transition maps inherit such properties when the naturality squares are
pullbacks.

In the extension step of absolute Noetherian approximation (Stacks, Proposition 32.5.4 (01ZA))
this makes the transition maps between the gluings `Uⱼ ∪_{Vⱼ} Spec C` affine.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.isPullback_pushout_inl_map`,
  `TauCeti.AlgebraicGeometry.Scheme.isPullback_pushout_inr_map`: the two pullback squares.
* `TauCeti.AlgebraicGeometry.Scheme.pushout_map_of_isZariskiLocalAtTarget`: properties local at
  the target pass from `u` and `v` to `pushout.map`.
* `TauCeti.AlgebraicGeometry.Scheme.pushoutFunctor`: the functor of gluings of a span of functors.
* `TauCeti.AlgebraicGeometry.Scheme.pushoutFunctor_map_of_isZariskiLocalAtTarget`: its transition
  maps.
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {W U V W' U' V' : Scheme.{u}} {f : W ⟶ U} {g : W ⟶ V} [IsOpenImmersion f]
  [IsOpenImmersion g] {f' : W' ⟶ U'} {g' : W' ⟶ V'} [IsOpenImmersion f'] [IsOpenImmersion g']
  {w : W' ⟶ W} {u : U' ⟶ U} {v : V' ⟶ V}

/-- Let `u : U' ⟶ U` and `v : V' ⟶ V` be compatible with `w : W' ⟶ W` along open immersions, with
`W'` the preimage of `W` in `V'`. Then the preimage of `U` in `U' ∪_{W'} V'` under the induced map
of gluings is `U'`. -/
theorem isPullback_pushout_inl_map (hf : f' ≫ u = w ≫ f) (hg : IsPullback g' w v g) :
    IsPullback u (pushout.inl f' g') (pushout.inl f g) (pushout.map f' g' f g u v w hf hg.w) := by
  refine IsOpenImmersion.isPullback u (pushout.inl f' g') (pushout.inl f g) _
    (pushout.inl_desc _ _ _) (le_antisymm (fun x hx ↦ ?_) ?_)
  · obtain ⟨y, hy⟩ := hx
    have hcov := opensRange_pushout_inl_sup_opensRange_pushout_inr f' g'
    obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ : x ∈ Set.range (pushout.inl f' g') ∨
        x ∈ Set.range (pushout.inr f' g') := hcov.ge (Set.mem_univ x)
    · exact ⟨a, rfl⟩
    · have hb : pushout.inl f g y = pushout.inr f g (v b) := by
        rw [hy, ← Scheme.Hom.comp_apply, pushout.inr_desc, Scheme.Hom.comp_apply]
      obtain ⟨w₀, -, hw₀⟩ := exists_eq_of_pushout_inl_eq_pushout_inr f g hb
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback b w₀ hw₀.symm
      refine ⟨f' ((hg.isoPullback.inv) z), ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pushout.condition,
        Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Category.assoc,
        IsPullback.isoPullback_inv_fst, Scheme.Hom.comp_apply, hz]
  · rintro _ ⟨a, rfl⟩
    exact ⟨u a, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pushout.inl_desc]⟩

/-- Let `u : U' ⟶ U` and `v : V' ⟶ V` be compatible with `w : W' ⟶ W` along open immersions, with
`W'` the preimage of `W` in `U'`. Then the preimage of `V` in `U' ∪_{W'} V'` under the induced map
of gluings is `V'`. -/
theorem isPullback_pushout_inr_map (hf : IsPullback f' w u f) (hg : g' ≫ v = w ≫ g) :
    IsPullback v (pushout.inr f' g') (pushout.inr f g) (pushout.map f' g' f g u v w hf.w hg) := by
  refine IsOpenImmersion.isPullback v (pushout.inr f' g') (pushout.inr f g) _
    (pushout.inr_desc _ _ _) (le_antisymm (fun x hx ↦ ?_) ?_)
  · obtain ⟨y, hy⟩ := hx
    have hcov := opensRange_pushout_inl_sup_opensRange_pushout_inr f' g'
    obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ : x ∈ Set.range (pushout.inl f' g') ∨
        x ∈ Set.range (pushout.inr f' g') := hcov.ge (Set.mem_univ x)
    · have ha : pushout.inl f g (u a) = pushout.inr f g y := by
        rw [hy, ← Scheme.Hom.comp_apply (pushout.inl f' g'), pushout.inl_desc,
          Scheme.Hom.comp_apply]
      obtain ⟨w₀, hw₀, -⟩ := exists_eq_of_pushout_inl_eq_pushout_inr f g ha
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback a w₀ hw₀.symm
      refine ⟨g' ((hf.isoPullback.inv) z), ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← pushout.condition,
        Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Category.assoc,
        IsPullback.isoPullback_inv_fst, Scheme.Hom.comp_apply, hz]
    · exact ⟨b, rfl⟩
  · rintro _ ⟨b, rfl⟩
    exact ⟨v b, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pushout.inr_desc]⟩

/-- Let `u : U' ⟶ U` and `v : V' ⟶ V` be compatible with `w : W' ⟶ W` along open immersions, with
`W'` the preimage of `W` both in `U'` and in `V'`. If `u` and `v` have a property local at the
target, so does the induced map `U' ∪_{W'} V' ⟶ U ∪_W V` of gluings. -/
theorem pushout_map_of_isZariskiLocalAtTarget (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] (hf : IsPullback f' w u f) (hg : IsPullback g' w v g) (hu : P u)
    (hv : P v) : P (pushout.map f' g' f g u v w hf.w hg.w) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun b : Bool ↦ bif b then (pushout.inl f g).opensRange else (pushout.inr f g).opensRange)
    (by rw [iSup_bool_eq]; exact opensRange_pushout_inl_sup_opensRange_pushout_inr f g)
    fun b ↦ ?_
  cases b
  · refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange _ _)).mpr ?_
    have h := (isPullback_pushout_inr_map hf hg.w).flip
    exact (P.arrow_mk_iso_iff (Arrow.isoMk h.isoPullback (Iso.refl _) (by simp))).mp hv
  · refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange _ _)).mpr ?_
    have h := (isPullback_pushout_inl_map hf.w hg).flip
    exact (P.arrow_mk_iso_iff (Arrow.isoMk h.isoPullback (Iso.refl _) (by simp))).mp hu

section Functor

variable {Λ : Type*} [Category Λ] {Vf Uf Sf : Λ ⥤ Scheme.{u}} (α : Vf ⟶ Uf) (β : Vf ⟶ Sf)
  [∀ a, IsOpenImmersion (α.app a)] [∀ a, IsOpenImmersion (β.app a)]

/-- The gluings `Uf a ∪_{Vf a} Sf a` along the open immersions `α a`, `β a`, as a functor. -/
noncomputable def pushoutFunctor : Λ ⥤ Scheme.{u} where
  obj a := pushout (α.app a) (β.app a)
  map f := pushout.map _ _ _ _ (Uf.map f) (Sf.map f) (Vf.map f) (α.naturality f).symm
    (β.naturality f).symm
  map_id a := by simp_rw [CategoryTheory.Functor.map_id]; exact pushout.map_id
  map_comp f g := by simp_rw [CategoryTheory.Functor.map_comp]; exact (pushout.map_comp ..).symm

@[reassoc (attr := simp)]
lemma pushout_inl_pushoutFunctor_map {a b : Λ} (f : a ⟶ b) :
    pushout.inl (α.app a) (β.app a) ≫ (pushoutFunctor α β).map f =
      Uf.map f ≫ pushout.inl (α.app b) (β.app b) :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma pushout_inr_pushoutFunctor_map {a b : Λ} (f : a ⟶ b) :
    pushout.inr (α.app a) (β.app a) ≫ (pushoutFunctor α β).map f =
      Sf.map f ≫ pushout.inr (α.app b) (β.app b) :=
  pushout.inr_desc _ _ _

/-- If the naturality squares of `α` and `β` are pullbacks, every property local at the target of
the transition maps of `Uf` and `Sf` passes to those of the gluings. -/
theorem pushoutFunctor_map_of_isZariskiLocalAtTarget (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] {a b : Λ} (f : a ⟶ b)
    (hα : IsPullback (α.app a) (Vf.map f) (Uf.map f) (α.app b))
    (hβ : IsPullback (β.app a) (Vf.map f) (Sf.map f) (β.app b)) (hU : P (Uf.map f))
    (hS : P (Sf.map f)) : P ((pushoutFunctor α β).map f) :=
  pushout_map_of_isZariskiLocalAtTarget P hα hβ hU hS

end Functor

end TauCeti.AlgebraicGeometry.Scheme
