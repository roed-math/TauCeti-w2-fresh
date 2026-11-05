/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The sheaf of derivations into the ideal of a thickening

For `f : X ⟶ S`, `i : T ⟶ T'` and `a : T ⟶ X`, this file defines the sheaf of abelian groups
`liftDerivationSheaf f i a` on `T'` of derivations of `a⁻¹ 𝒪_X` over `𝒪_S` into the ideal of `i`,
with no affine chart. A section over an open `W` of `T'` is a family of additive maps
`D U V : Γ(X, U) → Γ(T', V)`, one for every open `U` of `X` and every open `V ⊆ W` of `T'` with
`i ⁻¹ V ⊆ a ⁻¹ U`, which

* is compatible with restriction in `V` and in `U`;
* takes values in the ideal of `i`: `i^♯ (D U V x) = 0`;
* kills the sections coming from `S`: `D U V (f^♯ s) = 0`;
* satisfies the Leibniz rule `D U V (x * y) = z * D U V y + w * D U V x` for all `z`, `w` in
  `Γ(T', V)` lifting `a^♯ x` and `a^♯ y` along `i`.

When `i` is a first-order thickening, its ideal is a module over `𝒪_T` and these are the sections
of the sheaf `Hom(a^* Ω_{X/S}, I)` of Stacks, Lemma 37.9.5 (04FJ), under which the lifts of `a`
along `i` form a torsor: the difference `AlgebraicGeometry.Scheme.Hom.appLESub` of two lifts
satisfies the conditions above (`Scheme.Hom.appLESub_mul_of_isFirstOrderThickening`,
`Scheme.Hom.appLE_appLESub_eq_zero`, `Scheme.Hom.appLESub_appLE_eq_zero`). The Leibniz rule is
stated with lifts `z`, `w` because, over a non-affine `V`, the sections `a^♯ x` of `T` need not
lift to `T'`; they do over affine `V`, and the condition is imposed on every `V ⊆ W`.

## Main definitions

* `TauCeti.AlgebraicGeometry.IsLiftDerivation f i a D`: the family `D` over `W` is a derivation
  into the ideal of `i`.
* `TauCeti.AlgebraicGeometry.liftDerivationSubgroup f i a W`: the derivations over `W`.
* `TauCeti.AlgebraicGeometry.liftDerivationSheaf f i a`: the sheaf of derivations on `T'`.

## Main results

* `TauCeti.AlgebraicGeometry.liftDerivationPresheaf_isSheaf`: derivations on the members of an open
  cover that agree on the intersections glue uniquely.

## References

* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ).
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace TauCeti.AlgebraicGeometry

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) (i : T ⟶ T') (a : T ⟶ X)

/-- The pairs `(U, V)` of an open `U` of `X` and an open `V ⊆ W` of `T'` with
`i ⁻¹ V ⊆ a ⁻¹ U`, indexing the components of a derivation over `W`. -/
abbrev LiftDerivationIndex (W : T'.Opens) : Type u :=
  { p : X.Opens × T'.Opens // p.2 ≤ W ∧ i ⁻¹ᵁ p.2 ≤ a ⁻¹ᵁ p.1 }

/-- The index obtained by shrinking the open `V` of `T'` to `V' ⊆ V`. -/
abbrev LiftDerivationIndex.shrink {W : T'.Opens} (p : LiftDerivationIndex i a W) (V' : T'.Opens)
    (hV : V' ≤ p.1.2) : LiftDerivationIndex i a W :=
  ⟨(p.1.1, V'), hV.trans p.2.1, (i.preimage_mono hV).trans p.2.2⟩

/-- A family `D U V : Γ(X, U) →+ Γ(T', V)`, over the pairs `(U, V)` with `V ⊆ W` and
`i ⁻¹ V ⊆ a ⁻¹ U`, is a derivation of `a⁻¹ 𝒪_X` over `𝒪_S` into the ideal of `i`: it is
compatible with restriction, takes values in the ideal of `i`, kills the sections coming from
`S`, and satisfies the Leibniz rule along lifts of `a^♯ x` and `a^♯ y`. -/
structure IsLiftDerivation {W : T'.Opens}
    (D : ∀ p : LiftDerivationIndex i a W, Γ(X, p.1.1) →+ Γ(T', p.1.2)) : Prop where
  /-- Compatibility with restriction to a smaller open `V' ⊆ V` of `T'`. -/
  map_apply (p : LiftDerivationIndex i a W) (V' : T'.Opens) (hV : V' ≤ p.1.2) (x : Γ(X, p.1.1)) :
    T'.presheaf.map (homOfLE hV).op (D p x) = D (p.shrink i a V' hV) x
  /-- Compatibility with restriction to a smaller open `U' ⊆ U` of `X`. -/
  apply_map (p : LiftDerivationIndex i a W) (U' : X.Opens) (hU : i ⁻¹ᵁ p.1.2 ≤ a ⁻¹ᵁ U')
    (e : U' ≤ p.1.1) (x : Γ(X, p.1.1)) :
    D ⟨(U', p.1.2), p.2.1, hU⟩ (X.presheaf.map (homOfLE e).op x) = D p x
  /-- The values lie in the ideal of `i`. -/
  app_apply (p : LiftDerivationIndex i a W) (x : Γ(X, p.1.1)) : i.app p.1.2 (D p x) = 0
  /-- The sections coming from `S` are killed. -/
  apply_appLE (p : LiftDerivationIndex i a W) {O : S.Opens} (e : p.1.1 ≤ f ⁻¹ᵁ O) (s : Γ(S, O)) :
    D p (f.appLE O p.1.1 e s) = 0
  /-- The Leibniz rule, along lifts `z` and `w` of `a^♯ x` and `a^♯ y`. -/
  map_mul (p : LiftDerivationIndex i a W) (x y : Γ(X, p.1.1)) (z w : Γ(T', p.1.2))
    (hz : i.app p.1.2 z = a.appLE p.1.1 (i ⁻¹ᵁ p.1.2) p.2.2 x)
    (hw : i.app p.1.2 w = a.appLE p.1.1 (i ⁻¹ᵁ p.1.2) p.2.2 y) :
    D p (x * y) = z * D p y + w * D p x

/-- The derivations of `a⁻¹ 𝒪_X` over `𝒪_S` into the ideal of `i` over an open `W` of `T'`, as an
additive subgroup of the families of additive maps `Γ(X, U) →+ Γ(T', V)`. -/
def liftDerivationSubgroup (W : T'.Opens) :
    AddSubgroup (∀ p : LiftDerivationIndex i a W, Γ(X, p.1.1) →+ Γ(T', p.1.2)) where
  carrier := { D | IsLiftDerivation f i a D }
  zero_mem' := ⟨by simp, by simp, by simp, by simp, by simp⟩
  add_mem' {D E} hD hE :=
    ⟨fun p V' hV x ↦ by simp [hD.map_apply, hE.map_apply],
      fun p U' hU e x ↦ congrArg₂ (· + ·) (hD.apply_map p U' hU e x) (hE.apply_map p U' hU e x),
      fun p x ↦ by simp [hD.app_apply, hE.app_apply],
      fun p O e s ↦ by simp [hD.apply_appLE, hE.apply_appLE],
      fun p x y z w hz hw ↦ by
        simp only [Pi.add_apply, AddMonoidHom.add_apply, hD.map_mul p x y z w hz hw,
          hE.map_mul p x y z w hz hw]
        ring⟩
  neg_mem' {D} hD :=
    ⟨fun p V' hV x ↦ by simp [hD.map_apply],
      fun p U' hU e x ↦ congrArg Neg.neg (hD.apply_map p U' hU e x),
      fun p x ↦ by simp [hD.app_apply],
      fun p O e s ↦ by simp [hD.apply_appLE],
      fun p x y z w hz hw ↦ by
        simp only [Pi.neg_apply, AddMonoidHom.neg_apply, hD.map_mul p x y z w hz hw]
        ring⟩

variable {f i a} in
theorem mem_liftDerivationSubgroup {W : T'.Opens}
    {D : ∀ p : LiftDerivationIndex i a W, Γ(X, p.1.1) →+ Γ(T', p.1.2)} :
    D ∈ liftDerivationSubgroup f i a W ↔ IsLiftDerivation f i a D :=
  (Iff.rfl)

variable {f i a} in
/-- An element of `liftDerivationSubgroup f i a W` is a derivation. -/
theorem isLiftDerivation_coe {W : T'.Opens} (D : liftDerivationSubgroup f i a W) :
    IsLiftDerivation f i a D.1 :=
  D.2

variable {f i a} in
/-- Two derivations over `W` are equal if their components agree. -/
theorem liftDerivationSubgroup.ext {W : T'.Opens} {D E : liftDerivationSubgroup f i a W}
    (h : ∀ p x, D.1 p x = E.1 p x) : D = E :=
  Subtype.ext <| funext fun p ↦ AddMonoidHom.ext (h p)

/-- Restriction of derivations from `W` to a smaller open `W' ⊆ W`. -/
def liftDerivationSubgroupRestrict {W W' : T'.Opens} (e : W' ≤ W) :
    liftDerivationSubgroup f i a W →+ liftDerivationSubgroup f i a W' where
  toFun D := ⟨fun q ↦ D.1 ⟨q.1, q.2.1.trans e, q.2.2⟩,
    ⟨fun q _ hV x ↦ (isLiftDerivation_coe D).map_apply ⟨q.1, q.2.1.trans e, q.2.2⟩ _ hV x,
      fun q _ hU e' x ↦ (isLiftDerivation_coe D).apply_map ⟨q.1, q.2.1.trans e, q.2.2⟩ _ hU e' x,
      fun q x ↦ (isLiftDerivation_coe D).app_apply ⟨q.1, q.2.1.trans e, q.2.2⟩ x,
      fun q _ e' s ↦ (isLiftDerivation_coe D).apply_appLE ⟨q.1, q.2.1.trans e, q.2.2⟩ e' s,
      fun q x y z w hz hw ↦
        (isLiftDerivation_coe D).map_mul ⟨q.1, q.2.1.trans e, q.2.2⟩ x y z w hz hw⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem liftDerivationSubgroupRestrict_apply {W W' : T'.Opens} (e : W' ≤ W)
    (D : liftDerivationSubgroup f i a W) (q : LiftDerivationIndex i a W') :
    (liftDerivationSubgroupRestrict f i a e D).1 q = D.1 ⟨q.1, q.2.1.trans e, q.2.2⟩ :=
  (rfl)

/-- Restricting a derivation twice is restricting it once. -/
@[simp]
theorem liftDerivationSubgroupRestrict_restrict {W W' W'' : T'.Opens} (e : W' ≤ W) (e' : W'' ≤ W')
    (D : liftDerivationSubgroup f i a W) :
    liftDerivationSubgroupRestrict f i a e' (liftDerivationSubgroupRestrict f i a e D) =
      liftDerivationSubgroupRestrict f i a (e'.trans e) D :=
  (rfl)

variable {f i a} in
/-- Derivations over `W` that agree on the members of an open cover of `W` are equal. -/
theorem liftDerivationSubgroup.ext_of_le_iSup {W : T'.Opens} {ι : Type*} (O : ι → T'.Opens)
    (hO : ∀ j, O j ≤ W) (hW : W ≤ ⨆ j, O j) {D E : liftDerivationSubgroup f i a W}
    (h : ∀ j, liftDerivationSubgroupRestrict f i a (hO j) D =
      liftDerivationSubgroupRestrict f i a (hO j) E) : D = E := by
  refine liftDerivationSubgroup.ext fun p x ↦ T'.IsSheaf.section_ext fun t ht ↦ ?_
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hW (p.2.1 ht))
  refine ⟨p.1.2 ⊓ O j, inf_le_left, ⟨ht, hj⟩, ?_⟩
  rw [(isLiftDerivation_coe D).map_apply, (isLiftDerivation_coe E).map_apply]
  have := congrArg (fun F : liftDerivationSubgroup f i a (O j) ↦
    F.1 ⟨(p.1.1, p.1.2 ⊓ O j), inf_le_right, (i.preimage_mono inf_le_left).trans p.2.2⟩ x) (h j)
  simpa only [liftDerivationSubgroupRestrict_apply] using this

/-- The presheaf of derivations of `a⁻¹ 𝒪_X` over `𝒪_S` into the ideal of `i`, on `T'`. -/
@[expose] noncomputable def liftDerivationPresheaf : TopCat.Presheaf AddCommGrpCat.{u} T' where
  obj W := AddCommGrpCat.of (liftDerivationSubgroup f i a W.unop)
  map e := AddCommGrpCat.ofHom (liftDerivationSubgroupRestrict f i a e.unop.le)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

@[simp]
theorem liftDerivationPresheaf_map_apply {W W' : T'.Opens} (e : W' ⟶ W)
    (D : liftDerivationSubgroup f i a W) (q : LiftDerivationIndex i a W') :
    ((liftDerivationPresheaf f i a).map e.op D : liftDerivationSubgroup f i a W').1 q =
      D.1 ⟨q.1, q.2.1.trans e.le, q.2.2⟩ :=
  (rfl)

section Gluing

variable {f i a} {ι : Type u} {U : ι → T'.Opens}

/-- A component of a derivation over `⨆ U`, cut down to the member `U j` of the cover. -/
private abbrev LiftDerivationIndex.cut (p : LiftDerivationIndex i a (iSup U)) (j : ι) :
    LiftDerivationIndex i a (U j) :=
  ⟨(p.1.1, p.1.2 ⊓ U j), inf_le_right, (i.preimage_mono inf_le_left).trans p.2.2⟩

private lemma le_iSup_inf (p : LiftDerivationIndex i a (iSup U)) : p.1.2 ≤ ⨆ j, p.1.2 ⊓ U j :=
  fun x hx ↦ by
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (p.2.1 hx)
    exact Opens.mem_iSup.2 ⟨j, hx, hj⟩

variable (sf : ∀ j, liftDerivationSubgroup f i a (U j))
  (hsf : ∀ j k, liftDerivationSubgroupRestrict f i a (inf_le_left (b := U k)) (sf j) =
    liftDerivationSubgroupRestrict f i a inf_le_right (sf k))

include hsf in
/-- Two members of a compatible family of derivations agree on indices below both members. -/
private lemma apply_eq_apply_of_compatible {j k : ι} (q : X.Opens × T'.Opens)
    (hj : q.2 ≤ U j) (hk : q.2 ≤ U k) (hq : i ⁻¹ᵁ q.2 ≤ a ⁻¹ᵁ q.1) (x : Γ(X, q.1)) :
    (sf j).1 ⟨q, hj, hq⟩ x = (sf k).1 ⟨q, hk, hq⟩ x :=
  DFunLike.congr_fun (congrFun (congrArg Subtype.val (hsf j k)) ⟨q, le_inf hj hk, hq⟩) x

include hsf in
/-- The components of a compatible family of derivations glue in `𝒪_{T'}`. -/
private lemma existsUnique_glue (p : LiftDerivationIndex i a (iSup U)) (x : Γ(X, p.1.1)) :
    ∃! t : Γ(T', p.1.2), ∀ j,
      T'.presheaf.map (homOfLE inf_le_left).op t = (sf j).1 (p.cut j) x := by
  refine T'.sheaf.existsUnique_gluing' (U := fun j ↦ p.1.2 ⊓ U j) p.1.2
    (fun j ↦ homOfLE inf_le_left) (le_iSup_inf p) _ fun j k ↦ ?_
  -- `IsCompatible` is stated with the generic inclusions `infLELeft` and `infLERight`.
  change T'.presheaf.map (homOfLE inf_le_left).op ((sf j).1 (p.cut j) x) =
    T'.presheaf.map (homOfLE inf_le_right).op ((sf k).1 (p.cut k) x)
  rw [(isLiftDerivation_coe (sf j)).map_apply, (isLiftDerivation_coe (sf k)).map_apply]
  exact apply_eq_apply_of_compatible sf hsf (p.1.1, (p.1.2 ⊓ U j) ⊓ (p.1.2 ⊓ U k))
    (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    ((i.preimage_mono (inf_le_left.trans inf_le_left)).trans p.2.2) x

/-- The glued component of a compatible family of derivations. -/
private noncomputable def glueApply (p : LiftDerivationIndex i a (iSup U)) (x : Γ(X, p.1.1)) :
    Γ(T', p.1.2) :=
  (existsUnique_glue sf hsf p x).exists.choose

private lemma glueApply_spec (p : LiftDerivationIndex i a (iSup U)) (x : Γ(X, p.1.1)) (j : ι) :
    T'.presheaf.map (homOfLE inf_le_left).op (glueApply sf hsf p x) = (sf j).1 (p.cut j) x :=
  (existsUnique_glue sf hsf p x).exists.choose_spec j

/-- Sections of `𝒪_{T'}` over `V` that agree on every `V ⊓ U j` are equal. -/
private lemma eq_of_inf_eq (p : LiftDerivationIndex i a (iSup U)) {s t : Γ(T', p.1.2)}
    (H : ∀ j, T'.presheaf.map (homOfLE (inf_le_left (b := U j))).op s =
      T'.presheaf.map (homOfLE inf_le_left).op t) : s = t :=
  T'.sheaf.eq_of_locally_eq' (U := fun j ↦ p.1.2 ⊓ U j) p.1.2 (fun _ ↦ homOfLE inf_le_left)
    (le_iSup_inf p) s t H

private lemma glueApply_eq (p : LiftDerivationIndex i a (iSup U)) (x : Γ(X, p.1.1))
    (t : Γ(T', p.1.2))
    (ht : ∀ j, T'.presheaf.map (homOfLE inf_le_left).op t = (sf j).1 (p.cut j) x) :
    glueApply sf hsf p x = t :=
  eq_of_inf_eq p fun j ↦ (glueApply_spec sf hsf p x j).trans (ht j).symm

/-- The glued component of a compatible family of derivations, as an additive map. -/
private noncomputable def glueHom (p : LiftDerivationIndex i a (iSup U)) :
    Γ(X, p.1.1) →+ Γ(T', p.1.2) where
  toFun := glueApply sf hsf p
  map_zero' := glueApply_eq sf hsf p 0 0 fun j ↦ by simp
  map_add' x y := glueApply_eq sf hsf p _ _ fun j ↦ by
    simp [glueApply_spec]

private lemma glueHom_spec (p : LiftDerivationIndex i a (iSup U)) (x : Γ(X, p.1.1)) (j : ι) :
    T'.presheaf.map (homOfLE inf_le_left).op (glueHom sf hsf p x) = (sf j).1 (p.cut j) x :=
  glueApply_spec sf hsf p x j

/-- Restricting along `T'` and pulling back along `i` commute. -/
private lemma app_map_apply {V V' : T'.Opens} (e : V' ≤ V) (t : Γ(T', V)) :
    T.presheaf.map (homOfLE (i.preimage_mono e)).op (i.app V t) =
      i.app V' (T'.presheaf.map (homOfLE e).op t) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

/-- Two successive restrictions are one restriction. -/
private lemma map_map_apply {Z : Scheme.{u}} {V₁ V₂ V₃ : Z.Opens} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂)
    (t : Γ(Z, V₁)) :
    Z.presheaf.map (homOfLE h₂).op (Z.presheaf.map (homOfLE h₁).op t) =
      Z.presheaf.map (homOfLE (h₂.trans h₁)).op t := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The glued family is a derivation. -/
private lemma isLiftDerivation_glueHom : IsLiftDerivation f i a (glueHom sf hsf) := by
  refine ⟨fun p V' hV x ↦ ?_, fun p U' hU e x ↦ ?_, fun p x ↦ ?_, fun p O e s ↦ ?_,
    fun p x y z w hz hw ↦ ?_⟩
  · refine eq_of_inf_eq (p.shrink i a V' hV) fun j ↦ ?_
    refine ((map_map_apply _ _ _).trans ?_).trans
      (glueHom_spec sf hsf (p.shrink i a V' hV) x j).symm
    have h : V' ⊓ U j ≤ p.1.2 ⊓ U j := inf_le_inf_right _ hV
    refine (map_map_apply inf_le_left h _).symm.trans ?_
    exact (congrArg _ (glueHom_spec sf hsf p x j)).trans
      ((isLiftDerivation_coe (sf j)).map_apply (p.cut j) _ h x)
  · refine eq_of_inf_eq p fun j ↦ ?_
    exact (glueHom_spec sf hsf ⟨(U', p.1.2), p.2.1, hU⟩ _ j).trans
      (((isLiftDerivation_coe (sf j)).apply_map (p.cut j) U'
        ((i.preimage_mono inf_le_left).trans hU) e x).trans
        (glueHom_spec sf hsf p x j).symm)
  · -- `T` is covered by the `i ⁻¹ (V ⊓ U j)`.
    have H : ∀ j, T.presheaf.map (homOfLE (i.preimage_mono (inf_le_left (b := U j)))).op
        (i.app p.1.2 (glueHom sf hsf p x)) =
          T.presheaf.map (homOfLE (i.preimage_mono (inf_le_left (b := U j)))).op 0 := fun j ↦ by
      rw [app_map_apply (i := i) (inf_le_left (b := U j)), glueHom_spec,
        (isLiftDerivation_coe (sf j)).app_apply (p.cut j) x, map_zero]
    exact T.sheaf.eq_of_locally_eq' (U := fun j ↦ i ⁻¹ᵁ (p.1.2 ⊓ U j)) (i ⁻¹ᵁ p.1.2)
      (fun j ↦ homOfLE (i.preimage_mono inf_le_left))
      (by rw [← Scheme.Hom.preimage_iSup]; exact i.preimage_mono (le_iSup_inf p)) _ 0 H
  · refine eq_of_inf_eq p fun j ↦ ?_
    refine (glueHom_spec sf hsf p _ j).trans ?_
    rw [(isLiftDerivation_coe (sf j)).apply_appLE (p.cut j) e s, map_zero]
  · refine eq_of_inf_eq p fun j ↦ ?_
    have hlift (z : Γ(T', p.1.2)) (x : Γ(X, p.1.1))
        (hz : i.app p.1.2 z = a.appLE p.1.1 (i ⁻¹ᵁ p.1.2) p.2.2 x) :
        i.app (p.1.2 ⊓ U j) (T'.presheaf.map (homOfLE inf_le_left).op z) =
          a.appLE p.1.1 (i ⁻¹ᵁ (p.1.2 ⊓ U j)) (p.cut j).2.2 x := by
      rw [← app_map_apply, hz, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    refine (glueHom_spec sf hsf p _ j).trans ?_
    simp only [map_add, map_mul, glueHom_spec]
    exact (isLiftDerivation_coe (sf j)).map_mul (p.cut j) x y _ _ (hlift z x hz) (hlift w y hw)

/-- The glued derivation. -/
private noncomputable def glue : liftDerivationSubgroup f i a (iSup U) :=
  ⟨glueHom sf hsf, isLiftDerivation_glueHom sf hsf⟩

end Gluing

/-- The presheaf of derivations is a sheaf: derivations on the members of an open cover that agree
on the intersections glue uniquely. -/
theorem liftDerivationPresheaf_isSheaf : (liftDerivationPresheaf f i a).IsSheaf := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).2 fun ι U sf hsf ↦ ?_
  replace hsf : ∀ j k, liftDerivationSubgroupRestrict f i a (inf_le_left (b := U k)) (sf j) =
      liftDerivationSubgroupRestrict f i a inf_le_right (sf k) := hsf
  refine ⟨glue sf hsf, fun j ↦ Subtype.ext <| funext fun q ↦ AddMonoidHom.ext fun x ↦ ?_,
    fun D hD ↦ Subtype.ext <| funext fun p ↦ AddMonoidHom.ext fun x ↦ ?_⟩
  · -- On `q` below `U j`, the glued component restricts on every `V ⊓ U k` as `sf j` does.
    let p : LiftDerivationIndex i a (iSup U) := ⟨q.1, q.2.1.trans (le_iSup U j), q.2.2⟩
    refine eq_of_inf_eq p fun k ↦ ?_
    -- Unfold the restriction of the glued derivation to `U j`.
    change T'.presheaf.map _ (glueHom sf hsf p x) = T'.presheaf.map _ ((sf j).1 q x)
    refine (glueHom_spec sf hsf p x k).trans ?_
    rw [(isLiftDerivation_coe (sf j)).map_apply]
    exact (apply_eq_apply_of_compatible sf hsf (q.1.1, q.1.2 ⊓ U k)
      (inf_le_left.trans q.2.1) inf_le_right ((i.preimage_mono inf_le_left).trans q.2.2) x).symm
  · replace hD (k : ι) (q : LiftDerivationIndex i a (U k)) (y : Γ(X, q.1.1)) :
        D.1 ⟨q.1, q.2.1.trans (le_iSup U k), q.2.2⟩ y = (sf k).1 q y :=
      DFunLike.congr_fun (congrFun (congrArg Subtype.val (hD k)) q) y
    symm
    refine glueApply_eq sf hsf p x _ fun k ↦ ?_
    rw [(isLiftDerivation_coe D).map_apply]
    exact hD k (p.cut k) x

/-- The sheaf of derivations of `a⁻¹ 𝒪_X` over `𝒪_S` into the ideal of `i`, on `T'`: its
sections over `W` are the families of additive maps `D U V : Γ(X, U) → Γ(T', V)`, for `V ⊆ W`
and `i ⁻¹ V ⊆ a ⁻¹ U`, satisfying `IsLiftDerivation f i a`. -/
@[expose] noncomputable def liftDerivationSheaf : TopCat.Sheaf AddCommGrpCat.{u} T' :=
  ⟨liftDerivationPresheaf f i a, liftDerivationPresheaf_isSheaf f i a⟩

end TauCeti.AlgebraicGeometry
