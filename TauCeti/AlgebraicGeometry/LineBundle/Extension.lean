/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
public import TauCeti.AlgebraicGeometry.LineBundle.Power
import TauCeti.Algebra.Group.Action.Pow
import TauCeti.AlgebraicGeometry.Modules.Localization

/-!
# Tensor powers of sections, and extending sections from nonvanishing loci

A section `s` of a line bundle `L` over an open `U` of a scheme `X` has tensor powers `s^{⊗n}`,
sections of `L^{⊗n}`, built from the tensor product of sections
`TauCeti.AlgebraicGeometry.InvertibleSheaf.tmul`. With them we prove the two halves of the lemma
of Stacks, Tag 01PW, for quasi-compact quasi-separated `U` and sections of line bundles: a section
vanishing on the nonvanishing locus `X_s` is killed by a power of `s`, and every section over
`X_s` extends to `U` after multiplication by a power of `s`. For the structure sheaf, where `X_s`
is a basic open set, these are
`AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_zero_of_isCompact` and
`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict_of_qcqs`, to which the
proofs reduce locally.

## Main declarations

* `TauCeti.AlgebraicGeometry.InvertibleSheaf.oneSection`: the unit section of the trivial line
  bundle.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.sectionPow`: the tensor power `s^{⊗n}`, with
  `sectionPow_map`, `sectionPow_smul` and `nonvanishingLocus_sectionPow_succ`.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.exists_tmul_sectionPow_eq_zero`: sections vanishing
  on `X_s` are killed by powers of `s`.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.exists_map_eq_tmul_sectionPow`: sections over `X_s`
  extend after multiplication by a power of `s`.

## References

* The Stacks Project, Tag 01PW.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

universe u

variable {X : Scheme.{u}} {L K : InvertibleSheaf X} {U : X.Opens}

/-- The unit section `1` of the trivial line bundle over `U`. -/
noncomputable def oneSection (U : X.Opens) : Γ((trivial X).obj, U) :=
  (trivialObjIsoUnit X).inv.app U
    (show Γ(_root_.SheafOfModules.unit X.ringCatSheaf, U) from (1 : Γ(X, U)))

/-- The unit section restricts to the unit section. -/
lemma oneSection_map {V : X.Opens} (i : V ⟶ U) :
    (trivial X).obj.presheaf.map i.op (oneSection U) = oneSection V := by
  have h := (trivialObjIsoUnit X).inv.mapPresheaf.naturality_apply i.op
    (show Γ(_root_.SheafOfModules.unit X.ringCatSheaf, U) from (1 : Γ(X, U)))
  simp only [Scheme.Modules.mapPresheaf_app, unop_op] at h
  rw [oneSection, ← h]
  exact congrArg _ (map_one (X.presheaf.map i.op).hom)

/-- The unit section vanishes nowhere on its domain. -/
theorem nonvanishingLocus_oneSection (U : X.Opens) :
    (trivial X).obj.nonvanishingLocus (oneSection U) = U := by
  exact (Scheme.Modules.nonvanishingLocus_hom_app (trivialObjIsoUnit X).symm _).trans
    ((Scheme.Modules.nonvanishingLocus_unit (1 : Γ(X, U))).trans X.basicOpen_one)

/-- The **tensor power** `s^{⊗n} ∈ Γ(L^{⊗n}, U)` of a section `s` of `L` over `U`, defined by
`s^{⊗0} = 1` and `s^{⊗(n+1)} = s^{⊗n} ⊗ s`, matching `InvertibleSheaf.tensorPow`. -/
@[expose]
noncomputable def sectionPow (s : Γ(L.obj, U)) : (n : ℕ) → Γ((L.tensorPow n).obj, U)
  | 0 => oneSection U
  | n + 1 => tmul (sectionPow s n) s

/-- The zeroth tensor power of a section is the unit section. -/
@[simp]
lemma sectionPow_zero (s : Γ(L.obj, U)) : sectionPow s 0 = oneSection U :=
  rfl

/-- The `(n + 1)`-st tensor power of `s` is `s^{⊗n} ⊗ s`. -/
lemma sectionPow_succ (s : Γ(L.obj, U)) (n : ℕ) :
    sectionPow s (n + 1) = tmul (sectionPow s n) s :=
  rfl

/-- Tensor powers of sections commute with restriction. -/
lemma sectionPow_map {V : X.Opens} (i : V ⟶ U) (s : Γ(L.obj, U)) (n : ℕ) :
    (L.tensorPow n).obj.presheaf.map i.op (sectionPow s n) =
      sectionPow (L.obj.presheaf.map i.op s) n := by
  induction n with
  | zero => exact oneSection_map i
  | succ n ih => rw [sectionPow_succ, sectionPow_succ, ← ih]; exact tmul_map i _ _

/-- The tensor power of a regular multiple: `(r • s)^{⊗n} = rⁿ • s^{⊗n}`. -/
lemma sectionPow_smul (r : Γ(X, U)) (s : Γ(L.obj, U)) (n : ℕ) :
    sectionPow (r • s) n = r ^ n • sectionPow s n := by
  induction n with
  | zero => rw [pow_zero, one_smul]; rfl
  | succ n ih =>
    rw [sectionPow_succ, sectionPow_succ, ih, smul_tmul, tmul_smul, smul_smul, pow_succ]
    rfl

/-- A positive tensor power `s^{⊗(n+1)}` vanishes nowhere exactly where `s` does. -/
theorem nonvanishingLocus_sectionPow_succ (s : Γ(L.obj, U)) (n : ℕ) :
    (L.tensorPow (n + 1)).obj.nonvanishingLocus (sectionPow s (n + 1)) =
      L.obj.nonvanishingLocus s := by
  induction n with
  | zero =>
    rw [sectionPow_succ]
    refine (nonvanishingLocus_tmul _ _).trans ?_
    exact (congrArg (· ⊓ _) (nonvanishingLocus_oneSection U)).trans
      (inf_eq_right.mpr (Scheme.Modules.nonvanishingLocus_le s))
  | succ n ih =>
    rw [sectionPow_succ]
    refine (nonvanishingLocus_tmul _ _).trans ?_
    rw [ih, inf_idem]

/-- Near each point of `U`, the line bundle `L` has a generator `e` on an affine open `V ⊆ U`, and
`s = r • e` there; then `X_s ∩ V` is the basic open set `D(r)`. -/
private lemma exists_isAffineOpen_smul_eq (s : Γ(L.obj, U)) {x : X} (hx : x ∈ U) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (hVU : V ≤ U) (r : Γ(X, V))
      (e : Γ(L.obj, V)), L.obj.nonvanishingLocus e = V ∧
        r • e = L.obj.presheaf.map (homOfLE hVU).op s ∧
        X.basicOpen r = V ⊓ L.obj.nonvanishingLocus s := by
  obtain ⟨V₀, t, hx₀⟩ := Scheme.Modules.exists_mem_trivialization L.obj x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((V₀ ⊓ U : X.Opens) : Set X) from ⟨hx₀, hx⟩) (V₀ ⊓ U).isOpen
  have hVV₀ : V ≤ V₀ := fun y hy ↦ (hVle hy).1
  have hVU : V ≤ U := fun y hy ↦ (hVle hy).2
  -- On `V`, the restriction of `L` is generated by the restricted basis section `e`.
  let e : Γ(L.obj, V) := L.obj.presheaf.map (homOfLE hVV₀).op
    (Scheme.Modules.trivializationGenerator L.obj t)
  have he : L.obj.nonvanishingLocus e = V := by
    rw [Scheme.Modules.nonvanishingLocus_map,
      Scheme.Modules.nonvanishingLocus_trivializationGenerator, inf_eq_left.mpr hVV₀]
  obtain ⟨r, hr⟩ := Scheme.Modules.surjective_smul_of_le_nonvanishingLocus he.ge
    (L.obj.presheaf.map (homOfLE hVU).op s)
  refine ⟨V, hV, hxV, hVU, r, e, he, hr, ?_⟩
  have := Scheme.Modules.nonvanishingLocus_map (homOfLE hVU) s
  rw [← hr, Scheme.Modules.nonvanishingLocus_smul, he] at this
  rw [← this, inf_eq_left.mpr (X.basicOpen_le r)]

/-- Near each point of `U`, a section `w` vanishing on `X_s` is killed by the powers of `s` from
some exponent on. -/
private lemma exists_map_tmul_sectionPow_eq_zero {F : InvertibleSheaf X} (s : Γ(L.obj, U))
    (w : Γ(F.obj, U))
    (hw : F.obj.presheaf.map (homOfLE (Scheme.Modules.nonvanishingLocus_le s)).op w = 0)
    {x : X} (hx : x ∈ U) :
    ∃ (V : X.Opens) (_ : x ∈ V) (hVU : V ≤ U) (m : ℕ), ∀ n, m ≤ n →
      ((L.tensorPow n).tensorProduct F).obj.presheaf.map (homOfLE hVU).op
        (tmul (sectionPow s n) w) = 0 := by
  obtain ⟨V, hV, hxV, hVU, r, e, -, hr, hDr⟩ := exists_isAffineOpen_smul_eq s hx
  -- The section `w` vanishes on `X_s ∩ V = D(r)`, so a power of `r` kills it on `V`.
  obtain ⟨m, hm⟩ := F.obj.exists_pow_smul_eq_zero_of_isCompact hV.isCompact r
    (F.obj.presheaf.map (homOfLE hVU).op w) (by
      rw [Scheme.Modules.basicOpenRestrict_apply, ← Functor.map_comp_apply, ← op_comp,
        homOfLE_comp, ← homOfLE_comp (hDr.trans_le inf_le_right)
          (Scheme.Modules.nonvanishingLocus_le s), op_comp, Functor.map_comp_apply, hw, map_zero])
  refine ⟨V, hxV, hVU, m, fun n hn ↦ ?_⟩
  rw [tmul_map, sectionPow_map, ← hr, sectionPow_smul, smul_tmul, ← tmul_smul,
    pow_smul_eq_zero_of_le hn hm, tmul_zero]

/-- If `s` vanishes nowhere on `U`, so do all its tensor powers. -/
theorem nonvanishingLocus_sectionPow_of_le {s : Γ(L.obj, U)}
    (h : U ≤ L.obj.nonvanishingLocus s) (n : ℕ) :
    (L.tensorPow n).obj.nonvanishingLocus (sectionPow s n) = U := by
  cases n with
  | zero => exact nonvanishingLocus_oneSection U
  | succ n =>
    exact (nonvanishingLocus_sectionPow_succ s n).trans
      (le_antisymm (Scheme.Modules.nonvanishingLocus_le s) h)

/-- The nonvanishing locus of a section lies in that of each of its tensor powers. -/
theorem nonvanishingLocus_le_nonvanishingLocus_sectionPow (s : Γ(L.obj, U)) (n : ℕ) :
    L.obj.nonvanishingLocus s ≤ (L.tensorPow n).obj.nonvanishingLocus (sectionPow s n) := by
  cases n with
  | zero =>
    exact (Scheme.Modules.nonvanishingLocus_le s).trans (nonvanishingLocus_oneSection U).ge
  | succ n => rw [nonvanishingLocus_sectionPow_succ]

/-- **Sections vanishing on `X_s` are killed by powers of `s`** (Stacks, Tag 01PW (1)). Let `U` be
quasi-compact, `s` a section of `L` over `U`, and `w` a section of a line bundle `F` over `U` whose
restriction to `X_s` vanishes. Then `s^{⊗n} ⊗ w = 0` for all large `n`. Locally on an affine open
`V` where `L` is generated by `e` and `s = r • e`, the open `X_s ∩ V` is the basic open `D(r)`,
and a power of `r` kills `w` on `V` (`Scheme.Modules.exists_pow_smul_eq_zero_of_isCompact`). -/
theorem exists_tmul_sectionPow_eq_zero {F : InvertibleSheaf X} (hU : IsCompact (U : Set X))
    (s : Γ(L.obj, U)) (w : Γ(F.obj, U))
    (hw : F.obj.presheaf.map (homOfLE (Scheme.Modules.nonvanishingLocus_le s)).op w = 0) :
    ∃ m : ℕ, ∀ n, m ≤ n → tmul (sectionPow s n) w = 0 := by
  choose V hxV hVU m hm using fun x : U ↦ exists_map_tmul_sectionPow_eq_zero s w hw x.2
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun x : U ↦ (V x : Set X))
    (fun x ↦ (V x).isOpen)
    fun y hy ↦ Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxV _⟩
  refine ⟨t.sup m, fun n hn ↦ TopCat.Sheaf.eq_of_locally_eq'
    (⟨_, ((L.tensorPow n).tensorProduct F).obj.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun i : t ↦ V i) U (fun i ↦ homOfLE (hVU i)) (fun y hy ↦ ?_) _ _ fun i ↦ ?_⟩
  · obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (ht hy)
    exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hyi⟩
  · change ((L.tensorPow n).tensorProduct F).obj.presheaf.map _ _ =
      ((L.tensorPow n).tensorProduct F).obj.presheaf.map _ _
    rw [map_zero]
    exact hm i n ((Finset.le_sup i.2).trans hn)

/-- **Sections over `X_s` extend after multiplication by a power of `s`** (Stacks, Tag 01PW (2)).
Let `U` be quasi-compact and quasi-separated, `s` a section of `L` over `U`, and `y` a section of a
line bundle `F` over `X_s`. Then for some `a` and `b` the section `s^{⊗b} ⊗ s^{⊗a} ⊗ y` over `X_s`
is the restriction of a section over `U`. On an affine open `V` where `s = r • e` for a generator
`e`, some `rᵃ • y` extends from `D(r) = X_s ∩ V` to `V`
(`Scheme.Modules.exists_pow_smul_eq_map`); the local extensions `e^{⊗a} ⊗ rᵃ • y` agree on
`X_s`, so by `exists_tmul_sectionPow_eq_zero` they glue after multiplication by `s^{⊗b}`. -/
theorem exists_map_eq_tmul_sectionPow {F : InvertibleSheaf X} (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) (s : Γ(L.obj, U))
    (y : Γ(F.obj, L.obj.nonvanishingLocus s)) :
    ∃ (a b : ℕ)
      (ξ : Γ(((L.tensorPow b).tensorProduct ((L.tensorPow a).tensorProduct F)).obj, U)),
      ((L.tensorPow b).tensorProduct ((L.tensorPow a).tensorProduct F)).obj.presheaf.map
          (homOfLE (Scheme.Modules.nonvanishingLocus_le s)).op ξ =
        tmul (sectionPow (L.obj.presheaf.map
            (homOfLE (Scheme.Modules.nonvanishingLocus_le s)).op s) b)
          (tmul (sectionPow (L.obj.presheaf.map
            (homOfLE (Scheme.Modules.nonvanishingLocus_le s)).op s) a) y) := by
  have hDU := Scheme.Modules.nonvanishingLocus_le s
  -- Cover `U` by finitely many affine opens `V i` on which `L` is generated by `e i` and
  -- `s = r i • e i`, so that `X_s ∩ V i = D(r i)`.
  choose V hV hxV hVU r e he hr hDr using fun x : U ↦ exists_isAffineOpen_smul_eq s x.2
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun x : U ↦ (V x : Set X))
    (fun x ↦ (V x).isOpen)
    fun y hy ↦ Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxV _⟩
  have hUV : U ≤ ⨆ i : t, V i := fun y hy ↦ by
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (ht hy)
    exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hyi⟩
  have hDrD (i : U) : X.basicOpen (r i) ≤ L.obj.nonvanishingLocus s :=
    (hDr i).trans_le inf_le_right
  -- On `V i`, some `r i ^ a i • y` extends to a section `z i`.
  choose a z hz using fun i : U ↦ F.obj.exists_pow_smul_eq_map (hV i) (r i) rfl
    (X.basicOpen_le (r i)) (F.obj.presheaf.map (homOfLE (hDrD i)).op y)
  let A := t.sup a
  -- The local sections `e i ^ A ⊗ r i ^ (A - a i) • z i` restrict to `s ^ A ⊗ y` on
  -- `X_s ∩ V i`.
  let x (i : U) : Γ(((L.tensorPow A).tensorProduct F).obj, V i) :=
    tmul (sectionPow (e i) A) (r i ^ (A - a i) • z i)
  have hx (i : t) {W : X.Opens} (hW : W ≤ X.basicOpen (r i)) :
      ((L.tensorPow A).tensorProduct F).obj.presheaf.map
          (homOfLE (hW.trans (X.basicOpen_le _))).op (x i) =
        tmul (sectionPow (L.obj.presheaf.map (homOfLE ((hW.trans (hDrD i)).trans hDU)).op s) A)
          (F.obj.presheaf.map (homOfLE (hW.trans (hDrD i))).op y) := by
    have hz' := congrArg (F.obj.presheaf.map (homOfLE hW).op) (hz i)
    simp only [Scheme.Modules.map_smul, map_pow, ← Functor.map_comp_apply, ← op_comp,
      homOfLE_comp] at hz'
    have hr' := congrArg (L.obj.presheaf.map (homOfLE (hW.trans (X.basicOpen_le _))).op) (hr i)
    simp only [Scheme.Modules.map_smul, ← Functor.map_comp_apply, ← op_comp,
      homOfLE_comp] at hr'
    simp only [x, tmul_map, sectionPow_map, Scheme.Modules.map_smul, map_pow, ← hz', smul_smul,
      ← pow_add, ← hr', sectionPow_smul, smul_tmul, tmul_smul]
    rw [Nat.sub_add_cancel (Finset.le_sup (f := a) i.2)]
  -- The local sections `x i` and `x j` agree on `X_s ∩ V i ∩ V j`, so a power of `s` kills
  -- their difference on the quasi-compact open `V i ∩ V j`.
  have H (p : t × t) : ∃ m : ℕ, ∀ n, m ≤ n →
      tmul (sectionPow (L.obj.presheaf.map
          (homOfLE (inf_le_left.trans (hVU p.1) : V p.1 ⊓ V p.2 ≤ U)).op s) n)
        (((L.tensorPow A).tensorProduct F).obj.presheaf.map
            (homOfLE inf_le_left : V p.1 ⊓ V p.2 ⟶ V p.1).op (x p.1) -
          ((L.tensorPow A).tensorProduct F).obj.presheaf.map
            (homOfLE inf_le_right : V p.1 ⊓ V p.2 ⟶ V p.2).op (x p.2)) = 0 := by
    refine exists_tmul_sectionPow_eq_zero (hU' _ _ (hVU p.1) (V p.1).isOpen (hV p.1).isCompact
      (hVU p.2) (V p.2).isOpen (hV p.2).isCompact) _ _ ?_
    have hN := Scheme.Modules.nonvanishingLocus_map
      (homOfLE (inf_le_left.trans (hVU p.1) : V p.1 ⊓ V p.2 ≤ U)) s
    have h₁ : L.obj.nonvanishingLocus (L.obj.presheaf.map
        (homOfLE (inf_le_left.trans (hVU p.1) : V p.1 ⊓ V p.2 ≤ U)).op s) ≤
        X.basicOpen (r p.1) :=
      hN.le.trans ((hDr p.1).ge.trans' (inf_le_inf_right _ inf_le_left))
    have h₂ : L.obj.nonvanishingLocus (L.obj.presheaf.map
        (homOfLE (inf_le_left.trans (hVU p.1) : V p.1 ⊓ V p.2 ≤ U)).op s) ≤
        X.basicOpen (r p.2) :=
      hN.le.trans ((hDr p.2).ge.trans' (inf_le_inf_right _ inf_le_right))
    rw [map_sub, sub_eq_zero, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
      ← op_comp, homOfLE_comp, homOfLE_comp, hx p.1 h₁, hx p.2 h₂]
  choose m hm using H
  -- After multiplication by `s ^ B`, the local sections `x i` glue to a section `ξ` over `U`.
  let B := Finset.univ.sup m
  let ξ (i : t) : Γ(((L.tensorPow B).tensorProduct ((L.tensorPow A).tensorProduct F)).obj, V i) :=
    tmul (sectionPow (L.obj.presheaf.map (homOfLE (hVU i)).op s) B) (x i)
  have hc : TopCat.Presheaf.IsCompatible
      ((L.tensorPow B).tensorProduct ((L.tensorPow A).tensorProduct F)).obj.presheaf
      (fun i : t ↦ V i) ξ := by
    intro i j
    have h := hm (i, j) B (Finset.le_sup (f := m) (Finset.mem_univ (i, j)))
    rw [tmul_sub, sub_eq_zero] at h
    change ((L.tensorPow B).tensorProduct ((L.tensorPow A).tensorProduct F)).obj.presheaf.map
        (homOfLE inf_le_left).op _ =
      ((L.tensorPow B).tensorProduct ((L.tensorPow A).tensorProduct F)).obj.presheaf.map
        (homOfLE inf_le_right).op _
    simpa only [ξ, tmul_map, sectionPow_map, ← Functor.map_comp_apply, ← op_comp,
      homOfLE_comp] using h
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨((L.tensorPow B).tensorProduct ((L.tensorPow A).tensorProduct F)).obj.presheaf,
      ((L.tensorPow B).tensorProduct ((L.tensorPow A).tensorProduct F)).obj.isSheaf⟩ :
      TopCat.Sheaf AddCommGrpCat X) (fun i : t ↦ V i) U
    (fun i ↦ homOfLE (hVU i)) hUV ξ hc
  -- On each `X_s ∩ V i`, the glued section is `s ^ B ⊗ s ^ A ⊗ y`.
  refine ⟨A, B, g, TopCat.Sheaf.eq_of_locally_eq'
    (⟨((L.tensorPow B).tensorProduct ((L.tensorPow A).tensorProduct F)).obj.presheaf,
      ((L.tensorPow B).tensorProduct ((L.tensorPow A).tensorProduct F)).obj.isSheaf⟩ :
      TopCat.Sheaf AddCommGrpCat X)
    (fun i : t ↦ V i ⊓ L.obj.nonvanishingLocus s) _ (fun i ↦ homOfLE inf_le_right)
    (fun y hy ↦ ?_) _ _ fun i ↦ ?_⟩
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hUV (hDU hy))
    exact Opens.mem_iSup.mpr ⟨i, hi, hy⟩
  · change ((L.tensorPow B).tensorProduct ((L.tensorPow A).tensorProduct F)).obj.presheaf.map _ _ =
      ((L.tensorPow B).tensorProduct ((L.tensorPow A).tensorProduct F)).obj.presheaf.map _ _
    have hW : V i ⊓ L.obj.nonvanishingLocus s ≤ X.basicOpen (r i) := (hDr i).ge
    have hg' := congrArg
      (((L.tensorPow B).tensorProduct ((L.tensorPow A).tensorProduct F)).obj.presheaf.map
        (homOfLE (inf_le_left : V i ⊓ L.obj.nonvanishingLocus s ≤ V i)).op) (hg i)
    simp only [ξ, tmul_map, sectionPow_map, ← Functor.map_comp_apply, ← op_comp,
      homOfLE_comp] at hg' ⊢
    rw [hg', hx i hW]

end TauCeti.AlgebraicGeometry.InvertibleSheaf
