/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Depth.Basic
public import TauCeti.Algebra.Homology.LocalCohomology.DegreeZero
import TauCeti.Algebra.Category.ModuleCat.Ext.Basic
import TauCeti.Algebra.Homology.Ext.ProjectiveResolution
import TauCeti.RingTheory.Depth.WeaklyRegular
import TauCeti.RingTheory.Finiteness.Nakayama
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures

/-!
# Local cohomology and depth

Mathlib defines `localCohomology I q` as the colimit over `n` of the derived-functor
`Ext^q_A(A/Iⁿ, M)`, and `Ideal.depth I M` through the vanishing of the derived-category
`Ext (A ⧸ I) M`. This file relates the two for a finite module `M` over a Noetherian ring: local
cohomology vanishes below the depth (Stacks, Lemma 47.11.1 (0AVZ)) and does not vanish in degree
the depth (Stacks, Lemma 47.11.3 (0BUW)).

The two `Ext`s vanish together. Below the depth, every `Ext^q(A/Iⁿ, M)` vanishes. If `I M = M`,
this is because `Iⁿ` and the annihilator of `M` are comaximal; otherwise it is Rees' theorem, as
`A/Iⁿ` is supported in `V(I)`. In degree `d = depth_I M` the same vanishing in degree `d - 1`,
applied to the kernel of `A/Iᵐ → A/I`, makes the transition maps `Ext^d(A/I, M) → Ext^d(A/Iᵐ, M)`
injective. So the nonzero group `Ext^d(A/I, M)` injects into the colimit.

## Main results

* `TauCeti.Supports.isZero_Ext_iff_subsingleton`: the derived-functor `Ext` of modules vanishes
  exactly when the derived-category `Ext` does.
* `TauCeti.Supports.isZero_localCohomology_of_subsingleton_ext`: `H^q_I(M) = 0` once every
  `Ext^q(A/Iⁿ, M)` vanishes.
* `TauCeti.Supports.depth_localCohomology_vanishing`: `H^q_I(M) = 0` for `q < depth_I M`.
* `TauCeti.Supports.depth_localCohomology_nonvanishing`: `H^d_I(M) ≠ 0` for `depth_I M = d`.
* `TauCeti.Supports.depth_localCohomology_zero_guard`: the zero module has depth `⊤` and all of
  its local cohomology vanishes.
-/

public section

universe u

open CategoryTheory CategoryTheory.Abelian Limits Opposite

namespace TauCeti.Supports

variable {A : Type u} [CommRing A]

/-- The derived-functor `Ext` of modules vanishes exactly when the derived-category `Ext` does. In
degree zero both are `Hom`. -/
theorem isZero_Ext_iff_subsingleton (N M : ModuleCat.{u} A) :
    ∀ q : ℕ, IsZero (((_root_.Ext A (ModuleCat.{u} A) q).obj (op N)).obj M) ↔
      Subsingleton (Ext N M q)
  | 0 => by
    change IsZero (((_root_.Ext A (ModuleCat.{u} A) 0).flip.obj M).obj (op N)) ↔ _
    rw [((extZeroIso M).app (op N)).isZero_iff, ModuleCat.isZero_iff_subsingleton,
      Ext.homEquiv₀.subsingleton_congr]
    rfl
  | p + 1 => isZero_Ext_succ_iff_subsingleton N M p

/-- `H^q_I(M)` vanishes once `Ext^q(A/Iⁿ, M)` vanishes for every `n`. -/
theorem isZero_localCohomology_of_subsingleton_ext (I : Ideal A) (M : ModuleCat.{u} A) (q : ℕ)
    (h : ∀ n : ℕ, Subsingleton (Ext (ModuleCat.of A (A ⧸ I ^ n)) M q)) :
    IsZero ((localCohomology I q).obj M) := by
  refine IsZero.of_iso ?_ (colimitObjIsoColimitCompEvaluation _ M)
  refine (IsZero.iff_id_eq_zero _).2 (colimit.hom_ext fun n => ?_)
  exact ((isZero_Ext_iff_subsingleton _ M q).2 (h n.unop.unop)).eq_of_src _ _

/-- Below the `I`-depth of a finite module `M` with `I M ≠ M` over a Noetherian ring, `Ext^q(N, M)`
vanishes for every finite module `N` supported in `V(I)`: this is Rees' theorem
`ModuleCat.exists_isRegular_tfae` when `N ≠ 0`. -/
theorem subsingleton_ext_of_support_subset [IsNoetherianRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M] (hI : I • (⊤ : Submodule A M) ≠ ⊤) {q : ℕ}
    (hq : (q : ℕ∞) < I.depth M) (N : ModuleCat.{u} A) [Module.Finite A N]
    (hN : Module.support A N ⊆ PrimeSpectrum.zeroLocus I) : Subsingleton (Ext N M q) := by
  by_cases hn : Nontrivial N
  · have hext : ∀ i < q + 1, Subsingleton (Ext (ModuleCat.of A (Shrink.{u} (A ⧸ I))) M i) :=
      fun i hi => ModuleCat.subsingleton_ext_of_lt_depth
        (lt_of_le_of_lt (Nat.cast_le.2 (Nat.lt_succ_iff.1 hi)) hq)
    have rees := (ModuleCat.exists_isRegular_tfae I (q + 1) M (lt_top_iff_ne_top.2 hI)).out 2 1
    exact rees.1 hext N hn inferInstance hN q q.lt_succ_self
  · refine Ext.subsingleton_of_annihilator_sup_eq_top ?_ q
    rw [Module.annihilator_eq_top_iff.2 (not_nontrivial_iff_subsingleton.1 hn), top_sup_eq]

/-- `Ext^q(A/Iⁿ, M)` vanishes below the `I`-depth of a finite module `M` over a Noetherian ring.
If `I M = M`, then `Iⁿ` and the annihilator of `M` are comaximal; otherwise
`subsingleton_ext_of_support_subset` applies, as `A/Iⁿ` is supported in `V(I)`. -/
theorem subsingleton_ext_quotient_pow_of_lt_depth [IsNoetherianRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M] {q : ℕ} (hq : (q : ℕ∞) < I.depth M) (n : ℕ) :
    Subsingleton (Ext (ModuleCat.of A (A ⧸ I ^ n)) M q) := by
  by_cases hI : I • (⊤ : Submodule A M) = ⊤
  · refine Ext.subsingleton_of_annihilator_sup_eq_top ?_ q
    rw [Ideal.smul_top_eq_top_iff_sup_annihilator_eq_top, sup_comm] at hI
    change Module.annihilator A (A ⧸ I ^ n) ⊔ _ = ⊤
    rw [Ideal.annihilator_quotient, sup_comm]
    exact Ideal.sup_pow_eq_top hI
  refine subsingleton_ext_of_support_subset I M hI hq _ ?_
  change Module.support A (A ⧸ I ^ n) ⊆ _
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  exact fun P hP => P.isPrime.le_of_pow_le hP

/-- Local cohomology vanishes below the depth: for a finite module `M` over a Noetherian ring and
`q < depth_I M`, `H^q_I(M) = 0`. Stacks, Lemma 47.11.1 (0AVZ). -/
@[stacks 0AVZ]
theorem depth_localCohomology_vanishing [IsNoetherianRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M] {q : ℕ} (hq : (q : ℕ∞) < I.depth M) :
    IsZero ((localCohomology I q).obj M) :=
  isZero_localCohomology_of_subsingleton_ext I M q
    (subsingleton_ext_quotient_pow_of_lt_depth I M hq)

/-- In degrees up to the `I`-depth of a finite module `M` with `I M ≠ M` over a Noetherian ring,
precomposition with the quotient map `A ⧸ Iᵐ → A ⧸ I¹` is injective on `Ext^{p+1}(−, M)`: its
kernel is supported in `V(I)`, so `Ext^p` of the kernel vanishes, and the long exact sequence
applies. -/
theorem injective_ext_precomp_quotient [IsNoetherianRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M] (hI : I • (⊤ : Submodule A M) ≠ ⊤) {p : ℕ}
    (hp : ((p + 1 : ℕ) : ℕ∞) ≤ I.depth M) {m : ℕ} (hm : I ^ m ≤ I ^ 1) :
    Function.Injective fun α : Ext (ModuleCat.of A (A ⧸ I ^ 1)) M (p + 1) =>
      (Ext.mk₀ (ModuleCat.ofHom (Submodule.mapQ (I ^ m) (I ^ 1) LinearMap.id (by exact hm)))).comp α
        (zero_add _) := by
  let g := Submodule.mapQ (I ^ m) (I ^ 1) LinearMap.id (by exact hm)
  have hg : Function.Surjective g := fun y => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hS := LinearMap.shortExact_shortComplexKer hg
  refine (injective_iff_map_eq_zero ((Ext.mk₀ (ModuleCat.ofHom g)).precomp M
    (zero_add (p + 1)))).2 fun x hx => ?_
  obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₃ hS M x hx (add_comm 1 p)
  have hsupp : Module.support A (LinearMap.ker g) ⊆ PrimeSpectrum.zeroLocus I := by
    refine (Module.support_subset_of_injective _ (LinearMap.ker g).injective_subtype).trans ?_
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    exact fun P hP => P.isPrime.le_of_pow_le hP
  have := subsingleton_ext_of_support_subset I M hI
    (lt_of_lt_of_le (Nat.cast_lt.2 p.lt_succ_self) hp) (ModuleCat.of A (LinearMap.ker g)) hsupp
  rw [Subsingleton.elim y 0, Ext.comp_zero]

/-- The transition maps `Ext^d(A ⧸ I¹, M) → Ext^d(A ⧸ Iᵐ, M)` of the system defining `H^d_I(M)`
are injective for `d` at most the `I`-depth of a finite module `M` with `I M ≠ M` over a Noetherian
ring. In degree zero this is precomposition with a surjection on `Hom`. -/
theorem injective_Ext_map_quotient [IsNoetherianRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M] (hI : I • (⊤ : Submodule A M) ≠ ⊤) {m : ℕ}
    (hm : I ^ m ≤ I ^ 1) :
    ∀ {d : ℕ}, (d : ℕ∞) ≤ I.depth M → Function.Injective (((_root_.Ext A (ModuleCat.{u} A) d).map
      (ModuleCat.ofHom (Submodule.mapQ (I ^ m) (I ^ 1) LinearMap.id (by exact hm))).op).app M).hom
  | 0, _ => by
    let g := ModuleCat.ofHom (Submodule.mapQ (I ^ m) (I ^ 1) LinearMap.id (by exact hm))
    have : Epi g := (ModuleCat.epi_iff_surjective g).2 fun y => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk x, rfl⟩
    have hy : Mono (((linearYoneda A (ModuleCat.{u} A)).obj M).map g.op) :=
      (ModuleCat.mono_iff_injective _).2 fun φ₁ φ₂ h => (cancel_epi g).1 h
    have : Mono ((((_root_.Ext A (ModuleCat.{u} A) 0).flip.obj M).map g.op) ≫
        (extZeroIso M).hom.app _) := by
      rw [(extZeroIso M).hom.naturality]
      exact @mono_comp _ _ _ _ _ _ inferInstance _ hy
    exact (ModuleCat.mono_iff_injective _).1
      (@mono_of_mono _ _ _ _ _ _ ((extZeroIso M).hom.app _) this)
  | p + 1, hp => injective_Ext_map_succ _ M p (injective_ext_precomp_quotient I M hI hp hm)

/-- Local cohomology does not vanish in degree the depth: for a finite module `M` over a
Noetherian ring with `depth_I M = d`, `H^d_I(M) ≠ 0`. The first term `Ext^d(A ⧸ I¹, M)` of the
defining system is nonzero, and it injects into the colimit because the transition maps are
injective. Stacks, Lemma 47.11.3
(0BUW). -/
@[stacks 0BUW]
theorem depth_localCohomology_nonvanishing [IsNoetherianRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M] {d : ℕ} (hd : I.depth M = d) :
    Nontrivial ((localCohomology I d).obj M) := by
  have hI : I • (⊤ : Submodule A M) ≠ ⊤ := fun h =>
    ENat.natCast_ne_top d (hd ▸ Ideal.depth_eq_top_of_smul_top_eq_top I M h)
  have hne : Nontrivial (Ext (ModuleCat.of A (A ⧸ I ^ 1)) M d) := by
    have := ((ModuleCat.depth_eq_iff _ M d).1 hd).1
    let e := ((Shrink.linearEquiv A (A ⧸ I)).trans
      (Submodule.quotEquivOfEq _ _ (pow_one I).symm)).toModuleIso
    exact @Equiv.nontrivial _ _
      (((extFunctor d).mapIso e.symm.op).app M).addCommGroupIsoToAddEquiv.toEquiv.symm this
  let D := localCohomology.diagram (localCohomology.idealPowersDiagram I) d
  let F := D ⋙ (evaluation _ _).obj M
  have : PreservesColimit F (forget (ModuleCat.{u} A)) :=
    have := preservesFilteredColimitsOfSize_shrink.{0, u, 0, u} (forget (ModuleCat.{u} A))
    inferInstance
  have hF : Nontrivial (F.obj (op (op 1))) := not_subsingleton_iff_nontrivial.1 fun h =>
    @not_subsingleton _ hne ((isZero_Ext_iff_subsingleton _ M d).1
      (@ModuleCat.isZero_of_subsingleton _ _ _ h))
  obtain ⟨x, hx⟩ := exists_ne (0 : F.obj (op (op 1)))
  have hι : colimit.ι F (op (op 1)) x ≠ 0 := fun h => by
    obtain ⟨j, i, hi⟩ := Concrete.colimit_rep_eq_zero A F _ x h
    have hinj : Function.Injective (F.map i).hom := injective_Ext_map_quotient I M hI
      (m := j.unop.unop) (leOfHom ((localCohomology.idealPowersDiagram I).map i.unop)) hd.ge
    exact hx (hinj (hi.trans (map_zero _).symm))
  have : Nontrivial ↑(colimit F) := ⟨⟨colimit.ι F _ x, 0, hι⟩⟩
  exact @Equiv.nontrivial _ _ (colimitObjIsoColimitCompEvaluation D M).toLinearEquiv.toEquiv this

/-- The zero module has depth `⊤` and every degree of its local cohomology vanishes, so it has no
finite degree of nonvanishing. No hypothesis on `A` is needed. -/
theorem depth_localCohomology_zero_guard (I : Ideal A) (M : ModuleCat.{u} A) [Subsingleton M] :
    I.depth M = ⊤ ∧ ∀ q : ℕ, IsZero ((localCohomology I q).obj M) := by
  refine ⟨Ideal.depth_eq_top_of_subsingleton I M, fun q =>
    isZero_localCohomology_of_subsingleton_ext I M q fun n =>
      Ext.subsingleton_of_annihilator_sup_eq_top ?_ q⟩
  rw [(Module.annihilator_eq_top_iff (R := A) (M := M)).2 ‹_›, sup_top_eq]

end TauCeti.Supports
