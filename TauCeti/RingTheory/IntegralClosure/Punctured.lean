/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import TauCeti.RingTheory.Conductor

/-!
# Integral closure over a punctured spectrum

Let `A` be a commutative ring, `q` a maximal ideal of `A` and `u : A` with `√(u) = q`, so that
`Spec A_u` is `Spec A` with the closed point `q` removed. Let `C` be the integral closure of `A` in
`A_u`. Every element of `C ⊆ A_u` is carried into `A` by a power of `u`, so the cokernel `C / A` is
`u`-power torsion, and an element of `A` outside `q` is coprime to every power of `u`. Hence
`C / A` is already a module over the localization `A_q`: the cokernel of `A → C` is that of
`A_q → C_q`, and `C_q` is the integral closure of `A_q` in `(A_u)_q`, because integral closure
commutes with localization (`IsLocalization.integralClosure`).

This globalizes a computation at the local ring `A_q` to an affine neighbourhood of `q`: for the
local ring at a node of a curve, `C_q` is the blowup of the closed point and its cokernel is the
residue field (`AlgebraicGeometry.Scheme.exists_conductor_stalk_eq_maximalIdeal`), so the
normalization of a neighbourhood of the node in its complement has cokernel `A / q` and conductor
`q`.

## Main results

* `TauCeti.exists_notMem_forall_eq_of_isMaximal`: in a Noetherian ring, if `q` is the only prime
  below `q` containing `u`, then some basic open `D(g) ∋ q` meets `V(u)` only in `q`.
* `TauCeti.exists_notMem_radical_span_singleton_eq`: if `u` generates an ideal of radical `𝔪` in
  `A_q`, then on some basic open `D(g) ∋ q` the closed point `q` is the radical of `(u)`.
* `TauCeti.isLocalizedModule_id_of_pow_smul_eq_zero`: a `u`-power torsion module is its own
  localization at `q`.
* `TauCeti.integralClosureQuotientEquiv`: the cokernel of `A → C` is the cokernel of the integral
  closure of `A_q` in a localization of `A_u` at `q`.
* `TauCeti.conductor_integralClosure_eq_of_conductor_eq_maximalIdeal`: if the local conductor is
  the maximal ideal, the conductor of `C` over `A` is `q`.
* `TauCeti.integralClosureQuotientEquivOfQuotientEquiv` and
  `TauCeti.finite_integralClosure_of_quotientEquiv`: if the local cokernel is the residue field,
  the cokernel of `A → C` is `A / q`, and `C` is finite over `A`.
-/

@[expose] public section

noncomputable section

open Submodule IsLocalRing

namespace TauCeti

variable {A : Type*} [CommRing A] {q : Ideal A} [q.IsMaximal] {u : A}

/-- If `√(u)` is a maximal ideal `q`, every element outside `q` is coprime to every power
of `u`. -/
theorem isCoprime_pow_of_radical_span_singleton_eq (hu : (Ideal.span {u}).radical = q)
    {s : A} (hs : s ∉ q) (n : ℕ) : IsCoprime s (u ^ n) := by
  have htop : Ideal.span {s, u} = ⊤ := by
    by_contra h
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h
    have hqP : q ≤ P := hu ▸ (Ideal.IsPrime.radical_le_iff hP.isPrime).mpr
      ((Ideal.span_singleton_le_iff_mem _).mpr (hle (Ideal.subset_span (by simp))))
    exact hs ((Ideal.IsMaximal.eq_of_le inferInstance hP.ne_top hqP) ▸
      hle (Ideal.subset_span (by simp)))
  exact IsCoprime.pow_right (Ideal.mem_span_pair.mp (htop ▸ Submodule.mem_top))

/-- **Punctured neighbourhoods.** Let `A` be Noetherian, `q` a maximal ideal and `u : A` such that
`q` is the only prime below `q` containing `u`, so that `V(u)` is the closed point near `q`. Then
there is `g ∉ q` such that `q` is the only prime of `A` containing `u` but not `g`: on the basic
open `D(g)`, the vanishing locus of `u` is the closed point `q`. -/
theorem exists_notMem_forall_eq_of_isMaximal [IsNoetherianRing A]
    (h : ∀ P : Ideal A, P.IsPrime → u ∈ P → P ≤ q → P = q) :
    ∃ g ∉ q, ∀ P : Ideal A, P.IsPrime → u ∈ P → g ∉ P → P = q := by
  classical
  have hfin := (Ideal.span {u}).finite_minimalPrimes_of_isNoetherianRing
  have hout : ∀ P ∈ (Ideal.span {u}).minimalPrimes, P ≠ q → ∃ g ∈ P, g ∉ q := by
    intro P hP hPq
    by_contra! hle
    exact hPq (h P hP.1.1 ((Ideal.span_singleton_le_iff_mem _).mp hP.1.2) hle)
  choose! gP hgP hgPq using hout
  let S := hfin.toFinset.filter (· ≠ q)
  refine ⟨∏ P ∈ S, gP P, fun hmem ↦ ?_, fun P' hP' hu hg ↦ ?_⟩
  · obtain ⟨P, hP, hPq⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset] at hP
    exact hgPq P hP.1 hP.2 hPq
  · obtain ⟨P, hP, hPP'⟩ := Ideal.exists_minimalPrimes_le
      ((Ideal.span_singleton_le_iff_mem _).mpr hu)
    by_cases hPq : P = q
    · exact ((inferInstance : q.IsMaximal).eq_of_le hP'.ne_top (hPq ▸ hPP')).symm
    · exact (hg (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem gP (by simp [S, hP, hPq]))
        (hPP' (hgP P hP hPq)))).elim

/-- **Isolating a closed point in `V(u)`.** Let `A` be Noetherian, `q` a maximal ideal and `u : A`
generating an ideal of radical `𝔪` in the localization `A_q`. Then some `g ∉ q` cuts out a basic
open `D(g) ∋ q` meeting `V(u)` only in `q`: in every localization `B` of `A` away from `g`, the
extension of `q` is a maximal ideal, and it is the radical of `(u)`. -/
theorem exists_notMem_radical_span_singleton_eq [IsNoetherianRing A] (Aq : Type*) [CommRing Aq]
    [Algebra A Aq] [IsLocalization.AtPrime Aq q] [IsLocalRing Aq]
    (hu : (Ideal.span {algebraMap A Aq u}).radical = maximalIdeal Aq) :
    ∃ g ∉ q, ∀ (B : Type*) [CommRing B] [Algebra A B] [IsLocalization.Away g B],
      (q.map (algebraMap A B)).IsMaximal ∧
        (Ideal.span {algebraMap A B u}).radical = q.map (algebraMap A B) := by
  have huq : u ∈ q := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal Aq q, Ideal.mem_comap, ← hu]
    exact Ideal.le_radical (Ideal.mem_span_singleton_self _)
  -- In `A_q`, a prime containing `u` contains `√(u) = 𝔪`, so `q` is the only prime below `q`
  -- containing `u`.
  obtain ⟨g, hgq, hg⟩ := exists_notMem_forall_eq_of_isMaximal (u := u) fun P hP huP hPq ↦ by
    have hdisj : Disjoint (q.primeCompl : Set A) P :=
      Set.disjoint_left.mpr fun _ hs hsP ↦ hs (hPq hsP)
    have := IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl Aq P hP hdisj
    refine hPq.antisymm ?_
    rw [← IsLocalization.under_map_of_isPrime_disjoint q.primeCompl Aq hP hdisj,
      ← IsLocalization.AtPrime.under_maximalIdeal Aq q]
    refine Ideal.comap_mono ?_
    rw [← hu, Ideal.IsPrime.radical_le_iff this, Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ huP
  refine ⟨g, hgq, fun B _ _ _ ↦ ?_⟩
  have hdisj : Disjoint (Submonoid.powers g : Set A) q :=
    (Ideal.disjoint_powers_iff_notMem g (inferInstance : q.IsMaximal).isPrime.isRadical).mpr hgq
  have hQ := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) B q inferInstance
    hdisj
  -- A prime of `B` containing `u` lies over a prime of `A` containing `u` but not `g`.
  have key (P : Ideal B) (hP : P.IsPrime) (huP : algebraMap A B u ∈ P) :
      P = q.map (algebraMap A B) := by
    have hgP : g ∉ P.comap (algebraMap A B) := fun h ↦
      hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit g))
    rw [← IsLocalization.map_under (Submonoid.powers g) B P]
    exact congr_arg _ (hg _ (hP.comap (algebraMap A B)) huP hgP)
  have hmax : (q.map (algebraMap A B)).IsMaximal := by
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hQ.ne_top
    exact key M hM.isPrime (hle (Ideal.mem_map_of_mem _ huq)) ▸ hM
  refine ⟨hmax, le_antisymm ?_ ?_⟩
  · rw [Ideal.IsPrime.radical_le_iff hQ, Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ huq
  · rw [Ideal.radical_eq_sInf]
    exact le_sInf fun P ⟨hP, hPp⟩ ↦
      (key P hPp ((Ideal.span_singleton_le_iff_mem _).mp hP)).ge

/-- **Torsion modules over a punctured spectrum.** If `√(u)` is a maximal ideal `q` and every
element of `M` is killed by a power of `u`, then the elements outside `q` act bijectively on `M`,
so `M` is its own localization at `q`. -/
theorem isLocalizedModule_id_of_pow_smul_eq_zero (hu : (Ideal.span {u}).radical = q)
    {M : Type*} [AddCommGroup M] [Module A M] (hM : ∀ m : M, ∃ n : ℕ, u ^ n • m = 0) :
    IsLocalizedModule q.primeCompl (LinearMap.id : M →ₗ[A] M) where
  map_units s := by
    refine (Module.End.isUnit_iff _).mpr ⟨fun m m' h ↦ ?_, fun m ↦ ?_⟩
    · obtain ⟨n, hn⟩ := hM (m - m')
      obtain ⟨a, b, hab⟩ := isCoprime_pow_of_radical_span_singleton_eq hu s.2 n
      have h' : (s : A) • (m - m') = 0 := by
        simpa [Module.algebraMap_end_apply, smul_sub, sub_eq_zero] using h
      rw [← sub_eq_zero, ← one_smul A (m - m'), ← hab, add_smul, mul_smul, h', mul_smul, hn,
        smul_zero, smul_zero, add_zero]
    · obtain ⟨n, hn⟩ := hM m
      obtain ⟨a, b, hab⟩ := isCoprime_pow_of_radical_span_singleton_eq hu s.2 n
      refine ⟨a • m, ?_⟩
      rw [Module.algebraMap_end_apply, ← mul_smul, mul_comm, ← add_zero ((a * s) • m),
        ← smul_zero b, ← hn, ← mul_smul, ← add_smul, hab, one_smul]
  surj m := ⟨(m, 1), by simp⟩
  exists_of_eq {m m'} h := ⟨1, by simpa using h⟩

variable (A q) (L Aq L' : Type*) [CommRing L] [Algebra A L] [CommRing Aq] [Algebra A Aq]
  [IsLocalization.AtPrime Aq q] [CommRing L'] [Algebra Aq L'] [Algebra A L'] [Algebra L L']
  [IsScalarTower A Aq L'] [IsScalarTower A L L']
  [IsLocalization (Algebra.algebraMapSubmonoid L q.primeCompl) L']

/-- The localization map from the integral closure of `A` in `L` to that of `A_q` in a
localization `L'` of `L` at `q`: the structure map of `TauCeti.integralClosureMapAlgebra`, bundled
as an `A`-algebra map so that the cokernels below carry a single `A`-module structure. -/
def integralClosureMap : integralClosure A L →ₐ[A] integralClosure Aq L' where
  toFun x := ⟨algebraMap L L' x, (x.2.map (IsScalarTower.toAlgHom A L L')).tower_top⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  commutes' a := by ext; simp [← IsScalarTower.algebraMap_apply]

@[simp]
theorem coe_integralClosureMap (x : integralClosure A L) :
    (integralClosureMap A L Aq L' x : L') = algebraMap L L' x :=
  rfl

/-- The integral closure of `A_q` in `L'` is the localization of the integral closure of `A`
in `L` at `q`. -/
instance isLocalizedModule_integralClosureMap :
    IsLocalizedModule q.primeCompl (integralClosureMap A L Aq L').toLinearMap := by
  let := (integralClosureMap A L Aq L').toRingHom.toAlgebra
  have : IsScalarTower (integralClosure A L) (integralClosure Aq L') L' :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A (integralClosure A L) (integralClosure Aq L') :=
    .of_algebraMap_eq fun a ↦ ((integralClosureMap A L Aq L').commutes a).symm
  have := IsLocalization.integralClosure (R := A) (S := L) (Rf := Aq) (Sf := L') q.primeCompl
  exact isLocalizedModule_iff_isLocalization.mpr this

/-- The extension of the image of `A` in its integral closure is the image of `A_q`. -/
theorem localized'_one_integralClosureMap :
    (1 : Submodule A (integralClosure A L)).localized' Aq q.primeCompl
      (integralClosureMap A L Aq L').toLinearMap = 1 := by
  rw [Submodule.one_eq_span, Submodule.one_eq_span, localized'_span]
  simp

variable {A}

/-- **The cokernel over a punctured spectrum is local.** If `√(u)` is a maximal ideal `q` and `L`
is the localization `A_u`, the cokernel of `A` in its integral closure in `L` is the cokernel of
`A_q` in its integral closure in a localization `L'` of `L` at `q`. -/
def integralClosureQuotientEquiv (hu : (Ideal.span {u}).radical = q) [IsLocalization.Away u L] :
    (integralClosure A L ⧸ (1 : Submodule A (integralClosure A L))) ≃ₗ[A]
      (integralClosure Aq L' ⧸ (1 : Submodule Aq (integralClosure Aq L'))) := by
  have := isLocalizedModule_id_of_pow_smul_eq_zero hu
    (M := integralClosure A L ⧸ (1 : Submodule A (integralClosure A L))) fun m ↦ by
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers u) (c : L)
      simp only [map_pow] at h
      refine ⟨n, (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, Subtype.ext ?_⟩⟩
      simp [Algebra.smul_def, mul_comm, ← h]
  exact IsLocalizedModule.linearEquiv q.primeCompl LinearMap.id
    ((1 : Submodule A (integralClosure A L)).toLocalizedQuotient' Aq q.primeCompl
      (integralClosureMap A L Aq L').toLinearMap) ≪≫ₗ
    (Submodule.quotEquivOfEq _ _ (localized'_one_integralClosureMap A q L Aq L')).restrictScalars A

/-- `TauCeti.integralClosureQuotientEquiv` sends the class of `c` to the class of its image in the
localized integral closure. -/
@[simp]
theorem integralClosureQuotientEquiv_mk (hu : (Ideal.span {u}).radical = q)
    [IsLocalization.Away u L] (c : integralClosure A L) :
    integralClosureQuotientEquiv q L Aq L' hu (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (integralClosureMap A L Aq L' c) := by
  simp only [integralClosureQuotientEquiv, LinearEquiv.trans_apply]
  rw [show Submodule.Quotient.mk c = LinearMap.id (R := A) (Submodule.Quotient.mk c) from rfl,
    IsLocalizedModule.linearEquiv_apply]
  rfl

/-- If the conductor of the integral closure of `A_q` in `L'` is the maximal ideal, the conductor
of the integral closure of `A` in `A_u` is `q`. -/
theorem conductor_integralClosure_eq_of_conductor_eq_maximalIdeal
    (hu : (Ideal.span {u}).radical = q) [IsLocalization.Away u L] [IsLocalRing Aq]
    (h : Algebra.conductor Aq (integralClosure Aq L') = maximalIdeal Aq) :
    Algebra.conductor A (integralClosure A L) = q := by
  ext a
  rw [Algebra.conductor_eq_annihilator, Module.mem_annihilator,
    ← IsLocalization.AtPrime.under_maximalIdeal Aq q, Ideal.mem_comap, ← h,
    Algebra.conductor_eq_annihilator, Module.mem_annihilator,
    ← (integralClosureQuotientEquiv q L Aq L' hu).forall_congr_right]
  refine forall_congr' fun m ↦ ?_
  rw [← (integralClosureQuotientEquiv q L Aq L' hu).map_eq_zero_iff, map_smul, algebraMap_smul]
  exact Iff.rfl

/-- The residue field of `A_q` is `A / q`, as an `A`-module. -/
def quotientEquivQuotientMaximalIdeal [IsLocalRing Aq] : (A ⧸ q) ≃ₗ[A] Aq ⧸ maximalIdeal Aq :=
  let f : A →ₗ[A] Aq ⧸ maximalIdeal Aq :=
    (Submodule.mkQ (maximalIdeal Aq)).restrictScalars A ∘ₗ Algebra.linearMap A Aq
  have hsurj : Function.Surjective f := fun y ↦ by
    have hmax : ((maximalIdeal Aq).under A).IsMaximal := by
      rw [IsLocalization.AtPrime.under_maximalIdeal Aq q]
      infer_instance
    obtain ⟨x, hx⟩ := IsLocalization.surjective_quotientMap_of_maximal_of_localization
      q.primeCompl (S := Aq) (I := maximalIdeal Aq) (J := q)
      (H := (IsLocalization.AtPrime.under_maximalIdeal Aq q).ge) hmax y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, hx⟩
  have hker : LinearMap.ker f = q := by
    ext a
    simp only [f, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      Algebra.linearMap_apply, LinearMap.coe_restrictScalars, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff Aq q a
  (Submodule.quotEquivOfEq _ _ hker).symm ≪≫ₗ f.quotKerEquivOfSurjective hsurj

/-- If the cokernel of the integral closure of `A_q` in `L'` is the residue field, the cokernel
of the integral closure of `A` in `A_u` is `A / q`. -/
def integralClosureQuotientEquivOfQuotientEquiv (hu : (Ideal.span {u}).radical = q)
    [IsLocalization.Away u L] [IsLocalRing Aq]
    (e : (integralClosure Aq L' ⧸ (1 : Submodule Aq (integralClosure Aq L'))) ≃ₗ[Aq]
      Aq ⧸ maximalIdeal Aq) :
    (integralClosure A L ⧸ (1 : Submodule A (integralClosure A L))) ≃ₗ[A] A ⧸ q :=
  integralClosureQuotientEquiv q L Aq L' hu ≪≫ₗ e.restrictScalars A ≪≫ₗ
    (quotientEquivQuotientMaximalIdeal q Aq).symm

/-- If the cokernel of the integral closure of `A_q` in `L'` is the residue field, the integral
closure of `A` in `A_u` is a finite `A`-module. -/
theorem finite_integralClosure_of_quotientEquiv (hu : (Ideal.span {u}).radical = q)
    [IsLocalization.Away u L] [IsLocalRing Aq]
    (e : (integralClosure Aq L' ⧸ (1 : Submodule Aq (integralClosure Aq L'))) ≃ₗ[Aq]
      Aq ⧸ maximalIdeal Aq) :
    Module.Finite A (integralClosure A L) := by
  have : Module.Finite A (integralClosure A L ⧸ (1 : Submodule A (integralClosure A L))) :=
    .equiv (integralClosureQuotientEquivOfQuotientEquiv q L Aq L' hu e).symm
  have : Module.Finite A (1 : Submodule A (integralClosure A L)) := by
    rw [Submodule.one_eq_span]
    infer_instance
  exact .of_submodule_quotient 1

end TauCeti
