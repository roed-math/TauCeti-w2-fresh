/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import TauCeti.RingTheory.Length.Determinant
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.LocalRing.Length

/-!
# The order of a norm

Let `A` be a Noetherian domain of Krull dimension at most one with fraction field `K`, and let `B`
be a domain that is a finite `A`-algebra, with fraction field `L`. For a nonzero `b : B`, this
file computes the order of the norm `N_{L/K}(b)` in two steps (Fulton, *Intersection Theory*,
Appendix A.3):

* `TauCeti.ordFrac_norm_eq_coe_of_length_eq`: the order of `N_{L/K}(b)` is the `A`-length of
  `B ⧸ bB`. The norm need not lie in `A`, since `A` need not be integrally closed, so its order is
  Mathlib's `Ring.ordFrac A` on `K`. This is Fulton's determinant lemma (Appendix A.2)
  (`LinearMap.ordFrac_det_eq_coe_of_length_eq`) for multiplication by `b` on the lattice `B ⊆ L`,
  which spans `L` over `K` because `B` is integral over `A`
  (`TauCeti.span_range_algebraMap_eq_top`).
* `TauCeti.length_quotient_span_singleton_eq_finsum_ord`: for `A` local, that length is
  `Σ_m ord_{B_m}(b) [κ(B_m) : κ(A)]` over the maximal ideals `m` of `B`. The Artinian ring
  `B ⧸ bB` is the product of its localizations
  (`TauCeti.length_quotient_span_singleton_eq_finsum`),
  the localization of `B ⧸ bB` at `m` is `B_m ⧸ b B_m`
  (`TauCeti.length_localization_quotient_span_singleton`), and Mathlib's
  `IsLocalRing.length_restrictScalars` converts lengths over `B_m` into lengths over `A`.

Together they give `ord_A N_{L/K}(b) = Σ_m [κ(B_m) : κ(A)] ord_{B_m}(b)`, the coefficient identity
behind the pushforward of principal divisors along finite maps (Fulton, Proposition 1.4(b)).
-/

public section

namespace TauCeti

variable {A K B L : Type*} [CommRing A] [Field K] [Algebra A K] [CommRing B] [Algebra A B]
  [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [IsScalarTower A B L]

variable (K) in
/-- For `B` integral over `A`, the fraction field `L` of `B` is spanned by `B` over any field `K`
between `A` and `L`: the `K`-span of `B` is a `K`-subalgebra, and contains the inverse of each
nonzero element of `B`, which is algebraic over `K`. -/
theorem span_range_algebraMap_eq_top [Algebra.IsIntegral A B] :
    Submodule.span K (Set.range (algebraMap B L)) = ⊤ := by
  let S : Subalgebra K L := Algebra.adjoin K (Set.range (algebraMap B L))
  have hS : Subalgebra.toSubmodule S = Submodule.span K (Set.range (algebraMap B L)) := by
    rw [Algebra.adjoin_eq_span]
    congr 1
    change (Submonoid.closure (Set.range ((algebraMap B L : B →* L) : B → L)) : Set L) =
      Set.range ((algebraMap B L : B →* L) : B → L)
    rw [MonoidHom.mclosure_range, MonoidHom.coe_mrange]
  rw [← hS, eq_top_iff]
  intro x _
  obtain ⟨β, γ, hγ, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  have hγS : algebraMap B L γ ∈ S := Algebra.subset_adjoin ⟨γ, rfl⟩
  have hγK : IsAlgebraic K (algebraMap B L γ) :=
    (((Algebra.IsIntegral.isIntegral (R := A) γ).map (IsScalarTower.toAlgHom A B L)).tower_top
      (A := K)).isAlgebraic
  rw [div_eq_mul_inv]
  exact S.mul_mem (Algebra.subset_adjoin ⟨β, rfl⟩)
    (Subalgebra.inv_mem_of_algebraic S (x := ⟨_, hγS⟩) hγK)

variable [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsFractionRing A K]
  [Module.Finite A B]

/-- **The order of a norm is a length** (Fulton, *Intersection Theory*, Appendix A.3, first step).
Let `A` be a Noetherian domain of dimension at most one with fraction field `K`, and let `B` be a
domain finite over `A`, with fraction field `L`. For nonzero `b : B` with `B ⧸ bB` of `A`-length
`n`, the norm `N_{L/K}(b)` has order `n`. -/
theorem ordFrac_norm_eq_coe_of_length_eq {b : B} (hb : b ≠ 0) {n : ℕ}
    (hn : Module.length A (B ⧸ Ideal.span {b}) = n) :
    Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) = Multiplicative.ofAdd (n : ℤ) := by
  -- The lattice `B ⊆ L`, the image of the `A`-linear map `f`.
  let f : B →ₗ[A] L := (IsScalarTower.toAlgHom A B L).toLinearMap
  have hf : Function.Injective f := IsFractionRing.injective B L
  let M : Submodule A L := LinearMap.range f
  have hspan : Submodule.span K (M : Set L) = ⊤ := by
    rw [← span_range_algebraMap_eq_top K (A := A) (B := B)]
    rfl
  have : Module.Finite K L := by
    classical
    obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := A) (M := B))
    refine ⟨⟨s.image f, ?_⟩⟩
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    have hy : f y ∈ Submodule.span A (f '' (s : Set B)) := by
      rw [← Submodule.map_span, hs]
      exact Submodule.mem_map_of_mem Submodule.mem_top
    rw [Finset.coe_image]
    exact Submodule.span_le_restrictScalars A K _ hy
  -- Multiplication by `b` on `L` preserves the lattice.
  let φ : L →ₗ[K] L := Algebra.lmul K L (algebraMap B L b)
  have hφM : ∀ x ∈ M, φ x ∈ M := by
    rintro _ ⟨y, rfl⟩
    exact ⟨b * y, by simp [φ, f]⟩
  have hb' : algebraMap B L b ≠ 0 := (map_ne_zero_iff _ hf).2 hb
  have hdet : LinearMap.det φ ≠ 0 := by
    rw [← Algebra.norm_apply]
    exact (Algebra.norm_ne_zero_iff).2 hb'
  rw [Algebra.norm_apply]
  refine LinearMap.ordFrac_det_eq_coe_of_length_eq φ M ?_ hspan hφM hdet ?_
  · change (LinearMap.range f).FG
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map f
  -- Under `B ≃ M`, the ideal `bB` is the image of multiplication by `b`.
  let e : B ≃ₗ[A] M := LinearEquiv.ofInjective f hf
  have he : ((Ideal.span {b}).restrictScalars A).map (e : B →ₗ[A] M) =
      LinearMap.range ((φ.restrictScalars A).restrict hφM) := by
    ext ⟨x, hx⟩
    simp only [Submodule.mem_map, Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
      LinearMap.mem_range, Subtype.ext_iff, LinearEquiv.coe_coe, Subtype.exists]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨f a, ⟨a, rfl⟩, by rw [LinearEquiv.ofInjective_apply]; simp [φ, f, mul_comm]⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨b * a, ⟨a, mul_comm a b⟩, by rw [LinearEquiv.ofInjective_apply]; simp [φ, f]⟩
  rw [← (Submodule.Quotient.equiv _ _ e he).length_eq,
    (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {b})).length_eq, hn]

section Local

/-- The localization `R_{f⁻¹ J} → P_J` of a surjective ring map `f : R → P` is surjective. -/
theorem _root_.Localization.localRingHom_surjective_of_surjective {R P : Type*} [CommRing R]
    [CommRing P] (J : Ideal P) [J.IsPrime] {f : R →+* P} (hf : Function.Surjective f) :
    Function.Surjective (Localization.localRingHom (J.comap f) J f rfl) := by
  have hT : (J.comap f).primeCompl.map f = J.primeCompl := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hz
      obtain ⟨s, rfl⟩ := hf z
      exact ⟨s, hz, rfl⟩
  have : IsLocalization ((J.comap f).primeCompl.map f) (Localization.AtPrime J) := by
    rw [hT]; infer_instance
  exact IsLocalization.map_surjective_of_surjective _ _ _ hf

/-- Localizing `R ⧸ bR` at a prime `q` gives `R_m ⧸ b R_m`, for `m` the prime of `R` under `q`. In
particular the localization `(R ⧸ bR)_q` has length `ord_{R_m} b` over itself. -/
theorem length_localization_quotient_span_singleton {R : Type*} [CommRing R] (b : R)
    (q : Ideal (R ⧸ Ideal.span {b})) [q.IsPrime] :
    Module.length (Localization.AtPrime q) (Localization.AtPrime q) =
      Ring.ord (Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {b}))))
        (algebraMap R _ b) := by
  -- The localization `ψ : R_m → (R ⧸ bR)_q` of `R → R ⧸ bR` is surjective with kernel `b R_m`.
  let ψ := Localization.localRingHom _ q (Ideal.Quotient.mk (Ideal.span {b})) rfl
  have hψ : Function.Surjective ψ :=
    Localization.localRingHom_surjective_of_surjective q Ideal.Quotient.mk_surjective
  have hT : (q.comap (Ideal.Quotient.mk (Ideal.span {b}))).primeCompl.map
      (Ideal.Quotient.mk (Ideal.span {b})) = q.primeCompl := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hz
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨s, hz, rfl⟩
  have hker : RingHom.ker ψ = Ideal.span {algebraMap R _ b} := by
    refine (IsLocalization.ker_map (Localization.AtPrime q) (Ideal.Quotient.mk (Ideal.span {b}))
      hT).trans ?_
    rw [Ideal.mk_ker, Ideal.map_span, Set.image_singleton]
  let _ : Algebra (Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {b}))))
      (Localization.AtPrime q) := ψ.toAlgebra
  let e : (Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {b}))) ⧸ RingHom.ker ψ)
      ≃ₐ[Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {b})))]
      Localization.AtPrime q :=
    AlgEquiv.ofRingEquiv (f := RingHom.quotientKerEquivOfSurjective hψ) fun x ↦ rfl
  rw [← Module.length_eq_of_surjective
      (S := Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {b})))) hψ,
    ← e.toLinearEquiv.length_eq,
    (Ideal.quotientEquivAlgOfEq _ hker).toLinearEquiv.length_eq]
  rfl

/-- The residue field of `(R ⧸ bR)_q` is that of `R_m`, for `m` the prime of `R` under `q`; in
particular they have the same length over any ring `A` acting on `R`. -/
theorem _root_.Ideal.length_residueField_localization_quotient {A R : Type*} [CommRing A]
    [CommRing R] [Algebra A R] (I : Ideal R) (q : Ideal (R ⧸ I)) [q.IsPrime] :
    Module.length A (IsLocalRing.ResidueField (Localization.AtPrime q)) =
      Module.length A (IsLocalRing.ResidueField
        (Localization.AtPrime (q.comap (Ideal.Quotient.mk I)))) := by
  let ψ := Localization.localRingHom _ q (Ideal.Quotient.mk I) rfl
  have hψ : Function.Surjective ψ :=
    Localization.localRingHom_surjective_of_surjective q Ideal.Quotient.mk_surjective
  let φ := IsLocalRing.ResidueField.map ψ
  have hφ : Function.Bijective φ := by
    refine ⟨φ.injective, fun z ↦ ?_⟩
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨x, rfl⟩ := hψ y
    exact ⟨IsLocalRing.residue _ x, IsLocalRing.ResidueField.map_residue _ _⟩
  let e : IsLocalRing.ResidueField (Localization.AtPrime (q.comap (Ideal.Quotient.mk I))) ≃ₗ[A]
      IsLocalRing.ResidueField (Localization.AtPrime q) :=
    { RingEquiv.ofBijective φ hφ with
      map_smul' := fun a x ↦ by
        simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
          RingEquiv.ofBijective_apply, Algebra.smul_def, map_mul, RingHom.id_apply]
        congr 1
        rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime (q.comap
            (Ideal.Quotient.mk I))) (IsLocalRing.ResidueField _),
          IsScalarTower.algebraMap_apply A R (Localization.AtPrime _),
          IsScalarTower.algebraMap_apply A (Localization.AtPrime q) (IsLocalRing.ResidueField _),
          IsScalarTower.algebraMap_apply A (R ⧸ I) (Localization.AtPrime q)]
        simp [φ, ψ] }
  exact e.length_eq.symm

variable {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]

/-- For a domain `B` finite over a Noetherian domain `A` of dimension at most one, `B ⧸ bB` has
finite `A`-length for `b ≠ 0`: the ideal `bB` meets `A` in a nonzero element, which annihilates
`B ⧸ bB`. -/
theorem isFiniteLength_quotient_span_singleton {b : B} (hb : b ≠ 0) :
    IsFiniteLength A (B ⧸ Ideal.span {b}) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.under_ne_bot_of_integral_mem hb (Ideal.mem_span_singleton_self b)
      (Algebra.IsIntegral.isIntegral (R := A) b))
  refine isFiniteLength_of_nonZeroDivisor_mem_annihilator (x := a) ?_
    (mem_nonZeroDivisors_of_ne_zero ha0)
  rw [Module.mem_annihilator]
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ ha

/-- **The length of `B ⧸ bB` is a sum of local lengths** (Fulton, *Intersection Theory*,
Appendix A.3, second step). Let `A` be a local Noetherian domain of dimension at most one and `B`
a domain finite over `A`. For `b ≠ 0`, the Artinian ring `C = B ⧸ bB` is the product of its
localizations `C_q` at its finitely many maximal ideals, and each `C_q` has `A`-length
`length_{C_q} C_q * [κ(C_q) : κ(A)]` (Mathlib's `IsLocalRing.length_restrictScalars`); the residue
degree `[κ(C_q) : κ(A)]` is the `A`-length of `κ(C_q)`. -/
theorem length_quotient_span_singleton_eq_finsum [IsLocalRing A] {b : B} (hb : b ≠ 0) :
    Module.length A (B ⧸ Ideal.span {b}) =
      ∑ᶠ q : MaximalSpectrum (B ⧸ Ideal.span {b}),
        Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) *
          Module.length A (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) := by
  set C := B ⧸ Ideal.span {b}
  have : IsArtinian A C :=
    (isFiniteLength_iff_isNoetherian_isArtinian.1 (isFiniteLength_quotient_span_singleton hb)).2
  have : IsArtinianRing C := isArtinian_of_tower A inferInstance
  have := Fintype.ofFinite (MaximalSpectrum C)
  rw [((MaximalSpectrum.toPiLocalizationEquiv C).toLinearEquiv.restrictScalars A).length_eq,
    Module.length_pi_of_fintype, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  -- The maximal ideal of `C_q` lies over the maximal ideal of `A`, since `C` is integral over `A`.
  have : IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := by
    refine ((IsLocalRing.local_hom_tfae _).out 1 5).2 ?_
    have hq : (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).comap
        (algebraMap C (Localization.AtPrime q.asIdeal)) = q.asIdeal :=
      Localization.AtPrime.under_maximalIdeal
    have : q.asIdeal.IsMaximal := q.isMaximal
    rw [IsScalarTower.algebraMap_eq A C (Localization.AtPrime q.asIdeal), ← Ideal.comap_comap, hq]
    exact IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A q.asIdeal)
  rw [IsLocalRing.length_restrictScalars A (Localization.AtPrime q.asIdeal)
    (Localization.AtPrime q.asIdeal), Module.length_eq_of_surjective
      (M := IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
      (IsLocalRing.residue_surjective (R := A))]

/-- **The order of a norm, local form** (Fulton, *Intersection Theory*, Appendix A.3). Let `A` be
a local Noetherian domain of dimension at most one and `B` a domain finite over `A`. For `b ≠ 0`,
`length_A (B ⧸ bB) = Σ_m ord_{B_m}(b) [κ(B_m) : κ(A)]`, the sum over the maximal ideals `m` of `B`
(only those containing `b` contribute), with the residue degree `[κ(B_m) : κ(A)]` read as the
`A`-length of `κ(B_m)`. -/
theorem length_quotient_span_singleton_eq_finsum_ord [IsLocalRing A] {b : B} (hb : b ≠ 0) :
    Module.length A (B ⧸ Ideal.span {b}) =
      ∑ᶠ m : MaximalSpectrum B, Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b) *
        Module.length A (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal)) := by
  set G : MaximalSpectrum B → ℕ∞ := fun m ↦
    Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b) *
      Module.length A (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal))
  -- The maximal ideals of `B ⧸ bB` are those of `B` containing `b`.
  let c : MaximalSpectrum (B ⧸ Ideal.span {b}) → MaximalSpectrum B := fun q ↦
    ⟨q.asIdeal.comap (Ideal.Quotient.mk _),
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
  have hc : Function.Injective c := fun q q' h ↦ MaximalSpectrum.ext
    (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      (congrArg MaximalSpectrum.asIdeal h))
  have hsupp : Function.support G ⊆ Set.range c := by
    intro m hm
    have hbm : b ∈ m.asIdeal := by
      by_contra hbm
      refine hm ?_
      simp only [G, Ring.ord_of_isUnit ((IsLocalization.AtPrime.isUnit_to_map_iff _ _ b).2 hbm),
        zero_mul]
    have hle : Ideal.span {b} ≤ m.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hbm
    have : (m.asIdeal.map (Ideal.Quotient.mk (Ideal.span {b}))).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
        (by rwa [Ideal.mk_ker])
    exact ⟨⟨_, this⟩, MaximalSpectrum.ext (Ideal.comap_map_mk hle)⟩
  have hG : ∑ᶠ m, G m = ∑ᶠ q, G (c q) := by
    rw [← finsum_mem_range hc, finsum_mem_def, Set.indicator_eq_self.2 hsupp]
  rw [length_quotient_span_singleton_eq_finsum hb, hG]
  refine finsum_congr fun q ↦ ?_
  rw [length_localization_quotient_span_singleton, Ideal.length_residueField_localization_quotient]

end Local

end TauCeti
