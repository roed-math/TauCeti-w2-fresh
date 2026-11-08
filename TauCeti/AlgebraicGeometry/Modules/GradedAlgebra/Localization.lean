/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import TauCeti.Algebra.Module.LocalizedModule.DirectSum
public import TauCeti.AlgebraicGeometry.Modules.GradedAlgebra.Sections
public import TauCeti.AlgebraicGeometry.Modules.Localization
public import Mathlib.RingTheory.RingHom.FiniteType
public import TauCeti.RingTheory.Localization.Closure

/-!
# Graded rings of sections over basic opens

Let `A = ⨁ₙ Aₙ` be a graded algebra on a scheme `X` whose homogeneous components are
quasicoherent, let `U` be an affine open of `X` and `f ∈ Γ(X, U)`. Restriction of sections
identifies the graded ring `⨁ n, Γ(Aₙ, X.basicOpen f)` with the localization of the graded ring
`⨁ n, Γ(Aₙ, U)` away from `f`, placed in degree zero. In each degree this is the localization of
the sections of a quasicoherent module (`Scheme.Modules.isLocalizedModule_basicOpenRestrict`), and
localization of modules commutes with direct sums.

This is the compatibility of the affine graded charts of `A` with passage to basic opens: it is
what identifies the spectrum, or the `Proj`, of the graded ring over `X.basicOpen f` with the
corresponding open subscheme of the construction over `U`, as needed to glue affine-local
constructions with graded algebras. It is the graded counterpart of
`CategoryTheory.CommMon.isLocalization_basicOpen` for commutative `𝒪_X`-algebras.

## Main statements

* `CategoryTheory.CommMon.isLocalization_gradedSections_basicOpen`: the restriction
  `⨁ n, Γ(Aₙ, U) → ⨁ n, Γ(Aₙ, X.basicOpen f)` is a localization away from `f`.
* `CategoryTheory.CommMon.isBaseChange_restrictGradedSections`: the same restriction exhibits
  `⨁ n, Γ(Aₙ, X.basicOpen f)` as the base change of `⨁ n, Γ(Aₙ, U)` along
  `Γ(X, U) → Γ(X, X.basicOpen f)`, for the algebra structure
  `CategoryTheory.CommMon.algebraGradedSectionsBasicOpen`.
* `CategoryTheory.CommMon.finiteType_gradedSections_of_span_eq_top`: finite type of the graded
  sections over an affine open can be checked on basic opens covering it.
* `CategoryTheory.CommMon.adjoin_gradedSectionsGrading_eq_top_of_span_eq_top`: generation in degree
  one of the graded sections over an affine open can be checked on basic opens covering it.
* `CategoryTheory.CommMon.coequifibered_toGradedSectionsPresheaf`: on the affine opens of `X`, the
  presheaf of graded rings of sections is coequifibered over the structure presheaf.
-/

public section

open CategoryTheory Opposite DirectSum AlgebraicGeometry Scheme.AffineZariskiSite

namespace TauCeti

universe u

noncomputable section

variable {X : Scheme.{u}} (A : CommMon (GradedObject ℕ X.Modules))

/-- The `Γ(X, U)`-module structure on the graded sections over `X.basicOpen f`, assembled from the
module structures `Scheme.Modules.moduleBasicOpen` of the homogeneous components, is
multiplication by the restriction of the structure map `Γ(X, U) → ⨁ n, Γ(Aₙ, U)`. -/
private lemma smul_gradedSections_basicOpen {U : X.Opens} (f r : Γ(X, U))
    (z : ⨁ n, Γ(A.X n, X.basicOpen f)) :
    r • z = A.restrictGradedSections (homOfLE (X.basicOpen_le f))
      (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) r) * z := by
  rw [CommMon.restrictGradedSections_algebraMap, ← Algebra.smul_def]
  ext n
  rw [DirectSum.smul_apply, DirectSum.smul_apply]
  -- The `Γ(X, U)`-algebra structure on `Γ(X, X.basicOpen f)` is restriction of functions
  -- (`AlgebraicGeometry.Scheme.algebra_section_section_basicOpen`), so its algebra map is the
  -- restriction appearing on the right.
  exact (algebraMap_smul Γ(X, X.basicOpen f) r (z n)).symm

/-- For a graded algebra `A` with quasicoherent homogeneous components, an affine open `U` and
`f ∈ Γ(X, U)`, restriction exhibits the graded ring of sections `⨁ n, Γ(Aₙ, X.basicOpen f)` as the
localization of `⨁ n, Γ(Aₙ, U)` away from the image of `f` in degree zero. -/
theorem _root_.CategoryTheory.CommMon.isLocalization_gradedSections_basicOpen
    [∀ n, (A.X n).IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) :
    letI := (A.restrictGradedSections (homOfLE (X.basicOpen_le f))).toAlgebra
    IsLocalization.Away (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) f)
      (⨁ n, Γ(A.X n, X.basicOpen f)) := by
  let := (A.restrictGradedSections (homOfLE (X.basicOpen_le f))).toAlgebra
  -- Restriction of graded sections is the direct sum of the degreewise restrictions, each of
  -- which is a localization of modules away from `f`.
  let φ := DirectSum.lmap fun n ↦ (A.X n).basicOpenRestrict f
  have := fun n ↦ (A.X n).isLocalizedModule_basicOpenRestrict hU f
  have hφ (x : ⨁ n, Γ(A.X n, U)) :
      φ x = algebraMap (⨁ n, Γ(A.X n, U)) (⨁ n, Γ(A.X n, X.basicOpen f)) x := by
    ext n
    rw [DirectSum.lmap_apply, Scheme.Modules.basicOpenRestrict_apply,
      RingHom.algebraMap_toAlgebra, CommMon.restrictGradedSections_apply]
  refine (isLocalization_iff _ _).mpr ⟨?_, fun z ↦ ?_, fun {x y} h ↦ ?_⟩
  · rintro ⟨_, k, rfl⟩
    rw [map_pow, RingHom.algebraMap_toAlgebra, CommMon.restrictGradedSections_algebraMap]
    exact ((X.toRingedSpace.isUnit_res_basicOpen f).map _).pow k
  · obtain ⟨⟨x, _, k, rfl⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers f) φ z
    refine ⟨⟨x, ⟨_, k, rfl⟩⟩, ?_⟩
    dsimp only at hx ⊢
    rw [Submonoid.smul_def, smul_gradedSections_basicOpen, hφ, map_pow] at hx
    rw [mul_comm, ← hx, RingHom.algebraMap_toAlgebra]
  · obtain ⟨⟨_, k, rfl⟩, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f)
      (f := φ) ((hφ x).trans (h.trans (hφ y).symm))
    refine ⟨⟨_, k, rfl⟩, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def] at hc
    dsimp only
    rwa [← map_pow]

section BaseChange

variable {U : X.Opens} (f : Γ(X, U))

/-- The `Γ(X, U)`-algebra structure on `⨁ n, Γ(Aₙ, D(f))` whose underlying module structure is the
one by restriction of scalars along `Γ(X, U) → Γ(X, D(f))` (`Scheme.Modules.moduleBasicOpen`). -/
abbrev _root_.CategoryTheory.CommMon.algebraGradedSectionsBasicOpen :
    Algebra Γ(X, U) (⨁ n, Γ(A.X n, X.basicOpen f)) :=
  Algebra.ofModule
    (fun r x y ↦ by rw [← algebraMap_smul Γ(X, X.basicOpen f) r, ← algebraMap_smul
      Γ(X, X.basicOpen f) r, smul_mul_assoc])
    (fun r x y ↦ by rw [← algebraMap_smul Γ(X, X.basicOpen f) r, ← algebraMap_smul
      Γ(X, X.basicOpen f) r, mul_smul_comm])

/-- Restriction of sections from `U` to `D(f)` is a homomorphism of `Γ(X, U)`-algebras. -/
theorem _root_.CategoryTheory.CommMon.restrictGradedSections_algebraMap_basicOpen (r : Γ(X, U)) :
    let := A.algebraGradedSectionsBasicOpen f
    A.restrictGradedSectionsGradedHom (homOfLE (X.basicOpen_le f))
        (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) r) =
      algebraMap Γ(X, U) (⨁ n, Γ(A.X n, X.basicOpen f)) r := by
  intro
  rw [CommMon.restrictGradedSectionsGradedHom_apply, CommMon.restrictGradedSections_algebraMap,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  exact algebraMap_smul Γ(X, X.basicOpen f) r (1 : ⨁ n, Γ(A.X n, X.basicOpen f))

/-- Over an affine open `U` and `f ∈ Γ(X, U)`, restriction of sections exhibits
`⨁ n, Γ(Aₙ, D(f))` as the base change of `⨁ n, Γ(Aₙ, U)` along `Γ(X, U) → Γ(X, D(f))`. -/
theorem _root_.CategoryTheory.CommMon.isBaseChange_restrictGradedSections
    [∀ n, (A.X n).IsQuasicoherent] (hU : IsAffineOpen U) :
    let := A.algebraGradedSectionsBasicOpen f
    IsBaseChange Γ(X, X.basicOpen f)
      (AlgHom.mk (R := Γ(X, U))
        (A.restrictGradedSectionsGradedHom (homOfLE (X.basicOpen_le f))).toRingHom
        (A.restrictGradedSections_algebraMap_basicOpen f)).toLinearMap := by
  intro
  let := (A.restrictGradedSections (homOfLE (X.basicOpen_le f))).toAlgebra
  have := IsScalarTower.of_algebraMap_eq (R := Γ(X, U)) (S := ⨁ n, Γ(A.X n, U))
    (A := ⨁ n, Γ(A.X n, X.basicOpen f)) fun r ↦
      ((A.restrictGradedSectionsGradedHom_apply _ _).symm.trans
        (A.restrictGradedSections_algebraMap_basicOpen f r)).symm
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  have hloc := A.isLocalization_gradedSections_basicOpen hU f
  have : IsLocalization (Algebra.algebraMapSubmonoid (⨁ n, Γ(A.X n, U)) (Submonoid.powers f))
      (⨁ n, Γ(A.X n, X.basicOpen f)) := by
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  have key : IsBaseChange Γ(X, X.basicOpen f) (IsScalarTower.toAlgHom Γ(X, U)
      (⨁ n, Γ(A.X n, U)) (⨁ n, Γ(A.X n, X.basicOpen f))).toLinearMap :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) Γ(X, X.basicOpen f) _).mp
      ((isLocalizedModule_iff_isLocalization (S := Submonoid.powers f)).mpr inferInstance)
  convert key using 1
  exact LinearMap.ext fun x ↦ A.restrictGradedSectionsGradedHom_apply _ x

end BaseChange

/-- **Finite type of the graded sections is local on affine opens**: if `s` generates the unit
ideal of `Γ(X, U)` for an affine open `U`, and over each basic open `D(f)`, `f ∈ s`, the graded
sections form a finitely generated `Γ(X, D(f))`-algebra, then so do the graded sections over `U`.
Both rings over `D(f)` are localizations away from `f` (`IsAffineOpen.isLocalization_basicOpen`,
`CategoryTheory.CommMon.isLocalization_gradedSections_basicOpen`), so this is the locality of
finite type, `RingHom.finiteType_ofLocalizationSpan`. -/
theorem _root_.CategoryTheory.CommMon.finiteType_gradedSections_of_span_eq_top
    [∀ n, (A.X n).IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (s : Set Γ(X, U))
    (hs : Ideal.span s = ⊤)
    (h : ∀ f ∈ s, Algebra.FiniteType Γ(X, X.basicOpen f) (⨁ n, Γ(A.X n, X.basicOpen f))) :
    Algebra.FiniteType Γ(X, U) (⨁ n, Γ(A.X n, U)) := by
  rw [← RingHom.finiteType_algebraMap]
  refine RingHom.finiteType_ofLocalizationSpan.ofIsLocalization RingHom.finiteType_respectsIso _ s
    hs fun f ↦ ?_
  let := (A.restrictGradedSections (homOfLE (X.basicOpen_le f.1))).toAlgebra
  have := hU.isLocalization_basicOpen f.1
  have := A.isLocalization_gradedSections_basicOpen hU f.1
  refine ⟨Γ(X, X.basicOpen f.1), ⨁ n, Γ(A.X n, X.basicOpen f.1), inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, algebraMap _ _,
    RingHom.ext fun r ↦ ?_, RingHom.finiteType_algebraMap.mpr (h f.1 f.2)⟩
  -- the algebra map `⨁ n, Γ(Aₙ, U) → ⨁ n, Γ(Aₙ, D(f))` is restriction of sections
  exact (A.restrictGradedSections_algebraMap (homOfLE (X.basicOpen_le f.1)) r).symm

/-- Over an affine open `U` and `f ∈ Γ(X, U)`, every homogeneous section of degree `k` over `D(f)`
becomes the restriction of a homogeneous section of degree `k` over `U` after multiplication by a
power of `f` (`AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_map`). -/
private lemma exists_pow_mul_of_eq_restrictGradedSections [∀ n, (A.X n).IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) (k : ℕ) (w : Γ(A.X k, X.basicOpen f)) :
    ∃ n : ℕ, ∃ y ∈ A.gradedSectionsGrading U k,
      A.restrictGradedSections (homOfLE (X.basicOpen_le f)) y =
        A.restrictGradedSections (homOfLE (X.basicOpen_le f))
          (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) f) ^ n * DirectSum.of _ k w := by
  obtain ⟨n, y, hy⟩ := (A.X k).exists_pow_smul_eq_map hU f rfl (X.basicOpen_le f) w
  refine ⟨n, DirectSum.of _ k y, A.of_mem_gradedSectionsGrading k y, ?_⟩
  rw [CommMon.restrictGradedSections_of, ← hy, DirectSum.of_smul, Algebra.smul_def, map_pow,
    CommMon.restrictGradedSections_algebraMap]

/-- A degree-zero or degree-one section over a basic open has, after clearing a denominator,
a lift in the algebra generated by degrees zero and one over the larger affine open. -/
private lemma exists_pow_mul_mem_adjoin_of_mem_zero_union_one
    [∀ n, (A.X n).IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    {z : ⨁ n, Γ(A.X n, X.basicOpen f)}
    (hz : z ∈ Set.range (algebraMap (A.gradedSectionsGrading (X.basicOpen f) 0) _) ∪
      (A.gradedSectionsGrading (X.basicOpen f) 1 : Set (⨁ n, Γ(A.X n, X.basicOpen f)))) :
    ∃ (n : ℕ) (y : ⨁ n, Γ(A.X n, U)),
      y ∈ Algebra.adjoin (A.gradedSectionsGrading U 0)
        (A.gradedSectionsGrading U 1 : Set (⨁ n, Γ(A.X n, U))) ∧
      A.restrictGradedSections (homOfLE (X.basicOpen_le f)) y =
        A.restrictGradedSections (homOfLE (X.basicOpen_le f))
          (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) f) ^ n * z := by
  let B := Algebra.adjoin (A.gradedSectionsGrading U 0)
    (A.gradedSectionsGrading U 1 : Set (⨁ n, Γ(A.X n, U)))
  have hk (k : ℕ) (w : Γ(A.X k, X.basicOpen f)) (hk₀₁ : k = 0 ∨ k = 1) :
      ∃ (n : ℕ) (y : ⨁ n, Γ(A.X n, U)), y ∈ B ∧
        A.restrictGradedSections (homOfLE (X.basicOpen_le f)) y =
          A.restrictGradedSections (homOfLE (X.basicOpen_le f))
            (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) f) ^ n * DirectSum.of _ k w := by
    obtain ⟨n, y, hy, e⟩ := exists_pow_mul_of_eq_restrictGradedSections A hU f k w
    refine ⟨n, y, ?_, e⟩
    obtain rfl | rfl := hk₀₁
    · exact Subalgebra.algebraMap_mem B (⟨y, hy⟩ : A.gradedSectionsGrading U 0)
    · exact Algebra.subset_adjoin hy
  rcases hz with ⟨z, rfl⟩ | hz
  · obtain ⟨w, hw⟩ := DirectSum.mem_summand.mp z.2
    obtain ⟨n, y, hy, e⟩ := hk 0 w (.inl rfl)
    exact ⟨n, y, hy, e.trans (congrArg (_ * ·) hw)⟩
  · obtain ⟨w, rfl⟩ := DirectSum.mem_summand.mp hz
    exact hk 1 w (.inr rfl)

/-- **Generation in degree one is local on affine opens**: if `s` generates the unit ideal of
`Γ(X, U)` for an affine open `U`, and over each basic open `D(f)`, `f ∈ s`, the graded sections are
generated by the degree-one sections over the degree-zero sections, then so are the graded sections
over `U`. A section over `U` is a polynomial in degree-one sections over each `D(f)`, hence, after
multiplication by a power of `f`, a polynomial in degree-one sections over `U`
(`TauCeti.IsLocalization.exists_mul_mem_of_mem_closure`), and the powers of the `f ∈ s` generate
the unit ideal. -/
theorem _root_.CategoryTheory.CommMon.adjoin_gradedSectionsGrading_eq_top_of_span_eq_top
    [∀ n, (A.X n).IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (s : Set Γ(X, U))
    (hs : Ideal.span s = ⊤)
    (h : ∀ f ∈ s, Algebra.adjoin (A.gradedSectionsGrading (X.basicOpen f) 0)
      (A.gradedSectionsGrading (X.basicOpen f) 1 : Set (⨁ n, Γ(A.X n, X.basicOpen f))) = ⊤) :
    Algebra.adjoin (A.gradedSectionsGrading U 0)
      (A.gradedSectionsGrading U 1 : Set (⨁ n, Γ(A.X n, U))) = ⊤ := by
  let B := Algebra.adjoin (A.gradedSectionsGrading U 0)
    (A.gradedSectionsGrading U 1 : Set (⨁ n, Γ(A.X n, U)))
  have hB {y : ⨁ n, Γ(A.X n, U)} (hy : y ∈ A.gradedSectionsGrading U 0) : y ∈ B :=
    Subalgebra.algebraMap_mem _ (⟨y, hy⟩ : A.gradedSectionsGrading U 0)
  -- the functions on `U` lie in degree zero
  have hr (r : Γ(X, U)) : algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) r ∈ B := by
    rw [DirectSum.algebraMap_apply]
    exact hB (A.of_mem_gradedSectionsGrading 0 _)
  -- so `B` is a `Γ(X, U)`-submodule
  let B' : Submodule Γ(X, U) (⨁ n, Γ(A.X n, U)) :=
    { B.toSubring.toAddSubgroup with
      smul_mem' := fun r y hy ↦ by
        rw [Algebra.smul_def]
        exact mul_mem (hr r) hy }
  refine eq_top_iff.mpr fun x _ ↦ B'.mem_of_span_eq_top_of_smul_pow_mem s hs x fun ⟨f, hf⟩ ↦ ?_
  let := (A.restrictGradedSections (homOfLE (X.basicOpen_le f))).toAlgebra
  have := A.isLocalization_gradedSections_basicOpen hU f
  let G := Set.range (algebraMap (A.gradedSectionsGrading (X.basicOpen f) 0) _) ∪
    (A.gradedSectionsGrading (X.basicOpen f) 1 : Set (⨁ n, Γ(A.X n, X.basicOpen f)))
  have hG : ∀ z ∈ G, ∃ m ∈ Submonoid.powers (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) f),
      ∃ y ∈ B.toSubring, algebraMap _ (⨁ n, Γ(A.X n, X.basicOpen f)) y = algebraMap _ _ m * z := by
    intro z hz
    obtain ⟨n, y, hy, e⟩ := exists_pow_mul_mem_adjoin_of_mem_zero_union_one A hU f hz
    exact ⟨_, ⟨n, rfl⟩, y, hy, e.trans (congrArg (· * _) (map_pow _ _ n).symm)⟩
  have hx : algebraMap _ (⨁ n, Γ(A.X n, X.basicOpen f)) x ∈ Subring.closure G := by
    rw [← Algebra.adjoin_eq_ring_closure, Subalgebra.mem_toSubring]
    exact Algebra.eq_top_iff.mp (h f hf) _
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ :=
    TauCeti.IsLocalization.exists_mul_mem_of_mem_closure (Submonoid.powers_le.mpr (hr f)) hG hx
  refine ⟨n, ?_⟩
  change _ ∈ B
  rw [Algebra.smul_def, map_pow]
  exact hn

/-- On the affine opens of `X`, the presheaf of graded rings of sections of a graded algebra with
quasicoherent homogeneous components is coequifibered over the structure presheaf: its graded rings
of sections over basic opens are localizations. This is the condition under which Mathlib glues the
spectra of its sections (`AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData`). -/
theorem _root_.CategoryTheory.CommMon.coequifibered_toGradedSectionsPresheaf
    [∀ n, (A.X n).IsQuasicoherent] :
    ((toOpensFunctor X).op.whiskerLeft A.toGradedSectionsPresheaf).Coequifibered := by
  apply coequifibered_iff_forall_isLocalizationAway.mpr
  intro U f
  rw [Functor.whiskerLeft_app, CommMon.toGradedSectionsPresheaf_app]
  exact A.isLocalization_gradedSections_basicOpen U.2 f

end

end TauCeti
