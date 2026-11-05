/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.CategoryTheory.Abelian.Exact
public import TauCeti.CategoryTheory.Abelian.Injective.Horseshoe

/-!
# Cartan–Eilenberg resolutions of cochain complexes

Let `K` be a cochain complex in an abelian category with enough injectives, indexed by `ℕ`. For
each degree `q` there are two short exact sequences

* `0 ⟶ Zᵠ ⟶ Kᵠ ⟶ Kᵠ / Zᵠ ⟶ 0` (`CochainComplex.cyclesShortComplex`), with `Zᵠ = K.cycles q`;
* `0 ⟶ Kᵠ / Zᵠ ⟶ Zᵠ⁺¹ ⟶ Hᵠ⁺¹ ⟶ 0` (`CochainComplex.boundariesShortComplex`), whose first map is
  induced by the differential.

Choosing injective resolutions of the objects `Kᵠ / Zᵠ` and `Hᵠ⁺¹` and of `Z⁰`, the horseshoe lemma
(`CategoryTheory.InjectiveResolution.horseshoe`) gives injective resolutions of every `Zᵠ` and
every `Kᵠ` (`CochainComplex.cartanEilenbergResolution`), such that the differential of `K` lifts
to the composite `J(Kᵠ) ⟶ J(Kᵠ / Zᵠ) ⟶ J(Zᵠ⁺¹) ⟶ J(Kᵠ⁺¹)` of the chain maps of the horseshoes.
These lifts square to zero, and form the Cartan–Eilenberg double complex
`CochainComplex.cartanEilenberg K`, whose columns are injective resolutions of the terms of `K`,
the augmentations `Kᵠ ⟶ J(Kᵠ)⁰` commuting with the differentials
(`CochainComplex.cartanEilenbergResolution_ι₀_comp_cartanEilenbergD_f`). By construction, the
cycles, boundaries and cohomology of each row are resolved by the chosen resolutions of `Zᵠ`,
`Kᵠ / Zᵠ` and `Hᵠ`.

After any additive functor `G`, the row `q ↦ G(J(Kᵠ)ᵖ)` in resolution degree `p` has cohomology
`G(J(Hᵠ)ᵖ)` in degree `q` (`CochainComplex.cartanEilenbergRowHomologyIso`), where `J(Hᵠ)` is the
chosen resolution `CochainComplex.homologyResolution` of `Hᵠ(K)`, and under these isomorphisms
the vertical differentials induce the differentials of `G(J(Hᵠ))`
(`CochainComplex.homologyMap_map_flip_d_cartanEilenbergRowHomologyIso_hom`): the rows are sums of
split pieces, which every additive functor preserves.

The Cartan–Eilenberg double complex is the input of the Grothendieck spectral sequence, and
hence of the Leray spectral sequence.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 5.7.
* [Stacks, Section 13.21 (015G)](https://stacks.math.columbia.edu/tag/015G)
-/

@[expose] public section

open CategoryTheory Category Limits Preadditive

universe v u

namespace CategoryTheory

namespace ShortComplex.LeftHomologyData

variable {C : Type u} [Category.{v} C] [Preadditive C] (S : ShortComplex C) {A Z H B : C}
  (e : S.X₁ ⟶ A) [he : Epi e] (a : A ⟶ Z) (π : Z ⟶ H) (wπ : a ≫ π = 0)
  (hπ : IsColimit (CokernelCofork.ofπ π wπ)) (i : Z ⟶ S.X₂) (c : S.X₂ ⟶ B) (wi : i ≫ c = 0)
  (hi : IsLimit (KernelFork.ofι i wi)) (m : B ⟶ S.X₃) [hm : Mono m] (hf : e ≫ a ≫ i = S.f)
  (hg : c ≫ m = S.g)

omit he in
include hf in
/-- The map from `X₁` to the kernel `Z` of `X₂ ⟶ X₃` induced by `S.f` is `X₁ ⟶ A ⟶ Z`. -/
lemma lift_eq_of_factorization :
    (isKernelCompMono hi m hg.symm).lift (KernelFork.ofι S.f S.zero) = e ≫ a := by
  have : Mono i := Fork.IsLimit.mono hi
  rw [← cancel_mono i, assoc, hf]
  exact (isKernelCompMono hi m hg.symm).fac _ WalkingParallelPair.zero

/-- The left homology data of a short complex `S` whose first map factors as `X₁ ⟶ A ⟶ Z ⟶ X₂`
with `X₁ ⟶ A` an epimorphism, and whose second map factors as `X₂ ⟶ B ⟶ X₃` with `B ⟶ X₃` a
monomorphism: its cycles are a kernel `Z` of `X₂ ⟶ B`, and its homology a cokernel `H` of
`A ⟶ Z`. It is an abbreviation so that its cycles and homology are reducibly `Z` and `H`. -/
@[simps]
noncomputable abbrev ofFactorization : S.LeftHomologyData where
  K := Z
  H := H
  i := i
  π := π
  wi := by rw [← hg, reassoc_of% wi, zero_comp]
  hi := isKernelCompMono hi m hg.symm
  wπ := by
    rw [lift_eq_of_factorization S e a i c wi hi m hf hg, assoc, wπ, comp_zero]
  hπ := isCokernelEpiComp hπ e (lift_eq_of_factorization S e a i c wi hi m hf hg)

end ShortComplex.LeftHomologyData

namespace InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An injective resolution of `Z` is one of every object isomorphic to `Z`, with the same
complex. -/
@[simps cocomplex]
noncomputable def ofIso {Z Z' : C} (I : InjectiveResolution Z) (e : Z' ≅ Z) :
    InjectiveResolution Z' where
  cocomplex := I.cocomplex
  injective := I.injective
  hasHomology := I.hasHomology
  ι := (CochainComplex.single₀ C).map e.hom ≫ I.ι

end InjectiveResolution

end CategoryTheory

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] (K : CochainComplex C ℕ)

/-- The short complex `Zᵠ ⟶ Kᵠ ⟶ Kᵠ / Zᵠ` of a cochain complex. -/
noncomputable abbrev cyclesShortComplex (q : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles q) (cokernel.π (K.iCycles q)) (cokernel.condition _)

/-- The short complex `Zᵠ ⟶ Kᵠ ⟶ Kᵠ / Zᵠ` is short exact. -/
lemma cyclesShortComplex_shortExact (q : ℕ) : (K.cyclesShortComplex q).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance

/-- The map `Kᵠ / Zᵠ ⟶ Zᵠ⁺¹` induced by the differential. -/
noncomputable def cokernelCyclesToCycles (q : ℕ) : cokernel (K.iCycles q) ⟶ K.cycles (q + 1) :=
  cokernel.desc _ (K.toCycles q (q + 1)) (by
    rw [← cancel_mono (K.iCycles (q + 1)), assoc, HomologicalComplex.toCycles_i,
      HomologicalComplex.iCycles_d, zero_comp])

@[reassoc (attr := simp)]
lemma π_cokernelCyclesToCycles (q : ℕ) :
    cokernel.π (K.iCycles q) ≫ K.cokernelCyclesToCycles q = K.toCycles q (q + 1) :=
  cokernel.π_desc _ _ _

@[reassoc (attr := simp)]
lemma cokernelCyclesToCycles_homologyπ (q : ℕ) :
    K.cokernelCyclesToCycles q ≫ K.homologyπ (q + 1) = 0 := by
  rw [← cancel_epi (cokernel.π (K.iCycles q)), π_cokernelCyclesToCycles_assoc,
    HomologicalComplex.toCycles_comp_homologyπ, comp_zero]

/-- The short complex `Kᵠ / Zᵠ ⟶ Zᵠ⁺¹ ⟶ Hᵠ⁺¹` of a cochain complex. -/
noncomputable abbrev boundariesShortComplex (q : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.cokernelCyclesToCycles q) (K.homologyπ (q + 1))
    (K.cokernelCyclesToCycles_homologyπ q)

/-- The map `Kᵠ / Zᵠ ⟶ Zᵠ⁺¹` is a monomorphism, since `Zᵠ` is the kernel of `Kᵠ ⟶ Zᵠ⁺¹`. -/
instance (q : ℕ) : Mono (K.cokernelCyclesToCycles q) := by
  refine Preadditive.mono_of_cancel_zero _ fun {T} x hx ↦ ?_
  obtain ⟨T', π, _, y, hy⟩ := surjective_up_to_refinements_of_epi (cokernel.π (K.iCycles q)) x
  have hy' : y ≫ K.d q (q + 1) = 0 := by
    rw [← HomologicalComplex.toCycles_i, ← π_cokernelCyclesToCycles, ← assoc, ← assoc, ← hy,
      assoc, assoc, reassoc_of% hx, zero_comp, comp_zero]
  have hy'' : y = K.liftCycles y (q + 1) (by simp) hy' ≫ K.iCycles q := by simp
  rw [← cancel_epi π, comp_zero, hy, hy'', assoc, cokernel.condition, comp_zero]

/-- The short complex `Kᵠ / Zᵠ ⟶ Zᵠ⁺¹ ⟶ Hᵠ⁺¹` is short exact. -/
lemma boundariesShortComplex_shortExact (q : ℕ) : (K.boundariesShortComplex q).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  have hS : (ShortComplex.mk _ _ (K.toCycles_comp_homologyπ q (q + 1))).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel q (q + 1) (by simp))
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x₂ hx₂
  obtain ⟨T', π, _, y, hy⟩ := hS.exact_up_to_refinements x₂ hx₂
  exact ⟨T', π, inferInstance, y ≫ cokernel.π _, by simpa using hy⟩

variable [HasInjectiveResolutions C]

/-- The chosen injective resolutions `J(Zᵠ)` of the cycles of a cochain complex: an arbitrary one
in degree `0`, and in degree `q + 1` the horseshoe of `0 ⟶ Kᵠ / Zᵠ ⟶ Zᵠ⁺¹ ⟶ Hᵠ⁺¹ ⟶ 0`. -/
noncomputable def cyclesResolution : (q : ℕ) → InjectiveResolution (K.cycles q)
  | 0 => injectiveResolution _
  | q + 1 => InjectiveResolution.horseshoe (K.boundariesShortComplex_shortExact q)
      (injectiveResolution _) (injectiveResolution _)

/-- The injective resolution `J(Kᵠ)` of the term of degree `q` of a cochain complex: the horseshoe
of `0 ⟶ Zᵠ ⟶ Kᵠ ⟶ Kᵠ / Zᵠ ⟶ 0`. -/
noncomputable def cartanEilenbergResolution (q : ℕ) : InjectiveResolution (K.X q) :=
  InjectiveResolution.horseshoe (K.cyclesShortComplex_shortExact q) (K.cyclesResolution q)
    (injectiveResolution _)

/-- The chain map `J(Zᵠ) ⟶ J(Kᵠ)` of the horseshoe, lifting `Zᵠ ⟶ Kᵠ`. -/
noncomputable def cyclesResolutionInl (q : ℕ) :
    (K.cyclesResolution q).cocomplex ⟶ (K.cartanEilenbergResolution q).cocomplex :=
  InjectiveResolution.horseshoeInl (K.cyclesShortComplex_shortExact q) (K.cyclesResolution q)
    (injectiveResolution _)

/-- The chain map `J(Kᵠ) ⟶ J(Kᵠ / Zᵠ)` of the horseshoe, lifting `Kᵠ ⟶ Kᵠ / Zᵠ`. -/
noncomputable def cartanEilenbergResolutionSnd (q : ℕ) :
    (K.cartanEilenbergResolution q).cocomplex ⟶
      (injectiveResolution (cokernel (K.iCycles q))).cocomplex :=
  InjectiveResolution.horseshoeSnd (K.cyclesShortComplex_shortExact q) (K.cyclesResolution q)
    (injectiveResolution _)

/-- The chain map `J(Kᵠ / Zᵠ) ⟶ J(Zᵠ⁺¹)` of the horseshoe, lifting `Kᵠ / Zᵠ ⟶ Zᵠ⁺¹`. -/
noncomputable def cokernelCyclesResolutionInl (q : ℕ) :
    (injectiveResolution (cokernel (K.iCycles q))).cocomplex ⟶
      (K.cyclesResolution (q + 1)).cocomplex :=
  InjectiveResolution.horseshoeInl (K.boundariesShortComplex_shortExact q)
    (injectiveResolution _) (injectiveResolution _)

@[reassoc (attr := simp)]
lemma cyclesResolutionInl_cartanEilenbergResolutionSnd (q : ℕ) :
    K.cyclesResolutionInl q ≫ K.cartanEilenbergResolutionSnd q = 0 :=
  (InjectiveResolution.horseshoeShortComplex (K.cyclesShortComplex_shortExact q)
    (K.cyclesResolution q) (injectiveResolution _)).zero

@[reassoc (attr := simp)]
lemma cyclesResolution_ι₀_comp_cyclesResolutionInl_f (q : ℕ) :
    (K.cyclesResolution q).ι₀ ≫ (K.cyclesResolutionInl q).f 0 =
      K.iCycles q ≫ (K.cartanEilenbergResolution q).ι₀ :=
  InjectiveResolution.ι₀_comp_horseshoeInl_f_zero (K.cyclesShortComplex_shortExact q)
    (K.cyclesResolution q) (injectiveResolution _)

@[reassoc (attr := simp)]
lemma cartanEilenbergResolution_ι₀_comp_cartanEilenbergResolutionSnd_f (q : ℕ) :
    (K.cartanEilenbergResolution q).ι₀ ≫ (K.cartanEilenbergResolutionSnd q).f 0 =
      cokernel.π (K.iCycles q) ≫ (injectiveResolution (cokernel (K.iCycles q))).ι₀ :=
  InjectiveResolution.horseshoe_ι₀_comp_horseshoeSnd_f_zero (K.cyclesShortComplex_shortExact q)
    (K.cyclesResolution q) (injectiveResolution _)

@[reassoc (attr := simp)]
lemma ι₀_comp_cokernelCyclesResolutionInl_f (q : ℕ) :
    (injectiveResolution (cokernel (K.iCycles q))).ι₀ ≫ (K.cokernelCyclesResolutionInl q).f 0 =
      K.cokernelCyclesToCycles q ≫ (K.cyclesResolution (q + 1)).ι₀ :=
  InjectiveResolution.ι₀_comp_horseshoeInl_f_zero (K.boundariesShortComplex_shortExact q)
    (injectiveResolution _) (injectiveResolution _)

/-- The lift `J(Kᵠ) ⟶ J(Kᵠ⁺¹)` of the differential of `K`: the composite
`J(Kᵠ) ⟶ J(Kᵠ / Zᵠ) ⟶ J(Zᵠ⁺¹) ⟶ J(Kᵠ⁺¹)` of the chain maps of the horseshoes. -/
noncomputable def cartanEilenbergD (q : ℕ) :
    (K.cartanEilenbergResolution q).cocomplex ⟶ (K.cartanEilenbergResolution (q + 1)).cocomplex :=
  K.cartanEilenbergResolutionSnd q ≫ K.cokernelCyclesResolutionInl q ≫
    K.cyclesResolutionInl (q + 1)

@[reassoc (attr := simp)]
lemma cartanEilenbergD_comp_cartanEilenbergD (q : ℕ) :
    K.cartanEilenbergD q ≫ K.cartanEilenbergD (q + 1) = 0 := by
  simp [cartanEilenbergD]

/-- The lifts of the differential of `K` commute with the augmentations: the square
`Kᵠ ⟶ J(Kᵠ)⁰`, `Kᵠ⁺¹ ⟶ J(Kᵠ⁺¹)⁰` commutes. -/
@[reassoc]
lemma cartanEilenbergResolution_ι₀_comp_cartanEilenbergD_f (q : ℕ) :
    (K.cartanEilenbergResolution q).ι₀ ≫ (K.cartanEilenbergD q).f 0 =
      K.d q (q + 1) ≫ (K.cartanEilenbergResolution (q + 1)).ι₀ := by
  simp [cartanEilenbergD]

/-- The Cartan–Eilenberg double complex of a cochain complex `K`: its `q`-th column is the
injective resolution `J(Kᵠ)`, and its differentials lift the differential of `K`. -/
noncomputable def cartanEilenberg : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  CochainComplex.of (fun q ↦ (K.cartanEilenbergResolution q).cocomplex) K.cartanEilenbergD
    K.cartanEilenbergD_comp_cartanEilenbergD

lemma cartanEilenberg_X (q : ℕ) :
    K.cartanEilenberg.X q = (K.cartanEilenbergResolution q).cocomplex := rfl

lemma cartanEilenberg_d (q : ℕ) : K.cartanEilenberg.d q (q + 1) = K.cartanEilenbergD q := by
  dsimp only [cartanEilenberg]
  exact CochainComplex.of_d _ _ q


/-! ### The rows of the Cartan–Eilenberg double complex -/

/-- The chosen injective resolutions `J(Hᵠ)` of the cohomology of a cochain complex: in degree
`0`, the resolution `J(Z⁰)` of `Z⁰ = H⁰`, and in degree `q + 1` an arbitrary one. -/
noncomputable def homologyResolution : (q : ℕ) → InjectiveResolution (K.homology q)
  | 0 => (K.cyclesResolution 0).ofIso K.isoHomologyπ₀.symm
  | _ + 1 => injectiveResolution _

/-- The chain map `J(Zᵠ) ⟶ J(Hᵠ)`: the identity in degree `0`, and in degree `q + 1` the chain map
of the horseshoe, lifting `Zᵠ⁺¹ ⟶ Hᵠ⁺¹`. -/
noncomputable def cyclesResolutionSnd : (q : ℕ) →
    (K.cyclesResolution q).cocomplex ⟶ (K.homologyResolution q).cocomplex
  | 0 => 𝟙 (K.cyclesResolution 0).cocomplex
  | q + 1 => InjectiveResolution.horseshoeSnd (K.boundariesShortComplex_shortExact q)
      (injectiveResolution _) (injectiveResolution _)

instance (p q : ℕ) : IsSplitMono ((K.cyclesResolutionInl q).f p) :=
  IsSplitMono.mk' ⟨biprod.fst, biprod.inl_fst⟩

instance (p q : ℕ) : IsSplitMono ((K.cokernelCyclesResolutionInl q).f p) :=
  IsSplitMono.mk' ⟨biprod.fst, biprod.inl_fst⟩

instance (p q : ℕ) : IsSplitEpi ((K.cartanEilenbergResolutionSnd q).f p) :=
  IsSplitEpi.mk' ⟨biprod.inr, biprod.inr_snd⟩

instance (p : ℕ) : IsIso ((K.cyclesResolutionSnd 0).f p) :=
  inferInstanceAs (IsIso (𝟙 _))

instance (p q : ℕ) : IsSplitEpi ((K.cyclesResolutionSnd q).f p) := by
  cases q with
  | zero => exact IsSplitEpi.mk' ⟨𝟙 _, Category.id_comp _⟩
  | succ q => exact IsSplitEpi.mk' ⟨biprod.inr, biprod.inr_snd⟩

variable {D : Type*} [Category* D] [Abelian D] (G : C ⥤ D) [G.Additive]

/-- The image under `G` of the row `p` of the Cartan–Eilenberg double complex: the complex
`q ↦ G(J(Kᵠ)ᵖ)`. -/
noncomputable abbrev cartanEilenbergRow (p : ℕ) : CochainComplex D ℕ :=
  (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (K.cartanEilenberg.flip.X p)

/-- The inclusion `G(J(Zᵠ)ᵖ) ⟶ G(J(Kᵠ)ᵖ)` of the cycles of the row `p` of `G(J)`, the image of the
chain map `J(Zᵠ) ⟶ J(Kᵠ)` of the horseshoe. -/
noncomputable def cartanEilenbergRowι (p q : ℕ) :
    G.obj ((K.cyclesResolution q).cocomplex.X p) ⟶ (K.cartanEilenbergRow G p).X q :=
  G.map ((K.cyclesResolutionInl q).f p)

/-- The projection `G(J(Kᵠ)ᵖ) ⟶ G(J(Kᵠ / Zᵠ)ᵖ)`, the image of the chain map `J(Kᵠ) ⟶ J(Kᵠ / Zᵠ)` of
the horseshoe. -/
noncomputable def cartanEilenbergRowSnd (p q : ℕ) : (K.cartanEilenbergRow G p).X q ⟶
    G.obj ((injectiveResolution (cokernel (K.iCycles q))).cocomplex.X p) :=
  G.map ((K.cartanEilenbergResolutionSnd q).f p)

instance (p q : ℕ) : Mono (K.cartanEilenbergRowι G p q) :=
  inferInstanceAs (Mono (G.map ((K.cyclesResolutionInl q).f p)))

instance (p q : ℕ) : Epi (K.cartanEilenbergRowSnd G p q) :=
  inferInstanceAs (Epi (G.map ((K.cartanEilenbergResolutionSnd q).f p)))

@[reassoc (attr := simp)]
lemma cartanEilenbergRowι_cartanEilenbergRowSnd (p q : ℕ) :
    K.cartanEilenbergRowι G p q ≫ K.cartanEilenbergRowSnd G p q = 0 := by
  have h : G.map ((K.cyclesResolutionInl q).f p ≫ (K.cartanEilenbergResolutionSnd q).f p) = 0 := by
    rw [← HomologicalComplex.comp_f, cyclesResolutionInl_cartanEilenbergResolutionSnd,
      HomologicalComplex.zero_f, G.map_zero]
  exact (G.map_comp _ _).symm.trans h

/-- The differentials of the row `p` of `G(J)`: the composite
`G(J(Kᵠ)ᵖ) ⟶ G(J(Kᵠ / Zᵠ)ᵖ) ⟶ G(J(Zᵠ⁺¹)ᵖ) ⟶ G(J(Kᵠ⁺¹)ᵖ)`. -/
lemma cartanEilenbergRow_d (p q : ℕ) :
    (K.cartanEilenbergRow G p).d q (q + 1) = K.cartanEilenbergRowSnd G p q ≫
      G.map ((K.cokernelCyclesResolutionInl q).f p) ≫ K.cartanEilenbergRowι G p (q + 1) := by
  have h : G.map ((K.cartanEilenbergD q).f p) = G.map ((K.cartanEilenbergResolutionSnd q).f p) ≫
      G.map ((K.cokernelCyclesResolutionInl q).f p) ≫
        G.map ((K.cyclesResolutionInl (q + 1)).f p) := by
    simp [cartanEilenbergD]
  -- The row of the flipped bicomplex is formed by the resolutions by definition.
  exact (congrArg G.map (HomologicalComplex.congr_hom (K.cartanEilenberg_d q) p)).trans h

@[reassoc (attr := simp)]
lemma cartanEilenbergRowι_d (p q : ℕ) :
    K.cartanEilenbergRowι G p q ≫ (K.cartanEilenbergRow G p).d q (q + 1) = 0 := by
  rw [cartanEilenbergRow_d, cartanEilenbergRowι_cartanEilenbergRowSnd_assoc, zero_comp]

/-- The vertical differentials of `G(J)` restrict to the cycles of the rows: the differentials of
`G(J(Zᵠ))`. -/
@[reassoc]
lemma cartanEilenbergRowι_comp_map_flip_d_f (p q : ℕ) :
    K.cartanEilenbergRowι G p q ≫
        ((G.mapHomologicalComplex _).map (K.cartanEilenberg.flip.d p (p + 1))).f q =
      G.map ((K.cyclesResolution q).cocomplex.d p (p + 1)) ≫ K.cartanEilenbergRowι G (p + 1) q :=
  -- The vertical differentials of the flipped bicomplex are those of the resolutions by
  -- definition.
  (G.map_comp _ _).symm.trans ((congrArg G.map ((K.cyclesResolutionInl q).comm p (p + 1))).trans
    (G.map_comp _ _))

/-- The left homology data of the row `p` of `G(J)` in degree `0`: its cycles and its
cohomology are `G(J(Z⁰)ᵖ)`. It is an abbreviation so that these are reducibly the objects of
`G(J(Z⁰))` and `G(J(H⁰))`. -/
noncomputable abbrev cartanEilenbergRowLeftHomologyDataZero (p : ℕ) :
    ((K.cartanEilenbergRow G p).sc' 0 0 1).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofFactorization _ (𝟙 _) 0
    (G.map ((K.cyclesResolutionSnd 0).f p)) zero_comp
    ((CokernelCofork.IsColimit.ofId _ rfl).ofIsoColimit
      (Cofork.ext (asIso (G.map ((K.cyclesResolutionSnd 0).f p))) (Category.id_comp _)))
    (K.cartanEilenbergRowι G p 0)
    (K.cartanEilenbergRowSnd G p 0) _
    ((ShortComplex.Splitting.ofHasBinaryBiproduct _ _).map G).shortExact.fIsKernel
    (G.map ((K.cokernelCyclesResolutionInl 0).f p) ≫ K.cartanEilenbergRowι G p 1)
    (by simp) (K.cartanEilenbergRow_d G p 0).symm
    (hm := inferInstanceAs (Mono (G.map ((K.cokernelCyclesResolutionInl 0).f p) ≫
      G.map ((K.cyclesResolutionInl 1).f p))))

/-- The left homology data of the row `p` of `G(J)` in degree `q + 1`: its cycles are
`G(J(Zᵠ⁺¹)ᵖ)`, and its cohomology `G(J(Hᵠ⁺¹)ᵖ)`. It is an abbreviation for the same reason as
`CochainComplex.cartanEilenbergRowLeftHomologyDataZero`. -/
noncomputable abbrev cartanEilenbergRowLeftHomologyDataSucc (p q : ℕ) :
    ((K.cartanEilenbergRow G p).sc' q (q + 1) (q + 2)).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofFactorization _ (K.cartanEilenbergRowSnd G p q)
    (G.map ((K.cokernelCyclesResolutionInl q).f p)) (G.map ((K.cyclesResolutionSnd (q + 1)).f p))
    _ ((ShortComplex.Splitting.ofHasBinaryBiproduct _ _).map G).shortExact.gIsCokernel
    (K.cartanEilenbergRowι G p (q + 1)) (K.cartanEilenbergRowSnd G p (q + 1)) _
    ((ShortComplex.Splitting.ofHasBinaryBiproduct _ _).map G).shortExact.fIsKernel
    (G.map ((K.cokernelCyclesResolutionInl (q + 1)).f p) ≫ K.cartanEilenbergRowι G p (q + 2))
    (K.cartanEilenbergRow_d G p q).symm (K.cartanEilenbergRow_d G p (q + 1)).symm
    (hm := inferInstanceAs (Mono (G.map ((K.cokernelCyclesResolutionInl (q + 1)).f p) ≫
      G.map ((K.cyclesResolutionInl (q + 2)).f p))))

/-- **The rows of the Cartan–Eilenberg double complex**, after any additive functor `G`: the
cohomology in degree `q` of the row `q ↦ G(J(Kᵠ)ᵖ)` is `G(J(Hᵠ)ᵖ)`. -/
noncomputable def cartanEilenbergRowHomologyIso (p : ℕ) : (q : ℕ) →
    (K.cartanEilenbergRow G p).homology q ≅ G.obj ((K.homologyResolution q).cocomplex.X p)
  | 0 => (K.cartanEilenbergRow G p).homologyIsoSc' 0 0 1 (by simp) (by simp) ≪≫
      (K.cartanEilenbergRowLeftHomologyDataZero G p).homologyIso
  | q + 1 => (K.cartanEilenbergRow G p).homologyIsoSc' q (q + 1) (q + 2) (by simp) (by simp) ≪≫
      (K.cartanEilenbergRowLeftHomologyDataSucc G p q).homologyIso

/-- The isomorphism `cartanEilenbergRowHomologyIso` sends the class of a cycle of `G(J(Zᵠ)ᵖ)` to
its image in `G(J(Hᵠ)ᵖ)`. -/
@[reassoc (attr := simp)]
lemma liftCycles_homologyπ_cartanEilenbergRowHomologyIso_hom (p q : ℕ) :
    (K.cartanEilenbergRow G p).liftCycles (K.cartanEilenbergRowι G p q) (q + 1) (by simp)
        (K.cartanEilenbergRowι_d G p q) ≫
      (K.cartanEilenbergRow G p).homologyπ q ≫ (K.cartanEilenbergRowHomologyIso G p q).hom =
    G.map ((K.cyclesResolutionSnd q).f p) := by
  cases q with
  | zero =>
    have h : (K.cartanEilenbergRow G p).liftCycles (K.cartanEilenbergRowι G p 0) 1
        (by simp) (K.cartanEilenbergRowι_d G p 0) ≫
        ((K.cartanEilenbergRow G p).cyclesIsoSc' 0 0 1 (by simp) (by simp)).hom ≫
        (K.cartanEilenbergRowLeftHomologyDataZero G p).cyclesIso.hom =
          𝟙 (K.cartanEilenbergRowLeftHomologyDataZero G p).K := by
      rw [← cancel_mono (K.cartanEilenbergRowLeftHomologyDataZero G p).i, Category.assoc,
        Category.assoc, ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
        HomologicalComplex.cyclesIsoSc'_hom_iCycles, HomologicalComplex.liftCycles_i,
        Category.id_comp]
    simp only [cartanEilenbergRowHomologyIso, Iso.trans_hom,
      HomologicalComplex.π_homologyIsoSc'_hom_assoc,
      ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom, reassoc_of% h]
  | succ q =>
    have h : (K.cartanEilenbergRow G p).liftCycles (K.cartanEilenbergRowι G p (q + 1))
        (q + 2) (by simp) (K.cartanEilenbergRowι_d G p (q + 1)) ≫
        ((K.cartanEilenbergRow G p).cyclesIsoSc' q (q + 1) (q + 2) (by simp) (by simp)).hom ≫
        (K.cartanEilenbergRowLeftHomologyDataSucc G p q).cyclesIso.hom =
          𝟙 (K.cartanEilenbergRowLeftHomologyDataSucc G p q).K := by
      rw [← cancel_mono (K.cartanEilenbergRowLeftHomologyDataSucc G p q).i, Category.assoc,
        Category.assoc, ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
        HomologicalComplex.cyclesIsoSc'_hom_iCycles, HomologicalComplex.liftCycles_i,
        Category.id_comp]
    simp only [cartanEilenbergRowHomologyIso, Iso.trans_hom,
      HomologicalComplex.π_homologyIsoSc'_hom_assoc,
      ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom, reassoc_of% h]

instance (p q : ℕ) : Epi ((K.cartanEilenbergRow G p).liftCycles (K.cartanEilenbergRowι G p q)
    (q + 1) (by simp) (K.cartanEilenbergRowι_d G p q) ≫
      (K.cartanEilenbergRow G p).homologyπ q) := by
  have h := K.liftCycles_homologyπ_cartanEilenbergRowHomologyIso_hom G p q
  rw [← Category.assoc] at h
  rw [(Iso.eq_comp_inv _).2 h]
  infer_instance

/-- **The cohomology of the rows of `G(J)` is `G(J(Hᵠ))`, as a complex**: under
`cartanEilenbergRowHomologyIso`, the vertical differentials of `G(J)` induce the differentials of
`G(J(Hᵠ))`. -/
@[reassoc]
theorem homologyMap_map_flip_d_cartanEilenbergRowHomologyIso_hom (p q : ℕ) :
    HomologicalComplex.homologyMap
        ((G.mapHomologicalComplex _).map (K.cartanEilenberg.flip.d p (p + 1))) q ≫
      (K.cartanEilenbergRowHomologyIso G (p + 1) q).hom =
    (K.cartanEilenbergRowHomologyIso G p q).hom ≫
      G.map ((K.homologyResolution q).cocomplex.d p (p + 1)) := by
  rw [← cancel_epi ((K.cartanEilenbergRow G p).liftCycles (K.cartanEilenbergRowι G p q)
    (q + 1) (CochainComplex.next ℕ q) (K.cartanEilenbergRowι_d G p q) ≫
      (K.cartanEilenbergRow G p).homologyπ q)]
  have h : (K.cartanEilenbergRow G (p + 1)).liftCycles (K.cartanEilenbergRowι G p q ≫
        ((G.mapHomologicalComplex _).map (K.cartanEilenberg.flip.d p (p + 1))).f q) (q + 1)
        (CochainComplex.next ℕ q) (by
          rw [Category.assoc, cartanEilenbergRowι_comp_map_flip_d_f_assoc, cartanEilenbergRowι_d,
            comp_zero]) =
      G.map ((K.cyclesResolution q).cocomplex.d p (p + 1)) ≫
        (K.cartanEilenbergRow G (p + 1)).liftCycles (K.cartanEilenbergRowι G (p + 1) q) (q + 1)
          (CochainComplex.next ℕ q) (K.cartanEilenbergRowι_d G (p + 1) q) := by
    rw [← cancel_mono ((K.cartanEilenbergRow G (p + 1)).iCycles q),
      HomologicalComplex.liftCycles_i, Category.assoc, HomologicalComplex.liftCycles_i,
      cartanEilenbergRowι_comp_map_flip_d_f]
  simp only [Category.assoc, HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc, h,
    liftCycles_homologyπ_cartanEilenbergRowHomologyIso_hom_assoc,
    liftCycles_homologyπ_cartanEilenbergRowHomologyIso_hom]
  rw [← G.map_comp, ← G.map_comp, HomologicalComplex.Hom.comm]

end CochainComplex
