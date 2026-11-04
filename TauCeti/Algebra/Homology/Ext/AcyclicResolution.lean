/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Computing `Ext` from an acyclic resolution

Let `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` be a resolution of an object `F` of an abelian category, and let `P` be
an object such that `Extᵏ⁺¹(P, Kʲ) = 0` for all `j` and `k`. Then the complex of abelian groups
`Hom(P, K)` computes `Ext(P, F)`: `Extⁿ(P, F)` is the cohomology of `Hom(P, K)` in degree `n`, for
every `n` (`TauCeti.CategoryTheory.extAddEquivHomologyOfResolution`). The statement is made for
any additive functor `G : C ⥤ Ab` corepresented by `P` in place of `Hom(P, -)`. For the functor of
sections over an object `V` of a site, corepresented by the free abelian sheaf on `V`, `Ext(P, -)`
is the sheaf cohomology `H(V, -)`, and this is the computation of sheaf cohomology by acyclic
resolutions (Hartshorne, Proposition III.1.2A). For `K` an injective resolution and
`G = Hom(P, -)` it is Mathlib's `CategoryTheory.InjectiveResolution.extAddEquivCohomologyClass`.

The proof is the classical dimension shift. Write `Zʲ` for the cycles of `K` in degree `j`. The
resolution splits into short exact sequences `0 ⟶ F ⟶ K⁰ ⟶ Z¹ ⟶ 0` and `0 ⟶ Zʲ ⟶ Kʲ ⟶ Zʲ⁺¹ ⟶ 0`.

* For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `Extᵐ(P, X₂) = Extᵐ⁺¹(P, X₂) = 0`, the
  connecting map `Extᵐ(P, X₃) ⟶ Extᵐ⁺¹(P, X₁)` is bijective
  (`TauCeti.CategoryTheory.extClassPostcompAddEquiv`). This gives
  `Extⁿ⁺¹(P, F) ≅ Extⁿ(P, Z¹) ≅ ⋯ ≅ Ext¹(P, Zⁿ)`.
* If `Ext¹(P, X₂) = 0`, then `Ext¹(P, X₁)` is the cokernel of `Hom(P, X₂) ⟶ Hom(P, X₃)`
  (`TauCeti.CategoryTheory.surjective_extClass_postcomp_mk₀`,
  `TauCeti.CategoryTheory.extClass_postcomp_mk₀_eq_zero_iff`). For the sequence
  `0 ⟶ Zⁿ ⟶ Kⁿ ⟶ Zⁿ⁺¹ ⟶ 0` this cokernel is the cohomology of `G(K)` in degree `n + 1`, as
  the corepresentable functor `G` preserves kernels
  (`TauCeti.CategoryTheory.surjective_homologyClassOfCycles`,
  `TauCeti.CategoryTheory.homologyClassOfCycles_eq_zero_iff`).

In degree `0`, `Ext⁰(P, F) = Hom(P, F) ≅ G(F)` is the kernel of `G(K⁰) ⟶ G(K¹)`, again because
`G` preserves kernels.

## Main definitions

* `TauCeti.CategoryTheory.extAddEquivHomologyOfResolution`: the additive equivalence
  `Extⁿ(P, F) ≃+ Hⁿ(G(K))` for a resolution `K` of `F` by objects without higher `Ext` from `P`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.1.2A.
-/

public section

open CategoryTheory Limits Opposite Abelian

universe t w v u

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] (P : C)

section ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact)

include hS in
/-- The connecting map `Extᵐ(P, X₃) ⟶ Extᵐ⁺¹(P, X₁)` of a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is bijective when `Extᵐ(P, X₂)` and `Extᵐ⁺¹(P, X₂)` vanish. -/
theorem bijective_extClass_postcomp (m : ℕ) (h₀ : Subsingleton (Ext P S.X₂ m))
    (h₁ : Subsingleton (Ext P S.X₂ (m + 1))) :
    Function.Bijective (hS.extClass.postcomp P (rfl : m + 1 = m + 1)) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨x₂, rfl⟩ := Ext.covariant_sequence_exact₃ P hS x rfl hx
    rw [Subsingleton.elim x₂ 0, Ext.zero_comp]
  · exact Ext.covariant_sequence_exact₁ P hS y (Subsingleton.elim _ _) rfl

/-- The connecting map `Extᵐ(P, X₃) ≃+ Extᵐ⁺¹(P, X₁)` of a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `Extᵐ(P, X₂) = Extᵐ⁺¹(P, X₂) = 0`. -/
noncomputable def extClassPostcompAddEquiv (m : ℕ) (h₀ : Subsingleton (Ext P S.X₂ m))
    (h₁ : Subsingleton (Ext P S.X₂ (m + 1))) : Ext P S.X₃ m ≃+ Ext P S.X₁ (m + 1) :=
  AddEquiv.ofBijective _ (bijective_extClass_postcomp P hS m h₀ h₁)

@[simp]
lemma extClassPostcompAddEquiv_apply (m : ℕ) (h₀ : Subsingleton (Ext P S.X₂ m))
    (h₁ : Subsingleton (Ext P S.X₂ (m + 1))) (x : Ext P S.X₃ m) :
    extClassPostcompAddEquiv P hS m h₀ h₁ x = x.comp hS.extClass rfl :=
  (rfl)

include hS in
/-- For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, the class in `Ext¹(P, X₁)` of a morphism
`P ⟶ X₃` vanishes exactly when the morphism lifts to `X₂`. -/
theorem extClass_postcomp_mk₀_eq_zero_iff (φ : P ⟶ S.X₃) :
    (Ext.mk₀ φ).comp hS.extClass (zero_add 1) = 0 ↔ ∃ ψ : P ⟶ S.X₂, ψ ≫ S.g = φ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ P hS (Ext.mk₀ φ) (zero_add 1) h
    refine ⟨Ext.addEquiv₀ x₂, (Ext.mk₀_bijective _ _).1 ?_⟩
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply, hx₂]
  · rintro ⟨ψ, rfl⟩
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

include hS in
/-- For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `Ext¹(P, X₂) = 0`, every class in
`Ext¹(P, X₁)` is the class of a morphism `P ⟶ X₃`. -/
theorem surjective_extClass_postcomp_mk₀ (h : Subsingleton (Ext P S.X₂ 1)) :
    Function.Surjective fun φ : P ⟶ S.X₃ ↦ (Ext.mk₀ φ).comp hS.extClass (zero_add 1) := by
  intro y
  obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ P hS y (Subsingleton.elim _ _) (zero_add 1)
  exact ⟨Ext.addEquiv₀ x₃, by dsimp only; rw [Ext.mk₀_addEquiv₀_apply]⟩

end ShortExact

section Resolution

/-! ### Resolutions

In this section `G : C ⥤ Ab` is an additive functor corepresented by `P`, for instance `Hom(P, -)`,
or the sections over `V` of abelian sheaves, corepresented by the free abelian sheaf on `V`. -/

variable {P} (G : C ⥤ AddCommGrpCat.{t}) [G.Additive]
  (R : (G ⋙ forget AddCommGrpCat).CorepresentableBy P) {K : CochainComplex C ℕ}

omit [Abelian C] [HasExt.{w} C] [G.Additive] in
private lemma homEquiv_comp {X Y : C} (f : P ⟶ X) (g : X ⟶ Y) :
    R.homEquiv (f ≫ g) = G.map g (R.homEquiv f) :=
  R.homEquiv_comp g f

omit [HasExt.{w} C] in
private lemma homEquiv_add {X : C} (f f' : P ⟶ X) :
    R.homEquiv (f + f') = R.homEquiv f + R.homEquiv f' := by
  rw [R.homEquiv_eq, R.homEquiv_eq f, R.homEquiv_eq f']
  exact congrArg (fun g : G.obj P ⟶ G.obj X ↦ g (R.homEquiv (𝟙 P))) (G.map_add (f := f) (g := f'))

/-- The additive equivalence `(P ⟶ X) ≃+ G(X)` of a corepresentation of `G` by `P`. -/
private noncomputable def homAddEquiv (X : C) : (P ⟶ X) ≃+ G.obj X :=
  { R.homEquiv with map_add' := homEquiv_add G R }

omit [Abelian C] [HasExt.{w} C] [G.Additive] in
include R in
private lemma map_injective {X Y : C} (f : X ⟶ Y) [Mono f] : Function.Injective (G.map f) := by
  intro x y h
  rw [← Equiv.apply_symm_apply R.homEquiv x, ← Equiv.apply_symm_apply R.homEquiv y,
    ← homEquiv_comp, ← homEquiv_comp] at h
  rw [← Equiv.apply_symm_apply R.homEquiv x, ← Equiv.apply_symm_apply R.homEquiv y,
    (cancel_mono f).1 (R.homEquiv.injective h)]

/-- The class in `Hᵏ⁺¹(G(K))` of an element of `G(Zᵏ⁺¹(K))`, for the cycles `Zᵏ⁺¹(K)` of `K`. -/
noncomputable def homologyClassOfCycles (k : ℕ) :
    G.obj (K.cycles (k + 1)) →+ ((G.mapHomologicalComplex _).obj K).homology (k + 1) :=
  (HomologicalComplex.liftCycles ((G.mapHomologicalComplex _).obj K) (G.map (K.iCycles (k + 1)))
    (k + 2) (by simp) (by simp [← Functor.map_comp]) ≫
      HomologicalComplex.homologyπ ((G.mapHomologicalComplex _).obj K) (k + 1)).hom

omit [HasExt.{w} C] in
private lemma iCycles_liftCycles_apply {X : C} {i : ℕ} (j : ℕ) (f : X ⟶ K.X i) (hj hf)
    (x : G.obj X) :
    ((G.mapHomologicalComplex _).obj K).iCycles i
      (HomologicalComplex.liftCycles ((G.mapHomologicalComplex _).obj K) (G.map f) j hj hf x) =
        G.map f x :=
  ConcreteCategory.congr_hom (HomologicalComplex.liftCycles_i _ _ _ hj hf) x

omit [HasExt.{w} C] in
private lemma iCycles_toCycles_apply (k : ℕ) (y : G.obj (K.X k)) :
    ((G.mapHomologicalComplex _).obj K).iCycles (k + 1)
      (((G.mapHomologicalComplex _).obj K).toCycles k (k + 1) y) = G.map (K.d k (k + 1)) y :=
  ConcreteCategory.congr_hom (((G.mapHomologicalComplex _).obj K).toCycles_i k (k + 1)) y

omit [HasExt.{w} C] in
include R in
/-- Every cycle of `G(K)` in degree `i` comes from `G(Zⁱ(K))`: `G` preserves kernels, being
corepresentable. -/
private lemma exists_liftCycles_eq {i : ℕ} (j : ℕ) (hj : (ComplexShape.up ℕ).next i = j)
    (c : ((G.mapHomologicalComplex _).obj K).cycles i) :
    ∃ x : G.obj (K.cycles i), HomologicalComplex.liftCycles ((G.mapHomologicalComplex _).obj K)
      (G.map (K.iCycles i)) j hj (by simp [← Functor.map_comp]) x = c := by
  -- the morphism `P ⟶ Kⁱ` corresponding to `c`
  obtain ⟨φ, hφ⟩ : ∃ φ : P ⟶ K.X i,
      R.homEquiv φ = ((G.mapHomologicalComplex _).obj K).iCycles i c :=
    ⟨_, Equiv.apply_symm_apply R.homEquiv _⟩
  have hc : φ ≫ K.d i j = 0 := by
    apply R.homEquiv.injective
    rw [homEquiv_comp, hφ, show R.homEquiv (0 : P ⟶ K.X j) = 0 from (homAddEquiv G R _).map_zero]
    exact ConcreteCategory.congr_hom (HomologicalComplex.iCycles_d _ i j) c
  refine ⟨R.homEquiv (K.liftCycles φ j hj hc), (AddCommGrpCat.mono_iff_injective
    (HomologicalComplex.iCycles ((G.mapHomologicalComplex _).obj K) i)).1 inferInstance ?_⟩
  rw [iCycles_liftCycles_apply, ← homEquiv_comp, HomologicalComplex.liftCycles_i, hφ]

omit [HasExt.{w} C] in
include R in
/-- Every class in `Hᵏ⁺¹(G(K))` is the class of an element of `G(Zᵏ⁺¹(K))`. -/
theorem surjective_homologyClassOfCycles (k : ℕ) :
    Function.Surjective (homologyClassOfCycles G (K := K) k) := by
  intro y
  obtain ⟨c, rfl⟩ := (AddCommGrpCat.epi_iff_surjective
    (HomologicalComplex.homologyπ ((G.mapHomologicalComplex _).obj K) (k + 1))).1 inferInstance y
  obtain ⟨x, rfl⟩ := exists_liftCycles_eq G R (k + 2) (by simp) c
  exact ⟨x, rfl⟩

omit [HasExt.{w} C] in
include R in
/-- The class in `Hᵏ⁺¹(G(K))` of an element of `G(Zᵏ⁺¹(K))` vanishes exactly when the element
comes from `G(Kᵏ)` through the differential `Kᵏ ⟶ Zᵏ⁺¹(K)`. -/
theorem homologyClassOfCycles_eq_zero_iff (k : ℕ) (x : G.obj (K.cycles (k + 1))) :
    homologyClassOfCycles G k x = 0 ↔ ∃ y : G.obj (K.X k), G.map (K.toCycles k (k + 1)) y = x := by
  have hex := ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk _ _
    (((G.mapHomologicalComplex _).obj K).toCycles_comp_homologyπ k (k + 1)))
      (((G.mapHomologicalComplex _).obj K).homologyIsCokernel k (k + 1) (by simp))
  have hmono := (AddCommGrpCat.mono_iff_injective
    (((G.mapHomologicalComplex _).obj K).iCycles (k + 1))).1 inferInstance
  -- both sides of `G(Zᵏ⁺¹) ⟶ G(Kᵏ⁺¹)` agree on the image of `y ∈ G(Kᵏ)`
  have key (y : G.obj (K.X k)) : HomologicalComplex.liftCycles ((G.mapHomologicalComplex _).obj K)
      (G.map (K.iCycles (k + 1))) (k + 2) (by simp) (by simp [← Functor.map_comp])
        (G.map (K.toCycles k (k + 1)) y) =
          ((G.mapHomologicalComplex _).obj K).toCycles k (k + 1) y := by
    apply hmono
    rw [iCycles_liftCycles_apply, iCycles_toCycles_apply, ← K.toCycles_i k (k + 1), G.map_comp]
    rfl
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).1 hex _ h
    refine ⟨y, map_injective G R (K.iCycles (k + 1)) ?_⟩
    rw [← iCycles_liftCycles_apply G (k + 2) _ (by simp) (by simp [← Functor.map_comp]),
      ← iCycles_liftCycles_apply G (k + 2) _ (by simp) (by simp [← Functor.map_comp]), key]
    exact congrArg _ hy
  · rintro ⟨y, rfl⟩
    exact (congrArg (HomologicalComplex.homologyπ ((G.mapHomologicalComplex _).obj K) (k + 1))
      (key y)).trans (ConcreteCategory.congr_hom
        (((G.mapHomologicalComplex _).obj K).toCycles_comp_homologyπ k (k + 1)) y)

/-- For a short exact sequence `0 ⟶ X ⟶ Kᵏ ⟶ Zᵏ⁺¹(K) ⟶ 0` whose second map is the differential and
with `Ext¹(P, Kᵏ) = 0`, `Ext¹(P, X)` is the cohomology of `G(K)` in degree `k + 1`. -/
noncomputable def extOneAddEquivHomology (k : ℕ) {X : C} (f : X ⟶ K.X k)
    (w : f ≫ K.toCycles k (k + 1) = 0) (hS : (ShortComplex.mk f _ w).ShortExact)
    (h : Subsingleton (Ext P (K.X k) 1)) :
    Ext P X 1 ≃+ ((G.mapHomologicalComplex _).obj K).homology (k + 1) :=
  let f₁ : G.obj (K.cycles (k + 1)) →+ Ext P X 1 :=
    (hS.extClass.postcomp P (zero_add 1)).comp
      ((homAddEquiv G R _).symm.trans Ext.addEquiv₀.symm).toAddMonoidHom
  have hf₁ : Function.Surjective f₁ :=
    ((surjective_extClass_postcomp_mk₀ P hS h).comp (homAddEquiv G R _).symm.surjective :)
  have hker : f₁.ker = (homologyClassOfCycles G (K := K) k).ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, homologyClassOfCycles_eq_zero_iff G R]
    refine (extClass_postcomp_mk₀_eq_zero_iff P hS _).trans
      ⟨fun ⟨ψ, hψ⟩ ↦ ⟨R.homEquiv ψ, ?_⟩, fun ⟨y, hy⟩ ↦ ⟨R.homEquiv.symm y, ?_⟩⟩
    · rw [← homEquiv_comp]
      exact (Equiv.eq_symm_apply R.homEquiv).1 hψ
    · apply R.homEquiv.injective
      rw [homEquiv_comp, Equiv.apply_symm_apply]
      exact hy.trans (Equiv.apply_symm_apply R.homEquiv x).symm
  (QuotientAddGroup.quotientKerEquivOfSurjective f₁ hf₁).symm.trans <|
    (QuotientAddGroup.quotientAddEquivOfEq hker).trans <|
      QuotientAddGroup.quotientKerEquivOfSurjective _ (surjective_homologyClassOfCycles G R k)

omit [HasExt.{w} C] in
private lemma shortExact_cycles (hK : ∀ j, K.ExactAt (j + 1)) (j : ℕ) :
    (ShortComplex.mk (K.iCycles j) (K.toCycles j (j + 1))
      (K.iCycles_toCycles j (j + 1))).ShortExact :=
  K.cyclesShortComplex_def j (j + 1) ▸ K.cyclesShortComplex_shortExact j (j + 1) rfl (hK j)

/-- Dimension shifting along the cycles of `K`: `Extⁿ⁺¹(P, Zʲ) ≃+ Ext¹(P, Zᵏ)` for `k = j + n`. -/
private noncomputable def extCyclesAddEquiv (hK : ∀ j, K.ExactAt (j + 1))
    (hKP : ∀ j k, Subsingleton (Ext P (K.X j) (k + 1))) :
    (n j k : ℕ) → j + n = k → (Ext P (K.cycles j) (n + 1) ≃+ Ext P (K.cycles k) 1)
  | 0, j, k, h => by subst h; exact AddEquiv.refl _
  | n + 1, j, k, h =>
    (extClassPostcompAddEquiv P (shortExact_cycles hK j) (n + 1) (hKP j n)
      (hKP j (n + 1))).symm.trans (extCyclesAddEquiv hK hKP n (j + 1) k (by omega))

variable {F : C} (ι : F ⟶ K.X 0) [Mono ι] (hι : ι ≫ K.d 0 1 = 0)
  (hι' : (ShortComplex.mk ι (K.d 0 1) hι).Exact)

omit [HasExt.{w} C] in
include R hι' in
/-- For a resolution `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯`, `G(F)` is the group of cycles of `G(K)` in
degree `0`. -/
private lemma bijective_liftCycles_zero :
    Function.Bijective (HomologicalComplex.liftCycles ((G.mapHomologicalComplex _).obj K)
      (G.map ι) 1 (by simp) (by simp [← Functor.map_comp, hι])).hom := by
  refine ⟨fun x x' h ↦ map_injective G R ι ?_, fun c ↦ ?_⟩
  · rw [← iCycles_liftCycles_apply G 1 ι (by simp) (by simp [← Functor.map_comp, hι]),
      ← iCycles_liftCycles_apply G 1 ι (by simp) (by simp [← Functor.map_comp, hι])]
    exact congrArg _ h
  · obtain ⟨x, rfl⟩ := exists_liftCycles_eq G R 1 (by simp) c
    obtain ⟨φ, rfl⟩ := R.homEquiv.surjective x
    refine ⟨R.homEquiv (hι'.lift (φ ≫ K.iCycles 0) (by simp)), (AddCommGrpCat.mono_iff_injective
      (HomologicalComplex.iCycles ((G.mapHomologicalComplex _).obj K) 0)).1 inferInstance ?_⟩
    rw [iCycles_liftCycles_apply, iCycles_liftCycles_apply, ← homEquiv_comp, ← homEquiv_comp]
    exact congrArg _ (hι'.lift_f _ _)

/-- **`Ext` from an acyclic resolution.** Let `G : C ⥤ Ab` be an additive functor corepresented by
`P`, and let `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` be a resolution of `F` with `Extᵏ⁺¹(P, Kʲ) = 0` for all `j`
and `k`. Then `Extⁿ(P, F)` is the cohomology of the complex `G(K)` in degree `n`. -/
noncomputable def extAddEquivHomologyOfResolution (hK : ∀ j, K.ExactAt (j + 1))
    (hKP : ∀ j k, Subsingleton (Ext P (K.X j) (k + 1))) :
    (n : ℕ) → Ext P F n ≃+ ((G.mapHomologicalComplex _).obj K).homology n
  | 0 => Ext.addEquiv₀.trans <| (homAddEquiv G R F).trans <|
      (AddEquiv.ofBijective _ (bijective_liftCycles_zero G R ι hι hι')).trans
        (CochainComplex.isoHomologyπ₀ ((G.mapHomologicalComplex _).obj K)).addCommGroupIsoToAddEquiv
  | 1 => extOneAddEquivHomology G R 0 ι _ (K.shortExact_toCycles ι hι hι' (by simp) (hK 0))
      (hKP 0 0)
  | n + 2 =>
    (extClassPostcompAddEquiv P (K.shortExact_toCycles ι hι hι' (by simp) (hK 0)) (n + 1)
      (hKP 0 n) (hKP 0 (n + 1))).symm.trans <|
      (extCyclesAddEquiv hK hKP n 1 (n + 1) (by omega)).trans <|
        extOneAddEquivHomology G R (n + 1) (K.iCycles (n + 1)) (K.iCycles_toCycles _ _)
          (shortExact_cycles hK (n + 1)) (hKP (n + 1) 0)

end Resolution

end TauCeti.CategoryTheory
