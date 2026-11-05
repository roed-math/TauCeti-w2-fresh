/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import TauCeti.AlgebraicGeometry.Cohomology.Support
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Flasque
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
import TauCeti.Algebra.Module.Torsion.PrimaryComponent

/-!
# Cohomology with supports of the sheaf associated to a module

Let `R` be a commutative ring, `I` an ideal of `R` and `M` an `R`-module, with associated
quasi-coherent sheaf `M^~` on `Spec R`. This file compares cohomology with supports in the zero
locus `V(I)` with the `I`-power torsion of `M`.

In degree zero, a global section of `M^~` is an element `m ∈ M`, and it is supported in `V(I)`
when it vanishes on the complement `D(g₁) ∪ ⋯ ∪ D(gₙ)` for generators `gᵢ` of `I`, that is, when
a power of every `gᵢ` kills `m`. For finitely generated `I` this says that `m` lies in the
`I`-power torsion `Γ_I(M)` (Mathlib's `Ideal.primaryComponent`), so
`Γ_{V(I)}(Spec R, M^~) ≅ Γ_I(M)` (Stacks, Lemma 51.2.1 (0A6T) in degree zero).

In positive degrees, if `R` is Noetherian and `J` is an injective `R`-module, then `J^~` is
flasque (Hartshorne, Proposition III.3.4, `TauCeti.AlgebraicGeometry.isFlasque_tilde_of_injective`),
so it has no cohomology with supports in positive degrees. Consequently, for a short exact
sequence `0 ⟶ M ⟶ J ⟶ N ⟶ 0` of modules with `J` injective, the connecting maps of cohomology
with supports shift degrees: `H^{n+1}_Z(N^~) ≅ H^{n+2}_Z(M^~)`, and `H^0_Z(N^~)` surjects onto
`H^1_Z(M^~)`. With degree zero, this is the input for comparing cohomology with supports with the
derived functors of `Γ_I` by dimension shifting (Stacks, Lemma 51.2.1 (0A6T)).

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.Modules.zeroLocusCloseds I`: the closed subset `V(I)` of
  `Spec R`;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.toOpen_eq_zero_iff`: an element of `M` vanishes as a
  section of `M^~` over `D(g₁) ∪ ⋯ ∪ D(gₙ)` iff a power of every `gᵢ` kills it;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.mem_sectionsWithSupport_tilde_iff`: for finitely
  generated `I`, a global section of `M^~` is supported in `V(I)` iff the corresponding element of
  `M` lies in `Γ_I(M)`;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.primaryComponentLinearEquivSectionsWithSupport`:
  `Γ_I(M) ≃ₗ[R] Γ_{V(I)}(Spec R, M^~)` for finitely generated `I`;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.tilde_map_smul_id`: multiplication by `r` on `M`
  induces multiplication by the global function `r` on `M^~`;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.subsingleton_cohomologyWithSupport_tilde_succ`:
  `H^{n+1}_Z(Spec R, J^~) = 0` for an injective module `J` over a Noetherian ring and any closed
  `Z`;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportTildeδ`: the connecting map
  `H^n_Z(Spec R, S.X₃^~) ⟶ H^{n+1}_Z(Spec R, S.X₁^~)` of a short exact sequence of modules, and
  `TauCeti.AlgebraicGeometry.Scheme.Modules.exists_cohomologyWithSupportMap_tilde_eq`: exactness
  of the long exact sequence at `H^n_Z(Spec R, S.X₃^~)`;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.bijective_cohomologyWithSupportTildeδ_succ` and
  `TauCeti.AlgebraicGeometry.Scheme.Modules.surjective_cohomologyWithSupportTildeδ_zero`:
  dimension shifting along `0 ⟶ M ⟶ J ⟶ N ⟶ 0` with `J` injective over a Noetherian ring.

## References

* [Stacks, Lemma 51.2.1 (0A6T)](https://stacks.math.columbia.edu/tag/0A6T).
* R. Hartshorne, *Algebraic Geometry*, Chapter III, Proposition 3.4.
-/

public section

open CategoryTheory TopologicalSpace Opposite PrimeSpectrum _root_.AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace Scheme.Modules

variable {R : CommRingCat.{u}} (I : Ideal R) (M : ModuleCat.{u} R)

/-- The zero locus `V(I)` of an ideal `I` of `R`, as a closed subset of `Spec R`. -/
def zeroLocusCloseds : Closeds (Spec R) :=
  ⟨zeroLocus (I : Set R), isClosed_zeroLocus _⟩

@[simp]
lemma coe_zeroLocusCloseds : (zeroLocusCloseds I : Set (Spec R)) = zeroLocus (I : Set R) :=
  (rfl)

/-- The complement of `V(g₁, …, gₙ)` is `D(g₁) ∪ ⋯ ∪ D(gₙ)`. -/
lemma compl_zeroLocusCloseds_span (G : Finset R) :
    (zeroLocusCloseds (Ideal.span (G : Set R))).compl =
      ⨆ g ∈ G, (basicOpen g : (Spec R).Opens) := by
  ext p
  change p ∉ zeroLocus ((Ideal.span (G : Set R) : Ideal R) : Set R) ↔
    p ∈ ⨆ g ∈ G, (basicOpen g : (Spec R).Opens)
  rw [zeroLocus_span]
  change ¬(G : Set R) ⊆ p.asIdeal ↔ _
  rw [Set.not_subset]
  refine ⟨fun ⟨g, hg, hp⟩ ↦ Opens.mem_iSup.2 ⟨g, Opens.mem_iSup.2 ⟨hg, hp⟩⟩, fun hp ↦ ?_⟩
  obtain ⟨g, hp⟩ := Opens.mem_iSup.1 hp
  obtain ⟨hg, hp⟩ := Opens.mem_iSup.1 hp
  exact ⟨g, hg, hp⟩

/-- `M^~` as a presheaf of `R`-modules. Its sections over `D(f)` are the localization `M_f`,
through `tilde.toOpen`. -/
local notation "𝓕" => TopCat.Sheaf.presheaf (modulesSpecToSheaf.obj (tilde M))

/-- Restriction of sections of `M^~` along an inclusion `h : V ≤ U`. -/
local notation "res[" h "]" =>
  Prefunctor.map (CategoryTheory.Functor.toPrefunctor 𝓕) (Quiver.Hom.op (homOfLE h))

variable {M} in
/-- An element `m ∈ M` vanishes as a section of `M^~` over `D(g₁) ∪ ⋯ ∪ D(gₙ)` iff a power of
every `gᵢ` kills it. -/
theorem toOpen_eq_zero_iff (G : Finset R) {U : (Spec R).Opens}
    (hU : U = ⨆ g ∈ G, (basicOpen g : (Spec R).Opens)) (m : M) :
    tilde.toOpen M U m = 0 ↔ ∀ g ∈ G, ∃ n : ℕ, g ^ n • m = 0 := by
  have hD : ∀ g ∈ G, (basicOpen g : (Spec R).Opens) ≤ U := fun g hg ↦
    hU ▸ le_iSup₂ (f := fun g (_ : g ∈ G) ↦ (basicOpen g : (Spec R).Opens)) g hg
  have hres (g : R) (h : (basicOpen g : (Spec R).Opens) ≤ U) :
      res[h] (tilde.toOpen M U m) = tilde.toOpen M (basicOpen g) m :=
    congr($(tilde.toOpen_res M _ _ (homOfLE h)) m)
  refine ⟨fun h g hg ↦ ?_, fun h ↦ ?_⟩
  · have hm : tilde.toOpen M (basicOpen g) m = 0 := by
      rw [← hres g (hD g hg), h, map_zero]
    obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
      (IsLocalizedModule.eq_zero_iff (.powers g) (tilde.toOpen M (basicOpen g)).hom).mp hm
    exact ⟨n, hn⟩
  · refine TopCat.Presheaf.IsSheaf.section_ext (modulesSpecToSheaf.obj (tilde M)).2
      fun p hp ↦ ?_
    rw [unop_op, hU] at hp
    obtain ⟨g, hp⟩ := Opens.mem_iSup.mp hp
    obtain ⟨hg, hp⟩ := Opens.mem_iSup.mp hp
    obtain ⟨n, hn⟩ := h g hg
    refine ⟨basicOpen g, hD g hg, hp, (hres g (hD g hg)).trans ?_⟩
    rw [map_zero]
    exact (IsLocalizedModule.eq_zero_iff (.powers g) (tilde.toOpen M (basicOpen g)).hom).mpr
      ⟨⟨_, n, rfl⟩, hn⟩

variable {I M} in
/-- For a finitely generated ideal `I`, a global section `s` of `M^~` is supported in `V(I)` iff
the corresponding element of `M` lies in the `I`-power torsion `Γ_I(M)`. -/
theorem mem_sectionsWithSupport_tilde_iff (hI : I.FG) (s : Γ(tilde M, ⊤)) :
    s ∈ sectionsWithSupport (zeroLocusCloseds I) (tilde M) ↔
      (tilde.isoTop M).inv s ∈ I.primaryComponent M := by
  obtain ⟨G, rfl⟩ := hI
  obtain ⟨m, rfl⟩ := (ConcreteCategory.bijective_of_isIso (tilde.isoTop M).hom).2 s
  have h := (toOpen_eq_zero_iff G ((top_inf_eq _).trans (compl_zeroLocusCloseds_span G)) m).trans
    (Ideal.mem_primaryComponent_span_iff G).symm
  rw [← congr($(tilde.toOpen_res M _ _ (homOfLE (inf_le_left :
    ⊤ ⊓ (zeroLocusCloseds (Ideal.span (G : Set R))).compl ≤ ⊤))) m)] at h
  refine (mem_sectionsWithSupport_iff _).trans ((Sheaf.mem_supportedSections_iff _).trans ?_)
  rw [Iso.hom_inv_id_apply]
  exact h

variable {I} in
/-- For a finitely generated ideal `I`, the `I`-power torsion `Γ_I(M)` is the module of global
sections of `M^~` supported in `V(I)`, through `tilde.toOpen M ⊤ : M ≅ Γ(Spec R, M^~)`. -/
noncomputable def primaryComponentLinearEquivSectionsWithSupport (hI : I.FG) :
    I.primaryComponent M ≃ₗ[R]
      (sectionsWithSupport (zeroLocusCloseds I) (tilde M)).restrictScalars R :=
  have hbij := ConcreteCategory.bijective_of_isIso (tilde.isoTop M).hom
  have hmem (m : M) : (tilde.isoTop M).hom m ∈ sectionsWithSupport (zeroLocusCloseds I) (tilde M) ↔
      m ∈ I.primaryComponent M :=
    (mem_sectionsWithSupport_tilde_iff hI _).trans (by rw [Iso.hom_inv_id_apply])
  LinearEquiv.ofBijective ((tilde.isoTop M).hom.hom.restrict fun m hm ↦ (hmem m).2 hm)
    ⟨fun x y h ↦ Subtype.ext (hbij.1 congr(Subtype.val $h)), fun s ↦ by
      obtain ⟨m, hm⟩ := hbij.2 s.1
      exact ⟨⟨m, (hmem m).1 (hm ▸ s.2)⟩, Subtype.ext hm⟩⟩

/-- Multiplication by `r : R` on `M` induces on `M^~` the multiplication by the global function
`r`. -/
lemma tilde_map_smul_id (r : R) :
    tilde.map (r • 𝟙 M) = (tilde M).globalSectionsSmul ((Scheme.ΓSpecIso R).inv r) := by
  have key (f g : (tilde.functor R).obj M ⟶ (tilde.functor R).obj M)
      (h : tilde.adjunction.unit.app M ≫ moduleSpecΓFunctor.map f =
        tilde.adjunction.unit.app M ≫ moduleSpecΓFunctor.map g) : f = g :=
    (tilde.adjunction.homEquiv _ _).injective (by rwa [Adjunction.homEquiv_unit,
      Adjunction.homEquiv_unit])
  refine key (tilde.map (r • 𝟙 M)) ((tilde M).globalSectionsSmul _) ?_
  ext m
  refine (ConcreteCategory.congr_hom (tilde.toOpen_map_app (r • 𝟙 M) ⊤) m).trans ?_
  change tilde.toOpen M ⊤ (r • m) =
    ((tilde M).globalSectionsSmul ((Scheme.ΓSpecIso R).inv r)).app ⊤ (tilde.toOpen M ⊤ m)
  rw [map_smul]
  refine (_root_.AlgebraicGeometry.Scheme.Modules.smul_Spec_def (M := tilde M) (U := ⊤) r
    (tilde.toOpen M ⊤ m)).trans ?_
  rw [_root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_app]
  rfl

/-- **Injective modules have no cohomology with supports.** If `R` is Noetherian and `J` is an
injective `R`-module, then `H^{n+1}_Z(Spec R, J^~) = 0` for every closed subset `Z`, because `J^~`
is flasque (Hartshorne, Proposition III.3.4). -/
instance subsingleton_cohomologyWithSupport_tilde_succ [IsNoetherianRing R]
    (Z : Closeds (Spec R)) (J : ModuleCat.{u} R) [Module.Injective R J] (n : ℕ) :
    Subsingleton (cohomologyWithSupport Z (tilde J) (n + 1)) :=
  have : TopCat.Presheaf.IsFlasque ((SheafOfModules.toSheaf _).obj (tilde J)).obj :=
    isFlasque_tilde_of_injective J
  inferInstance

section DimensionShift

variable (Z : Closeds (Spec R)) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)

include hS in
/-- The sequence of abelian sheaves `0 ⟶ S.X₁^~ ⟶ S.X₂^~ ⟶ S.X₃^~ ⟶ 0` associated to a short
exact sequence of `R`-modules is short exact. -/
lemma shortExact_map_tilde_toSheaf :
    (S.map (tilde.functor R ⋙ toSheaf (Spec R))).ShortExact :=
  hS.map_of_exact _

/-- The connecting map `H^n_Z(Spec R, S.X₃^~) ⟶ H^{n+1}_Z(Spec R, S.X₁^~)` of a short exact
sequence of `R`-modules: the Yoneda product with the extension class of the associated short exact
sequence of sheaves. -/
noncomputable def cohomologyWithSupportTildeδ (n : ℕ) :
    cohomologyWithSupport Z (tilde S.X₃) n →+ cohomologyWithSupport Z (tilde S.X₁) (n + 1) :=
  (shortExact_map_tilde_toSheaf hS).extClass.postcomp _ rfl

lemma cohomologyWithSupportTildeδ_apply (n : ℕ) (x : cohomologyWithSupport Z (tilde S.X₃) n) :
    cohomologyWithSupportTildeδ Z hS n x = x.comp (shortExact_map_tilde_toSheaf hS).extClass rfl :=
  (rfl)

/-- Exactness of the long exact sequence of cohomology with supports at `H^n_Z(Spec R, S.X₃^~)`:
a class killed by the connecting map comes from `H^n_Z(Spec R, S.X₂^~)`. -/
lemma exists_cohomologyWithSupportMap_tilde_eq (n : ℕ)
    (y : cohomologyWithSupport Z (tilde S.X₃) n) (hy : cohomologyWithSupportTildeδ Z hS n y = 0) :
    ∃ x, cohomologyWithSupportMap Z (tilde.map S.g) n x = y := by
  obtain ⟨x, hx⟩ := Abelian.Ext.covariant_sequence_exact₃
    (TauCeti.CategoryTheory.relativeFreeYonedaSheaf _ (Z.complInclusion ⊤))
    (shortExact_map_tilde_toSheaf hS) y rfl hy
  exact ⟨x, (cohomologyWithSupportMap_apply _ _ _ _).trans hx⟩

variable [IsNoetherianRing R] [Module.Injective R S.X₂]

/-- **Dimension shifting.** For a short exact sequence `0 ⟶ M ⟶ J ⟶ N ⟶ 0` of modules over a
Noetherian ring with `J` injective, the connecting maps
`H^{n+1}_Z(Spec R, N^~) ⟶ H^{n+2}_Z(Spec R, M^~)` are bijective. -/
theorem bijective_cohomologyWithSupportTildeδ_succ (n : ℕ) :
    Function.Bijective (cohomologyWithSupportTildeδ Z hS (n + 1)) :=
  have : TopCat.Presheaf.IsFlasque (S.map (tilde.functor R ⋙ toSheaf (Spec R))).X₂.obj :=
    isFlasque_tilde_of_injective S.X₂
  Sheaf.relativeH'.extClass_postcomp_bijective_of_isFlasque (shortExact_map_tilde_toSheaf hS)
    (Z.complInclusion ⊤) n

/-- For a short exact sequence `0 ⟶ M ⟶ J ⟶ N ⟶ 0` of modules over a Noetherian ring with `J`
injective, every class in `H^1_Z(Spec R, M^~)` comes from `H^0_Z(Spec R, N^~)`. -/
theorem surjective_cohomologyWithSupportTildeδ_zero :
    Function.Surjective (cohomologyWithSupportTildeδ Z hS 0) := fun x ↦ by
  have hT := shortExact_map_tilde_toSheaf hS
  have : TopCat.Presheaf.IsFlasque (S.map (tilde.functor R ⋙ toSheaf (Spec R))).X₂.obj :=
    isFlasque_tilde_of_injective S.X₂
  exact Abelian.Ext.covariant_sequence_exact₁ (n₁ := 0 + 1)
    (TauCeti.CategoryTheory.relativeFreeYonedaSheaf _ (Z.complInclusion ⊤)) hT x
    (Subsingleton.elim _ _) rfl

end DimensionShift

end Scheme.Modules

end AlgebraicGeometry

end TauCeti
