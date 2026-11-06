/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Length
public import TauCeti.AlgebraicGeometry.Morphisms.PureRelativeDimension
import TauCeti.Topology.KrullDimension.Basic
import TauCeti.Topology.Sober

/-!
# Flat pullback of algebraic cycles

The flat pullback of a prime cycle `[V]`, `V = closure {y}`, along a flat morphism `f : X ⟶ Y`
is the cycle of the closed subscheme `f⁻¹(V)`, a sum over the generic points of `f⁻¹(V)` weighted
by the lengths of their local rings
([Stacks, Section 42.14](https://stacks.math.columbia.edu/tag/02RA)). Since a flat morphism
satisfies going down (`Flat.generalizingMap`), these generic points all lie over `y`: they are
exactly the generic points of the fibre `f⁻¹{y}`, and the local ring of `f⁻¹(V)` at such a point
`x` is the local ring `𝒪_{X,x} ⧸ 𝔪_y 𝒪_{X,x}` of the fibre. Hence the coefficient of `f^*α` at `x`
is `length(𝒪_{X,x} ⧸ 𝔪_{f x} 𝒪_{X,x}) · α(f x)` when `x` is a generic point of its fibre, and
zero otherwise.

## Main definitions and results

* `TauCeti.GeneralizingMap.maximal_mem_preimage_closure_singleton_iff`,
  `Chow.maximal_mem_preimage_closure_singleton_iff`: for a flat morphism (more generally a
  continuous generalizing map of `T0` spaces) the generic points of `f⁻¹(closure {y})` are the
  generic points of `f⁻¹{y}`, for the specialization order (`x ≤ x' ↔ x' ⤳ x`).
* `TauCeti.finite_maximal_mem_inter`: a closed subset of a quasi-sober `T0` space has finitely many
  generic points in a Noetherian open subset.

* `TauCeti.AlgebraicGeometry.isIso_residueFieldMap_of_surjectiveOnStalks`: a morphism surjective
  on stalks (for instance the inclusion of a fibre) induces isomorphisms of residue fields.

The remaining declarations are in the namespace `TauCeti.AlgebraicGeometry.Chow`.

* `maximal_mem_preimage_comp_iff`: generic points of the fibres of `f ≫ g` for flat `f`.
* `height_preimage_singleton_eq`: for `f` of pure relative dimension `n`, a generic point of a
  fibre has dimension `n` inside the fibre.
* `fiberLength`: the length of the local ring of the fibre, `fiberLength_ne_top`: it is finite at
  generic points of fibres of a locally Noetherian scheme.
* `cycleFlatPullback`: the flat pullback `AlgebraicCycle Y ℤ → AlgebraicCycle X ℤ`, additive.

## References

* [Stacks, Section 42.14](https://stacks.math.columbia.edu/tag/02RA)
* Fulton, *Intersection Theory*, §1.7
-/

@[expose] public section

open CategoryTheory Topology TopologicalSpace AlgebraicGeometry

universe u

namespace TauCeti

/-- For a continuous generalizing map `f` of `T0` spaces, the generic points of the preimage of
the closure of `y` are the generic points of the fibre over `y`. Generic points are the maximal
elements for the specialization order `x ≤ x' ↔ x' ⤳ x`. -/
theorem GeneralizingMap.maximal_mem_preimage_closure_singleton_iff {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T0Space X] [T0Space Y] {f : X → Y}
    (hf : GeneralizingMap f) (hcont : Continuous f) {x : X} {y : Y} :
    (letI := specializationPreorder X; Maximal (· ∈ f ⁻¹' closure {y}) x) ↔
      f x = y ∧ (letI := specializationPreorder X; Maximal (· ∈ f ⁻¹' {y}) x) := by
  let := specializationPreorder X
  constructor
  · intro hx
    obtain ⟨x', hx'x, hx'y⟩ := hf (specializes_iff_mem_closure.mpr hx.1)
    have hxx' : x ⤳ x' := hx.2 (show f x' ∈ closure {y} from hx'y ▸ subset_closure rfl) hx'x
    have hxy : f x = y := (hx'x.antisymm hxx').eq ▸ hx'y
    exact ⟨hxy, hx.mono (fun z hz ↦ subset_closure hz) hxy⟩
  · rintro ⟨rfl, hx⟩
    refine ⟨subset_closure rfl, fun x' hx' hxx' ↦ hx.2 ?_ hxx'⟩
    exact ((hxx'.map hcont).antisymm (specializes_iff_mem_closure.mpr hx')).eq

/-- In a quasi-sober `T0` space, a closed set `s` has only finitely many generic points (points
with no proper generalization in `s`) inside an open subset `V` that is a Noetherian space. -/
theorem finite_maximal_mem_inter {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    {s V : Set X} (hs : IsClosed s) (hV : IsOpen V) [NoetherianSpace V] :
    {x | x ∈ V ∧ x ∈ s ∧ ∀ x' ∈ s, x' ⤳ x → x' = x}.Finite := by
  let T : Set V := (↑) ⁻¹' s
  have : QuasiSober V := hV.isOpenEmbedding_subtypeVal.quasiSober
  have : QuasiSober T :=
    (hs.preimage continuous_subtype_val).isClosedEmbedding_subtypeVal.quasiSober
  have hT : (genericPoints T).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  refine (hT.image fun t : T ↦ ((t : V) : X)).subset ?_
  rintro x ⟨hxV, hxs, hx⟩
  refine ⟨⟨⟨x, hxV⟩, hxs⟩, TauCeti.mem_genericPoints_iff.mpr fun t ht ↦ ?_, rfl⟩
  rw [subtype_specializes_iff, subtype_specializes_iff] at ht
  exact Subtype.ext <| Subtype.ext <| hx _ t.2 ht

end TauCeti

namespace TauCeti.AlgebraicGeometry

/-- A morphism surjective on stalks, such as the inclusion `f.fiberι y` of a fibre, induces
isomorphisms of residue fields. -/
instance isIso_residueFieldMap_of_surjectiveOnStalks {X Y : Scheme.{u}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : IsIso (f.residueFieldMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(f.residueFieldMap x).hom.injective, fun a ↦ ?_⟩
  obtain ⟨b, rfl⟩ := X.residue_surjective x a
  obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
  exact ⟨Y.residue (f x) c, by
    rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩

end TauCeti.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Chow

/-- For a flat morphism `f : X ⟶ Y`, the generic points of `f⁻¹(closure {y})` are the generic
points of the fibre `f⁻¹{y}`: by going down, they all lie over `y`. -/
theorem maximal_mem_preimage_closure_singleton_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {x : X} {y : Y} :
    Maximal (· ∈ f ⁻¹' closure {y}) x ↔ f x = y ∧ Maximal (· ∈ f ⁻¹' {y}) x :=
  GeneralizingMap.maximal_mem_preimage_closure_singleton_iff (Flat.generalizingMap f) f.continuous

/-- For a flat morphism `f : X ⟶ Y`, every generic point of `f⁻¹(closure {y})` lies over `y`. -/
theorem apply_eq_of_maximal_mem_preimage_closure_singleton {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] {x : X} {y : Y} (hx : Maximal (· ∈ f ⁻¹' closure {y}) x) : f x = y :=
  ((maximal_mem_preimage_closure_singleton_iff f).mp hx).1

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- For a flat morphism `f : X ⟶ Y` and any `g : Y ⟶ Z`, a point `x` is a generic point of its
fibre under `f ≫ g` exactly when it is a generic point of its fibre under `f` and `f x` is a
generic point of its fibre under `g`. -/
theorem maximal_mem_preimage_comp_iff [Flat f] {Z : Scheme.{u}} (g : Y ⟶ Z) {x : X} :
    Maximal (· ∈ (f ≫ g) ⁻¹' {(f ≫ g) x}) x ↔
      Maximal (· ∈ f ⁻¹' {f x}) x ∧ Maximal (· ∈ g ⁻¹' {g (f x)}) (f x) := by
  simp only [Scheme.Hom.comp_apply]
  constructor
  · intro hx
    refine ⟨hx.mono (fun x' hx' ↦ by simp_all) rfl, rfl, fun y' hy' (hyx : y' ⤳ f x) ↦ ?_⟩
    obtain ⟨x', hx'x, rfl⟩ := Flat.generalizingMap f hyx
    exact (hx.2 hy' hx'x).map f.continuous
  · rintro ⟨hxf, hxg⟩
    refine ⟨rfl, fun x' hx' (hx'x : x' ⤳ x) ↦ hxf.2 ?_ hx'x⟩
    exact ((hx'x.map f.continuous).antisymm (hxg.2 hx' (hx'x.map f.continuous))).eq

/-- If `f` has pure relative dimension `n`, a generic point `x` of its fibre has dimension `n`
inside the fibre `f ⁻¹' {f x}`, for the specialization order induced from `X`: its closure there is
an irreducible component of the fibre. -/
theorem height_preimage_singleton_eq {n : ℕ} [PureRelativeDimension n f] {x : X}
    (hx : Maximal (· ∈ f ⁻¹' {f x}) x) : Order.height (⟨x, rfl⟩ : f ⁻¹' {f x}) = n := by
  have : QuasiSober (f ⁻¹' {f x}) := (f.fiberHomeo (f x)).symm.isClosedEmbedding.quasiSober
  have hgen : (⟨x, rfl⟩ : f ⁻¹' {f x}) ∈ genericPoints (f ⁻¹' {f x}) :=
    TauCeti.mem_genericPoints_iff.mpr fun x' hx' ↦ by
      have h : (x' : X) ⤳ x := (subtype_specializes_iff _ _).mp hx'
      exact Subtype.ext (h.antisymm (hx.2 x'.2 h)).eq
  have h := height_eq_topologicalKrullDim_closure_singleton (⟨x, rfl⟩ : f ⁻¹' {f x})
  rw [isPureDimensional_iff.mp (PureRelativeDimension.isPureDimensional_preimage (d := n) (f := f)
    (f x)) _ hgen] at h
  -- The specialization order of the fibre is the order induced from `X`.
  have hord : (inferInstance : Preorder (f ⁻¹' {f x})) = specializationPreorder _ :=
    Preorder.ext fun a b ↦ (subtype_specializes_iff b a).symm
  have h' : @Order.height _ (specializationPreorder _) (⟨x, rfl⟩ : f ⁻¹' {f x}) = n := by
    exact_mod_cast h
  rwa [← hord] at h'

/-- The multiplicity of the flat pullback at a point `x`: the length of the local ring
`𝒪_{X,x} ⧸ 𝔪_{f x} 𝒪_{X,x}` of the fibre `X_{f x}` at `x`. At a generic point `x` of `f⁻¹(V)`,
`V = closure {f x}` with its reduced structure, this is the length of `𝒪_{f⁻¹(V),x}`, the
coefficient of `[x]` in the cycle `[f⁻¹(V)]`. -/
noncomputable def fiberLength (x : X) : ℕ∞ :=
  Module.length (X.presheaf.stalk x)
    (X.presheaf.stalk x ⧸ (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map
      (f.stalkMap x).hom)

/-- At a generic point `x` of its fibre, a point of a locally Noetherian scheme has finite
`fiberLength`. Indeed a prime `𝔭` of `𝒪_{X,x}` containing `𝔪_{f x} 𝒪_{X,x}` is a generalization of
`x` lying over `f x`, hence is `x` itself; so `𝒪_{X,x} ⧸ 𝔪_{f x} 𝒪_{X,x}` is a Noetherian ring of
dimension zero, hence Artinian. -/
theorem fiberLength_ne_top [IsLocallyNoetherian X] {x : X}
    (hx : Maximal (· ∈ f ⁻¹' {f x}) x) : fiberLength f x ≠ ⊤ := by
  set I := (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom
  have hmin : ∀ J ∈ I.minimalPrimes, J.IsMaximal := by
    intro J hJ
    let p : Spec (X.presheaf.stalk x) := ⟨J, hJ.1.1⟩
    have hspec : X.fromSpecStalk x p ⤳ x := by
      have : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have hcomap : Spec.map (f.stalkMap x) p = IsLocalRing.closedPoint _ := by
      rw [Spec.map_apply]
      refine PrimeSpectrum.ext ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le
        (PrimeSpectrum.comap _ p).isPrime.ne_top (Ideal.map_le_iff_le_comap.mp hJ.1.2)).symm
    have hf : f (X.fromSpecStalk x p) = f x := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
        Scheme.Hom.comp_apply, hcomap, Scheme.fromSpecStalk_closedPoint]
    have hxx : X.fromSpecStalk x p = x := (hspec.antisymm (hx.2 hf hspec)).eq
    have hp : p = IsLocalRing.closedPoint _ :=
      (X.fromSpecStalk x).isEmbedding.injective (hxx.trans Scheme.fromSpecStalk_closedPoint.symm)
    change p.asIdeal.IsMaximal
    rw [hp]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have : IsArtinianRing (X.presheaf.stalk x ⧸ I) :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr
      ⟨inferInstance, Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr hmin⟩
  have : IsArtinian (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ I) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  exact Module.length_ne_top

open scoped Classical in
/-- The flat pullback of an algebraic cycle along a flat morphism `f : X ⟶ Y` to a locally
Noetherian scheme: the coefficient at a generic point `x` of its fibre is the coefficient of `α`
at `f x` times the length `fiberLength f x` of the local ring of the fibre, and the other
coefficients vanish. On a prime cycle `[V]` this is the cycle `[f⁻¹(V)]`, since the generic
points of `f⁻¹(V)` are the generic points of the fibre over the generic point of `V`
(`maximal_mem_preimage_closure_singleton_iff`).

Its support is locally finite: a Noetherian affine open `U` of `X` has quasi-compact image, which
meets the support of `α` in finitely many points, and over each of them `U` contains only
finitely many generic points of the fibre. -/
noncomputable def cycleFlatPullback [Flat f] [IsLocallyNoetherian X] (α : AlgebraicCycle Y ℤ) :
    AlgebraicCycle X ℤ where
  toFun x := if Maximal (· ∈ f ⁻¹' {f x}) x then (fiberLength f x).toNat * α (f x) else 0
  supportWithinDomain' _ _ := Set.mem_univ _
  supportLocallyFiniteWithinDomain' x _ := by
    obtain ⟨V, hV, hxV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
    have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have : NoetherianSpace (V : Set X) := noetherianSpace_of_isAffineOpen V hV
    have hfin := α.locallyFiniteSupport.finite_inter_support_of_isCompact
      (hV.isCompact.image f.continuous)
    refine ⟨V, V.isOpen.mem_nhds hxV, (hfin.biUnion fun y _ ↦
      finite_maximal_mem_inter (s := f ⁻¹' closure {y}) (isClosed_closure.preimage f.continuous)
        V.isOpen).subset ?_⟩
    rintro z ⟨hzV, hz⟩
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hz
    obtain ⟨hzmax, hzα⟩ := hz
    have hzmax' := (maximal_mem_preimage_closure_singleton_iff f).mpr ⟨rfl, hzmax⟩
    refine Set.mem_biUnion (x := f z) ⟨⟨z, hzV, rfl⟩, right_ne_zero_of_mul hzα⟩
      ⟨hzV, hzmax'.1, fun z' hz' hz'z ↦ (hz'z.antisymm (hzmax'.2 hz' hz'z)).eq⟩

open scoped Classical in
lemma cycleFlatPullback_apply [Flat f] [IsLocallyNoetherian X] (α : AlgebraicCycle Y ℤ) (x : X) :
    cycleFlatPullback f α x =
      if Maximal (· ∈ f ⁻¹' {f x}) x then (fiberLength f x).toNat * α (f x) else 0 :=
  rfl

@[simp]
lemma cycleFlatPullback_zero [Flat f] [IsLocallyNoetherian X] : cycleFlatPullback f 0 = 0 := by
  ext x
  simp [cycleFlatPullback_apply]

@[simp]
lemma cycleFlatPullback_add [Flat f] [IsLocallyNoetherian X] (α β : AlgebraicCycle Y ℤ) :
    cycleFlatPullback f (α + β) = cycleFlatPullback f α + cycleFlatPullback f β := by
  ext x
  simp only [cycleFlatPullback_apply, Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  split_ifs <;> simp [mul_add]

end TauCeti.AlgebraicGeometry.Chow
