/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Length
public import TauCeti.AlgebraicGeometry.Chow.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.PureRelativeDimension
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.TensorProduct.Quotient
import TauCeti.AlgebraicGeometry.ResidueField
import TauCeti.AlgebraicGeometry.Scheme.LocalDimension
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

The remaining declarations are in the namespace `TauCeti.AlgebraicGeometry.Chow`.

* `maximal_mem_preimage_comp_iff`: generic points of the fibres of `f ≫ g` for flat `f`.
* `height_preimage_singleton_eq`: for `f` of pure relative dimension `n`, a generic point of a
  fibre has dimension `n` inside the fibre.
* `height_asFiber_eq`, `height_asFiber_eq_toNat_trdeg`: as a point of the scheme-theoretic fibre,
  such a generic point `x` has height `n`, which is `trdeg_{κ(f x)} κ_{X_{f x}}(x)`.
* `fiberLength`: the length of the local ring of the fibre, `fiberLength_ne_top`: it is finite at
  generic points of fibres of a locally Noetherian scheme; `fiberLength_comp`: it is
  multiplicative along `f ≫ g` for flat `f`.
* `algebraMap_residueField_fiber`: the residue field of the fibre `X_{f x}` at `x` is `κ(x)` as a
  `κ(f x)`-algebra.
* `trdeg_residueField_lt_aleph0`, `isScalarTower_residueField`: residue fields of schemes locally
  of finite type over `K` have finite transcendence degree, in a tower `K → κ(f x) → κ(x)`.
* `height_eq_height_add`: for `f` of pure relative dimension `n` over a field, a generic point `x`
  of its fibre has dimension `dim (f x) + n`.
* `cycleFlatPullback`: the flat pullback `AlgebraicCycle Y ℤ → AlgebraicCycle X ℤ`, additive;
  `cyclesFlatPullback`: for `f` flat of pure relative dimension `n`, `Z_k(Y) →+ Z_{k+n}(X)`.
* `cycleFlatPullback_comp`, `cyclesFlatPullback_comp`: functoriality `(f ≫ g)^* = f^* ∘ g^*`.

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

/-- A generic point `x` of its fibre `f ⁻¹' {f x}` is a generic point of the scheme-theoretic fibre
`f.fiber (f x)`. -/
theorem asFiber_mem_genericPoints {x : X} (hx : Maximal (· ∈ f ⁻¹' {f x}) x) :
    f.asFiber x ∈ genericPoints (f.fiber (f x)) :=
  TauCeti.mem_genericPoints_iff.mpr fun q hq ↦ by
    have h : f.fiberι _ q ⤳ x := by simpa using hq.map (f.fiberι _).continuous
    have hmem : f.fiberι _ q ∈ f ⁻¹' {f x} := by rw [← f.range_fiberι]; exact ⟨q, rfl⟩
    exact (f.fiberι _).isEmbedding.injective (by simpa using (h.antisymm (hx.2 hmem h)).eq)

/-- If `f` has pure relative dimension `n`, a generic point `x` of its fibre has height `n` as a
point of the scheme-theoretic fibre `f.fiber (f x)`. -/
theorem height_asFiber_eq {n : ℕ} [PureRelativeDimension n f] {x : X}
    (hx : Maximal (· ∈ f ⁻¹' {f x}) x) : Order.height (f.asFiber x) = n := by
  have h := height_eq_topologicalKrullDim_closure_singleton (f.asFiber x)
  rw [isPureDimensional_iff.mp (PureRelativeDimension.isPureDimensional_fiber (d := n) f (f x)) _
    (asFiber_mem_genericPoints f hx)] at h
  exact_mod_cast h

/-- For `f` locally of finite type, the height of a point of the fibre `f.fiber (f x)`, a scheme
locally of finite type over `κ(f x)`, is the transcendence degree of its residue field over
`κ(f x)`. -/
theorem height_asFiber_eq_toNat_trdeg [LocallyOfFiniteType f] (x : X) :
    letI := f.fiberOverSpecResidueField (f x)
    Order.height (f.asFiber x) =
      (Algebra.trdeg (Y.residueField (f x))
        ((f.fiber (f x)).residueField (f.asFiber x))).toNat := by
  let := f.fiberOverSpecResidueField (f x)
  have : LocallyOfFiniteType (f.fiber (f x) ↘ Spec (.of (Y.residueField (f x)))) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd f (Y.fromSpecResidueField (f x))))
  have h := height_eq_topologicalKrullDim_closure_singleton (f.asFiber x)
  rw [topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField
    (Y.residueField (f x))] at h
  exact_mod_cast h

/-- The `κ(f x)`-algebra structure on the residue field of the fibre `f.fiber (f x)` at `x` is
`κ(f x) → κ(x) ≅ κ_{X_{f x}}(x)`, the isomorphism being induced by the inclusion `f.fiberι`. -/
theorem algebraMap_residueField_fiber (x : X) :
    letI := f.fiberOverSpecResidueField (f x)
    CommRingCat.ofHom (algebraMap (Y.residueField (f x))
        ((f.fiber (f x)).residueField (f.asFiber x))) =
      f.residueFieldMap x ≫ (X.residueFieldCongr (f.fiberι_asFiber x)).inv ≫
        (f.fiberι _).residueFieldMap (f.asFiber x) := by
  let := f.fiberOverSpecResidueField (f x)
  -- Both sides are compared after `Spec` and the monomorphism `Y.fromSpecResidueField (f x)`:
  -- each becomes the composite of the fibre square `f.fiber_fac` through `Spec κ_{X_{f x}}(x)`.
  have hs (s : Spec (.of (Y.residueField (f x)))) :
      Spec.map (Scheme.Spec.residueFieldIsoOfField s).inv =
        (Spec (.of (Y.residueField (f x)))).fromSpecResidueField s := by
    simp [Scheme.Spec.residueFieldIsoOfField_inv, Scheme.fromSpecResidueField,
      Spec.fromSpecStalk_eq, ← Spec.map_comp]
    rfl
  have h1 := Scheme.Hom.residueFieldIsoOfField_inv_residueFieldMap
    (f.fiber (f x) ↘ Spec (.of (Y.residueField (f x)))) (f.asFiber x)
  have h2 : CommRingCat.ofHom (algebraMap (Y.residueField (f x))
        ((f.fiber (f x)).residueField (f.asFiber x))) =
      (Scheme.Spec.residueFieldIsoOfField _).inv ≫
        (f.fiber (f x) ↘ Spec (.of (Y.residueField (f x)))).residueFieldMap (f.asFiber x) := by
    rw [h1, Scheme.residueFieldBaseAlgebra_eq_compHom]; rfl
  apply Scheme.eq_of_SpecMap_comp_fromSpecResidueField
  rw [h2, Spec.map_comp_assoc, hs, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]
  change _ ≫ f.fiberToSpecResidueField _ ≫ _ = _
  rw [← Scheme.Hom.fiber_fac]
  simp [Spec.map_comp]

section

variable (K : Type u) [Field K]

/-- On a scheme locally of finite type over a field `K`, every residue field has finite
transcendence degree over `K`: in an affine chart of finite type it is the residue field of a
prime of a finitely generated `K`-algebra, essentially of finite type over `K`. -/
theorem trdeg_residueField_lt_aleph0 {X : Scheme.{u}} [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] (x : X) :
    Algebra.trdeg K (X.residueField x) < Cardinal.aleph0 := by
  obtain ⟨R, g, _, y, φ, hφ, rfl, hR⟩ := (X ↘ Spec (.of K)).exists_isOpenImmersion_finiteType x
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType K R := hR
  have := y.isPrime
  have : Algebra.EssFiniteType K y.asIdeal.ResidueField := .comp K R _
  rw [(g.residueFieldAlgEquivOfIsOpenImmersion φ hφ y).trdeg_eq]
  exact trdeg_lt_aleph0 K _

variable [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))] [f.IsOver (Spec (.of K))]

/-- For `f` a morphism over `Spec K`, the `K`-algebra structures on residue fields form a scalar
tower `K → κ(f x) → κ(x)` along `f.residueFieldMap x`. -/
theorem isScalarTower_residueField (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    IsScalarTower K (Y.residueField (f x)) (X.residueField x) := by
  let := (f.residueFieldMap x).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  ext c
  change X.residue x (Scheme.baseRingToStalk K X x c) =
    f.residueFieldMap x (Y.residue (f x) (Scheme.baseRingToStalk K Y (f x) c))
  rw [Scheme.residue_baseRingToStalk, Scheme.residue_baseRingToStalk,
    Scheme.Modules.baseRingToGlobalSections_apply, Scheme.Modules.baseRingToGlobalSections_apply,
    Scheme.Γevaluation_naturality_apply, ← comp_over f (Spec (.of K))]
  rfl

/-- **Dimension shift for morphisms of pure relative dimension.** Let `f : X ⟶ Y` be a morphism of
schemes locally of finite type over a field `K`, of pure relative dimension `n`. A generic point
`x` of its fibre has dimension `dim (f x) + n`: in the tower `K → κ(f x) → κ(x)`, the residue field
`κ(x)` of the fibre has transcendence degree `n` over `κ(f x)` (Stacks 02JS). -/
theorem height_eq_height_add {n : ℕ} [PureRelativeDimension n f]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [LocallyOfFiniteType (Y ↘ Spec (.of K))] {x : X}
    (hx : Maximal (· ∈ f ⁻¹' {f x}) x) : Order.height x = Order.height (f x) + n := by
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ Y ↘ Spec (.of K)) := by
      rw [comp_over]; infer_instance
    exact locallyOfFiniteType_of_comp f (Y ↘ Spec (.of K))
  let := (f.residueFieldMap x).hom.toAlgebra
  have := isScalarTower_residueField f K x
  let e : X.residueField x ≃+* (f.fiber (f x)).residueField (f.asFiber x) :=
    ((X.residueFieldCongr (f.fiberι_asFiber x)).symm ≪≫
      asIso ((f.fiberι _).residueFieldMap (f.asFiber x))).commRingCatIsoToRingEquiv
  let := f.fiberOverSpecResidueField (f x)
  have hn : (Algebra.trdeg (Y.residueField (f x)) (X.residueField x)).toNat = n := by
    let e' : X.residueField x ≃ₐ[Y.residueField (f x)]
        (f.fiber (f x)).residueField (f.asFiber x) :=
      AlgEquiv.ofRingEquiv (f := e) fun c ↦ by
        have h := congr(($(algebraMap_residueField_fiber f x)).hom c)
        exact h.symm
    rw [e'.trdeg_eq]
    exact_mod_cast (height_asFiber_eq_toNat_trdeg f x).symm.trans (height_asFiber_eq f hx)
  have hX := (height_eq_topologicalKrullDim_closure_singleton x).trans
    (topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField K x)
  have hY := (height_eq_topologicalKrullDim_closure_singleton (f x)).trans
    (topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField K (f x))
  have hsum := trdeg_add_eq K (Y.residueField (f x)) (A := X.residueField x)
  have hfin := trdeg_residueField_lt_aleph0 K x
  rw [← hsum] at hfin
  obtain ⟨h1, h2⟩ := Cardinal.add_lt_aleph0_iff.mp hfin
  have : (Order.height x : WithBot ℕ∞) = (Order.height (f x) + n : ℕ∞) := by
    rw [hX, WithBot.coe_add, hY, ← hsum, Cardinal.toNat_add h1 h2, hn]
    push_cast; rfl
  exact_mod_cast this

end

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

open scoped TensorProduct in
/-- **Multiplicativity of `fiberLength`.** For `f` flat, the fibre length of `f ≫ g` at `x` is the
product of the fibre lengths of `f` at `x` and of `g` at `f x`: `𝒪_{X,x} ⧸ 𝔪_{g (f x)} 𝒪_{X,x}` is
the base change of `𝒪_{Y,f x} ⧸ 𝔪_{g (f x)} 𝒪_{Y,f x}` along the flat local map
`𝒪_{Y,f x} → 𝒪_{X,x}`, which multiplies lengths by `fiberLength f x`
(`IsLocalRing.length_baseChange`). -/
theorem fiberLength_comp [Flat f] {Z : Scheme.{u}} (g : Y ⟶ Z) (x : X) :
    fiberLength (f ≫ g) x = fiberLength f x * fiberLength g (f x) := by
  let := (f.stalkMap x).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  set I := (IsLocalRing.maximalIdeal (Z.presheaf.stalk (g (f x)))).map (g.stalkMap (f x)).hom
  have h : ((f ≫ g).stalkMap x).hom = (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom := by
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  calc fiberLength (f ≫ g) x
      = Module.length (X.presheaf.stalk x)
          (X.presheaf.stalk x ⧸ I.map (algebraMap (Y.presheaf.stalk (f x)) _)) := by
        rw [fiberLength, h]
        simp only [I]
        rw [Ideal.map_map]
        rfl
    _ = Module.length (X.presheaf.stalk x)
          (X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)] (Y.presheaf.stalk (f x) ⧸ I)) :=
        (Algebra.TensorProduct.quotIdealMapEquivTensorQuot _ I).toLinearEquiv.length_eq
    _ = fiberLength f x * fiberLength g (f x) := by
        rw [IsLocalRing.length_baseChange, mul_comm]
        rfl

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

/-- **Functoriality of flat pullback of cycles**: `(f ≫ g)^* = f^* ∘ g^*`. The supports agree by
`maximal_mem_preimage_comp_iff` and the multiplicities by `fiberLength_comp`. -/
theorem cycleFlatPullback_comp [Flat f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {Z : Scheme.{u}} (g : Y ⟶ Z) [Flat g] (α : AlgebraicCycle Z ℤ) :
    cycleFlatPullback (f ≫ g) α = cycleFlatPullback f (cycleFlatPullback g α) := by
  ext x
  rw [cycleFlatPullback_apply, maximal_mem_preimage_comp_iff, fiberLength_comp, ENat.toNat_mul,
    cycleFlatPullback_apply, cycleFlatPullback_apply]
  by_cases hf : Maximal (· ∈ f ⁻¹' {f x}) x
  · by_cases hg : Maximal (· ∈ g ⁻¹' {g (f x)}) (f x)
    · rw [ite_eq_left ⟨hf, hg⟩, ite_eq_left hf, ite_eq_left hg, Nat.cast_mul, mul_assoc]
      rfl
    · rw [ite_eq_right (hg ·.2), ite_eq_left hf, ite_eq_right hg, mul_zero]
  · rw [ite_eq_right (hf ·.1), ite_eq_right hf]

/-- **Flat pullback of `k`-cycles.** For `f : X ⟶ Y` flat of pure relative dimension `n` between
schemes locally of finite type over a field `K`, the flat pullback `cycleFlatPullback f` sends
`k`-cycles to `(k + n)`-cycles (`height_eq_height_add`), giving `f^* : Z_k(Y) →+ Z_{k+n}(X)`. -/
noncomputable def cyclesFlatPullback (K : Type u) [Field K] [X.Over (Spec (.of K))]
    [Y.Over (Spec (.of K))] [f.IsOver (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [IsLocallyNoetherian X] [Flat f] {n : ℕ}
    [PureRelativeDimension n f] (k : ℤ) :
    cyclesOfDimension Y k →+ cyclesOfDimension X (k + n) where
  toFun α := ⟨cycleFlatPullback f α, mem_cyclesOfDimension_iff.mpr fun x hx ↦ by
    classical
    rw [Function.mem_support, cycleFlatPullback_apply] at hx
    split_ifs at hx with hmax
    · obtain ⟨m, hm, rfl⟩ :=
        mem_pointsOfDimension.mp (mem_cyclesOfDimension_iff.mp α.2 (right_ne_zero_of_mul hx))
      exact mem_pointsOfDimension.mpr
        ⟨m + n, by rw [height_eq_height_add f K (n := n) hmax, hm]; rfl, by push_cast; rfl⟩
    · exact absurd rfl hx⟩
  map_zero' := Subtype.ext (cycleFlatPullback_zero f)
  map_add' α β := Subtype.ext (cycleFlatPullback_add f α β)

@[simp]
lemma cyclesFlatPullback_apply (K : Type u) [Field K] [X.Over (Spec (.of K))]
    [Y.Over (Spec (.of K))] [f.IsOver (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [IsLocallyNoetherian X] [Flat f] {n : ℕ}
    [PureRelativeDimension n f] {k : ℤ} (α : cyclesOfDimension Y k) :
    (cyclesFlatPullback f K (n := n) k α : AlgebraicCycle X ℤ) = cycleFlatPullback f α :=
  rfl

/-- **Functoriality of flat pullback of `k`-cycles**: `(f ≫ g)^* = f^* ∘ g^*` from `Z_k(Z)` to
`Z_{k+m+n}(X)`, for `g` of pure relative dimension `m` and `f` of pure relative dimension `n` (the
dimension `m + n` of `f ≫ g` is stated as an instance). -/
lemma cyclesFlatPullback_comp (K : Type u) [Field K] [X.Over (Spec (.of K))]
    [Y.Over (Spec (.of K))] [f.IsOver (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [Flat f] {Z : Scheme.{u}} (g : Y ⟶ Z) [Z.Over (Spec (.of K))] [g.IsOver (Spec (.of K))]
    [LocallyOfFiniteType (Z ↘ Spec (.of K))] [Flat g] {m n : ℕ} [PureRelativeDimension n f]
    [PureRelativeDimension m g] [PureRelativeDimension (m + n) (f ≫ g)] {k : ℤ}
    (α : cyclesOfDimension Z k) :
    (cyclesFlatPullback (f ≫ g) K (n := m + n) k α : AlgebraicCycle X ℤ) =
      cyclesFlatPullback f K (n := n) (k + m) (cyclesFlatPullback g K (n := m) k α) :=
  cycleFlatPullback_comp f g α

end TauCeti.AlgebraicGeometry.Chow
