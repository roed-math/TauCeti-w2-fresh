/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Invariants

/-!
# Inflation on the explicit low-degree complex, and the inflation-restriction sequence

Inflation is the compatible pair consisting of the quotient homomorphism `G → G ⧸ N` for a normal
subgroup `N` and the inclusion `M ^ N ↪ M` of coefficients, which is equivariant along that
homomorphism because `M ^ N` carries the `G ⧸ N`-action of
`TauCeti.distribMulActionQuotientFixedPointsAddSubgroup`. This file specialises the compatible-pair
pullback of `TauCeti/RepresentationTheory/Homological/ContCohomology/ExplicitFunctoriality.lean` to
that pair in degrees `1` and `2`, and proves the three-term exact sequence

```
0 → H¹(G ⧸ N, M ^ N) → H¹(G, M) → H¹(N, M)
```

on the explicit model. It holds over an arbitrary topological group: neither profiniteness nor a
continuous section of `G → G ⧸ N` is used, only the cochain argument.

The heart of the exactness statement is `TauCeti.ContCohomology.descendZ1`: a continuous
`1`-cocycle of `G` that *vanishes* on `N` is automatically constant on the left cosets of `N` and
takes its values in `M ^ N`, so it is the inflation of a continuous `1`-cocycle of `G ⧸ N` on the
nose, with no coboundary subtracted. Exactness at `H¹(G, M)` then only has to subtract the
coboundary that makes the restriction vanish.

In degree `2` inflation is recorded together with the vanishing `res ∘ infl = 0`; exactness of the
five-term sequence at the two remaining nodes needs the transgression and is not proved here.

## Main definitions

* `TauCeti.ContCohomology.inflCocycles1` and `TauCeti.ContCohomology.inflCocycles2`: inflation on
  continuous cocycles, `z ↦ (g ↦ z g)`.
* `TauCeti.ContCohomology.explicitInfl1` and `TauCeti.ContCohomology.explicitInfl2`: inflation
  `Hⁱ(G ⧸ N, M ^ N) → Hⁱ(G, M)` on the explicit model, for `i = 1, 2`.
* `TauCeti.ContCohomology.descendZ1`: the descent of a continuous `1`-cocycle vanishing on `N`.

## Main results

* `TauCeti.ContCohomology.explicitRes1_explicitInfl1` and
  `TauCeti.ContCohomology.explicitRes2_explicitInfl2`: restricting an inflated class to `N` gives
  zero, in degrees `1` and `2`.
* `TauCeti.ContCohomology.explicitInfl1_injective` and
  `TauCeti.ContCohomology.explicitInfRes_exact`: the inflation-restriction sequence in degree `1`
  is exact at `H¹(G ⧸ N, M ^ N)` and at `H¹(G, M)`.

## Roadmap

This is the inflation half of the "three instances, in all three degrees" milestone of Layer 2 of
`TauCetiRoadmap/ProfiniteCohomology/README.md`, together with the "inflation-restriction" milestone
of Layer 5, whose two named targets are `explicitInfl1_injective` and `explicitInfRes_exact` and
which that layer states for an arbitrary topological group with discrete coefficients.

The two exactness proofs follow Mathlib's discrete `groupCohomology.H1InfRes_exact` and the
`Mono (H1InfRes A S).f` instance beside it, which Layer 5 names as the model; the continuous
statement adds continuity of the descended cocycle, which holds because `G → G ⧸ N` is a quotient
map.
-/

public section

namespace TauCeti.ContCohomology

universe uG uM

section Degree1

variable (G : Type uG) [Group G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]
  (N : Subgroup G) [N.Normal]

/-- **Inflation on continuous `1`-cocycles**: the compatible-pair pullback along the quotient
homomorphism `G → G ⧸ N` and the inclusion `M ^ N ↪ M`, sending `z` to `g ↦ z g`. -/
noncomputable def inflCocycles1 : Z1 (G ⧸ N) (H0 N M) →+ Z1 G M :=
  cocyclesMap1 (G ⧸ N) (H0 N M) G M (ContinuousMonoidHom.quotientMk N)
    (H0 N M).subtype continuous_subtype_val fun _ _ => rfl

/-- The inflated cocycle takes at `g` the value the original cocycle takes at the coset of `g`. -/
@[simp]
theorem coe_inflCocycles1 (z : Z1 (G ⧸ N) (H0 N M)) (g : G) :
    (inflCocycles1 G M N z : G → M) g = ((z : G ⧸ N → H0 N M) (g : G ⧸ N) : M) :=
  cocyclesMap1_apply (G ⧸ N) (H0 N M) G M _ _ _ _ z g

/-- The inflation of a continuous `1`-cocycle vanishes on `N`, since the cosets of the elements of
`N` are the identity and a cocycle vanishes at the identity. -/
theorem coe_inflCocycles1_of_mem (z : Z1 (G ⧸ N) (H0 N M)) {n : G} (hn : n ∈ N) :
    (inflCocycles1 G M N z : G → M) n = 0 := by
  rw [coe_inflCocycles1, (QuotientGroup.eq_one_iff n).2 hn, map_one_of_mem_Z1 z.2,
    ZeroMemClass.coe_zero]

variable [ContinuousSMul G M] [ContinuousSMul (G ⧸ N) (H0 N M)]

/-- **Inflation on explicit `H¹`**, the map `H¹(G ⧸ N, M ^ N) → H¹(G, M)` induced by the compatible
pair consisting of the quotient homomorphism `G → G ⧸ N` and the inclusion `M ^ N ↪ M`. -/
noncomputable def explicitInfl1 : H1 (G ⧸ N) (H0 N M) →+ H1 G M :=
  explicitMap1 (G ⧸ N) (H0 N M) G M (ContinuousMonoidHom.quotientMk N)
    (H0 N M).subtype continuous_subtype_val fun _ _ => rfl

/-- Inflation sends the class of a continuous `1`-cocycle to the class of its inflation; no
coboundary correction enters. -/
@[simp]
theorem explicitInfl1_mk (z : Z1 (G ⧸ N) (H0 N M)) :
    explicitInfl1 G M N (z : H1 (G ⧸ N) (H0 N M)) = (inflCocycles1 G M N z : H1 G M) :=
  explicitMap1_mk (G ⧸ N) (H0 N M) G M _ _ _ _ z

/-- An inflated class restricts to zero on `N`, because the inflated cocycle already vanishes
on `N`. -/
@[simp]
theorem explicitRes1_explicitInfl1 (x : H1 (G ⧸ N) (H0 N M)) :
    explicitRes1 G M N (explicitInfl1 G M N x) = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    rw [explicitInfl1_mk, explicitRes1_mk, H1pi_eq_zero_iff]
    have hzero : (cocyclesMap1 G M N M (ContinuousMonoidHom.subgroupSubtype N)
        (AddMonoidHom.id M) continuous_id (fun _ _ => rfl) (inflCocycles1 G M N z) :
        N → M) = 0 :=
      funext fun n => (cocyclesMap1_apply G M N M _ _ _ _ _ n).trans
        (coe_inflCocycles1_of_mem G M N z n.2)
    rw [hzero]
    exact zero_mem _

/-- The composition law for restriction after inflation: the composite
`H¹(G ⧸ N, M ^ N) → H¹(G, M) → H¹(N, M)` is zero. -/
theorem explicitRes1_comp_explicitInfl1 :
    (explicitRes1 G M N).comp (explicitInfl1 G M N) = 0 :=
  AddMonoidHom.ext (explicitRes1_explicitInfl1 G M N)

end Degree1

section Descent

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]
  {N : Subgroup G} [N.Normal]
  {z : G → M} (hz : z ∈ Z1 G M) (h0 : ∀ n ∈ N, z n = 0)

include hz h0

omit [N.Normal] in
/-- A continuous `1`-cocycle vanishing on `N` is constant on the left cosets of `N`. -/
private theorem descend_apply_mul (g : G) {n : G} (hn : n ∈ N) : z (g * n) = z g := by
  rw [(mem_Z1_iff.1 hz).2 g n, h0 n hn, smul_zero, zero_add]

/-- A continuous `1`-cocycle vanishing on the normal subgroup `N` takes its values in the
invariants `M ^ N`: normality turns left multiplication by `n ∈ N` into right multiplication by a
conjugate, which `descend_apply_mul` absorbs. -/
private theorem descend_mem (g : G) : z g ∈ H0 N M := by
  refine (FixedPoints.mem_addSubgroup N M (z g)).2 fun n => ?_
  have hleft : z ((n : G) * g) = (n : G) • z g := by
    rw [(mem_Z1_iff.1 hz).2 (n : G) g, h0 (n : G) n.2, add_zero]
  rw [show (n : G) * g = g * (g⁻¹ * (n : G) * g) by group,
    descend_apply_mul hz h0 g (Subgroup.Normal.conj_mem' ‹N.Normal› (n : G) n.2 g)] at hleft
  exact hleft.symm

/-- The function on `G ⧸ N` that a continuous `1`-cocycle vanishing on `N` descends to. -/
private def descendFun : G ⧸ N → H0 N M := fun q =>
  Quotient.liftOn' q (fun g => (⟨z g, descend_mem hz h0 g⟩ : H0 N M))
    fun a b hab => Subtype.ext
      ((descend_apply_mul hz h0 a (QuotientGroup.leftRel_apply.1 hab)).symm.trans
        (congrArg z (by group : a * (a⁻¹ * b) = b)))

private theorem coe_descendFun_mk (g : G) : (descendFun hz h0 (g : G ⧸ N) : M) = z g := rfl

private theorem continuous_descendFun : Continuous (descendFun hz h0) := by
  refine (QuotientGroup.isQuotientMap_mk N).continuous_iff.2 ?_
  exact Continuous.subtype_mk (mem_Z1_iff.1 hz).1 _

private theorem isCocycle₁_descendFun : groupCohomology.IsCocycle₁ (descendFun hz h0) := by
  intro q q'
  induction q using QuotientGroup.induction_on with
  | H g =>
    induction q' using QuotientGroup.induction_on with
    | H g' =>
      refine Subtype.ext ?_
      rw [← QuotientGroup.mk_mul, AddSubgroup.coe_add,
        coe_quotient_smul_fixedPoints_addSubgroup, coe_smul_fixedPoints_addSubgroup,
        coe_descendFun_mk, coe_descendFun_mk, coe_descendFun_mk]
      exact (mem_Z1_iff.1 hz).2 g g'

/-- **The descent of a continuous `1`-cocycle vanishing on a normal subgroup.** A continuous
`1`-cocycle `z` of `G` with `z n = 0` for every `n ∈ N` is constant on the left cosets of `N` and
takes its values in `M ^ N`, so it is the pullback of a continuous `1`-cocycle of `G ⧸ N` with
coefficients in `M ^ N`. Nothing is subtracted: `explicitInfl1_descendZ1` inflates it back to `z`
itself. -/
def descendZ1 : Z1 (G ⧸ N) (H0 N M) :=
  ⟨descendFun hz h0, mem_Z1_iff.2 ⟨continuous_descendFun hz h0, isCocycle₁_descendFun hz h0⟩⟩

/-- The descended cocycle has the values of the original one. -/
@[simp]
theorem coe_descendZ1_mk (g : G) :
    ((descendZ1 hz h0 : G ⧸ N → H0 N M) (g : G ⧸ N) : M) = z g :=
  coe_descendFun_mk hz h0 g

/-- Inflating the descended cocycle returns the original cocycle, on the nose. -/
@[simp]
theorem inflCocycles1_descendZ1 : inflCocycles1 G M N (descendZ1 hz h0) = ⟨z, hz⟩ :=
  Subtype.ext (funext fun g => (coe_inflCocycles1 G M N (descendZ1 hz h0) g).trans
    (coe_descendZ1_mk hz h0 g))

variable [ContinuousSMul G M] [ContinuousSMul (G ⧸ N) (H0 N M)]

/-- The class of the descended cocycle inflates to the class of the original cocycle. -/
theorem explicitInfl1_descendZ1 :
    explicitInfl1 G M N ((descendZ1 hz h0 : Z1 (G ⧸ N) (H0 N M)) : H1 (G ⧸ N) (H0 N M)) =
      ((⟨z, hz⟩ : Z1 G M) : H1 G M) := by
  rw [explicitInfl1_mk, inflCocycles1_descendZ1]

end Descent

section InflationRestriction

variable (G : Type uG) [Group G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (N : Subgroup G) [N.Normal] [ContinuousSMul (G ⧸ N) (H0 N M)]

/-- **Inflation is injective in degree one.** If the inflation of a class on `G ⧸ N` is the
coboundary of `m ∈ M`, then `m` is already `N`-invariant, because the inflated cocycle vanishes on
`N`; so the class was the coboundary of `m` inside `M ^ N`. -/
theorem explicitInfl1_injective : Function.Injective (explicitInfl1 G M N) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    rw [explicitInfl1_mk, H1pi_eq_zero_iff, mem_B1_iff] at hx
    obtain ⟨m, hm⟩ := hx
    have hmem : m ∈ H0 N M := by
      refine (FixedPoints.mem_addSubgroup N M m).2 fun n => ?_
      have h := (hm (n : G)).trans (coe_inflCocycles1_of_mem G M N z n.2)
      rwa [sub_eq_zero] at h
    rw [H1pi_eq_zero_iff, mem_B1_iff]
    refine ⟨⟨m, hmem⟩, fun q => ?_⟩
    induction q using QuotientGroup.induction_on with
    | H g =>
      refine Subtype.ext ?_
      rw [AddSubgroup.coe_sub, coe_quotient_smul_fixedPoints_addSubgroup,
        coe_smul_fixedPoints_addSubgroup]
      exact (hm g).trans (coe_inflCocycles1 G M N z g)

/-- **Exactness of the inflation-restriction sequence at `H¹(G, M)`.** A continuous `1`-cocycle
whose restriction to `N` is a coboundary becomes, after that coboundary is subtracted, a cocycle
vanishing on `N`, and `descendZ1` exhibits it as an inflation. -/
theorem explicitInfRes_exact :
    Function.Exact (explicitInfl1 G M N) (explicitRes1 G M N) := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ f =>
    refine ⟨fun hx => ?_, fun ⟨y, hy⟩ => hy ▸ explicitRes1_explicitInfl1 G M N y⟩
    rw [explicitRes1_mk, H1pi_eq_zero_iff, mem_B1_iff] at hx
    obtain ⟨m, hm⟩ := hx
    have hres : ∀ n ∈ N, (f : G → M) n = n • m - m := fun n hn =>
      ((hm ⟨n, hn⟩).trans (cocyclesMap1_apply G M N M _ _ _ _ f ⟨n, hn⟩)).symm
    -- Subtract the coboundary of `m`: the difference vanishes on `N`, hence descends.
    have hd0 : d0 G M m ∈ Z1 G M :=
      B1_le_Z1 G M (mem_B1_iff.2 ⟨m, fun g => (d0_apply m g).symm⟩)
    have hsub : (f : G → M) - d0 G M m ∈ Z1 G M := (Z1 G M).sub_mem f.2 hd0
    have hvanish : ∀ n ∈ N, ((f : G → M) - d0 G M m) n = 0 := fun n hn => by
      rw [Pi.sub_apply, d0_apply, hres n hn, sub_self]
    refine ⟨((descendZ1 hsub hvanish : Z1 (G ⧸ N) (H0 N M)) : H1 (G ⧸ N) (H0 N M)), ?_⟩
    rw [explicitInfl1_descendZ1, H1pi_eq_iff, AddSubgroup.coe_mk]
    refine mem_B1_iff.2 ⟨-m, fun g => ?_⟩
    rw [Pi.sub_apply, Pi.sub_apply, d0_apply, smul_neg]
    abel

end InflationRestriction

section Degree2

variable (G : Type uG) [Group G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]
  (N : Subgroup G) [N.Normal]

/-- **Inflation on continuous `2`-cocycles**, the degree-two compatible-pair pullback along the
same pair as `inflCocycles1`. -/
noncomputable def inflCocycles2 : Z2 (G ⧸ N) (H0 N M) →+ Z2 G M :=
  cocyclesMap2 (G ⧸ N) (H0 N M) G M (ContinuousMonoidHom.quotientMk N)
    (H0 N M).subtype continuous_subtype_val fun _ _ => rfl

/-- The inflated `2`-cocycle takes at `(g, h)` the value the original one takes at the pair of
cosets. -/
@[simp]
theorem coe_inflCocycles2 (z : Z2 (G ⧸ N) (H0 N M)) (g h : G) :
    (inflCocycles2 G M N z : G × G → M) (g, h) =
      ((z : (G ⧸ N) × (G ⧸ N) → H0 N M) ((g : G ⧸ N), (h : G ⧸ N)) : M) :=
  cocyclesMap2_apply (G ⧸ N) (H0 N M) G M _ _ _ _ z g h

/-- On `N × N` the inflation of a continuous `2`-cocycle is constant with value `z (1, 1)`: both
arguments have trivial coset. -/
theorem coe_inflCocycles2_of_mem (z : Z2 (G ⧸ N) (H0 N M)) {n n' : G} (hn : n ∈ N)
    (hn' : n' ∈ N) :
    (inflCocycles2 G M N z : G × G → M) (n, n') =
      ((z : (G ⧸ N) × (G ⧸ N) → H0 N M) (1, 1) : M) := by
  rw [coe_inflCocycles2, (QuotientGroup.eq_one_iff n).2 hn, (QuotientGroup.eq_one_iff n').2 hn']

variable [IsTopologicalGroup G] [ContinuousSMul G M] [ContinuousSMul (G ⧸ N) (H0 N M)]

/-- **Inflation on explicit `H²`**, the map `H²(G ⧸ N, M ^ N) → H²(G, M)` induced by the same
compatible pair as `explicitInfl1`. It is the last map of the five-term exact sequence, so it is a
target in its own right and not a variant of the degree-one map. -/
noncomputable def explicitInfl2 : H2 (G ⧸ N) (H0 N M) →+ H2 G M :=
  explicitMap2 (G ⧸ N) (H0 N M) G M (ContinuousMonoidHom.quotientMk N)
    (H0 N M).subtype continuous_subtype_val fun _ _ => rfl

/-- Inflation sends the class of a continuous `2`-cocycle to the class of its inflation. -/
@[simp]
theorem explicitInfl2_mk (z : Z2 (G ⧸ N) (H0 N M)) :
    explicitInfl2 G M N (z : H2 (G ⧸ N) (H0 N M)) = (inflCocycles2 G M N z : H2 G M) :=
  explicitMap2_mk (G ⧸ N) (H0 N M) G M _ _ _ _ z

/-- An inflated degree-two class restricts to zero on `N`: the restriction of the inflated cocycle
is constant with value `z (1, 1)`, which is the coboundary of the constant `1`-cochain with that
same `N`-invariant value. -/
@[simp]
theorem explicitRes2_explicitInfl2 (x : H2 (G ⧸ N) (H0 N M)) :
    explicitRes2 G M N (explicitInfl2 G M N x) = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    rw [explicitInfl2_mk, explicitRes2_mk, H2pi_eq_zero_iff]
    refine mem_B2_iff'.2 ⟨Function.const N
      ((z : (G ⧸ N) × (G ⧸ N) → H0 N M) (1, 1) : M), continuous_const, fun n n' => ?_⟩
    have hval := (cocyclesMap2_apply G M N M (ContinuousMonoidHom.subgroupSubtype N)
      (AddMonoidHom.id M) continuous_id (fun _ _ => rfl) (inflCocycles2 G M N z) n n').trans
        (coe_inflCocycles2_of_mem G M N z n.2 n'.2)
    have hfix := (FixedPoints.mem_addSubgroup N M
      ((z : (G ⧸ N) × (G ⧸ N) → H0 N M) (1, 1) : M)).1
        ((z : (G ⧸ N) × (G ⧸ N) → H0 N M) (1, 1)).2 n
    rw [hval, Function.const_apply, Function.const_apply, Function.const_apply, hfix]
    abel

/-- The composition law for restriction after inflation in degree two: the composite
`H²(G ⧸ N, M ^ N) → H²(G, M) → H²(N, M)` is zero. -/
theorem explicitRes2_comp_explicitInfl2 :
    (explicitRes2 G M N).comp (explicitInfl2 G M N) = 0 :=
  AddMonoidHom.ext (explicitRes2_explicitInfl2 G M N)

end Degree2

end TauCeti.ContCohomology
