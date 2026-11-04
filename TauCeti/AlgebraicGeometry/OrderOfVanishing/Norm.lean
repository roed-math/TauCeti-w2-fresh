/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Norm.Defs
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import Mathlib.RingTheory.QuasiFinite.Basic
import TauCeti.AlgebraicGeometry.AffineScheme.PrimesOver
import TauCeti.RingTheory.KrullDimension.Integral
import TauCeti.RingTheory.Length.Norm.PrimesOver

/-!
# The order of a norm at a point of codimension one

Let `f : X ⟶ Y` be a dominant morphism of locally Noetherian integral schemes, so that `f`
pulls back rational functions, `K(Y) → K(X)`. Let `y ∈ Y` be a point of codimension one with an
affine open neighbourhood `V` whose preimage `f⁻¹ V` is affine and finite over `V`. For a nonzero
rational function `r` on `X`,
`ord_y N_{K(X)/K(Y)}(r) = Σ_{f x = y} [κ(x) : κ(y)] ord_x(r)`
(`TauCeti.AlgebraicGeometry.ord_norm_eq_finsum_of_isAffineOpen`). This is the coefficient of
`div N(r)` at `y` in Fulton, *Intersection Theory*, Proposition 1.4(b): the right-hand side is the
coefficient at `y` of the pushforward of `div r` with residue-degree weights.

The proof reads the identity off the commutative algebra of Fulton's Appendix A.3
(`TauCeti.ordFrac_norm_eq_finprod_primesOver`) applied to the finite extension
`Γ(Y, V) → Γ(X, f⁻¹ V)`, the prime of `y` and the local rings of `X` at the points of the fibre,
which are the primes over it (`AlgebraicGeometry.IsAffineOpen.preimageSingletonEquivPrimesOver`).
The residue degrees enter as lengths: `length_{𝒪_{Y,y}} κ(x) = [κ(x) : κ(y)]`
(`TauCeti.AlgebraicGeometry.length_residueField_eq_residueDegree`).
-/

public section

open AlgebraicGeometry CategoryTheory Order IsLocalRing

universe u

namespace TauCeti.AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The local ring `𝒪_{Y,y}` maps to the local ring `𝒪_{X,x}` of a point over `y`, through the
stalk map of `f` at `x`. -/
noncomputable abbrev stalkAlgebraOfApplyEq (f : X ⟶ Y) {x : X} {y : Y} (h : f x = y) :
    Algebra (Y.presheaf.stalk y) (X.presheaf.stalk x) :=
  (Y.presheaf.stalkSpecializes (specializes_of_eq h) ≫ f.stalkMap x).hom.toAlgebra

/-- The residue field `κ(x)` of a point over `y`, as a module over `𝒪_{Y,y}`, has length the
residue degree `[κ(x) : κ(y)]` (both are `0` when the extension is infinite). -/
theorem length_residueField_eq_residueDegree (f : X ⟶ Y) {x : X} {y : Y} (h : f x = y) :
    letI := stalkAlgebraOfApplyEq f h
    (Module.length (Y.presheaf.stalk y) (ResidueField (X.presheaf.stalk x))).toNat =
      f.residueDegree x := by
  subst h
  let φ := (Y.presheaf.stalkSpecializes (specializes_of_eq (rfl : f x = f x)) ≫ f.stalkMap x).hom
  have hφ : φ = (f.stalkMap x).hom := by simp [φ]
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := φ.toAlgebra
  let _ : Algebra (ResidueField (Y.presheaf.stalk (f x))) (ResidueField (X.presheaf.stalk x)) :=
    (ResidueField.map (f.stalkMap x).hom).toAlgebra
  -- `𝒪_{Y,f x}` acts on `κ(x)` through `κ(f x)`.
  have : IsScalarTower (Y.presheaf.stalk (f x)) (ResidueField (Y.presheaf.stalk (f x)))
      (ResidueField (X.presheaf.stalk x)) :=
    .of_algebraMap_smul fun a c ↦ by
      obtain ⟨c, rfl⟩ := residue_surjective c
      change ResidueField.map (f.stalkMap x).hom (residue _ a) * residue _ c =
        residue _ (φ a * c)
      rw [ResidueField.map_residue, hφ, map_mul]
  rw [Module.length_eq_of_surjective (R := ResidueField (Y.presheaf.stalk (f x)))
    residue_surjective]
  change _ = Module.finrank (ResidueField (Y.presheaf.stalk (f x)))
    (ResidueField (X.presheaf.stalk x))
  by_cases hfin : Module.Finite (ResidueField (Y.presheaf.stalk (f x)))
      (ResidueField (X.presheaf.stalk x))
  · rw [Module.length_eq_finrank, ENat.toNat_natCast]
  · rw [Module.finrank_of_not_finite hfin, ENat.toNat_eq_zero]
    refine Or.inr (not_not.mp fun h ↦ hfin ?_)
    have := (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp h)).1
    infer_instance

variable [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- **The order of a norm at a point of codimension one** (Fulton, *Intersection Theory*,
Proposition 1.4(b) and Appendix A.3). Let `f : X ⟶ Y` be a dominant morphism of locally
Noetherian integral schemes, `y ∈ Y` a point of codimension one, and `V ∋ y` an affine open whose
preimage is affine and finite over it. For a nonzero rational function `r` on `X`,
`ord_y N_{K(X)/K(Y)}(r) = Σ_{f x = y} [κ(x) : κ(y)] ord_x(r)`. -/
theorem ord_norm_eq_finsum_of_isAffineOpen (f : X ⟶ Y) [IsDominant f] {V : Y.Opens}
    (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
    (hfin : (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.Finite) {y : Y} (hy : y ∈ V)
    (hy1 : coheight y = 1) {r : X.functionField} (hr : r ≠ 0) :
    letI := f.functionFieldMap.hom.toAlgebra
    Y.ord (Algebra.norm Y.functionField r) y =
      ∑ᶠ x ∈ f ⁻¹' {y}, X.ord r x * f.residueDegree x := by
  let _ := f.functionFieldMap.hom.toAlgebra
  have : Nonempty V := ⟨⟨y, hy⟩⟩
  have : Nonempty (f ⁻¹ᵁ V) := ⟨⟨genericPoint X, by
    rw [Scheme.Hom.mem_preimage, f.genericPoint_eq_of_isDominant]
    exact (genericPoint_spec Y).mem_open_set_iff V.isOpen |>.mpr ⟨y, trivial, hy⟩⟩⟩
  -- The finite extension `A₀ = Γ(Y, V) → B₀ = Γ(X, f⁻¹ V)` of domains.
  algebraize [(f.appLE V (f ⁻¹ᵁ V) le_rfl).hom]
  have : FaithfulSMul Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (f.appLE_injective_of_isDominant V (f ⁻¹ᵁ V) le_rfl)
  set p := (hV.primeIdealOf ⟨y, hy⟩).asIdeal
  -- The local ring `A = 𝒪_{Y,y}` is the localization of `A₀` at `p`.
  let _ : Algebra Γ(Y, V) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk ⟨y, hy⟩
  have : IsLocalization.AtPrime (Y.presheaf.stalk y) p := hV.isLocalization_stalk ⟨y, hy⟩
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk y) := krullDimLE_of_coheight_le hy1.le
  have hp : p.height = 1 := by
    have := (IsLocalization.AtPrime.ringKrullDim_eq_height p (Y.presheaf.stalk y)).symm.trans
      (ringKrullDim_stalk_eq_coheight y)
    rw [hy1] at this
    exact_mod_cast this
  -- The function fields and their towers.
  let _ : Algebra (Y.presheaf.stalk y) X.functionField :=
    ((algebraMap Y.functionField X.functionField).comp
      (algebraMap (Y.presheaf.stalk y) Y.functionField)).toAlgebra
  have : IsScalarTower (Y.presheaf.stalk y) Y.functionField X.functionField :=
    .of_algebraMap_eq' rfl
  let _ : Algebra Γ(Y, V) X.functionField :=
    ((algebraMap (Y.presheaf.stalk y) X.functionField).comp
      (algebraMap Γ(Y, V) (Y.presheaf.stalk y))).toAlgebra
  have : IsScalarTower Γ(Y, V) (Y.presheaf.stalk y) X.functionField := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) X.functionField := .of_algebraMap_eq' <| by
    have h := functionField_isScalarTower Y V ⟨y, hy⟩
    change (algebraMap Y.functionField X.functionField).comp
      ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (algebraMap Γ(Y, V) _)) = _
    rw [← IsScalarTower.algebraMap_eq]
    change (f.functionFieldMap.hom).comp (Y.germToFunctionField V).hom =
      (X.germToFunctionField (f ⁻¹ᵁ V)).hom.comp (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom
    rw [← CommRingCat.hom_comp, f.germToFunctionField_functionFieldMap, ← CommRingCat.hom_comp,
      Scheme.Hom.appLE_eq_app]
  have : IsFractionRing Γ(X, f ⁻¹ᵁ V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X _ hU
  -- The points of the fibre, indexed by the primes of `B₀` over `p`.
  let x (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : X := hU.fromSpec ⟨q.1, q.2.1⟩
  have hxU (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : x q ∈ f ⁻¹ᵁ V := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  let e := hV.preimageSingletonEquivPrimesOver f hU rfl hy
  have hex (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : (e.symm q).1 = x q :=
    hV.coe_preimageSingletonEquivPrimesOver_symm_apply f hU rfl hy q
  have hfx (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : f (x q) = y := hex q ▸ (e.symm q).2
  -- The local rings `𝒪_{X, x q}`, localizations of `B₀` at `q` and `A`-algebras.
  let _ (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : Algebra Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk (x q)) :=
    X.presheaf.algebra_section_stalk ⟨x q, hxU q⟩
  have (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : IsLocalization.AtPrime (X.presheaf.stalk (x q)) q.1 :=
    hU.isLocalization_stalk' ⟨q.1, q.2.1⟩ (hxU q)
  have (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) :
      IsScalarTower Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk (x q)) X.functionField :=
    functionField_isScalarTower X (f ⁻¹ᵁ V) ⟨x q, hxU q⟩
  let _ (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : Algebra (Y.presheaf.stalk y) (X.presheaf.stalk (x q)) :=
    stalkAlgebraOfApplyEq f (hfx q)
  let _ (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : Algebra Γ(Y, V) (X.presheaf.stalk (x q)) :=
    ((algebraMap Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk (x q))).comp
      (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V))).toAlgebra
  have (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) :
      IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk (x q)) :=
    .of_algebraMap_eq' rfl
  have (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) :
      IsScalarTower Γ(Y, V) (Y.presheaf.stalk y) (X.presheaf.stalk (x q)) :=
    .of_algebraMap_eq' <| by
      change (X.presheaf.germ _ (x q) (hxU q)).hom.comp (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom =
        (Y.presheaf.stalkSpecializes (specializes_of_eq (hfx q)) ≫ f.stalkMap (x q)).hom.comp
          (Y.presheaf.germ V y hy).hom
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
        TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap,
        Scheme.Hom.appLE_eq_app]
  -- The points of the fibre have codimension one: `ht q ≤ ht p = 1` by incomparability, and
  -- `q ≠ 0` since `p ≠ 0`.
  have hq1 (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : coheight (x q) = 1 := by
    have : q.1.IsPrime := q.2.1
    have h :=
      (IsLocalization.AtPrime.ringKrullDim_eq_height q.1 (X.presheaf.stalk (x q))).symm.trans
        (ringKrullDim_stalk_eq_coheight (x q))
    have hle : q.1.height ≤ p.height := by
      have h' := height_le_height_apply_of_strictMono _
        (primeSpectrumComap_strictMono_of_isIntegral (R := Γ(Y, V)) (S := Γ(X, f ⁻¹ᵁ V)))
        ⟨q.1, q.2.1⟩
      have : q.1.LiesOver p := q.2.2
      have hc : PrimeSpectrum.comap (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) ⟨q.1, q.2.1⟩ =
          ⟨p, inferInstance⟩ :=
        PrimeSpectrum.ext (Ideal.over_def q.1 p).symm
      rw [hc, ← PrimeSpectrum.height_eq_orderHeight, ← PrimeSpectrum.height_eq_orderHeight] at h'
      exact h'
    have hne : q.1.height ≠ 0 := by
      have : q.1.LiesOver p := q.2.2
      rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
      intro h0
      have hp0 : p = ⊥ := by
        rw [Ideal.over_def q.1 p, h0]
        exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
      rw [hp0, Ideal.height_bot] at hp
      exact zero_ne_one hp
    have hq : q.1.height = 1 :=
      le_antisymm (hle.trans hp.le) (Order.one_le_iff_ne_zero.mpr hne)
    rw [hq] at h
    exact_mod_cast h.symm
  have (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : Ring.KrullDimLE 1 (X.presheaf.stalk (x q)) :=
    krullDimLE_of_coheight_le (hq1 q).le
  -- Fulton's Appendix A.3 over the primes above `p`.
  have H := ordFrac_norm_eq_finprod_primesOver (K := Y.functionField) (A := Y.presheaf.stalk y) p
    (fun q ↦ X.presheaf.stalk (x q)) hr
  have hord (q : p.primesOver Γ(X, f ⁻¹ᵁ V)) : Ring.ordFrac (X.presheaf.stalk (x q)) r =
      ↑(Multiplicative.ofAdd (X.ord r (x q))) :=
    (Scheme.ord_eq_iff (hq1 q) hr).mp rfl
  have : Fintype (p.primesOver Γ(X, f ⁻¹ᵁ V)) := (Algebra.QuasiFinite.finite_primesOver p).fintype
  simp only [hord, length_residueField_eq_residueDegree f (hfx _), ← WithZero.coe_pow,
    ← ofAdd_nsmul, finprod_eq_prod_of_fintype] at H
  have hprod : ∏ q, ((Multiplicative.ofAdd (f.residueDegree (x q) • X.ord r (x q)) :
      Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ↑(∏ q, Multiplicative.ofAdd (f.residueDegree (x q) • X.ord r (x q))) :=
    (map_prod (WithZero.coeMonoidHom : Multiplicative ℤ →* WithZero (Multiplicative ℤ)) _ _).symm
  rw [hprod, ← ofAdd_sum] at H
  have hN : Algebra.norm Y.functionField r ≠ 0 := by
    intro h0
    rw [h0, map_zero] at H
    exact WithZero.zero_ne_coe H
  rw [Scheme.ord_eq_iff hy1 hN, ← finsum_set_coe_eq_finsum_mem, ← finsum_comp_equiv e.symm,
    finsum_eq_sum_of_fintype]
  refine H.trans ?_
  congr 2
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [hex, nsmul_eq_mul, mul_comm]

end TauCeti.AlgebraicGeometry
