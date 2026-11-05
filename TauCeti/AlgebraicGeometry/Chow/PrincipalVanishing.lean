/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.PrincipalPushforward
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.GenericFiber
import TauCeti.AlgebraicGeometry.Chow.CurveDegree
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.AlgebraicGeometry.OrderOfVanishing.StalkIso

/-!
# Principal divisors push forward to zero along dimension-dropping proper maps

Let `k` be a field and `f : X ⟶ Y` a proper morphism over `k` from an integral scheme, between
schemes locally of finite type over `k`. If the image `f(X)` has smaller dimension than `X`, then
for every nonzero rational function `r` on `X`, the pushforward of its principal cycle with
residue-degree weights vanishes: `f_* div(r) = 0` (`Chow.map_height_div_eq_zero_of_height_lt`;
Fulton, *Intersection Theory*, Proposition 1.4(a)).

The points `x` contributing to `f_* div(r)` have codimension one in `X` and finite residue
extension over `f x`, so `f x` has the dimension `dim X - 1` of `x`, while it lies in `f(X)`.

* If `dim f(X) < dim X - 1`, there are no such points
  (`Chow.map_height_div_eq_zero_of_height_add_one_lt`).
* If `dim f(X) = dim X - 1`, every such `f x` is the generic point `η` of `f(X)`. Replacing `Y` by
  `f(X)`, the coefficient of `f_* div(r)` at `η` is `Σ_{f x = η} [κ(x) : κ(η)] ord_x(r)`. The
  generic fibre `X_η` of `f` is an integral curve, proper over `κ(η)`, with the local rings, the
  orders of vanishing and the residue degrees of `X` at the points over `η`
  (`TauCeti.AlgebraicGeometry.bijective_stalkMap_fiberι_genericPoint`,
  `TauCeti.AlgebraicGeometry.ord_functionFieldMap_of_bijective`,
  `TauCeti.AlgebraicGeometry.residueDegree_fiberι`). So the coefficient is the degree of the
  principal cycle of `r` on `X_η`, which vanishes (`Chow.degree_div_eq_zero`)
  (`Chow.map_height_div_eq_zero_of_height_add_one`).

## Main results

* `TauCeti.AlgebraicGeometry.Chow.map_height_div_eq_zero_of_height_add_one_lt`: `f_* div(r) = 0`
  when `dim f(X) + 1 < dim X`, for `f` quasi-compact.
* `TauCeti.AlgebraicGeometry.Chow.map_height_div_eq_zero_of_height_add_one`: `f_* div(r) = 0` for
  `f : X ⟶ Y` proper and dominant with `dim Y + 1 = dim X`.
* `TauCeti.AlgebraicGeometry.Chow.map_height_div_eq_zero_of_height_lt`: `f_* div(r) = 0` for `f`
  proper with `dim f(X) < dim X`.

## References

* W. Fulton, *Intersection Theory*, Proposition 1.4.
* The Stacks Project, Lemma 02RU.
-/

public section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace TauCeti.AlgebraicGeometry

section GenericFiber

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
  [LocallyOfFiniteType f]

/-- **The generic fibre is a curve** as soon as it has a closed point of codimension one. Let
`f : X ⟶ Y` be a dominant morphism of integral schemes, locally of finite type, and let `x` be a
point over the generic point `η` of `Y`, of codimension one in `X`, with `κ(x)` finite over
`κ(η)`. Then the generic fibre has dimension one: `x` has codimension one in it, and it is a closed
point of the fibre, a scheme locally of finite type over `κ(η)`. -/
theorem topologicalKrullDim_fiber_genericPoint_eq_one {x : X} (hx : f x = genericPoint Y)
    (h1 : coheight x = 1) (hd : f.residueDegree x ≠ 0) :
    topologicalKrullDim (f.fiber (genericPoint Y)) = 1 := by
  let K := Y.residueField (genericPoint Y)
  let _ : (f.fiber (genericPoint Y)).Over (Spec (.of K)) := f.fiberOverSpecResidueField _
  let _ : (Spec (.of K)).Over (Spec (.of K)) := ⟨𝟙 _⟩
  have : (f.fiber (genericPoint Y) ↘ Spec (.of K)).IsOver (Spec (.of K)) := ⟨Category.comp_id _⟩
  have : LocallyOfFiniteType (f.fiber (genericPoint Y) ↘ Spec (.of K)) :=
    inferInstanceAs
      (LocallyOfFiniteType (Limits.pullback.snd f (Y.fromSpecResidueField (genericPoint Y))))
  have : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let x₀ := (f.fiberHomeo (genericPoint Y)).symm ⟨x, hx⟩
  have hι : f.fiberι (genericPoint Y) x₀ = x := f.fiberι_fiberHomeo_symm _ ⟨x, hx⟩
  -- `x₀` has the residue field of `x`, finite over `K`, so it has the height of the point of
  -- `Spec K`, which is zero.
  have h0 : height x₀ = 0 := by
    rw [← height_apply_eq_height_of_residueDegree_ne_zero K
      (f.fiber (genericPoint Y) ↘ Spec (.of K)) (by rwa [← hι, residueDegree_fiberι] at hd)]
    exact height_eq_zero.mpr fun b _ ↦ (Subsingleton.elim _ b).le
  have h1 : coheight x₀ = 1 := by rw [← coheight_fiberι_genericPoint, hι, h1]
  rw [← coheight_add_height_eq_topologicalKrullDim K x₀, h0, h1]
  simp

/-- **Degrees on the generic fibre.** Let `f : X ⟶ Y` be a dominant quasi-compact morphism of
integral schemes, locally of finite type, with `X` locally Noetherian, and let `η` be the generic
point of `Y`. For a nonzero rational function `r` on `X`, viewed on the generic fibre, the degree
over `κ(η)` of its principal cycle on the generic fibre is `Σ_{f x = η} [κ(x) : κ(η)] ord_x(r)`:
the generic fibre has the local rings, hence the orders of vanishing, and the residue degrees of
`X` at the points over `η`. -/
theorem degree_div_fiber_genericPoint [IsLocallyNoetherian X] [QuasiCompact f]
    (r : X.functionFieldˣ) :
    AlgebraicCycle.degree (f.fiberToSpecResidueField (genericPoint Y)) (AlgebraicCycle.div
        (Units.map (f.fiberι (genericPoint Y)).functionFieldMap.hom.toMonoidHom r)) =
      ∑ᶠ x ∈ f ⁻¹' {genericPoint Y}, AlgebraicCycle.div r x * f.residueDegree x := by
  rw [AlgebraicCycle.degree_apply,
    ← finsum_comp_equiv (f.fiberHomeo (genericPoint Y)).toEquiv.symm,
    ← finsum_set_coe_eq_finsum_mem]
  refine finsum_congr fun p ↦ ?_
  simp only [Homeomorph.coe_symm_toEquiv, AlgebraicCycle.div_apply, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, ← residueDegree_fiberι]
  rw [ord_functionFieldMap_of_bijective _ (bijective_stalkMap_fiberι_genericPoint f _),
    f.fiberι_fiberHomeo_symm, nsmul_eq_mul, mul_comm]

end GenericFiber

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [IsIntegral X] [IsLocallyNoetherian X]

namespace Chow

/-- A point contributing to `f_* div(r)` has codimension one, finite residue extension, and image
of dimension `dim X - 1`. -/
private lemma height_add_one_of_div_mul_ne_zero (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    {r : X.functionFieldˣ} {x : X} (hne : AlgebraicCycle.div r x * f.residueDegree x ≠ 0) :
    coheight x = 1 ∧ f.residueDegree x ≠ 0 ∧ height (f x) + 1 = height (genericPoint X) := by
  rw [AlgebraicCycle.div_apply] at hne
  have hd : f.residueDegree x ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hne
  -- `x` has codimension one, so `height x + 1 = dim X`.
  have hx1 : coheight x = 1 := by
    by_contra h'
    exact left_ne_zero_of_mul hne (Scheme.ord_eq_zero_of_coheight_neq_one h' _)
  have hdim := coheight_add_height_eq_topologicalKrullDim k x
  rw [topologicalKrullDim_eq_height_genericPoint, hx1, add_comm] at hdim
  refine ⟨hx1, hd, ?_⟩
  rw [height_apply_eq_height_of_residueDegree_ne_zero k f hd]
  exact WithBot.coe_injective hdim

/-- **Principal divisors vanish under a large drop of dimension.** Let `f : X ⟶ Y` be a
quasi-compact morphism over a field `k` from an integral scheme, between schemes locally of
finite type over `k`, whose image has dimension less than `dim X - 1`. Then `f_* div r = 0` for
every nonzero rational function `r` on `X`: the points of `div r` have dimension `dim X - 1`, and
those with finite residue extension would keep that dimension in the image. -/
theorem map_height_div_eq_zero_of_height_add_one_lt (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [QuasiCompact f] (h : height (f (genericPoint X)) + 1 < height (genericPoint X))
    (r : X.functionFieldˣ) :
    AlgebraicCycle.map f height height (AlgebraicCycle.div r) = 0 := by
  ext y
  rw [map_height_apply k, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
  refine finsum_mem_eq_zero_of_forall_eq_zero fun x _ ↦ ?_
  by_contra hne
  obtain ⟨-, -, hx⟩ := height_add_one_of_div_mul_ne_zero k f hne
  -- `f x` is a specialization of `f η`, of dimension `dim X - 1`.
  have hle : height (f x) ≤ height (f (genericPoint X)) :=
    height_mono (((genericPoint_spec X).specializes (Set.mem_univ x)).map f.continuous)
  exact h.not_ge (hx ▸ add_le_add_left hle 1)

/-- **Principal divisors push forward to zero along a proper map onto an integral scheme of one
dimension less** (Fulton, *Intersection Theory*, Proposition 1.4(a)). Let `f : X ⟶ Y` be a
proper dominant morphism over a field `k` of integral schemes locally of finite type over `k`, with
`dim X = dim Y + 1`. Then `f_* div r = 0` for every nonzero rational function `r` on `X`.

Only the generic point `η` of `Y` can carry a coefficient, and that coefficient
`Σ_{f x = η} [κ(x) : κ(η)] ord_x(r)` is the degree of the principal cycle of `r` on the generic
fibre, an integral curve proper over `κ(η)`, so it vanishes (`Chow.degree_div_eq_zero`). -/
theorem map_height_div_eq_zero_of_height_add_one [IsIntegral Y] (f : X ⟶ Y)
    [f.IsOver (Spec (.of k))] [IsProper f] [IsDominant f]
    (h : height (genericPoint Y) + 1 = height (genericPoint X)) (r : X.functionFieldˣ) :
    AlgebraicCycle.map f height height (AlgebraicCycle.div r) = 0 := by
  ext y
  rw [map_height_apply k, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
  by_contra hne
  obtain ⟨x, hxy, hx⟩ := exists_ne_zero_of_finsum_mem_ne_zero hne
  obtain ⟨hx1, hd, hxh⟩ := height_add_one_of_div_mul_ne_zero k f hx
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hxy
  subst hxy
  -- `f x` is the generic point `η` of `Y`: it is a specialization of `η` of the same dimension.
  have hfx : f x = genericPoint Y := by
    have hle : f x ≤ genericPoint Y := (genericPoint_spec Y).specializes (Set.mem_univ _)
    by_contra hne'
    have hlt : f x < genericPoint Y :=
      hle.lt_of_not_ge fun hge ↦ hne' (Specializes.antisymm hge hle).eq
    have hfin : height (f x) < ⊤ := by
      rw [height_eq_toNat_trdeg_residueField k]
      exact ENat.natCast_lt_top _
    exact (height_strictMono hlt hfin).ne (WithTop.add_right_cancel ENat.one_ne_top
      (hxh.trans h.symm))
  rw [hfx] at hne
  -- The generic fibre is a proper curve over `κ(η)`, on which principal cycles have degree zero.
  let K := Y.residueField (genericPoint Y)
  let _ : (f.fiber (genericPoint Y)).Over (Spec (.of K)) := f.fiberOverSpecResidueField _
  have : IsProper (f.fiber (genericPoint Y) ↘ Spec (.of K)) :=
    inferInstanceAs (IsProper (Limits.pullback.snd f (Y.fromSpecResidueField (genericPoint Y))))
  exact hne ((degree_div_fiber_genericPoint f r).symm.trans
    (degree_div_eq_zero K (topologicalKrullDim_fiber_genericPoint_eq_one f hfx hx1 hd) _))

/-- **Principal divisors push forward to zero along dimension-dropping proper maps** (Fulton,
*Intersection Theory*, Proposition 1.4(a)). Let `f : X ⟶ Y` be a proper morphism over a field `k`
from an integral scheme, between schemes locally of finite type over `k`, whose image has smaller
dimension than `X`. Then `f_* div r = 0` for every nonzero rational function `r` on `X`. -/
theorem map_height_div_eq_zero_of_height_lt (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (h : height (f (genericPoint X)) < height (genericPoint X)) (r : X.functionFieldˣ) :
    AlgebraicCycle.map f height height (AlgebraicCycle.div r) = 0 := by
  rcases (Order.add_one_le_of_lt h).lt_or_eq with hlt | heq
  · exact map_height_div_eq_zero_of_height_add_one_lt k f hlt r
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  -- The image is an integral scheme over `k`, locally of finite type, through `Y`.
  let _ : f.image.Over (Spec (.of k)) := ⟨f.imageι ≫ Y ↘ Spec (.of k)⟩
  have : f.imageι.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : f.toImage.IsOver (Spec (.of k)) := ⟨by
    -- The structure morphism of the image is, by the definition above, `f.imageι` followed by
    -- that of `Y`.
    change f.toImage ≫ f.imageι ≫ Y ↘ Spec (.of k) = _
    rw [f.toImage_imageι_assoc, comp_over]⟩
  have : LocallyOfFiniteType (f.image ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (f.imageι ≫ Y ↘ Spec (.of k)))
  have : IsProper (f.toImage ≫ f.imageι) := by rw [f.toImage_imageι]; infer_instance
  have : IsProper f.toImage := IsProper.of_comp f.toImage f.imageι
  -- The generic point of the image has the dimension of `f η` in `Y`.
  have hη : height (genericPoint f.image) + 1 = height (genericPoint X) := by
    rw [← f.toImage.genericPoint_eq_of_isDominant, ← f.imageι.height_apply_eq_height,
      ← Scheme.Hom.comp_apply, f.toImage_imageι, heq]
  -- Substitute `f = f.toImage ≫ f.imageι`; the two sides differ only in instance arguments.
  have key : ∀ (g : X ⟶ Y) [QuasiCompact g], g = f →
      AlgebraicCycle.map f height height (AlgebraicCycle.div r) =
        AlgebraicCycle.map g height height (AlgebraicCycle.div r) := by
    rintro g _ rfl
    rfl
  rw [key _ f.toImage_imageι, map_height_comp k f.toImage f.imageι,
    map_height_div_eq_zero_of_height_add_one k f.toImage hη r]
  ext y
  rw [map_height_apply k]
  simp

end Chow

end TauCeti.AlgebraicGeometry
