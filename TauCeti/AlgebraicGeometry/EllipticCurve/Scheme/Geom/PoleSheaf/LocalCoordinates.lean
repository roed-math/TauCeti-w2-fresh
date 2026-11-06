/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PoleSheaf.FiltrationQuotient
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PoleSheaf.LocallyFree
public import TauCeti.RingTheory.LocalRing.QuotientComplement

/-!
# Sections of exact pole order on an elliptic curve, Zariski locally on the base

Let `π : E ⟶ S` be an elliptic curve with pole sheaves `ℒ_n = 𝒪_E(n[0])`, and let `U` be the image
of the base of a pointed Weierstrass chart of `E`. For `n ≥ 2`, the quotient of `Γ(U, π_*ℒ_n)` by
the image of `Γ(U, π_*ℒ_(n-1))` is finite projective of rank one over `Γ(S, U)`. So at every point
`p` of `U` there is a section `s` of `ℒ_n` over `π⁻¹(U)` whose class generates this quotient freely
after inverting some function `g` not vanishing at `p`: `s` has exact pole order `n` at `[0]` over
the basic open `D(g)`.

For `n = 2` and `n = 3` these sections are the Weierstrass coordinates `x` and `y` of the
presentation of a pointed genus-one curve (Katz–Mazur 2.1), chosen on a neighbourhood of any point
of the base.

## Main results

* `EllipticCurveGeom.exists_notMem_bijective_toSpanSingleton_mkQ_range_pushforward_poleSheafMap`:
  for `n ≥ 2` and a prime `p` of `Γ(S, U)`, a section of `π_*ℒ_n` over `U` generates the quotient
  by `π_*ℒ_(n-1)` freely away from some `g ∉ p`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

open Scheme.Modules

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) {n : ℕ}

/-- **Sections of exact pole order `n`, Zariski locally.** Over the image `U` of the base of a
pointed Weierstrass chart of `E`, for `n ≥ 2` and a prime `p` of `Γ(S, U)`, there are a section `s`
of `π_*ℒ_n` over `U` and a function `g ∉ p` such that, after inverting `g`, the class of `s`
freely generates the quotient of `Γ(U, π_*ℒ_n)` by the image of `Γ(U, π_*ℒ_(n-1))`. For `n = 2, 3`
this chooses the Weierstrass coordinates `x` and `y` near `p`. -/
theorem exists_notMem_bijective_toSpanSingleton_mkQ_range_pushforward_poleSheafMap
    (c : PointedWeierstrassChart E.structureMap E.zero) (hn : 2 ≤ n)
    (p : PrimeSpectrum Γ(S, c.baseMap.opensRange)) :
    ∃ s : Γ((pushforward E.structureMap).obj (E.poleSheaf n).obj, c.baseMap.opensRange),
      ∃ g ∉ p.asIdeal, Function.Bijective (LocalizedModule.map (.powers g)
        (LinearMap.toSpanSingleton Γ(S, c.baseMap.opensRange) _
          ((LinearMap.range (((pushforward E.structureMap).map
            (E.poleSheafMap (n.sub_le 1)).hom).appLinear c.baseMap.opensRange)).mkQ s))) := by
  have hm : 0 < n - 1 := by omega
  have hn' := E.finite_projective_sections_poleSheaf c (n := n) (by omega)
  have := (E.finite_projective_sections_pushforward_of_finite_projective_sections
    (E.poleSheaf n).obj c ⟨hn'.1, hn'.2.1⟩).1
  have := E.projective_quotient_range_pushforward_poleSheafMap c hm (n.sub_le 1)
  obtain ⟨x, g, hg, H⟩ := TauCeti.Module.exists_notMem_bijective_localizedModule_map_toSpanSingleton
    p (by rw [E.rankAtStalk_quotient_range_pushforward_poleSheafMap c hm (n.sub_le 1) p]; omega)
  obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective _ x
  exact ⟨s, g, hg, H⟩

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
