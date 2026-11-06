/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.PoleSheaf.FiltrationQuotient
public import TauCeti.RingTheory.LocalRing.QuotientComplement

/-!
# Sections of exact pole order over a local ring

Let `W` be an elliptic Weierstrass curve over a local ring `R`, and let `n ≥ 2`. The quotient
`H⁰(𝒪(n[0])) ⧸ H⁰(𝒪((n - 1)[0]))` of the pole filtration is finite projective of rank one
(`WeierstrassCurve.projective_quotient_range_cohomologyMapBaseLinear_poleSheafMap`), hence free of
rank one. So there is a section `s` of `𝒪(n[0])` with
`H⁰(𝒪(n[0])) = H⁰(𝒪((n - 1)[0])) ⊕ R s`: a section of exact pole order `n` at the zero section.

For `n = 2` and `n = 3` these are the sections `x` and `y` from which the Weierstrass presentation
of a pointed genus-one curve is built (Katz–Mazur 2.1). Over a general base they exist Zariski
locally, after localising at a point.

## Main results

* `WeierstrassCurve.exists_isCompl_range_cohomologyMapBaseLinear_poleSheafMap`: over a local
  ring, `H⁰(𝒪((n - 1)[0]))` has a complement in `H⁰(𝒪(n[0]))` spanned by one linearly independent
  section, for `n ≥ 2`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1.
-/

public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules TauCeti TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R) [W.IsElliptic]
  {n : ℕ}

/-- **Sections of exact pole order `n`**: over a local ring `R` and for `n ≥ 2`, the image of
`H⁰(projModel W, 𝒪((n - 1)[0]))` in `H⁰(projModel W, 𝒪(n[0]))` has a complement `R ∙ s` spanned by
a linearly independent section `s`. For `n = 2, 3` this gives the Weierstrass coordinates `x`
and `y`. -/
theorem exists_isCompl_range_cohomologyMapBaseLinear_poleSheafMap (hn : 2 ≤ n) :
    ∃ s : Cohomology (W.poleSheaf n).obj 0,
      IsCompl (LinearMap.range
        (cohomologyMapBaseLinear R W.projModel (W.poleSheafMap (n.sub_le 1)).hom 0)) (R ∙ s) ∧
      LinearIndependent R ![s] := by
  have hm : 0 < n - 1 := by omega
  have := W.finitePresentation_cohomology_zero_poleSheaf (n := n) (by omega)
  have := W.projective_quotient_range_cohomologyMapBaseLinear_poleSheafMap hm (n.sub_le 1)
  refine IsLocalRing.exists_isCompl_span_singleton_of_rankAtStalk_eq_one _ ?_
  rw [W.rankAtStalk_quotient_range_cohomologyMapBaseLinear_poleSheafMap hm (n.sub_le 1)]
  omega

end WeierstrassCurve
