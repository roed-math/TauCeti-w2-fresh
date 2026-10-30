/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Morphisms from limits to schemes of finite presentation over `ℤ`

Let `D : I ⥤ Scheme` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine
transition maps and limit cone `c`, and let `X` be a scheme locally of finite presentation over
`ℤ`, that is, over the terminal scheme. Mathlib proves, relative to an arbitrary base scheme,
that `Hom(lim Dᵢ, X)` is the filtered colimit of the `Hom(Dᵢ, X)` (Stacks, Proposition 32.6.1
(01ZC)). Over the terminal scheme every compatibility condition with the base holds
automatically, and this file records the absolute statements used by absolute Noetherian
approximation: every morphism `lim Dᵢ ⟶ X` factors through some `Dᵢ`, and two morphisms
`Dᵢ ⟶ X` agreeing on the limit agree at some later stage.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.exists_map_comp_eq_of_isLimit`: two morphisms `Dᵢ ⟶ X` to a
  scheme locally of finite type over `ℤ` that agree on the limit agree on some `Dₖ`.
* `TauCeti.AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_isLimit`: every morphism from the
  limit to a scheme locally of finite presentation over `ℤ` factors through some `Dᵢ`.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {c : Cone D} (hc : IsLimit c) {X : Scheme.{u}}

include hc in
/-- Two morphisms `Dᵢ ⟶ X`, with `X` locally of finite type over `ℤ`, that agree after composing
with the projection from the limit already agree on some `Dₖ`. Stacks, Proposition 32.6.1
(01ZC), injectivity, over `ℤ`. -/
theorem exists_map_comp_eq_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [LocallyOfFiniteType (terminal.from X)] {i : I} (a b : D.obj i ⟶ X)
    (hab : c.π.app i ≫ a = c.π.app i ≫ b) :
    ∃ (k : I) (hki : k ⟶ i), D.map hki ≫ a = D.map hki ≫ b :=
  AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType D
    { app _ := terminal.from _, naturality _ _ _ := terminal.hom_ext _ _ } (terminal.from X) c hc
    a b (terminal.hom_ext _ _) (terminal.hom_ext _ _) hab

include hc in
/-- Every morphism from the limit of a cofiltered diagram of quasi-compact quasi-separated schemes
with affine transition maps to a scheme locally of finite presentation over `ℤ` factors through
some member of the diagram. Stacks, Proposition 32.6.1 (01ZC), surjectivity, over `ℤ`. -/
theorem exists_π_app_comp_eq_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] [LocallyOfFinitePresentation (terminal.from X)]
    (a : c.pt ⟶ X) : ∃ (i : I) (g : D.obj i ⟶ X), c.π.app i ≫ g = a :=
  have ⟨i, g, hg, _⟩ := AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    D { app _ := terminal.from _, naturality _ _ _ := terminal.hom_ext _ _ } (terminal.from X) c hc
    a (by ext; exact terminal.hom_ext _ _)
  ⟨i, g, hg⟩

end TauCeti.AlgebraicGeometry.Scheme
