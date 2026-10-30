/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Separation and affineness of limits with affine transition maps

Let `D : I ⥤ Scheme` be a cofiltered diagram whose transition maps are affine, with limit cone
`c`. Mathlib shows that each projection `c.π.app i` is affine (`isAffineHom_π_app`) and that the
limit of quasi-compact schemes is quasi-compact (`Scheme.compactSpace_of_isLimit`). Since an
affine morphism is separated, separation and quasi-separation of a single member pass to the
limit (Stacks, Lemma 32.2.2 (01YX) with Morphisms, Lemma 29.11.2 (01S7)). Likewise affineness
and quasi-affineness pass from a member to the limit; combined with Mathlib's converses
(Stacks, Tags 01Z5 and 01Z6), for qcqs members the limit is affine
(quasi-affine) if and only if some member is.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.isSeparated_of_isLimit`: the limit is separated as soon as
  some member is.
* `TauCeti.AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_isLimit`: the limit is
  quasi-separated as soon as some member is.
* `TauCeti.AlgebraicGeometry.Scheme.isAffine_iff_exists_of_isLimit`: for qcqs members, the
  limit is affine if and only if some member is.
* `TauCeti.AlgebraicGeometry.Scheme.isQuasiAffine_iff_exists_of_isLimit`: for qcqs members, the
  limit is quasi-affine if and only if some member is.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {c : Cone D} (hc : IsLimit c)

include hc in
/-- The limit of a cofiltered diagram of schemes with affine transition maps is separated as soon
as one member is. Stacks, Lemma 32.2.2 (01YX). -/
theorem isSeparated_of_isLimit (i : I) [(D.obj i).IsSeparated] : c.pt.IsSeparated := by
  have := isAffineHom_π_app D c hc i
  have : IsSeparated (c.π.app i) := .of_isAffineHom _
  refine ⟨?_⟩
  rw [terminal.hom_ext (terminal.from c.pt) (c.π.app i ≫ terminal.from (D.obj i))]
  infer_instance

include hc in
/-- The limit of a cofiltered diagram of schemes with affine transition maps is quasi-separated as
soon as one member is. Stacks, Lemma 32.2.2 (01YX). -/
theorem quasiSeparatedSpace_of_isLimit (i : I) [QuasiSeparatedSpace (D.obj i)] :
    QuasiSeparatedSpace c.pt := by
  have := isAffineHom_π_app D c hc i
  have : IsSeparated (c.π.app i) := .of_isAffineHom _
  exact quasiSeparatedSpace_of_quasiSeparated (c.π.app i)

include hc in
/-- The limit of a cofiltered diagram of schemes with affine transition maps is affine as soon as
one member is. -/
theorem isAffine_of_isLimit (i : I) [IsAffine (D.obj i)] : IsAffine c.pt :=
  have := isAffineHom_π_app D c hc i
  isAffine_of_isAffineHom (c.π.app i)

include hc in
/-- The limit of a cofiltered diagram of schemes with affine transition maps is quasi-affine as
soon as one member is. -/
theorem isQuasiAffine_of_isLimit (i : I) [(D.obj i).IsQuasiAffine] : c.pt.IsQuasiAffine :=
  have := isAffineHom_π_app D c hc i
  .of_isAffineHom (c.π.app i)

include hc in
/-- The limit of a cofiltered diagram of quasi-compact quasi-separated schemes with affine
transition maps is affine if and only if some member is. Stacks, Tag 01Z6. -/
theorem isAffine_iff_exists_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] : IsAffine c.pt ↔ ∃ i, IsAffine (D.obj i) :=
  ⟨fun _ ↦ Scheme.exists_isAffine_of_isLimit D c hc,
    fun ⟨i, _⟩ ↦ isAffine_of_isLimit hc i⟩

include hc in
/-- The limit of a cofiltered diagram of quasi-compact quasi-separated schemes with affine
transition maps is quasi-affine if and only if some member is. Stacks, Tag 01Z5. -/
theorem isQuasiAffine_iff_exists_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] : c.pt.IsQuasiAffine ↔ ∃ i, (D.obj i).IsQuasiAffine :=
  ⟨fun _ ↦ Scheme.exists_isQuasiAffine_of_isLimit D c hc,
    fun ⟨i, _⟩ ↦ isQuasiAffine_of_isLimit hc i⟩

end TauCeti.AlgebraicGeometry.Scheme
