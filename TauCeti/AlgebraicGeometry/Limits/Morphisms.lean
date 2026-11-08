/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Limits.BaseChange
public import TauCeti.AlgebraicGeometry.Limits.Smooth

/-!
# Morphisms over a member and separatedness: inheritance from a finite stage

Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact schemes with affine transition maps, and
let `g : X ⟶ Y` be a morphism of schemes over a member `Sᵢ`, with `Y` quasi-compact over `Sᵢ`. If
the base change `X ×_{Sᵢ} S ⟶ Y ×_{Sᵢ} S` of `g` is a closed immersion, finite, smooth or étale
(under the finiteness assumptions on `g` of the corresponding case `Y = Sᵢ`), then so is its base
change to some `Sⱼ`. These are Stacks, Lemmas 32.8.5 (01ZP), 32.8.3 (01ZO), 32.8.9 (0C0C) and
32.8.10 (07RP) in the form stated there, for a morphism over `Sᵢ`.

They follow from the case `Y = Sᵢ` (`exists_isClosedImmersion_pullback_fst_of_isLimit`, ...): the
base changes of `g` to `S` and to the `Sⱼ` are the base changes of the single morphism
`X ×_Y (Sᵢ ×_{Sᵢ} Y) ⟶ Sᵢ ×_{Sᵢ} Y` to the limit `Y ×_{Sᵢ} S = lim (Y ×_{Sᵢ} Sⱼ)` and to its
members (`exists_pullbackMap_of_pullbackOver`).

For `Y` quasi-compact and quasi-separated over `Sᵢ`, separatedness of `Y ×_{Sᵢ} S ⟶ S` is
inherited by `Y ×_{Sᵢ} Sⱼ ⟶ Sⱼ` for some `j`; proper morphisms are separated, so this is one
ingredient of the inheritance of properness (Stacks, Lemma 32.13.1 (081F)). The base change to any
`T ⟶ Sᵢ` of the diagonal `Y ⟶ Y ×_{Sᵢ} Y` is the diagonal of `Y ×_{Sᵢ} T` over `T`
(`CategoryTheory.MorphismProperty.diagonal_pullback_fst_iff`). The diagonal is quasi-compact
since `Y` is quasi-separated over `Sᵢ`, and as an immersion it is quasi-separated and locally of
finite type, so the descent of closed immersions between schemes over `Sᵢ` applies to it.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.exists_pullbackMap_of_pullbackOver`: the reduction to the
  case `Y = Sᵢ` over the limit `Y ×_{Sᵢ} S = lim (Y ×_{Sᵢ} Sⱼ)`.
* `TauCeti.AlgebraicGeometry.Scheme.exists_isClosedImmersion_pullbackMap_of_isLimit`,
  `exists_isFinite_pullbackMap_of_isLimit`, `exists_smooth_pullbackMap_of_isLimit`,
  `exists_etale_pullbackMap_of_isLimit`: the four properties.
* `TauCeti.AlgebraicGeometry.Scheme.exists_isSeparated_pullback_fst_of_isLimit`: separatedness is
  inherited from the limit.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)] {c : Cone D}
  (hc : IsLimit c)

include hc in
/-- Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact schemes with affine transition maps,
and `g : X ⟶ Y` a quasi-compact, quasi-separated morphism, locally of finite type, of schemes over
a member `Sᵢ`, with `Y` quasi-compact over `Sᵢ`. If the base change of `g` to `S` is a closed
immersion, then so is its base change to some `Sⱼ`. Stacks, Lemma 32.8.5 (01ZP). -/
theorem exists_isClosedImmersion_pullbackMap_of_isLimit {i : I} {X Y : Scheme.{u}}
    {p : X ⟶ D.obj i} {q : Y ⟶ D.obj i} [QuasiCompact q] (g : X ⟶ Y) [QuasiCompact g]
    [QuasiSeparated g] [LocallyOfFiniteType g] (hg : g ≫ q = p)
    [IsClosedImmersion
      (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg]))] :
    ∃ (j : I) (hji : j ⟶ i), IsClosedImmersion
      (pullback.map (D.map hji) p (D.map hji) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])) :=
  exists_pullbackMap_of_pullbackOver c @IsClosedImmersion g hg
    (fun h ↦ have := h; exists_isClosedImmersion_pullback_fst_of_isLimit (hc.pullbackOver q) _)
    ‹_›

include hc in
/-- Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact schemes with affine transition maps,
and `g : X ⟶ Y` a quasi-compact, quasi-separated morphism, locally of finite type, of schemes over
a member `Sᵢ`, with `Y` quasi-compact over `Sᵢ`. If the base change of `g` to `S` is finite, then
so is its base change to some `Sⱼ`. Stacks, Lemma 32.8.3 (01ZO). -/
theorem exists_isFinite_pullbackMap_of_isLimit {i : I} {X Y : Scheme.{u}}
    {p : X ⟶ D.obj i} {q : Y ⟶ D.obj i} [QuasiCompact q] (g : X ⟶ Y) [QuasiCompact g]
    [QuasiSeparated g] [LocallyOfFiniteType g] (hg : g ≫ q = p)
    [IsFinite
      (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg]))] :
    ∃ (j : I) (hji : j ⟶ i), IsFinite
      (pullback.map (D.map hji) p (D.map hji) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])) :=
  -- Instance search does not find `RespectsIso @IsFinite` from stability under base change.
  have : MorphismProperty.RespectsIso @IsFinite.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exists_pullbackMap_of_pullbackOver c @IsFinite g hg
    (fun h ↦ have := h; exists_isFinite_pullback_fst_of_isLimit (hc.pullbackOver q) _) ‹_›

include hc in
/-- Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact schemes with affine transition maps,
and `g : X ⟶ Y` a quasi-compact, quasi-separated morphism, locally of finite presentation, of
schemes over a member `Sᵢ`, with `Y` quasi-compact over `Sᵢ`. If the base change of `g` to `S` is
smooth, then so is its base change to some `Sⱼ`. Stacks, Lemma 32.8.9 (0C0C). -/
theorem exists_smooth_pullbackMap_of_isLimit {i : I} {X Y : Scheme.{u}}
    {p : X ⟶ D.obj i} {q : Y ⟶ D.obj i} [QuasiCompact q] (g : X ⟶ Y) [QuasiCompact g]
    [QuasiSeparated g] [LocallyOfFinitePresentation g] (hg : g ≫ q = p)
    [Smooth (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg]))] :
    ∃ (j : I) (hji : j ⟶ i), Smooth
      (pullback.map (D.map hji) p (D.map hji) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])) :=
  -- Instance search does not find `RespectsIso @Smooth` from stability under base change.
  have : MorphismProperty.RespectsIso @Smooth.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exists_pullbackMap_of_pullbackOver c @Smooth g hg
    (fun h ↦ have := h; exists_smooth_pullback_fst_of_isLimit (hc.pullbackOver q) _) ‹_›

include hc in
/-- Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact schemes with affine transition maps,
and `g : X ⟶ Y` a quasi-compact, quasi-separated morphism, locally of finite presentation, of
schemes over a member `Sᵢ`, with `Y` quasi-compact over `Sᵢ`. If the base change of `g` to `S` is
étale, then so is its base change to some `Sⱼ`. Stacks, Lemma 32.8.10 (07RP). -/
theorem exists_etale_pullbackMap_of_isLimit {i : I} {X Y : Scheme.{u}}
    {p : X ⟶ D.obj i} {q : Y ⟶ D.obj i} [QuasiCompact q] (g : X ⟶ Y) [QuasiCompact g]
    [QuasiSeparated g] [LocallyOfFinitePresentation g] (hg : g ≫ q = p)
    [Etale (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg]))] :
    ∃ (j : I) (hji : j ⟶ i), Etale
      (pullback.map (D.map hji) p (D.map hji) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])) :=
  -- Instance search does not find `RespectsIso @Etale` from stability under base change.
  have : MorphismProperty.RespectsIso @Etale.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exists_pullbackMap_of_pullbackOver c @Etale g hg
    (fun h ↦ have := h; exists_etale_pullback_fst_of_isLimit (hc.pullbackOver q) _) ‹_›

include hc in
/-- Let `S = lim Sⱼ` be a cofiltered limit of quasi-compact schemes with affine transition maps,
and `Y` a quasi-compact and quasi-separated scheme over a member `Sᵢ`. If the base
change `Y ×_{Sᵢ} S ⟶ S` is separated, then so is `Y ×_{Sᵢ} Sⱼ ⟶ Sⱼ` for some `j`. -/
theorem exists_isSeparated_pullback_fst_of_isLimit {i : I} {Y : Scheme.{u}}
    (q : Y ⟶ D.obj i) [QuasiCompact q] [QuasiSeparated q]
    [IsSeparated (pullback.fst (c.π.app i) q)] :
    ∃ (j : I) (hji : j ⟶ i), IsSeparated (pullback.fst (D.map hji) q) := by
  have := (MorphismProperty.diagonal_pullback_fst_iff (P := @IsClosedImmersion) (c.π.app i) q).mp
    ((isSeparated_iff _).mp ‹_›)
  obtain ⟨j, hji, h⟩ := exists_isClosedImmersion_pullbackMap_of_isLimit hc
    (p := q) (q := pullback.snd q q ≫ q) (pullback.diagonal q) (by simp)
  exact ⟨j, hji, (isSeparated_iff _).mpr
    ((MorphismProperty.diagonal_pullback_fst_iff (P := @IsClosedImmersion) (D.map hji) q).mpr h)⟩

end TauCeti.AlgebraicGeometry.Scheme
