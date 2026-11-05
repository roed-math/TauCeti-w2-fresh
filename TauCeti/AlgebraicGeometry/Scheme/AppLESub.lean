/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Thickening

/-!
# Differences of morphisms of schemes on sections

For two morphisms of schemes `l₁ l₂ : Y ⟶ X`, an open `U` of `X` and an open `V` of `Y` lying in
both `l₁ ⁻¹ U` and `l₂ ⁻¹ U`, the difference `x ↦ l₁^♯ x - l₂^♯ x` is an additive map
`Γ(X, U) → Γ(Y, V)`. It satisfies the twisted Leibniz rule
`(l₁ - l₂)(x * y) = l₁^♯ x * (l₁ - l₂) y + l₂^♯ y * (l₁ - l₂) x`, it is compatible with restriction
in `U` and in `V` and with precomposition, and the differences of three morphisms add up. If `l₁`
and `l₂` agree after `f : X ⟶ S`, the difference kills the sections coming from `S`; if they agree
after precomposing with `j : Z ⟶ Y`, it takes values in the kernel of `j^♯`. If moreover `j` is
surjective, `l₁` and `l₂` agree on points, and they are equal as soon as their differences vanish.

When `j` is a first-order thickening, the twist in the Leibniz rule disappears and the
difference of two deformations of a morphism along `j` is a derivation into the ideal of `j`, as
in Stacks, Lemma 37.9.5 (04FJ).

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.appLESub l₁ l₂ U V e₁ e₂`: the additive map
  `Γ(X, U) → Γ(Y, V)`, `x ↦ l₁.appLE U V e₁ x - l₂.appLE U V e₂ x`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.appLESub_mul`: the twisted Leibniz rule.
* `AlgebraicGeometry.Scheme.Hom.appLESub_mul_of_isFirstOrderThickening`: along a first-order
  thickening `j` with `j ≫ l₁ = j ≫ l₂`, the untwisted Leibniz rule.
* `AlgebraicGeometry.Scheme.Hom.appLESub_appLE_eq_zero`: for `l₁ ≫ f = l₂ ≫ f`, the difference
  kills the sections of `S`.
* `AlgebraicGeometry.Scheme.Hom.appLE_appLESub_eq_zero`: for `j ≫ l₁ = j ≫ l₂`, the difference
  takes values in the kernel of `j^♯`.
* `AlgebraicGeometry.Scheme.Hom.eq_iff_appLESub_eq_zero`: for `j` surjective with
  `j ≫ l₁ = j ≫ l₂`, `l₁ = l₂` if and only if all their differences vanish.

## References

* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ).
-/

public section

open CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry (IsFirstOrderThickening)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z S : Scheme.{u}} (l₁ l₂ l₃ : Y ⟶ X)

/-- The difference of two morphisms `l₁ l₂ : Y ⟶ X` on sections: for an open `U` of `X` and an
open `V` of `Y` lying in `l₁ ⁻¹ U` and in `l₂ ⁻¹ U`, the additive map `Γ(X, U) → Γ(Y, V)`,
`x ↦ l₁^♯ x - l₂^♯ x`. -/
noncomputable def appLESub (U : X.Opens) (V : Y.Opens) (e₁ : V ≤ l₁ ⁻¹ᵁ U)
    (e₂ : V ≤ l₂ ⁻¹ᵁ U) : Γ(X, U) →+ Γ(Y, V) :=
  (l₁.appLE U V e₁).hom.toAddMonoidHom - (l₂.appLE U V e₂).hom.toAddMonoidHom

variable {l₁ l₂ l₃} {U U' : X.Opens} {V V' : Y.Opens}

@[simp]
theorem appLESub_apply (e₁ : V ≤ l₁ ⁻¹ᵁ U) (e₂ : V ≤ l₂ ⁻¹ᵁ U) (x : Γ(X, U)) :
    appLESub l₁ l₂ U V e₁ e₂ x = l₁.appLE U V e₁ x - l₂.appLE U V e₂ x :=
  (rfl)

/-- The twisted Leibniz rule of a difference of morphisms. -/
theorem appLESub_mul (e₁ : V ≤ l₁ ⁻¹ᵁ U) (e₂ : V ≤ l₂ ⁻¹ᵁ U) (x y : Γ(X, U)) :
    appLESub l₁ l₂ U V e₁ e₂ (x * y) =
      l₁.appLE U V e₁ x * appLESub l₁ l₂ U V e₁ e₂ y +
        l₂.appLE U V e₂ y * appLESub l₁ l₂ U V e₁ e₂ x := by
  simp only [appLESub_apply, map_mul]
  ring

theorem appLESub_one (e₁ : V ≤ l₁ ⁻¹ᵁ U) (e₂ : V ≤ l₂ ⁻¹ᵁ U) :
    appLESub l₁ l₂ U V e₁ e₂ 1 = 0 := by
  simp

@[simp]
theorem appLESub_self (e₁ e₂ : V ≤ l₁ ⁻¹ᵁ U) : appLESub l₁ l₁ U V e₁ e₂ = 0 := by
  ext x
  simp

/-- The differences of three morphisms add up. -/
theorem appLESub_add_appLESub (e₁ : V ≤ l₁ ⁻¹ᵁ U) (e₂ : V ≤ l₂ ⁻¹ᵁ U) (e₃ : V ≤ l₃ ⁻¹ᵁ U) :
    appLESub l₁ l₂ U V e₁ e₂ + appLESub l₂ l₃ U V e₂ e₃ = appLESub l₁ l₃ U V e₁ e₃ := by
  ext x
  simp

/-- Swapping two morphisms negates their difference. -/
theorem neg_appLESub (e₁ : V ≤ l₁ ⁻¹ᵁ U) (e₂ : V ≤ l₂ ⁻¹ᵁ U) :
    -appLESub l₁ l₂ U V e₁ e₂ = appLESub l₂ l₁ U V e₂ e₁ := by
  ext x
  simp

/-- The difference of two morphisms is compatible with restriction to a smaller open `V' ⊆ V`. -/
theorem appLESub_map (e₁ : V ≤ l₁ ⁻¹ᵁ U) (e₂ : V ≤ l₂ ⁻¹ᵁ U) (e : V' ≤ V) (x : Γ(X, U)) :
    Y.presheaf.map (homOfLE e).op (appLESub l₁ l₂ U V e₁ e₂ x) =
      appLESub l₁ l₂ U V' (e.trans e₁) (e.trans e₂) x := by
  simp only [appLESub_apply, map_sub, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/-- The difference of two morphisms is compatible with restriction to a smaller open `U' ⊆ U`. -/
theorem map_appLESub (e₁ : V ≤ l₁ ⁻¹ᵁ U') (e₂ : V ≤ l₂ ⁻¹ᵁ U') (e : U' ≤ U)
    (x : Γ(X, U)) :
    appLESub l₁ l₂ U' V e₁ e₂ (X.presheaf.map (homOfLE e).op x) =
      appLESub l₁ l₂ U V (e₁.trans (l₁.preimage_mono e)) (e₂.trans (l₂.preimage_mono e)) x := by
  simp only [appLESub_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- If `l₁ ≫ f = l₂ ≫ f`, the difference of `l₁` and `l₂` kills the sections coming from `S`. -/
theorem appLESub_appLE_eq_zero {f : X ⟶ S} (hf : l₁ ≫ f = l₂ ≫ f) {W : S.Opens}
    (e₁ : V ≤ l₁ ⁻¹ᵁ U) (e₂ : V ≤ l₂ ⁻¹ᵁ U) (e : U ≤ f ⁻¹ᵁ W) (s : Γ(S, W)) :
    appLESub l₁ l₂ U V e₁ e₂ (f.appLE W U e s) = 0 := by
  rw [appLESub_apply, sub_eq_zero, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  simp only [hf]

/-- If `j ≫ l₁ = j ≫ l₂`, the difference of `l₁` and `l₂` takes values in the kernel of
`j^♯`. -/
theorem appLE_appLESub_eq_zero {j : Z ⟶ Y} (hj : j ≫ l₁ = j ≫ l₂) {V₀ : Z.Opens}
    (e₁ : V ≤ l₁ ⁻¹ᵁ U) (e₂ : V ≤ l₂ ⁻¹ᵁ U) (e : V₀ ≤ j ⁻¹ᵁ V) (x : Γ(X, U)) :
    j.appLE V V₀ e (appLESub l₁ l₂ U V e₁ e₂ x) = 0 := by
  rw [appLESub_apply, map_sub, sub_eq_zero, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  simp only [hj]

/-- The difference of `g ≫ l₁` and `g ≫ l₂` is the difference of `l₁` and `l₂` followed by
`g^♯`. -/
theorem appLESub_comp {Y' : Scheme.{u}} (g : Y' ⟶ Y) {V₀ : Y'.Opens} (e₁ : V ≤ l₁ ⁻¹ᵁ U)
    (e₂ : V ≤ l₂ ⁻¹ᵁ U) (e : V₀ ≤ g ⁻¹ᵁ V) (x : Γ(X, U)) :
    appLESub (g ≫ l₁) (g ≫ l₂) U V₀ (e.trans (g.preimage_mono e₁))
        (e.trans (g.preimage_mono e₂)) x =
      g.appLE V V₀ e (appLESub l₁ l₂ U V e₁ e₂ x) := by
  rw [appLESub_apply, appLESub_apply, map_sub, ← CategoryTheory.comp_apply,
    ← CategoryTheory.comp_apply, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]

/-- If `j` is a first-order thickening and `j ≫ l₁ = j ≫ l₂`, the difference of `l₁` and `l₂`
satisfies the Leibniz rule along `l₁`: the twist by `l₂` is absorbed by the square-zero ideal of
`j`. -/
theorem appLESub_mul_of_isFirstOrderThickening {j : Z ⟶ Y} [IsFirstOrderThickening j]
    (hj : j ≫ l₁ = j ≫ l₂) (e₁ : V ≤ l₁ ⁻¹ᵁ U) (e₂ : V ≤ l₂ ⁻¹ᵁ U) (x y : Γ(X, U)) :
    appLESub l₁ l₂ U V e₁ e₂ (x * y) =
      l₁.appLE U V e₁ x * appLESub l₁ l₂ U V e₁ e₂ y +
        l₁.appLE U V e₁ y * appLESub l₁ l₂ U V e₁ e₂ x := by
  have hker (z : Γ(X, U)) : j.app V (appLESub l₁ l₂ U V e₁ e₂ z) = 0 := by
    rw [← appLE_eq_app]
    exact appLE_appLESub_eq_zero hj e₁ e₂ le_rfl z
  have hl₂ : l₂.appLE U V e₂ y = l₁.appLE U V e₁ y - appLESub l₁ l₂ U V e₁ e₂ y := by
    rw [appLESub_apply]
    ring
  rw [appLESub_mul, hl₂, sub_mul,
    IsFirstOrderThickening.mul_eq_zero_of_app_eq_zero j (hker y) (hker x), sub_zero]

variable {j : Z ⟶ Y} [Surjective j]

/-- If `j` is surjective and `j ≫ l₁ = j ≫ l₂`, then `l₁` and `l₂` agree on points. -/
theorem apply_eq_of_comp_eq (hj : j ≫ l₁ = j ≫ l₂) (y : Y) : l₁ y = l₂ y := by
  obtain ⟨z, rfl⟩ := j.surjective y
  rw [← Scheme.Hom.comp_apply, hj, Scheme.Hom.comp_apply]

/-- If `j` is surjective and `j ≫ l₁ = j ≫ l₂`, the preimages of an open under `l₁` and `l₂`
agree. -/
theorem preimage_eq_of_comp_eq (hj : j ≫ l₁ = j ≫ l₂) (U : X.Opens) : l₁ ⁻¹ᵁ U = l₂ ⁻¹ᵁ U :=
  Opens.ext <| Set.ext fun y ↦ by
    simp only [SetLike.mem_coe, Scheme.Hom.mem_preimage, apply_eq_of_comp_eq hj y]

/-- If `j` is surjective and `j ≫ l₁ = j ≫ l₂`, then `l₁ = l₂` if and only if all differences
of `l₁` and `l₂` vanish. -/
theorem eq_iff_appLESub_eq_zero (hj : j ≫ l₁ = j ≫ l₂) :
    l₁ = l₂ ↔ ∀ U : X.Opens,
      appLESub l₁ l₂ U (l₂ ⁻¹ᵁ U) (preimage_eq_of_comp_eq hj U).ge le_rfl = 0 := by
  refine ⟨by rintro rfl U; exact appLESub_self _ _, fun H ↦ ?_⟩
  have hbase : l₁.base = l₂.base := by
    ext y
    exact apply_eq_of_comp_eq hj y
  refine Scheme.Hom.ext hbase fun U ↦ ?_
  ext x
  have hx := DFunLike.congr_fun (H U) x
  rw [appLESub_apply, AddMonoidHom.zero_apply, sub_eq_zero, Scheme.Hom.appLE_eq_app] at hx
  exact hx

end AlgebraicGeometry.Scheme.Hom
