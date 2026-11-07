/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Automorphy

/-!
# Local sections of the automorphy sheaf from functions of the quotient coordinate

Let `ψ` be a local linearizing coordinate at a point `z` of the upper half-plane for a subgroup `Γ`
of `PSL(2, ℝ)`, with coordinate `u`, local quotient coordinate `w = u ^ m`
(`m = Nat.card (stabilizer Γ z)`) and frame
`Subgroup.LinearizingCoordinate.automorphyFrame ψ k r τ = (τ - conj z) ^ (-k) * u ^ r`.
The file `TauCeti.Analysis.Complex.Fuchsian.Elliptic.Automorphy` writes every local section `f` of
the weight-`k` automorphy sheaf on the invariant disc as the frame times a holomorphic function of
`w`, its coefficient `Subgroup.LinearizingCoordinate.automorphyDescent ψ k r f`. This file proves
the converse, so that the local sections at an elliptic point are *exactly* the frame times the
holomorphic functions of the quotient coordinate: this is the local description, by invariant
sections in the linearizing coordinate, of the invertible sheaf on the coarse quotient that the
weight-`k` transformation data induces (Diamond–Shurman §§3.5–3.6).

For a function `G` of the quotient coordinate, `Subgroup.LinearizingCoordinate.automorphySection
ψ k r G` is the function `τ ↦ (τ - conj z) ^ (-k) * u ^ r * G (u ^ m)` on the upper half-plane.

* If `G` is holomorphic on the set of quotient-coordinate values, this function is holomorphic on
  the invariant disc (`Subgroup.LinearizingCoordinate.mdifferentiableOn_automorphySection`).
* It satisfies the weight-`k` transformation law for the elements `g` of a subgroup `Γ'` of
  `SL(2, ℝ)` fixing `z`, as soon as these lift elements of `Γ` and
  `denom g z ^ (2 * r + k) = 1` (`Subgroup.LinearizingCoordinate.automorphySection_smul`).
* Its coefficient is `G`
  (`Subgroup.LinearizingCoordinate.eqOn_automorphyDescent_automorphySection`), and every local
  section is the section of its coefficient
  (`Subgroup.LinearizingCoordinate.automorphySection_automorphyDescent`).

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §§2.3, 3.5–3.6.
-/

public section

noncomputable section

open Metric MulAction Set UpperHalfPlane TauCeti

open scoped ComplexConjugate Manifold MatrixGroups

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)} {z : ℍ} {ε : ℝ}

namespace LinearizingCoordinate

variable [Finite (stabilizer Γ z)] (ψ : Γ.LinearizingCoordinate z ε)

/-- **The local section of the weight-`k` automorphy sheaf with coefficient `G`**: the function
`τ ↦ (τ - conj z) ^ (-k) * u ^ r * G (u ^ m)` on the upper half-plane, for `u` the coordinate of
`ψ` and `m = Nat.card (stabilizer Γ z)`. On the invariant disc it is the frame
`Subgroup.LinearizingCoordinate.automorphyFrame ψ k r` times `G` of the local quotient coordinate
(`Subgroup.LinearizingCoordinate.automorphySection_coe`). -/
def automorphySection (k : ℤ) (r : ℕ) (G : ℂ → ℂ) (τ : ℍ) : ℂ :=
  ((τ : ℂ) - conj (z : ℂ)) ^ (-k) * ψ.toEquiv (UpperHalfPlane.discCoordinate z τ) ^ r *
    G (ψ.toEquiv (UpperHalfPlane.discCoordinate z τ) ^ Nat.card (stabilizer Γ z))

theorem automorphySection_def (k : ℤ) (r : ℕ) (G : ℂ → ℂ) (τ : ℍ) :
    ψ.automorphySection k r G τ =
      ((τ : ℂ) - conj (z : ℂ)) ^ (-k) * ψ.toEquiv (UpperHalfPlane.discCoordinate z τ) ^ r *
        G (ψ.toEquiv (UpperHalfPlane.discCoordinate z τ) ^ Nat.card (stabilizer Γ z)) :=
  (rfl)

/-- On the invariant disc, the local section with coefficient `G` is the frame times `G` of the
local quotient coordinate. -/
theorem automorphySection_coe (k : ℤ) (r : ℕ) (G : ℂ → ℂ) (τ : stabilizerBall Γ z ε) :
    ψ.automorphySection k r G τ = ψ.automorphyFrame k r τ * G (ψ.quotientCoordinate τ) := by
  rw [automorphySection_def, automorphyFrame_eq_toEquiv_discCoordinate, quotientCoordinate_def,
    coordinate_def]

variable {Γ' : Subgroup SL(2, ℝ)} {k : ℤ} {r : ℕ} {G : ℂ → ℂ}

/-- **The local section with a holomorphic coefficient is holomorphic** on the invariant disc. -/
theorem mdifferentiableOn_automorphySection (hG : DifferentiableOn ℂ G ψ.quotientImage) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (ψ.automorphySection k r G) (ball z ε) := fun τ hτ ↦ by
  let w : ℍ → ℂ := fun τ ↦ ψ.toEquiv (UpperHalfPlane.discCoordinate z τ) ^ Nat.card (stabilizer Γ z)
  have hw : w τ ∈ ψ.quotientImage :=
    (ψ.mem_quotientImage_iff _).mpr ⟨⟨τ, (mem_stabilizerBall Γ z ε).2 (mem_ball.mp hτ)⟩, by
      rw [quotientCoordinate_def, coordinate_def]⟩
  have hGw : MDiffAt (G ∘ w) τ :=
    ((hG _ hw).differentiableAt (ψ.isOpen_quotientImage.mem_nhds hw)).comp_mdifferentiableAt
      ((ψ.mdifferentiableOn_quotientCoordinate τ hτ).mdifferentiableAt (isOpen_ball.mem_nhds hτ))
  exact ((((ψ.mdifferentiableOn_automorphyFrame k r) τ hτ).mdifferentiableAt
    (isOpen_ball.mem_nhds hτ)).mul hGw).mdifferentiableWithinAt

/-- **The transformation law of the local section with coefficient `G`.** If the elements of `Γ'`
fixing `z` lift elements of `Γ` and satisfy `denom g z ^ (2 * r + k) = 1`, then the local section
with any coefficient satisfies the weight-`k` transformation law for them on the invariant disc. -/
theorem automorphySection_smul (hΓ' : Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))) ≤ Γ)
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    {g : SL(2, ℝ)} (hg : g ∈ Γ') (hgz : g • z = z) {τ : ℍ} (hτ : τ ∈ ball z ε) :
    ψ.automorphySection k r G (g • τ) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * ψ.automorphySection k r G τ := by
  let q : stabilizer Γ z :=
    ⟨⟨g, hΓ' (Subgroup.mem_map_of_mem _ hg)⟩, by
      change ((g : PSL(2, ℝ))) • z = z
      rw [pslMk_smul, hgz]⟩
  let σ : stabilizerBall Γ z ε := ⟨τ, (mem_stabilizerBall Γ z ε).2 (mem_ball.mp hτ)⟩
  have hgq : (g : PSL(2, ℝ)) = ((q : Γ) : PSL(2, ℝ)) := rfl
  have h := coe_smul_stabilizerBall_of_coe_eq q hgq σ
  change ψ.automorphySection k r G (g • (σ : ℍ)) =
    denom (Matrix.SpecialLinearGroup.mapGL ℝ g) (σ : ℍ) ^ k * ψ.automorphySection k r G σ
  rw [← h, automorphySection_coe, automorphySection_coe, ψ.automorphyFrame_smul k r q hgq
    (hk g hg hgz), quotientCoordinate_smul, mul_assoc]

/-- **The coefficient of the local section with coefficient `G` is `G`** on the set of local
quotient-coordinate values, when `r < m`, the subgroup `Γ` is the image of `Γ'` near `z`, and
`denom g z ^ (2 * r + k) = 1` for the elements `g ∈ Γ'` fixing `z`. -/
theorem eqOn_automorphyDescent_automorphySection
    (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))))
    (hΓ' : Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))) ≤ Γ)
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hr : r < Nat.card (stabilizer Γ z)) (hG : DifferentiableOn ℂ G ψ.quotientImage) :
    EqOn G (ψ.automorphyDescent k r (ψ.automorphySection k r G)) ψ.quotientImage :=
  ψ.eqOn_automorphyDescent hΓ hk (fun _ hg hgz _ hτ ↦ ψ.automorphySection_smul hΓ' hk hg hgz hτ)
    (ψ.mdifferentiableOn_automorphySection hG) hr hG.continuousOn
    fun τ ↦ ψ.automorphySection_coe k r G τ

/-- **Every local section is the local section with its coefficient**: under the hypotheses of
`Subgroup.LinearizingCoordinate.automorphyFrame_mul_automorphyDescent`, a local section `f` of the
weight-`k` automorphy sheaf agrees on the invariant disc with the local section whose coefficient
is `Subgroup.LinearizingCoordinate.automorphyDescent ψ k r f`. -/
theorem automorphySection_automorphyDescent {f : ℍ → ℂ}
    (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hf : ∀ g ∈ Γ', g • z = z → ∀ τ ∈ ball z ε,
      f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (ball z ε)) (hr : r < Nat.card (stabilizer Γ z)) :
    EqOn (ψ.automorphySection k r (ψ.automorphyDescent k r f)) f (ball z ε) := fun τ hτ ↦ by
  let σ : stabilizerBall Γ z ε := ⟨τ, (mem_stabilizerBall Γ z ε).2 (mem_ball.mp hτ)⟩
  change ψ.automorphySection k r (ψ.automorphyDescent k r f) σ = f σ
  rw [automorphySection_coe, ψ.automorphyFrame_mul_automorphyDescent hΓ hk hf hfd hr]

end LinearizingCoordinate

end Subgroup
