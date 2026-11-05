/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Module

/-!
# Inclusions of ideal sheaves

For ideal sheaves `J ≤ I` on a scheme `X`, the sections of `J` over every open are sections of
`I` (`Scheme.IdealSheafData.sections_mono`), so the ideal sheaf `J`, as an `𝒪_X`-module, includes
into `I` (`Scheme.IdealSheafData.sheafOfLE`). The inclusion is a monomorphism compatible with the
inclusions into `𝒪_X`, and it is functorial in the inequality.

## Main declarations

* `Scheme.IdealSheafData.sections_mono`: the sections of ideal sheaves are monotone;
* `Scheme.IdealSheafData.sheafOfLE`: the inclusion `J ⟶ I` of ideal sheaves for `J ≤ I`, with
  `sheafOfLE_sheafι`, `sheafOfLE_refl` and `sheafOfLE_comp`;
* `Scheme.IdealSheafData.eqToHom_sheafι`: transport along an equality of ideal sheaves commutes
  with the inclusions into `𝒪_X`.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

variable {X : Scheme.{u}} {I J K : X.IdealSheafData}

/-- The sections of ideal sheaves are monotone: a regular function on `U` lying in `J` lies in
every larger ideal sheaf `I`. -/
lemma sections_mono (h : J ≤ I) (U : X.Opens) : J.sections U ≤ I.sections U := by
  intro s hs
  -- Membership is local, and over an affine open the sections are the ideals compared by `h`.
  refine I.mem_sections_of_forall_exists fun x hx ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  refine ⟨V, homOfLE hVU, hxV, ?_⟩
  have hJ := J.map_mem_sections (homOfLE hVU) hs
  have hJV := J.sections_eq_ideal ⟨V, hV⟩
  have hIV := I.sections_eq_ideal ⟨V, hV⟩
  dsimp only at hJV hIV
  rw [hJV] at hJ
  rw [hIV]
  exact h _ hJ

/-- The inclusion `J ⟶ I` of ideal sheaves for `J ≤ I`, as a morphism of `𝒪_X`-modules. -/
def sheafOfLE (h : J ≤ I) : J.sheaf ⟶ I.sheaf :=
  I.sheafLift J.sheafι fun U s ↦ sections_mono h U (J.sheafι_app_mem U s)

/-- The inclusion `J ⟶ I` commutes with the inclusions into `𝒪_X`. -/
@[simp]
lemma sheafOfLE_sheafι (h : J ≤ I) : sheafOfLE h ≫ I.sheafι = J.sheafι :=
  I.sheafLift_ι _ _

instance mono_sheafOfLE (h : J ≤ I) : Mono (sheafOfLE h) :=
  have : Mono (sheafOfLE h ≫ I.sheafι) := by
    rw [sheafOfLE_sheafι]
    infer_instance
  mono_of_mono _ I.sheafι

/-- The inclusion of an ideal sheaf into itself is the identity. -/
@[simp]
lemma sheafOfLE_refl : sheafOfLE (le_refl I) = 𝟙 I.sheaf := by
  rw [← cancel_mono I.sheafι, sheafOfLE_sheafι]
  exact (Category.id_comp (obj := X.Modules) _).symm

/-- The inclusions of ideal sheaves compose. -/
@[reassoc (attr := simp)]
lemma sheafOfLE_comp (h₁ : K ≤ J) (h₂ : J ≤ I) :
    sheafOfLE h₁ ≫ sheafOfLE h₂ = sheafOfLE (h₁.trans h₂) := by
  rw [← cancel_mono I.sheafι, sheafOfLE_sheafι]
  exact (Category.assoc (obj := X.Modules) _ _ _).trans (by
    rw [sheafOfLE_sheafι, sheafOfLE_sheafι])

/-- Transport of an ideal sheaf along an equality commutes with the inclusions into `𝒪_X`. -/
@[simp, reassoc]
lemma eqToHom_sheafι {J₁ J₂ : X.IdealSheafData} (h : J₁ = J₂) :
    eqToHom (congrArg sheaf h) ≫ J₂.sheafι = J₁.sheafι := by
  subst h
  exact Category.id_comp _

end

end AlgebraicGeometry.Scheme.IdealSheafData
