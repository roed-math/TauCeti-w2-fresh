/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.Support
import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-!
# Cohomology with supports on affine schemes

Let `X` be an affine scheme, `Z ⊆ X` a closed subset and `M` a quasi-coherent sheaf of
`𝒪_X`-modules. Serre's vanishing theorem `subsingleton_cohomologyOn_succ_of_isAffineOpen` kills
`H^q(X, M)` for `q ≥ 1`, so the long exact sequence of the pair `(X, X ∖ Z)`

`0 ⟶ H_Z^0(X, M) ⟶ M(X) ⟶ M(X ∖ Z) ⟶ H_Z^1(X, M) ⟶ 0`, `H_Z^{q+1}(X, M) ≃ H^q(X ∖ Z, M)`

computes cohomology with supports from the open complement (Stacks, Section 20.34 (0G6Y)). In
degree one, `H_Z^1(X, M)` is the group of sections over `X ∖ Z` modulo restrictions of global
sections. If `X ∖ Z` is affine too, for example the complement `D(f)` of the zero locus `V(f)` of
a global function, then `H_Z^q(X, M)` vanishes for `q ≥ 2`.

## Main declarations

* `Scheme.Modules.cohomologyWithSupportOneEquiv`: `M(X ∖ Z) / M(X) ≃+ H_Z^1(X, M)` for affine `X`;
* `Scheme.Modules.subsingleton_cohomologyWithSupport_add_two`: `H_Z^{n+2}(X, M) = 0` when `X` and
  `X ∖ Z` are affine, and `Scheme.Modules.subsingleton_cohomologyWithSupport_basicOpen_add_two`,
  its case `Z = V(f)`.
-/

public section

open CategoryTheory TopologicalSpace AlgebraicGeometry Scheme.Modules Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}} (Z : Closeds X) (M : X.Modules) [M.IsQuasicoherent]

/-- On an affine scheme, the degree-one cohomology `H_Z^1(X, M)` of a quasi-coherent sheaf with
supports in `Z` is the group of sections of `M` over `X ∖ Z` modulo the restrictions of global
sections, through the connecting map of the pair `(X, X ∖ Z)`. -/
def cohomologyWithSupportOneEquiv [IsAffine X] :
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.obj (op (⊤ ⊓ Z.compl)) ⧸
        (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.map (Z.complInclusion ⊤).op).hom.range
      ≃+ cohomologyWithSupport Z M 1 :=
  CategoryTheory.Sheaf.supportedHOneEquiv _ Z ⊤
    (subsingleton_cohomologyOn_succ_of_isAffineOpen M (isAffineOpen_top X) 0)

/-- The degree-one identification `cohomologyWithSupportOneEquiv` sends a section over `X ∖ Z` to
its image under the connecting map of the pair `(X, X ∖ Z)`. -/
lemma cohomologyWithSupportOneEquiv_mk [IsAffine X]
    (s : ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.obj (op (⊤ ⊓ Z.compl))) :
    cohomologyWithSupportOneEquiv Z M s =
      CategoryTheory.Sheaf.relativeH'.δ _ (Z.complInclusion ⊤) (add_zero 1)
        ((TauCeti.CategoryTheory.cohomologyZeroSectionsEquiv _ _).symm s) :=
  CategoryTheory.Sheaf.supportedHOneEquiv_mk _ Z ⊤ _ s

/-- If both `X` and the complement `X ∖ Z` are affine, a quasi-coherent sheaf has no cohomology
with supports in `Z` in degrees at least two. -/
theorem subsingleton_cohomologyWithSupport_add_two [IsAffine X] (hZ : IsAffineOpen Z.compl)
    (n : ℕ) : Subsingleton (cohomologyWithSupport Z M (n + 2)) :=
  CategoryTheory.Sheaf.relativeH'.subsingleton_add_two _ _
    (subsingleton_cohomologyOn_succ_of_isAffineOpen M (by rwa [top_inf_eq]) n)
    (subsingleton_cohomologyOn_succ_of_isAffineOpen M (isAffineOpen_top X) (n + 1))

/-- On an affine scheme, a quasi-coherent sheaf has no cohomology with supports in the zero locus
`V(f)` of a global function in degrees at least two: the complement `D(f)` is affine. -/
theorem subsingleton_cohomologyWithSupport_basicOpen_add_two [IsAffine X] (f : Γ(X, ⊤)) (n : ℕ) :
    Subsingleton (cohomologyWithSupport (X.basicOpen f).compl M (n + 2)) :=
  subsingleton_cohomologyWithSupport_add_two _ M
    (by rw [Opens.compl_compl]; exact (isAffineOpen_top X).basicOpen f) n

section structureSheaf

variable (r : Γ(X, ⊤))

/-- The complement of the zero locus `V(r)` is the basic open `D(r)`. -/
private lemma top_inf_compl_compl_basicOpen : ⊤ ⊓ (X.basicOpen r).compl.compl = X.basicOpen r := by
  rw [Opens.compl_compl, top_inf_eq]

/-- The functions on `D(r)` as functions on `X ∖ V(r)`. -/
private def basicOpenSectionsAddEquiv :
    Γ(X, X.basicOpen r) ≃+ ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (SheafOfModules.unit X.ringCatSheaf)).obj.obj (op (⊤ ⊓ (X.basicOpen r).compl.compl)) :=
  (X.presheaf.mapIso (eqToIso (top_inf_compl_compl_basicOpen r)).op).commRingCatIsoToRingEquiv
    |>.toAddEquiv

/-- Under `basicOpenSectionsAddEquiv`, the localization map `Γ(X, ⊤) ⟶ Γ(X, D(r))` is
restriction to `X ∖ V(r)`. -/
private lemma basicOpenSectionsAddEquiv_algebraMap (s : Γ(X, ⊤)) :
    basicOpenSectionsAddEquiv r (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen r) s) =
      X.presheaf.map ((X.basicOpen r).compl.complInclusion ⊤).op s := by
  change X.presheaf.map _ (X.presheaf.map _ s) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  -- the two inclusions of opens agree, because `X.Opens` is a thin category
  rfl

variable [IsAffine X]

/-- On an affine scheme, the degree-one cohomology of the structure sheaf with supports in the
zero locus `V(r)` of a global function is `Γ(X, ⊤)_r / Γ(X, ⊤)`: the ring of functions on `D(r)`,
the localization `Γ(X, D(r))` of `Γ(X, ⊤)` away from `r`, modulo global functions. -/
def cohomologyWithSupportBasicOpenOneEquiv :
    Γ(X, X.basicOpen r) ⧸ (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen r)).range.toAddSubgroup ≃+
      cohomologyWithSupport (X.basicOpen r).compl (SheafOfModules.unit X.ringCatSheaf) 1 :=
  (QuotientAddGroup.congr _ (((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (SheafOfModules.unit X.ringCatSheaf)).obj.map
        ((X.basicOpen r).compl.complInclusion ⊤).op).hom.range (basicOpenSectionsAddEquiv r) (by
    ext y
    simp only [AddSubgroup.mem_map, Subring.mem_toAddSubgroup, RingHom.mem_range,
      AddMonoidHom.mem_range]
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (basicOpenSectionsAddEquiv_algebraMap r s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, ⟨s, rfl⟩, basicOpenSectionsAddEquiv_algebraMap r s⟩)).trans
    (cohomologyWithSupportOneEquiv _ _)

/-- On an affine scheme, the structure sheaf has no sections supported in the zero locus `V(r)`
of a nonzerodivisor `r`, so its degree-zero cohomology with supports in `V(r)` vanishes. -/
theorem subsingleton_cohomologyWithSupport_basicOpen_zero (hr : r ∈ nonZeroDivisors Γ(X, ⊤)) :
    Subsingleton
      (cohomologyWithSupport (X.basicOpen r).compl (SheafOfModules.unit X.ringCatSheaf) 0) := by
  refine (cohomologyWithSupportZeroLinearEquiv _ _).toEquiv.subsingleton_congr.2
    ⟨fun a b ↦ Subtype.ext ?_⟩
  have h (s : Γ(X, ⊤))
      (hs : X.presheaf.map ((X.basicOpen r).compl.complInclusion ⊤).op s = 0) : s = 0 := by
    refine IsLocalization.injective (M := Submonoid.powers r) Γ(X, X.basicOpen r)
      (Submonoid.powers_le.2 hr) ((basicOpenSectionsAddEquiv r).injective ?_)
    rw [basicOpenSectionsAddEquiv_algebraMap, map_zero, map_zero]
    exact hs
  have h' (a : sectionsWithSupport (X.basicOpen r).compl (SheafOfModules.unit X.ringCatSheaf)) :
      a.1 = 0 :=
    h _ ((CategoryTheory.Sheaf.mem_supportedSections_iff _).1
      ((mem_sectionsWithSupport_iff _).1 a.2))
  exact (h' a).trans (h' b).symm

end structureSheaf

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
