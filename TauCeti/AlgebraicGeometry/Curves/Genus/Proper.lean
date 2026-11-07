/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.FlatBaseChange

/-!
# The genus of a proper scheme under extension of the base field

Let `X` be a proper scheme over a field `k` with `H⁰(X, 𝒪_X) = k`, and let `X_K = X ×_k K` be its
base change to a field extension `K / k`. Then `H⁰(X_K, 𝒪) = K` and `X_K` has the genus of `X`
(Stacks, Lemma 0BY9).

Both follow from flat base change of cohomology
(`TauCeti.AlgebraicGeometry.finrank_cohomology_pullback_eq_of_isPullback`): on a quasi-compact
scheme with affine diagonal, for instance a proper one, `dim_K Hⁿ(X_K, 𝒪) = dim_k Hⁿ(X, 𝒪)` for
every `n`. No smoothness, reducedness, irreducibility or dimension hypothesis is needed, which
matters because `X_K` need not be reduced or irreducible when `K / k` is inseparable.

The hypothesis `H⁰(X, 𝒪_X) = k` cannot be dropped from the conclusion `H⁰(X_K, 𝒪) = K`: for
`X = ℙ¹_L` viewed as a `k`-scheme with `L / k` finite of degree `> 1`, the ring
`H⁰(X_L, 𝒪) = L ⊗_k L` has dimension `[L : k] > 1` over `L`.

## Main declarations

* `TauCeti.AlgebraicGeometry.finrank_cohomology_trivial_pullback_eq_of_isPullback`: the dimension
  of `Hⁿ(X, 𝒪_X)` is unchanged by extension of the base field;
* `TauCeti.AlgebraicGeometry.Curve.baseChange`: the base change `X ×_k K` of a `k`-scheme;
* `TauCeti.AlgebraicGeometry.Curve.genus_baseChange`: for `X` proper over `k` with
  `H⁰(X, 𝒪_X) = k`, `H⁰(X_K, 𝒪) = K` and `X_K` has the genus of `X`.

## References

* [The Stacks Project, Lemma 0BY9](https://stacks.math.columbia.edu/tag/0BY9).
* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3 (flat base change).
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open Module (finrank)

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

section IsPullback

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of K))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))

include H in
/-- The dimension of `Hⁿ(X, 𝒪_X)` does not change under extension of the base field, on a
quasi-compact scheme with affine diagonal, for instance a proper scheme over `k`. -/
theorem finrank_cohomology_trivial_pullback_eq_of_isPullback [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (n : ℕ) :
    finrank K (Scheme.Modules.Cohomology (InvertibleSheaf.trivial Y).obj n) =
      finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj n) := by
  let e : (Scheme.Modules.pullback g).obj (InvertibleSheaf.trivial X).obj ≅
      (InvertibleSheaf.trivial Y).obj :=
    (Scheme.Modules.pullback g).mapIso (InvertibleSheaf.trivialObjIsoUnit X) ≪≫
      Scheme.Modules.pullbackObjUnitIso g ≪≫ (InvertibleSheaf.trivialObjIsoUnit Y).symm
  rw [← Scheme.Modules.finrank_cohomology_congr K e n,
    finrank_cohomology_pullback_eq_of_isPullback H]

end IsPullback

namespace Curve

variable (k : Type u) [Field k]

/-- The base change `X ×_k K` of a scheme `X` over `k` along a field extension `k → K`. -/
abbrev baseChange (X : Scheme.{u}) [X.Over (Spec (.of k))] (K : Type u) [Field K]
    [Algebra k K] : Scheme.{u} :=
  pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-- The base change `X ×_k K` is a scheme over `K` through its second projection. -/
instance (X : Scheme.{u}) [X.Over (Spec (.of k))] (K : Type u) [Field K] [Algebra k K] :
    (baseChange k X K).Over (Spec (.of K)) :=
  ⟨pullback.snd _ _⟩

/-- **A proper scheme with `H⁰(X, 𝒪_X) = k` keeps `H⁰ = K` and its genus after any extension
`K / k` of the base field.** Neither the dimension of `X` nor its reducedness or irreducibility
matters. Stacks, Lemma 0BY9. -/
theorem genus_baseChange (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
    (hH0 : finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 0) = 1)
    (K : Type u) [Field K] [Algebra k K]
    [FiniteDimensional K
      (Scheme.Modules.Cohomology (InvertibleSheaf.trivial (baseChange k X K)).obj 1)] :
    finrank K (Scheme.Modules.Cohomology (InvertibleSheaf.trivial (baseChange k X K)).obj 0) = 1 ∧
      (baseChange k X K).genus K = X.genus k := by
  have H : IsPullback (pullback.fst _ _) (baseChange k X K ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    IsPullback.of_hasPullback _ _
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from (X ↘ Spec (.of k))]
    infer_instance
  refine ⟨(finrank_cohomology_trivial_pullback_eq_of_isPullback H 0).trans hH0, ?_⟩
  rw [Scheme.genus_def, Scheme.genus_def, finrank_cohomology_trivial_pullback_eq_of_isPullback H]

end Curve

end

end TauCeti.AlgebraicGeometry
