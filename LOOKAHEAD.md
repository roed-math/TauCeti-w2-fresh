<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"curve-genus-base-change","main":"12f052f135ad64b77f5eb238c44a85138a7b175d","status":"complete","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: the genus of a proper scheme with H⁰ = k is invariant under field extension"}]}-->

# Lookahead: `curve-genus-base-change` (SchemeAndStackFoundations §3.1)

Built on `main` at `12f052f135ad64b77f5eb238c44a85138a7b175d`.

## Stubs: none

The listed supplier, `qcoh-higher-direct-image-vanishing` (open PR #30322, pinned
`QCoh.higherDirectImage_vanishing`), is **not consumed**. The only cohomological input the target
needs is flat base change of cohomology over a field, and `main` already has it in full generality
(any quasi-compact scheme with affine diagonal, every degree):
`TauCeti.AlgebraicGeometry.finrank_cohomology_pullback_eq_of_isPullback` in
`TauCeti/AlgebraicGeometry/Cohomology/FlatBaseChange.lean`. Hence there is no
`TauCeti/Lookahead/CurveGenusBaseChange/Stubs.lean`, no `sorry` anywhere on the branch, and the
target does not have to wait for its supplier: split 1 can be opened against `main` as it is.

## The target and its pinned form

`Suggested.lean` (SchemeAndStackFoundations, Layer 3) pins:

```lean
theorem genus_baseChange (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
    (hH0 : cohomologyDim k X (structureModule X) 0 = 1)
    (K : Type u) [Field K] [Algebra k K]
    [FiniteDimensional K
      (Scheme.Modules.Cohomology (InvertibleSheaf.trivial (baseChange k X K)).obj 1)] :
    cohomologyDim K (baseChange k X K) (structureModule _) 0 = 1 ∧
      (baseChange k X K).genus K = X.genus k
```

As proved (`TauCeti.AlgebraicGeometry.Curve.genus_baseChange`):

```lean
theorem genus_baseChange (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
    (hH0 : finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 0) = 1)
    (K : Type u) [Field K] [Algebra k K]
    [FiniteDimensional K
      (Scheme.Modules.Cohomology (InvertibleSheaf.trivial (baseChange k X K)).obj 1)] :
    finrank K (Scheme.Modules.Cohomology (InvertibleSheaf.trivial (baseChange k X K)).obj 0) = 1 ∧
      (baseChange k X K).genus K = X.genus k
```

Differences, all generalisations or spelling:

- `hdim : topologicalKrullDim X = 1` is dropped: it is unused (the result holds for every proper
  scheme), and the unused-hypothesis rubric would flag it.
- `cohomologyDim k X F i` is spelled `Module.finrank k (Scheme.Modules.Cohomology F i)` (its
  definition), and `structureModule X = SheafOfModules.unit X.ringCatSheaf` is spelled
  `(InvertibleSheaf.trivial X).obj`, the structure-sheaf spelling `Scheme.genus` and every
  neighbouring genus lemma on `main` use (`Cohomology/Genus.lean`, `Cohomology/BaseChange.lean`,
  `Curves/Genus/BaseChange.lean`). The README's *Lean:* line also names the abbreviations
  `Curve.cohomologyDim` and `Curve.structureModule`; they are not added, as thin wrappers with no
  consumer on `main`. If the port's reviewers want them, they are one line each and the theorem
  restates through them by `rfl`/`trivialObjIsoUnit`.
- `Curve.baseChange` and its `Over (Spec K)` instance are taken verbatim from `Suggested.lean`.
- Namespace: `TauCetiRoadmap.SchemeAndStackFoundations.Curve` becomes
  `TauCeti.AlgebraicGeometry.Curve`, next to the other `TauCeti.AlgebraicGeometry` genus lemmas.

Not on the branch: the README's italic Checks for §3.1 (*genus_baseChange_test_projectiveLine*,
*genus_baseChange_test_inseparable*, *genus_baseChange_test_constant_field*). The constant-field
counterexample (why `H⁰ = k` is essential) is explained in the module docstring but not formalised;
it needs `H⁰(ℙ¹_L, 𝒪) = L` and is a natural follow-up PR, not part of the pinned statement.

## Split plan

1. **feat: the genus of a proper scheme with H⁰ = k is invariant under field extension** — needs
   nothing first.
   - File: `TauCeti/AlgebraicGeometry/Curves/Genus/Proper.lean` (new, 115 lines).
   - Declarations: `TauCeti.AlgebraicGeometry.finrank_cohomology_trivial_pullback_eq_of_isPullback`
     (`dim_K Hⁿ(X_K, 𝒪) = dim_k Hⁿ(X, 𝒪)` for quasi-compact `X` with affine diagonal),
     `TauCeti.AlgebraicGeometry.Curve.baseChange`, its `Over (Spec K)` instance, and the target
     `TauCeti.AlgebraicGeometry.Curve.genus_baseChange`.
   - PR description line: `Roadmap: SchemeAndStackFoundations` (target `genus_baseChange`, §3.1).
