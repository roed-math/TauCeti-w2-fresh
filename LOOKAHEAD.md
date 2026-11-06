<!--tauceti-lookahead:v1 {"area":"StableReduction","slug":"prestable-model-of-nodal-special-fiber","main":"385ec2ddd8ddf8cc779b78c176308cb9c6b55499","status":"partial","suppliers":["nodal-local-normal-form"],"splits":[{"n":1,"after":[],"title":"feat: prestable models from a special fibre with only ordinary nodes"}]}-->

# Lookahead: `prestable-model-of-nodal-special-fiber` (StableReduction, Layer 5)

Built on `main` at `385ec2ddd8ddf8cc779b78c176308cb9c6b55499`. Target text (README, Layer 5):
"Prove that a geometrically reduced and connected special fibre with geometrically smooth
components and only ordinary nodes after algebraic closure is a prestable model. Give the
equivalent formulation using finite separable residue extensions at singular points."

## Stubbed declarations

Supplier `nodal-local-normal-form` (StableReduction Layer 1; in flight as open PR #28569).

`Suggested.lean` pins **no** declaration for this supplier: the StableReduction `Suggested.lean`
contains only `exists_regular_proper_model`. Open PR #28569 is a partial of the supplier (the
nondegenerate Hessian at a node of a hypersurface over any base,
`TauCeti.forall_mem_and_det_hessian_notMem_of_formallyUnramified`) and does not state the
consumed clause either. The stub is therefore taken from the README's Layer 1 text, "Prove ...
that nodality is stable under base change and local for the étale topology". Stability under base
change and locality on the base (fpqc descent) are already on `main`
(`AtWorstNodalOfRelativeDimensionOne.isStableUnderBaseChange`,
`AtWorstNodalOfRelativeDimensionOne.descendsAlong_surjective_inf_flat_inf_quasicompact`), so
only étale locality on the source is stubbed:

```lean
-- TauCeti/Lookahead/PrestableModelOfNodalSpecialFiber/Stubs.lean
theorem TauCeti.AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne.of_etale_cover
    {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} {U : ι → Scheme.{u}} (e : ∀ i, U i ⟶ X) [∀ i, Etale (e i)]
    (he : ∀ x : X, ∃ i, x ∈ Set.range (e i))
    (h : ∀ i, AtWorstNodalOfRelativeDimensionOne (e i ≫ f)) :
    AtWorstNodalOfRelativeDimensionOne f
```

- `Suggested.lean` signature: none (not pinned).
- Source: README Layer 1 prose; PR #28569's diff contains no such statement.
- Differences: the name, namespace and family-of-étale-maps form are my choice, matching the
  neighbouring `AffineAtWorstNodalOfRelativeDimensionOne.of_openCover` (open covers of the
  source, `Curves/Node/Locality.lean`) and the existing `comp_of_etale`. The statement is true:
  syntomicity is étale local on the source, `Sing(U/S)` is the pullback of `Sing(X/S)` along an
  étale `U ⟶ X` (`Scheme.isPullback_singularLocus_subschemeι_of_etale`, on `main`), and
  unramifiedness is étale local on the source. When the supplier lands, swap in whatever form it
  gives (for instance a `MorphismProperty` locality instance) and adapt the single call in
  `of_isOrdinaryNodeOrSmoothAt` and in `of_forall_exists_isSeparable`.

## Split plan

The whole proof is about 260 lines, so it is one pull request.

1. **feat: prestable models from a special fibre with only ordinary nodes** (after: none, but it
   needs the supplier's étale-locality theorem on `main`).
   - `TauCeti/AlgebraicGeometry/Curves/Node/Ordinary.lean` (new):
     `IsOrdinaryNodeOrSmoothAt` (étale-local ordinary double point or smooth point of a scheme over
     a field), `isOrdinaryNodeOrSmoothAt_nodeAlgebra` (witness: every point of the split node chart),
     `AffineAtWorstNodalOfRelativeDimensionOne.comp_spec_map_of_etale` (nodality survives an étale
     change of affine base, from `Scheme.singularLocus_eq_of_formallyUnramified_base`),
     `IsOrdinaryNodeOrSmoothAt.exists_etale`,
     `AtWorstNodalOfRelativeDimensionOne.of_isOrdinaryNodeOrSmoothAt`,
     `AtWorstNodalOfRelativeDimensionOne.of_baseChange_isOrdinaryNodeOrSmoothAt` (after any field
     extension, e.g. an algebraic closure; uses fpqc descent on `main`),
     `AtWorstNodalOfRelativeDimensionOne.of_forall_exists_isSeparable` (pointwise finite separable
     extensions).
   - `TauCeti/AlgebraicGeometry/Curves/StableReduction/Model/NodalSpecialFiber.lean` (new): the
     exported theorems `TauCeti.Model.prestableFamily_toBase_of_specialFiber` and
     `TauCeti.Model.prestableFamily_toBase_of_specialFiber_of_isSeparable`.
   - Port: replace `import TauCeti.Lookahead.PrestableModelOfNodalSpecialFiber.Stubs` in
     `Ordinary.lean` by the supplier's module, delete `TauCeti/Lookahead/`, and delete this file.
     `comp_spec_map_of_etale` uses only `main`; if a reviewer prefers, it can move to
     `Curves/Node/Locality.lean`.

## Status: partial

Proved (modulo the stub): a proper model of a prestable curve `C ⟶ Spec K` over a DVR whose special
fibre is geometrically connected and, after a field extension `L` of the residue field (e.g. an
algebraic closure), has only smooth points and ordinary nodes, is a prestable model; and the same
with a finite separable extension chosen at each point. Design choices recorded for review:

- "Ordinary node" is formalized étale locally (an étale neighbourhood étale over
  `Spec L[u,v]/(uv)` over `L`), not through the completed local ring `L[[x,y]]/(xy)`.
- Geometric reducedness and smoothness of geometric components are not needed as hypotheses (the
  theorem is stronger without them; components with self-nodes are allowed).
- The generic fibre is assumed prestable (`[PrestableFamily toK]`), e.g. via
  `PrestableFamily.of_smooth` for a smooth proper geometrically connected `C`.

What remains:

1. The **converse** that makes the two formulations *equivalent*: a nodal curve over a field
   has, at each point, a finite separable extension over which the point is an ordinary node or
   smooth (and hence the algebraic-closure and the pointwise-separable hypotheses are equivalent,
   both being equivalent to the special fibre being prestable). This is the special-fibre case of
   the supplier's local normal form (étale `R ⊂ R'`, `U ⟶ Spec R'[u,v]/(uv - πⁿ)`), whose pinned
   form is not yet stated anywhere; stub it once the supplier PR states it.
2. Optionally, the comparison of `IsOrdinaryNodeOrSmoothAt` over an algebraically closed field
   with the completed-local-ring definition `κ̄[[x,y]]/(xy)`.
