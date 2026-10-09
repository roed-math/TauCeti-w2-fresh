<!--tauceti-lookahead:v1 {"area":"LocalGaloisGroups","slug":"nonempty-tate-module","main":"f92c36ac0c8ae0a45c822e2358c0ec9b164833fc","status":"partial","suppliers":["projective-ker-of-is-zero-res"],"splits":[{"n":1,"after":[],"title":"feat(TateCohomology): the splitting module of a Tate class is cohomologically trivial"},{"n":2,"after":[1],"title":"feat: the Tate module of a finite p-adic layer, from a cohomologically trivial extension"},{"n":3,"after":[],"title":"feat: the reciprocity class of A(L) satisfies Tate's hypotheses on p-subgroups"},{"n":4,"after":[1,2,3],"title":"feat: existence of the Tate module of a finite Galois p-adic layer"}]}-->

# Lookahead: `nonempty-tate-module` (LocalGaloisGroups, Layer 7 Step 3)

Target: the structure `TateModule p L K` (here `TauCeti.LayerTateModule`) and
`nonempty_tateModule` of `TauCetiRoadmap/LocalGaloisGroups/README.md`, Layer 7, Step 3 ("The Tate module").

Status: **partial**. The structure is defined, and the target is reduced, with full proofs, to
one arithmetic input (a class in `H²(Gal(L/K), A(L))` satisfying Tate's hypotheses on the
`p`-subgroups) plus a universe transport. The only `sorry` on the branch is the stub of the
supplier, in `TauCeti/Lookahead/NonemptyTateModule/Stubs.lean`.

Built on `main` at `f92c36ac0c8ae0a45c822e2358c0ec9b164833fc`. `lake build` is green and
`lookahead-check` passes.

## The stubbed supplier declaration

Supplier `projective-ker-of-is-zero-res` (ClassFieldTheory, Layer 0, item 4). It has no open PR,
so the stub follows `Suggested.lean`.

`Suggested.lean` (`TauCetiRoadmap/ClassFieldTheory/Suggested.lean`), verbatim, with its section
context (`namespace TateCohomology`, `variable {k G : Type u} [CommRing k] [Group G] [Finite G]`,
then `variable [IsDomain k] [IsPrincipalIdealRing k] [CharZero k]`):

```lean
theorem projective_ker_of_isZero_res
    (hk : ∀ p : ℕ, p.Prime → IsUnit (p : k) ∨ (Ideal.span {(p : k)}).IsMaximal)
    (A : Rep k G)
    (hA : ∀ (S : Subgroup G) [Fintype S] (n : ℤ),
      Limits.IsZero (tateCohomology (res S.subtype A) n))
    {P : Type*} [AddCommGroup P] [Module (MonoidAlgebra k G) P]
    [Module.Projective (MonoidAlgebra k G) P]
    (f : P →ₗ[MonoidAlgebra k G] A.ρ.asModule) (hf : Function.Surjective f) :
    Module.Projective (MonoidAlgebra k G) (LinearMap.ker f) :=
  sorry
```

The stub, in `TauCeti/Lookahead/NonemptyTateModule/Stubs.lean`:

```lean
namespace Rep
variable {k G : Type u} [CommRing k] [Group G]

theorem projective_ker_of_isZero_res [Finite G] [IsDomain k] [IsPrincipalIdealRing k]
    [CharZero k]
    (hk : ∀ p : ℕ, p.Prime → IsUnit (p : k) ∨ (Ideal.span {(p : k)}).IsMaximal)
    (A : Rep k G)
    (hA : ∀ (S : Subgroup G) [Fintype S] (n : ℤ),
      IsZero (tateCohomology (res S.subtype A) n))
    {P : Type*} [AddCommGroup P] [Module (MonoidAlgebra k G) P]
    [Module.Projective (MonoidAlgebra k G) P]
    (f : P →ₗ[MonoidAlgebra k G] A.ρ.asModule) (hf : Function.Surjective f) :
    Module.Projective (MonoidAlgebra k G) (LinearMap.ker f) :=
  sorry
```

Differences, and why:

- **Namespace `Rep`, not `TauCeti.TateCohomology`.** Its landed siblings from the same roadmap
  item, pinned as `TateCohomology.projective_of_isZero_res` and
  `TateCohomology.isZero_res_of_exact`, landed on `main` as `Rep.projective_of_isZero_res` and
  `Rep.isZero_res_of_exact` in
  `TauCeti/RepresentationTheory/Homological/TateCohomology/Projective.lean`. The stub sits beside
  them under the same convention. If the supplier lands under a different name, only the one call
  in `LayerTateModule.nonempty_of_isZero` changes.
- **Instance binders on the theorem.** `[Finite G] [IsDomain k] [IsPrincipalIdealRing k]
  [CharZero k]` are section variables in `Suggested.lean`; the stub binds them on the theorem, as
  `Rep.projective_of_isZero_res` does on `main`. The hypotheses are the same.
- `Limits.IsZero` is written `IsZero` under `open CategoryTheory Limits`. This is the same
  constant.

The proof uses the stub at `k = ℤ_[p]`. The hypothesis `hk` is discharged by the new
`PadicInt.isUnit_natCast_or_isMaximal_span`.

## Differences from the target's pinned forms

- **Name `TauCeti.LayerTateModule`, not `TauCeti.TateModule`.** The name `TauCeti.TateModule`
  is already taken on `main` by the `p`-adic Tate module `lim_n A[p^n]` of an abelian group
  (`TauCeti/Algebra/Module/Torsion/TateModule.lean`), and the axiom audit, which imports both,
  rejects the clash. The structure and its API therefore live under `LayerTateModule`, and split 4
  would name the exported theorem `nonempty_layerTateModule`. This rename should be confirmed by a
  human against the roadmap.
- `TauCeti.LayerTateModule p L K` has exactly the fields, field names and field types of the
  pinned `TateModule`, with one difference. The augmentation ideal is written
  `RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L))` (Tau Ceti's augmentation) instead
  of the roadmap's abbreviation `augmentationIdeal p (L ≃ₐ[K] L)`. The pin defines that
  abbreviation as exactly this kernel. It is not on `main`, and the landed consumer
  `TauCeti.nonempty_linearEquiv_tameFrameModule_prod` (Decomposition.lean) already spells the
  kernel out. The structure is universe-polymorphic (`L K : Type u`), as pinned.

## Splits

### Split 1 — `feat(TateCohomology): the splitting module of a Tate class is cohomologically trivial`

Needs first: nothing.

Files:
- `TauCeti/RepresentationTheory/Homological/TateCohomology/SplittingModule.lean` (new, 208 lines)
  - `TauCeti.TateCohomology.tateCohomologyZeroResTrivialEquiv`: `Ĥ⁰(S, k) ≃ₗ[k] k ⧸ |S|k`.
  - `TauCeti.TateCohomology.isZero_res_splittingModule`: let `k` have no additive torsion. If, on
    every subgroup `S` of prime-power order, `H¹(S, A) = 0`, `res u` generates `H²(S, A)`, and
    `H²(S, A)` has the finite order of `k ⧸ |S|k`, then the splitting module `A(u)` is
    cohomologically trivial (Tate; Milne II 3.11).
  - The private step `isZero_groupCohomology_res_splittingModule`, which proves `H¹ = H² = 0` on
    one subgroup.
- `TauCeti/RepresentationTheory/Homological/GroupCohomology/SplittingModule.lean` (+13 lines):
  `Rep.splittingModuleIncl_comp_splittingModuleProj` and `Rep.splittingModuleSES_def`. The body of
  `splittingModuleSES` is not exposed, so downstream files could not see the maps of the sequence
  without these.

### Split 2 — `feat: the Tate module of a finite p-adic layer, from a cohomologically trivial extension`

Needs first: split 1, and the supplier `projective-ker-of-is-zero-res` landed (the stub import is
replaced by `TauCeti.RepresentationTheory.Homological.TateCohomology.Projective`).

Files:
- `TauCeti/NumberTheory/Padics/MultiplicativeCompletion/LayerTateModule.lean` (new, 251 lines)
  - `TauCeti.LayerTateModule` (the pinned `TateModule`), with `LayerTateModule.exact_ι_π`
    (`Function.Exact Y.ι Y.π`, the form `nonempty_linearEquiv_tameFrameModule_prod` consumes).
  - `TauCeti.LayerTateModule.nonempty_of_isZero`: a cohomologically trivial `ℤ_p[G]`-extension
    `0 → A(L) → Y → I_G → 0` is a Tate module. Finiteness comes from
    `padicCompletionUnits_module_finite` and `ker_augmentation_eq_span`; projective dimension one
    comes from the supplier.
  - `TauCeti.LayerTateModule.nonempty_of_tateHypotheses`: if `u ∈ H²(Gal(L/K), A(L))` has, on every
    `p`-subgroup `S`, `H¹(S, A(L)) = 0`, `res u` generating `H²(S, A(L))`, and
    `#H²(S, A(L)) = #S`, then a Tate module exists, namely the splitting module of `u`. On
    `ℓ`-subgroups with `ℓ ≠ p` every hypothesis is automatic, because `#S` is a unit of `ℤ_p`.
- `TauCeti/NumberTheory/Padics/PadicIntegers.lean` (+13): `PadicInt.isUnit_natCast_of_coprime`,
  `PadicInt.isUnit_natCast_or_isMaximal_span`.
- `TauCeti/RepresentationTheory/Homological/GroupCohomology/Corestriction.lean` (+8):
  `groupCohomology.subsingleton_of_isUnit_natCard`.
- `TauCeti/RepresentationTheory/Homological/Augmentation.lean` (+10, plus a public import of
  `TauCeti.Algebra.MonoidAlgebra.Exactness`): `Rep.augmentation_hom_apply`. The representation
  augmentation is the coefficient sum `TauCeti.MonoidAlgebra.augmentation`.

### Split 3 — `feat: the reciprocity class of A(L) satisfies Tate's hypotheses on p-subgroups` (not on the branch)

Needs first: nothing. It does not import splits 1–2.

For a finite Galois layer `L/K` of `p`-adic fields in `Type`, construct
`u ∈ H²(Gal(L/K), A(L))` (Mathlib `groupCohomology` of
`Rep.of (padicCompletionUnitsRepresentation p L K)`) and prove the three hypotheses of
`LayerTateModule.nonempty_of_tateHypotheses` on every `p`-subgroup `S`. The route, with all inputs
already on `main`:

- Choose `ι : L →ₐ[K] SeparableClosure K` and set `V = galoisSubgroup K L ι`.
- Let `W` be the preimage of `S` in `G_K`. Then `scd_p W ≤ 2`, by
  `strictCohomologicalDimensionAt_le_of_isClosed` and
  `ClassFieldTheory.strictCohomologicalDimensionAt_absoluteGaloisGroup_eq_two`.
- `subsingleton_h1_abelianizationProP_of_isPGroup` and
  `abelianizationProPClass_generates_of_isPGroup` at `(W, V.subgroupOf W)` give the hypotheses for
  `V^ab(p)`.
- Transport these to `A(L)` along:
  - `padicCompletionUnitsEquivAbelianizationProP` and its equivariance `_smul`;
  - `abelianizationProPSubgroupOfEquiv` / `abelianizationProPSubgroupOfH2Equiv_class` (restriction
    of the class);
  - `G_K ⧸ V ≃ Gal(L/K)`;
  - `ContCohomology.explicitH1IsoGroupCohomology` / `explicitH2IsoGroupCohomology`, which are over
    `ℤ`. They must still be compared with `groupCohomology` over `ℤ_[p]` of the same additive
    group. `main` has no API for that comparison, in degrees 1 and 2 or naturally in restriction.
    It is general infrastructure and is probably best opened as its own PR ahead of split 3.

Split 3 is likely to run past 600 lines. If so, it splits along the bullets above: the
comparison over `ℤ` and `ℤ_[p]`, then the transport of the class module to `A(L)`.

### Split 4 — `feat: existence of the Tate module of a finite Galois p-adic layer` (not on the branch)

Needs first: splits 1, 2, 3.

Adds `TauCeti.nonempty_layerTateModule : Nonempty (LayerTateModule p L K)` (the pinned
`nonempty_tateModule`) under the pinned hypotheses
`[Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L] [Algebra ℚ_[p] K] [Module.Finite ℚ_[p] K]
[IsScalarTower ℚ_[p] K L] [IsGalois K L] [FiniteDimensional K L]`, for `L K : Type u`. In `Type`
this is split 3 fed into `LayerTateModule.nonempty_of_tateHypotheses`. For a general universe it also
needs a transport: both fields have copies in `Type`, being finite-dimensional over `ℚ_p`, and
`LayerTateModule` must be carried along the induced isomorphisms of `A(L)` and `ℤ_p[Gal(L/K)]`. That
transport is needed because local reciprocity
(`padicCompletionUnitsEquivAbelianizationProP`) and Mathlib's `Rep ℤ_[p] G` (which needs
`G : Type`) are both universe-0 on `main`.

## What is proved, and what remains

Proved on the branch, with no `sorry` outside the stub:

- the Tate-module structure;
- "cohomologically trivial extension ⇒ Tate module";
- the generic theorem that the splitting module of a class satisfying Tate's hypotheses is
  cohomologically trivial;
- "class satisfying Tate's hypotheses on `p`-subgroups ⇒ Tate module".

Remains:

- split 3: the arithmetic input, which is NSW (3.6.4) at `G = G_K` read on `A(L)` through local
  reciprocity, together with the comparison of continuous with discrete cohomology over `ℤ_p`;
- split 4: assembling `nonempty_layerTateModule` (the pinned `nonempty_tateModule`) and the
  universe transport.
