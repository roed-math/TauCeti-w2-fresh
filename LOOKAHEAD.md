<!--tauceti-lookahead:v1 {"area":"LocalGaloisGroups","slug":"nonempty-tate-module","main":"dcef23604e4ed5b31e6ddaeff8b89dda75d08d10","status":"complete","suppliers":["projective-ker-of-is-zero-res"],"splits":[{"n":1,"after":[],"title":"feat(TateCohomology): the splitting module of a Tate class is cohomologically trivial"},{"n":2,"after":[1],"title":"feat: the Tate module of a finite p-adic layer, from a cohomologically trivial extension"},{"n":3,"after":[],"title":"feat(ContCohomology): explicit low-degree cohomology along a compatible pair"},{"n":4,"after":[],"title":"feat(ContCohomology): strict cohomological dimension is invariant under isomorphism"},{"n":5,"after":[3,4],"title":"feat: the low-degree cohomology of A(L) on p-subgroups"},{"n":6,"after":[1,2,3,4,5],"title":"feat: existence of the Tate module of a finite Galois p-adic layer"}]}-->

# Lookahead: `nonempty-tate-module` (LocalGaloisGroups, Layer 7 Step 3)

Target: the structure `TateModule p L K` (here `TauCeti.LayerTateModule`) and
`nonempty_tateModule` (here `TauCeti.nonempty_layerTateModule`) of
`TauCetiRoadmap/LocalGaloisGroups/README.md`, Layer 7, Step 3 ("The Tate module").

Status: **complete**. `TauCeti.nonempty_layerTateModule` is proved for `L K : Type u` under the
pinned hypotheses, with no `sorry` outside the supplier stub in
`TauCeti/Lookahead/NonemptyTateModule/Stubs.lean`.

Built on `main` at `dcef23604e4ed5b31e6ddaeff8b89dda75d08d10`. `lake build` is green and
`lookahead-check` passes.

## The stubbed supplier declaration

Supplier `projective-ker-of-is-zero-res` (ClassFieldTheory, Layer 0, item 4), in flight as
PR #13553 ("feat: projective kernels of cohomologically trivial representations"). The stub
follows the PR's diff, which agrees with `Suggested.lean` up to the placement noted below.

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

PR #13553 states it, in the new file
`TauCeti/RepresentationTheory/Homological/TateCohomology/NakayamaRim.lean` (which publicly imports
`TauCeti.RepresentationTheory.Homological.TateCohomology.Projective`), under
`namespace Rep`, `variable {k G : Type u} [CommRing k] [Group G] [Finite G] [IsDomain k]
[IsPrincipalIdealRing k] [CharZero k]`, `open CategoryTheory Limits TauCeti.TateCohomology`, as:

```lean
theorem projective_ker_of_isZero_res
    (hk : ∀ p : ℕ, p.Prime → IsUnit (p : k) ∨ (Ideal.span {(p : k)}).IsMaximal)
    (A : Rep k G)
    (hA : ∀ (S : Subgroup G) [Fintype S] (n : ℤ),
      IsZero (tateCohomology (res S.subtype A) n))
    {P : Type*} [AddCommGroup P] [Module (MonoidAlgebra k G) P]
    [Module.Projective (MonoidAlgebra k G) P]
    (f : P →ₗ[MonoidAlgebra k G] A.ρ.asModule) (hf : Function.Surjective f) :
    Module.Projective (MonoidAlgebra k G) (LinearMap.ker f)
```

The stub, in `TauCeti/Lookahead/NonemptyTateModule/Stubs.lean` (importing
`TauCeti.RepresentationTheory.Homological.TateCohomology.Projective`):

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

- **Namespace `Rep`, not `TauCeti.TateCohomology`.** This is where PR #13553 puts it, beside the
  landed siblings of the same roadmap item (`Rep.projective_of_isZero_res`,
  `Rep.isZero_res_of_exact`, pinned as `TateCohomology.…`).
- **Instance binders on the theorem** rather than section variables: the same hypotheses.
- `Limits.IsZero` is written `IsZero` under `open CategoryTheory Limits`: the same constant.
- **Module.** When the supplier lands, the import of `TauCeti.Lookahead.NonemptyTateModule.Stubs`
  in `LayerTateModule/Basic.lean` becomes
  `TauCeti.RepresentationTheory.Homological.TateCohomology.NakayamaRim`. The one consumer is
  `LayerTateModule.nonempty_of_isZero`, used at `k = ℤ_[p]` with `hk` discharged by
  `PadicInt.isUnit_natCast_or_isMaximal_span`.

## Differences from the target's pinned forms

- **Name `TauCeti.LayerTateModule`, not `TauCeti.TateModule`.** `TauCeti.TateModule` is already
  taken on `main` by the `p`-adic Tate module `lim_n A[p^n]` of an abelian group
  (`TauCeti/Algebra/Module/Torsion/TateModule.lean`). The structure and its API therefore live
  under `LayerTateModule`, and the pinned `nonempty_tateModule` is `nonempty_layerTateModule`. This
  rename should be confirmed by a human against the roadmap.
- `TauCeti.LayerTateModule p L K` has the fields, field names and field types of the pinned
  `TateModule`, except that the augmentation ideal is written
  `RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L))` (Tau Ceti's augmentation) rather
  than the roadmap's abbreviation `augmentationIdeal p (L ≃ₐ[K] L)`, which the pin defines as this
  kernel. The abbreviation is not on `main`, and the landed consumer
  `TauCeti.nonempty_linearEquiv_tameFrameModule_prod` already spells out the kernel.
- `TauCeti.nonempty_layerTateModule` takes exactly the pinned hypotheses
  (`[Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L] [Algebra ℚ_[p] K] [Module.Finite ℚ_[p] K]
  [IsScalarTower ℚ_[p] K L] [IsGalois K L] [FiniteDimensional K L]`, with `L K : Type u`) and the
  pinned conclusion.
- **The route.** The roadmap sketches the proof through the local class formation
  (`ClassFormation.fundamentalClass`, `tateTheorem`) and Tate's criterion. The proof here uses the
  class module of `main` instead: `A(L) ≃ V^ab(p)` by local reciprocity (Step 1), and NSW (3.6.4)
  at `G_K` (`abelianizationProPClass_generates_of_isPGroup`,
  `subsingleton_h1_abelianizationProP_of_isPGroup`, `abelianizationProPClass_generates`, with
  `scd_p G_K = 2`), followed by Tate's theorem in the form
  `TateCohomology.isZero_res_splittingModule` (split 1) and Nakayama–Rim (the supplier). The
  statement is unaffected.

## Splits

### Split 1 — `feat(TateCohomology): the splitting module of a Tate class is cohomologically trivial`

Needs first: nothing. About 220 lines.

- `TauCeti/RepresentationTheory/Homological/TateCohomology/SplittingModule.lean` (new, 208 lines):
  `TauCeti.TateCohomology.tateCohomologyZeroResTrivialEquiv` (`Ĥ⁰(S, k) ≃ₗ[k] k ⧸ |S|k`),
  `TauCeti.TateCohomology.isZero_res_splittingModule` (Tate; Milne II 3.11: if, on every subgroup
  of prime-power order, `H¹ = 0`, `res u` generates `H²` and `#H² = #(k ⧸ |S|k)`, then the
  splitting module `A(u)` is cohomologically trivial), and the private step
  `isZero_groupCohomology_res_splittingModule`.
- `TauCeti/RepresentationTheory/Homological/GroupCohomology/SplittingModule.lean` (+13):
  `Rep.splittingModuleIncl_comp_splittingModuleProj`, `Rep.splittingModuleSES_def`.

### Split 2 — `feat: the Tate module of a finite p-adic layer, from a cohomologically trivial extension`

Needs first: split 1, and the supplier `projective-ker-of-is-zero-res` landed (replace the stub
import as above, and delete `TauCeti/Lookahead/`). About 280 lines.

- `TauCeti/NumberTheory/Padics/MultiplicativeCompletion/LayerTateModule/Basic.lean` (new, 251
  lines): `TauCeti.LayerTateModule` (the pinned `TateModule`), `LayerTateModule.exact_ι_π`,
  `LayerTateModule.nonempty_of_isZero` (a cohomologically trivial extension of `I_G` by `A(L)` is
  a Tate module; finiteness from `padicCompletionUnits_module_finite`, projective dimension from
  the supplier), `LayerTateModule.nonempty_of_tateHypotheses` (a class in `H²(Gal(L/K), A(L))`
  satisfying Tate's hypotheses on the `p`-subgroups gives a Tate module, namely its splitting
  module).
- `TauCeti/NumberTheory/Padics/PadicIntegers.lean` (+13): `PadicInt.isUnit_natCast_of_coprime`,
  `PadicInt.isUnit_natCast_or_isMaximal_span`.
- `TauCeti/RepresentationTheory/Homological/GroupCohomology/Corestriction.lean` (+8):
  `groupCohomology.subsingleton_of_isUnit_natCard`.
- `TauCeti/RepresentationTheory/Homological/Augmentation.lean` (+10): `Rep.augmentation_hom_apply`.

### Split 3 — `feat(ContCohomology): explicit low-degree cohomology along a compatible pair`

Needs first: nothing. About 175 lines.

- `TauCeti/RepresentationTheory/Homological/ContCohomology/GroupCohomologyIso.lean` (+173):
  `TauCeti.ContCohomology.explicitH1AddEquivGroupCohomology`,
  `TauCeti.ContCohomology.explicitH2AddEquivGroupCohomology` (explicit `H¹`/`H²` of a discrete
  group `G` in `M` ≃+ Mathlib's `groupCohomology B n` for `B : Rep k H`, along `φ : G ≃* H` and an
  equivariant `ψ : M ≃+ B`; over any coefficient ring `k`), with their `_mk` lemmas and private
  cocycle-transport steps. A possible follow-up refactor, not part of this target, is to derive
  the existing `explicitH1IsoGroupCohomology`/`explicitH2IsoGroupCohomology` (`φ = ψ = id`,
  `k = ℤ`) from these.

### Split 4 — `feat(ContCohomology): strict cohomological dimension is invariant under isomorphism`

Needs first: nothing. About 115 lines.

- `TauCeti/RepresentationTheory/Homological/ContCohomology/Functoriality.lean` (+36):
  `TauCeti.ContinuousCohomology.map_continuousMulEquiv_injective` (restriction along `H ≃ₜ* G` is
  injective on continuous cohomology).
- `TauCeti/RepresentationTheory/Homological/ContCohomology/CohomologicalDimension/Equiv.lean`
  (new, 79 lines): `TauCeti.StrictCohomologicalDimensionLE.of_continuousMulEquiv`,
  `TauCeti.strictCohomologicalDimensionAt_congr`. This is what reads `scd_p = 2`, proved on `main`
  for Mathlib's `Field.absoluteGaloisGroup K`, on Tau Ceti's `AbsoluteGaloisGroup K`, the group
  local reciprocity for `A(L)` is stated on.

### Split 5 — `feat: the low-degree cohomology of A(L) on p-subgroups`

Needs first: splits 3 and 4. About 200 lines.

- `TauCeti/NumberTheory/Padics/MultiplicativeCompletion/Cohomology.lean` (new, 199 lines), for a
  finite Galois layer `L/K` of `p`-adic fields in `Type`:
  `TauCeti.isZero_groupCohomology_one_res_padicCompletionUnits` (`H¹(S, A(L)) = 0` on every
  `p`-subgroup `S`), `TauCeti.natCard_groupCohomology_two_res_padicCompletionUnits`
  (`#H²(S, A(L)) = #S`), `TauCeti.exists_zmultiples_eq_top_groupCohomology_two_padicCompletionUnits`
  (`H²(Gal(L/K), A(L))` is cyclic of order `p ^ v_p(#Gal(L/K))`). Private steps: the reciprocity
  equivalence read additively and its equivariance, `G_K ⧸ V ≃ Gal(L/K)`, `scd_p G_K ≤ 2` on
  `AbsoluteGaloisGroup K`, and the common proof on a `p`-subgroup through the preimage `W` of `S`
  in `G_K` and `abelianizationProPSubgroupOfH1Equiv`/`H2Equiv`.

### Split 6 — `feat: existence of the Tate module of a finite Galois p-adic layer`

Needs first: splits 1, 2, 3, 4, 5. About 385 lines. The only split that completes the target.

- `TauCeti/NumberTheory/Padics/MultiplicativeCompletion/Basic.lean` (+85):
  `TauCeti.padicCompletionUnitsCongr` (`A(L) ≃* A(L')` along `L ≃+* L'`),
  `padicCompletionUnitsCongr_apply`, `padicCompletionUnitsCongr_smul` (`ℤ_p`-linearity),
  `padicCompletionUnitsCongr_aut` (equivariance).
- `TauCeti/Algebra/MonoidAlgebra/Exactness.lean` (+7):
  `TauCeti.MonoidAlgebra.augmentation_mapDomainRingEquiv`.
- `TauCeti/RepresentationTheory/Homological/GroupCohomology/Corestriction.lean` (+35):
  `groupCohomology.zmultiples_map_subtype_eq_top` (a class whose order has the full `p`-part of
  `#G` restricts to a generator on every `p`-subgroup `S` with `#Hⁿ(S) = #S`, via
  `cor ∘ res = [G : S]`).
- `TauCeti/NumberTheory/Padics/MultiplicativeCompletion/LayerTateModule/Existence.lean` (new, 258
  lines): `TauCeti.LayerTateModule.nonempty_of_equiv` (transport of a Tate module along an
  isomorphism of layers, the carrier lifted by `ULift` and the group algebras identified by
  `MonoidAlgebra.mapDomainRingEquiv`), the private `Type`-level existence, and the exported
  **`TauCeti.nonempty_layerTateModule`** (the pinned `nonempty_tateModule`) for `L K : Type u`,
  through the copies `Shrink L / Shrink K`.
