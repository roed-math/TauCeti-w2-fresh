<!--tauceti-lookahead:v1 {"area": "StableReduction", "slug": "normalization-exact-sequence", "main": "81820d6b555f126c9030bfa46d25d61690af4fb6", "status": "partial", "suppliers": ["node-branch-splitting"], "splits": [{"n": 1, "after": [], "title": "feat: the cokernel of an algebra modulo an ideal inside the base"}, {"n": 2, "after": [1], "title": "feat: one blowup normalizes a node: conductor, cokernel and regularity"}, {"n": 3, "after": [], "title": "feat: the integral closure over a punctured spectrum is determined at the closed point"}, {"n": 4, "after": [2], "title": "feat: the normalization of the local ring at a node of a curve"}, {"n": 5, "after": [2, 3, 4], "title": "feat: the normalization of an affine neighbourhood of a node"}, {"n": 6, "after": [1], "title": "feat: finiteness and conductor of a relative normalization over an affine cover"}, {"n": 7, "after": [5, 6], "title": "feat: the normalization of a nodal curve is finite, with conductor the singular locus"}, {"n": 8, "after": [1, 2, 3, 4, 5, 6, 7], "title": "feat: the normalization exact sequence of a nodal curve"}]}-->

# Lookahead: `normalization-exact-sequence` (StableReduction)

Target (StableReduction `README.md`, Layer 1, *nodes, normalization, and dual graphs*): "Develop
normalization, the conductor, and the normalization exact sequence for `𝒪_X`." Built on `main`
at `81820d6b555`.

Status: **partial**. The branch now proves, for a nodal curve `X` over a field `K` (no properness
needed) and `ν : X̃ ⟶ X` the normalization of `X` in `U = X ∖ Sing(X/K)` along `ι : U ⟶ X`
(Mathlib's `Scheme.Hom.fromNormalization`):

* `ν` is **finite** (`AlgebraicGeometry.Scheme.isFinite_fromNormalization_compl_singularLocus`);
* its **conductor** is the ideal sheaf of `Sing(X/K)`
  (`AlgebraicGeometry.Scheme.conductor_fromNormalization_compl_singularLocus`);
* `ι` is scheme-theoretically dominant
  (`AlgebraicGeometry.Scheme.isSchemeTheoreticallyDominant_ι_compl_singularLocus`), so
* the **normalization sequence** `0 → 𝒪_X → ν_* 𝒪_X̃ → ν_* 𝒪_X̃ / 𝒪_X → 0` is short exact
  (`AlgebraicGeometry.Scheme.shortExact_cokernelSequence_fromNormalization`).

What remains is the identification of the cokernel `Q = ν_* 𝒪_X̃ / 𝒪_X` (split 8, at the end).

**Changed this round (on top of tip `782c4632b46`).**

* Merged `main` (`81820d6b555`); no conflict. #27451 is still open and its two stubbed statements
  are unchanged (re-checked against its head `3064f030e31`).
* `exists_affineOpen_integralClosure_away` (split 5) is strengthened: the neighbourhood `W` now
  meets `Sing(X/K)` only in `x`, with `D(a) = W ∖ Sing(X/K)`, the singular-locus ideal over `W` is
  the prime of `x` (the singular subscheme is unramified, hence reduced), and `a` is a
  nonzerodivisor of `Γ(X, W)`. For this, `exists_notMem_forall_eq_of_isMaximal` takes an ideal
  instead of an element, `exists_notMem_radical_span_singleton_eq` holds on every smaller basic
  open `D(g h)`, and `mem_nonZeroDivisors_of_radical_span_singleton_eq` is new (split 3); the
  private chart lemma also records the prime of `x` and the singular-locus ideal.
* New `TauCeti.Algebra.conductor_congr` (split 1), new split 6 in
  `Normalization/Finite.lean`, and new split 7, `Curves/Normalization.lean`.

## Suppliers and stubs

Supplier: `node-branch-splitting` (StableReduction), open PR #27451 ("feat: the blowup of the local
ring at a node has an étale exceptional fibre of degree two"). `StableReduction/Suggested.lean`
pins **no** declaration for this item: its only theorem is `exists_regular_proper_model`. Both
stubs therefore restate the declarations of #27451's diff, with the same names, namespaces,
hypotheses and conclusions. They live in
`TauCeti/Lookahead/NormalizationExactSequence/Stubs.lean`, which imports the modules #27451's
declarations sit in or import (`LocalRing/Hessian`, `RegularLocalRing/Basic`, `Smooth/Regular`).
Earlier merged parts of the same supplier (#23800's `ExceptionalFiber.lean`, `PlaneCurve.lean`, the
Hessian criterion and the singular-locus criterion) are used directly from `main`.

1. `TauCeti.IsRegularLocalRing.of_formallySmooth` (#27451, `TauCeti/RingTheory/Smooth/Regular.lean`).
   `Suggested.lean`: none. #27451, verbatim (under `variable {R S : Type*} [CommRing R]
   [CommRing S] [Algebra R S]`):
   ```lean
   theorem IsRegularLocalRing.of_formallySmooth [IsRegularRing R] [IsLocalRing S]
       [Algebra.EssFiniteType R S] [Algebra.FormallySmooth R S] : IsRegularLocalRing S
   ```
   Stub: the same, with the section variables written into the signature as
   `{R S : Type*} [CommRing R] [CommRing S] [Algebra R S]`. No other difference.
2. `TauCeti.exists_quadratic_relation_of_isUnit_det_hessian` (#27451, new
   `TauCeti/RingTheory/Node/TangentCone.lean`). `Suggested.lean`: none. #27451, verbatim (under
   `variable {P A : Type*} [CommRing P] [CommRing A]` and `variable [IsRegularLocalRing P]
   [IsLocalRing A] {R : Type*} [CommSemiring R] [Algebra R P] {s : Fin 2 → P}
   {D : Fin 2 → Derivation R P P} {f : P}`):
   ```lean
   theorem exists_quadratic_relation_of_isUnit_det_hessian
       (hs : maximalIdeal P = Ideal.span (Set.range s))
       (hD : ∀ i j, D i (s j) = if i = j then 1 else 0) (hf : f ∈ maximalIdeal P ^ 2)
       (hH : IsUnit (hessian D f).det) (π : P →+* A) (hπ : Function.Surjective π)
       (hker : RingHom.ker π = Ideal.span {f}) :
       ∃ x y a b : A, maximalIdeal A = Ideal.span {x, y} ∧ x ∈ nonZeroDivisors A ∧
         ¬ (maximalIdeal A).IsPrincipal ∧ a * x ^ 2 + b * x * y + y ^ 2 = 0 ∧
         IsUnit (discrim a b 1)
   ```
   Stub: the same, with the section variables written into the signature. No other difference.

**Porting note.** When #27451 lands, delete `Stubs.lean`, import
`TauCeti.RingTheory.Node.TangentCone` (and `TauCeti.RingTheory.Smooth.Regular`) in
`QuadraticRelation.lean` instead. The private `exists_quadratic_relation_of_algEquiv` of
`QuadraticRelation.lean` mirrors #27451's private `exists_etale_tensor_affineBlowup_of_algEquiv`;
if #27451 lands with a public transport lemma, use it.

## Splits

1. **`feat: the cokernel of an algebra modulo an ideal inside the base`** (after: none).
   File: `TauCeti/RingTheory/Conductor.lean` (+74 lines). Adds
   `TauCeti.Algebra.conductor_congr` (isomorphic algebras have the same conductor),
   `TauCeti.Algebra.map_conductor_le_one`, `TauCeti.Algebra.quotientOneEquivOfLE` (for an ideal
   `I ⊆ A` of `B`, `B / A ≃ₗ[A] (B / I) / A`) and `TauCeti.Algebra.quotientOneEquivOfLE_mk`.
2. **`feat: one blowup normalizes a node: conductor, cokernel and regularity`** (after: 1).
   Files: new `TauCeti/RingTheory/Node/Resolution.lean` (428 lines) and
   `TauCeti/RingTheory/Ideal/AffineBlowup.lean` (+10). Adds
   `Ideal.algebraMap_affineBlowup_injective`, `TauCeti.maximalIdeal_le_conductor_affineBlowup`,
   `TauCeti.conductor_affineBlowup_eq_maximalIdeal`, `TauCeti.affineBlowupQuotientEquiv`,
   `TauCeti.affineBlowupQuotientEquiv_mk_divBy`, `TauCeti.affineBlowupQuotientEquivFiber`,
   `TauCeti.isRegularLocalRing_localization_affineBlowup`,
   `TauCeti.isDiscreteValuationRing_localization_affineBlowup` and
   `TauCeti.integralClosure_eq_affineBlowup`.
3. **`feat: the integral closure over a punctured spectrum is determined at the closed point`**
   (after: none; it uses only `main`'s `TauCeti.Algebra.conductor`). File: new
   `TauCeti/RingTheory/IntegralClosure/Punctured.lean` (323 lines). Adds
   `TauCeti.isCoprime_pow_of_radical_span_singleton_eq`,
   `TauCeti.mem_nonZeroDivisors_of_radical_span_singleton_eq` (**new**: if `√(u) = q` is maximal
   and `u` is a nonzerodivisor of `A_q`, it is one of `A`),
   `TauCeti.exists_notMem_forall_eq_of_isMaximal` (now for an ideal `I`: some `D(g) ∋ q` meets
   `V(I)` only in `q`), `TauCeti.exists_notMem_radical_span_singleton_eq` (now also on every
   smaller `D(g h)`, `h ∉ q`), `TauCeti.isLocalizedModule_id_of_pow_smul_eq_zero`,
   `TauCeti.integralClosureMap`, `TauCeti.coe_integralClosureMap`, the instance
   `TauCeti.isLocalizedModule_integralClosureMap`, `TauCeti.localized'_one_integralClosureMap`,
   `TauCeti.integralClosureQuotientEquiv`, `TauCeti.integralClosureQuotientEquiv_mk`,
   `TauCeti.conductor_integralClosure_eq_of_conductor_eq_maximalIdeal`,
   `TauCeti.quotientEquivQuotientMaximalIdeal`,
   `TauCeti.integralClosureQuotientEquivOfQuotientEquiv` and
   `TauCeti.finite_integralClosure_of_quotientEquiv`.
   *Reuse notes.* `integralClosureMap` is the structure map of `main`'s
   `TauCeti.integralClosureMapAlgebra`, bundled because the `letI` instance form made instance
   search on the quotients time out. `quotientEquivQuotientMaximalIdeal` is Mathlib's
   `IsLocalization.AtPrime.equivQuotMaximalIdealPow q A_q 1` up to `pow_one`; transporting along
   `pow_one` timed out in `whnf`.
4. **`feat: the normalization of the local ring at a node of a curve`** (after: 2; and the
   supplier #27451 must have landed, replacing the stubs). Files: new
   `TauCeti/RingTheory/Node/QuadraticRelation.lean` (206 lines) and new
   `TauCeti/AlgebraicGeometry/Curves/Node/Stalk.lean` up to and including
   `exists_conductor_stalk_eq_maximalIdeal` (lines 1–203, with the module docstring trimmed to
   these results). Adds `TauCeti.exists_quadratic_relation_of_ringEquiv`,
   `TauCeti.exists_quadratic_relation_mul_unit` (the shape survives multiplying `x` by a unit),
   `TauCeti.radical_span_singleton_eq_maximalIdeal` (`𝔪 = √(x)`), the private
   `exists_quadratic_relation_of_algEquiv`, `TauCeti.exists_quadratic_relation_of_formallyUnramified`,
   `TauCeti.exists_integralClosure_eq_affineBlowup_of_formallyUnramified`,
   `Algebra.Presentation.exists_quadratic_relation_of_formallyUnramified`, the private chart lemma
   `exists_chart`, `AlgebraicGeometry.Scheme.exists_quadratic_relation_stalk`,
   `AlgebraicGeometry.Scheme.exists_integralClosure_stalk_eq_affineBlowup` and
   `AlgebraicGeometry.Scheme.exists_conductor_stalk_eq_maximalIdeal` (at a node, `u` is a
   nonzerodivisor, the conductor of `𝒪_{X,x}[𝔪/u]` is `𝔪`, and its cokernel is `κ(x)`).
5. **`feat: the normalization of an affine neighbourhood of a node`** (after: 2, 3, 4). Files: new
   `TauCeti/RingTheory/Node/Punctured.lean` (92 lines), `TauCeti/RingTheory/Unramified/LocalRing.lean`
   (+18) and the rest of `TauCeti/AlgebraicGeometry/Curves/Node/Stalk.lean` (lines 205–355, ≈150
   lines). Adds `TauCeti.conductor_integralClosure_away_eq_of_maximalIdeal_eq_span` (if `√(u) = q`
   and `A_q` has the node shape with first generator `u`, the integral closure of `A` in `A_u` is
   finite with conductor `q` and cokernel `A / q`; its private
   `conductor_integralClosure_away_eq_aux` states it over an abstract localization `L'`, because
   instance search on the cokernels times out when `L'` is the concrete `A_q ⊗[A] A_u`),
   `Ideal.IsPrime.isMaximal_of_formallyUnramified_quotient` (a prime over an ideal with unramified
   quotient over a field is maximal) and
   `AlgebraicGeometry.Scheme.exists_affineOpen_integralClosure_away` (a node `x` has an affine
   neighbourhood `W` with `W ∩ Sing(X/K) = {x}`, singular-locus ideal over `W` the prime of `x`,
   and a nonzerodivisor `a` with `D(a) = W ∖ Sing(X/K)`, such that the integral closure of
   `Γ(X, W)` in `Γ(X, W)_a` is finite, with conductor the prime of `x` and cokernel
   `Γ(X, W) / 𝔭_x`).
6. **`feat: finiteness and conductor of a relative normalization over an affine cover`**
   (after: 1, for `conductor_congr`). File: `TauCeti/AlgebraicGeometry/Normalization/Finite.lean`
   (+93). Adds `AlgebraicGeometry.Scheme.Hom.finite_fromNormalization_app_iff` (factored out of
   `isFinite_fromNormalization_iff`, which now uses it),
   `AlgebraicGeometry.Scheme.Hom.isFinite_fromNormalization_of_iSup_eq_top` (finiteness of a
   normalization can be checked over an affine open cover),
   `AlgebraicGeometry.Scheme.Hom.normalizationObjAlgEquiv` and its `_apply` lemma (Mathlib's
   `normalizationObjIso` as a `Γ(Y, U)`-algebra isomorphism), and
   `AlgebraicGeometry.Scheme.Hom.conductor_fromNormalization_ideal` (over an affine open, the
   conductor of a finite normalization is that of the integral closure). It imports
   `TauCeti.AlgebraicGeometry.IdealSheaf.Conductor`. *Note.* The affine property of `IsFinite`
   is not found by instance search without the `respectTransparency` option, so the proof names
   it with `observe`, as `TauCeti/AlgebraicGeometry/Frobenius/Smooth.lean` on `main` does.
7. **`feat: the normalization of a nodal curve is finite, with conductor the singular locus`**
   (after: 5, 6). File: new `TauCeti/AlgebraicGeometry/Curves/Normalization.lean` (210 lines, the
   path the README's J-B contract names). Adds the private `exists_affineOpen_integralClosure`
   (each point has an affine `W` over which `Γ(X, W) → Γ(U ∩ W)` is injective and the integral
   closure is finite with conductor the singular-locus ideal: at a node by split 5, elsewhere with
   `W ⊆ U`), `AlgebraicGeometry.Scheme.isFinite_fromNormalization_compl_singularLocus`,
   `AlgebraicGeometry.Scheme.conductor_fromNormalization_compl_singularLocus`,
   `AlgebraicGeometry.Scheme.isSchemeTheoreticallyDominant_ι_compl_singularLocus` and
   `AlgebraicGeometry.Scheme.shortExact_cokernelSequence_fromNormalization`
   (via `main`'s
   `Modules/StructureSheafSequence.lean`). The derived instances (`IsLocallyNoetherian X`, needed
   for the quasi-compactness of `ι`, and finiteness of `ν`, needed for its conductor) are
   `haveI`s in the statements.
   *Reuse note.* `main`'s `TauCeti/RingTheory/Node/{Conductor,Normalization}.lean` compute the
   conductor and normalization of the *split* model `R[x,y]/(xy)`; the branch works with the
   abstract local ring at a node over a field, split or not, so it does not pass through those
   models (they would need the étale-local chart and descent along it).
8. **`feat: the normalization exact sequence of a nodal curve`** (after: 1–7). *Not on the
   branch.* It carries the target's exported identification of the cokernel and is the only
   split that completes the target.

## What remains (split 8)

Identify the cokernel `Q = ν_* 𝒪_X̃ / 𝒪_X` of the short exact sequence of split 7, in
`TauCeti/AlgebraicGeometry/Curves/Normalization.lean`:

* **Sections over affines.** `Q` is quasicoherent (`main`'s
  `isQuasicoherent_cokernel_unitToPushforwardObjUnit`, `ν` being affine), so over an affine `W`
  its sections are the module cokernel `Γ(X̃, ν⁻¹ W) / Γ(X, W)`; via `normalizationObjAlgEquiv`
  this is the cokernel of `Γ(X, W)` in its integral closure. This needs a "sections of a
  quasicoherent cokernel over an affine open" lemma (not on `main`; `tildeCokernelIso` in
  `Modules/Quasicoherent/Cokernels.lean` is the starting point).
* **The local answer.** Over the cover of split 7, the cokernel is `Γ(X, W) / 𝔭_x` at a node
  (split 5's cokernel clause) and `0` elsewhere. So `Q` is killed by the conductor `= I_Sing`
  (split 7) and is an invertible `𝒪_{Sing(X/K)}`-module; by split 1 (`quotientOneEquivOfLE`) it
  is canonically the functions on the branch scheme `ν⁻¹ Sing(X/K)` modulo those on
  `Sing(X/K)`.
* **Export.** State the sequence with `Q` replaced by the direct image of that quotient (or of
  `𝒪_{Sing(X/K)}` after choosing a trivialization on the finite étale `Sing(X/K)`), as the J-B
  contract asks for the normalization exact-sequence maps.
