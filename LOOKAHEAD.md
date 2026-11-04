<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"noetherian-approximation","main":"333c9e49143de812ed1452b412193ee9c05501e7","status":"partial","suppliers":["qcoh-extension"],"splits":[{"n":1,"after":[],"title":"feat: separation, affineness and underlying space of limits of schemes with affine transition maps"},{"n":2,"after":[],"title":"feat: Noetherian approximation of affine schemes"},{"n":3,"after":[],"title":"feat: descent of morphisms and isomorphisms of finitely presented schemes along cofiltered limits"},{"n":4,"after":[1],"title":"feat: existence of cofiltered limits of schemes with affine transition maps"},{"n":5,"after":[3],"title":"feat: descent of finitely presented schemes and their properties to a finite stage"},{"n":6,"after":[2,4,5],"title":"feat: extending finite-presentation models across a quasi-compact open"},{"n":7,"after":[1,2,3,4,5,6],"title":"feat: absolute Noetherian approximation of quasi-compact quasi-separated schemes"}]}-->
# Lookahead: `noetherian-approximation` (SchemeAndStackFoundations §0.9)

Built on `main` at `333c9e4914`. Status: **partial**.

The roadmap pins no Lean forms for §0.9 in `Suggested.lean`; the target is specified by the
README only (`affine_transition_limits`, `noetherian_approximation`,
`finite_presentation_limits`).

## Stubbed declarations

### `qcoh-extension`: finite-type submodule extension (Stacks 01PF)

`Suggested.lean` pins no Lean signature for `qcoh_extension` (`grep qcoh Suggested.lean` is
empty); its README §0.4 states it in prose: "a finite-type quasi-coherent submodule of `j^*G` is
`j^*G'` for a finite-type quasi-coherent submodule `G' ⊆ G` (Lemma 28.23.2 (01PF))". Parts (1)
and (2) of 01PE have since landed on `main` (PR #22951) as
`AlgebraicGeometry.Scheme.Modules.exists_isQuasicoherent_restrict_iso` and
`AlgebraicGeometry.Scheme.Modules.exists_mono_restrict_iso_of_isQuasicoherent` in
`TauCeti/AlgebraicGeometry/Modules/Quasicoherent/Extension.lean`, so they are not stubbed. The
supplier's open PR #26972 ("finite type of sheaves of modules can be checked on an open cover")
adds `SheafOfModules.IsFiniteType.of_coversTop` and
`isFiniteType_of_isFiniteType_restrict(_affineOpens)`, prerequisites of 01PF, but not 01PF itself.
The stub follows main's form of 01PE part (2), adding the finite-type hypotheses and conclusion and
qcqs of `X` (which 01PF needs and the README states):

```lean
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_restrict_iso
    [QuasiCompact j] [CompactSpace X] [QuasiSeparatedSpace X] {G : X.Modules}
    [G.IsQuasicoherent] {F : U.Modules} [F.IsQuasicoherent] [F.IsFiniteType]
    (i : F ⟶ G.restrict j) [Mono i] :
    ∃ (G' : X.Modules) (_ : G'.IsQuasicoherent) (_ : G'.IsFiniteType) (i' : G' ⟶ G) (_ : Mono i')
      (e : G'.restrict j ≅ F), (Scheme.Modules.restrictFunctor j).map i' = e.hom ≫ i
```

(in `namespace TauCeti.AlgebraicGeometry` with `variable {U X : Scheme.{u}} (j : U ⟶ X)
[IsOpenImmersion j]`, as on `main`). Differences from main's
`exists_mono_restrict_iso_of_isQuasicoherent`: the added
`[CompactSpace X] [QuasiSeparatedSpace X] [F.IsFiniteType]` hypotheses and `G'.IsFiniteType`
conclusion (the content of 01PF); the "isomorphism over `V`" clause is dropped since split 6 does
not consume it. No proved declaration on this branch uses the stub yet: it is consumed by split 6
(extending a finite-type quasi-coherent ideal sheaf, cutting out the closure of a
finite-presentation model over an open, from `U` to `X`).

## Splits

1. **feat: separation, affineness and underlying space of limits of schemes with affine
   transition maps** (after: none) — *proved*. File
   `TauCeti/AlgebraicGeometry/Limits/AffineTransition.lean` (198 lines), namespace
   `TauCeti.AlgebraicGeometry.Scheme`: `isSeparated_of_isLimit`, `quasiSeparatedSpace_of_isLimit`
   (the separatedness half of `affine_transition_limits`, 01YX + 01S7; quasi-compactness is
   Mathlib's `Scheme.compactSpace_of_isLimit`), `isAffine_of_isLimit`, `isQuasiAffine_of_isLimit`,
   `isAffine_iff_exists_of_isLimit`, `isQuasiAffine_iff_exists_of_isLimit` (with Mathlib's 01Z6/01Z5
   converses); and `|lim Xᵢ| = lim |Xᵢ|` (0CUF): `exists_π_app_eq_of_isLimit` (every compatible
   family of points comes from a point of the limit, via the spectrum of the colimit of the residue
   fields; for any cofiltered diagram), `specializes_of_isLimit`, `ext_of_isLimit`,
   `topologicalSpace_eq_iInf_induced_of_isLimit`, and the instance `preservesLimit_forgetToTop :
   PreservesLimit D Scheme.forgetToTop`.
2. **feat: Noetherian approximation of affine schemes** (after: none) — *proved*.
   File `TauCeti/AlgebraicGeometry/Limits/NoetherianApproximation.lean` (105 lines):
   `finsetAdjoinDiagram`, `finsetAdjoinCocone`, `isColimitFinsetAdjoinCocone` (every ring is the
   filtered colimit of its finitely generated `ℤ`-subalgebras), the instance
   `Algebra.FinitePresentation ℤ ((finsetAdjoinDiagram A).obj s)`,
   `locallyOfFinitePresentation_terminal_from_Spec`, and
   `Scheme.exists_isLimit_finitePresentation_of_isAffine` (the affine case of 01ZA).
3. **feat: descent of morphisms and isomorphisms of finitely presented schemes along cofiltered
   limits** (after: none) — *proved*. Files:
   - `TauCeti/CategoryTheory/Limits/Shapes/Pullback/Cofiltered.lean` (123 lines), in any category
     with pullbacks: `CategoryTheory.Functor.pullbackOver` (`j ↦ Dⱼ ×_{Dᵢ} Z` over `Over i`),
     `CategoryTheory.Limits.Cone.pullbackOver`, `CategoryTheory.Limits.IsLimit.pullbackOver` (the
     base change of a cofiltered limit cone is a limit cone), and their `_map_fst/_map_snd`,
     `_π_app_fst/_π_app_snd` lemmas;
   - `TauCeti/AlgebraicGeometry/Limits/BaseChange.lean` (50 lines): instances passing affine
     transition maps, quasi-compactness and quasi-separation to `D.pullbackOver r`;
   - `TauCeti/AlgebraicGeometry/Limits/FinitePresentation.lean` (193 lines), namespace
     `TauCeti.AlgebraicGeometry.Scheme`: the absolute (over `ℤ`) 01ZC statements
     `exists_map_comp_eq_of_isLimit`, `exists_π_app_comp_eq_of_isLimit`;
     `exists_pullbackMap_comp_eq_of_isLimit` (01ZM, descent of morphisms: a morphism over the limit
     between base changes of schemes over `Dᵢ`, the target locally of finite presentation, is the
     base change of one over some `Dⱼ`); `exists_isIso_pullbackMap_of_isLimit` (081E, the
     "isomorphism" case of the inherited properties of `finite_presentation_limits`).
4. **feat: existence of cofiltered limits of schemes with affine transition maps** (after: 1) —
   *remaining*. `affine_transition_limits` existence (01YW), by gluing the affine limits
   `Spec (colim Γ)` over an affine open cover of one member (Mathlib's `isLimitOpensCone` identifies
   the restrictions), or by relative `Spec` of the colimit of the pushed-forward quasi-coherent
   algebras (needs filtered colimits in `QuasicoherentAlgebra`, absent on `main`); into
   `Limits/AffineTransition.lean` or a new `Limits/Existence.lean`.
5. **feat: descent of finitely presented schemes and their properties to a finite stage**
   (after: 3) — *remaining*. The object half of 01ZM (a scheme of finite presentation over the
   limit is the base change of one over some `Dᵢ`), and the properties flat, smooth, étale,
   proper, finite, closed immersion, open immersion inherited from a finite stage (04AI, 0C0C,
   07RP, 081F, 01ZO, 01ZP, 0EUU), in `Limits/FinitePresentation.lean` and new files; likely two
   PRs.
6. **feat: extending finite-presentation models across a quasi-compact open** (after: 2, 4, 5) —
   *remaining*. Stacks 01Z7, 01Z9, 07RN: given `X = U ∪ W`, `W` affine, and `U` a limit of f.p.
   `ℤ`-schemes, glue an f.p. model over `W`; consumes the stub
   `exists_isFiniteType_mono_restrict_iso` to extend the finite-type ideal sheaf. New file
   `Limits/NoetherianApproximation/Extension.lean`.
7. **feat: absolute Noetherian approximation of quasi-compact quasi-separated schemes**
   (after: 1, 2, 3, 4, 5, 6) — *remaining*. `noetherian_approximation` (01ZA) by induction on the
   number of affines in a cover, starting from split 2; completes the target.

## What remains

Proved: the separatedness/quasi-separatedness and (quasi-)affineness criteria of limits with affine
transition maps; the underlying space of such a limit is the limit of the underlying spaces
(0CUF); the full affine case of absolute Noetherian approximation; the absolute 01ZC
factorization and agreement statements; base change of cofiltered limits; descent of morphisms
(01ZM, morphism half) and of isomorphisms (081E) to a finite stage. Remaining: splits 4–7 above —
existence of affine-transition limits (01YW), descent of finitely presented schemes themselves and
of the remaining properties (flat, smooth, étale, proper, finite, closed and open immersion), the
extension step across an open (the only consumer of the `qcoh-extension` stub), and the qcqs
induction for `noetherian_approximation`.
