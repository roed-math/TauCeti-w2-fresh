<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"noetherian-approximation","main":"ab1c5af023f864980704684df6008c9288ab4fcf","status":"partial","suppliers":["qcoh-extension"],"splits":[{"n":1,"after":[],"title":"feat: separation and affineness of limits of schemes with affine transition maps"},{"n":2,"after":[],"title":"feat: Noetherian approximation of affine schemes"},{"n":3,"after":[1],"title":"feat: existence of cofiltered limits of schemes with affine transition maps"},{"n":4,"after":[3],"title":"feat: descent of finitely presented schemes and their properties to a finite stage"},{"n":5,"after":[2,3,4],"title":"feat: extending finite-presentation models across a quasi-compact open"},{"n":6,"after":[1,2,3,4,5],"title":"feat: absolute Noetherian approximation of quasi-compact quasi-separated schemes"}]}-->
# Lookahead: `noetherian-approximation` (SchemeAndStackFoundations §0.9)

Built on `main` at `ab1c5af023`. Status: **partial**.

The roadmap pins no Lean forms for §0.9 in `Suggested.lean`; the target is specified by the
README only (`affine_transition_limits`, `noetherian_approximation`,
`finite_presentation_limits`).

## Stubbed declarations

### `qcoh-extension`: finite-type submodule extension (Stacks 01PF)

`Suggested.lean` pins no Lean signature for `qcoh_extension`; its README §0.4 states it in prose:
"a finite-type quasi-coherent submodule of `j^*G` is `j^*G'` for a finite-type quasi-coherent
submodule `G' ⊆ G` (Lemma 28.23.2 (01PF))". The open supplier PR #22951 lands parts (1) and (2)
of 01PE as `AlgebraicGeometry.Scheme.Modules.exists_isQuasicoherent_restrict_iso` and
`AlgebraicGeometry.Scheme.Modules.exists_mono_restrict_iso_of_isQuasicoherent`, in
`TauCeti/AlgebraicGeometry/Modules/Quasicoherent/Extension.lean`; it does not yet contain 01PF.
PR #22968 adds finite type checked on an open cover. The stub follows #22951's form of part (2),
adding the finite-type hypotheses and conclusion, and qcqs of `X` (which 01PF needs and the README
states):

```lean
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_restrict_iso
    [QuasiCompact j] [CompactSpace X] [QuasiSeparatedSpace X] {G : X.Modules}
    [G.IsQuasicoherent] {F : U.Modules} [F.IsQuasicoherent] [F.IsFiniteType]
    (i : F ⟶ G.restrict j) [Mono i] :
    ∃ (G' : X.Modules) (_ : G'.IsQuasicoherent) (_ : G'.IsFiniteType) (i' : G' ⟶ G) (_ : Mono i')
      (e : G'.restrict j ≅ F), (Scheme.Modules.restrictFunctor j).map i' = e.hom ≫ i
```

(in `namespace TauCeti.AlgebraicGeometry` with `variable {U X : Scheme.{u}} (j : U ⟶ X)
[IsOpenImmersion j]`, as in #22951). Differences from #22951's part (2): the added
`[CompactSpace X] [QuasiSeparatedSpace X] [F.IsFiniteType]` hypotheses and `G'.IsFiniteType`
conclusion (the content of 01PF); the "isomorphism over `V`" clause of #22951 is dropped since
split 5 does not consume it. No proved declaration on this branch uses the stub yet: it is
consumed by split 5 (extending a finite-type quasi-coherent ideal sheaf, cutting out the closure
of a finite-presentation model over an open, from `U` to `X`).

## Splits

1. **feat: separation and affineness of limits of schemes with affine transition maps**
   (after: none) — *proved*. File `TauCeti/AlgebraicGeometry/Limits/AffineTransition.lean`
   (94 lines): `TauCeti.AlgebraicGeometry.Scheme.isSeparated_of_isLimit`,
   `TauCeti.AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_isLimit` (the separatedness half of
   `affine_transition_limits`, 01YX + 01S7; quasi-compactness is Mathlib's
   `Scheme.compactSpace_of_isLimit`), `isAffine_of_isLimit`, `isQuasiAffine_of_isLimit` (a
   member's (quasi-)affineness passes to the limit) and `isAffine_iff_exists_of_isLimit`,
   `isQuasiAffine_iff_exists_of_isLimit` (for qcqs members, combined with Mathlib's 01Z6/01Z5
   converses `Scheme.exists_isAffine_of_isLimit`, `Scheme.exists_isQuasiAffine_of_isLimit`).
2. **feat: Noetherian approximation of affine schemes** (after: none) — *proved*.
   File `TauCeti/AlgebraicGeometry/Limits/NoetherianApproximation.lean` (105 lines):
   `finsetAdjoinDiagram`, `finsetAdjoinCocone`, `isColimitFinsetAdjoinCocone` (every ring is the
   filtered colimit of its finitely generated `ℤ`-subalgebras), the instance
   `Algebra.FinitePresentation ℤ ((finsetAdjoinDiagram A).obj s)`,
   `locallyOfFinitePresentation_terminal_from_Spec`, and
   `Scheme.exists_isLimit_finitePresentation_of_isAffine` (the affine case of 01ZA).
3. **feat: existence of cofiltered limits of schemes with affine transition maps** (after: 1) —
   *remaining*. `affine_transition_limits` existence (01YW: relative `Spec` over a member of the
   colimit of the pushed-forward quasi-coherent algebras, using `TauCeti/AlgebraicGeometry/
   RelativeSpec`), affine-locality (01YX) and `|lim X_i| = lim |X_i|` (0CUF), into
   `Limits/AffineTransition.lean`.
4. **feat: descent of finitely presented schemes and their properties to a finite stage**
   (after: 3) — *partly proved*. File `TauCeti/AlgebraicGeometry/Limits/FinitePresentation.lean`
   (65 lines so far) proves the absolute (over `ℤ`, i.e. the terminal scheme) form of Stacks 01ZC,
   specialising Mathlib's relative statements:
   `TauCeti.AlgebraicGeometry.Scheme.exists_map_comp_eq_of_isLimit` (two morphisms `Dᵢ ⟶ X`, `X`
   locally of finite type over `ℤ`, agreeing on the limit agree at some stage) and
   `TauCeti.AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_isLimit` (every morphism from the
   limit to `X` locally of finite presentation over `ℤ` factors through some `Dᵢ`). Remaining in
   this split: `finite_presentation_limits` proper — 01ZM (a finitely presented scheme over the
   limit descends to a finite stage), and flat, smooth, étale, proper, finite, closed immersion,
   open immersion, isomorphism inherited from a finite stage (04AI, 0C0C, 07RP, 081F, 01ZO, 01ZP,
   0EUU, 081E), into the same file; likely itself two PRs.
5. **feat: extending finite-presentation models across a quasi-compact open** (after: 2, 3, 4) —
   *remaining*. Stacks 01Z7, 01Z9, 07RN: given `X = U ∪ W`, `W` affine, and `U` a limit of
   f.p. `ℤ`-schemes, glue an f.p. model over `W`; consumes the stub
   `exists_isFiniteType_mono_restrict_iso` to extend the finite-type ideal sheaf. New file
   `Limits/NoetherianApproximation/Extension.lean`.
6. **feat: absolute Noetherian approximation of quasi-compact quasi-separated schemes**
   (after: 1, 2, 3, 4, 5) — *remaining*. `noetherian_approximation` (01ZA) by induction on the
   number of affines in a cover, starting from split 2; completes the target.

## What remains

Proved: the separatedness/quasi-separatedness and (quasi-)affineness criteria of limits with affine
transition maps, the full affine case of absolute Noetherian approximation, and the absolute
factorization of morphisms from a limit into a scheme locally of finite presentation over `ℤ`
(01ZC over `ℤ`, the part of split 4 that split 6 consumes to compare models). Remaining: splits 3–6 above — existence and
topology of affine-transition limits, `finite_presentation_limits`, the extension step across an
open (the only consumer of the `qcoh-extension` stub), and the qcqs induction for
`noetherian_approximation`.
