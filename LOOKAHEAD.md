<!--tauceti-lookahead:v1 {"area":"ThetaSeries","slug":"disc-char","main":"e7068108eef137a393590a3e2a09f9b2dbb8b9e4","status":"complete","suppliers":[],"splits":[{"n":1,"after":[],"title":"feat: the nebentypus of an even lattice"}]}-->

# Lookahead: ThetaSeries `disc-char` (Layer 6F, the nebentypus)

Built on `main` at `e7068108eef137a393590a3e2a09f9b2dbb8b9e4`. Status: **complete**, with no
stubs and no `sorry` anywhere on the branch.

## Suppliers: none stubbed — `gauss-sum-eq` has already landed

The round named `gauss-sum-eq` (6E) as an unlanded supplier to stub. It is already on `main`, as
is most of 6F, under names that differ from `Suggested.lean`'s. That is why the list still
shows the item open:

| `Suggested.lean` (ThetaSeries) | landed on `main` | PR |
| --- | --- | --- |
| `gaussSum_eq` (6E) | `ZLattice.IsEven.gaussSum_eq_sqrt_card_mul_jacobiSym` (`ThetaSeries/GaussSum.lean`) | #28531 |
| `signedDisc L k` | `ZLattice.signedDiscr L` (no `k`; `signedDiscr_of_finrank_eq` gives the `(-1)^k` form) | — |
| `signedDisc_modEq` | `ZLattice.IsEven.signedDiscr_modEq_zero_or_one` | — |
| `factorsThrough_changeLevel_kroneckerChar_signedDisc` + `conductor_kroneckerChar_signedDisc_dvd_level` (6F) | `ZLattice.IsEven.conductor_kroneckerChar_signedDiscr_dvd_level` (via `TauCeti.conductor_kroneckerChar_dvd_iff`) | #28533 |
| `kroneckerChar` (`ℂ`-valued) | `TauCeti.kroneckerChar R` (any `CommRing R`) | — |

So `TauCeti/Lookahead/DiscChar/Stubs.lean` would contain nothing: the stub rules forbid restating
anything `main` has. I created no stub module. The branch proves the rest of the target directly
against `main`, and its one split can go to Tau Ceti as soon as a round allows it. It waits on no
supplier.

What `main` lacked, and what this branch adds, is the definition of `χ_L` and its four pinned
properties.

## The declarations (one new file)

`TauCeti/NumberTheory/ModularForms/ThetaSeries/Nebentypus.lean` (134 lines), in namespace
`ZLattice`:

- `ZLattice.discChar L : DirichletCharacter ℂ (level L)`, defined as
  `changeLevel (conductor ∣ N) (primitiveCharacter (kroneckerChar ℂ D_L))` when
  `IsEven L ∧ Even (finrank ℝ E)`, and the trivial character otherwise.
- `ZLattice.IsEven.discChar_eq_changeLevel`: unfolds `discChar` under its hypotheses.
- `ZLattice.IsEven.discChar_intCast`: `χ_L a = (D_L / a)` for `IsCoprime a (level L)`.
- `ZLattice.IsEven.discChar_natCast`: the `ℕ` form of the same evaluation.
- `ZLattice.discChar_isQuadratic`: `χ_L` is quadratic. This needs no hypothesis.
- `ZLattice.IsEven.discChar_neg_one`: `χ_L (-1) = (-1)^k` in rank `2k`.
- `ZLattice.IsEven.discChar_eq_one_of_isSquare`: `χ_L = 1` when `D_L` is a square.
- `ZLattice.IsEven.discChar_eq_one_of_isUnimodular`: `χ_L = 1` for an even unimodular `L`.

### Differences from `Suggested.lean`'s pinned 6F forms, and why

- **No `k` parameter.** `Suggested.lean` has `discChar L k` and `signedDisc L k`. `main`'s landed
  `signedDiscr L` dropped `k`: the sign comes from `finrank ℝ E`. The guard is therefore
  `IsEven L ∧ Even (finrank ℝ E)` and not `finrank ℝ E = 2 * k ∧ IsEven L`. Only
  `discChar_neg_one` takes `k`, through `hk : finrank ℝ E = 2 * k`, as in the landed
  `IsEven.kroneckerChar_signedDiscr_neg_one`.
- **Dot-notation namespace `ZLattice.IsEven`, with hypotheses `hL : IsEven L`,
  `hE : Even (finrank ℝ E)`.** This matches the neighbouring landed API
  (`ZLattice.IsEven.conductor_kroneckerChar_signedDiscr_dvd_level` and the rest of
  `ThetaSeries/GaussSum.lean`). Nothing here is under `namespace TauCeti`. The neighbouring
  ThetaSeries files all live in root `ZLattice`, and `hL.discChar_intCast` dot notation only
  resolves in `ZLattice.IsEven`.
- **`discChar_isQuadratic` takes no hypotheses.** The junk value `1` is quadratic too, so the
  pinned hypotheses would be unused (generality rubric).
- **Added `discChar_eq_one_of_isSquare`.** The roadmap's prose asks for triviality "when `D_L` is a
  square, and in particular when `L` is unimodular". `Suggested.lean` pins only the unimodular
  case, which is now derived from the square case.
- **Added `discChar_eq_changeLevel` and `discChar_natCast`.** These are the unfolding lemma and
  the `ℕ` evaluation (API rubric). Downstream consumers (7A) can then use the API without
  unfolding the `dite`.
- `factorsThrough_changeLevel_kroneckerChar_signedDisc` and
  `conductor_kroneckerChar_signedDisc_dvd_level` are not re-added. `main` has the conductor
  theorem as `IsEven.conductor_kroneckerChar_signedDiscr_dvd_level`, proved through the
  unit-kernel criterion `TauCeti.conductor_kroneckerChar_dvd_iff`.

## Split plan

1. **`feat: the nebentypus of an even lattice`**. File:
   `TauCeti/NumberTheory/ModularForms/ThetaSeries/Nebentypus.lean` (new, 134 lines). Adds every
   declaration listed above. Needs no earlier split, since everything it imports is on `main`.
   It completes the target `disc-char`. PR description line: `Roadmap: ThetaSeries`.
