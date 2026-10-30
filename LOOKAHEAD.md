<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"leray-spectral-sequence","main":"ab1c5af023f864980704684df6008c9288ab4fcf","status":"partial","suppliers":["sheaf-h-pullback"],"splits":[{"n":1,"after":[],"title":"feat: the edge map of the Leray spectral sequence"},{"n":2,"after":[],"title":"feat: the Grothendieck spectral sequence of a composite of left exact functors"},{"n":3,"after":[],"title":"feat: the Čech double complex of a covering with coefficients in an injective resolution"},{"n":4,"after":[1,2,3],"title":"feat: the Leray and Čech-to-cohomology spectral sequences"}]}-->

# Lookahead: `leray-spectral-sequence` (SchemeAndStackFoundations §2.2)

Built on `main` at `ab1c5af023f864980704684df6008c9288ab4fcf`. Status: **partial**.

## Stubbed declarations (supplier `sheaf-h-pullback`)

`Suggested.lean` of SchemeAndStackFoundations pins **no** Lean form for `Sheaf.H.pullback`
(`grep -n 'H.pullback\|sheafPullback' Suggested.lean` finds nothing); the README §2.1 states it in
prose as `Sheaf.H.pullback pb G n : G.H n →+ (pb.obj G).H n`. The stubs therefore follow the
supplier's open PR #22647 (head `5d57f8bdf236594622909312be1bf9cd967b880d`), file
`TauCeti/CategoryTheory/Sites/SheafCohomology/Pullback.lean`, which is what will land. All live in
`TauCeti/Lookahead/LeraySpectralSequence/Stubs.lean`, namespace `CategoryTheory.Sheaf.H` (as in the
PR and the neighbouring `TauCeti/CategoryTheory/Sites/SheafCohomology/` files on `main`), under the
section variables of the PR:
`{C} [Category* C] {J} {D} [Category* D] {K} [HasSheafify J Ab.{w}] [HasSheafify K Ab.{w}]
[HasExt.{w₁} (Sheaf J Ab.{w})] [HasExt.{w₂} (Sheaf K Ab.{w})]`.

1. `Sheaf.H.pullback`
   - README (no `Suggested.lean` signature): `Sheaf.H.pullback pb G n : G.H n →+ (pb.obj G).H n`.
   - PR #22647: `def pullback (G : Sheaf J AddCommGrpCat.{w}) (n : ℕ) : H G n →+ H (pb.obj G) n`
     with section variables `(pb : Sheaf J Ab ⥤ Sheaf K Ab) [pb.Additive] [PreservesFiniteLimits pb]
     [PreservesFiniteColimits pb] (c : (constantSheaf K Ab).obj (of (ULift ℤ)) ⟶
     pb.obj ((constantSheaf J Ab).obj (of (ULift ℤ))))`.
   - Stub: the same, with `pb`, its three instances and `c` written as explicit binders of the
     `def` (a `sorry` body would otherwise drop the unused section variables, changing the arity),
     body `sorry`, `@[nolint unusedArguments]`.
   - Difference from the README: the extra comparison argument `c : ℤ_K ⟶ pb ℤ_J`. The README
     itself (§2.1 opening paragraph) requires it; the PR follows that. No difference from the PR.
2. `Sheaf.H.addEquiv₀_pullback` (PR, `@[simp]`):
   `Ext.addEquiv₀ (pullback pb c G 0 x) = c ≫ pb.map (Ext.addEquiv₀ x)`. Stub identical, `sorry`.
   This is the README's `pullback_zero` in Ext form.
3. `Sheaf.H.pullback_naturality` (PR):
   `pullback pb c G₂ n (H.map f n x) = H.map (pb.map f) n (pullback pb c G₁ n x)`. Stub identical.
4. `Sheaf.H.pullback_δ` (PR): for `hS : S.ShortExact`,
   `pullback pb c S.X₁ n₁ (H.δ hS n₀ n₁ h x) = H.δ (hS.map_of_exact pb) n₀ n₁ h (pullback pb c S.X₃ n₀ x)`.
   Stub identical.

The proof uses only these four statements, never the body of `pullback`. The PR's other
declarations (`pullback_apply`, `pullback_id`, `pullback_comp_apply`, `equiv₀_pullback_sheafPullback`,
`Functor.sheafPullbackConstantSheafIso`, `Functor.Initial.constHomEquiv`) are not consumed and not
stubbed. When #22647 lands: delete `Stubs.lean` and replace its import by
`TauCeti.CategoryTheory.Sites.SheafCohomology.Pullback`.

## What is proved

`TauCeti/CategoryTheory/Sites/SheafCohomology/LerayEdge.lean` (namespace `CategoryTheory.Sheaf.H`),
for `adj : pb ⊣ pf` with `pb` exact additive and `c : ℤ_K ⟶ pb ℤ_J` (for a morphism of sites `f`:
`pb = f⁻¹ = u.sheafPullback`, `pf = f_*`, `c` the inverse of `sheafPullbackConstantSheafIso`):

- `lerayEdge adj c F n : H (pf.obj F) n →+ H F n` — the edge map `E₂^{n,0} = Hⁿ(C, f_*F) → Hⁿ(D, F)`
  (pullback, then the counit), with `lerayEdge_apply`;
- `lerayEdge_naturality` — natural in `F`;
- `lerayEdge_δ` — commutes with connecting homomorphisms when `S` and `f_* S` are short exact;
- `addEquiv₀_lerayEdge` — in degree 0 it is `g ↦ c ≫ adj.homEquiv.symm g`;
- `lerayEdge_zero_bijective` — bijective in degree 0 when `c` is an isomorphism;
- `subsingleton_H_obj_of_injective` — `Hⁿ⁺¹(C, f_* I) = 0` for injective `I` (Stacks 072Z input);
- `lerayEdge_one_injective` — when `c` is an isomorphism and `Sheaf K Ab` has enough injectives,
  the edge map `H¹(C, f_* F) → H¹(D, F)` is injective: the first map of the five-term exact
  sequence, proved directly by embedding `F` into an injective and chasing the two long exact
  sequences (uses `pullback_δ` and `addEquiv₀_pullback` of the stubs).

## What remains

The spectral sequence itself. Concretely:
1. A Grothendieck spectral sequence for `G ∘ F` with `F` sending injectives to `G`-acyclics, in
   Mathlib's `Abelian.SpectralObject`/`HasSpectralSequence` language: Cartan–Eilenberg (or
   injective) resolutions of `F` applied to an injective resolution, the double complex, and the
   identification of its `E₂` page `R^p G (R^q F)`. `main` has the row-filtration spectral sequence
   of a first-quadrant (homological) bicomplex, `TauCeti/Algebra/Homology/SpectralSequence/Bicomplex.lean`,
   and finite-filtration convergence, `.../Filtered/Convergence.lean`, to build on; the `E₂`
   identification and the cohomological reindexing are not there.
2. `R^q f_*` on sites. The README assigns `Sheaf.higherDirectImage` to §2.1, but the listed supplier
   `sheaf-h-pullback` covers only `Sheaf.H.pullback`; the statement can use Mathlib's
   `(u.sheafPushforwardContinuous Ab J K).rightDerived q` directly, which is what
   `Sheaf.higherDirectImage pf q` unfolds to.
3. `leray_spectral_sequence` (with naturality in `F`, the relative form for `g ∘ f` and the
   identification of its `E₂^{n,0}` edge with `lerayEdge`), `cech_to_cohomology` and Leray's
   acyclicity theorem, from the Čech double complex `Ȟ^p(U, I^q)` of an injective resolution `I`.

## Split plan

1. **feat: the edge map of the Leray spectral sequence** — files:
   `TauCeti/CategoryTheory/Sites/SheafCohomology/LerayEdge.lean` (this branch, ~220 lines, importing
   the landed `Pullback.lean`). Adds `lerayEdge`, `lerayEdge_apply`, `lerayEdge_naturality`,
   `lerayEdge_δ`, `addEquiv₀_lerayEdge`, `lerayEdge_zero_bijective`,
   `subsingleton_H_obj_of_injective`, `lerayEdge_one_injective`, `lerayEdge_bijective`. After: none (needs #22647 on `main`).
2. **feat: the Grothendieck spectral sequence of a composite of left exact functors** — files under
   `TauCeti/Algebra/Homology/SpectralSequence/Grothendieck*.lean`: the double complex of resolutions,
   its `E₂` identification and convergence. After: none. (Not yet written.)
3. **feat: the Čech double complex of a covering with coefficients in an injective resolution** —
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Cech/DoubleComplex.lean`. After: none. (Not yet written.)
4. **feat: the Leray and Čech-to-cohomology spectral sequences** —
   `TauCeti/CategoryTheory/Sites/SheafCohomology/Leray.lean`: `leray_spectral_sequence`, its
   naturality, relative form and edge maps, `cech_to_cohomology`, Leray's acyclicity theorem. After:
   1, 2, 3. The only split that completes the target. (Not yet written.)
