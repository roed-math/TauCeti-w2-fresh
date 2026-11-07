<!--tauceti-lookahead:v1 {"area":"ModularForms","slug":"primitive-pair-unique","main":"4e97a69715ff64e710f3e9d69e5fdc67ea1d23aa","status":"complete","suppliers":["cross-level-strong-multiplicity-one"],"splits":[{"n":1,"after":[],"title":"feat(ModularForms/Newforms/Associated): the primitive pair is unique among all newforms"}]}-->

# Lookahead: `primitive-pair-unique` (ModularForms, Layer 4B)

Built on `main` at `4e97a69715ff64e710f3e9d69e5fdc67ea1d23aa`. Status: **complete** — the whole
target is proved, modulo the one stubbed supplier theorem.

## What was already on `main`

`TauCeti/NumberTheory/ModularForms/Newforms/Associated.lean` already proves the newform
decomposition (4A existence, plus span membership) and uniqueness of the pair `(M, g)` **only among
newforms whose nebentypus induces `χ`** (it consumes
`Newform.level_eq_and_coe_eq_of_comp_unitsMap_eq`, the nebentypus-compatible cross-level SMO that
the supplier's partial PRs landed). What 4B still lacked is uniqueness of the pair outright — the
roadmap's "the pair `(M, g)` is unique", with no hypothesis on the nebentypus of the competitor —
and the corollary that the eigenform lies in `span {g(dz) : d ∣ L/M}` for *every* newform `g` with
its good eigenvalues. Both need the nebentypus-free cross-level SMO, which is the supplier.

## Stubbed declaration

Supplier: `cross-level-strong-multiplicity-one` (ModularForms, Layer 5, Miyake Thm 4.6.19).

**Pinned form.** `Suggested.lean` pins no Lean signature for this target (the file seeds only the
Layer 10 dimension-formula instances); the pinned form is the README's statement, quoted verbatim:

> two normalized newforms `f`, `g` of the same weight and of levels `N`, `M` whose eigenvalues
> `a_p` agree at all but finitely many primes `p ∤ NM` satisfy `N = M`, have the same nebentypus,
> and are equal.

No open PR for this supplier could be inspected (the `gh` search failed in this sandbox), so the
stub follows the README and the conventions of the supplier's merged partials on `main`
(`TauCeti/NumberTheory/ModularForms/Newforms/StrongMultiplicityOne/Basic.lean`).

**Stub** (`TauCeti/Lookahead/PrimitivePairUnique/Stubs.lean`, namespace `HeckeRing.GL2`, where
all neighbouring newform code on `main` lives):

```lean
theorem Newform.level_eq_and_χ_comp_unitsMap_eq_and_coe_eq_of_forall_notMem_prime_eigenvalue_eq
    {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ} (f : Newform N k) (g : Newform M k) {S : Finset ℕ}
    (h : ∀ (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N) (hpM : p.Coprime M), p ∉ S →
      f.eigenvalue ⟨p, hp.pos⟩ hpN = g.eigenvalue ⟨p, hp.pos⟩ hpM) :
    N = M ∧ f.χ.comp (ZMod.unitsMap (Nat.dvd_lcm_left N M)) =
      g.χ.comp (ZMod.unitsMap (Nat.dvd_lcm_right N M)) ∧ ⇑f.toCuspForm = ⇑g.toCuspForm :=
  sorry
```

**Differences from the README statement, and why.**
- "all but finitely many primes `p ∤ NM`" is rendered as `p ∉ S` for a `Finset ℕ` `S`, with the
  coprimality proofs bound in the hypothesis, exactly as in the merged partial
  `Newform.level_eq_and_coe_eq_of_forall_notMem_prime_eigenvalue_eq` on `main`.
- "have the same nebentypus" is stated as equality of the two nebentypes pulled back to
  `(ZMod (lcm N M))ˣ`, since `f.χ` and `g.χ` live on different types until `N = M` is known; at
  `N = M` the reduction is onto, so this is equality of the nebentypes. This is the encoding `main`
  uses for the same notion (`hχ` of the merged partials, and
  `Newform.χ_comp_unitsMap_eq_of_forall_notMem_qExpansion_coeff_eq`).
- "are equal" is stated as `⇑f.toCuspForm = ⇑g.toCuspForm` (same function on `ℍ`), as `main`
  does across levels, because `f` and `g` have different types.
- No hypothesis on the nebentypes: this is exactly what distinguishes the supplier from the
  merged partial `Newform.level_eq_and_coe_eq_of_forall_notMem_prime_eigenvalue_eq`, whose `hχ`
  this target cannot supply. Name: the merged partial's name with the new nebentypus conclusion
  inserted (`…_and_χ_comp_unitsMap_eq_and_…`); if the supplier instead lands by dropping `hχ`
  from the existing theorem, the port only renames the three call sites and reads the nebentypus
  conclusion from the supplier's separate lemma.

The proof uses all three conclusions (the level and function equalities for uniqueness, the
nebentypus equality for `Newform.χ_comp_unitsMap_eq_of_forall_heckeTCuspNat_eq_smul`).

## Split plan

A single split; the change is about 100 lines in one existing file.

### Split 1 — `feat(ModularForms/Newforms/Associated): the primitive pair is unique among all newforms`

- Needs first: none (on `main` plus the landed supplier).
- File: `TauCeti/NumberTheory/ModularForms/Newforms/Associated.lean` (modified; the port
  replaces the stub import by the supplier's landed module).
- Adds (namespace `HeckeRing.GL2`):
  - `Newform.level_eq_and_χ_comp_unitsMap_eq_and_coe_eq_of_forall_prime_eigenvalue_eq` — two
    newforms of levels dividing `N` with the same eigenvalues at the primes `p ∤ N` (outside a
    finite set) have the same level and nebentypus and are the same function;
  - `Newform.χ_comp_unitsMap_eq_of_forall_heckeTCuspNat_eq_smul` — a newform with the eigenvalues
    of a nonzero good Hecke eigenvector of `S_k(N, χ)` has nebentypus inducing `χ`;
  - `EigenformAwayFromLevel.mem_span_levelRaise_of_eigenvalue_eq` — a good Hecke eigenform lies in
    `span {V_d g : d * M ∣ N}` for every newform `g` of level `M ∣ N` with its good eigenvalues.
- Strengthens (no compatibility copy kept, per the repository rules):
  `Newform.exists_newform_mem_span_levelRaise_of_forall_heckeTCuspNat_eq_smul` and
  `EigenformAwayFromLevel.exists_newform_mem_span_levelRaise` — their uniqueness clause drops the
  hypothesis `g'.χ.comp (ZMod.unitsMap hM') = χ`, so the pair `(M, g)` (the conductor `M` and the
  primitive form `g`) is unique among all newforms of levels dividing `N`. These are the target's
  exported theorems. Nothing on `main` used the old forms.
- Module docstring updated accordingly.
- `Roadmap: ModularForms`.
