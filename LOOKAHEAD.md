<!--tauceti-lookahead:v1 {"area":"ModularForms","slug":"galois-conjugate-newform","main":"5f8b5c6fc72ef02143a5bd96d1b787615f8312df","status":"complete","suppliers":["newspace-hecke-algebra-over-character-field"],"splits":[{"n":1,"after":[],"title":"feat(ModularForms/Newforms/Hecke): the full Hecke algebra of the newspace and its newform characters"},{"n":2,"after":[1],"title":"feat(ModularForms/Newforms): the Galois conjugate of a newform"}]}-->
# Lookahead: `galois-conjugate-newform` (ModularForms, Layer 8G)

Built on `main` at `5f8b5c6fc72e`. Status: **complete**, modulo the one supplier stub below.

The target is proved in full: for a newform `f` of weight `k ≥ 2` and an embedding
`σ : CoefficientField f →ₐ[ℚ] ℂ`, `Newform.galoisConj hk f σ` is a newform with
`χ_{f^σ} = σ ∘ χ_f` (`Newform.χ_galoisConj`) and `aₙ(f^σ) = σ(aₙ(f))` at **every** positive
index `n` (`Newform.qExpansion_coeff_galoisConj`), and it is the unique newform with that
nebentypus and those good eigenvalues (`Newform.eq_galoisConj_iff`).

## Stubbed declaration (`TauCeti/Lookahead/GaloisConjugateNewform/Stubs.lean`)

The supplier `newspace-hecke-algebra-over-character-field` has no pinned form in
`ModularForms/Suggested.lean` (`grep` finds nothing) and no open PR; its pin is the README
bullet *The semisimple Hecke-algebra correspondence* (Layer 8G): "The finite Hecke algebra of
the newspace over ℚ[χ] [or over ℚ, after summing the character orbit]; the theorem that after
⊗ ℂ its characters … are exactly the normalized newforms of the space". Its partial PRs
(#22665, #28276) landed the `ℚ(χ)` algebra and its conjugate characters
(`Newforms/Hecke/CharacterField.lean`) and the rational algebra of the good `T_p` and diamonds
(`Newforms/Hecke/Rational.lean`). Only the correspondence theorem is stubbed.

1. `TauCeti.Newform.exists_heckeTDiamondCuspNewFullRationalCharacter_eq`
   - Suggested.lean signature: none (README: "the theorem that after `⊗ ℂ` its characters —
     equivalently its eigenlines — are exactly the normalized newforms of the space", over `ℚ`).
   - Stub:
     ```lean
     theorem Newform.exists_heckeTDiamondCuspNewFullRationalCharacter_eq (hk : 2 ≤ k)
         (φ : heckeTDiamondCuspNewFullRationalAlgebra N k →ₐ[ℚ] ℂ) :
         ∃ g : Newform N k, Newform.heckeTDiamondCuspNewFullRationalCharacter g = φ
     ```
   - Differences and reasons:
     * The algebra is the rational algebra generated on the whole newspace of `Γ₁(N)` by `T_p`
       at **every** prime (the `U_p` at `p ∣ N` included) and the diamonds, defined for real in
       split 1 (`Newforms/Hecke/Full.lean`). It sums all nebentypus characters, which contains
       the README's "after summing the character orbit". The bad-prime operators are needed:
       `σ` moves `χ`, so the `ℚ(χ)` form cannot reach `aₚ` for `p ∣ N`, and `main`'s
       `heckeTDiamondCuspNewRationalAlgebra` (good `T_p` only) cannot either, since a
       `ℚ`-character of the full algebra need not be forced on `U_p` by its good-prime restriction.
     * `hk : 2 ≤ k` is added, matching the landed `exists_conjHeckeTCuspNewCharFieldCharacter_eq`
       (the weight-one input is Layer 8W).
     * `ℚ`-algebra characters into `ℂ` are the characters of the algebra `⊗_ℚ ℂ`.
     * The statement is true (Shimura Thm 3.52 / Diamond–Shurman §6.5: the algebra is the
       `ℚ`-span of a lattice-preserving `ℤ`-algebra, so `⊗ ℂ` is the diagonal complex algebra,
       whose characters are the newforms by strong multiplicity one). When the supplier lands it
       in another form (for example over the integral or `ℚ(χ)`-orbit algebra), the port derives
       this statement from it, or the supplier's PR is asked to include the full algebra.
   - Earlier rounds stubbed `exists_heckeTCuspNewCharFieldCharacter_eq` and
     `Newform.exists_heckeTDiamondCuspNewRationalCharacter_eq`; both are no longer consumed and
     were removed.

## Splits

1. **feat(ModularForms/Newforms/Hecke): the full Hecke algebra of the newspace and its newform
   characters** (after: none; independent of the supplier). File
   `TauCeti/NumberTheory/ModularForms/Newforms/Hecke/Full.lean` (189 lines). Adds
   `heckeTCuspNatNewEnd` (+ `coe_heckeTCuspNatNewEnd_apply`), `heckeTDiamondCuspNewFullGenerators`,
   `heckeTDiamondCuspNewFullAlgebra`, `heckeTDiamondCuspNewFullRationalAlgebra`,
   the membership lemmas `heckeTCuspNatNewEnd_mem_…`, `diamondOpCuspNewEnd_mem_…`,
   `heckeTDiamondCuspNewFullRationalAlgebra_le_iff`, `heckeTDiamondCuspNewFullRationalAlgebra_le`,
   `heckeTDiamondCuspNewFullRationalAlgebraToComplex`, `heckeTCuspNatNewEnd_basis`,
   `Newform.heckeTDiamondCuspNewFullCharacter`, `Newform.heckeTDiamondCuspNewFullRationalCharacter`,
   `Newform.apply_basis_eq_heckeTDiamondCuspNewFull(Rational)Character_smul`, and the evaluation
   lemmas `Newform.heckeTDiamondCuspNewFullRationalCharacter_apply_heckeTCuspNatNewEnd`
   (`a_p` at every prime) and `…_apply_diamondOpCuspNewEnd`. Roadmap: the supplier's "finite
   Hecke algebra of the newspace over ℚ"; it may instead ride with the supplier's PR.
2. **feat(ModularForms/Newforms): the Galois conjugate of a newform** (after: 1, and the
   supplier). File `TauCeti/NumberTheory/ModularForms/Newforms/GaloisConjugate.lean` (229 lines).
   Adds `Newform.heckeTDiamondCuspNewFullRationalCharacter_mem_CoefficientField`,
   `Newform.heckeTDiamondCuspNewFullRationalCoefficientCharacter` (+ `coe_…_apply`),
   `Newform.galoisConj`, `Newform.heckeTDiamondCuspNewFullRationalCharacter_galoisConj`,
   `Newform.χ_galoisConj` (`χ_{f^σ} = σ ∘ χ_f`), `Newform.qExpansion_coeff_galoisConj_prime`
   (every prime), `Newform.eigenvalue_galoisConj`, `Newform.eq_galoisConj_iff` (uniqueness),
   and `Newform.qExpansion_coeff_galoisConj` (`aₙ(f^σ) = σ(aₙ(f))`, every positive `n`; private
   helpers `eigenvalue_eq_qExpansion_coeff`, `qExpansion_coeff_galoisConj_aux`). The port replaces
   the stub import with the supplier's module.

## History

Earlier rounds proved the target at indices coprime to the level and for `σ` fixing `ℚ(χ_f)`.
This round (main `5f8b5c6fc72e`) built the full newspace Hecke algebra (split 1), moved the
stub to it, and closed the bad-prime indices: `a_p(f^σ) = σ(a_p(f))` at `p ∣ N` from the `U_p`
eigenvalue, then `a_{p^r} = a_p^r` (`qExpansion_coeff_prime_pow_of_mem_badPrimes`) and
multiplicativity of the full eigenform. The special-case theorems
`qExpansion_coeff_galoisConj_of_coprime` / `…_of_forall_char` became redundant and were removed.
