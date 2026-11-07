<!--tauceti-lookahead:v1 {"area":"ModularForms","slug":"galois-conjugate-newform","main":"08a51bc861c1164cec8967d78702731083676e5d","status":"partial","suppliers":["newspace-hecke-algebra-over-character-field"],"splits":[{"n":1,"after":[],"title":"feat(ModularForms/Newforms): the Galois conjugate of a newform"}]}-->
# Lookahead: `galois-conjugate-newform` (ModularForms, Layer 8G)

Built on `main` at `08a51bc861c1`. Status: **partial** (see *What remains*).

## Stubbed declarations (`TauCeti/Lookahead/GaloisConjugateNewform/Stubs.lean`)

The supplier `newspace-hecke-algebra-over-character-field` has no pinned form in
`ModularForms/Suggested.lean` (`grep` finds nothing) and no open PR; its pin is the README
bullet *The semisimple Hecke-algebra correspondence* (Layer 8G). Its partial PRs have
landed on `main`: `heckeTCuspNewCharFieldAlgebra`, `heckeTCuspNewCharFieldCharacter`,
`conjHeckeTCuspNewCharFieldCharacter` (`Newforms/Hecke/CharacterField.lean`) and the rational
algebra `heckeTDiamondCuspNewRationalAlgebra` with `Newform.heckeTDiamondCuspNewRationalCharacter`
(`Newforms/Hecke/Rational.lean`). `CharacterField.lean` says explicitly that the remaining
theorem, that the characters are exactly the newform characters, is not proved there. Only
that theorem is stubbed, in its two README forms.

1. `TauCeti.exists_heckeTCuspNewCharFieldCharacter_eq`
   - Suggested.lean signature: none (README: "the theorem that after `⊗ ℂ` its characters —
     equivalently its eigenlines — are exactly the normalized newforms of the space", over `ℚ(χ)`).
   - Stub:
     ```lean
     theorem exists_heckeTCuspNewCharFieldCharacter_eq {χ : (ZMod N)ˣ →* ℂˣ} (hk : 2 ≤ k)
         (φ : heckeTCuspNewCharFieldAlgebra k χ →ₐ[CharacterField χ] ℂ) :
         ∃ g, heckeTCuspNewCharFieldCharacter g = φ
     ```
   - Differences: `hk : 2 ≤ k` is added, matching the landed
     `forall_exists_heckeTCuspNewCharFieldCharacter_eq_iff` and `exists_conjHeckeTCuspNewCharFieldCharacter_eq`
     (the weight-1 number-field input is Layer 8W). `ℚ(χ)`-algebra characters into `ℂ` are the
     characters of the algebra `⊗_{ℚ(χ)} ℂ`, as in the landed file.
2. `TauCeti.Newform.exists_heckeTDiamondCuspNewRationalCharacter_eq`
   - Suggested.lean signature: none (README: the same theorem "over `ℚ`, after summing the
     character orbit").
   - Stub:
     ```lean
     theorem Newform.exists_heckeTDiamondCuspNewRationalCharacter_eq (hk : 2 ≤ k)
         (φ : heckeTDiamondCuspNewRationalAlgebra N k →ₐ[ℚ] ℂ) :
         ∃ g : Newform N k, Newform.heckeTDiamondCuspNewRationalCharacter g = φ
     ```
   - Differences: stated over main's rational algebra of the whole newspace of `Γ₁(N)`, which sums
     all nebentypus characters, not just one character orbit. Same `hk` as above.

## Splits

1. **feat(ModularForms/Newforms): the Galois conjugate of a newform** (after: none, once the
   supplier lands). File `TauCeti/NumberTheory/ModularForms/Newforms/GaloisConjugate.lean`.
   It adds `Newform.heckeTDiamondCuspNewRationalCharacter_mem_CoefficientField`,
   `Newform.heckeTDiamondCuspNewRationalCoefficientCharacter` (and its `coe_..._apply`),
   `Newform.galoisConj`, `Newform.heckeTDiamondCuspNewRationalCharacter_galoisConj`,
   `Newform.χ_galoisConj` (`χ_{f^σ} = σ ∘ χ_f`), `Newform.eigenvalue_galoisConj`,
   `Newform.qExpansion_coeff_galoisConj_prime` (`a_p(f^σ) = σ(a_p(f))`, `p ∤ N`),
   `Newform.qExpansion_coeff_galoisConj_of_coprime` (`aₙ(f^σ) = σ(aₙ(f))` for every positive
   `n` coprime to `N`, by the good prime-power recurrence and multiplicativity; private helper
   `qExpansion_coeff_galoisConj_of_coprime_aux`),
   `Newform.eq_galoisConj_iff` (uniqueness), and
   `Newform.qExpansion_coeff_galoisConj_of_forall_char` (`aₙ(f^σ) = σ(aₙ(f))` for every `n`
   when `σ` fixes `ℚ(χ_f)`). The port replaces the stub import with the supplier's module.

## What remains

`f^σ` is defined for every embedding `σ : CoefficientField f →ₐ[ℚ] ℂ` (weight `k ≥ 2`).
`χ_{f^σ} = σ ∘ χ_f` is proved, and so is uniqueness. `aₙ(f^σ) = σ(aₙ(f))` is proved at every
positive `n` coprime to `N` for every `σ` (this round), and at every `n` for `σ` fixing `ℚ(χ_f)`.
Still open: `aₙ(f^σ) = σ(aₙ(f))` for arbitrary `σ` at indices sharing a factor with `N` (the
`U_p` eigenvalues; the rest follows by multiplicativity and `a_{p^r} = a_p^r` for `p ∣ N`). It needs a ℚ-algebra that contains **all** `Tₙ` and the
diamonds on the newspace summed over the character orbit. The supplier's README names it, but `main`'s
`heckeTDiamondCuspNewRationalAlgebra` holds only good `Tₚ` and diamonds. It cannot come from
the `ℚ(χ)` form alone because `σ` moves `χ`. The next round should either stub that ℚ-algebra
(with all `Tₙ`) together with its "characters are exactly the newforms" theorem, or wait for the
supplier to land it. Then it should define `galoisConj` through that algebra and prove the
coefficient identity at every `n`.
