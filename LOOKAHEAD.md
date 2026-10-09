<!--tauceti-lookahead:v1 {"area":"LocalGaloisGroups","slug":"tate-module-linear-equiv","main":"39c285d3e89411b9597fe4f8ef4d1bc3f155b264","status":"complete","suppliers":["nonempty-tate-module"],"splits":[{"n":1,"after":[],"title":"feat: the integral decomposition of the Tate module of a layer"}]}-->
# Lookahead: `tate-module-linear-equiv` (LocalGaloisGroups)

Target: Layer 7 Step 3, the integral decomposition `Y ≃ M₀ ⊕ ℤ_p[G]^N` as `ℤ_p[G]`-modules
(the isomorphism `(∗∗)` in the proof of NSW (7.4.1)). Built on `main` at
`39c285d3e89411b9597fe4f8ef4d1bc3f155b264`. **Status: complete** — the whole target is proved
against the stub below, with no `sorry` outside `TauCeti/Lookahead/`.

## Stubbed declarations

Supplier `nonempty-tate-module` (open PR #13651, which defines the structure; `nonempty_…` is
still to come). The target consumes **only the structure**, not the existence theorem, so only
the structure is stubbed.

### `TateModule` → `TauCeti.LayerTateModule`

`Suggested.lean` signature (verbatim):

```lean
structure TateModule where
  /-- The carrier `Y`. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) carrier]
  /-- The inclusion of `A(L)`. -/
  ι : Additive ↥(padicCompletionUnits p L) →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] carrier
  /-- The projection onto the augmentation ideal. -/
  π : carrier →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] ↥(augmentationIdeal p (L ≃ₐ[K] L))
  ι_injective : Function.Injective ι
  π_surjective : Function.Surjective π
  exact : LinearMap.ker π = LinearMap.range ι
  finite : Module.Finite (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) carrier
  /-- Projective dimension at most one: a quotient of a free module by a projective kernel. -/
  projdim : ∃ (n : ℕ)
      (f : (Fin n → MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] carrier),
    Function.Surjective f ∧ Module.Projective (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (LinearMap.ker f)

attribute [instance] TateModule.addCommGroup TateModule.module
```

Stub (in `TauCeti/Lookahead/TateModuleLinearEquiv/Stubs.lean`), copied from PR #13651's diff
(`TauCeti/NumberTheory/Padics/MultiplicativeCompletion/LayerTateModule/Basic.lean`):

```lean
variable (p : ℕ) [Fact p.Prime] (L : Type u) [Field L] (K : Type u) [Field K] [Algebra K L]

structure LayerTateModule where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) carrier]
  ι : Additive ↑(padicCompletionUnits p L) →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] carrier
  π : carrier →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
    RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L))
  ι_injective : Function.Injective ι
  π_surjective : Function.Surjective π
  exact : LinearMap.ker π = LinearMap.range ι
  finite : Module.Finite (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) carrier
  projdim : ∃ (n : ℕ) (f : (Fin n → MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) →ₗ[MonoidAlgebra ℤ_[p]
      (L ≃ₐ[K] L)] carrier),
    Function.Surjective f ∧ Module.Projective (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (LinearMap.ker f)

attribute [instance] LayerTateModule.addCommGroup LayerTateModule.module
```

Differences from `Suggested.lean`, all taken from PR #13651:

- Name `TateModule` → `LayerTateModule`: `TauCeti.TateModule` is already the `p`-adic Tate module
  of an abelian group on `main`.
- `augmentationIdeal p (L ≃ₐ[K] L)` → `RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L))`:
  `main` has no `augmentationIdeal p G` as a left ideal; the landed rational decomposition uses
  this spelling too.
- `L K : Type u` are explicit section variables (the roadmap's section binds them likewise).

A structure has no body to `sorry`; it is restated field for field. The stub file states no
API about it beyond its fields, and the proof uses only the fields (`ι`, `π`, `ι_injective`,
`π_surjective`, `exact`, `finite`, `projdim`). `LayerTateModule.exact_ι_π` from the PR is not
needed (`LinearMap.exact_iff.mpr Y.exact` is used instead) and is not stubbed.

**Swap:** delete `TauCeti/Lookahead/`, and in
`TauCeti/NumberTheory/Padics/MultiplicativeCompletion/LayerTateModule/Decomposition.lean` replace
`public import TauCeti.Lookahead.TateModuleLinearEquiv.Stubs` by
`public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.LayerTateModule.Basic`.

## The target as proved, and how it differs from the pinned form

`Suggested.lean` pins

```lean
theorem tateModule_linearEquiv (Y : TateModule p L K) (σ τ : L ≃ₐ[K] L) (a b : ℕ)
    (_hσ : ∀ ζ ∈ pPowerRootsOfUnity p L, Units.map (σ : L →* L) ζ = ζ ^ a)
    (_hτ : ∀ ζ ∈ pPowerRootsOfUnity p L, Units.map (τ : L →* L) ζ = ζ ^ b)
    (_hsharp : Nat.card (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L) ⧸ Ideal.span
        {MonoidAlgebra.single σ (1 : ℤ_[p]) - a, MonoidAlgebra.single τ (1 : ℤ_[p]) - b})
        = localRootOfUnityOrder p L (finite_pPowerRootsOfUnity p L)) :
    Nonempty (Y.carrier ≃ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
      (tameFrameModule p (L ≃ₐ[K] L) σ τ a b ×
        (Fin (Module.finrank ℚ_[p] K) → MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))))
```

and the branch proves `TauCeti.LayerTateModule.nonempty_linearEquiv_tameFrameModule_prod`.

**The mathematics is already on `main`.** `main` has the decomposition in *unbundled* form:
`TauCeti.nonempty_linearEquiv_tameFrameModule_prod` in
`TauCeti/NumberTheory/Padics/MultiplicativeCompletion/Decomposition.lean` (#11916). It is stated
for any `Y` with a length-one resolution `0 → P₁ → P₀ → Y → 0` by finitely generated projectives
and an exact `0 → A(L) → Y → I_G → 0`; PR #13651's docstring already cites it. The proof covers
the stable isomorphism through torsion, the rational splitting, and NSW (5.6.11). So the target
against the supplier's bundled `LayerTateModule` is a corollary. Its only extra content is
turning `Y.projdim` into the resolution `0 → ker f → ℤ_p[G]^n → Y → 0`: `ker f` is finitely
generated because `ℤ_p[G]^n` is noetherian over `ℤ_p`. The bundled form goes in
`LayerTateModule` so that it does not collide with the unbundled name and is available as
`Y.nonempty_linearEquiv_tameFrameModule_prod`:

```lean
theorem LayerTateModule.nonempty_linearEquiv_tameFrameModule_prod (Y : LayerTateModule p L K)
    (h : Finite (pPowerRootsOfUnity p L)) (σ τ : L ≃ₐ[K] L)
    (hgen : Subgroup.closure {σ, τ} = ⊤) (a b : ℕ)
    (ha : ∀ ζ ∈ pPowerRootsOfUnity p L, Units.map (σ : L →* L) ζ = ζ ^ a)
    (hb : ∀ ζ ∈ pPowerRootsOfUnity p L, Units.map (τ : L →* L) ζ = ζ ^ b)
    (hcard : Nat.card (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L) ⧸ Ideal.span
      {MonoidAlgebra.single σ (1 : ℤ_[p]) - a, MonoidAlgebra.single τ (1 : ℤ_[p]) - b}) =
        localRootOfUnityOrder p L h) :
    Nonempty (Y.carrier ≃ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
      (TameFrameModule ℤ_[p] (L ≃ₐ[K] L) σ τ (a : ℤ_[p]) (b : ℤ_[p]) ×
        (Fin (Module.finrank ℚ_[p] K) → MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))))
```

under `[Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L] [Algebra ℚ_[p] K] [IsScalarTower ℚ_[p] K L]
[IsGalois K L]`, the hypotheses of the landed rational decomposition
`nonempty_padicCompletionUnits_tensorRat_linearEquiv`.

All the following differences are inherited from the landed unbundled theorem, which carries
exactly these hypotheses:

- **`hgen` (generation) is added.** The landed unbundled theorem has it. So does the landed
  torsion comparison it uses, `TauCeti.tameFrameModule_torsion_linearEquiv`, which requires
  `Subgroup.closure {σ, τ} = ⊤`, unlike its `Suggested.lean` form. Without generation the pinned statement is not reachable from the
  landed API, and is likely false. Sharpness then forces `q(L) = 1`, so the *left* ideal
  `(σ - a, τ - b)` is the unit ideal. But the torsion of `M₀` is dual to the quotient by the
  *right* ideal (`AuslanderReitenTranspose.torsionDualLinearEquiv`), which can be proper when
  `σ, τ` generate a proper subgroup. The README says generation is load-bearing for the sharp
  exponents, and the only consumer, `exists_relationModule_surjective_of_tameFrame`, carries
  `hgen`, so nothing downstream is lost. A human should align `Suggested.lean`.
- `finite_pPowerRootsOfUnity p L` → an explicit `h : Finite (pPowerRootsOfUnity p L)`, as in
  the landed `tameFrameModule_torsion_linearEquiv`. `main`'s finiteness lemma needs a local-field
  structure that the statement does not carry.
- `tameFrameModule p G σ τ a b` → `main`'s landed `TameFrameModule ℤ_[p] G σ τ (a : ℤ_[p]) (b : ℤ_[p])`.
- `[Module.Finite ℚ_[p] K] [FiniteDimensional K L]` are dropped: both follow from the tower, and
  the landed rational decomposition does not take them.

## Split plan

1. **feat: the integral decomposition of the Tate module of a layer** — after: none. Open it
   once the supplier's structure (PR #13651, `LayerTateModule/Basic.lean`) is on `main`. It is the
   only split and completes the target.
   File: `TauCeti/NumberTheory/Padics/MultiplicativeCompletion/LayerTateModule/Decomposition.lean`
   (80 lines). Adds `TauCeti.LayerTateModule.nonempty_linearEquiv_tameFrameModule_prod`.

The split is far below the usual 200 lines because `main` already carries the mathematics. It
could instead be folded into the supplier's follow-up PR that proves `nonempty_tateModule`, since
it shares that PR's file family and topic.

An earlier draft of this branch re-proved the stable isomorphism and a rational splitting lemma.
Both were deleted: they duplicate `main`'s
`TauCeti.nonempty_linearEquiv_tameFrameModule_prod` and
`TauCeti.IsFractionRing.nonempty_tensor_linearEquiv_prod_of_exact`.
