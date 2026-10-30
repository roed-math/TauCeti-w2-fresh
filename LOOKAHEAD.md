<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"qcoh-extension","main":"ea7e54cf967c2ab502c7e69bf69501e5a3ae3130","status":"partial","suppliers":["qcoh-pushforward"],"splits":[{"n":1,"after":[],"title":"feat: extend quasi-coherent modules and submodules along quasi-compact open immersions"},{"n":2,"after":[],"title":"feat: finite type of sheaves of modules can be checked on an open cover"},{"n":3,"after":[2],"title":"feat: quasi-coherent modules on affine schemes are unions of finite-type submodules"},{"n":4,"after":[1,2,3],"title":"feat: extend finite-type and finitely presented quasi-coherent modules along quasi-compact open immersions"}]}-->

# Lookahead: `qcoh-extension` (SchemeAndStackFoundations, Layer 0, §0.4)

Built on `main` at `ea7e54cf967c2ab502c7e69bf69501e5a3ae3130`. Status: **partial** (last updated in session 7, 2026-10-30). Stacks
Lemma 28.23.1 (01PE), parts (1) and (2), is proved against a stub of the supplier. So is the
first, supplier-free step of 01PG: finitely many global sections of a quasi-coherent module lie
in a quasi-coherent submodule of finite type. So is the affine case of 01PG: on an affine scheme
a quasi-coherent module is the union of its finite-type quasi-coherent submodules. So is
directedness: finite-type quasi-coherent submodules form a directed family. So is the
locality of finite type: a module whose restrictions to an open cover are of finite type is of
finite type (session 6). So is the gluing step of the 01PF induction over `X = U ∪ W`
(session 7). The qcqs case
of 01PG and the finite-type and finitely presented parts (01PF, 0G41, 01PI) are not proved yet.

## Stubbed declarations (supplier `qcoh-pushforward`)

The stubs are in `TauCeti/Lookahead/QcohExtension/Stubs.lean`.

### `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward`

`Suggested.lean` signature: **none**. The SchemeAndStackFoundations `Suggested.lean` pins no
declaration for `qcoh_pushforward` (or `qcoh_extension`). `grep -n 'qcoh_\|pushforward'` finds
nothing in that file. The README §0.4 prose is the only roadmap specification.

PR #21787's form, from its diff
(`TauCeti/AlgebraicGeometry/Modules/Quasicoherent/Pushforward/QuasiSeparated.lean`, head
`e9afd8375f3d4db3dd83a3d59d4154e4179a7798`):

```lean
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (M : X.Modules) (f : X ⟶ Y)
instance isQuasicoherent_pushforward [M.IsQuasicoherent] [QuasiCompact f] [QuasiSeparated f] :
    ((pushforward f).obj M).IsQuasicoherent
```

The stub as stated: the PR's form verbatim, in the same namespace and with the same variables,
with body `sorry`. Differences: none in the statement. The stub module imports
`TauCeti.AlgebraicGeometry.Modules.Pushforward`, `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`
and `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`. The PR's module instead imports
`TauCeti.AlgebraicGeometry.Modules.Localization`. When the supplier lands, replace
`public import TauCeti.Lookahead.QcohExtension.Stubs` with
`public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated`.

The other closure properties of `qcoh_pushforward` that the proof uses are kernels and
cokernels. They are already on `main` (`Quasicoherent/Kernels.lean`,
`Quasicoherent/Cokernels.lean`), so they are not stubbed.

## What is proved

The proofs are in `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/Extension.lean`, in
`namespace TauCeti.AlgebraicGeometry` with `_root_` names, following `Quasicoherent/Kernels.lean`:

- `AlgebraicGeometry.Scheme.Modules.exists_isQuasicoherent_restrict_iso`: let `j : U ⟶ X` be a
  quasi-compact open immersion and `F` a quasi-coherent module on `U`. Then
  `∃ G, G.IsQuasicoherent ∧ Nonempty (G.restrict j ≅ F)`, with `G = j_* F` (01PE (1)).
- `AlgebraicGeometry.Scheme.Modules.exists_mono_restrict_iso_of_isQuasicoherent`: let `G` be
  quasi-coherent on `X` and `i : F ⟶ G.restrict j` a mono with `F` quasi-coherent. Then there
  are a quasi-coherent `G'`, a mono `i' : G' ⟶ G` and `e : G'.restrict j ≅ F` with
  `j^*(i') = e.hom ≫ i` (01PE (2)). Here `G'` is the kernel of
  `G ⟶ j_* (cokernel i)`, the adjoint of the cokernel projection. Session 7 added a second
  conclusion: for every open `V ⊆ X` such that `i` is an isomorphism over `j⁻¹ V`, `i'` is an
  isomorphism over `V`. The proof shows that `cokernel i` vanishes over `j⁻¹ V`, so
  `j_* (cokernel i)` vanishes over `V` (by `restrictPushforwardIso` from `Modules/Pushforward.lean`
  on `main`), and the kernel of a map to zero is everything.

Neither proof needs `X` quasi-compact or quasi-separated: an open immersion is quasi-separated,
so only quasi-compactness of `j` is used.

The first step of 01PG is in `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/FiniteTypeImage.lean`
(added in session 2, 2026-10-29). It does not use the stub, and it holds on any scheme `X`:

- `AlgebraicGeometry.Scheme.Modules.isFiniteType_of_generatingSections`: a module with a finite
  family of global generating sections (`σ : M.GeneratingSections` with `σ.IsFiniteType`) is of
  finite type. It uses Mathlib's `GeneratingSections.localGeneratorsData`.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_image` (instance): the image of a morphism of
  quasi-coherent modules is quasi-coherent. It is `kernel (cokernel.π f)` up to
  `Abelian.imageIsoImage`.
- `AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_sections`: let `N` be
  quasi-coherent and `s : I → N.sections` with `I` finite. Then there is a quasi-coherent
  submodule `i : N' ⟶ N` of finite type and `t : I → N'.sections` with
  `sectionsMap i (t k) = s k`. Here `N'` is the image of `𝒪_X^I ⟶ N`.

Session 4 (2026-10-30) added to `FiniteTypeImage.lean`, again without the stub:

- `AlgebraicGeometry.Scheme.Modules.epi_overFunctor_map`: restriction to the slice site over an
  open `U` (`SheafOfModules.overFunctor`) preserves epimorphisms. Up to Mathlib's
  `overFunctorEquiv` it is `restrictFunctor U.ι`, a left adjoint, followed by an equivalence.
- `AlgebraicGeometry.Scheme.Modules.isFiniteType_of_epi`: a quotient of a module of finite type
  is of finite type (push local generators forward with `GeneratingSections.ofEpi`).
- `AlgebraicGeometry.Scheme.Modules.isFiniteType_image`: the image of a morphism out of a module
  of finite type is of finite type. It replaces session 2's
  `isFiniteType_image_of_generatingSections`, which was its special case and is removed.
- `AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_factors`: directedness. Any two
  finite-type quasi-coherent submodules `N₁, N₂ ⟶ N` of a quasi-coherent `N` factor through a
  third, the image of `N₁ ⊞ N₂ ⟶ N` (using `isFiniteType_biprod` from `Modules/Biprod.lean`).

Session 5 (2026-10-30) added to `FiniteTypeImage.lean`, without the stub:

- `AlgebraicGeometry.Scheme.Modules.isFiniteType_restrict` (instance): the restriction of a
  module of finite type along an open immersion is of finite type. It applies
  `isFiniteType_of_epi` to `restrictFunctorIsoPullback`, and then uses `isFiniteType_pullback`
  from `Modules/Pullback/Basic.lean`. The qcqs induction for 01PG needs it, to restrict a
  finite-type submodule to `U ∩ W`.

Session 6 (2026-10-30) proved that finite type is local, without the stub. New file
`TauCeti/Algebra/Category/ModuleCat/Sheaf/FiniteType.lean` (site level, in
`namespace TauCeti.SheafOfModules` with `_root_` names, following `Sheaf/LocallyFree.lean`):

- `SheafOfModules.IsFiniteType.of_iso`: finite type is invariant under isomorphism.
- `SheafOfModules.IsFiniteType.of_coversTop`: finite type can be checked on a covering family.
  It combines local generators with `SheafOfModules.LocalGeneratorsData.bind`, already on `main`
  (`Sheaf/LocallyFree.lean`), as `IsLocallyFree.of_coversTop` does.
- `SheafOfModules.LocalGeneratorsData.pushforward` and the instance
  `SheafOfModules.LocalGeneratorsData.isFiniteType_pushforward`: local generators carried along a
  continuous and cocontinuous functor. This copies Mathlib's
  `SheafOfModules.QuasicoherentData.pushforward`, with generators in place of presentations.
- `SheafOfModules.isFiniteType_pushforward_of_isLeftAdjoint`: the finite-type analogue of
  Mathlib's `isQuasicoherent_pushforward_of_isLeftAdjoint`. Mathlib's proof sets
  `backward.isDefEq.respectTransparency false`, which Tau Ceti forbids. Here the `IsIso` of the
  restricted ring map is supplied by `Functor.map_isIso` instead.

New file `TauCeti/AlgebraicGeometry/Modules/Restriction/FiniteType.lean` (scheme level, in
`namespace TauCeti.AlgebraicGeometry`, following `Quasicoherent/Restriction.lean`):

- `TauCeti.AlgebraicGeometry.isFiniteType_overEquiv_inverse` (instance): the inverse
  open-subscheme equivalence preserves finite type.
- `TauCeti.AlgebraicGeometry.isFiniteType_over_of_isFiniteType_restrict`: finite type of
  `M.restrict U.ι` gives finite type of `M.over U`.
- `TauCeti.AlgebraicGeometry.isFiniteType_of_isFiniteType_restrict`: finite type can be checked
  on restrictions to an open cover. It is the analogue of
  `isQuasicoherent_of_isQuasicoherent_restrict`.
- `TauCeti.AlgebraicGeometry.isFiniteType_of_isFiniteType_restrict_affineOpens`: the same on
  all affine opens.

Session 7 (2026-10-30) added the gluing step of the 01PF induction. New file
`TauCeti/AlgebraicGeometry/Modules/Quasicoherent/Extension/FiniteType.lean`, which uses the stub
through `Extension.lean`:

- `AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_restrict_iso_of_sup_eq_top`: let
  `X = U ⊔ W` with `W.ι` quasi-compact, and let `G` be quasi-coherent with `G|_U` of finite type.
  Let `i : H ⟶ G|_W` be a finite-type quasi-coherent submodule that is an isomorphism over
  `W.ι ⁻¹ᵁ U` (that is, over `U ∩ W`). Then there are a finite-type quasi-coherent submodule
  `i' : G' ⟶ G` that is an isomorphism over `U`, and an isomorphism `e : G'|_W ≅ H` with
  `i'|_W = e.hom ≫ i`. `G'` is the 01PE (2) extension of `H` along `W.ι`. It is all of `G` over
  `U` by the new conclusion of 01PE (2), and it is of finite type by
  `isFiniteType_of_isFiniteType_restrict` on the cover `{U, W}`.

This gluing step replaces the kernel of `N ⟶ j_*(N|_U / F) ⊞ k_*(N|_W / F'')`, which the
session 6 notes proposed. In Stacks' proof, the submodule over `U` is first extended to all of
`X` with 01PE (2), as `G` here. So it suffices to extend the piece over `W`, inside `G`.

The affine case of 01PG (added in session 3, 2026-10-29) does not use the stub either. New file
`TauCeti/AlgebraicGeometry/Modules/Quasicoherent/AffineGlobalSections.lean`:

- `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_restrictFunctor_map`: restriction along an
  isomorphism of schemes `j` reflects isomorphisms of modules (via `restrictFunctorComp`,
  `restrictFunctorCongr`, `restrictFunctorId`).
- `AlgebraicGeometry.Scheme.Modules.isIso_of_bijective_sectionsFunctor_map_top`: on an affine
  `X`, a morphism of quasi-coherent modules bijective on global sections (`sectionsFunctor ⊤`) is
  an isomorphism. Proof: `IsAffineOpen.restrictFromSpecCompModuleSpecΓFunctorIso` for `⊤`, the
  tilde equivalence reflects isomorphisms, and `IsAffineOpen.fromSpec_top` makes the chart an
  isomorphism.
- `AlgebraicGeometry.Scheme.Modules.isIso_of_mono_of_surjective_sectionsFunctor_map_top`: on an
  affine `X`, a mono of quasi-coherent modules surjective on global sections is an isomorphism.

And appended to `FiniteTypeImage.lean`:

- `AlgebraicGeometry.Scheme.Modules.isIso_of_mono_of_forall_isFiniteType_factors`: on an affine
  `X`, a quasi-coherent submodule `i : M ⟶ N` of a quasi-coherent `N` through which every
  finite-type quasi-coherent submodule of `N` factors is an isomorphism. This is the affine case
  of 01PG in mono form. It uses a private helper `sectionsOfTop` (a section over `⊤` as an element
  of `N.sections`). A reviewer may ask for that helper to become public API, for instance an
  equivalence `N.sections ≃ Γ(N, ⊤)`; Mathlib has none (checked `sectionsEquiv`, `IsInitial`).

Elaboration notes. `X.Modules` and `SheafOfModules X.ringCatSheaf` carry the same category
instance, but instance search does not unify across them. For example, `GeneratingSections.ofEpi`
needs `Epi` stated with `C := SheafOfModules X.ringCatSheaf`. Inside the
`_root_.AlgebraicGeometry.Scheme.Modules.*` declarations, write `_root_.SheafOfModules.free`, and
build `LocalGeneratorsData.IsFiniteType` with `constructor`, not with an anonymous constructor.

## What remains (for `status: complete`)

The plan follows Stacks' proof of 01PF (Lemma 28.23.2). Let `X` be qcqs, `j : U ⟶ X` a
quasi-compact open, `F` quasi-coherent on `X`, and `G ⊆ F|_U` of finite type and
quasi-coherent. Write `X = U ∪ W_1 ∪ … ∪ W_n` with the `W_k` affine, and induct on `n`. For
`X = U ∪ W` with `W` affine, extend `G` to a quasi-coherent `G'' ⊆ F` by 01PE (2). Then
`G''|_U ≅ G` is of finite type. Find a finite-type quasi-coherent `H ⊆ G''|_W` that is all of
`G''` over `U ∩ W`, and apply the gluing step
(`exists_isFiniteType_mono_restrict_iso_of_sup_eq_top`) to get a finite-type `G' ⊆ G'' ⊆ F`
that restricts to `G` over `U`.

1. **The missing input: finding `H`.** On an affine `W`, let `N` be quasi-coherent and
   `V ⊆ W` a quasi-compact open with `N|_V` of finite type. Find a finite-type quasi-coherent
   submodule `H ⊆ N` that is an isomorphism over `V`. A suggested proof: refine the local
   generators of `N|_V` to finitely many basic opens `D(f_k) ⊆ V`. Write each generator as
   `m / f_k^r` with `m ∈ Γ(N, W)`. Take `H` to be the image of `𝒪_W^{m's}`
   (`exists_isFiniteType_mono_sections`). Then `H ⟶ N` is an epimorphism on each `D(f_k)`, hence
   an isomorphism over `V`. The tools are on `main`: `Quasicoherent/Affine.lean` (tildes),
   `Quasicoherent/Colimits.lean` (sections over affines commute with colimits). Equivalently,
   the finite-type quasi-coherent submodules of `N` form a directed family whose union is `N`
   (the affine case is done: `isIso_of_mono_of_forall_isFiniteType_factors`), and a finite-type
   module over a quasi-compact base lies in one member of such a family.
2. **01PF (Lemma 28.23.2).** The induction on `n` above, given item 1. It carries the
   statement: a finite-type quasi-coherent submodule of `j^* F` is `j^* G'` for a finite-type
   quasi-coherent `G' ⊆ F`. The qcqs case of 01PG follows from 01PF and the affine case.
3. **0G41 (Lemma 28.23.5).** A finite-type `F` on `U` extends to a finite-type `G` on `X`: apply
   01PF to `F ⊆ (j_* F)|_U`. A finitely presented `F` extends to a finitely presented `G`.
4. **01PI (Lemma 28.23.4).** A map from a finitely presented `F` to `j^* H` extends to a map from
   a finitely presented extension of `F` to `H`.

Notes for the next session (checked against `main` at `ea7e54cf96`, 2026-10-30, session 7).
PR #21787 is still open, at head `e9afd8375f3d`, so the stub stays. Mathlib provides
`SheafOfModules.IsFiniteType` and `SheafOfModules.IsFinitePresentation`. `main` provides
`restrictPushforwardIso` (`Modules/Pushforward.lean`): restricting `f_* M` to an open `V` of the
base is pushing forward `M|_{f⁻¹ V}` along `f ∣_ V`.

## Split plan

1. **Split 1** (after: none, once `qcoh-pushforward` / PR #21787 has landed). File
   `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/Extension.lean` (103 lines), with
   `exists_isQuasicoherent_restrict_iso` and `exists_mono_restrict_iso_of_isQuasicoherent`
   (the latter including the conclusion over opens `V` where `i` is an isomorphism).
   Subject: `feat: extend quasi-coherent modules and submodules along quasi-compact open immersions`.
2. **Split 2** (after: none, independent of the supplier). Written. Files
   `TauCeti/Algebra/Category/ModuleCat/Sheaf/FiniteType.lean` (167 lines), with
   `SheafOfModules.IsFiniteType.of_iso`, `SheafOfModules.IsFiniteType.of_coversTop`,
   `SheafOfModules.LocalGeneratorsData.pushforward`,
   `SheafOfModules.LocalGeneratorsData.isFiniteType_pushforward` and
   `SheafOfModules.isFiniteType_pushforward_of_isLeftAdjoint`, and
   `TauCeti/AlgebraicGeometry/Modules/Restriction/FiniteType.lean` (70 lines), with
   `isFiniteType_overEquiv_inverse`, `isFiniteType_over_of_isFiniteType_restrict`,
   `isFiniteType_of_isFiniteType_restrict` and
   `isFiniteType_of_isFiniteType_restrict_affineOpens`.
   Subject: `feat: finite type of sheaves of modules can be checked on an open cover`.
3. **Split 3** (after: 2, independent of the supplier). Started. File
   `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/FiniteTypeImage.lean` (199 lines), with
   `isFiniteType_of_generatingSections`, `epi_overFunctor_map`, `isFiniteType_of_epi`,
   `isFiniteType_restrict`,
   `isQuasicoherent_image`, `isFiniteType_image`, `exists_isFiniteType_mono_sections`,
   `exists_isFiniteType_mono_factors` and `isIso_of_mono_of_forall_isFiniteType_factors`. Also
   `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/AffineGlobalSections.lean` (93 lines), with
   `isIso_of_isIso_restrictFunctor_map`, `isIso_of_bijective_sectionsFunctor_map_top` and
   `isIso_of_mono_of_surjective_sectionsFunctor_map_top`. Still to write: item 1 of "What
   remains" (on an affine scheme, a finite-type quasi-coherent submodule that is everything over
   a given quasi-compact open of finite type), in a sibling file. If the split exceeds about 600
   lines, the two existing files (the affine case and directedness, about 290 lines) can be
   opened alone first. The qcqs case of 01PG moved to split 4, because it follows from 01PF.
   Subject: `feat: quasi-coherent modules on affine schemes are unions of finite-type submodules`.
4. **Split 4** (after: 1, 2, 3). Started. File
   `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/Extension/FiniteType.lean` (67 lines), with
   the gluing step `exists_isFiniteType_mono_restrict_iso_of_sup_eq_top`. Still to add: the
   finite-type submodule extension (01PF), finite-type and finitely presented extension (0G41)
   and map extension (01PI), and the qcqs case of 01PG as a corollary of 01PF. These go in this file, or in siblings under `Extension/` if it
   grows past about 600 lines. It carries the exported
   finite-type extension theorem and is the only split that completes the target.
   Subject: `feat: extend finite-type and finitely presented quasi-coherent modules along quasi-compact open immersions`.
