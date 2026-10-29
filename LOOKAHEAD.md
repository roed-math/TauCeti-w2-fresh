<!--tauceti-lookahead:v1 {"area":"SchemeAndStackFoundations","slug":"qcoh-extension","main":"ea7e54cf967c2ab502c7e69bf69501e5a3ae3130","status":"partial","suppliers":["qcoh-pushforward"],"splits":[{"n":1,"after":[],"title":"feat: extend quasi-coherent modules and submodules along quasi-compact open immersions"},{"n":2,"after":[],"title":"feat: quasi-coherent modules on qcqs schemes are directed unions of finite-type submodules"},{"n":3,"after":[1,2],"title":"feat: extend finite-type and finitely presented quasi-coherent modules along quasi-compact open immersions"}]}-->

# Lookahead: `qcoh-extension` (SchemeAndStackFoundations, Layer 0, §0.4)

Built on `main` at `ea7e54cf967c2ab502c7e69bf69501e5a3ae3130`. Status: **partial**. Stacks
Lemma 28.23.1 (01PE), parts (1) and (2), is proved against a stub of the supplier. So is the
first, supplier-free step of 01PG: finitely many global sections of a quasi-coherent module lie
in a quasi-coherent submodule of finite type. The rest of 01PG and the finite-type and
finitely presented parts (01PF, 0G41, 01PI) are not proved yet.

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
  `G ⟶ j_* (cokernel i)`, the adjoint of the cokernel projection.

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
- `AlgebraicGeometry.Scheme.Modules.isFiniteType_image_of_generatingSections`: the image of a
  morphism out of a module with finitely many generating sections is of finite type.
- `AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_sections`: let `N` be
  quasi-coherent and `s : I → N.sections` with `I` finite. Then there is a quasi-coherent
  submodule `i : N' ⟶ N` of finite type and `t : I → N'.sections` with
  `sectionsMap i (t k) = s k`. Here `N'` is the image of `𝒪_X^I ⟶ N`.

Elaboration notes. `X.Modules` and `SheafOfModules X.ringCatSheaf` carry the same category
instance, but instance search does not unify across them. For example, `GeneratingSections.ofEpi`
needs `Epi` stated with `C := SheafOfModules X.ringCatSheaf`. Inside the
`_root_.AlgebraicGeometry.Scheme.Modules.*` declarations, write `_root_.SheafOfModules.free`, and
build `LocalGeneratorsData.IsFiniteType` with `constructor`, not with an anonymous constructor.

## What remains (for `status: complete`)

On a quasi-compact quasi-separated `X`:
1. 01PG (Stacks, Lemma 28.22.3): a quasi-coherent module is the directed union of its
   finite-type quasi-coherent submodules. `exists_isFiniteType_mono_sections` above is the
   finite-sections step. The affine case still needs the following lemma. On an affine `X`, a mono
   `i : N' ⟶ N` into a quasi-coherent `N` through which every global section of `N` factors is
   an isomorphism. This needs global generation on affines: `freeHomEquiv.symm id` from
   `free N.sections` to `N` is epi, via `N ≅ tilde Γ(N)` and `X.isoSpec`. `main` does not have
   this as a `GeneratingSections` statement. The general case then needs an induction on a finite
   affine cover, using 01PE (2) above.
2. 01PF (Lemma 28.23.2): a finite-type quasi-coherent submodule of `j^* G` is `j^* G'` for a
   finite-type quasi-coherent `G' ⊆ G`. Apply 01PE (2), then 01PG to the extension, and use the
   quasi-compactness of `U`.
3. 0G41 (Lemma 28.23.5): a finite-type `F` extends to a finite-type `G` (01PF applied inside
   `j_* F`), and a finitely presented `F` extends to a finitely presented `G`.
4. 01PI (Lemma 28.23.4): a map from a finitely presented `F` to `j^* H` extends to a map from a
   finitely presented extension of `F` to `H`.

Notes for the next session (checked against `main` at `ea7e54cf96`, 2026-10-29). PR #21787 is
still open, so the stub stays. Mathlib provides `SheafOfModules.IsFiniteType` and
`SheafOfModules.IsFinitePresentation`. `main` provides `isQuasicoherent_of_isColimit` and
`isColimitMapCoconeSectionsFunctor` in `Quasicoherent/Colimits.lean`: on an affine open, sections
of quasi-coherent modules commute with colimits. It also has `Quasicoherent/Affine.lean`
(`affineEquiv`, quasi-coherent modules on an affine scheme are module tildes). These are the
natural inputs for the affine case of 01PG. A workable statement of 01PG: the finite-type
quasi-coherent subobjects of `G` form a directed family whose supremum is `⊤`. Equivalently,
the cocone of their inclusions into `G` is a colimit, which matches the existing colimit API.

## Split plan

1. **Split 1** (after: none, once `qcoh-pushforward` / PR #21787 has landed). File
   `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/Extension.lean` (83 lines now), with
   `exists_isQuasicoherent_restrict_iso` and `exists_mono_restrict_iso_of_isQuasicoherent`.
   Subject: `feat: extend quasi-coherent modules and submodules along quasi-compact open immersions`.
2. **Split 2** (after: none, independent of the supplier). Started. File
   `TauCeti/AlgebraicGeometry/Modules/Quasicoherent/FiniteTypeImage.lean` (104 lines), with
   `isFiniteType_of_generatingSections`, `isQuasicoherent_image`,
   `isFiniteType_image_of_generatingSections` and `exists_isFiniteType_mono_sections`. Still to
   write: global generation on affines, the affine directed-union statement, and the qcqs
   induction, either in this file or in a sibling file proving 01PG. If the split exceeds about
   600 lines, `FiniteTypeImage.lean` can be opened alone first.
   Subject: `feat: quasi-coherent modules on qcqs schemes are directed unions of finite-type submodules`.
3. **Split 3** (after: 1, 2). Not yet written. It adds the finite-type submodule extension
   (01PF), finite-type and finitely presented extension (0G41) and map extension (01PI), either
   in `Extension.lean` or in a sibling `Extension/FiniteType.lean`. It carries the exported
   finite-type extension theorem and is the only split that completes the target.
   Subject: `feat: extend finite-type and finitely presented quasi-coherent modules along quasi-compact open immersions`.
