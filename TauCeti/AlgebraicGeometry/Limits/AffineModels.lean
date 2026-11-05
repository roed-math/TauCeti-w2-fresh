/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Limits.FiberProductSystem
public import TauCeti.AlgebraicGeometry.Limits.SpecFiberProduct

/-!
# Affine models of a scheme near a quasi-compact open

Let `V` be a quasi-compact open of a quasi-compact quasi-separated scheme `X`, the limit of a
cofiltered diagram `D` of quasi-compact quasi-separated schemes locally of finite type over `ℤ`,
with affine transition maps. Suppose the `D j` are covered by affine basic opens `D(b j k)`,
compatibly with the transition maps, with `π_j^* (b j k)` the restriction of `g k : Γ(X, ⊤)` and
`D(g k) ⊆ V`. Then there are finite subsets `s j` of the fibre products
`P j = Γ(X, ⊤) ×_{Γ(X, V)} Γ(D j, ⊤)` such that for every finitely generated subring `C ⊆ P j`
containing `s j` (an object `(j, C)` of `TauCeti.CommRingCat.FGSubringPair`):

* `D j` is an open subscheme of `Spec C`, whose preimage in `X` is `V`;
* its image is the union of the basic opens of the elements `(g k, b j k)` of `C`;
* hence, along a morphism `(j', C') ⟶ (j, C)`, the preimage of the image of `D j` in `Spec C'` is
  the image of `D j'`.

With `TauCeti.AlgebraicGeometry.Scheme.isLimitSpecFiberProductCocone`, the `Spec C` are a
cofiltered system of affine models of `X` near `V`; gluing them to models of an open complement of
`V` is the extension step in the proof of Stacks, Proposition 32.5.4 (01ZA).

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.fiberProductElem`: the element `(g k, b j k)` of `P j`.
* `TauCeti.AlgebraicGeometry.Scheme.exists_finset_isPullback_fgSubringPair`: the subsets `s j`.
* `TauCeti.AlgebraicGeometry.Scheme.preimage_opensRange_fgSubringPair`: compatibility of the
  images with the transition maps.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {X : Scheme.{u}} {V : X.Opens}
  (π : (Functor.const I).obj V.toScheme ⟶ D) {ι : Type*} (g : ι → Γ(X, ⊤))
  (b : ∀ j, ι → Γ(D.obj j, ⊤))
  (hgb : ∀ j k,
    ((π.app j).appTop ≫ V.topIso.hom) (b j k) = X.presheaf.map (homOfLE le_top).op (g k))

/-- The element `(g k, b j k)` of the fibre product `Γ(X, ⊤) ×_{Γ(X, V)} Γ(D j, ⊤)`. -/
def fiberProductElem (j : I) (k : ι) : (fiberProductSystem π).obj (op j) :=
  ⟨(g k, b j k), (hgb j k).symm⟩

@[simp]
lemma fiberProductCone_fst_fiberProductElem (j : I) (k : ι) :
    (fiberProductCone π j).fst (fiberProductElem π g b hgb j k) = g k :=
  rfl

@[simp]
lemma fiberProductCone_snd_fiberProductElem (j : I) (k : ι) :
    (fiberProductCone π j).snd (fiberProductElem π g b hgb j k) = b j k :=
  rfl

lemma fiberProductMap_fiberProductElem
    (hbD : ∀ {j j' : I} (f : j' ⟶ j) k, (D.map f).appTop (b j k) = b j' k) {j j' : I}
    (f : j' ⟶ j) (k : ι) :
    fiberProductMap π f (fiberProductElem π g b hgb j k) = fiberProductElem π g b hgb j' k := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact congr($(fiberProductMap_fst π f) (fiberProductElem π g b hgb j k))
  · exact congr($(fiberProductMap_snd π f) (fiberProductElem π g b hgb j k)).trans (hbD f k)

/-- The morphism `D j ⟶ Spec C` for a subring `C` of the fibre product
`Γ(X, ⊤) ×_{Γ(X, V)} Γ(D j, ⊤)`. -/
noncomputable abbrev toSpecFGSubring {j : I}
    (C : Subalgebra ℤ ((fiberProductSystem π).obj (op j))) : D.obj j ⟶ Spec (.of C) :=
  (D.obj j).toSpecΓ ≫ Spec.map (CommRingCat.ofHom C.val.toRingHom ≫ fiberProductSnd π j)

/-- For a morphism `(j', C') ⟶ (j, C)` of pairs, `D j' ⟶ Spec C' ⟶ Spec C` is
`D j' ⟶ D j ⟶ Spec C`. -/
@[reassoc]
lemma toSpecFGSubring_naturality {s : ∀ j, Finset ((fiberProductSystem π).obj (op j))}
    {a a' : CommRingCat.FGSubringPair (fiberProductSystem π) s} (f : a' ⟶ a) :
    toSpecFGSubring π a'.sub ≫
        Spec.map (CommRingCat.FGSubringPair.ringHom f) =
      D.map f.1 ≫ toSpecFGSubring π a.sub := by
  have key : CommRingCat.FGSubringPair.ringHom f ≫
      CommRingCat.ofHom a'.sub.val.toRingHom ≫ fiberProductSnd π a'.idx =
        (CommRingCat.ofHom a.sub.val.toRingHom ≫ fiberProductSnd π a.idx) ≫
          (D.map f.1).appTop := by
    ext x
    exact congr($(fiberProductMap_snd π f.1) x.1)
  rw [Category.assoc, ← Spec.map_comp, key, Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc]

/-- Let `V` be a quasi-compact open of a quasi-compact quasi-separated scheme `X` and `π : V ⟶ D`
a cone on a diagram of quasi-compact quasi-separated schemes locally of finite type over `ℤ`.
Suppose each `D j` is covered by finitely many affine basic opens `D(b j k)`, where
`π_j^* (b j k)` is the restriction of `g k : Γ(X, ⊤)` and `D(g k) ⊆ V`. Then there are finite
subsets `s j` of the fibre products `P j = Γ(X, ⊤) ×_{Γ(X, V)} Γ(D j, ⊤)`, containing the
`(g k, b j k)`, such that for every finitely generated subring `C ⊆ P j` containing `s j`, `D j`
is an open subscheme of `Spec C` with preimage `V` in `X`, and its image is the union of the basic
opens of the `(g k, b j k)`. Part of the proof of Stacks, Proposition 32.5.4 (01ZA). -/
theorem exists_finset_isPullback_fgSubringPair [CompactSpace X] [QuasiSeparatedSpace X]
    (hV : IsCompact (V : Set X)) [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)] [∀ j, LocallyOfFiniteType (terminal.from (D.obj j))]
    [Finite ι] (hg : ∀ k, X.basicOpen (g k) ≤ V)
    (hb : ∀ j k, IsAffineOpen ((D.obj j).basicOpen (b j k)))
    (hY : ∀ j, ⨆ k, (D.obj j).basicOpen (b j k) = ⊤) :
    ∃ s : ∀ j, Finset ((fiberProductSystem π).obj (op j)),
      (∀ j k, fiberProductElem π g b hgb j k ∈ s j) ∧
      ∀ a : CommRingCat.FGSubringPair (fiberProductSystem π) s,
        ∃ _ : IsOpenImmersion (toSpecFGSubring π a.sub),
          IsPullback (π.app a.idx) V.ι (toSpecFGSubring π a.sub)
            (X.toSpecΓ ≫ Spec.map
              (CommRingCat.ofHom a.sub.val.toRingHom ≫ (fiberProductCone π a.idx).fst)) ∧
          ∀ y : ι → a.sub, (∀ k, (y k : (fiberProductSystem π).obj (op a.idx)) =
              fiberProductElem π g b hgb a.idx k) →
            (toSpecFGSubring π a.sub).opensRange = ⨆ k, PrimeSpectrum.basicOpen (y k) := by
  classical
  cases nonempty_fintype ι
  choose s₀ hs₀ using fun j ↦ exists_finset_isPullback_toSpecΓ_comp_SpecMap hV (π.app j) g (b j)
    (hgb j) hg (hb j) (hY j)
  refine ⟨fun j ↦ s₀ j ∪ Finset.univ.image (fiberProductElem π g b hgb j),
    fun j k ↦ Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)),
    fun a ↦ ?_⟩
  obtain ⟨hopen, hpb, hrange⟩ := hs₀ a.idx a.sub
    (fun y hy ↦ a.subset (Finset.mem_coe.mpr (Finset.mem_union_left _ hy)))
  exact ⟨hopen, hpb, fun y hy ↦ hrange y fun k ↦
    ⟨congr((fiberProductCone π a.idx).fst $(hy k)), congr((fiberProductCone π a.idx).snd $(hy k))⟩⟩

/-- In the situation of `exists_finset_isPullback_fgSubringPair`, if the `b j k` are compatible
with the transition maps, then for a morphism `(j', C') ⟶ (j, C)` of pairs the preimage in
`Spec C'` of the image of `D j` in `Spec C` is the image of `D j'`. -/
theorem preimage_opensRange_fgSubringPair
    (hbD : ∀ {j j' : I} (f : j' ⟶ j) k, (D.map f).appTop (b j k) = b j' k)
    {s : ∀ j, Finset ((fiberProductSystem π).obj (op j))}
    {a a' : CommRingCat.FGSubringPair (fiberProductSystem π) s} (f : a' ⟶ a)
    [IsOpenImmersion (toSpecFGSubring π a.sub)] [IsOpenImmersion (toSpecFGSubring π a'.sub)]
    (y : ι → a.sub) (hy : ∀ k, (y k : (fiberProductSystem π).obj (op a.idx)) =
      fiberProductElem π g b hgb a.idx k)
    (y' : ι → a'.sub) (hy' : ∀ k, (y' k : (fiberProductSystem π).obj (op a'.idx)) =
      fiberProductElem π g b hgb a'.idx k)
    (h : (toSpecFGSubring π a.sub).opensRange = ⨆ k, PrimeSpectrum.basicOpen (y k))
    (h' : (toSpecFGSubring π a'.sub).opensRange = ⨆ k, PrimeSpectrum.basicOpen (y' k)) :
    Spec.map (CommRingCat.FGSubringPair.ringHom f) ⁻¹ᵁ
      (toSpecFGSubring π a.sub).opensRange = (toSpecFGSubring π a'.sub).opensRange := by
  have hψ (k : ι) : CommRingCat.FGSubringPair.ringHom f (y k) =
      y' k := by
    refine Subtype.ext ?_
    rw [CommRingCat.FGSubringPair.ringHom_apply_coe, hy, hy']
    exact fiberProductMap_fiberProductElem π g b hgb hbD f.1 k
  rw [h, h']
  ext p
  refine TopologicalSpace.Opens.mem_iSup.trans
    ((exists_congr fun k ↦ ?_).trans TopologicalSpace.Opens.mem_iSup.symm)
  rw [← hψ k]
  exact Iff.rfl

end TauCeti.AlgebraicGeometry.Scheme
