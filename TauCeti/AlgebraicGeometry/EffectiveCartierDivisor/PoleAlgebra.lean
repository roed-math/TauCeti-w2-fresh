/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Multiplication
public import TauCeti.AlgebraicGeometry.LineBundle.Dual.Map
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
public import TauCeti.CategoryTheory.Monoidal.Braided.Evaluation

/-!
# The pole algebra of an effective Cartier divisor

Let `D` be an effective Cartier divisor on a scheme `X`, with ideal sheaf `I = 𝒪_X(-D)`, and let
`𝒪_X(nD) = 𝓗om(Iⁿ, 𝒪_X)` be the line bundle of functions with a pole of order at most `n` along
`D`. The multiplications `𝒪_X(aD) ⊗ 𝒪_X(bD) ≅ 𝒪_X((a + b)D)`
(`Scheme.IdealSheafData.IsEffectiveCartier.dualPowMulIso`) make

`⨁ₙ 𝒪_X(nD) = 𝒪_X ⊕ 𝒪_X(D) ⊕ 𝒪_X(2D) ⊕ ⋯`

a graded commutative quasi-coherent `𝒪_X`-algebra, the **pole algebra** of `D`
(`Scheme.IdealSheafData.IsEffectiveCartier.poleAlgebra`). Its unit is `𝒪_X ≅ 𝒪_X(0D)`, sending a
regular function `f` to the functional `s ↦ f s` on `I⁰ = 𝒪_X`.

The laws are proved by evaluating against the powers of `I`: a product `φ ψ` of local sections
of `𝒪_X(aD)` and `𝒪_X(bD)` evaluates on `t s ∈ I^(a + b)` to `φ(s) ψ(t)`
(`Scheme.IdealSheafData.IsEffectiveCartier.whiskerLeft_dualPowMulIso_hom_comp_ev`). Associativity
and commutativity then reduce to those of the multiplication `I^b ⊗ I^a ≅ I^(a + b)` of ideal
sheaves
(`Scheme.IdealSheafData.IsEffectiveCartier.whiskerLeft_powTensorIso_hom_comp_powTensorIso_hom`
and `Scheme.IdealSheafData.IsEffectiveCartier.braiding_powTensorIso_hom`), which are those of
`𝒪_X`;
commutativity also exchanges the two nested evaluations
(`TauCeti.braiding_tensorHom_braiding_comp_nestedEvaluation`).

For the zero section `[0]` of an elliptic curve, the pole algebra is `⨁ₙ 𝒪_E(n[0])`, whose
pieces of degree at most `6` carry the Weierstrass coordinates `x`, `y` and their relation.

## Main declarations

* `Scheme.IdealSheafData.poleComponent I n`: the line bundle `𝒪_X(nD) = 𝓗om(Iⁿ, 𝒪_X)`.
* `Scheme.IdealSheafData.IsEffectiveCartier.poleMul` and
  `Scheme.IdealSheafData.IsEffectiveCartier.poleOne`: the homogeneous multiplication and the
  unit, with the laws `poleOne_whiskerRight_poleMul`, `whiskerLeft_poleOne_poleMul`,
  `poleMul_assoc` and `braiding_poleMul`.
* `Scheme.IdealSheafData.IsEffectiveCartier.poleAlgebra`: the pole algebra `⨁ₙ 𝒪_X(nD)`, as a
  graded quasi-coherent `𝒪_X`-algebra.

## Implementation notes

As for `Scheme.IdealSheafData.reesAlgebra`, the pole algebra is built from the named family
`Scheme.IdealSheafData.poleComponent I` and the named multiplication `poleMul`, and its laws are
stated literally in the form `GradedQuasicoherentAlgebra.ofHomogeneous` asks for: with a `fun`
family the kernel must match the laws against beta-redexes and times out unfolding the monoidal
structure of `X.Modules`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1 and 2.2.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The homogeneous component `𝒪_X(nD) = 𝓗om(Iⁿ, 𝒪_X)` of the pole algebra of the ideal sheaf
`I = 𝒪_X(-D)`. -/
noncomputable abbrev poleComponent {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) : X.Modules :=
  (ihom (I ^ n).sheaf).obj (𝟙_ X.Modules)

namespace IsEffectiveCartier

noncomputable section

variable {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsEffectiveCartier)

/-- The inclusion `J ⟶ 𝒪_X`, read as a morphism to the monoidal unit. It is opaque, so that the
kernel does not compare `SheafOfModules.unit` with `𝟙_ X.Modules` in every proof. -/
private def ιU (J : X.IdealSheafData) : J.sheaf ⟶ 𝟙_ X.Modules := J.sheafι

private instance (J : X.IdealSheafData) : Mono (ιU J) := inferInstanceAs (Mono J.sheafι)

/-- `powTensorIso_hom_sheafι`, stated with the inclusions read as morphisms to the unit. -/
@[reassoc]
private lemma powTensorIso_hom_ιU (a b : ℕ) :
    (powTensorIso hI a b).hom ≫ ιU (I ^ (a + b)) =
      (ιU (I ^ b) ⊗ₘ ιU (I ^ a)) ≫ (λ_ (𝟙_ _)).hom :=
  powTensorIso_hom_sheafι hI a b

/-- Transport between powers of `I` commutes with the inclusions into `𝒪_X`. -/
@[reassoc]
private lemma eqToHom_ιU {m n : ℕ} (h : m = n) (h' : (I ^ m).sheaf = (I ^ n).sheaf) :
    eqToHom h' ≫ ιU (I ^ n) = ιU (I ^ m) := by
  subst h
  exact Category.id_comp _

/-- **The multiplication of ideal sheaves is associative**: `t (s r) = (t s) r` for local sections
`t` of `I^c`, `s` of `I^b` and `r` of `I^a`. -/
theorem whiskerLeft_powTensorIso_hom_comp_powTensorIso_hom (a b c : ℕ) :
    (I ^ c).sheaf ◁ (powTensorIso hI a b).hom ≫ (powTensorIso hI (a + b) c).hom =
      (α_ _ _ _).inv ≫ (powTensorIso hI b c).hom ▷ (I ^ a).sheaf ≫
        (powTensorIso hI a (b + c)).hom ≫
        eqToHom (congrArg (fun n ↦ (I ^ n).sheaf) (add_assoc a b c).symm) := by
  rw [← cancel_mono (ιU (I ^ (a + b + c)))]
  simp (disch := omega) only [Category.assoc, powTensorIso_hom_ιU, eqToHom_ιU,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc]
  monoidal

/-- The inverses of the multiplications of ideal sheaves are associative. -/
theorem powTensorIso_inv_whiskerLeft_powTensorIso_inv (a b c : ℕ) :
    (powTensorIso hI (a + b) c).inv ≫ (I ^ c).sheaf ◁ (powTensorIso hI a b).inv =
      eqToHom (congrArg (fun n ↦ (I ^ n).sheaf) (add_assoc a b c)) ≫
        (powTensorIso hI a (b + c)).inv ≫ (powTensorIso hI b c).inv ▷ (I ^ a).sheaf ≫
        (α_ _ _ _).hom := by
  have := Iso.inv_eq_inv
    (whiskerLeftIso (I ^ c).sheaf (powTensorIso hI a b) ≪≫ powTensorIso hI (a + b) c)
    ((α_ _ _ _).symm ≪≫ whiskerRightIso (powTensorIso hI b c) (I ^ a).sheaf ≪≫
      powTensorIso hI a (b + c) ≪≫
      eqToIso (congrArg (fun n ↦ (I ^ n).sheaf) (add_assoc a b c).symm))
  simpa using this.2 (by simpa using whiskerLeft_powTensorIso_hom_comp_powTensorIso_hom hI a b c)

/-- Rewriting a pair of whiskered morphisms along a factorisation. -/
private lemma whiskerRight_assoc_whiskerLeft_whiskerRight {V P Q R W D : X.Modules}
    (m₁ : P ⟶ V ⊗ Q) (m₂ : Q ⟶ R) (h : P ⟶ V ⊗ R) (hm : m₁ ≫ V ◁ m₂ = h) :
    m₁ ▷ (W ⊗ D) ≫ (α_ V Q (W ⊗ D)).hom ≫ V ◁ (α_ Q W D).inv ≫ V ◁ ((m₂ ▷ W) ▷ D) =
      h ▷ (W ⊗ D) ≫ (α_ V R (W ⊗ D)).hom ≫ V ◁ (α_ R W D).inv := by
  subst hm
  monoidal

/-- Evaluating against `Iⁿ` after transporting `𝒪_X(mD)` to `𝒪_X(nD)` along `m = n` is
evaluating against `Iᵐ` after transporting `Iⁿ` to `Iᵐ`. -/
@[reassoc]
private lemma whiskerLeft_eqToHom_ev {m n : ℕ} (h : m = n) :
    (I ^ n).sheaf ◁ eqToHom (congrArg I.poleComponent h) ≫
        (ihom.ev (I ^ n).sheaf).app (𝟙_ _) =
      eqToHom (congrArg (fun k ↦ (I ^ k).sheaf) h.symm) ▷ _ ≫
        (ihom.ev (I ^ m).sheaf).app (𝟙_ _) := by
  subst h
  simp

/-- The homogeneous multiplication `𝒪_X(aD) ⊗ 𝒪_X(bD) ⟶ 𝒪_X((a + b)D)` of the pole algebra:
the isomorphism `dualPowMulIso`. -/
def poleMul (a b : ℕ) : I.poleComponent a ⊗ I.poleComponent b ⟶ I.poleComponent (a + b) :=
  (dualPowMulIso hI a b).hom

/-- `TauCeti.whiskerLeft_whiskerLeft_comp_evaluate`, under a further whiskering. -/
@[reassoc]
private lemma whiskerLeft_whiskerLeft_comp_evaluate {V A B C D : X.Modules} (f : A ⊗ B ⟶ 𝟙_ _)
    (g : C ⟶ D) :
    V ◁ (A ◁ B ◁ g) ≫ V ◁ (α_ A B D).inv ≫ V ◁ (f ▷ D) ≫ V ◁ (λ_ D).hom =
      V ◁ ((α_ A B C).inv ≫ f ▷ C ≫ (λ_ C).hom) ≫ V ◁ g := by
  simp only [← MonoidalCategory.whiskerLeft_comp, TauCeti.whiskerLeft_whiskerLeft_comp_evaluate]

/-- **The multiplication of the pole algebra is associative.** -/
theorem poleMul_assoc (a b c : ℕ) :
    hI.poleMul a b ▷ I.poleComponent c ≫ hI.poleMul (a + b) c =
      (α_ (I.poleComponent a) (I.poleComponent b) (I.poleComponent c)).hom ≫
        I.poleComponent a ◁ hI.poleMul b c ≫ hI.poleMul a (b + c) ≫
        eqToHom (congrArg I.poleComponent (add_assoc a b c).symm) := by
  unfold poleMul
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_dualPowMulIso_hom_comp_ev, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_eqToHom_ev (add_assoc a b c).symm, whisker_exchange_assoc,
    associator_naturality_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, associator_inv_naturality_middle,
    MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc _ ((_ ◁ (dualPowMulIso hI a b).hom) ▷ _),
    ← comp_whiskerRight, whiskerLeft_dualPowMulIso_hom_comp_ev]
  conv_rhs =>
    rw [whisker_exchange_assoc, whiskerLeft_dualPowMulIso_hom_comp_ev,
      whisker_exchange_assoc _ (_ ◁ (dualPowMulIso hI b c).hom),
      whisker_exchange_assoc _ (α_ _ _ _).hom,
      whisker_exchange_assoc _ (_ ◁ (dualPowMulIso hI b c).hom),
      associator_naturality_right_assoc, whiskerLeft_whiskerLeft_comp_evaluate_assoc,
      whiskerLeft_dualPowMulIso_hom_comp_ev, whisker_exchange_assoc (powTensorIso hI b c).inv]
  rw [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [reassoc_of% whiskerRight_assoc_whiskerLeft_whiskerRight _ _ _
      (powTensorIso_inv_whiskerLeft_powTensorIso_inv hI a b c)]
  -- `monoidal` would try to treat the transport between the powers of `I` as structural.
  generalize eqToHom (congrArg (fun n ↦ (I ^ n).sheaf) (add_assoc a b c)) = e
  monoidal

/-- `I⁰ = 𝒪_X` is a right unit for the multiplication of ideal sheaves. -/
private lemma powTensorIso_zero_inv_whiskerLeft (n : ℕ) :
    (powTensorIso hI 0 n).inv ≫ (I ^ n).sheaf ◁ ιU (I ^ 0) ≫ (ρ_ _).hom =
      eqToHom (congrArg (fun k ↦ (I ^ k).sheaf) (zero_add n)) := by
  rw [← cancel_mono (ιU (I ^ n)), Category.assoc, Category.assoc, eqToHom_ιU (zero_add n) _,
    Iso.inv_comp_eq, powTensorIso_hom_ιU, ← rightUnitor_naturality, unitors_equal,
    whisker_exchange_assoc, tensorHom_def, Category.assoc]

/-- `I⁰ = 𝒪_X` is a left unit for the multiplication of ideal sheaves. -/
private lemma powTensorIso_zero_inv_whiskerRight (n : ℕ) :
    (powTensorIso hI n 0).inv ≫ ιU (I ^ 0) ▷ (I ^ n).sheaf ≫ (λ_ _).hom =
      eqToHom (congrArg (fun k ↦ (I ^ k).sheaf) (add_zero n)) := by
  rw [← cancel_mono (ιU (I ^ n)), Category.assoc, Category.assoc, eqToHom_ιU (add_zero n) _,
    Iso.inv_comp_eq, powTensorIso_hom_ιU, ← leftUnitor_naturality, tensorHom_def,
    Category.assoc]

/-- The unit `𝒪_X ⟶ 𝒪_X(0D)`: a regular function `f` is the functional `s ↦ f s` on
`I⁰ = 𝒪_X`. -/
def poleOne : 𝟙_ X.Modules ⟶ I.poleComponent 0 :=
  curry ((ρ_ _).hom ≫ ιU (I ^ 0))

/-- The unit of the pole algebra is a left identity for its multiplication. -/
theorem poleOne_whiskerRight_poleMul (n : ℕ) :
    poleOne ▷ I.poleComponent n ≫ hI.poleMul 0 n =
      (λ_ (I.poleComponent n)).hom ≫ eqToHom (congrArg I.poleComponent (zero_add n).symm) := by
  unfold poleMul
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_dualPowMulIso_hom_comp_ev, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_eqToHom_ev (zero_add n).symm, whisker_exchange_assoc,
    associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    associator_inv_naturality_middle, MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc _ ((_ ◁ poleOne) ▷ _), ← comp_whiskerRight,
    poleOne, whiskerLeft_curry_ihom_ev_app, ← powTensorIso_zero_inv_whiskerLeft hI n]
  monoidal

/-- The unit of the pole algebra is a right identity for its multiplication. -/
theorem whiskerLeft_poleOne_poleMul (n : ℕ) :
    I.poleComponent n ◁ poleOne ≫ hI.poleMul n 0 =
      (ρ_ (I.poleComponent n)).hom ≫ eqToHom (congrArg I.poleComponent (add_zero n).symm) := by
  unfold poleMul
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_dualPowMulIso_hom_comp_ev, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_eqToHom_ev (add_zero n).symm, whisker_exchange_assoc,
    associator_naturality_right_assoc, whiskerLeft_whiskerLeft_comp_evaluate_assoc, poleOne,
    whiskerLeft_curry_ihom_ev_app, ← rightUnitor_naturality, whisker_exchange_assoc,
    ← powTensorIso_zero_inv_whiskerRight hI n]
  monoidal


/-- **The multiplication of ideal sheaves is commutative**: `s t = t s` for local sections `s` of
`I^a` and `t` of `I^b`. -/
theorem braiding_powTensorIso_hom (a b : ℕ) :
    (β_ (I ^ b).sheaf (I ^ a).sheaf).hom ≫ (powTensorIso hI b a).hom =
      (powTensorIso hI a b).hom ≫ eqToHom (congrArg (fun n ↦ (I ^ n).sheaf) (add_comm a b)) := by
  rw [← cancel_mono (ιU (I ^ (b + a))), Category.assoc, Category.assoc, powTensorIso_hom_ιU,
    eqToHom_ιU (add_comm a b) _, powTensorIso_hom_ιU,
    ← BraidedCategory.braiding_naturality_assoc]
  -- The remaining identity is the commutativity of the multiplication of `𝒪_X`.
  exact congrArg (_ ≫ ·) (IsCommMonObj.mul_comm (𝟙_ X.Modules))

/-- The inverse of the multiplication of ideal sheaves, in the other order. -/
private lemma powTensorIso_inv_eq (a b : ℕ) :
    (powTensorIso hI b a).inv = eqToHom (congrArg (fun n ↦ (I ^ n).sheaf) (add_comm b a)) ≫
      (powTensorIso hI a b).inv ≫ (β_ (I ^ b).sheaf (I ^ a).sheaf).hom := by
  rw [← cancel_epi (powTensorIso hI b a).hom, Iso.hom_inv_id,
    ← cancel_epi (β_ (I ^ b).sheaf (I ^ a).sheaf).hom, reassoc_of% braiding_powTensorIso_hom]
  simp

/-- **The multiplication of the pole algebra is commutative.** -/
theorem braiding_poleMul (a b : ℕ) :
    (β_ (I.poleComponent a) (I.poleComponent b)).hom ≫ hI.poleMul b a =
      hI.poleMul a b ≫ eqToHom (congrArg I.poleComponent (add_comm a b)) := by
  unfold poleMul
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_dualPowMulIso_hom_comp_ev, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_eqToHom_ev (add_comm a b)]
  conv_rhs => rw [whisker_exchange_assoc, whiskerLeft_dualPowMulIso_hom_comp_ev,
    ← braiding_tensorHom_braiding_comp_nestedEvaluation ((ihom.ev (I ^ a).sheaf).app (𝟙_ _))
      ((ihom.ev (I ^ b).sheaf).app (𝟙_ _))]
  rw [powTensorIso_inv_eq, whisker_exchange_assoc, tensorHom_def]
  simp only [comp_whiskerRight, Category.assoc]


include hI in
/-- The line bundles `𝒪_X(nD)` are quasi-coherent. -/
theorem isQuasicoherent_poleComponent (n : ℕ) : (I.poleComponent n).IsQuasicoherent := by
  rw [poleComponent, ← (TauCeti.isEffectiveCartier_pow hI n).toInvertibleSheaf_obj,
    ← InvertibleSheaf.dual_obj_eq_ihom]
  exact inferInstanceAs ((InvertibleSheaf.toFiniteLocallyFree X).obj (InvertibleSheaf.dual
    (TauCeti.isEffectiveCartier_pow hI n).toInvertibleSheaf)).obj.IsQuasicoherent

/-- **The pole algebra** `⨁ₙ 𝒪_X(nD)` of an effective Cartier divisor `D`, as a graded
quasi-coherent `𝒪_X`-algebra. Its degree-`n` component is `𝒪_X(nD) = 𝓗om(Iⁿ, 𝒪_X)`
(`poleAlgebra_obj_X`), its multiplication is `poleMul` (`mul_poleAlgebra`) and its unit
is `poleOne` (`one_poleAlgebra`). -/
def poleAlgebra : GradedQuasicoherentAlgebra X :=
  haveI := isQuasicoherent_poleComponent hI
  GradedQuasicoherentAlgebra.ofHomogeneous I.poleComponent poleOne hI.poleMul
    (poleOne_whiskerRight_poleMul hI) (whiskerLeft_poleOne_poleMul hI) (poleMul_assoc hI)
    (braiding_poleMul hI)

/-- The homogeneous components of the pole algebra are the line bundles `𝒪_X(nD)`. -/
@[simp]
theorem poleAlgebra_obj_X : hI.poleAlgebra.obj.X = I.poleComponent :=
  haveI := isQuasicoherent_poleComponent hI
  GradedQuasicoherentAlgebra.ofHomogeneous_obj_X _ _ _ _ _ _ _

/-- The homogeneous multiplication of the pole algebra is `poleMul`. -/
@[simp]
theorem mul_poleAlgebra (i j : ℕ) :
    hI.poleAlgebra.obj.toMon.mul i j =
      (eqToHom (by rw [poleAlgebra_obj_X]) :
        hI.poleAlgebra.obj.X i ⊗ hI.poleAlgebra.obj.X j ⟶ _) ≫ hI.poleMul i j ≫
        eqToHom (congrFun hI.poleAlgebra_obj_X (i + j)).symm :=
  haveI := isQuasicoherent_poleComponent hI
  GradedQuasicoherentAlgebra.mul_ofHomogeneous _ _ _ _ _ _ _ i j

/-- The unit of the pole algebra is `poleOne`. -/
@[simp]
theorem one_poleAlgebra :
    hI.poleAlgebra.obj.toMon.one = poleOne ≫ eqToHom (congrFun hI.poleAlgebra_obj_X 0).symm :=
  haveI := isQuasicoherent_poleComponent hI
  GradedQuasicoherentAlgebra.one_ofHomogeneous _ _ _ _ _ _ _

end

end IsEffectiveCartier

end AlgebraicGeometry.Scheme.IdealSheafData
