/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Algebra.Lie.Cochain
public import Mathlib.Algebra.Lie.Graded
public import Mathlib.Algebra.Lie.InvariantForm
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition

/-!
# Loop Lie algebras and their central extensions

Given a Lie algebra `L`, the loop algebra is the Lie algebra of maps from a circle into `L`. This
can mean many different things, e.g., continuous maps, smooth maps, polynomial maps. In this file,
we consider the simplest case of polynomial maps, meaning we take a base change with the ring of
Laurent polynomials.

Loop Lie algebras admit central extensions attached to invariant inner products on the base Lie
algebra. When the base Lie algebra is finite dimensional and simple, the corresponding central
extension (with an outer derivation attached) admits an infinite root system with affine Weyl group.
These extended Lie algebras are called untwisted affine Kac-Moody Lie algebras.

We implement the basic theory using `AddMonoidAlgebra` instead of `LaurentPolynomial` for
flexibility. The classical loop algebra is then written `loopAlgebra R ℤ L`.

## Main definitions
* `LieAlgebra.loopAlgebra`: The tensor product of a Lie algebra with an `AddMonoidAlgebra`.
* `LieAlgebra.loopAlgebra.toFinsupp`: A linear equivalence from the loop algebra to the space of
  finitely supported functions.
* `LieAlgebra.loopAlgebra.twoCochainOfBilinear`: The 2-cochain for a loop algebra with trivial
  coefficients attached to a symmetric bilinear form on the base Lie algebra.
* `LieAlgebra.loopAlgebra.twoCocycleOfBilinear`: The 2-cocycle for a loop algebra with trivial
  coefficients attached to a symmetric invariant bilinear form on the base Lie algebra.

## TODO
* Evaluation representations
* Construction of central extensions from invariant forms.
* Positive energy representations induced from a fixed central character

## Tags
lie ring, lie algebra, base change, Laurent polynomial
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

variable (R A L : Type*)

namespace LieAlgebra

variable [CommRing R] [LieRing L] [LieAlgebra R L]

/--
Definition of `loopAlgebra` / `loopAlgebra` 的定义

English:
abbreviation loopAlgebra
  body: AddMonoidAlgebra R A otimes[R] L

中文:
缩写 loopAlgebra
  定义体: AddMonoidAlgebra R A otimes[R] L

Depends on / 依赖: AddMonoidAlgebra, otimes
-/
abbrev loopAlgebra := AddMonoidAlgebra R A otimes[R] L

open LaurentPolynomial in
/--
Definition of `loopAlgebraEquivLaurent` / `loopAlgebraEquivLaurent` 的定义

English:
definition loopAlgebraEquivLaurent
  signature: :
  body: LieEquiv.refl

中文:
定义 loopAlgebraEquivLaurent
  签名: :
  定义体: LieEquiv.refl

Depends on / 依赖: LieEquiv, LieEquiv.refl
-/
def loopAlgebraEquivLaurent :
    loopAlgebra R Int L ≃ₗ⁅R⁆ R[T;T⁻¹] otimes[R] L :=
  LieEquiv.refl

namespace LoopAlgebra

open DirectSum in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: A] [AddCommMonoid A] :
  body: by
    rw [decomposeTensor_apply] at hi hj ⊢
    obtain ⟨xi, rfl⟩ := hi
    obtain ⟨xj, rfl⟩ := hj
    induction xi using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply]
      induction xj using TensorProduct.indu

中文:
实例 [DecidableEq
  签名: A] [AddCommMonoid A] :
  定义体: by
    rw [decomposeTensor_apply] at hi hj ⊢
    obtain ⟨xi, rfl⟩ := hi
    obtain ⟨xj, rfl⟩ := hj
    induction xi using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply]
      induction xj using TensorProduct.indu

Depends on / 依赖: LinearMap, LinearMap.map_add, LinearMap.rTensor_tmul, SetLike, SetLike.mul_mem_graded, Submodule, Submodule.subtype_apply, TensorProduct, TensorProduct.induction_on, decomposeTensor_apply, induction_on, lie_add, map_add, mul_mem_graded, rTensor_tmul, subtype_apply
-/
noncomputable instance [DecidableEq A] [AddCommMonoid A] :
    GradedLieAlgebra (fun a : A => (decomposeTensor (AddMonoidAlgebra.grade R) L a)) where
  bracket_mem i j xi xj hi hj := by
    rw [decomposeTensor_apply] at hi hj ⊢
    obtain ⟨xi, rfl⟩ := hi
    obtain ⟨xj, rfl⟩ := hj
    induction xi using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply]
      induction xj using TensorProduct.induction_on with
      | zero => simp
      | tmul u v =>
        obtain ⟨x, hx⟩ := x
        obtain ⟨u, hu⟩ := u
        use ⟨x * u, SetLike.mul_mem_graded hx hu⟩ otimesₜ ⁅y, v⁆
        simp
      | add u v hu hv =>
        rw [LinearMap.map_add]; rw [lie_add]
        obtain ⟨u', hu'⟩ := hu
        obtain ⟨v', hv'⟩ := hv
        use u' + v'
        simp [← hu', ← hv']
    | add x y hx hy =>
      rw [LinearMap.map_add]; rw [add_lie]
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      use u + v
      simp [← hu, ← hv]
  decompose' := (tensorDecomposition (fun a : A => AddMonoidAlgebra.grade R a) L).decompose'
  left_inv := (tensorDecomposition _ L).left_inv
  right_inv := (tensorDecomposition _ L).right_inv

open scoped Classical in
/--
Definition of `toFinsupp` / `toFinsupp` 的定义

English:
definition toFinsupp
  signature: : loopAlgebra R A L ≃ₗ[R] A ->₀ L
  body: TensorProduct.equivFinsuppOfBasisLeft (AddMonoidAlgebra.basis A R)

@[simp]

中文:
定义 toFinsupp
  签名: : loopAlgebra R A L ≃ₗ[R] A ->₀ L
  定义体: TensorProduct.equivFinsuppOfBasisLeft (AddMonoidAlgebra.basis A R)

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.basis, TensorProduct, TensorProduct.equivFinsuppOfBasisLeft, equivFinsuppOfBasisLeft
-/
def toFinsupp : loopAlgebra R A L ≃ₗ[R] A ->₀ L :=
  TensorProduct.equivFinsuppOfBasisLeft (AddMonoidAlgebra.basis A R)

@[simp]
/--
lemma `toFinsupp_symm_single` / 引理 `toFinsupp_symm_single`

English:
lemma toFinsupp_symm_single
  given: (c : A) (z : L)
  proof: by
  simp [toFinsupp]

@[simp]

中文:
引理 toFinsupp_symm_single
  条件: (c : A) (z : L)
  证明: by
  simp [toFinsupp]

@[simp]

Depends on / 依赖: toFinsupp
-/
lemma toFinsupp_symm_single (c : A) (z : L) :
    (toFinsupp R A L).symm (Finsupp.single c z) = AddMonoidAlgebra.single c 1 otimesₜ[R] z := by
  simp [toFinsupp]

@[simp]
/--
lemma `toFinsupp_single_tmul` / 引理 `toFinsupp_single_tmul`

English:
lemma toFinsupp_single_tmul
  given: (c : A) (z : L)
  proof: by
  simp [← toFinsupp_symm_single]

中文:
引理 toFinsupp_single_tmul
  条件: (c : A) (z : L)
  证明: by
  simp [← toFinsupp_symm_single]

Depends on / 依赖: toFinsupp_symm_single
-/
lemma toFinsupp_single_tmul (c : A) (z : L) :
    (toFinsupp R A L (AddMonoidAlgebra.single c 1 otimesₜ[R] z)) = Finsupp.single c z := by
  simp [← toFinsupp_symm_single]

open Finsupp in
set_option backward.isDefEq.respectTransparency false in
/-- The residue pairing on the loop algebra. When `A = ℤ` and the elements are viewed as Laurent
polynomials with coefficients in `L`, the pairing is interpreted as `(f, g) ↦ Res f dg`. -/
@[simps]
/--
Definition of `residuePairing` / `residuePairing` 的定义

English:
definition residuePairing
  signature: [AddCommGroup A] [DistribSMul A R] [SMulCommClass A R R]
  body: letI F := toFinsupp R A L
    { toFun g := (F g).sum fun a v => a • Φ (F f (-a)) v
      map_add' x y := by
        classical
        let u : Finset A := (F x).support union (F y).support
        have hu₁ : (F x).support subseteq u := Finset.subset_union_left
        have hu₂ : (F y).support subsete

中文:
定义 residuePairing
  签名: [AddCommGroup A] [DistribSMul A R] [SMulCommClass A R R]
  定义体: letI F := toFinsupp R A L
    { toFun g := (F g).sum fun a v => a • Φ (F f (-a)) v
      map_add' x y := by
        classical
        let u : Finset A := (F x).support union (F y).support
        have hu₁ : (F x).support subseteq u := Finset.subset_union_left
        have hu₂ : (F y).support subsete

Depends on / 依赖: Finset, Finset.subset_union_left, Finset.subset_union_right, classical, map_add, replace, subset_union_left, subset_union_right, subseteq, sum_of_support_subset, support, toFinsupp
-/
def residuePairing [AddCommGroup A] [DistribSMul A R] [SMulCommClass A R R]
    (Φ : LinearMap.BilinForm R L) :
    LinearMap.BilinForm R (loopAlgebra R A L) where
  toFun f :=
    letI F := toFinsupp R A L
    { toFun g := (F g).sum fun a v => a • Φ (F f (-a)) v
      map_add' x y := by
        classical
        let u : Finset A := (F x).support union (F y).support
        have hu₁ : (F x).support subseteq u := Finset.subset_union_left
        have hu₂ : (F y).support subseteq u := Finset.subset_union_right
        have hu₃ : (F (x + y)).support subseteq u := fun a ha => by
          replace ha : F x a + F y a != 0 := by simpa using ha
          grind
        rw [sum_of_support_subset _ hu₃ _ (by simp)]; rw [sum_of_support_subset _ hu₁ _ (by simp)]; rw [sum_of_support_subset _ hu₂ _ (by simp)]
        simp [Finset.sum_add_distrib, u]
      map_smul' r x := by
        rw [map_smul]; rw [sum_of_support_subset _ support_smul _ (by simp)]; rw [sum]; rw [Finset.smul_sum]
        simp [-smul_eq_mul, smul_comm] }
  map_add' x y := by ext; simp [sum_add]
  map_smul' r x := by ext; simp [-smul_eq_mul, smul_comm]

open LieModule in
/--
Definition of `twoCochainOfBilinear` / `twoCochainOfBilinear` 的定义

English:
definition twoCochainOfBilinear
  signature: [CommRing A] [IsAddTorsionFree R] [Algebra A R]
  body: (residuePairing R A L Φ).compr₂ (TrivialLieModule.equiv R (loopAlgebra R A L) R).symm
  property := by
    refine Cohomology.mem_twoCochain_iff.mpr fun f => ?_
    let F := toFinsupp R A L
    suffices ((F f).sum fun a v => a • Φ (F f (-a)) v) = 0 by simpa
    classical
    set s := (F f).support un

中文:
定义 twoCochainOfBilinear
  签名: [CommRing A] [IsAddTorsionFree R] [Algebra A R]
  定义体: (residuePairing R A L Φ).compr₂ (TrivialLieModule.equiv R (loopAlgebra R A L) R).symm
  property := by
    refine Cohomology.mem_twoCochain_iff.mpr fun f => ?_
    let F := toFinsupp R A L
    suffices ((F f).sum fun a v => a • Φ (F f (-a)) v) = 0 by simpa
    classical
    set s := (F f).support un

Depends on / 依赖: TrivialLieModule, TrivialLieModule.equiv, loopAlgebra, residuePairing
-/
def twoCochainOfBilinear [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : Φ.IsSymm) :
    Cohomology.twoCochain R (loopAlgebra R A L) (TrivialLieModule R (loopAlgebra R A L) R) where
  val := (residuePairing R A L Φ).compr₂ (TrivialLieModule.equiv R (loopAlgebra R A L) R).symm
  property := by
    refine Cohomology.mem_twoCochain_iff.mpr fun f => ?_
    let F := toFinsupp R A L
    suffices ((F f).sum fun a v => a • Φ (F f (-a)) v) = 0 by simpa
    classical
    set s := (F f).support union (F f).support.image (Equiv.neg A) with hs
    have hs' : (F f).support subseteq s := Finset.subset_union_left
    rw [Finsupp.sum_of_support_subset _ hs' _ (by simp)]
    refine Function.Odd.finsetSum_eq_zero (fun n => by simp [hΦ.eq]) (Finset.map_eq_of_subset ?_)
    intro x hx
    rw [Finset.mem_union]
    replace hx : -x in (F f).support ∨ -x in (F f).support.image Neg.neg := by simpa [hs] using hx
    obtain (h | h) := hx
· exact Or.inr Finset.mem_image.mpr ⟨-x, by simp [h]⟩
· exact Or.inl by simpa using h

@[simp]
/--
lemma `twoCochainOfBilinear_apply_apply` / 引理 `twoCochainOfBilinear_apply_apply`

English:
lemma twoCochainOfBilinear_apply_apply
  statement: [CommRing A] [IsAddTorsionFree R] [Algebra A R]
  proof: rfl

中文:
引理 twoCochainOfBilinear_apply_apply
  结论: [CommRing A] [IsAddTorsionFree R] [Algebra A R]
  证明: rfl
-/
lemma twoCochainOfBilinear_apply_apply [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : Φ.IsSymm) (x y : loopAlgebra R A L) :
    twoCochainOfBilinear R A L Φ hΦ x y =
      (TrivialLieModule.equiv R (loopAlgebra R A L) R).symm (residuePairing R A L Φ x y) :=
  rfl

open LieModule in
/-- A 2-cocycle on a loop algebra given by an invariant bilinear form. -/
@[simps]
/--
Definition of `twoCocycleOfBilinear` / `twoCocycleOfBilinear` 的定义

English:
definition twoCocycleOfBilinear
  signature: [CommRing A] [IsAddTorsionFree R] [Algebra A R]
  body: twoCochainOfBilinear R A L Φ hΦs
  property := by
    apply (LieModule.Cohomology.mem_twoCocycle_iff ..).mpr
    ext a x b y c z
    suffices
        b • Φ (Finsupp.single (a + c) ⁅x, z⁆ (-b)) y =
        c • Φ (Finsupp.single (a + b) ⁅x, y⁆ (-c)) z +
        a • Φ (Finsupp.single (b + c) ⁅y, z⁆ (-a

中文:
定义 twoCocycleOfBilinear
  签名: [CommRing A] [IsAddTorsionFree R] [Algebra A R]
  定义体: twoCochainOfBilinear R A L Φ hΦs
  property := by
    apply (LieModule.Cohomology.mem_twoCocycle_iff ..).mpr
    ext a x b y c z
    suffices
        b • Φ (Finsupp.single (a + c) ⁅x, z⁆ (-b)) y =
        c • Φ (Finsupp.single (a + b) ⁅x, y⁆ (-c)) z +
        a • Φ (Finsupp.single (b + c) ⁅y, z⁆ (-a

Depends on / 依赖: twoCochainOfBilinear
-/
def twoCocycleOfBilinear [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) :
    Cohomology.twoCocycle R (loopAlgebra R A L) (TrivialLieModule R (loopAlgebra R A L) R) where
  val := twoCochainOfBilinear R A L Φ hΦs
  property := by
    apply (LieModule.Cohomology.mem_twoCocycle_iff ..).mpr
    ext a x b y c z
    suffices
        b • Φ (Finsupp.single (a + c) ⁅x, z⁆ (-b)) y =
        c • Φ (Finsupp.single (a + b) ⁅x, y⁆ (-c)) z +
        a • Φ (Finsupp.single (b + c) ⁅y, z⁆ (-a)) x by
      simpa [trivial_lie_zero, sub_eq_zero, neg_add_eq_iff_eq_add, ← LinearEquiv.map_add,
        -LinearEquiv.map_add]
    by_cases h0 : a + b + c = 0
    · suffices b • Φ ⁅x, z⁆ y = c • Φ ⁅x, y⁆ z + a • Φ ⁅y, z⁆ x by
        simpa only [show a + b = -c by grind, show a + c = -b by grind, show b + c = -a by grind,
          Finsupp.single_eq_same]
      rw [hΦ]; rw [hΦs.eq z ⁅x]; rw [y⁆]; rw [hΦ y]; rw [← lie_skew y x]; rw [hΦs.eq z]; rw [Φ.neg_left]; rw [neg_neg]; rw [show b = -(a + c) by grind]; rw [neg_smul]; rw [smul_neg]; rw [neg_neg]; rw [add_smul]; rw [add_comm]
    · simp [Finsupp.single_eq_of_ne (a := a + c) (a' := -b) (by grind),
        Finsupp.single_eq_of_ne (a := a + b) (a' := -c) (by grind),
        Finsupp.single_eq_of_ne (a := b + c) (a' := -a) (by grind)]

end LoopAlgebra

end LieAlgebra
