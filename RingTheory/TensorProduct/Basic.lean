/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Adjoin.Basic

/-!
# The tensor product of R-algebras

This file provides results about the multiplicative structure on `A ⊗[R] B` when `R` is a
commutative (semi)ring and `A` and `B` are both `R`-algebras. On these tensor products,
multiplication is characterized by `(a₁ ⊗ₜ b₁) * (a₂ ⊗ₜ b₂) = (a₁ * a₂) ⊗ₜ (b₁ * b₂)`.

## Main declarations

- `Algebra.TensorProduct.semiring`: the ring structure on `A ⊗[R] B` for two `R`-algebras `A`, `B`.
- `Algebra.TensorProduct.leftAlgebra`: the `S`-algebra structure on `A ⊗[R] B`, for when `A` is
  additionally an `S` algebra.

## References

* [C. Kassel, *Quantum Groups* (§II.4)][Kassel1995]

-/

@[expose] public section

assert_not_exists Equiv.Perm.cycleType

open scoped TensorProduct

open TensorProduct


namespace LinearMap

section liftBaseChange

variable {R M N} (A) [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
variable [AddCommMonoid N] [Module R M] [Module R N] [Module A N] [IsScalarTower R A N]

/--
Definition of `liftBaseChangeEquiv` / `liftBaseChangeEquiv` 的定义

English:
definition liftBaseChangeEquiv
  signature: : (M ->ₗ[R] N) ≃ₗ[A] (A otimes[R] M ->ₗ[A] N)
  body: (LinearMap.ringLmapEquivSelf _ _ _).symm.trans (AlgebraTensorModule.lift.equiv _ _ _ _ _ _)

中文:
定义 liftBaseChangeEquiv
  签名: : (M ->ₗ[R] N) ≃ₗ[A] (A otimes[R] M ->ₗ[A] N)
  定义体: (LinearMap.ringLmapEquivSelf _ _ _).symm.trans (AlgebraTensorModule.lift.equiv _ _ _ _ _ _)

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.lift.equiv, LinearMap, LinearMap.ringLmapEquivSelf, ringLmapEquivSelf, symm.trans
-/
def liftBaseChangeEquiv : (M ->ₗ[R] N) ≃ₗ[A] (A otimes[R] M ->ₗ[A] N) :=
  (LinearMap.ringLmapEquivSelf _ _ _).symm.trans (AlgebraTensorModule.lift.equiv _ _ _ _ _ _)

/--
Definition of `liftBaseChange` / `liftBaseChange` 的定义

English:
abbreviation liftBaseChange
  signature: (l : M ->ₗ[R] N)
  body: LinearMap.liftBaseChangeEquiv A l

@[simp]

中文:
缩写 liftBaseChange
  签名: (l : M ->ₗ[R] N)
  定义体: LinearMap.liftBaseChangeEquiv A l

@[simp]

Depends on / 依赖: LinearMap, LinearMap.liftBaseChangeEquiv, liftBaseChangeEquiv
-/
abbrev liftBaseChange (l : M ->ₗ[R] N) : A otimes[R] M ->ₗ[A] N :=
  LinearMap.liftBaseChangeEquiv A l

@[simp]
/--
lemma `liftBaseChange_tmul` / 引理 `liftBaseChange_tmul`

English:
lemma liftBaseChange_tmul
  given: (l : M ->ₗ[R] N) (x y)
  statement: l.liftBaseChange A (x otimesₜ y) = x • l y
  proof: rfl

中文:
引理 liftBaseChange_tmul
  条件: (l : M ->ₗ[R] N) (x y)
  结论: l.liftBaseChange A (x otimesₜ y) = x • l y
  证明: rfl
-/
lemma liftBaseChange_tmul (l : M ->ₗ[R] N) (x y) : l.liftBaseChange A (x otimesₜ y) = x • l y := rfl

/--
lemma `liftBaseChange_one_tmul` / 引理 `liftBaseChange_one_tmul`

English:
lemma liftBaseChange_one_tmul
  given: (l : M ->ₗ[R] N) (y)
  statement: l.liftBaseChange A (1 otimesₜ y) = l y
  proof: by simp

@[simp]

中文:
引理 liftBaseChange_one_tmul
  条件: (l : M ->ₗ[R] N) (y)
  结论: l.liftBaseChange A (1 otimesₜ y) = l y
  证明: by simp

@[simp]
-/
lemma liftBaseChange_one_tmul (l : M ->ₗ[R] N) (y) : l.liftBaseChange A (1 otimesₜ y) = l y := by simp

@[simp]
/--
lemma `liftBaseChangeEquiv_symm_apply` / 引理 `liftBaseChangeEquiv_symm_apply`

English:
lemma liftBaseChangeEquiv_symm_apply
  given: (l : A otimes[R] M ->ₗ[A] N) (x)
  proof: rfl

中文:
引理 liftBaseChangeEquiv_symm_apply
  条件: (l : A otimes[R] M ->ₗ[A] N) (x)
  证明: rfl
-/
lemma liftBaseChangeEquiv_symm_apply (l : A otimes[R] M ->ₗ[A] N) (x) :
    (liftBaseChangeEquiv A).symm l x = l (1 otimesₜ x) := rfl

/--
lemma `liftBaseChange_comp` / 引理 `liftBaseChange_comp`

English:
lemma liftBaseChange_comp
  statement: {P} [AddCommMonoid P] [Module A P] [Module R P] [IsScalarTower R A P]
  proof: by
  ext
  simp

@[simp]

中文:
引理 liftBaseChange_comp
  结论: {P} [AddCommMonoid P] [Module A P] [Module R P] [IsScalarTower R A P]
  证明: by
  ext
  simp

@[simp]
-/
lemma liftBaseChange_comp {P} [AddCommMonoid P] [Module A P] [Module R P] [IsScalarTower R A P]
    (l : M ->ₗ[R] N) (l' : N ->ₗ[A] P) :
      l' ∘ₗ l.liftBaseChange A = (l'.restrictScalars R ∘ₗ l).liftBaseChange A := by
  ext
  simp

@[simp]
/--
lemma `range_liftBaseChange` / 引理 `range_liftBaseChange`

English:
lemma range_liftBaseChange
  given: (l : M ->ₗ[R] N)
  proof: by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on
    · simp
    · rw [LinearMap.liftBaseChange_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · rw [map_add]
      exact add_mem ‹_› ‹_›
  · rw [Submodule.span_le]
    rintro _

中文:
引理 range_liftBaseChange
  条件: (l : M ->ₗ[R] N)
  证明: by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on
    · simp
    · rw [LinearMap.liftBaseChange_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · rw [map_add]
      exact add_mem ‹_› ‹_›
  · rw [Submodule.span_le]
    rintro _

Depends on / 依赖: LinearMap, LinearMap.liftBaseChange_tmul, Submodule, Submodule.smul_mem, Submodule.span_le, Submodule.subset_span, TensorProduct, TensorProduct.induction_on, add_mem, induction_on, le_antisymm, liftBaseChange_tmul, map_add, smul_mem, span_le, subset_span
-/
lemma range_liftBaseChange (l : M ->ₗ[R] N) :
    LinearMap.range (l.liftBaseChange A) = Submodule.span A (LinearMap.range l) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on
    · simp
    · rw [LinearMap.liftBaseChange_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · rw [map_add]
      exact add_mem ‹_› ‹_›
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨1 otimesₜ x, by simp⟩

end liftBaseChange

end LinearMap

namespace Algebra

namespace TensorProduct

universe uR uS uA uB uC uD uE uF
variable {R : Type uR} {R' : Type*} {S : Type uS} {T : Type*}
variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE} {F : Type uF}

/-!
### The `R`-algebra structure on `A ⊗[R] B`
-/

section AddCommMonoidWithOne

variable [CommSemiring R]
variable [AddCommMonoidWithOne A] [Module R A]
variable [AddCommMonoidWithOne B] [Module R B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (A otimes[R] B)
  body: 1 otimesₜ 1

中文:
实例 :
  签名: One (A otimes[R] B)
  定义体: 1 otimesₜ 1
-/
instance : One (A otimes[R] B) where one := 1 otimesₜ 1

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : A otimes[R] B) = (1 : A) otimesₜ (1 : B)
  proof: rfl

中文:
定理 one_def
  结论: (1 : A otimes[R] B) = (1 : A) otimesₜ (1 : B)
  证明: rfl
-/
theorem one_def : (1 : A otimes[R] B) = (1 : A) otimesₜ (1 : B) :=
  rfl

/--
Instance `instAddCommMonoidWithOne` / 实例 `instAddCommMonoidWithOne`

English:
instance instAddCommMonoidWithOne
  signature: : AddCommMonoidWithOne (A otimes[R] B) where
  body: n otimesₜ 1
  natCast_zero := by simp
  natCast_succ n := by simp [add_tmul, one_def]
  add_comm := add_comm

中文:
实例 instAddCommMonoidWithOne
  签名: : AddCommMonoidWithOne (A otimes[R] B) where
  定义体: n otimesₜ 1
  natCast_zero := by simp
  natCast_succ n := by simp [add_tmul, one_def]
  add_comm := add_comm
-/
instance instAddCommMonoidWithOne : AddCommMonoidWithOne (A otimes[R] B) where
  natCast n := n otimesₜ 1
  natCast_zero := by simp
  natCast_succ n := by simp [add_tmul, one_def]
  add_comm := add_comm

/--
theorem `natCast_def` / 定理 `natCast_def`

English:
theorem natCast_def
  given: (n : Nat)
  statement: (n : A otimes[R] B) = (n : A) otimesₜ (1 : B)
  proof: rfl

中文:
定理 natCast_def
  条件: (n : 自然数)
  结论: (n : A otimes[R] B) = (n : A) otimesₜ (1 : B)
  证明: rfl
-/
theorem natCast_def (n : Nat) : (n : A otimes[R] B) = (n : A) otimesₜ (1 : B) := rfl

/--
theorem `natCast_def'` / 定理 `natCast_def'`

English:
theorem natCast_def'
  given: (n : Nat)
  statement: (n : A otimes[R] B) = (1 : A) otimesₜ (n : B)
  proof: by
  rw [natCast_def]; rw [← nsmul_one]; rw [smul_tmul]; rw [nsmul_one]

中文:
定理 natCast_def'
  条件: (n : 自然数)
  结论: (n : A otimes[R] B) = (1 : A) otimesₜ (n : B)
  证明: by
  rw [natCast_def]; rw [← nsmul_one]; rw [smul_tmul]; rw [nsmul_one]

Depends on / 依赖: natCast_def, nsmul_one, smul_tmul
-/
theorem natCast_def' (n : Nat) : (n : A otimes[R] B) = (1 : A) otimesₜ (n : B) := by
  rw [natCast_def]; rw [← nsmul_one]; rw [smul_tmul]; rw [nsmul_one]

end AddCommMonoidWithOne

section NonUnitalNonAssocSemiring

variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

/-- (Implementation detail)
The multiplication map on `A ⊗[R] B`,
as an `R`-bilinear map.
-/
@[irreducible]
/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: : A otimes[R] B ->ₗ[R] A otimes[R] B ->ₗ[R] A otimes[R] B
  body: TensorProduct.map₂ (LinearMap.mul R A) (LinearMap.mul R B)

unseal mul in
@[simp]

中文:
定义 mul
  签名: : A otimes[R] B ->ₗ[R] A otimes[R] B ->ₗ[R] A otimes[R] B
  定义体: TensorProduct.map₂ (LinearMap.mul R A) (LinearMap.mul R B)

unseal mul in
@[simp]

Depends on / 依赖: LinearMap, LinearMap.mul, TensorProduct, TensorProduct.map
-/
def mul : A otimes[R] B ->ₗ[R] A otimes[R] B ->ₗ[R] A otimes[R] B :=
  TensorProduct.map₂ (LinearMap.mul R A) (LinearMap.mul R B)

unseal mul in
@[simp]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (a₁ a₂ : A) (b₁ b₂ : B)
  proof: rfl

中文:
定理 mul_apply
  条件: (a₁ a₂ : A) (b₁ b₂ : B)
  证明: rfl
-/
theorem mul_apply (a₁ a₂ : A) (b₁ b₂ : B) :
    mul (a₁ otimesₜ[R] b₁) (a₂ otimesₜ[R] b₂) = (a₁ * a₂) otimesₜ[R] (b₁ * b₂) :=
  rfl

-- providing this instance separately makes some downstream code substantially faster
/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (A otimes[R] B) where
  body: mul a b

unseal mul in
@[simp]

中文:
实例 instMul
  签名: : Mul (A otimes[R] B) where
  定义体: mul a b

unseal mul in
@[simp]
-/
instance instMul : Mul (A otimes[R] B) where
  mul a b := mul a b

unseal mul in
@[simp]
/--
theorem `tmul_mul_tmul` / 定理 `tmul_mul_tmul`

English:
theorem tmul_mul_tmul
  given: (a₁ a₂ : A) (b₁ b₂ : B)
  proof: rfl

unseal mul in

中文:
定理 tmul_mul_tmul
  条件: (a₁ a₂ : A) (b₁ b₂ : B)
  证明: rfl

unseal mul in
-/
theorem tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : B) :
    a₁ otimesₜ[R] b₁ * a₂ otimesₜ[R] b₂ = (a₁ * a₂) otimesₜ[R] (b₁ * b₂) :=
  rfl

unseal mul in
/--
theorem `_root_.SemiconjBy.tmul` / 定理 `_root_.SemiconjBy.tmul`

English:
theorem _root_.SemiconjBy.tmul
  statement: {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
  proof: congr_arg₂ (· otimesₜ[R] ·) ha.eq hb.eq

nonrec theorem _root_.Commute.tmul {a₁ a₂ : A} {b₁ b₂ : B}
    (ha : Commute a₁ a₂) (hb : Commute b₁ b₂) :
    Commute (a₁ otimesₜ[R] b₁) (a₂ otimesₜ[R] b₂) :=
  ha.tmul hb

中文:
定理 _root_.SemiconjBy.tmul
  结论: {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
  证明: congr_arg₂ (· otimesₜ[R] ·) ha.eq hb.eq

nonrec theorem _root_.Commute.tmul {a₁ a₂ : A} {b₁ b₂ : B}
    (ha : Commute a₁ a₂) (hb : Commute b₁ b₂) :
    Commute (a₁ otimesₜ[R] b₁) (a₂ otimesₜ[R] b₂) :=
  ha.tmul hb

Depends on / 依赖: ha.eq, hb.eq
-/
theorem _root_.SemiconjBy.tmul {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
    (ha : SemiconjBy a₁ a₂ a₃) (hb : SemiconjBy b₁ b₂ b₃) :
    SemiconjBy (a₁ otimesₜ[R] b₁) (a₂ otimesₜ[R] b₂) (a₃ otimesₜ[R] b₃) :=
  congr_arg₂ (· otimesₜ[R] ·) ha.eq hb.eq

nonrec theorem _root_.Commute.tmul {a₁ a₂ : A} {b₁ b₂ : B}
    (ha : Commute a₁ a₂) (hb : Commute b₁ b₂) :
    Commute (a₁ otimesₜ[R] b₁) (a₂ otimesₜ[R] b₂) :=
  ha.tmul hb

/--
Instance `instNonUnitalNonAssocSemiring` / 实例 `instNonUnitalNonAssocSemiring`

English:
instance instNonUnitalNonAssocSemiring
  signature: : NonUnitalNonAssocSemiring (A otimes[R] B) where
  body: by simp [HMul.hMul, Mul.mul]
  right_distrib a b c := by simp [HMul.hMul, Mul.mul]
  zero_mul a := by simp [HMul.hMul, Mul.mul]
  mul_zero a := by simp [HMul.hMul, Mul.mul]

中文:
实例 instNonUnitalNonAssocSemiring
  签名: : NonUnitalNonAssocSemiring (A otimes[R] B) where
  定义体: by simp [HMul.hMul, Mul.mul]
  right_distrib a b c := by simp [HMul.hMul, Mul.mul]
  zero_mul a := by simp [HMul.hMul, Mul.mul]
  mul_zero a := by simp [HMul.hMul, Mul.mul]

Depends on / 依赖: HMul.hMul, Mul.mul, mul_zero, right_distrib, zero_mul
-/
instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (A otimes[R] B) where
  left_distrib a b c := by simp [HMul.hMul, Mul.mul]
  right_distrib a b c := by simp [HMul.hMul, Mul.mul]
  zero_mul a := by simp [HMul.hMul, Mul.mul]
  mul_zero a := by simp [HMul.hMul, Mul.mul]

-- we want `isScalarTower_right` to take priority since it's better for unification elsewhere
instance (priority := 100) isScalarTower_right [Monoid S] [DistribMulAction S A]
    [IsScalarTower S A A] [SMulCommClass R S A] : IsScalarTower S (A otimes[R] B) (A otimes[R] B) where
  smul_assoc r x y := by
    change r • x * y = r • (x * y)
    induction y with
    | zero => simp [smul_zero]
    | tmul a b => induction x with
      | zero => simp [smul_zero]
      | tmul a' b' =>
        dsimp
        rw [TensorProduct.smul_tmul']; rw [TensorProduct.smul_tmul']; rw [tmul_mul_tmul]; rw [smul_mul_assoc]
      | add x y hx hy => simp [smul_add, add_mul _, *]
    | add x y hx hy => simp [smul_add, mul_add _, *]

-- we want `Algebra.to_smulCommClass` to take priority since it's better for unification elsewhere
instance (priority := 100) sMulCommClass_right [Monoid S] [DistribMulAction S A]
    [SMulCommClass S A A] [SMulCommClass R S A] : SMulCommClass S (A otimes[R] B) (A otimes[R] B) where
  smul_comm r x y := by
    change r • (x * y) = x * r • y
    induction y with
    | zero => simp [smul_zero]
    | tmul a b => induction x with
      | zero => simp [smul_zero]
      | tmul a' b' =>
        dsimp
        rw [TensorProduct.smul_tmul']; rw [TensorProduct.smul_tmul']; rw [tmul_mul_tmul]; rw [mul_smul_comm]
      | add x y hx hy => simp [smul_add, add_mul _, *]
    | add x y hx hy => simp [smul_add, mul_add _, *]

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [CommSemiring R]
variable [NonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

/--
theorem `one_mul` / 定理 `one_mul`

English:
theorem one_mul
  given: (x : A otimes[R] B)
  statement: mul (1 otimesₜ 1) x = x
  proof: by
  refine TensorProduct.induction_on x ?_ ?_ ?_ <;> simp +contextual

中文:
定理 one_mul
  条件: (x : A otimes[R] B)
  结论: mul (1 otimesₜ 1) x = x
  证明: by
  refine TensorProduct.induction_on x ?_ ?_ ?_ <;> simp +contextual
-/
protected theorem one_mul (x : A otimes[R] B) : mul (1 otimesₜ 1) x = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_ <;> simp +contextual

/--
theorem `mul_one` / 定理 `mul_one`

English:
theorem mul_one
  given: (x : A otimes[R] B)
  statement: mul x (1 otimesₜ 1) = x
  proof: by
  refine TensorProduct.induction_on x ?_ ?_ ?_ <;> simp +contextual

中文:
定理 mul_one
  条件: (x : A otimes[R] B)
  结论: mul x (1 otimesₜ 1) = x
  证明: by
  refine TensorProduct.induction_on x ?_ ?_ ?_ <;> simp +contextual
-/
protected theorem mul_one (x : A otimes[R] B) : mul x (1 otimesₜ 1) = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_ <;> simp +contextual

/--
Instance `instNonAssocSemiring` / 实例 `instNonAssocSemiring`

English:
instance instNonAssocSemiring
  signature: : NonAssocSemiring (A otimes[R] B) where
  body: Algebra.TensorProduct.one_mul
  mul_one := Algebra.TensorProduct.mul_one
  toNonUnitalNonAssocSemiring := instNonUnitalNonAssocSemiring
  __ := instAddCommMonoidWithOne

中文:
实例 instNonAssocSemiring
  签名: : NonAssocSemiring (A otimes[R] B) where
  定义体: Algebra.TensorProduct.one_mul
  mul_one := Algebra.TensorProduct.mul_one
  toNonUnitalNonAssocSemiring := instNonUnitalNonAssocSemiring
  __ := instAddCommMonoidWithOne

Depends on / 依赖: Algebra, Algebra.TensorProduct.one_mul, TensorProduct, one_mul
-/
instance instNonAssocSemiring : NonAssocSemiring (A otimes[R] B) where
  one_mul := Algebra.TensorProduct.one_mul
  mul_one := Algebra.TensorProduct.mul_one
  toNonUnitalNonAssocSemiring := instNonUnitalNonAssocSemiring
  __ := instAddCommMonoidWithOne

end NonAssocSemiring

section NonUnitalSemiring
variable [CommSemiring R]
variable [NonUnitalSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

unseal mul in
/--
theorem `mul_assoc` / 定理 `mul_assoc`

English:
theorem mul_assoc
  given: (x y z : A otimes[R] B)
  statement: mul (mul x y) z = mul x (mul y z)
  proof: by
  -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mul ∘ₗ mul =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip.toLinearMap <|
        LinearMap.llcomp R _ _ _ mul.flip ∘ₗ mul).flip by
    exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.co

中文:
定理 mul_assoc
  条件: (x y z : A otimes[R] B)
  结论: mul (mul x y) z = mul x (mul y z)
  证明: by
  -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mul ∘ₗ mul =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip.toLinearMap <|
        LinearMap.llcomp R _ _ _ mul.flip ∘ₗ mul).flip by
    exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.co
-/
protected theorem mul_assoc (x y z : A otimes[R] B) : mul (mul x y) z = mul x (mul y z) := by
  -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mul ∘ₗ mul =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip.toLinearMap <|
        LinearMap.llcomp R _ _ _ mul.flip ∘ₗ mul).flip by
    exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this x) y) z
  ext xa xb ya yb za zb
  exact congr_arg₂ (· otimesₜ ·) (mul_assoc xa ya za) (mul_assoc xb yb zb)

/--
Instance `instNonUnitalSemiring` / 实例 `instNonUnitalSemiring`

English:
instance instNonUnitalSemiring
  signature: : NonUnitalSemiring (A otimes[R] B) where
  body: Algebra.TensorProduct.mul_assoc

中文:
实例 instNonUnitalSemiring
  签名: : NonUnitalSemiring (A otimes[R] B) where
  定义体: Algebra.TensorProduct.mul_assoc

Depends on / 依赖: Algebra, Algebra.TensorProduct.mul_assoc, TensorProduct, mul_assoc
-/
instance instNonUnitalSemiring : NonUnitalSemiring (A otimes[R] B) where
  mul_assoc := Algebra.TensorProduct.mul_assoc

end NonUnitalSemiring

section Semiring
variable [CommSemiring R]
variable [Semiring A] [Algebra R A]
variable [Semiring B] [Algebra R B]
variable [Semiring C] [Algebra R C]

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: : Semiring (A otimes[R] B) where
  body: by simp [HMul.hMul, Mul.mul]
  right_distrib a b c := by simp [HMul.hMul, Mul.mul]
  zero_mul a := by simp [HMul.hMul, Mul.mul]
  mul_zero a := by simp [HMul.hMul, Mul.mul]
  mul_assoc := Algebra.TensorProduct.mul_assoc
  one_mul := Algebra.TensorProduct.one_mul
  mul_one := Algebra.TensorProduct.mu

中文:
实例 instSemiring
  签名: : Semiring (A otimes[R] B) where
  定义体: by simp [HMul.hMul, Mul.mul]
  right_distrib a b c := by simp [HMul.hMul, Mul.mul]
  zero_mul a := by simp [HMul.hMul, Mul.mul]
  mul_zero a := by simp [HMul.hMul, Mul.mul]
  mul_assoc := Algebra.TensorProduct.mul_assoc
  one_mul := Algebra.TensorProduct.one_mul
  mul_one := Algebra.TensorProduct.mu

Depends on / 依赖: AddMonoidWithOne, AddMonoidWithOne.natCast_succ, AddMonoidWithOne.natCast_zero, Algebra, Algebra.TensorProduct.mul_assoc, Algebra.TensorProduct.mul_one, Algebra.TensorProduct.one_mul, HMul.hMul, Mul.mul, TensorProduct, mul_assoc, mul_one, mul_zero, natCast_succ, natCast_zero, one_mul, right_distrib, zero_mul
-/
instance instSemiring : Semiring (A otimes[R] B) where
  left_distrib a b c := by simp [HMul.hMul, Mul.mul]
  right_distrib a b c := by simp [HMul.hMul, Mul.mul]
  zero_mul a := by simp [HMul.hMul, Mul.mul]
  mul_zero a := by simp [HMul.hMul, Mul.mul]
  mul_assoc := Algebra.TensorProduct.mul_assoc
  one_mul := Algebra.TensorProduct.one_mul
  mul_one := Algebra.TensorProduct.mul_one
  natCast_zero := AddMonoidWithOne.natCast_zero
  natCast_succ := AddMonoidWithOne.natCast_succ

@[simp]
/--
theorem `tmul_pow` / 定理 `tmul_pow`

English:
theorem tmul_pow
  given: (a : A) (b : B) (k : Nat)
  statement: a otimesₜ[R] b ^ k = (a ^ k) otimesₜ[R] (b ^ k)
  proof: by
  induction k with
  | zero => simp [one_def]
  | succ k ih => simp [pow_succ, ih]

中文:
定理 tmul_pow
  条件: (a : A) (b : B) (k : 自然数)
  结论: a otimesₜ[R] b ^ k = (a ^ k) otimesₜ[R] (b ^ k)
  证明: by
  induction k with
  | zero => simp [one_def]
  | succ k ih => simp [pow_succ, ih]

Depends on / 依赖: one_def, pow_succ
-/
theorem tmul_pow (a : A) (b : B) (k : Nat) : a otimesₜ[R] b ^ k = (a ^ k) otimesₜ[R] (b ^ k) := by
  induction k with
  | zero => simp [one_def]
  | succ k ih => simp [pow_succ, ih]

/-- The ring morphism `A →+* A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
@[simps!]
/--
Definition of `includeLeftRingHom` / `includeLeftRingHom` 的定义

English:
definition includeLeftRingHom
  signature: : A ->+* A otimes[R] B where
  body: (AlgebraTensorModule.mk R R A B).flip 1
  map_one' := rfl
  map_mul' := by simp

中文:
定义 includeLeftRingHom
  签名: : A ->+* A otimes[R] B where
  定义体: (AlgebraTensorModule.mk R R A B).flip 1
  map_one' := rfl
  map_mul' := by simp

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.mk
-/
def includeLeftRingHom : A ->+* A otimes[R] B where
.toAddMonoidHom __ := (AlgebraTensorModule.mk R R A B).flip 1
  map_one' := rfl
  map_mul' := by simp

variable [CommSemiring S] [Algebra S A]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `leftAlgebra` / 实例 `leftAlgebra`

English:
instance leftAlgebra
  signature: [SMulCommClass R S A]
  body: { commutes' := fun r x => by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply, includeLeftRingHom_apply]
      rw [algebraMap_eq_smul_one]; rw [← smul_tmul']; rw [← one_def]; rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [mul_one]; rw [one_mul]
    smul_def' := fun r x => by
      dsimp only

中文:
实例 leftAlgebra
  签名: [SMulCommClass R S A]
  定义体: { commutes' := fun r x => by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply, includeLeftRingHom_apply]
      rw [algebraMap_eq_smul_one]; rw [← smul_tmul']; rw [← one_def]; rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [mul_one]; rw [one_mul]
    smul_def' := fun r x => by
      dsimp only

Depends on / 依赖: RingHom, RingHom.comp_apply, RingHom.toFun_eq_coe, TensorProduct, TensorProduct.includeLeftRingHom.comp, algebraMap, algebraMap_eq_smul_one, commutes, comp_apply, includeLeftRingHom, includeLeftRingHom_apply, mul_one, mul_smul_comm, one_def, one_mul, smul_def, smul_mul_assoc, smul_tmul, toFun_eq_coe
-/
instance leftAlgebra [SMulCommClass R S A] : Algebra S (A otimes[R] B) :=
  { commutes' := fun r x => by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply, includeLeftRingHom_apply]
      rw [algebraMap_eq_smul_one]; rw [← smul_tmul']; rw [← one_def]; rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [mul_one]; rw [one_mul]
    smul_def' := fun r x => by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply, includeLeftRingHom_apply]
      rw [algebraMap_eq_smul_one]; rw [← smul_tmul']; rw [smul_mul_assoc]; rw [← one_def]; rw [one_mul]
    algebraMap := TensorProduct.includeLeftRingHom.comp (algebraMap S A) }

/--
lemma `algebraMap_def` / 引理 `algebraMap_def`

English:
lemma algebraMap_def
  given: [SMulCommClass R S A]
  proof: rfl

example : (Semiring.toNatAlgebra : Algebra Nat (Nat otimes[Nat] B)) = leftAlgebra := rfl

中文:
引理 algebraMap_def
  条件: [SMulCommClass R S A]
  证明: rfl

example : (Semiring.toNatAlgebra : Algebra Nat (Nat otimes[Nat] B)) = leftAlgebra := rfl
-/
lemma algebraMap_def [SMulCommClass R S A] :
    algebraMap S (A otimes[R] B) = includeLeftRingHom.comp (algebraMap S A) := rfl

example : (Semiring.toNatAlgebra : Algebra Nat (Nat otimes[Nat] B)) = leftAlgebra := rfl

-- This is for the `undergrad.yaml` list.
/--
Instance `instAlgebra` / 实例 `instAlgebra`

English:
instance instAlgebra
  signature: : Algebra R (A otimes[R] B)
  body: inferInstance

@[simp]

中文:
实例 instAlgebra
  签名: : Algebra R (A otimes[R] B)
  定义体: inferInstance

@[simp]
-/
instance instAlgebra : Algebra R (A otimes[R] B) :=
  inferInstance

@[simp]
/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: [SMulCommClass R S A] (r : S)
  proof: rfl

中文:
定理 algebraMap_apply
  条件: [SMulCommClass R S A] (r : S)
  证明: rfl
-/
theorem algebraMap_apply [SMulCommClass R S A] (r : S) :
    algebraMap S (A otimes[R] B) r = (algebraMap S A) r otimesₜ 1 :=
  rfl

/--
theorem `algebraMap_apply'` / 定理 `algebraMap_apply'`

English:
theorem algebraMap_apply'
  given: (r : R)
  proof: by
  rw [algebraMap_apply]; rw [Algebra.algebraMap_eq_smul_one]; rw [Algebra.algebraMap_eq_smul_one]; rw [smul_tmul]

中文:
定理 algebraMap_apply'
  条件: (r : R)
  证明: by
  rw [algebraMap_apply]; rw [Algebra.algebraMap_eq_smul_one]; rw [Algebra.algebraMap_eq_smul_one]; rw [smul_tmul]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_apply, algebraMap_eq_smul_one, smul_tmul
-/
theorem algebraMap_apply' (r : R) :
    algebraMap R (A otimes[R] B) r = 1 otimesₜ algebraMap R B r := by
  rw [algebraMap_apply]; rw [Algebra.algebraMap_eq_smul_one]; rw [Algebra.algebraMap_eq_smul_one]; rw [smul_tmul]

/--
Definition of `includeLeft` / `includeLeft` 的定义

English:
definition includeLeft
  signature: [SMulCommClass R S A]
  body: { includeLeftRingHom with commutes' := by simp }

@[simp]

中文:
定义 includeLeft
  签名: [SMulCommClass R S A]
  定义体: { includeLeftRingHom with commutes' := by simp }

@[simp]

Depends on / 依赖: commutes, includeLeftRingHom
-/
def includeLeft [SMulCommClass R S A] : A ->ₐ[S] A otimes[R] B :=
  { includeLeftRingHom with commutes' := by simp }

@[simp]
/--
theorem `includeLeft_apply` / 定理 `includeLeft_apply`

English:
theorem includeLeft_apply
  given: [SMulCommClass R S A] (a : A)
  proof: rfl

中文:
定理 includeLeft_apply
  条件: [SMulCommClass R S A] (a : A)
  证明: rfl
-/
theorem includeLeft_apply [SMulCommClass R S A] (a : A) :
    (includeLeft : A ->ₐ[S] A otimes[R] B) a = a otimesₜ 1 :=
  rfl

/--
theorem `toLinearMap_includeLeft` / 定理 `toLinearMap_includeLeft`

English:
theorem toLinearMap_includeLeft
  given: [SMulCommClass R S A]
  proof: rfl

中文:
定理 toLinearMap_includeLeft
  条件: [SMulCommClass R S A]
  证明: rfl
-/
@[simp] theorem toLinearMap_includeLeft [SMulCommClass R S A] :
    (includeLeft : A ->ₐ[S] A otimes[R] B).toLinearMap = (AlgebraTensorModule.mk R S A B).flip 1 := rfl

/--
Definition of `includeRight` / `includeRight` 的定义

English:
definition includeRight
  signature: : B ->ₐ[R] A otimes[R] B where
  body: AlgebraTensorModule.mk R R A B 1
  map_one' := rfl
  map_mul' := by simp
  commutes' r := by simp [algebraMap_eq_smul_one', smul_tmul]

@[simp]

中文:
定义 includeRight
  签名: : B ->ₐ[R] A otimes[R] B where
  定义体: AlgebraTensorModule.mk R R A B 1
  map_one' := rfl
  map_mul' := by simp
  commutes' r := by simp [algebraMap_eq_smul_one', smul_tmul]

@[simp]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.mk
-/
def includeRight : B ->ₐ[R] A otimes[R] B where
.toAddMonoidHom __ := AlgebraTensorModule.mk R R A B 1
  map_one' := rfl
  map_mul' := by simp
  commutes' r := by simp [algebraMap_eq_smul_one', smul_tmul]

@[simp]
/--
theorem `includeRight_apply` / 定理 `includeRight_apply`

English:
theorem includeRight_apply
  given: (b : B)
  statement: (includeRight : B ->ₐ[R] A otimes[R] B) b = 1 otimesₜ b
  proof: rfl

中文:
定理 includeRight_apply
  条件: (b : B)
  结论: (includeRight : B ->ₐ[R] A otimes[R] B) b = 1 otimesₜ b
  证明: rfl
-/
theorem includeRight_apply (b : B) : (includeRight : B ->ₐ[R] A otimes[R] B) b = 1 otimesₜ b :=
  rfl

/--
theorem `toLinearMap_includeRight` / 定理 `toLinearMap_includeRight`

English:
theorem toLinearMap_includeRight
  proof: rfl

中文:
定理 toLinearMap_includeRight
  证明: rfl
-/
@[simp] theorem toLinearMap_includeRight :
    (includeRight : B ->ₐ[R] A otimes[R] B).toLinearMap = AlgebraTensorModule.mk R R A B 1 := rfl

/--
theorem `includeLeftRingHom_comp_algebraMap` / 定理 `includeLeftRingHom_comp_algebraMap`

English:
theorem includeLeftRingHom_comp_algebraMap
  proof: by
  ext
  simp

中文:
定理 includeLeftRingHom_comp_algebraMap
  证明: by
  ext
  simp
-/
theorem includeLeftRingHom_comp_algebraMap :
    (includeLeftRingHom.comp (algebraMap R A) : R ->+* A otimes[R] B) =
      includeRight.toRingHom.comp (algebraMap R B) := by
  ext
  simp

section ext
variable [Algebra R S] [Algebra S C] [IsScalarTower R S A] [IsScalarTower R S C]

/-- A version of `TensorProduct.ext` for `AlgHom`.

Using this as the `@[ext]` lemma instead of `Algebra.TensorProduct.ext'` allows `ext` to apply
lemmas specific to `A →ₐ[S] _` and `B →ₐ[R] _`; notably this allows recursion into nested tensor
products of algebras.

See note [partially-applied ext lemmas]. -/
@[ext high]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: (A otimes[R] B) ->ₐ[S] C⦄
  proof: by
  apply AlgHom.toLinearMap_injective
  ext a b
  have := congr_arg₂ HMul.hMul (AlgHom.congr_fun ha a) (AlgHom.congr_fun hb b)
  dsimp at *
  rwa [← map_mul, ← map_mul, tmul_mul_tmul, one_mul, mul_one] at this

中文:
定理 ext
  条件: ⦃f g
  结论: (A otimes[R] B) ->ₐ[S] C⦄
  证明: by
  apply AlgHom.toLinearMap_injective
  ext a b
  have := congr_arg₂ HMul.hMul (AlgHom.congr_fun ha a) (AlgHom.congr_fun hb b)
  dsimp at *
  rwa [← map_mul, ← map_mul, tmul_mul_tmul, one_mul, mul_one] at this

Depends on / 依赖: AlgHom, AlgHom.congr_fun, AlgHom.toLinearMap_injective, HMul.hMul, congr_fun, map_mul, mul_one, one_mul, tmul_mul_tmul, toLinearMap_injective
-/
theorem ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄
    (ha : f.comp includeLeft = g.comp includeLeft)
    (hb : (f.restrictScalars R).comp includeRight = (g.restrictScalars R).comp includeRight) :
    f = g := by
  apply AlgHom.toLinearMap_injective
  ext a b
  have := congr_arg₂ HMul.hMul (AlgHom.congr_fun ha a) (AlgHom.congr_fun hb b)
  dsimp at *
  rwa [← map_mul, ← map_mul, tmul_mul_tmul, one_mul, mul_one] at this

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  given: {g h : A otimes[R] B ->ₐ[S] C} (H : forall a b, g (a otimesₜ b) = h (a otimesₜ b))
  statement: g = h
  proof: ext (AlgHom.ext fun _ => H _ _) (AlgHom.ext fun _ => H _ _)

@[ext high]

中文:
定理 ext'
  条件: {g h : A otimes[R] B ->ₐ[S] C} (H : 对任意 a b, g (a otimesₜ b) = h (a otimesₜ b))
  结论: g = h
  证明: ext (AlgHom.ext fun _ => H _ _) (AlgHom.ext fun _ => H _ _)

@[ext high]

Depends on / 依赖: AlgHom, AlgHom.ext
-/
theorem ext' {g h : A otimes[R] B ->ₐ[S] C} (H : forall a b, g (a otimesₜ b) = h (a otimesₜ b)) : g = h :=
  ext (AlgHom.ext fun _ => H _ _) (AlgHom.ext fun _ => H _ _)

@[ext high]
/--
lemma `ringHom_ext` / 引理 `ringHom_ext`

English:
lemma ringHom_ext
  statement: {C : Type*} [Semiring C] {f g : A otimes[R] B ->+* C}
  proof: by
  ext x
  induction x with
  | zero => simp
  | add x y _ _ => simp_all
  | tmul x y => simpa [← map_mul] using congr($h₁ x * $h₂ y)

中文:
引理 ringHom_ext
  结论: {C : 类型} [Semiring C] {f g : A otimes[R] B ->+* C}
  证明: by
  ext x
  induction x with
  | zero => simp
  | add x y _ _ => simp_all
  | tmul x y => simpa [← map_mul] using congr($h₁ x * $h₂ y)

Depends on / 依赖: map_mul
-/
lemma ringHom_ext {C : Type*} [Semiring C] {f g : A otimes[R] B ->+* C}
    (h₁ : f.comp includeLeftRingHom = g.comp includeLeftRingHom)
    (h₂ : f.comp includeRight.toRingHom = g.comp includeRight.toRingHom) : f = g := by
  ext x
  induction x with
  | zero => simp
  | add x y _ _ => simp_all
  | tmul x y => simpa [← map_mul] using congr($h₁ x * $h₂ y)

end ext

end Semiring

section AddCommGroupWithOne
variable [CommSemiring R]
variable [AddCommGroupWithOne A] [Module R A]
variable [AddCommMonoidWithOne B] [Module R B]

/--
Instance `instAddCommGroupWithOne` / 实例 `instAddCommGroupWithOne`

English:
instance instAddCommGroupWithOne
  signature: : AddCommGroupWithOne (A otimes[R] B) where
  body: TensorProduct.addCommGroup
  __ := instAddCommMonoidWithOne
  intCast z := z otimesₜ (1 : B)
  intCast_ofNat n := by simp [natCast_def]
  intCast_negSucc n := by simp [natCast_def, add_tmul, neg_tmul, one_def]

中文:
实例 instAddCommGroupWithOne
  签名: : AddCommGroupWithOne (A otimes[R] B) where
  定义体: TensorProduct.addCommGroup
  __ := instAddCommMonoidWithOne
  intCast z := z otimesₜ (1 : B)
  intCast_ofNat n := by simp [natCast_def]
  intCast_negSucc n := by simp [natCast_def, add_tmul, neg_tmul, one_def]

Depends on / 依赖: TensorProduct, TensorProduct.addCommGroup, addCommGroup
-/
instance instAddCommGroupWithOne : AddCommGroupWithOne (A otimes[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instAddCommMonoidWithOne
  intCast z := z otimesₜ (1 : B)
  intCast_ofNat n := by simp [natCast_def]
  intCast_negSucc n := by simp [natCast_def, add_tmul, neg_tmul, one_def]

/--
theorem `intCast_def` / 定理 `intCast_def`

English:
theorem intCast_def
  given: (z : Int)
  statement: (z : A otimes[R] B) = (z : A) otimesₜ (1 : B)
  proof: rfl

中文:
定理 intCast_def
  条件: (z : 整数)
  结论: (z : A otimes[R] B) = (z : A) otimesₜ (1 : B)
  证明: rfl

Depends on / 依赖: coe_add, coe_injective, coe_injective.nonUnitalNonAssocSemiring, coe_mul, coe_nsmul, coe_zero, fast_instance, nonUnitalNonAssocSemiring
-/
theorem intCast_def (z : Int) : (z : A otimes[R] B) = (z : A) otimesₜ (1 : B) := rfl

end AddCommGroupWithOne

section NonUnitalNonAssocRing
variable [CommSemiring R]
variable [NonUnitalNonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

/--
Instance `instNonUnitalNonAssocRing` / 实例 `instNonUnitalNonAssocRing`

English:
instance instNonUnitalNonAssocRing
  signature: : NonUnitalNonAssocRing (A otimes[R] B) where
  body: TensorProduct.addCommGroup
  __ := instNonUnitalNonAssocSemiring

中文:
实例 instNonUnitalNonAssocRing
  签名: : NonUnitalNonAssocRing (A otimes[R] B) where
  定义体: TensorProduct.addCommGroup
  __ := instNonUnitalNonAssocSemiring

Depends on / 依赖: TensorProduct, TensorProduct.addCommGroup, addCommGroup, fast_instance
-/
instance instNonUnitalNonAssocRing : NonUnitalNonAssocRing (A otimes[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonUnitalNonAssocSemiring

end NonUnitalNonAssocRing

section NonAssocRing
variable [CommSemiring R]
variable [NonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

/--
Instance `instNonAssocRing` / 实例 `instNonAssocRing`

English:
instance instNonAssocRing
  signature: : NonAssocRing (A otimes[R] B) where
  body: TensorProduct.addCommGroup
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

中文:
实例 instNonAssocRing
  签名: : NonAssocRing (A otimes[R] B) where
  定义体: TensorProduct.addCommGroup
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

Depends on / 依赖: TensorProduct, TensorProduct.addCommGroup, addCommGroup, fast_instance
-/
instance instNonAssocRing : NonAssocRing (A otimes[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

end NonAssocRing

section NonUnitalRing
variable [CommSemiring R]
variable [NonUnitalRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

/--
Instance `instNonUnitalRing` / 实例 `instNonUnitalRing`

English:
instance instNonUnitalRing
  signature: : NonUnitalRing (A otimes[R] B) where
  body: TensorProduct.addCommGroup
  __ := instNonUnitalSemiring

中文:
实例 instNonUnitalRing
  签名: : NonUnitalRing (A otimes[R] B) where
  定义体: TensorProduct.addCommGroup
  __ := instNonUnitalSemiring

Depends on / 依赖: TensorProduct, TensorProduct.addCommGroup, addCommGroup, fast_instance
-/
instance instNonUnitalRing : NonUnitalRing (A otimes[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonUnitalSemiring

end NonUnitalRing

section CommSemiring
variable [CommSemiring R]
variable [CommSemiring A] [Algebra R A]
variable [CommSemiring B] [Algebra R B]

/--
Instance `instCommSemiring` / 实例 `instCommSemiring`

English:
instance instCommSemiring
  signature: : CommSemiring (A otimes[R] B) where
  body: inferInstance
  mul_comm x y := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro a₁ b₁
      refine TensorProduct.induction_on y ?_ ?_ ?_
      · simp
      · intro a₂ b₂
        simp [mul_comm]
      · intro a₂ b₂ ha hb
        simp [mul_add, add_mul, ha, hb]
    · intro x

中文:
实例 instCommSemiring
  签名: : CommSemiring (A otimes[R] B) where
  定义体: inferInstance
  mul_comm x y := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro a₁ b₁
      refine TensorProduct.induction_on y ?_ ?_ ?_
      · simp
      · intro a₂ b₂
        simp [mul_comm]
      · intro a₂ b₂ ha hb
        simp [mul_add, add_mul, ha, hb]
    · intro x

Depends on / 依赖: fast_instance
-/
instance instCommSemiring : CommSemiring (A otimes[R] B) where
  toSemiring := inferInstance
  mul_comm x y := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro a₁ b₁
      refine TensorProduct.induction_on y ?_ ?_ ?_
      · simp
      · intro a₂ b₂
        simp [mul_comm]
      · intro a₂ b₂ ha hb
        simp [mul_add, add_mul, ha, hb]
    · intro x₁ x₂ h₁ h₂
      simp [mul_add, add_mul, h₁, h₂]

end CommSemiring

section Ring
variable [CommSemiring R]
variable [Ring A] [Algebra R A]
variable [Semiring B] [Algebra R B]

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: : Ring (A otimes[R] B) where
  body: instSemiring
  __ := TensorProduct.addCommGroup
  __ := instNonAssocRing

中文:
实例 instRing
  签名: : Ring (A otimes[R] B) where
  定义体: instSemiring
  __ := TensorProduct.addCommGroup
  __ := instNonAssocRing

Depends on / 依赖: coe_add, coe_injective, coe_injective.nonUnitalNonAssocRing, coe_mul, coe_neg, coe_nsmul, coe_sub, coe_zero, coe_zsmul, fast_instance, instSemiring, nonUnitalNonAssocRing
-/
instance instRing : Ring (A otimes[R] B) where
  toSemiring := instSemiring
  __ := TensorProduct.addCommGroup
  __ := instNonAssocRing

/--
theorem `intCast_def'` / 定理 `intCast_def'`

English:
theorem intCast_def'
  given: {B} [Ring B] [Algebra R B] (z : Int)
  statement: (z : A otimes[R] B) = (1 : A) otimesₜ (z : B)
  proof: by
  rw [intCast_def]; rw [← zsmul_one]; rw [smul_tmul]; rw [zsmul_one]

中文:
定理 intCast_def'
  条件: {B} [Ring B] [Algebra R B] (z : 整数)
  结论: (z : A otimes[R] B) = (1 : A) otimesₜ (z : B)
  证明: by
  rw [intCast_def]; rw [← zsmul_one]; rw [smul_tmul]; rw [zsmul_one]

Depends on / 依赖: fast_instance, intCast_def, smul_tmul, zsmul_one
-/
theorem intCast_def' {B} [Ring B] [Algebra R B] (z : Int) : (z : A otimes[R] B) = (1 : A) otimesₜ (z : B) := by
  rw [intCast_def]; rw [← zsmul_one]; rw [smul_tmul]; rw [zsmul_one]

-- verify there are no diamonds
example : (instRing : Ring (A otimes[R] B)).toAddCommGroup = addCommGroup := by
  with_reducible_and_instances rfl
-- fails at `with_reducible_and_instances rfl` https://github.com/leanprover-community/mathlib4/issues/10906
example : (Ring.toIntAlgebra _ : Algebra Int (Int otimes[Int] A)) = leftAlgebra := rfl

end Ring

section CommRing
variable [CommSemiring R]
variable [CommRing A] [Algebra R A]
variable [CommSemiring B] [Algebra R B]

/--
Instance `instCommRing` / 实例 `instCommRing`

English:
instance instCommRing
  signature: : CommRing (A otimes[R] B)
  body: { toRing := inferInstance
    mul_comm := mul_comm }

中文:
实例 instCommRing
  签名: : CommRing (A otimes[R] B)
  定义体: { toRing := inferInstance
    mul_comm := mul_comm }

Depends on / 依赖: fast_instance, mul_comm, toRing
-/
instance instCommRing : CommRing (A otimes[R] B) :=
  { toRing := inferInstance
    mul_comm := mul_comm }

end CommRing

section RightAlgebra

variable [CommSemiring R]
variable [Semiring A] [Algebra R A]
variable [CommSemiring B] [Algebra R B]

/--
Definition of `rightAlgebra` / `rightAlgebra` 的定义

English:
abbreviation rightAlgebra
  signature: : Algebra B (A otimes[R] B)
  body: includeRight.toRingHom.toAlgebra' fun b x => by
    suffices LinearMap.mulLeft R (includeRight b) = LinearMap.mulRight R (includeRight b) from
      congr($this x)
    ext xa xb
    simp [mul_comm]

中文:
缩写 rightAlgebra
  签名: : Algebra B (A otimes[R] B)
  定义体: includeRight.toRingHom.toAlgebra' fun b x => by
    suffices LinearMap.mulLeft R (includeRight b) = LinearMap.mulRight R (includeRight b) from
      congr($this x)
    ext xa xb
    simp [mul_comm]

Depends on / 依赖: LinearMap, LinearMap.mulLeft, LinearMap.mulRight, includeRight, includeRight.toRingHom.toAlgebra, mulLeft, mulRight, mul_comm, toAlgebra, toRingHom
-/
abbrev rightAlgebra : Algebra B (A otimes[R] B) :=
  includeRight.toRingHom.toAlgebra' fun b x => by
    suffices LinearMap.mulLeft R (includeRight b) = LinearMap.mulRight R (includeRight b) from
      congr($this x)
    ext xa xb
    simp [mul_comm]

attribute [local instance] TensorProduct.rightAlgebra

/--
lemma `algebraMap_eq_includeRight` / 引理 `algebraMap_eq_includeRight`

English:
lemma algebraMap_eq_includeRight
  proof: rightAlgebra (R := R) (A := A) (B := B)
    algebraMap B (A otimes[R] B) = includeRight (R := R) (A := A) (B := B) := rfl

中文:
引理 algebraMap_eq_includeRight
  证明: rightAlgebra (R := R) (A := A) (B := B)
    algebraMap B (A otimes[R] B) = includeRight (R := R) (A := A) (B := B) := rfl

Depends on / 依赖: coe_add, coe_injective, coe_injective.nonUnitalCommSemiring, coe_mul, coe_nsmul, coe_zero, fast_instance, nonUnitalCommSemiring, rightAlgebra
-/
lemma algebraMap_eq_includeRight :
    letI := rightAlgebra (R := R) (A := A) (B := B)
    algebraMap B (A otimes[R] B) = includeRight (R := R) (A := A) (B := B) := rfl

/--
Instance `right_isScalarTower` / 实例 `right_isScalarTower`

English:
instance right_isScalarTower
  signature: : IsScalarTower R B (A otimes[R] B)
  body: IsScalarTower.of_algebraMap_eq fun r => (Algebra.TensorProduct.includeRight.commutes r).symm

中文:
实例 right_isScalarTower
  签名: : IsScalarTower R B (A otimes[R] B)
  定义体: IsScalarTower.of_algebraMap_eq fun r => (Algebra.TensorProduct.includeRight.commutes r).symm

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRight.commutes, IsScalarTower, IsScalarTower.of_algebraMap_eq, TensorProduct, commutes, fast_instance, includeRight, of_algebraMap_eq
-/
instance right_isScalarTower : IsScalarTower R B (A otimes[R] B) :=
  IsScalarTower.of_algebraMap_eq fun r => (Algebra.TensorProduct.includeRight.commutes r).symm

/--
lemma `right_algebraMap_apply` / 引理 `right_algebraMap_apply`

English:
lemma right_algebraMap_apply
  given: (b : B)
  statement: algebraMap B (A otimes[R] B) b = 1 otimesₜ b
  proof: rfl

中文:
引理 right_algebraMap_apply
  条件: (b : B)
  结论: algebraMap B (A otimes[R] B) b = 1 otimesₜ b
  证明: rfl

Depends on / 依赖: fast_instance
-/
lemma right_algebraMap_apply (b : B) : algebraMap B (A otimes[R] B) b = 1 otimesₜ b := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass A B (A otimes[R] B)
  body: x.induction_on (by simp)
    (fun _ _ => by simp [Algebra.smul_def, right_algebraMap_apply, smul_tmul'])
    fun _ _ h₁ h₂ => by simpa using congr($h₁ + $h₂)

中文:
实例 :
  签名: SMulCommClass A B (A otimes[R] B)
  定义体: x.induction_on (by simp)
    (fun _ _ => by simp [Algebra.smul_def, right_algebraMap_apply, smul_tmul'])
    fun _ _ h₁ h₂ => by simpa using congr($h₁ + $h₂)

Depends on / 依赖: fast_instance, induction_on, x.induction_on
-/
instance : SMulCommClass A B (A otimes[R] B) where
  smul_comm a b x := x.induction_on (by simp)
    (fun _ _ => by simp [Algebra.smul_def, right_algebraMap_apply, smul_tmul'])
    fun _ _ h₁ h₂ => by simpa using congr($h₁ + $h₂)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass B A (A otimes[R] B)
  body: .symm ..

中文:
实例 :
  签名: SMulCommClass B A (A otimes[R] B)
  定义体: .symm ..
-/
instance : SMulCommClass B A (A otimes[R] B) := .symm ..

end RightAlgebra

/-- Verify that typeclass search finds the ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely rings, by treating both as `ℤ`-algebras.
-/
example [Ring A] [Ring B] : Ring (A otimes[Int] B) := by infer_instance

/-- Verify that typeclass search finds the CommRing structure on `A ⊗[ℤ] B`
when `A` and `B` are merely `CommRing`s, by treating both as `ℤ`-algebras.
-/
example [CommRing A] [CommRing B] : CommRing (A otimes[Int] B) := by infer_instance

variable (R A B) in
/--
lemma `closure_range_union_range_eq_top` / 引理 `closure_range_union_range_eq_top`

English:
lemma closure_range_union_range_eq_top
  statement: [CommRing R] [Ring A] [Ring B]
  proof: by
  rw [← top_le_iff]
  rintro x -
  induction x with
  | zero => exact zero_mem _
  | tmul x y =>
    convert_to (Algebra.TensorProduct.includeLeftRingHom (R := R) x) *
      (Algebra.TensorProduct.includeRight y) in _
    · simp
    · exact mul_mem (Subring.subset_closure (.inl ⟨x, rfl⟩))
       

中文:
引理 closure_range_union_range_eq_top
  结论: [CommRing R] [Ring A] [Ring B]
  证明: by
  rw [← top_le_iff]
  rintro x -
  induction x with
  | zero => exact zero_mem _
  | tmul x y =>
    convert_to (Algebra.TensorProduct.includeLeftRingHom (R := R) x) *
      (Algebra.TensorProduct.includeRight y) in _
    · simp
    · exact mul_mem (Subring.subset_closure (.inl ⟨x, rfl⟩))
       

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeLeftRingHom, Algebra.TensorProduct.includeRight, Subring, Subring.subset_closure, TensorProduct, add_mem, convert_to, includeLeftRingHom, includeRight, mul_mem, subset_closure, top_le_iff, zero_mem
-/
lemma closure_range_union_range_eq_top [CommRing R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] :
    Subring.closure (Set.range (Algebra.TensorProduct.includeLeft : A ->ₐ[R] A otimes[R] B) union
      Set.range Algebra.TensorProduct.includeRight) = ⊤ := by
  rw [← top_le_iff]
  rintro x -
  induction x with
  | zero => exact zero_mem _
  | tmul x y =>
    convert_to (Algebra.TensorProduct.includeLeftRingHom (R := R) x) *
      (Algebra.TensorProduct.includeRight y) in _
    · simp
    · exact mul_mem (Subring.subset_closure (.inl ⟨x, rfl⟩))
        (Subring.subset_closure (.inr ⟨_, rfl⟩))
  | add x y _ _ => exact add_mem ‹_› ‹_›

set_option backward.isDefEq.respectTransparency false in
/--
lemma `adjoin_one_tmul_image_eq_top` / 引理 `adjoin_one_tmul_image_eq_top`

English:
lemma adjoin_one_tmul_image_eq_top
  statement: [CommSemiring R] [CommSemiring A]
  proof: by
  suffices h : adjoin A ((⊤ : Subalgebra R B).map (includeRight (A := A)) : Set (A otimes[R] B)) = ⊤ by
    simp [← h, ← hs, AlgHom.map_adjoin, adjoin_adjoin_of_tower]
  rw [← Algebra.toSubmodule_eq_top]; rw [← top_le_iff]; rw [Algebra.map_top]; rw [← Submodule.baseChange_top]; rw [Submodule.base

中文:
引理 adjoin_one_tmul_image_eq_top
  结论: [CommSemiring R] [CommSemiring A]
  证明: by
  suffices h : adjoin A ((⊤ : Subalgebra R B).map (includeRight (A := A)) : Set (A otimes[R] B)) = ⊤ by
    simp [← h, ← hs, AlgHom.map_adjoin, adjoin_adjoin_of_tower]
  rw [← Algebra.toSubmodule_eq_top]; rw [← top_le_iff]; rw [Algebra.map_top]; rw [← Submodule.baseChange_top]; rw [Submodule.base

Depends on / 依赖: AlgHom, AlgHom.map_adjoin, Algebra, Algebra.map_top, Algebra.toSubmodule_eq_top, Subalgebra, Submodule, Submodule.baseChange_eq_span, Submodule.baseChange_top, Submodule.map_top, adjoin, adjoin_adjoin_of_tower, baseChange_eq_span, baseChange_top, includeRight, map_adjoin, map_top, otimes, span_le_adjoin, toSubmodule_eq_top
-/
lemma adjoin_one_tmul_image_eq_top [CommSemiring R] [CommSemiring A]
    [Semiring B] [Algebra R A] [Algebra R B]
    (s : Set B) (hs : adjoin R s = ⊤) : adjoin A (((1 : A) otimesₜ[R] ·) '' s) = ⊤ := by
  suffices h : adjoin A ((⊤ : Subalgebra R B).map (includeRight (A := A)) : Set (A otimes[R] B)) = ⊤ by
    simp [← h, ← hs, AlgHom.map_adjoin, adjoin_adjoin_of_tower]
  rw [← Algebra.toSubmodule_eq_top]; rw [← top_le_iff]; rw [Algebra.map_top]; rw [← Submodule.baseChange_top]; rw [Submodule.baseChange_eq_span]; rw [Submodule.map_top]
  exact span_le_adjoin _ _

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

/--
lemma `mk_one_injective_of_isScalarTower` / 引理 `mk_one_injective_of_isScalarTower`

English:
lemma mk_one_injective_of_isScalarTower
  statement: (M : Type*) [AddCommMonoid M]
  proof: by
  apply Function.RightInverse.injective (g := LinearMap.liftBaseChange S LinearMap.id)
  intro m
  simp

中文:
引理 mk_one_injective_of_isScalarTower
  结论: (M : 类型) [AddCommMonoid M]
  证明: by
  apply Function.RightInverse.injective (g := LinearMap.liftBaseChange S LinearMap.id)
  intro m
  simp

Depends on / 依赖: Function, Function.RightInverse.injective, LinearMap, LinearMap.id, LinearMap.liftBaseChange, RightInverse, injective, liftBaseChange
-/
lemma mk_one_injective_of_isScalarTower (M : Type*) [AddCommMonoid M]
    [Module R M] [Module S M] [IsScalarTower R S M] :
    Function.Injective (TensorProduct.mk R S M 1) := by
  apply Function.RightInverse.injective (g := LinearMap.liftBaseChange S LinearMap.id)
  intro m
  simp

end TensorProduct

end Algebra

/--
lemma `Algebra.baseChange_lmul` / 引理 `Algebra.baseChange_lmul`

English:
lemma Algebra.baseChange_lmul
  statement: {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
  proof: by
  ext i
  simp

中文:
引理 Algebra.baseChange_lmul
  结论: {R B : 类型} [CommSemiring R] [Semiring B] [Algebra R B]
  证明: by
  ext i
  simp
-/
lemma Algebra.baseChange_lmul {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
    {A : Type*} [CommSemiring A] [Algebra R A] (f : B) :
    (Algebra.lmul R B f).baseChange A = Algebra.lmul A (A otimes[R] B) (1 otimesₜ f) := by
  ext i
  simp

namespace TensorProduct.Algebra

variable {R A B M : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [Semiring A] [Semiring B] [Module A M] [Module B M]
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R A M] [IsScalarTower R B M]

/--
Definition of `moduleAux` / `moduleAux` 的定义

English:
definition moduleAux
  signature: : A otimes[R] B ->ₗ[R] M ->ₗ[R] M
  body: TensorProduct.lift
    { toFun := fun a => a • (Algebra.lsmul R R M : B ->ₐ[R] Module.End R M).toLinearMap
      map_add' := fun r t => by
        ext
        simp only [add_smul, LinearMap.add_apply]
      map_smul' := fun n r => by
        ext
        simp only [RingHom.id_apply, LinearMap.smul_ap

中文:
定义 moduleAux
  签名: : A otimes[R] B ->ₗ[R] M ->ₗ[R] M
  定义体: TensorProduct.lift
    { toFun := fun a => a • (Algebra.lsmul R R M : B ->ₐ[R] Module.End R M).toLinearMap
      map_add' := fun r t => by
        ext
        simp only [add_smul, LinearMap.add_apply]
      map_smul' := fun n r => by
        ext
        simp only [RingHom.id_apply, LinearMap.smul_ap

Depends on / 依赖: Algebra, Algebra.lsmul, LinearMap, LinearMap.add_apply, LinearMap.smul_apply, Module, Module.End, RingHom, RingHom.id_apply, TensorProduct, TensorProduct.lift, add_apply, add_smul, id_apply, map_add, map_smul, smul_apply, smul_assoc, toLinearMap
-/
def moduleAux : A otimes[R] B ->ₗ[R] M ->ₗ[R] M :=
  TensorProduct.lift
    { toFun := fun a => a • (Algebra.lsmul R R M : B ->ₐ[R] Module.End R M).toLinearMap
      map_add' := fun r t => by
        ext
        simp only [add_smul, LinearMap.add_apply]
      map_smul' := fun n r => by
        ext
        simp only [RingHom.id_apply, LinearMap.smul_apply, smul_assoc] }

/--
theorem `moduleAux_apply` / 定理 `moduleAux_apply`

English:
theorem moduleAux_apply
  given: (a : A) (b : B) (m : M)
  statement: moduleAux (a otimesₜ[R] b) m = a • b • m
  proof: rfl

中文:
定理 moduleAux_apply
  条件: (a : A) (b : B) (m : M)
  结论: moduleAux (a otimesₜ[R] b) m = a • b • m
  证明: rfl
-/
theorem moduleAux_apply (a : A) (b : B) (m : M) : moduleAux (a otimesₜ[R] b) m = a • b • m :=
  rfl

variable [SMulCommClass A B M]

/-- If `M` is a representation of two different `R`-algebras `A` and `B` whose actions commute,
then it is a representation the `R`-algebra `A ⊗[R] B`.

An important example arises from a semiring `S`; allowing `S` to act on itself via left and right
multiplication, the roles of `R`, `A`, `B`, `M` are played by `ℕ`, `S`, `Sᵐᵒᵖ`, `S`. This example
is important because a submodule of `S` as a `Module` over `S ⊗[ℕ] Sᵐᵒᵖ` is a two-sided ideal.

NB: This is not an instance because in the case `B = A` and `M = A ⊗[R] A` we would have a diamond
of `smul` actions. Furthermore, this would not be a mere definitional diamond but a true
mathematical diamond in which `A ⊗[R] A` had two distinct scalar actions on itself: one from its
multiplication, and one from this would-be instance. Arguably we could live with this but in any
case the real fix is to address the ambiguity in notation, probably along the lines outlined here:
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.234773.20base.20change/near/240929258
-/
@[instance_reducible]
/--
Definition of `module` / `module` 的定义

English:
definition module
  signature: : Module (A otimes[R] B) M where
  body: moduleAux x m
  zero_smul m := by simp only [(· • ·), map_zero, LinearMap.zero_apply]
  smul_zero x := by simp only [(· • ·), map_zero]
  smul_add x m₁ m₂ := by simp only [(· • ·), map_add]
  add_smul x y m := by simp only [(· • ·), map_add, LinearMap.add_apply]
  one_smul m := by
    -- Porting not

中文:
定义 module
  签名: : Module (A otimes[R] B) M where
  定义体: moduleAux x m
  zero_smul m := by simp only [(· • ·), map_zero, LinearMap.zero_apply]
  smul_zero x := by simp only [(· • ·), map_zero]
  smul_add x m₁ m₂ := by simp only [(· • ·), map_add]
  add_smul x y m := by simp only [(· • ·), map_add, LinearMap.add_apply]
  one_smul m := by
    -- Porting not
-/
protected def module : Module (A otimes[R] B) M where
  smul x m := moduleAux x m
  zero_smul m := by simp only [(· • ·), map_zero, LinearMap.zero_apply]
  smul_zero x := by simp only [(· • ·), map_zero]
  smul_add x m₁ m₂ := by simp only [(· • ·), map_add]
  add_smul x y m := by simp only [(· • ·), map_add, LinearMap.add_apply]
  one_smul m := by
    -- Porting note: was one `simp only`, not two
    simp only [(· • ·), Algebra.TensorProduct.one_def]
    simp only [moduleAux_apply, one_smul]
  mul_smul x y m := by
    refine TensorProduct.induction_on x ?_ ?_ ?_ <;> refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a b
      simp only [(· • ·), zero_mul, map_zero, LinearMap.zero_apply]
    · intro z w _ _
      simp only [(· • ·), zero_mul, map_zero, LinearMap.zero_apply]
    · intro a b
      simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a₁ b₁ a₂ b₂
      -- Porting note: was one `simp only`, not two
      simp only [(· • ·), Algebra.TensorProduct.tmul_mul_tmul]
      simp only [moduleAux_apply, mul_smul, smul_comm a₁ b₂]
    · intro z w hz hw a b
      -- Porting note: was one `simp only`, but random stuff doesn't work
      simp only [(· • ·)] at hz hw ⊢
      simp only [moduleAux_apply, mul_add, map_add,
        LinearMap.add_apply, moduleAux_apply, hz, hw]
    · intro z w _ _
      simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a b z w hz hw
      simp only [(· • ·)] at hz hw ⊢
      simp only [map_add, add_mul, LinearMap.add_apply, hz, hw]
    · intro u v _ _ z w hz hw
      simp only [(· • ·)] at hz hw ⊢
      simp only [add_mul, map_add, LinearMap.add_apply, hz, hw, add_add_add_comm]

attribute [local instance] TensorProduct.Algebra.module

/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: (a : A) (b : B) (m : M)
  statement: a otimesₜ[R] b • m = a • b • m
  proof: rfl

中文:
定理 smul_def
  条件: (a : A) (b : B) (m : M)
  结论: a otimesₜ[R] b • m = a • b • m
  证明: rfl
-/
theorem smul_def (a : A) (b : B) (m : M) : a otimesₜ[R] b • m = a • b • m :=
  rfl

section Lemmas

/--
theorem `linearMap_comp_mul'` / 定理 `linearMap_comp_mul'`

English:
theorem linearMap_comp_mul'
  proof: by
  ext
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars, map_tmul,
    Algebra.linearMap_apply, map_one, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mul'_apply, mul_one, Algebra.TensorProduct.one_def]

中文:
定理 linearMap_comp_mul'
  证明: by
  ext
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars, map_tmul,
    Algebra.linearMap_apply, map_one, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mul'_apply, mul_one, Algebra.TensorProduct.one_def]

Depends on / 依赖: Algebra, Algebra.TensorProduct.one_def, Algebra.linearMap_apply, AlgebraTensorModule, AlgebraTensorModule.curry_apply, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearMap.mul, TensorProduct, _apply, coe_comp, coe_restrictScalars, comp_apply, curry_apply, linearMap_apply, map_one, map_tmul
-/
theorem linearMap_comp_mul' :
    Algebra.linearMap R (A otimes[R] B) ∘ₗ LinearMap.mul' R R =
      map (Algebra.linearMap R A) (Algebra.linearMap R B) := by
  ext
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars, map_tmul,
    Algebra.linearMap_apply, map_one, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mul'_apply, mul_one, Algebra.TensorProduct.one_def]

end Lemmas

end TensorProduct.Algebra

open LinearMap in
/--
lemma `Submodule.map_range_rTensor_subtype_lid` / 引理 `Submodule.map_range_rTensor_subtype_lid`

English:
lemma Submodule.map_range_rTensor_subtype_lid
  statement: {R Q} [CommSemiring R] [AddCommMonoid Q]
  proof: by
  rw [← map_top]; rw [← Submodule.map_comp]; rw [map_top]
  refine le_antisymm ?_ fun q h => Submodule.smul_induction_on h
    (fun r hr q _ => ⟨⟨r, hr⟩ otimesₜ q, by simp⟩) (by simp +contextual [add_mem])
  rintro _ ⟨t, rfl⟩
  exact t.induction_on (by simp) (by simp +contextual [Submodule.smul_m

中文:
引理 Submodule.map_range_rTensor_subtype_lid
  结论: {R Q} [CommSemiring R] [AddCommMonoid Q]
  证明: by
  rw [← map_top]; rw [← Submodule.map_comp]; rw [map_top]
  refine le_antisymm ?_ fun q h => Submodule.smul_induction_on h
    (fun r hr q _ => ⟨⟨r, hr⟩ otimesₜ q, by simp⟩) (by simp +contextual [add_mem])
  rintro _ ⟨t, rfl⟩
  exact t.induction_on (by simp) (by simp +contextual [Submodule.smul_m

Depends on / 依赖: Submodule, Submodule.map_comp, Submodule.smul_induction_on, Submodule.smul_mem_smul, add_mem, contextual, induction_on, le_antisymm, map_comp, map_top, smul_induction_on, smul_mem_smul, t.induction_on
-/
lemma Submodule.map_range_rTensor_subtype_lid {R Q} [CommSemiring R] [AddCommMonoid Q]
    [Module R Q] {I : Submodule R R} :
    (range <| rTensor Q I.subtype).map (TensorProduct.lid R Q : R otimes[R] Q ->ₗ[R] Q) = I • ⊤ := by
  rw [← map_top]; rw [← Submodule.map_comp]; rw [map_top]
  refine le_antisymm ?_ fun q h => Submodule.smul_induction_on h
    (fun r hr q _ => ⟨⟨r, hr⟩ otimesₜ q, by simp⟩) (by simp +contextual [add_mem])
  rintro _ ⟨t, rfl⟩
  exact t.induction_on (by simp) (by simp +contextual [Submodule.smul_mem_smul])
    (by simp +contextual [add_mem])

section

variable {R M S T : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [Semiring S] [Algebra R S] [Ring T] [Algebra R T]

variable (R S M) in
/--
theorem `TensorProduct.mk_surjective` / 定理 `TensorProduct.mk_surjective`

English:
theorem TensorProduct.mk_surjective
  given: (h : Function.Surjective (algebraMap R S))
  proof: by
  rw [← LinearMap.range_eq_top]; rw [← top_le_iff]; rw [← span_tmul_eq_top]; rw [Submodule.span_le]
  rintro _ ⟨x, y, rfl⟩
  obtain ⟨x, rfl⟩ := h x
  rw [Algebra.algebraMap_eq_smul_one]; rw [smul_tmul]
  exact ⟨x • y, rfl⟩

中文:
定理 TensorProduct.mk_surjective
  条件: (h : Function.Surjective (algebraMap R S))
  证明: by
  rw [← LinearMap.range_eq_top]; rw [← top_le_iff]; rw [← span_tmul_eq_top]; rw [Submodule.span_le]
  rintro _ ⟨x, y, rfl⟩
  obtain ⟨x, rfl⟩ := h x
  rw [Algebra.algebraMap_eq_smul_one]; rw [smul_tmul]
  exact ⟨x • y, rfl⟩

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, LinearMap, LinearMap.range_eq_top, Submodule, Submodule.span_le, algebraMap_eq_smul_one, range_eq_top, smul_tmul, span_le, span_tmul_eq_top, top_le_iff
-/
theorem TensorProduct.mk_surjective (h : Function.Surjective (algebraMap R S)) :
    Function.Surjective (TensorProduct.mk R S M 1) := by
  rw [← LinearMap.range_eq_top]; rw [← top_le_iff]; rw [← span_tmul_eq_top]; rw [Submodule.span_le]
  rintro _ ⟨x, y, rfl⟩
  obtain ⟨x, rfl⟩ := h x
  rw [Algebra.algebraMap_eq_smul_one]; rw [smul_tmul]
  exact ⟨x • y, rfl⟩

variable (S) in
/--
lemma `TensorProduct.flip_mk_surjective` / 引理 `TensorProduct.flip_mk_surjective`

English:
lemma TensorProduct.flip_mk_surjective
  given: (h : Function.Surjective (algebraMap R T))
  proof: by
  rw [← LinearMap.range_eq_top]; rw [← top_le_iff]; rw [← span_tmul_eq_top]; rw [Submodule.span_le]
  rintro _ ⟨s, t, rfl⟩
  obtain ⟨r, rfl⟩ := h t
  rw [Algebra.algebraMap_eq_smul_one]; rw [← smul_tmul]
  exact ⟨r • s, rfl⟩

中文:
引理 TensorProduct.flip_mk_surjective
  条件: (h : Function.Surjective (algebraMap R T))
  证明: by
  rw [← LinearMap.range_eq_top]; rw [← top_le_iff]; rw [← span_tmul_eq_top]; rw [Submodule.span_le]
  rintro _ ⟨s, t, rfl⟩
  obtain ⟨r, rfl⟩ := h t
  rw [Algebra.algebraMap_eq_smul_one]; rw [← smul_tmul]
  exact ⟨r • s, rfl⟩

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, LinearMap, LinearMap.range_eq_top, Submodule, Submodule.span_le, algebraMap_eq_smul_one, range_eq_top, smul_tmul, span_le, span_tmul_eq_top, top_le_iff
-/
lemma TensorProduct.flip_mk_surjective (h : Function.Surjective (algebraMap R T)) :
    Function.Surjective ((TensorProduct.mk R S T).flip 1) := by
  rw [← LinearMap.range_eq_top]; rw [← top_le_iff]; rw [← span_tmul_eq_top]; rw [Submodule.span_le]
  rintro _ ⟨s, t, rfl⟩
  obtain ⟨r, rfl⟩ := h t
  rw [Algebra.algebraMap_eq_smul_one]; rw [← smul_tmul]
  exact ⟨r • s, rfl⟩

variable (T) in
/--
lemma `Algebra.TensorProduct.includeRight_surjective` / 引理 `Algebra.TensorProduct.includeRight_surjective`

English:
lemma Algebra.TensorProduct.includeRight_surjective
  given: (h : Function.Surjective (algebraMap R S))
  proof: TensorProduct.mk_surjective _ _ _ h

中文:
引理 Algebra.TensorProduct.includeRight_surjective
  条件: (h : Function.Surjective (algebraMap R S))
  证明: TensorProduct.mk_surjective _ _ _ h

Depends on / 依赖: TensorProduct, TensorProduct.mk_surjective, mk_surjective
-/
lemma Algebra.TensorProduct.includeRight_surjective (h : Function.Surjective (algebraMap R S)) :
    Function.Surjective (includeRight : T ->ₐ[R] S otimes[R] T) :=
  TensorProduct.mk_surjective _ _ _ h

/--
lemma `Algebra.TensorProduct.includeLeft_surjective` / 引理 `Algebra.TensorProduct.includeLeft_surjective`

English:
lemma Algebra.TensorProduct.includeLeft_surjective
  proof: TensorProduct.flip_mk_surjective _ h

中文:
引理 Algebra.TensorProduct.includeLeft_surjective
  证明: TensorProduct.flip_mk_surjective _ h

Depends on / 依赖: TensorProduct, TensorProduct.flip_mk_surjective, flip_mk_surjective
-/
lemma Algebra.TensorProduct.includeLeft_surjective
    (S A : Type*) [CommSemiring S] [Semiring A] [Algebra S A] [Algebra R A]
    [SMulCommClass R S A] (h : Function.Surjective (algebraMap R T)) :
    Function.Surjective (includeLeft : A ->ₐ[S] A otimes[R] T) :=
  TensorProduct.flip_mk_surjective _ h

end

variable {R A B : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A]
  [NonUnitalNonAssocSemiring B] [Module R A] [Module R B] [SMulCommClass R A A]
  [SMulCommClass R B B] [IsScalarTower R A A] [IsScalarTower R B B]

@[simp]
/--
theorem `TensorProduct.Algebra.mul'_comp_tensorTensorTensorComm` / 定理 `TensorProduct.Algebra.mul'_comp_tensorTensorTensorComm`

English:
theorem TensorProduct.Algebra.mul'_comp_tensorTensorTensorComm
  proof: by
  ext
  simp

中文:
定理 TensorProduct.Algebra.mul'_comp_tensorTensorTensorComm
  证明: by
  ext
  simp
-/
theorem TensorProduct.Algebra.mul'_comp_tensorTensorTensorComm :
    LinearMap.mul' R (A otimes[R] B) ∘ₗ tensorTensorTensorComm R A A B B =
      map (LinearMap.mul' R A) (LinearMap.mul' R B) := by
  ext
  simp

/--
lemma `LinearMap.mul'_tensor` / 引理 `LinearMap.mul'_tensor`

English:
lemma LinearMap.mul'_tensor
  proof: ext_fourfold' by simp

中文:
引理 LinearMap.mul'_tensor
  证明: ext_fourfold' by simp
-/
lemma LinearMap.mul'_tensor :
    mul' R (A otimes[R] B) = map (mul' R A) (mul' R B) ∘ₗ tensorTensorTensorComm R A B A B :=
ext_fourfold' by simp

/--
lemma `LinearMap.mulLeft_tmul` / 引理 `LinearMap.mulLeft_tmul`

English:
lemma LinearMap.mulLeft_tmul
  given: (a : A) (b : B)
  proof: by
  ext; simp

中文:
引理 LinearMap.mulLeft_tmul
  条件: (a : A) (b : B)
  证明: by
  ext; simp
-/
lemma LinearMap.mulLeft_tmul (a : A) (b : B) :
    mulLeft R (a otimesₜ[R] b) = map (mulLeft R a) (mulLeft R b) := by
  ext; simp

/--
lemma `LinearMap.mulRight_tmul` / 引理 `LinearMap.mulRight_tmul`

English:
lemma LinearMap.mulRight_tmul
  given: (a : A) (b : B)
  proof: by
  ext; simp

中文:
引理 LinearMap.mulRight_tmul
  条件: (a : A) (b : B)
  证明: by
  ext; simp
-/
lemma LinearMap.mulRight_tmul (a : A) (b : B) :
    mulRight R (a otimesₜ[R] b) = map (mulRight R a) (mulRight R b) := by
  ext; simp

namespace TensorProduct
variable [StarRing R] [StarRing A] [StarRing B] [StarModule R A] [StarModule R B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarMul (A otimes[R] B)
  body: x.induction_on (by simp) (fun _ _ =>
      y.induction_on (by simp)
        fun _ _ => by simp
      fun _ _ h₁ h₂ => by simp [add_mul, mul_add, h₁, h₂])
    fun _ _ h₁ h₂ => by simp [add_mul, mul_add, h₁, h₂]

中文:
实例 :
  签名: StarMul (A otimes[R] B)
  定义体: x.induction_on (by simp) (fun _ _ =>
      y.induction_on (by simp)
        fun _ _ => by simp
      fun _ _ h₁ h₂ => by simp [add_mul, mul_add, h₁, h₂])
    fun _ _ h₁ h₂ => by simp [add_mul, mul_add, h₁, h₂]

Depends on / 依赖: add_mul, induction_on, mul_add, x.induction_on, y.induction_on
-/
noncomputable instance : StarMul (A otimes[R] B) where
  star_mul x y :=
    x.induction_on (by simp) (fun _ _ =>
      y.induction_on (by simp)
        fun _ _ => by simp
      fun _ _ h₁ h₂ => by simp [add_mul, mul_add, h₁, h₂])
    fun _ _ h₁ h₂ => by simp [add_mul, mul_add, h₁, h₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarRing (A otimes[R] B)
  body: by simp

中文:
实例 :
  签名: StarRing (A otimes[R] B)
  定义体: by simp
-/
noncomputable instance : StarRing (A otimes[R] B) where
  star_add := by simp

end TensorProduct

namespace AlgHom

variable (R S A B : Type*)
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
variable [Algebra R S] [Algebra R B] [IsScalarTower R S B]

/--
Definition of `liftEquiv` / `liftEquiv` 的定义

English:
definition liftEquiv
  signature: : (A ->ₐ[R] B) ≃ (S otimes[R] A ->ₐ[S] B) where
  body: .ofLinearMap (.liftBaseChange S f) (by simp [Algebra.TensorProduct.one_def]) fun x y => by
      rw [← LinearMap.mul_apply_apply S]; rw [← LinearMap.compr₂_apply]; rw [← LinearMap.mul_apply_apply S]; rw [← LinearMap.compl₁₂_apply]
      congr; ext; simp
.comp Algebra.TensorProduct.includeRight invFu

中文:
定义 liftEquiv
  签名: : (A ->ₐ[R] B) ≃ (S otimes[R] A ->ₐ[S] B) where
  定义体: .ofLinearMap (.liftBaseChange S f) (by simp [Algebra.TensorProduct.one_def]) fun x y => by
      rw [← LinearMap.mul_apply_apply S]; rw [← LinearMap.compr₂_apply]; rw [← LinearMap.mul_apply_apply S]; rw [← LinearMap.compl₁₂_apply]
      congr; ext; simp
.comp Algebra.TensorProduct.includeRight invFu

Depends on / 依赖: Algebra, Algebra.TensorProduct.ext, Algebra.TensorProduct.includeRight, Algebra.TensorProduct.one_def, LinearMap, LinearMap.compl, LinearMap.compr, LinearMap.mul_apply_apply, Subsingleton, Subsingleton.elim, TensorProduct, f.restrictScalars, includeRight, invFun, left_inv, liftBaseChange, mul_apply_apply, ofLinearMap, one_def, restrictScalars
-/
def liftEquiv : (A ->ₐ[R] B) ≃ (S otimes[R] A ->ₐ[S] B) where
  toFun f :=
    .ofLinearMap (.liftBaseChange S f) (by simp [Algebra.TensorProduct.one_def]) fun x y => by
      rw [← LinearMap.mul_apply_apply S]; rw [← LinearMap.compr₂_apply]; rw [← LinearMap.mul_apply_apply S]; rw [← LinearMap.compl₁₂_apply]
      congr; ext; simp
.comp Algebra.TensorProduct.includeRight invFun f := f.restrictScalars R
  left_inv f := by ext; simp
right_inv f := Algebra.TensorProduct.ext (Subsingleton.elim _ _) by ext; simp

variable {R S A B}

/--
lemma `liftEquiv_tmul` / 引理 `liftEquiv_tmul`

English:
lemma liftEquiv_tmul
  given: (f : A ->ₐ[R] B) (s : S) (a : A)
  proof: rfl

中文:
引理 liftEquiv_tmul
  条件: (f : A ->ₐ[R] B) (s : S) (a : A)
  证明: rfl
-/
@[simp] lemma liftEquiv_tmul (f : A ->ₐ[R] B) (s : S) (a : A) :
    f.liftEquiv R S A B (s otimesₜ a) = s • f a := rfl

/--
lemma `liftEquiv_symm_apply` / 引理 `liftEquiv_symm_apply`

English:
lemma liftEquiv_symm_apply
  given: (f : S otimes[R] A ->ₐ[S] B) (a : A)
  proof: rfl

@[ext high + 1]

中文:
引理 liftEquiv_symm_apply
  条件: (f : S otimes[R] A ->ₐ[S] B) (a : A)
  证明: rfl

@[ext high + 1]
-/
@[simp] lemma liftEquiv_symm_apply (f : S otimes[R] A ->ₐ[S] B) (a : A) :
    (liftEquiv ..).symm f a = f (1 otimesₜ[R] a) := rfl

@[ext high + 1]
/--
lemma `_root_.Algebra.TensorProduct.ext_ring` / 引理 `_root_.Algebra.TensorProduct.ext_ring`

English:
lemma _root_.Algebra.TensorProduct.ext_ring
  statement: {f g : S otimes[R] A ->ₐ[S] B}
  proof: .symm.injective h liftEquiv ..

中文:
引理 _root_.Algebra.TensorProduct.ext_ring
  结论: {f g : S otimes[R] A ->ₐ[S] B}
  证明: .symm.injective h liftEquiv ..

Depends on / 依赖: injective, liftEquiv, symm.injective
-/
lemma _root_.Algebra.TensorProduct.ext_ring {f g : S otimes[R] A ->ₐ[S] B}
    (h : (AlgHom.restrictScalars R f).comp Algebra.TensorProduct.includeRight =
      (AlgHom.restrictScalars R g).comp Algebra.TensorProduct.includeRight) :
    f = g :=
.symm.injective h liftEquiv ..

end AlgHom
