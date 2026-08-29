/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Nat.Cast.Basic

/-!
# Typeclasses for power-associative structures

In this file we define power-associativity for algebraic structures with a multiplication operation.
The class is a Prop-valued mixin named `NatPowAssoc`.

## Results

- `npow_add` a defining property: `x ^ (k + n) = x ^ k * x ^ n`
- `npow_one` a defining property: `x ^ 1 = x`
- `npow_assoc` strictly positive powers of an element have associative multiplication.
- `npow_comm` `x ^ m * x ^ n = x ^ n * x ^ m` for strictly positive `m` and `n`.
- `npow_mul` `x ^ (m * n) = (x ^ m) ^ n` for strictly positive `m` and `n`.
- `npow_eq_pow` monoid exponentiation coincides with semigroup exponentiation.

## Instances

We also produce the following instances:

- `NatPowAssoc` for Monoids, Pi types and products.

## TODO

* `to_additive`?

-/

public section

assert_not_exists DenselyOrdered

variable {M : Type*}

/--
Definition of `NatPowAssoc` / `NatPowAssoc` 的定义

English:
class NatPowAssoc
  parameters: (M : Type*) [MulOneClass M] [Pow M Nat]
  axioms and operations (3):
    - npow_add : forall (k n : Nat) (x : M), x ^ (k + n) = x ^ k * x ^ n
    - npow_zero : forall (x : M), x ^ 0 = 1
    - npow_one : forall (x : M), x ^ 1 = x

中文:
类 NatPowAssoc
  参数: (M : 类型) [MulOneClass M] [Pow M 自然数]
  公理与运算 (3 个):
    - npow_add : 对任意 (k n : 自然数) (x : M), x ^ (k + n) = x ^ k * x ^ n
    - npow_zero : 对任意 (x : M), x ^ 0 = 1
    - npow_one : 对任意 (x : M), x ^ 1 = x
-/
class NatPowAssoc (M : Type*) [MulOneClass M] [Pow M Nat] : Prop where
  /-- Multiplication is power-associative. -/
  protected npow_add : forall (k n : Nat) (x : M), x ^ (k + n) = x ^ k * x ^ n
  /-- Exponent zero is one. -/
  protected npow_zero : forall (x : M), x ^ 0 = 1
  /-- Exponent one is identity. -/
  protected npow_one : forall (x : M), x ^ 1 = x

section MulOneClass

variable [MulOneClass M] [Pow M Nat] [NatPowAssoc M]

/--
theorem `npow_add` / 定理 `npow_add`

English:
theorem npow_add
  given: (k n : Nat) (x : M)
  statement: x ^ (k + n) = x ^ k * x ^ n
  proof: NatPowAssoc.npow_add k n x

@[simp]

中文:
定理 npow_add
  条件: (k n : 自然数) (x : M)
  结论: x ^ (k + n) = x ^ k * x ^ n
  证明: NatPowAssoc.npow_add k n x

@[simp]

Depends on / 依赖: NatPowAssoc, NatPowAssoc.npow_add, npow_add
-/
theorem npow_add (k n : Nat) (x : M) : x ^ (k + n) = x ^ k * x ^ n :=
  NatPowAssoc.npow_add k n x

@[simp]
/--
theorem `npow_zero` / 定理 `npow_zero`

English:
theorem npow_zero
  given: (x : M)
  statement: x ^ 0 = 1
  proof: NatPowAssoc.npow_zero x

@[simp]

中文:
定理 npow_zero
  条件: (x : M)
  结论: x ^ 0 = 1
  证明: NatPowAssoc.npow_zero x

@[simp]

Depends on / 依赖: NatPowAssoc, NatPowAssoc.npow_zero, npow_zero
-/
theorem npow_zero (x : M) : x ^ 0 = 1 :=
  NatPowAssoc.npow_zero x

@[simp]
/--
theorem `npow_one` / 定理 `npow_one`

English:
theorem npow_one
  given: (x : M)
  statement: x ^ 1 = x
  proof: NatPowAssoc.npow_one x

中文:
定理 npow_one
  条件: (x : M)
  结论: x ^ 1 = x
  证明: NatPowAssoc.npow_one x

Depends on / 依赖: NatPowAssoc, NatPowAssoc.npow_one, npow_one
-/
theorem npow_one (x : M) : x ^ 1 = x :=
  NatPowAssoc.npow_one x

/--
theorem `npow_mul_assoc` / 定理 `npow_mul_assoc`

English:
theorem npow_mul_assoc
  given: (k m n : Nat) (x : M)
  proof: by
  simp only [← npow_add, add_assoc]

中文:
定理 npow_mul_assoc
  条件: (k m n : 自然数) (x : M)
  证明: by
  simp only [← npow_add, add_assoc]

Depends on / 依赖: add_assoc, npow_add
-/
theorem npow_mul_assoc (k m n : Nat) (x : M) :
    (x ^ k * x ^ m) * x ^ n = x ^ k * (x ^ m * x ^ n) := by
  simp only [← npow_add, add_assoc]

/--
theorem `npow_mul_comm` / 定理 `npow_mul_comm`

English:
theorem npow_mul_comm
  given: (m n : Nat) (x : M)
  proof: by simp only [← npow_add, add_comm]

中文:
定理 npow_mul_comm
  条件: (m n : 自然数) (x : M)
  证明: by simp only [← npow_add, add_comm]

Depends on / 依赖: add_comm, npow_add
-/
theorem npow_mul_comm (m n : Nat) (x : M) :
    x ^ m * x ^ n = x ^ n * x ^ m := by simp only [← npow_add, add_comm]

/--
theorem `npow_mul` / 定理 `npow_mul`

English:
theorem npow_mul
  given: (x : M) (m n : Nat)
  statement: x ^ (m * n) = (x ^ m) ^ n
  proof: by
  induction n with
  | zero => rw [npow_zero, mul_zero, npow_zero]
  | succ n ih => rw [mul_add, npow_add, ih, mul_one, npow_add, npow_one]

中文:
定理 npow_mul
  条件: (x : M) (m n : 自然数)
  结论: x ^ (m * n) = (x ^ m) ^ n
  证明: by
  induction n with
  | zero => rw [npow_zero, mul_zero, npow_zero]
  | succ n ih => rw [mul_add, npow_add, ih, mul_one, npow_add, npow_one]

Depends on / 依赖: mul_add, mul_one, mul_zero, npow_add, npow_one, npow_zero
-/
theorem npow_mul (x : M) (m n : Nat) : x ^ (m * n) = (x ^ m) ^ n := by
  induction n with
  | zero => rw [npow_zero, mul_zero, npow_zero]
  | succ n ih => rw [mul_add, npow_add, ih, mul_one, npow_add, npow_one]

/--
theorem `npow_mul'` / 定理 `npow_mul'`

English:
theorem npow_mul'
  given: (x : M) (m n : Nat)
  statement: x ^ (m * n) = (x ^ n) ^ m
  proof: by
  rw [mul_comm]
  exact npow_mul x n m

中文:
定理 npow_mul'
  条件: (x : M) (m n : 自然数)
  结论: x ^ (m * n) = (x ^ n) ^ m
  证明: by
  rw [mul_comm]
  exact npow_mul x n m

Depends on / 依赖: h.subset_singleton_iff, mul_comm, npow_mul, subset_singleton_iff
-/
theorem npow_mul' (x : M) (m n : Nat) : x ^ (m * n) = (x ^ n) ^ m := by
  rw [mul_comm]
  exact npow_mul x n m

end MulOneClass

section Neg

/--
theorem `neg_npow_assoc` / 定理 `neg_npow_assoc`

English:
theorem neg_npow_assoc
  given: {R : Type*} [NonAssocRing R] [Pow R Nat] [NatPowAssoc R] (a b : R) (k : Nat)
  proof: by
  induction k with
  | zero => simp only [npow_zero, one_mul]
  | succ k ih =>
    rw [npow_add]; rw [npow_one]; rw [← neg_mul_comm]; rw [mul_one]
    simp only [neg_mul, ih]

中文:
定理 neg_npow_assoc
  条件: {R : 类型} [NonAssocRing R] [Pow R 自然数] [自然数PowAssoc R] (a b : R) (k : 自然数)
  证明: by
  induction k with
  | zero => simp only [npow_zero, one_mul]
  | succ k ih =>
    rw [npow_add]; rw [npow_one]; rw [← neg_mul_comm]; rw [mul_one]
    simp only [neg_mul, ih]

Depends on / 依赖: mul_one, neg_mul, neg_mul_comm, npow_add, npow_one, npow_zero, one_mul
-/
theorem neg_npow_assoc {R : Type*} [NonAssocRing R] [Pow R Nat] [NatPowAssoc R] (a b : R) (k : Nat) :
    (-1) ^ k * a * b = (-1) ^ k * (a * b) := by
  induction k with
  | zero => simp only [npow_zero, one_mul]
  | succ k ih =>
    rw [npow_add]; rw [npow_one]; rw [← neg_mul_comm]; rw [mul_one]
    simp only [neg_mul, ih]

end Neg

/--
Instance `Pi.instNatPowAssoc` / 实例 `Pi.instNatPowAssoc`

English:
instance Pi.instNatPowAssoc
  signature: {ι : Type*} {α : ι -> Type*} [forall i, MulOneClass <| α i] [forall i, Pow (α i) Nat]
  body: by ext; simp [npow_add]
    npow_zero _ := by ext; simp
    npow_one _ := by ext; simp

中文:
实例 Pi.instNatPowAssoc
  签名: {ι : 类型} {α : ι -> 类型} [对任意 i, MulOneClass <| α i] [对任意 i, Pow (α i) 自然数]
  定义体: by ext; simp [npow_add]
    npow_zero _ := by ext; simp
    npow_one _ := by ext; simp

Depends on / 依赖: npow_add, npow_one, npow_zero
-/
instance Pi.instNatPowAssoc {ι : Type*} {α : ι -> Type*} [forall i, MulOneClass <| α i] [forall i, Pow (α i) Nat]
    [forall i, NatPowAssoc <| α i] : NatPowAssoc (forall i, α i) where
    npow_add _ _ _ := by ext; simp [npow_add]
    npow_zero _ := by ext; simp
    npow_one _ := by ext; simp

/--
Instance `Prod.instNatPowAssoc` / 实例 `Prod.instNatPowAssoc`

English:
instance Prod.instNatPowAssoc
  signature: {N : Type*} [MulOneClass M] [Pow M Nat] [NatPowAssoc M] [MulOneClass N]
  body: by ext <;> simp [npow_add]
  npow_zero _ := by ext <;> simp
  npow_one _ := by ext <;> simp

中文:
实例 Prod.instNatPowAssoc
  签名: {N : 类型} [MulOneClass M] [Pow M 自然数] [自然数PowAssoc M] [MulOneClass N]
  定义体: by ext <;> simp [npow_add]
  npow_zero _ := by ext <;> simp
  npow_one _ := by ext <;> simp

Depends on / 依赖: npow_add, npow_one, npow_zero
-/
instance Prod.instNatPowAssoc {N : Type*} [MulOneClass M] [Pow M Nat] [NatPowAssoc M] [MulOneClass N]
    [Pow N Nat] [NatPowAssoc N] : NatPowAssoc (M × N) where
  npow_add _ _ _ := by ext <;> simp [npow_add]
  npow_zero _ := by ext <;> simp
  npow_one _ := by ext <;> simp

section Monoid

variable [Monoid M]

/--
Instance `Monoid.PowAssoc` / 实例 `Monoid.PowAssoc`

English:
instance Monoid.PowAssoc
  signature: : NatPowAssoc M where
  body: pow_add _ _ _
  npow_zero _ := pow_zero _
  npow_one _ := pow_one _

@[simp, norm_cast]

中文:
实例 Monoid.PowAssoc
  签名: : 自然数PowAssoc M where
  定义体: pow_add _ _ _
  npow_zero _ := pow_zero _
  npow_one _ := pow_one _

@[simp, norm_cast]

Depends on / 依赖: pow_add
-/
instance Monoid.PowAssoc : NatPowAssoc M where
  npow_add _ _ _ := pow_add _ _ _
  npow_zero _ := pow_zero _
  npow_one _ := pow_one _

@[simp, norm_cast]
/--
theorem `Nat.cast_npow` / 定理 `Nat.cast_npow`

English:
theorem Nat.cast_npow
  given: (R : Type*) [NonAssocSemiring R] [Pow R Nat] [NatPowAssoc R] (n m : Nat)
  proof: by
  induction m with
  | zero => simp only [pow_zero, Nat.cast_one, npow_zero]
  | succ m ih => rw [npow_add, npow_add, Nat.cast_mul, ih, npow_one, npow_one]

@[simp, norm_cast]

中文:
定理 Nat.cast_npow
  条件: (R : 类型) [NonAssocSemiring R] [Pow R 自然数] [自然数PowAssoc R] (n m : 自然数)
  证明: by
  induction m with
  | zero => simp only [pow_zero, Nat.cast_one, npow_zero]
  | succ m ih => rw [npow_add, npow_add, Nat.cast_mul, ih, npow_one, npow_one]

@[simp, norm_cast]

Depends on / 依赖: Nat.cast_mul, Nat.cast_one, cast_mul, cast_one, npow_add, npow_one, npow_zero, pow_zero
-/
theorem Nat.cast_npow (R : Type*) [NonAssocSemiring R] [Pow R Nat] [NatPowAssoc R] (n m : Nat) :
    (↑(n ^ m) : R) = (↑n : R) ^ m := by
  induction m with
  | zero => simp only [pow_zero, Nat.cast_one, npow_zero]
  | succ m ih => rw [npow_add, npow_add, Nat.cast_mul, ih, npow_one, npow_one]

@[simp, norm_cast]
/--
theorem `Int.cast_npow` / 定理 `Int.cast_npow`

English:
theorem Int.cast_npow
  statement: (R : Type*) [NonAssocRing R] [Pow R Nat] [NatPowAssoc R]

中文:
定理 Int.cast_npow
  结论: (R : 类型) [NonAssocRing R] [Pow R 自然数] [自然数PowAssoc R]
-/
theorem Int.cast_npow (R : Type*) [NonAssocRing R] [Pow R Nat] [NatPowAssoc R]
    (n : Int) : forall (m : Nat), @Int.cast R NonAssocRing.toIntCast (n ^ m) = (n : R) ^ m
  | 0 => by
    rw [pow_zero]; rw [npow_zero]; rw [Int.cast_one]
  | m + 1 => by
    rw [npow_add]; rw [npow_one]; rw [Int.cast_mul]; rw [Int.cast_npow R n m]; rw [npow_add]; rw [npow_one]

end Monoid
