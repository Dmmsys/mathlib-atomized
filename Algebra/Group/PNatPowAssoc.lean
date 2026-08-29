/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Algebra.Notation.Prod

/-!
# Typeclasses for power-associative structures

In this file we define power-associativity for algebraic structures with a multiplication operation.
The class is a Prop-valued mixin named `PNatPowAssoc`, where `PNat` means only strictly positive
powers are considered.

## Results

- `ppow_add` a defining property: `x ^ (k + n) = x ^ k * x ^ n`
- `ppow_one` a defining property: `x ^ 1 = x`
- `ppow_assoc` strictly positive powers of an element have associative multiplication.
- `ppow_comm` `x ^ m * x ^ n = x ^ n * x ^ m` for strictly positive `m` and `n`.
- `ppow_mul` `x ^ (m * n) = (x ^ m) ^ n` for strictly positive `m` and `n`.
- `ppow_eq_pow` monoid exponentiation coincides with semigroup exponentiation.

## Instances

- PNatPowAssoc for products and Pi types

## TODO

* `NatPowAssoc` for `MulOneClass` - more or less the same flow
* It seems unlikely that anyone will want `NatSMulAssoc` and `PNatSMulAssoc` as additive versions of
  power-associativity, but we have found that it is not hard to write.

-/

public section

-- TODO:
-- assert_not_exists MonoidWithZero

variable {M : Type*}

/--
Definition of `PNatPowAssoc` / `PNatPowAssoc` 的定义

English:
class PNatPowAssoc
  parameters: (M : Type*) [Mul M] [Pow M Nat+]
  axioms and operations (2):
    - ppow_add : forall (k n : Nat+) (x : M), x ^ (k + n) = x ^ k * x ^ n
    - ppow_one : forall (x : M), x ^ (1 : Nat+) = x

中文:
类 PNatPowAssoc
  参数: (M : 类型) [Mul M] [Pow M 自然数+]
  公理与运算 (2 个):
    - ppow_add : 对任意 (k n : 自然数+) (x : M), x ^ (k + n) = x ^ k * x ^ n
    - ppow_one : 对任意 (x : M), x ^ (1 : 自然数+) = x
-/
class PNatPowAssoc (M : Type*) [Mul M] [Pow M Nat+] : Prop where
  /-- Multiplication is power-associative. -/
  protected ppow_add : forall (k n : Nat+) (x : M), x ^ (k + n) = x ^ k * x ^ n
  /-- Exponent one is identity. -/
  protected ppow_one : forall (x : M), x ^ (1 : Nat+) = x

section Mul

variable [Mul M] [Pow M Nat+] [PNatPowAssoc M]

/--
theorem `ppow_add` / 定理 `ppow_add`

English:
theorem ppow_add
  given: (k n : Nat+) (x : M)
  statement: x ^ (k + n) = x ^ k * x ^ n
  proof: PNatPowAssoc.ppow_add k n x

@[simp]

中文:
定理 ppow_add
  条件: (k n : 自然数+) (x : M)
  结论: x ^ (k + n) = x ^ k * x ^ n
  证明: PNatPowAssoc.ppow_add k n x

@[simp]

Depends on / 依赖: PNatPowAssoc, PNatPowAssoc.ppow_add, ppow_add
-/
theorem ppow_add (k n : Nat+) (x : M) : x ^ (k + n) = x ^ k * x ^ n :=
  PNatPowAssoc.ppow_add k n x

@[simp]
/--
theorem `ppow_one` / 定理 `ppow_one`

English:
theorem ppow_one
  given: (x : M)
  statement: x ^ (1 : Nat+) = x
  proof: PNatPowAssoc.ppow_one x

中文:
定理 ppow_one
  条件: (x : M)
  结论: x ^ (1 : 自然数+) = x
  证明: PNatPowAssoc.ppow_one x

Depends on / 依赖: PNatPowAssoc, PNatPowAssoc.ppow_one, ppow_one
-/
theorem ppow_one (x : M) : x ^ (1 : Nat+) = x :=
  PNatPowAssoc.ppow_one x

/--
theorem `ppow_mul_assoc` / 定理 `ppow_mul_assoc`

English:
theorem ppow_mul_assoc
  given: (k m n : Nat+) (x : M)
  proof: by
  simp only [← ppow_add, add_assoc]

中文:
定理 ppow_mul_assoc
  条件: (k m n : 自然数+) (x : M)
  证明: by
  simp only [← ppow_add, add_assoc]

Depends on / 依赖: add_assoc, ppow_add
-/
theorem ppow_mul_assoc (k m n : Nat+) (x : M) :
    (x ^ k * x ^ m) * x ^ n = x ^ k * (x ^ m * x ^ n) := by
  simp only [← ppow_add, add_assoc]

/--
theorem `ppow_mul_comm` / 定理 `ppow_mul_comm`

English:
theorem ppow_mul_comm
  given: (m n : Nat+) (x : M)
  proof: by simp only [← ppow_add, add_comm]

中文:
定理 ppow_mul_comm
  条件: (m n : 自然数+) (x : M)
  证明: by simp only [← ppow_add, add_comm]

Depends on / 依赖: add_comm, ppow_add
-/
theorem ppow_mul_comm (m n : Nat+) (x : M) :
    x ^ m * x ^ n = x ^ n * x ^ m := by simp only [← ppow_add, add_comm]

/--
theorem `ppow_mul` / 定理 `ppow_mul`

English:
theorem ppow_mul
  given: (x : M) (m n : Nat+)
  statement: x ^ (m * n) = (x ^ m) ^ n
  proof: by
  induction n with
  | one => rw [ppow_one, mul_one]
  | succ k hk => rw [ppow_add, ppow_one, mul_add, ppow_add, mul_one, hk]

中文:
定理 ppow_mul
  条件: (x : M) (m n : 自然数+)
  结论: x ^ (m * n) = (x ^ m) ^ n
  证明: by
  induction n with
  | one => rw [ppow_one, mul_one]
  | succ k hk => rw [ppow_add, ppow_one, mul_add, ppow_add, mul_one, hk]

Depends on / 依赖: mul_add, mul_one, ppow_add, ppow_one
-/
theorem ppow_mul (x : M) (m n : Nat+) : x ^ (m * n) = (x ^ m) ^ n := by
  induction n with
  | one => rw [ppow_one, mul_one]
  | succ k hk => rw [ppow_add, ppow_one, mul_add, ppow_add, mul_one, hk]

/--
theorem `ppow_mul'` / 定理 `ppow_mul'`

English:
theorem ppow_mul'
  given: (x : M) (m n : Nat+)
  statement: x ^ (m * n) = (x ^ n) ^ m
  proof: by
  rw [mul_comm]
  exact ppow_mul x n m

中文:
定理 ppow_mul'
  条件: (x : M) (m n : 自然数+)
  结论: x ^ (m * n) = (x ^ n) ^ m
  证明: by
  rw [mul_comm]
  exact ppow_mul x n m

Depends on / 依赖: mul_comm, ppow_mul
-/
theorem ppow_mul' (x : M) (m n : Nat+) : x ^ (m * n) = (x ^ n) ^ m := by
  rw [mul_comm]
  exact ppow_mul x n m

end Mul

/--
Instance `Pi.instPNatPowAssoc` / 实例 `Pi.instPNatPowAssoc`

English:
instance Pi.instPNatPowAssoc
  signature: {ι : Type*} {α : ι -> Type*} [forall i, Mul <| α i] [forall i, Pow (α i) Nat+]
  body: by ext; simp [ppow_add]
  ppow_one _ := by ext; simp

中文:
实例 Pi.instPNatPowAssoc
  签名: {ι : 类型} {α : ι -> 类型} [对任意 i, Mul <| α i] [对任意 i, Pow (α i) 自然数+]
  定义体: by ext; simp [ppow_add]
  ppow_one _ := by ext; simp

Depends on / 依赖: ppow_add, ppow_one
-/
instance Pi.instPNatPowAssoc {ι : Type*} {α : ι -> Type*} [forall i, Mul <| α i] [forall i, Pow (α i) Nat+]
    [forall i, PNatPowAssoc <| α i] : PNatPowAssoc (forall i, α i) where
  ppow_add _ _ _ := by ext; simp [ppow_add]
  ppow_one _ := by ext; simp

/--
Instance `Prod.instPNatPowAssoc` / 实例 `Prod.instPNatPowAssoc`

English:
instance Prod.instPNatPowAssoc
  signature: {N : Type*} [Mul M] [Pow M Nat+] [PNatPowAssoc M] [Mul N] [Pow N Nat+]
  body: by ext <;> simp [ppow_add]
  ppow_one _ := by ext <;> simp

中文:
实例 Prod.instPNatPowAssoc
  签名: {N : 类型} [Mul M] [Pow M 自然数+] [P自然数PowAssoc M] [Mul N] [Pow N 自然数+]
  定义体: by ext <;> simp [ppow_add]
  ppow_one _ := by ext <;> simp

Depends on / 依赖: ppow_add, ppow_one
-/
instance Prod.instPNatPowAssoc {N : Type*} [Mul M] [Pow M Nat+] [PNatPowAssoc M] [Mul N] [Pow N Nat+]
    [PNatPowAssoc N] : PNatPowAssoc (M × N) where
  ppow_add _ _ _ := by ext <;> simp [ppow_add]
  ppow_one _ := by ext <;> simp

/--
theorem `ppow_eq_pow` / 定理 `ppow_eq_pow`

English:
theorem ppow_eq_pow
  given: [Monoid M] [Pow M Nat+] [PNatPowAssoc M] (x : M) (n : Nat+)
  proof: by
  induction n with
  | one => rw [ppow_one, PNat.one_coe, pow_one]
  | succ k hk => rw [ppow_add, ppow_one, PNat.add_coe, pow_add, PNat.one_coe, pow_one, ← hk]

中文:
定理 ppow_eq_pow
  条件: [Monoid M] [Pow M 自然数+] [P自然数PowAssoc M] (x : M) (n : 自然数+)
  证明: by
  induction n with
  | one => rw [ppow_one, PNat.one_coe, pow_one]
  | succ k hk => rw [ppow_add, ppow_one, PNat.add_coe, pow_add, PNat.one_coe, pow_one, ← hk]

Depends on / 依赖: PNat.add_coe, PNat.one_coe, add_coe, one_coe, pow_add, pow_one, ppow_add, ppow_one
-/
theorem ppow_eq_pow [Monoid M] [Pow M Nat+] [PNatPowAssoc M] (x : M) (n : Nat+) :
    x ^ n = x ^ (n : Nat) := by
  induction n with
  | one => rw [ppow_one, PNat.one_coe, pow_one]
  | succ k hk => rw [ppow_add, ppow_one, PNat.add_coe, pow_add, PNat.one_coe, pow_one, ← hk]
