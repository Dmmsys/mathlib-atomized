/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Algebra.GroupWithZero.NeZero

/-!
# Lifting groups with zero along injective/surjective maps

-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

open Function

variable {M₀ G₀ M₀' G₀' : Type*}

section MulZeroClass

variable [MulZeroClass M₀]

/--
Definition of `Function.Injective.mulZeroClass` / `Function.Injective.mulZeroClass` 的定义

English:
abbreviation Function.Injective.mulZeroClass
  signature: [Mul M₀'] [Zero M₀'] (f : M₀' -> M₀)
  body: hf by simp only [mul, zero, zero_mul]
mul_zero a := hf by simp only [mul, zero, mul_zero]

中文:
缩写 函数.单射.mulZeroClass
  签名: [乘法 M₀'] [零 M₀'] (f : M₀' -> M₀)
  定义体: hf by simp only [mul, zero, zero_mul]
mul_zero a := hf by simp only [mul, zero, mul_zero]
-/
protected abbrev Function.Injective.mulZeroClass [Mul M₀'] [Zero M₀'] (f : M₀' -> M₀)
    (hf : Injective f) (zero : f 0 = 0) (mul : forall a b, f (a * b) = f a * f b) :
    MulZeroClass M₀' where
zero_mul a := hf by simp only [mul, zero, zero_mul]
mul_zero a := hf by simp only [mul, zero, mul_zero]

/--
Definition of `Function.Surjective.mulZeroClass` / `Function.Surjective.mulZeroClass` 的定义

English:
abbreviation Function.Surjective.mulZeroClass
  signature: [Mul M₀'] [Zero M₀'] (f : M₀ -> M₀')
  body: hf.forall.2 fun x => by simp only [← zero, ← mul, mul_zero]
  zero_mul := hf.forall.2 fun x => by simp only [← zero, ← mul, zero_mul]

中文:
缩写 函数.满射.mulZeroClass
  签名: [乘法 M₀'] [零 M₀'] (f : M₀ -> M₀')
  定义体: hf.forall.2 fun x => by simp only [← zero, ← mul, mul_zero]
  zero_mul := hf.forall.2 fun x => by simp only [← zero, ← mul, zero_mul]
-/
protected abbrev Function.Surjective.mulZeroClass [Mul M₀'] [Zero M₀'] (f : M₀ -> M₀')
    (hf : Surjective f) (zero : f 0 = 0) (mul : forall a b, f (a * b) = f a * f b) :
    MulZeroClass M₀' where
  mul_zero := hf.forall.2 fun x => by simp only [← zero, ← mul, mul_zero]
  zero_mul := hf.forall.2 fun x => by simp only [← zero, ← mul, zero_mul]

end MulZeroClass

section NoZeroDivisors

variable [Mul M₀] [Zero M₀] [Mul M₀'] [Zero M₀']
  (f : M₀ -> M₀') (hf : Injective f) (zero : f 0 = 0) (mul : forall x y, f (x * y) = f x * f y)

include hf zero mul

/--
theorem `Function.Injective.noZeroDivisors` / 定理 `Function.Injective.noZeroDivisors`

English:
theorem Function.Injective.noZeroDivisors
  given: [NoZeroDivisors M₀']
  statement: NoZeroDivisors M₀ where
  proof: have : f a * f b = 0 := by rw [← mul, H, zero]
    (eq_zero_or_eq_zero_of_mul_eq_zero this).imp
(fun H => hf <| by rwa [zero]) fun H => hf by rwa [zero]

中文:
定理 函数.单射.noZeroDivisors
  条件: [无零因子 M₀']
  结论: 无零因子 M₀ where
  证明: have : f a * f b = 0 := by rw [← mul, H, zero]
    (eq_zero_or_eq_zero_of_mul_eq_zero this).imp
(fun H => hf <| by rwa [zero]) fun H => hf by rwa [zero]
-/
protected theorem Function.Injective.noZeroDivisors [NoZeroDivisors M₀'] : NoZeroDivisors M₀ where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} H :=
    have : f a * f b = 0 := by rw [← mul, H, zero]
    (eq_zero_or_eq_zero_of_mul_eq_zero this).imp
(fun H => hf <| by rwa [zero]) fun H => hf by rwa [zero]

/--
theorem `Function.Injective.isLeftCancelMulZero` / 定理 `Function.Injective.isLeftCancelMulZero`

English:
theorem Function.Injective.isLeftCancelMulZero
  proof: by
    have := congr_arg f He
    rw [mul]; rw [mul] at this
    exact hf (mul_left_cancel₀ (fun Hfa => Hne <| hf <| by rw [Hfa, zero]) this)

中文:
定理 函数.单射.isLeftCancelMulZero
  证明: by
    have := congr_arg f He
    rw [mul]; rw [mul] at this
    exact hf (mul_left_cancel₀ (fun Hfa => Hne <| hf <| by rw [Hfa, zero]) this)
-/
protected theorem Function.Injective.isLeftCancelMulZero
    [IsLeftCancelMulZero M₀'] : IsLeftCancelMulZero M₀ where
  mul_left_cancel_of_ne_zero Hne _ _ He := by
    have := congr_arg f He
    rw [mul]; rw [mul] at this
    exact hf (mul_left_cancel₀ (fun Hfa => Hne <| hf <| by rw [Hfa, zero]) this)

/--
theorem `Function.Injective.isRightCancelMulZero` / 定理 `Function.Injective.isRightCancelMulZero`

English:
theorem Function.Injective.isRightCancelMulZero
  proof: by
    have := congr_arg f He
    rw [mul]; rw [mul] at this
    exact hf (mul_right_cancel₀ (fun Hfa => Hne <| hf <| by rw [Hfa, zero]) this)

中文:
定理 函数.单射.isRightCancelMulZero
  证明: by
    have := congr_arg f He
    rw [mul]; rw [mul] at this
    exact hf (mul_right_cancel₀ (fun Hfa => Hne <| hf <| by rw [Hfa, zero]) this)
-/
protected theorem Function.Injective.isRightCancelMulZero
    [IsRightCancelMulZero M₀'] : IsRightCancelMulZero M₀ where
  mul_right_cancel_of_ne_zero Hne _ _ He := by
    have := congr_arg f He
    rw [mul]; rw [mul] at this
    exact hf (mul_right_cancel₀ (fun Hfa => Hne <| hf <| by rw [Hfa, zero]) this)

/--
theorem `Function.Injective.isCancelMulZero` / 定理 `Function.Injective.isCancelMulZero`

English:
theorem Function.Injective.isCancelMulZero
  proof: hf.isLeftCancelMulZero f zero mul
  __ := hf.isRightCancelMulZero f zero mul

中文:
定理 函数.单射.isCancelMulZero
  证明: hf.isLeftCancelMulZero f zero mul
  __ := hf.isRightCancelMulZero f zero mul
-/
protected theorem Function.Injective.isCancelMulZero
    [IsCancelMulZero M₀'] : IsCancelMulZero M₀ where
  __ := hf.isLeftCancelMulZero f zero mul
  __ := hf.isRightCancelMulZero f zero mul

end NoZeroDivisors

section MulZeroOneClass

variable [MulZeroOneClass M₀]

/--
Definition of `Function.Injective.mulZeroOneClass` / `Function.Injective.mulZeroOneClass` 的定义

English:
abbreviation Function.Injective.mulZeroOneClass
  signature: [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀' -> M₀)
  body: { hf.mulZeroClass f zero mul, hf.mulOneClass f one mul with }

中文:
缩写 函数.单射.mulZeroOneClass
  签名: [乘法 M₀'] [零 M₀'] [幺 M₀'] (f : M₀' -> M₀)
  定义体: { hf.mulZeroClass f zero mul, hf.mulOneClass f one mul with }
-/
protected abbrev Function.Injective.mulZeroOneClass [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀' -> M₀)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : forall a b, f (a * b) = f a * f b) :
    MulZeroOneClass M₀' :=
  { hf.mulZeroClass f zero mul, hf.mulOneClass f one mul with }

/--
Definition of `Function.Surjective.mulZeroOneClass` / `Function.Surjective.mulZeroOneClass` 的定义

English:
abbreviation Function.Surjective.mulZeroOneClass
  signature: [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀ -> M₀')
  body: { hf.mulZeroClass f zero mul, hf.mulOneClass f one mul with }

中文:
缩写 函数.满射.mulZeroOneClass
  签名: [乘法 M₀'] [零 M₀'] [幺 M₀'] (f : M₀ -> M₀')
  定义体: { hf.mulZeroClass f zero mul, hf.mulOneClass f one mul with }
-/
protected abbrev Function.Surjective.mulZeroOneClass [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀ -> M₀')
    (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : forall a b, f (a * b) = f a * f b) :
    MulZeroOneClass M₀' :=
  { hf.mulZeroClass f zero mul, hf.mulOneClass f one mul with }

end MulZeroOneClass

section SemigroupWithZero

/--
Definition of `Function.Injective.semigroupWithZero` / `Function.Injective.semigroupWithZero` 的定义

English:
abbreviation Function.Injective.semigroupWithZero
  signature: [Zero M₀'] [Mul M₀'] [SemigroupWithZero M₀]
  body: { hf.mulZeroClass f zero mul, ‹Zero M₀'›, hf.semigroup f mul with }

中文:
缩写 函数.单射.semigroupWithZero
  签名: [零 M₀'] [乘法 M₀'] [带零半群 M₀]
  定义体: { hf.mulZeroClass f zero mul, ‹Zero M₀'›, hf.semigroup f mul with }
-/
protected abbrev Function.Injective.semigroupWithZero [Zero M₀'] [Mul M₀'] [SemigroupWithZero M₀]
    (f : M₀' -> M₀) (hf : Injective f) (zero : f 0 = 0) (mul : forall x y, f (x * y) = f x * f y) :
    SemigroupWithZero M₀' :=
  { hf.mulZeroClass f zero mul, ‹Zero M₀'›, hf.semigroup f mul with }

/--
Definition of `Function.Surjective.semigroupWithZero` / `Function.Surjective.semigroupWithZero` 的定义

English:
abbreviation Function.Surjective.semigroupWithZero
  signature: [SemigroupWithZero M₀] [Zero M₀'] [Mul M₀']
  body: { hf.mulZeroClass f zero mul, ‹Zero M₀'›, hf.semigroup f mul with }

中文:
缩写 函数.满射.semigroupWithZero
  签名: [带零半群 M₀] [零 M₀'] [乘法 M₀']
  定义体: { hf.mulZeroClass f zero mul, ‹Zero M₀'›, hf.semigroup f mul with }
-/
protected abbrev Function.Surjective.semigroupWithZero [SemigroupWithZero M₀] [Zero M₀'] [Mul M₀']
    (f : M₀ -> M₀') (hf : Surjective f) (zero : f 0 = 0) (mul : forall x y, f (x * y) = f x * f y) :
    SemigroupWithZero M₀' :=
  { hf.mulZeroClass f zero mul, ‹Zero M₀'›, hf.semigroup f mul with }

end SemigroupWithZero

section MonoidWithZero

/--
Definition of `Function.Injective.monoidWithZero` / `Function.Injective.monoidWithZero` 的定义

English:
abbreviation Function.Injective.monoidWithZero
  signature: [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' Nat]
  body: { hf.monoid f one mul npow, hf.mulZeroClass f zero mul with }

中文:
缩写 函数.单射.monoidWithZero
  签名: [零 M₀'] [乘法 M₀'] [幺 M₀'] [幂 M₀' 自然数]
  定义体: { hf.monoid f one mul npow, hf.mulZeroClass f zero mul with }
-/
protected abbrev Function.Injective.monoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' Nat]
    [MonoidWithZero M₀] (f : M₀' -> M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : forall x y, f (x * y) = f x * f y) (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n) :
    MonoidWithZero M₀' :=
  { hf.monoid f one mul npow, hf.mulZeroClass f zero mul with }

/--
Definition of `Function.Surjective.monoidWithZero` / `Function.Surjective.monoidWithZero` 的定义

English:
abbreviation Function.Surjective.monoidWithZero
  signature: [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' Nat]
  body: { hf.monoid f one mul npow, hf.mulZeroClass f zero mul with }

中文:
缩写 函数.满射.monoidWithZero
  签名: [零 M₀'] [乘法 M₀'] [幺 M₀'] [幂 M₀' 自然数]
  定义体: { hf.monoid f one mul npow, hf.mulZeroClass f zero mul with }
-/
protected abbrev Function.Surjective.monoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' Nat]
    [MonoidWithZero M₀] (f : M₀ -> M₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : forall x y, f (x * y) = f x * f y) (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n) :
    MonoidWithZero M₀' :=
  { hf.monoid f one mul npow, hf.mulZeroClass f zero mul with }

/--
Definition of `Function.Injective.commMonoidWithZero` / `Function.Injective.commMonoidWithZero` 的定义

English:
abbreviation Function.Injective.commMonoidWithZero
  signature: [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' Nat]
  body: { hf.commMonoid f one mul npow, hf.mulZeroClass f zero mul with }

中文:
缩写 函数.单射.commMonoidWithZero
  签名: [零 M₀'] [乘法 M₀'] [幺 M₀'] [幂 M₀' 自然数]
  定义体: { hf.commMonoid f one mul npow, hf.mulZeroClass f zero mul with }
-/
protected abbrev Function.Injective.commMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' Nat]
    [CommMonoidWithZero M₀] (f : M₀' -> M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : forall x y, f (x * y) = f x * f y) (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n) :
    CommMonoidWithZero M₀' :=
  { hf.commMonoid f one mul npow, hf.mulZeroClass f zero mul with }

/--
Definition of `Function.Surjective.commMonoidWithZero` / `Function.Surjective.commMonoidWithZero` 的定义

English:
abbreviation Function.Surjective.commMonoidWithZero
  signature: [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' Nat]
  body: { hf.commMonoid f one mul npow, hf.mulZeroClass f zero mul with }

中文:
缩写 函数.满射.commMonoidWithZero
  签名: [零 M₀'] [乘法 M₀'] [幺 M₀'] [幂 M₀' 自然数]
  定义体: { hf.commMonoid f one mul npow, hf.mulZeroClass f zero mul with }
-/
protected abbrev Function.Surjective.commMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' Nat]
    [CommMonoidWithZero M₀] (f : M₀ -> M₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : forall x y, f (x * y) = f x * f y) (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n) :
    CommMonoidWithZero M₀' :=
  { hf.commMonoid f one mul npow, hf.mulZeroClass f zero mul with }

end MonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀]

/--
Definition of `Function.Injective.groupWithZero` / `Function.Injective.groupWithZero` 的定义

English:
abbreviation Function.Injective.groupWithZero
  signature: [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀']
  body: { hf.monoidWithZero f zero one mul npow,
    hf.divInvMonoid f one mul inv div npow zpow,
    domain_nontrivial f zero one with
inv_zero := hf by rw [inv, zero, inv_zero],
mul_inv_cancel := fun x hx => hf by
      rw [one]; rw [mul]; rw [inv]; rw [mul_inv_cancel₀ ((hf.ne_iff' zero).2 hx)] }

中文:
缩写 函数.单射.groupWithZero
  签名: [零 G₀'] [乘法 G₀'] [幺 G₀'] [取逆 G₀'] [除法 G₀']
  定义体: { hf.monoidWithZero f zero one mul npow,
    hf.divInvMonoid f one mul inv div npow zpow,
    domain_nontrivial f zero one with
inv_zero := hf by rw [inv, zero, inv_zero],
mul_inv_cancel := fun x hx => hf by
      rw [one]; rw [mul]; rw [inv]; rw [mul_inv_cancel₀ ((hf.ne_iff' zero).2 hx)] }
-/
protected abbrev Function.Injective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀']
    [Pow G₀' Nat] [Pow G₀' Int] (f : G₀' -> G₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : forall x y, f (x * y) = f x * f y) (inv : forall x, f x⁻¹ = (f x)⁻¹)
    (div : forall x y, f (x / y) = f x / f y) (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n)
    (zpow : forall (x) (n : Int), f (x ^ n) = f x ^ n) : GroupWithZero G₀' :=
  { hf.monoidWithZero f zero one mul npow,
    hf.divInvMonoid f one mul inv div npow zpow,
    domain_nontrivial f zero one with
inv_zero := hf by rw [inv, zero, inv_zero],
mul_inv_cancel := fun x hx => hf by
      rw [one]; rw [mul]; rw [inv]; rw [mul_inv_cancel₀ ((hf.ne_iff' zero).2 hx)] }

/--
Definition of `Function.Surjective.groupWithZero` / `Function.Surjective.groupWithZero` 的定义

English:
abbreviation Function.Surjective.groupWithZero
  signature: [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀']
  body: { hf.monoidWithZero f zero one mul npow, hf.divInvMonoid f one mul inv div npow zpow with
    inv_zero := by rw [← zero, ← inv, inv_zero],
    mul_inv_cancel := hf.forall.2 fun x hx => by
        rw [← inv]; rw [← mul]; rw [mul_inv_cancel₀ (mt (congr_arg f) fun h => hx (h.trans zero))]; rw [one]
    exists_pair_ne := ⟨0, 1, h01⟩ }

中文:
缩写 函数.满射.groupWithZero
  签名: [零 G₀'] [乘法 G₀'] [幺 G₀'] [取逆 G₀']
  定义体: { hf.monoidWithZero f zero one mul npow, hf.divInvMonoid f one mul inv div npow zpow with
    inv_zero := by rw [← zero, ← inv, inv_zero],
    mul_inv_cancel := hf.forall.2 fun x hx => by
        rw [← inv]; rw [← mul]; rw [mul_inv_cancel₀ (mt (congr_arg f) fun h => hx (h.trans zero))]; rw [one]
    exists_pair_ne := ⟨0, 1, h01⟩ }
-/
protected abbrev Function.Surjective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀']
    [Div G₀'] [Pow G₀' Nat] [Pow G₀' Int] (h01 : (0 : G₀') != 1) (f : G₀ -> G₀') (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : forall x y, f (x * y) = f x * f y)
    (inv : forall x, f x⁻¹ = (f x)⁻¹) (div : forall x y, f (x / y) = f x / f y)
    (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n) (zpow : forall (x) (n : Int), f (x ^ n) = f x ^ n) :
    GroupWithZero G₀' :=
  { hf.monoidWithZero f zero one mul npow, hf.divInvMonoid f one mul inv div npow zpow with
    inv_zero := by rw [← zero, ← inv, inv_zero],
    mul_inv_cancel := hf.forall.2 fun x hx => by
        rw [← inv]; rw [← mul]; rw [mul_inv_cancel₀ (mt (congr_arg f) fun h => hx (h.trans zero))]; rw [one]
    exists_pair_ne := ⟨0, 1, h01⟩ }

end GroupWithZero

section CommGroupWithZero

variable [CommGroupWithZero G₀]

/--
Definition of `Function.Injective.commGroupWithZero` / `Function.Injective.commGroupWithZero` 的定义

English:
abbreviation Function.Injective.commGroupWithZero
  signature: [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀']
  body: { hf.groupWithZero f zero one mul inv div npow zpow, hf.commSemigroup f mul with }

中文:
缩写 函数.单射.commGroupWithZero
  签名: [零 G₀'] [乘法 G₀'] [幺 G₀'] [取逆 G₀']
  定义体: { hf.groupWithZero f zero one mul inv div npow zpow, hf.commSemigroup f mul with }
-/
protected abbrev Function.Injective.commGroupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀']
    [Div G₀'] [Pow G₀' Nat] [Pow G₀' Int] (f : G₀' -> G₀) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (mul : forall x y, f (x * y) = f x * f y) (inv : forall x, f x⁻¹ = (f x)⁻¹)
    (div : forall x y, f (x / y) = f x / f y) (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n)
    (zpow : forall (x) (n : Int), f (x ^ n) = f x ^ n) : CommGroupWithZero G₀' :=
  { hf.groupWithZero f zero one mul inv div npow zpow, hf.commSemigroup f mul with }

/-- Push forward a `CommGroupWithZero` along a surjective function.
See note [reducible non-instances]. -/
@[instance_reducible]
/--
Definition of `Function.Surjective.commGroupWithZero` / `Function.Surjective.commGroupWithZero` 的定义

English:
definition Function.Surjective.commGroupWithZero
  signature: [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀']
  body: { hf.groupWithZero h01 f zero one mul inv div npow zpow, hf.commSemigroup f mul with }

中文:
定义 函数.满射.commGroupWithZero
  签名: [零 G₀'] [乘法 G₀'] [幺 G₀'] [取逆 G₀']
  定义体: { hf.groupWithZero h01 f zero one mul inv div npow zpow, hf.commSemigroup f mul with }
-/
protected def Function.Surjective.commGroupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀']
    [Div G₀'] [Pow G₀' Nat] [Pow G₀' Int] (h01 : (0 : G₀') != 1) (f : G₀ -> G₀') (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : forall x y, f (x * y) = f x * f y)
    (inv : forall x, f x⁻¹ = (f x)⁻¹) (div : forall x y, f (x / y) = f x / f y)
    (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n) (zpow : forall (x) (n : Int), f (x ^ n) = f x ^ n) :
    CommGroupWithZero G₀' :=
  { hf.groupWithZero h01 f zero one mul inv div npow zpow, hf.commSemigroup f mul with }

end CommGroupWithZero
