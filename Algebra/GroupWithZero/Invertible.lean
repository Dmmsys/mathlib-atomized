/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Theorems about invertible elements in a `GroupWithZero`

We intentionally keep imports minimal here as this file is used by `Mathlib/Tactic/NormNum.lean`.
-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

open scoped Ring

universe u

variable {α : Type u}

/--
theorem `Invertible.ne_zero` / 定理 `Invertible.ne_zero`

English:
theorem Invertible.ne_zero
  given: [MulZeroOneClass α] (a : α) [Nontrivial α] [Invertible a]
  statement: a != 0
  proof: fun ha =>
zero_ne_one
    calc
      0 = ⅟a * a := by simp [ha]
      _ = 1 := invOf_mul_self

中文:
定理 Invertible.ne_zero
  条件: [MulZeroOneClass α] (a : α) [Nontrivial α] [Invertible a]
  结论: a != 0
  证明: fun ha =>
zero_ne_one
    calc
      0 = ⅟a * a := by simp [ha]
      _ = 1 := invOf_mul_self

Depends on / 依赖: invOf_mul_self, zero_ne_one
-/
theorem Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nontrivial α] [Invertible a] : a != 0 :=
  fun ha =>
zero_ne_one
    calc
      0 = ⅟a * a := by simp [ha]
      _ = 1 := invOf_mul_self

instance (priority := 100) Invertible.toNeZero [MulZeroOneClass α] [Nontrivial α] (a : α)
    [Invertible a] : NeZero a :=
  ⟨Invertible.ne_zero a⟩

section MonoidWithZero
variable [MonoidWithZero α]

/-- A variant of `Ring.inverse_unit`. -/
@[simp]
/--
theorem `Ring.inverse_invertible` / 定理 `Ring.inverse_invertible`

English:
theorem Ring.inverse_invertible
  given: (x : α) [Invertible x]
  statement: x⁻¹ʳ = ⅟x
  proof: Ring.inverse_unit (unitOfInvertible _)

中文:
定理 Ring.inverse_invertible
  条件: (x : α) [Invertible x]
  结论: x⁻¹ʳ = ⅟x
  证明: Ring.inverse_unit (unitOfInvertible _)

Depends on / 依赖: Ring.inverse_unit, inverse_unit, unitOfInvertible
-/
theorem Ring.inverse_invertible (x : α) [Invertible x] : x⁻¹ʳ = ⅟x :=
  Ring.inverse_unit (unitOfInvertible _)

end MonoidWithZero

section GroupWithZero
variable [GroupWithZero α]

/-- `a⁻¹` is an inverse of `a` if `a ≠ 0` -/
@[instance_reducible]
/--
Definition of `invertibleOfNonzero` / `invertibleOfNonzero` 的定义

English:
definition invertibleOfNonzero
  signature: {a : α} (h : a != 0)
  body: ⟨a⁻¹, inv_mul_cancel₀ h, mul_inv_cancel₀ h⟩

@[simp]

中文:
定义 invertibleOfNonzero
  签名: {a : α} (h : a != 0)
  定义体: ⟨a⁻¹, inv_mul_cancel₀ h, mul_inv_cancel₀ h⟩

@[simp]
-/
def invertibleOfNonzero {a : α} (h : a != 0) : Invertible a :=
  ⟨a⁻¹, inv_mul_cancel₀ h, mul_inv_cancel₀ h⟩

@[simp]
/--
theorem `invOf_eq_inv` / 定理 `invOf_eq_inv`

English:
theorem invOf_eq_inv
  given: (a : α) [Invertible a]
  statement: ⅟a = a⁻¹
  proof: invOf_eq_right_inv (mul_inv_cancel₀ (Invertible.ne_zero a))

@[simp]

中文:
定理 invOf_eq_inv
  条件: (a : α) [Invertible a]
  结论: ⅟a = a⁻¹
  证明: invOf_eq_right_inv (mul_inv_cancel₀ (Invertible.ne_zero a))

@[simp]

Depends on / 依赖: Invertible, Invertible.ne_zero, invOf_eq_right_inv, isLimit, isLimitConeOfHasLimitEval, limit.isLimit, ne_zero, preservesLimit_of_preserves_limit_cone
-/
theorem invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹ :=
  invOf_eq_right_inv (mul_inv_cancel₀ (Invertible.ne_zero a))

@[simp]
/--
theorem `inv_mul_cancel_of_invertible` / 定理 `inv_mul_cancel_of_invertible`

English:
theorem inv_mul_cancel_of_invertible
  given: (a : α) [Invertible a]
  statement: a⁻¹ * a = 1
  proof: inv_mul_cancel₀ (Invertible.ne_zero a)

@[simp]

中文:
定理 inv_mul_cancel_of_invertible
  条件: (a : α) [Invertible a]
  结论: a⁻¹ * a = 1
  证明: inv_mul_cancel₀ (Invertible.ne_zero a)

@[simp]

Depends on / 依赖: Invertible, Invertible.ne_zero, ne_zero
-/
theorem inv_mul_cancel_of_invertible (a : α) [Invertible a] : a⁻¹ * a = 1 :=
  inv_mul_cancel₀ (Invertible.ne_zero a)

@[simp]
/--
theorem `mul_inv_cancel_of_invertible` / 定理 `mul_inv_cancel_of_invertible`

English:
theorem mul_inv_cancel_of_invertible
  given: (a : α) [Invertible a]
  statement: a * a⁻¹ = 1
  proof: mul_inv_cancel₀ (Invertible.ne_zero a)

中文:
定理 mul_inv_cancel_of_invertible
  条件: (a : α) [Invertible a]
  结论: a * a⁻¹ = 1
  证明: mul_inv_cancel₀ (Invertible.ne_zero a)

Depends on / 依赖: Invertible, Invertible.ne_zero, ne_zero
-/
theorem mul_inv_cancel_of_invertible (a : α) [Invertible a] : a * a⁻¹ = 1 :=
  mul_inv_cancel₀ (Invertible.ne_zero a)

/--
Instance `invertibleInv` / 实例 `invertibleInv`

English:
instance invertibleInv
  signature: {a : α} [Invertible a]
  body: ⟨a, by simp, by simp⟩

@[simp]

中文:
实例 invertibleInv
  签名: {a : α} [Invertible a]
  定义体: ⟨a, by simp, by simp⟩

@[simp]
-/
instance invertibleInv {a : α} [Invertible a] : Invertible a⁻¹ :=
  ⟨a, by simp, by simp⟩

@[simp]
/--
theorem `div_mul_cancel_of_invertible` / 定理 `div_mul_cancel_of_invertible`

English:
theorem div_mul_cancel_of_invertible
  given: (a b : α) [Invertible b]
  statement: a / b * b = a
  proof: div_mul_cancel₀ a (Invertible.ne_zero b)

@[simp]

中文:
定理 div_mul_cancel_of_invertible
  条件: (a b : α) [Invertible b]
  结论: a / b * b = a
  证明: div_mul_cancel₀ a (Invertible.ne_zero b)

@[simp]

Depends on / 依赖: Invertible, Invertible.ne_zero, ne_zero
-/
theorem div_mul_cancel_of_invertible (a b : α) [Invertible b] : a / b * b = a :=
  div_mul_cancel₀ a (Invertible.ne_zero b)

@[simp]
/--
theorem `mul_div_cancel_of_invertible` / 定理 `mul_div_cancel_of_invertible`

English:
theorem mul_div_cancel_of_invertible
  given: (a b : α) [Invertible b]
  statement: a * b / b = a
  proof: mul_div_cancel_right₀ a (Invertible.ne_zero b)

@[simp]

中文:
定理 mul_div_cancel_of_invertible
  条件: (a b : α) [Invertible b]
  结论: a * b / b = a
  证明: mul_div_cancel_right₀ a (Invertible.ne_zero b)

@[simp]

Depends on / 依赖: Invertible, Invertible.ne_zero, ne_zero
-/
theorem mul_div_cancel_of_invertible (a b : α) [Invertible b] : a * b / b = a :=
  mul_div_cancel_right₀ a (Invertible.ne_zero b)

@[simp]
/--
theorem `div_self_of_invertible` / 定理 `div_self_of_invertible`

English:
theorem div_self_of_invertible
  given: (a : α) [Invertible a]
  statement: a / a = 1
  proof: div_self (Invertible.ne_zero a)

中文:
定理 div_self_of_invertible
  条件: (a : α) [Invertible a]
  结论: a / a = 1
  证明: div_self (Invertible.ne_zero a)

Depends on / 依赖: Invertible, Invertible.ne_zero, div_self, ne_zero
-/
theorem div_self_of_invertible (a : α) [Invertible a] : a / a = 1 :=
  div_self (Invertible.ne_zero a)

/-- `b / a` is the inverse of `a / b` -/
@[instance_reducible]
/--
Definition of `invertibleDiv` / `invertibleDiv` 的定义

English:
definition invertibleDiv
  signature: (a b : α) [Invertible a] [Invertible b]
  body: ⟨b / a, by simp [← mul_div_assoc], by simp [← mul_div_assoc]⟩

中文:
定义 invertibleDiv
  签名: (a b : α) [Invertible a] [Invertible b]
  定义体: ⟨b / a, by simp [← mul_div_assoc], by simp [← mul_div_assoc]⟩

Depends on / 依赖: mul_div_assoc
-/
def invertibleDiv (a b : α) [Invertible a] [Invertible b] : Invertible (a / b) :=
  ⟨b / a, by simp [← mul_div_assoc], by simp [← mul_div_assoc]⟩

/--
theorem `invOf_div` / 定理 `invOf_div`

English:
theorem invOf_div
  given: (a b : α) [Invertible a] [Invertible b] [Invertible (a / b)]
  proof: invOf_eq_right_inv (by simp [← mul_div_assoc])

中文:
定理 invOf_div
  条件: (a b : α) [Invertible a] [Invertible b] [Invertible (a / b)]
  证明: invOf_eq_right_inv (by simp [← mul_div_assoc])

Depends on / 依赖: invOf_eq_right_inv, mul_div_assoc
-/
theorem invOf_div (a b : α) [Invertible a] [Invertible b] [Invertible (a / b)] :
    ⅟(a / b) = b / a :=
  invOf_eq_right_inv (by simp [← mul_div_assoc])

end GroupWithZero
