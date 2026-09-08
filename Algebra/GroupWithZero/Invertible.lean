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

/-
**Invertible.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nontrivial α] [Invertible 
a] : a != 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Invertible.invOf_mul_self`：∀ {α : Type u} {inst : Mul α} {inst_1 : One α
} {a : α} [self : Invertible a], ⅟a * a = 1
-/
theorem Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nontrivial α] [Invertible a] : a ≠ 0 :=
  fun ha =>
  zero_ne_one <|
    calc
      0 = ⅟a * a := by simp [ha]
      _ = 1 := invOf_mul_self
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Invertible.toNeZero [MulZeroOneClass α] [Nontrivial α] (a : α)
    [Invertible a] : NeZero a :=
  ⟨Invertible.ne_zero a⟩

section MonoidWithZero
variable [MonoidWithZero α]

/-- A variant of `Ring.inverse_unit`. -/
@[simp]
/-
**Ring.inverse_invertible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.inverse_invertible (x : α) [Invertible x] : x⁻¹ʳ = ⅟x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)

--- 原说明 ---
A variant of `Ring.inverse_unit`.
-/
theorem Ring.inverse_invertible (x : α) [Invertible x] : x⁻¹ʳ = ⅟x :=
  Ring.inverse_unit (unitOfInvertible _)

end MonoidWithZero

section GroupWithZero
variable [GroupWithZero α]

/-- `a⁻¹` is an inverse of `a` if `a ≠ 0` -/
@[instance_reducible]
/-
**invertibleOfNonzero** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：invertibleOfNonzero {a : α} (h : a != 0) : Invertible a
参数：h : a != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1

--- 原说明 ---
`a⁻¹` is an inverse of `a` if `a ≠ 0`
-/
def invertibleOfNonzero {a : α} (h : a ≠ 0) : Invertible a :=
  ⟨a⁻¹, inv_mul_cancel₀ h, mul_inv_cancel₀ h⟩

@[simp]
/-
**invOf_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invOf_eq_right_inv`：invOf_eq_right_inv [Invertible a] (hac : a * b = 1) 
: ⅟a = b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Invertible.ne_zero`：Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nont
rivial α] [Invertible a] : a != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹ :=
  invOf_eq_right_inv (mul_inv_cancel₀ (Invertible.ne_zero a))

@[simp]
/-
**inv_mul_cancel_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_cancel_of_invertible (a : α) [Invertible a] : a⁻¹ * a = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Invertible.ne_zero`：Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nont
rivial α] [Invertible a] : a != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem inv_mul_cancel_of_invertible (a : α) [Invertible a] : a⁻¹ * a = 1 :=
  inv_mul_cancel₀ (Invertible.ne_zero a)

@[simp]
/-
**mul_inv_cancel_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_cancel_of_invertible (a : α) [Invertible a] : a * a⁻¹ = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Invertible.ne_zero`：Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nont
rivial α] [Invertible a] : a != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem mul_inv_cancel_of_invertible (a : α) [Invertible a] : a * a⁻¹ = 1 :=
  mul_inv_cancel₀ (Invertible.ne_zero a)

/-- `a` is the inverse of `a⁻¹` -/
/-
**invertibleInv** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：invertibleInv {a : α} [Invertible a] : Invertible a⁻¹
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`a` is the inverse of `a⁻¹`
-/
instance invertibleInv {a : α} [Invertible a] : Invertible a⁻¹ :=
  ⟨a, by simp, by simp⟩

@[simp]
/-
**div_mul_cancel_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mul_cancel_of_invertible (a b : α) [Invertible b] : a / b * b = a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `Invertible.ne_zero`：Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nont
rivial α] [Invertible a] : a != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem div_mul_cancel_of_invertible (a b : α) [Invertible b] : a / b * b = a :=
  div_mul_cancel₀ a (Invertible.ne_zero b)

@[simp]
/-
**mul_div_cancel_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_div_cancel_of_invertible (a b : α) [Invertible b] : a * b / b = a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `Invertible.ne_zero`：Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nont
rivial α] [Invertible a] : a != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem mul_div_cancel_of_invertible (a b : α) [Invertible b] : a * b / b = a :=
  mul_div_cancel_right₀ a (Invertible.ne_zero b)

@[simp]
/-
**div_self_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_self_of_invertible (a : α) [Invertible a] : a / a = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `Invertible.ne_zero`：Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nont
rivial α] [Invertible a] : a != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem div_self_of_invertible (a : α) [Invertible a] : a / a = 1 :=
  div_self (Invertible.ne_zero a)

/-- `b / a` is the inverse of `a / b` -/
@[instance_reducible]
/-
**invertibleDiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：invertibleDiv (a b : α) [Invertible a] [Invertible b] : Invertible (a / b)
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`b / a` is the inverse of `a / b`
-/
def invertibleDiv (a b : α) [Invertible a] [Invertible b] : Invertible (a / b) :=
  ⟨b / a, by simp [← mul_div_assoc], by simp [← mul_div_assoc]⟩
/-
**invOf_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_div (a b : α) [Invertible a] [Invertible b] [Invertible (a / b)] : ⅟
(a / b) = b / a
参数：a b : α；a / b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invOf_eq_right_inv`：invOf_eq_right_inv [Invertible a] (hac : a * b = 1) 
: ⅟a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_cancel_of_invertible`：div_mul_cancel_of_invertible (a b : α) [In
vertible b] : a / b * b = a
· 使用定理 `div_self_of_invertible`：div_self_of_invertible (a : α) [Invertible a] : 
a / a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invOf_div (a b : α) [Invertible a] [Invertible b] [Invertible (a / b)] :
    ⅟(a / b) = b / a :=
  invOf_eq_right_inv (by simp [← mul_div_assoc])

end GroupWithZero

