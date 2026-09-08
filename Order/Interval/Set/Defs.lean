/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Push.Attr

/-!
# Intervals

In any preorder `α`, we define intervals
(which on each side can be either infinite, open, or closed)
using the following naming conventions:
- `i`: infinite
- `o`: open
- `c`: closed

Each interval has the name `I` + letter for left side + letter for right side.
For instance, `Ioc a b` denotes the interval `(a, b]`.

We also define a typeclass `Set.OrdConnected`
saying that a set includes `Set.Icc a b` whenever it contains both `a` and `b`.
-/

@[expose] public section

namespace Set

variable {α : Type*} [Preorder α] {a b x : α}

/-- `Iio b` is the left-infinite right-open interval $(-∞, b)$. -/
@[to_dual /-- `Ioi a` is the left-open right-infinite interval $(a, ∞)$. -/]
/-
**Set.Iio** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：Iio (b : α)
参数：b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Iio b` is the left-infinite right-open interval $(-∞, b)$.
-/
def Iio (b : α) := { x | x < b }
/-
**Set.mem_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio b ↔ x < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_dual (attr := simp, grind =, push)] theorem mem_Iio : x ∈ Iio b ↔ x < b := .rfl
/-
**Set.Iio_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (a : α), {x | x < a} = Set.Iio a
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual] theorem Iio_def (a : α) : { x | x < a } = Iio a := rfl

/-- `Iic b` is the left-infinite right-closed interval $(-∞, b]$. -/
@[to_dual /-- `Ici a` is the left-closed right-infinite interval $[a, ∞)$. -/]
/-
**Set.Iic** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：Iic (b : α)
参数：b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Iic b` is the left-infinite right-closed interval $(-∞, b]$.
-/
def Iic (b : α) := { x | x ≤ b }
/-
**Set.mem_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iic b ↔ x ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_dual (attr := simp, grind =, push)] theorem mem_Iic : x ∈ Iic b ↔ x ≤ b := .rfl
/-
**Set.Iic_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (b : α), {x | x ≤ b} = Set.Iic b
参数：b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual] theorem Iic_def (b : α) : { x | x ≤ b } = Iic b := rfl

/-- `Ioo a b` is the left-open right-open interval $(a, b)$. -/
@[to_dual self (reorder := a b)]
/-
**Set.Ioo** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：Ioo (a b : α)
参数：a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Ioo a b` is the left-open right-open interval $(a, b)$.
-/
def Ioo (a b : α) := { x | a < x ∧ x < b }

to_dual_insert_cast Ioo := by simp only [and_comm]
/-
**Set.mem_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.Ioo a b ↔ a < x 
∧ x < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, grind =, push, to_dual none] theorem mem_Ioo : x ∈ Ioo a b ↔ a < x ∧ x < b := .rfl
/-
**Set.Ioo_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (a b : α), {x | a < x ∧ x < b} = Set.
Ioo a b
参数：a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual none] theorem Ioo_def (a b : α) : { x | a < x ∧ x < b } = Ioo a b := rfl

/-- `Ico a b` is the left-closed right-open interval $[a, b)$. -/
/-
**Set.Ico** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：Ico (a b : α)
参数：a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Ico a b` is the left-closed right-open interval $[a, b)$.
-/
def Ico (a b : α) := { x | a ≤ x ∧ x < b }

/-- `Ioc a b` is the left-open right-closed interval $(a, b]$. -/
@[to_dual existing (reorder := a b)]
/-
**Set.Ioc** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：Ioc (a b : α)
参数：a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Ioc a b` is the left-open right-closed interval $(a, b]$.
-/
def Ioc (a b : α) := { x | a < x ∧ x ≤ b }

to_dual_insert_cast Ico := by simp only [and_comm]
to_dual_insert_cast Ioc := by simp only [and_comm]
/-
**Set.mem_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.Ico a b ↔ a ≤ x 
∧ x < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, grind =, push, to_dual none] theorem mem_Ico : x ∈ Ico a b ↔ a ≤ x ∧ x < b := .rfl
/-
**Set.Ico_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (a b : α), {x | a ≤ x ∧ x < b} = Set.
Ico a b
参数：a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual none] theorem Ico_def (a b : α) : { x | a ≤ x ∧ x < b } = Ico a b := rfl
/-
**Set.mem_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.Ioc a b ↔ a < x 
∧ x ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, grind =, push, to_dual none] theorem mem_Ioc : x ∈ Ioc a b ↔ a < x ∧ x ≤ b := .rfl
/-
**Set.Ioc_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (a b : α), {x | a < x ∧ x ≤ b} = Set.
Ioc a b
参数：a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual none] theorem Ioc_def (a b : α) : { x | a < x ∧ x ≤ b } = Ioc a b := rfl

/-- `Icc a b` is the left-closed right-closed interval $[a, b]$. -/
@[to_dual self (reorder := a b)]
/-
**Set.Icc** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：Icc (a b : α)
参数：a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Icc a b` is the left-closed right-closed interval $[a, b]$.
-/
def Icc (a b : α) := { x | a ≤ x ∧ x ≤ b }

to_dual_insert_cast Icc := by simp only [and_comm]
/-
**Set.mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.Icc a b ↔ a ≤ x 
∧ x ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, grind =, push, to_dual none] theorem mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b := .rfl
/-
**Set.Icc_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (a b : α), {x | a ≤ x ∧ x ≤ b} = Set.
Icc a b
参数：a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual none] theorem Icc_def (a b : α) : { x | a ≤ x ∧ x ≤ b } = Icc a b := rfl

/-- We say that a set `s : Set α` is `OrdConnected` if for all `x y ∈ s` it includes the
interval `[[x, y]]`. If `α` is a `DenselyOrdered` `ConditionallyCompleteLinearOrder` with
the `OrderTopology`, then this condition is equivalent to `IsPreconnected s`. If `α` is a
linearly ordered field, then this condition is also equivalent to `Convex α s`. -/
/-
**Set.OrdConnected** 是 Mathlib 中的一个类，位于命名空间 `Set`。
形式化陈述：OrdConnected (s : Set α) : Prop where /-- `s : Set α` is `OrdConnected` if
 for all `x y ∈ s` it includes the interval `[[x, y]]`. -/ out' ⦃x : α⦄ (hx : x 
in s) ⦃y : α⦄ (hy : y in s) : Icc x y subseteq s  attribute [to_dual self (reord
er
参数：s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a set `s : Set α` is `OrdConnected` if for all `x y ∈ s` it includes
 the
interval `[[x, y]]`. If `α` is a `DenselyOrdered` `ConditionallyCompleteLinearOr
der` with
the `OrderTopology`, then this condition is equivalent to `IsPreconnected s`. If
 `α` is a
linearly ordered field, then this condition is also equivalent to `Convex α s`.
-/
class OrdConnected (s : Set α) : Prop where
  /-- `s : Set α` is `OrdConnected` if for all `x y ∈ s` it includes the interval `[[x, y]]`. -/
  out' ⦃x : α⦄ (hx : x ∈ s) ⦃y : α⦄ (hy : y ∈ s) : Icc x y ⊆ s

attribute [to_dual self (reorder := out' (x y, hx hy))] OrdConnected.mk
attribute [to_dual self (reorder := x y, hx hy)] OrdConnected.out'

end Set

