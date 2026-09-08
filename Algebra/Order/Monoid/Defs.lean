/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Yuyang Zhao
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Ordered monoids

This file provides the definitions of ordered monoids.

-/

public section


open Function

variable {α : Type*}

-- TODO: assume weaker typeclasses

/-- An ordered (additive) monoid is a monoid with a preorder such that addition is monotone. -/
/-
**IsOrderedAddMonoid** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：IsOrderedAddMonoid (α : Type*) [AddCommMonoid α] [Preorder α] where protec
ted add_le_add_left (a b : α) : a <= b -> forall c, a + c <= b + c protected add
_le_add_right (a b : α) : a <= b -> forall c, c + a <= c + b
参数：α : Type*；a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordered (additive) monoid is a monoid with a preorder such that addition is m
onotone.
-/
class IsOrderedAddMonoid (α : Type*) [AddCommMonoid α] [Preorder α] where
  protected add_le_add_left (a b : α) : a ≤ b → ∀ c, a + c ≤ b + c
  protected add_le_add_right (a b : α) : a ≤ b → ∀ c, c + a ≤ c + b := fun h c ↦ by
    rw [add_comm c, add_comm c]; exact add_le_add_left a b h c

/-- An ordered monoid is a monoid with a preorder such that multiplication is monotone. -/
@[to_additive]
/-
**IsOrderedMonoid** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：IsOrderedMonoid (α : Type*) [CommMonoid α] [Preorder α] where protected mu
l_le_mul_left (a b : α) : a <= b -> forall c, a * c <= b * c protected mul_le_mu
l_right (a b : α) : a <= b -> forall c, c * a <= c * b
参数：α : Type*；a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordered monoid is a monoid with a preorder such that multiplication is monoto
ne.
-/
class IsOrderedMonoid (α : Type*) [CommMonoid α] [Preorder α] where
  protected mul_le_mul_left (a b : α) : a ≤ b → ∀ c, a * c ≤ b * c
  protected mul_le_mul_right (a b : α) : a ≤ b → ∀ c, c * a ≤ c * b := fun h c ↦ by
    rw [mul_comm c, mul_comm c]; exact mul_le_mul_left a b h c

section IsOrderedMonoid
variable [CommMonoid α] [Preorder α] [IsOrderedMonoid α]

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) IsOrderedMonoid.toMulLeftMono : MulLeftMono α where
  elim := fun a _ _ bc ↦ IsOrderedMonoid.mul_le_mul_right _ _ bc a

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) IsOrderedMonoid.toMulRightMono : MulRightMono α where
  elim := fun a _ _ bc ↦ IsOrderedMonoid.mul_le_mul_left _ _ bc a

end IsOrderedMonoid

/-- An ordered cancellative additive monoid is an ordered additive
monoid in which addition is cancellative and monotone. -/
/-
**IsOrderedCancelAddMonoid** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：IsOrderedCancelAddMonoid (α : Type*) [AddCommMonoid α] [Preorder α] extend
s IsOrderedAddMonoid α where protected le_of_add_le_add_left : forall a b c : α,
 a + b <= a + c -> b <= c protected le_of_add_le_add_right : forall a b c : α, b
 + a <= c + a -> b <= c
参数：α : Type*。
继承自：IsOrderedAddMonoid α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordered cancellative additive monoid is an ordered additive
monoid in which addition is cancellative and monotone.
-/
class IsOrderedCancelAddMonoid (α : Type*) [AddCommMonoid α] [Preorder α] extends
    IsOrderedAddMonoid α where
  protected le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c
  protected le_of_add_le_add_right : ∀ a b c : α, b + a ≤ c + a → b ≤ c := fun a b c h ↦ by
    rw [add_comm _ a, add_comm _ a] at h; exact le_of_add_le_add_left a b c h

/-- An ordered cancellative monoid is an ordered monoid in which
multiplication is cancellative and monotone. -/
@[to_additive IsOrderedCancelAddMonoid]
/-
**IsOrderedCancelMonoid** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：IsOrderedCancelMonoid (α : Type*) [CommMonoid α] [Preorder α] extends IsOr
deredMonoid α where protected le_of_mul_le_mul_left : forall a b c : α, a * b <=
 a * c -> b <= c protected le_of_mul_le_mul_right : forall a b c : α, b * a <= c
 * a -> b <= c
参数：α : Type*。
继承自：IsOrderedMonoid α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordered cancellative monoid is an ordered monoid in which
multiplication is cancellative and monotone.
-/
class IsOrderedCancelMonoid (α : Type*) [CommMonoid α] [Preorder α] extends
    IsOrderedMonoid α where
  protected le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c
  protected le_of_mul_le_mul_right : ∀ a b c : α, b * a ≤ c * a → b ≤ c := fun a b c h ↦ by
    rw [mul_comm _ a, mul_comm _ a] at h; exact le_of_mul_le_mul_left a b c h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] :
    Lean.Grind.OrderedAdd α where
  add_le_left_iff {a b} c := ⟨
    fun h ↦ IsOrderedAddMonoid.add_le_add_left a b h c,
    IsOrderedCancelAddMonoid.le_of_add_le_add_right c a b⟩

section IsOrderedCancelMonoid
variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]

-- See note [lower instance priority]
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 200) IsOrderedCancelMonoid.toMulLeftReflectLE
  {α : Type*} [CommMonoid α] [Preorder α] [IsOrderedCancelMonoid α] : MulLeftReflectLE α where
  le_of_mul_le_mul_left' := IsOrderedCancelMonoid.le_of_mul_le_mul_left _ _ _

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) IsOrderedCancelMonoid.toMulLeftReflectLT : MulLeftReflectLT α where
  elim := contravariant_lt_of_contravariant_le α α _ fun _ ↦ MulLeftReflectLE.le_of_mul_le_mul_left'

@[to_additive]
/-
**IsOrderedCancelMonoid.toMulRightReflectLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOrderedCancelMonoid.toMulRightReflectLT : MulRightReflectLT α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
-/
theorem IsOrderedCancelMonoid.toMulRightReflectLT : MulRightReflectLT α :=
  inferInstance

-- See note [lower instance priority]
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsOrderedCancelMonoid.toIsCancelMul : IsCancelMul α where
  mul_left_cancel _ _ _ h :=
    (le_of_mul_le_mul_left' h.le).antisymm <| le_of_mul_le_mul_left' h.ge
  mul_right_cancel _ _ _ h :=
    (le_of_mul_le_mul_right' h.le).antisymm <| le_of_mul_le_mul_right' h.ge

@[to_additive]
/-
**IsOrderedCancelMonoid.of_mul_lt_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOrderedCancelMonoid.of_mul_lt_mul_left {α : Type*} [CommMonoid α] [Linea
rOrder α] (hmul : forall a b c : α, b < c -> a * b < a * c) : IsOrderedCancelMon
oid α where mul_le_mul_left a b h c
参数：hmul : forall a b c : α, b < c -> a * b < a * c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem IsOrderedCancelMonoid.of_mul_lt_mul_left {α : Type*} [CommMonoid α] [LinearOrder α]
    (hmul : ∀ a b c : α, b < c → a * b < a * c) : IsOrderedCancelMonoid α where
  mul_le_mul_left a b h c := by
    obtain rfl | h := eq_or_lt_of_le h
    · simp
    · simpa [mul_comm] using (hmul _ _ _ h).le
  le_of_mul_le_mul_left a b c h := by
    contrapose! h
    exact hmul _ _ _ h

end IsOrderedCancelMonoid

variable [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α] {a : α}

@[to_additive (attr := simp)]
/-
**one_le_mul_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_mul_self_iff : 1 <= a * a ↔ 1 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mul_lt_one'`：∀ {α : Type u_1} [inst : MulOneClass α] [inst_1 : Preorder 
α] [MulLeftMono α] {a b : α}, a < 1 → b < 1 → a * b < 1
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `one_le_mul`：∀ {α : Type u_1} [inst : MulOneClass α] [inst_1 : Preorder α
] [MulLeftMono α] {a b : α}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b
-/
theorem one_le_mul_self_iff : 1 ≤ a * a ↔ 1 ≤ a :=
  ⟨fun h ↦ by contrapose! h; exact mul_lt_one' h h, fun h ↦ one_le_mul h h⟩

@[to_additive (attr := simp)]
/-
**one_lt_mul_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_lt_mul_self_iff : 1 < a * a ↔ 1 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mul_le_one'`：∀ {α : Type u_1} [inst : MulOneClass α] [inst_1 : Preorder 
α] [MulLeftMono α] {a b : α}, a ≤ 1 → b ≤ 1 → a * b ≤ 1
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `one_lt_mul''`：∀ {α : Type u_1} [inst : MulOneClass α] [inst_1 : Preorder
 α] [MulLeftMono α] {a b : α}, 1 < a → 1 < b → 1 < a * b
-/
theorem one_lt_mul_self_iff : 1 < a * a ↔ 1 < a :=
  ⟨fun h ↦ by contrapose! h; exact mul_le_one' h h, fun h ↦ one_lt_mul'' h h⟩

@[to_additive (attr := simp)]
/-
**mul_self_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_self_le_one_iff : a * a <= 1 ↔ a <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_lt_mul_self_iff`：one_lt_mul_self_iff : 1 < a * a ↔ 1 < a
-/
theorem mul_self_le_one_iff : a * a ≤ 1 ↔ a ≤ 1 := by contrapose!; exact one_lt_mul_self_iff

@[to_additive (attr := simp)]
/-
**mul_self_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_self_lt_one_iff : a * a < 1 ↔ a < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_le_mul_self_iff`：one_le_mul_self_iff : 1 <= a * a ↔ 1 <= a
-/
theorem mul_self_lt_one_iff : a * a < 1 ↔ a < 1 := by contrapose!; exact one_le_mul_self_iff
