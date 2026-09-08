/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Algebra.Group.Units.Defs

/-!
# Units in ordered monoids
-/

@[expose] public section

namespace Units

variable {α : Type*}

@[to_additive]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] [Preorder α] : Preorder αˣ :=
  Preorder.lift val

@[to_additive (attr := simp, norm_cast)]
/-
**Units.val_le_val** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：val_le_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α) <= b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem val_le_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α) ≤ b ↔ a ≤ b :=
  Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Units.val_lt_val** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：val_lt_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α) < b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem val_lt_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α) < b ↔ a < b :=
  Iff.rfl

@[to_additive]
/-
**Units.instPartialOrderUnits** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：instPartialOrderUnits [Monoid α] [PartialOrder α] : PartialOrder αˣ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
-/
instance instPartialOrderUnits [Monoid α] [PartialOrder α] : PartialOrder αˣ :=
  PartialOrder.lift val val_injective

@[to_additive]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] [LinearOrder α] : Max αˣ where
  max a b := if a ≤ b then b else a

@[to_additive]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] [LinearOrder α] : Min αˣ where
  min a b := if a ≤ b then a else b


@[to_additive (attr := simp, norm_cast)]
/-
**Units.max_val** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：max_val [Monoid α] [LinearOrder α] (a b : αˣ) : (max a b).val = max a.val 
b.val
参数：a b : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `max_def`：max_def (a b : α) : max a b = if a <= b then b else a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
-/
theorem max_val [Monoid α] [LinearOrder α] (a b : αˣ) : (max a b).val = max a.val b.val := by
  simp_rw [max_def, val_le_val, ← apply_ite]
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Units.min_val** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：min_val [Monoid α] [LinearOrder α] (a b : αˣ) : (min a b).val = min a.val 
b.val
参数：a b : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_def`：min_def (a b : α) : min a b = if a <= b then a else b
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
-/
theorem min_val [Monoid α] [LinearOrder α] (a b : αˣ) : (min a b).val = min a.val b.val := by
  simp_rw [min_def, val_le_val, ← apply_ite]
  rfl

@[to_additive]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] [Ord α] : Ord αˣ where
  compare a b := compare a.val b.val

@[to_additive]
/-
**Units.compare_val** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：compare_val [Monoid α] [Ord α] (a b : αˣ) : compare a.val b.val = compare 
a b
参数：a b : αˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compare_val [Monoid α] [Ord α] (a b : αˣ) : compare a.val b.val = compare a b := rfl

@[to_additive]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] [LinearOrder α] : LinearOrder αˣ :=
  val_injective.linearOrder _ val_le_val val_lt_val min_val max_val compare_val

/-- `val : αˣ → α` as an order embedding. -/
@[to_additive (attr := simps -fullyApplied)
  /-- `val : add_units α → α` as an order embedding. -/]
/-
**Units.orderEmbeddingVal** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
形式化陈述：orderEmbeddingVal [Monoid α] [LinearOrder α] : αˣ ↪o α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
-/
def orderEmbeddingVal [Monoid α] [LinearOrder α] : αˣ ↪o α :=
  ⟨⟨val, val_injective⟩, .rfl⟩

end Units

