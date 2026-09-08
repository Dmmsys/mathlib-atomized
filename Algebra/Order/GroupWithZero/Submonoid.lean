/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Order.Interval.Set.Defs

/-!
# The submonoid of positive elements
-/

@[expose] public section

assert_not_exists RelIso Ring

namespace Submonoid
variable (α) [MulZeroOneClass α] [PartialOrder α] [PosMulStrictMono α] [ZeroLEOneClass α]
  [NeZero (1 : α)] {a : α}

/-- The submonoid of positive elements. -/
/-
**Submonoid.pos** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：(α : Type u_1) →   [inst : MulZeroOneClass α] →     [inst_1 : PartialOrder
 α] → [PosMulStrictMono α] → [ZeroLEOneClass α] → [NeZero 1] → Submonoid α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submonoid of positive elements.
-/
@[simps] def pos : Submonoid α where
  carrier := Set.Ioi 0
  one_mem' := zero_lt_one
  mul_mem' := mul_pos

variable {α}
/-
**Submonoid.mem_pos** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：∀ {α : Type u_1} [inst : MulZeroOneClass α] [inst_1 : PartialOrder α] [ins
t_2 : PosMulStrictMono α]   [inst_3 : ZeroLEOneClass α] [inst_4 : NeZero 1] {a :
 α}, a ∈ Submonoid.pos α ↔ 0 < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_pos : a ∈ pos α ↔ 0 < a := Iff.rfl

end Submonoid

