/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.LatticeIntervals
public import Mathlib.Order.SuccPred.Basic

/-!
# Successors in intervals

If `j` is an element of a partially ordered set equipped
with a successor function, then for any element `i : Set.Iic j`
which is not the maximum, we have `↑(Order.succ i) = Order.succ ↑i`.

-/

public section

namespace Set

variable {J : Type*} [PartialOrder J]

/-
**Set.Iic.coe_succ_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iic`。
形式化陈述：∀ {J : Type u_1} [inst : PartialOrder J] [inst_1 : SuccOrder J] {j : J} {i
 : ↑(Set.Iic j)},   ¬IsMax i → ↑(Order.succ i) = Order.succ ↑i
参数：Set.Iic j；Order.succ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ordConnected_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iic a).OrdConnected
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `coe_succ_of_mem`：coe_succ_of_mem [SuccOrder α] {a : s} (h : succ ↑a in s
) : (succ a).1 = succ ↑a
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `le_top`：le_top : a <= ⊤
-/
lemma Iic.coe_succ_of_not_isMax
    [SuccOrder J] {j : J} {i : Set.Iic j} (hi : ¬ IsMax i) :
    (Order.succ i).1 = Order.succ i.1 := by
  rw [coe_succ_of_mem]
  apply Order.succ_le_of_lt
  exact lt_of_le_of_ne (α := Set.Iic j) le_top (by simpa using hi)
/-
**Set.Iic.succ_eq_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iic`。
形式化陈述：∀ {J : Type u_1} [inst : PartialOrder J] [inst_1 : SuccOrder J] {j : J} {i
 : ↑(Set.Iic j)} (hi : ¬IsMax i),   Order.succ i = ⟨Order.succ ↑i, ⋯⟩
参数：Set.Iic j；hi : ¬IsMax i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Set.ordConnected_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iic a).OrdConnected
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Iic.coe_succ_of_not_isMax`：∀ {J : Type u_1} [inst : PartialOrder J] 
[inst_1 : SuccOrder J] {j : J} {i : ↑(Set.Iic j)},   ¬IsMax i → ↑(Order.succ i) 
= Order.succ ↑i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Iic.succ_eq_of_not_isMax
    [SuccOrder J] {j : J} {i : Set.Iic j} (hi : ¬ IsMax i) :
    Order.succ i = ⟨Order.succ i.1, by
      rw [← coe_succ_of_not_isMax hi]
      apply Subtype.coe_prop⟩ := by
  ext
  simp only [coe_succ_of_not_isMax hi]
/-
**Set.Ici.coe_pred_of_not_isMin** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ici`。
形式化陈述：∀ {J : Type u_1} [inst : PartialOrder J] [inst_1 : PredOrder J] {j : J} {i
 : ↑(Set.Ici j)},   ¬IsMin i → ↑(Order.pred i) = Order.pred ↑i
参数：Set.Ici j；Order.pred i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `coe_pred_of_mem`：coe_pred_of_mem [PredOrder α] {a : s} (h : pred a.1 in 
s) : (pred a).1 = pred ↑a
· 使用定理 `Order.le_pred_of_lt`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Pred
Order α] {a b : α}, b < a → b ≤ Order.pred a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma Ici.coe_pred_of_not_isMin
    [PredOrder J] {j : J} {i : Set.Ici j} (hi : ¬ IsMin i) :
    (Order.pred i).1 = Order.pred i.1 := by
  rw [coe_pred_of_mem]
  apply Order.le_pred_of_lt
  exact lt_of_le_of_ne (α := Set.Ici j) bot_le (Ne.symm (by simpa using hi))
/-
**Set.Ici.pred_eq_of_not_isMin** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ici`。
形式化陈述：∀ {J : Type u_1} [inst : PartialOrder J] [inst_1 : PredOrder J] {j : J} {i
 : ↑(Set.Ici j)} (hi : ¬IsMin i),   Order.pred i = ⟨Order.pred ↑i, ⋯⟩
参数：Set.Ici j；hi : ¬IsMin i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ici.coe_pred_of_not_isMin`：∀ {J : Type u_1} [inst : PartialOrder J] 
[inst_1 : PredOrder J] {j : J} {i : ↑(Set.Ici j)},   ¬IsMin i → ↑(Order.pred i) 
= Order.pred ↑i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ici.pred_eq_of_not_isMin
    [PredOrder J] {j : J} {i : Set.Ici j} (hi : ¬ IsMin i) :
    Order.pred i = ⟨Order.pred i.1, by
      rw [← coe_pred_of_not_isMin hi]
      apply Subtype.coe_prop⟩ := by
  ext
  simp only [coe_pred_of_not_isMin hi]

end Set

