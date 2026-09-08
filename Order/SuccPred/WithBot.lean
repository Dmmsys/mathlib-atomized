/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Order.SuccPred.Basic

/-!
# Successor function on `WithBot`

This file defines the successor of `a : WithBot α` as an element of `α`, and dually for `WithTop`.
-/

@[expose] public section

namespace WithBot
variable {α : Type*} [Preorder α] [OrderBot α] [SuccOrder α] {x y : WithBot α}

/-- The successor of `a : WithBot α` as an element of `α`. -/
/-
**WithBot.succ** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：succ (a : WithBot α) : α
参数：a : WithBot α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The successor of `a : WithBot α` as an element of `α`.
-/
def succ (a : WithBot α) : α := a.recBotCoe ⊥ Order.succ

/-- Not to be confused with `WithBot.orderSucc_bot`, which is about `Order.succ`. -/
/-
**WithBot.succ_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] [inst_2 : SuccO
rder α], ⊥.succ = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Not to be confused with `WithBot.orderSucc_bot`, which is about `Order.succ`.
-/
@[simp] lemma succ_bot : succ (⊥ : WithBot α) = ⊥ := rfl

/-- Not to be confused with `WithBot.orderSucc_coe`, which is about `Order.succ`. -/
/-
**WithBot.succ_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] [inst_2 : SuccO
rder α] (a : α), (↑a).succ = Order.succ a
参数：a : α；↑a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Not to be confused with `WithBot.orderSucc_coe`, which is about `Order.succ`.
-/
@[simp] lemma succ_coe (a : α) : succ (a : WithBot α) = Order.succ a := rfl
/-
**WithBot.succ_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] [inst_2 : SuccO
rder α] (a : WithBot α),   ↑a.succ = Order.succ a
参数：a : WithBot α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Not to be confused with `WithBot.orderSucc_coe`, which is about `Order.succ`.
-/
lemma succ_eq_succ : ∀ a : WithBot α, succ a = Order.succ a
  | ⊥ => rfl
  | (a : α) => rfl
/-
**WithBot.lt_succ** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：lt_succ [NoMaxOrder α] (x : WithBot α) : x < x.succ
参数：x : WithBot α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `bot_nonempty`：∀ (α : Type u_1) [Bot α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.succ_eq_succ`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Ord
erBot α] [inst_2 : SuccOrder α] (a : WithBot α),   ↑a.succ = Order.succ a
-/
lemma lt_succ [NoMaxOrder α] (x : WithBot α) : x < x.succ :=
  succ_eq_succ x ▸ Order.lt_succ x
/-
**WithBot.succ_mono** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] [inst_2 : SuccO
rder α], Monotone WithBot.succ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Order.succ_le_succ`：succ_le_succ (h : a <= b) : succ a <= succ b
-/
lemma succ_mono : Monotone (succ : WithBot α → α)
  | ⊥, _, _ => by simp
  | (a : α), ⊥, hab => by simp at hab
  | (a : α), (b : α), hab => Order.succ_le_succ (by simpa using hab)
/-
**WithBot.succ_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] [inst_2 : SuccO
rder α] [NoMaxOrder α],   StrictMono WithBot.succ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Order.succ_lt_succ`：succ_lt_succ (hab : a < b) : succ a < succ b
-/
lemma succ_strictMono [NoMaxOrder α] : StrictMono (succ : WithBot α → α)
  | ⊥, (b : α), hab => by simp
  | (a : α), (b : α), hab => Order.succ_lt_succ (by simpa using hab)
/-
**WithBot.succ_le_succ** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] [inst_2 : SuccO
rder α] {x y : WithBot α},   x ≤ y → x.succ ≤ y.succ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.succ_mono`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderB
ot α] [inst_2 : SuccOrder α], Monotone WithBot.succ
-/
@[gcongr] lemma succ_le_succ (hxy : x ≤ y) : x.succ ≤ y.succ := succ_mono hxy
/-
**WithBot.succ_lt_succ** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] [inst_2 : SuccO
rder α] {x y : WithBot α} [NoMaxOrder α],   x < y → x.succ < y.succ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.succ_strictMono`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : 
OrderBot α] [inst_2 : SuccOrder α] [NoMaxOrder α],   StrictMono WithBot.succ
-/
@[gcongr] lemma succ_lt_succ [NoMaxOrder α] (hxy : x < y) : x.succ < y.succ := succ_strictMono hxy

section LinearOrder

variable {α : Type*} [Nontrivial α] [LinearOrder α] [OrderBot α] [SuccOrder α]

@[simp]
/-
**WithBot.succ_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：succ_eq_bot (a : WithBot α) : WithBot.succ a = ⊥ ↔ a = ⊥
参数：a : WithBot α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `Order.succ_ne_bot`：succ_ne_bot (a : α) : succ a != ⊥
-/
theorem succ_eq_bot (a : WithBot α) : WithBot.succ a = ⊥ ↔ a = ⊥ := by
  cases a
  · simp
  · simpa [WithBot.succ_coe, WithBot.coe_ne_bot, iff_false] using Order.succ_ne_bot _

end LinearOrder
end WithBot

namespace WithTop
variable {α : Type*} [Preorder α] [OrderTop α] [PredOrder α] {x y : WithTop α}

/-- The predecessor of `a : WithTop α` as an element of `α`. -/
/-
**WithTop.pred** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：pred (a : WithTop α) : α
参数：a : WithTop α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predecessor of `a : WithTop α` as an element of `α`.
-/
def pred (a : WithTop α) : α := a.recTopCoe ⊤ Order.pred

/-- Not to be confused with `WithTop.orderPred_top`, which is about `Order.pred`. -/
/-
**WithTop.pred_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderTop α] [inst_2 : PredO
rder α], ⊤.pred = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Not to be confused with `WithTop.orderPred_top`, which is about `Order.pred`.
-/
@[simp] lemma pred_top : pred (⊤ : WithTop α) = ⊤ := rfl

/-- Not to be confused with `WithTop.orderPred_coe`, which is about `Order.pred`. -/
/-
**WithTop.pred_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderTop α] [inst_2 : PredO
rder α] (a : α), (↑a).pred = Order.pred a
参数：a : α；↑a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Not to be confused with `WithTop.orderPred_coe`, which is about `Order.pred`.
-/
@[simp] lemma pred_coe (a : α) : pred (a : WithTop α) = Order.pred a := rfl
/-
**WithTop.pred_eq_pred** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderTop α] [inst_2 : PredO
rder α] (a : WithTop α),   ↑a.pred = Order.pred a
参数：a : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Not to be confused with `WithTop.orderPred_coe`, which is about `Order.pred`.
-/
lemma pred_eq_pred : ∀ a : WithTop α, pred a = Order.pred a
  | ⊤ => rfl
  | (a : α) => rfl
/-
**WithTop.pred_mono** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderTop α] [inst_2 : PredO
rder α], Monotone WithTop.pred
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Order.pred_le_pred`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : PredO
rder α] {a b : α}, b ≤ a → Order.pred b ≤ Order.pred a
-/
lemma pred_mono : Monotone (pred : WithTop α → α)
  | _, ⊤, _ => by simp
  | ⊤, (a : α), hab => by simp at hab
  | (a : α), (b : α), hab => Order.pred_le_pred (by simpa using hab)
/-
**WithTop.pred_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderTop α] [inst_2 : PredO
rder α] [NoMinOrder α],   StrictMono WithTop.pred
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Order.pred_lt_pred`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : PredO
rder α] {a b : α} [NoMinOrder α],   b < a → Order.pred b < Order.pred a
-/
lemma pred_strictMono [NoMinOrder α] : StrictMono (pred : WithTop α → α)
  | (b : α), ⊤, hab => by simp
  | (a : α), (b : α), hab => Order.pred_lt_pred (by simpa using hab)
/-
**WithTop.pred_le_pred** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderTop α] [inst_2 : PredO
rder α] {x y : WithTop α},   x ≤ y → x.pred ≤ y.pred
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.pred_mono`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderT
op α] [inst_2 : PredOrder α], Monotone WithTop.pred
-/
@[gcongr] lemma pred_le_pred (hxy : x ≤ y) : x.pred ≤ y.pred := pred_mono hxy
/-
**WithTop.pred_lt_pred** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderTop α] [inst_2 : PredO
rder α] {x y : WithTop α} [NoMinOrder α],   x < y → x.pred < y.pred
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.pred_strictMono`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : 
OrderTop α] [inst_2 : PredOrder α] [NoMinOrder α],   StrictMono WithTop.pred
-/
@[gcongr] lemma pred_lt_pred [NoMinOrder α] (hxy : x < y) : x.pred < y.pred := pred_strictMono hxy

section LinearOrder

variable {α : Type*} [Nontrivial α] [LinearOrder α] [OrderTop α] [PredOrder α]

@[simp]
/-
**WithTop.pred_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：pred_eq_top (a : WithTop α) : WithTop.pred a = ⊤ ↔ a = ⊤
参数：a : WithTop α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pred_eq_top (a : WithTop α) : WithTop.pred a = ⊤ ↔ a = ⊤ := by
  cases a <;> simp [Order.pred_ne_top]

end LinearOrder
end WithTop

