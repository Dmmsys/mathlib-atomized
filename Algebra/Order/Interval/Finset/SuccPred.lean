/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Order.Interval.Finset.SuccPred

/-!
# Finset intervals in an additive successor-predecessor order

This file proves relations between the various finset intervals in an additive successor/predecessor
order.

## Notes

Please keep in sync with:
* `Mathlib/Algebra/Order/Interval/Set/SuccPred.lean`
* `Mathlib/Order/Interval/Finset/SuccPred.lean`
* `Mathlib/Order/Interval/Set/SuccPred.lean`

## TODO

Copy over `insert` lemmas from `Mathlib/Order/Interval/Finset/Nat.lean`.
-/

public section

open Function Order OrderDual

variable {ι α : Type*}

namespace Finset
variable [LinearOrder α] [One α]

/-! ### Two-sided intervals -/

section LocallyFiniteOrder
variable [LocallyFiniteOrder α]

section SuccAddOrder
variable [Add α] [SuccAddOrder α] {a b : α}

/-!
#### Orders possibly with maximal elements

##### Equalities of intervals
-/

/-
**Finset.Ico_add_one_left_eq_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ico_add_one_left_eq_Ioo (a b : α) : Ico (a + 1) b = Ioo a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.Ico_succ_left_eq_Ioo`：Ico_succ_left_eq_Ioo (a b : α) : Ico (succ 
a) b = Ioo a b

--- 原说明 ---
#### Orders possibly with maximal elements

##### Equalities of intervals
-/
lemma Ico_add_one_left_eq_Ioo (a b : α) : Ico (a + 1) b = Ioo a b := by
  simpa [succ_eq_add_one] using Ico_succ_left_eq_Ioo a b
/-
**Finset.Icc_add_one_left_eq_Ioc_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Finset`
。
形式化陈述：Icc_add_one_left_eq_Ioc_of_not_isMax (ha : ¬ IsMax a) (b : α) : Icc (a + 1
) b = Ioc a b
参数：ha : ¬ IsMax a；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.Icc_succ_left_eq_Ioc_of_not_isMax`：Icc_succ_left_eq_Ioc_of_not_is
Max (ha : ¬ IsMax a) (b : α) : Icc (succ a) b = Ioc a b
-/
lemma Icc_add_one_left_eq_Ioc_of_not_isMax (ha : ¬ IsMax a) (b : α) : Icc (a + 1) b = Ioc a b := by
  simpa [succ_eq_add_one] using Icc_succ_left_eq_Ioc_of_not_isMax ha b
/-
**Finset.Ico_add_one_right_eq_Icc_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Finset
`。
形式化陈述：Ico_add_one_right_eq_Icc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ico a (b 
+ 1) = Icc a b
参数：hb : ¬ IsMax b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.Ico_succ_right_eq_Icc_of_not_isMax`：Ico_succ_right_eq_Icc_of_not_
isMax (hb : ¬ IsMax b) (a : α) : Ico a (succ b) = Icc a b
-/
lemma Ico_add_one_right_eq_Icc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ico a (b + 1) = Icc a b := by
  simpa [succ_eq_add_one] using Ico_succ_right_eq_Icc_of_not_isMax hb a
/-
**Finset.Ioo_add_one_right_eq_Ioc_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Finset
`。
形式化陈述：Ioo_add_one_right_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ioo a (b 
+ 1) = Ioc a b
参数：hb : ¬ IsMax b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.Ioo_succ_right_eq_Ioc_of_not_isMax`：Ioo_succ_right_eq_Ioc_of_not_
isMax (hb : ¬ IsMax b) (a : α) : Ioo a (succ b) = Ioc a b
-/
lemma Ioo_add_one_right_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ioo a (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ioo_succ_right_eq_Ioc_of_not_isMax hb a
/-
**Finset.Ico_add_one_add_one_eq_Ioc_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Fins
et`。
形式化陈述：Ico_add_one_add_one_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ico (a 
+ 1) (b + 1) = Ioc a b
参数：hb : ¬ IsMax b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.Ico_succ_succ_eq_Ioc_of_not_isMax`：Ico_succ_succ_eq_Ioc_of_not_is
Max (hb : ¬ IsMax b) (a : α) : Ico (succ a) (succ b) = Ioc a b
-/
lemma Ico_add_one_add_one_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) :
    Ico (a + 1) (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ico_succ_succ_eq_Ioc_of_not_isMax hb a

/-! ##### Inserting into intervals -/

/-
**Finset.insert_Icc_add_one_left_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Icc_add_one_left_eq_Icc (h : a <= b) : insert a (Icc (a + 1) b) = I
cc a b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.insert_Icc_succ_left_eq_Icc`：insert_Icc_succ_left_eq_Icc (h : a <
= b) : insert a (Icc (succ a) b) = Icc a b

--- 原说明 ---
##### Inserting into intervals
-/
lemma insert_Icc_add_one_left_eq_Icc (h : a ≤ b) : insert a (Icc (a + 1) b) = Icc a b := by
  simpa [succ_eq_add_one] using insert_Icc_succ_left_eq_Icc h
/-
**Finset.insert_Icc_right_eq_Icc_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Icc_right_eq_Icc_add_one (h : a <= b + 1) : insert (b + 1) (Icc a b
) = Icc a (b + 1)
参数：h : a <= b + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.insert_Icc_right_eq_Icc_succ`：insert_Icc_right_eq_Icc_succ (h : a
 <= succ b) : insert (succ b) (Icc a b) = Icc a (succ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
-/
lemma insert_Icc_right_eq_Icc_add_one (h : a ≤ b + 1) :
    insert (b + 1) (Icc a b) = Icc a (b + 1) := by
  simpa [← succ_eq_add_one] using insert_Icc_right_eq_Icc_succ (succ_eq_add_one b ▸ h)
/-
**Finset.insert_Ico_right_eq_Ico_add_one_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 
`Finset`。
形式化陈述：insert_Ico_right_eq_Ico_add_one_of_not_isMax (h : a <= b) (hb : ¬ IsMax b)
 : insert b (Ico a b) = Ico a (b + 1)
参数：h : a <= b；hb : ¬ IsMax b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.insert_Ico_right_eq_Ico_succ_of_not_isMax`：insert_Ico_right_eq_Ic
o_succ_of_not_isMax (h : a <= b) (hb : ¬ IsMax b) : insert b (Ico a b) = Ico a (
succ b)
-/
lemma insert_Ico_right_eq_Ico_add_one_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert b (Ico a b) = Ico a (b + 1) := by
  simpa [succ_eq_add_one] using insert_Ico_right_eq_Ico_succ_of_not_isMax h hb
/-
**Finset.insert_Ico_add_one_left_eq_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Ico_add_one_left_eq_Ico (h : a < b) : insert a (Ico (a + 1) b) = Ic
o a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.insert_Ico_succ_left_eq_Ico`：insert_Ico_succ_left_eq_Ico (h : a <
 b) : insert a (Ico (succ a) b) = Ico a b
-/
lemma insert_Ico_add_one_left_eq_Ico (h : a < b) : insert a (Ico (a + 1) b) = Ico a b := by
  simpa [succ_eq_add_one] using insert_Ico_succ_left_eq_Ico h
/-
**Finset.insert_Ioc_right_eq_Ioc_add_one_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 
`Finset`。
形式化陈述：insert_Ioc_right_eq_Ioc_add_one_of_not_isMax (h : a <= b) (hb : ¬ IsMax b)
 : insert (b + 1) (Ioc a b) = Ioc a (b + 1)
参数：h : a <= b；hb : ¬ IsMax b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.insert_Ioc_right_eq_Ioc_succ_of_not_isMax`：insert_Ioc_right_eq_Io
c_succ_of_not_isMax (h : a <= b) (hb : ¬ IsMax b) : insert (succ b) (Ioc a b) = 
Ioc a (succ b)
-/
lemma insert_Ioc_right_eq_Ioc_add_one_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert (b + 1) (Ioc a b) = Ioc a (b + 1) := by
  simpa [succ_eq_add_one] using insert_Ioc_right_eq_Ioc_succ_of_not_isMax h hb
/-
**Finset.insert_Ioc_add_one_left_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Ioc_add_one_left_eq_Ioc (h : a < b) : insert (a + 1) (Ioc (a + 1) b
) = Ioc a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.insert_Ioc_succ_left_eq_Ioc`：insert_Ioc_succ_left_eq_Ioc (h : a <
 b) : insert (succ a) (Ioc (succ a) b) = Ioc a b
-/
lemma insert_Ioc_add_one_left_eq_Ioc (h : a < b) : insert (a + 1) (Ioc (a + 1) b) = Ioc a b := by
  simpa [succ_eq_add_one] using insert_Ioc_succ_left_eq_Ioc h

/-!
#### Orders with no maximal elements

##### Equalities of intervals
-/

variable [NoMaxOrder α]

/-
**Finset.Icc_add_one_left_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Icc_add_one_left_eq_Ioc (a b : α) : Icc (a + 1) b = Ioc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.Icc_succ_left_eq_Ioc`：Icc_succ_left_eq_Ioc (a b : α) : Icc (succ 
a) b = Ioc a b
-/
lemma Icc_add_one_left_eq_Ioc (a b : α) : Icc (a + 1) b = Ioc a b := by
  simpa [succ_eq_add_one] using Icc_succ_left_eq_Ioc a b
/-
**Finset.Ico_add_one_right_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ico_add_one_right_eq_Icc (a b : α) : Ico a (b + 1) = Icc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.Ico_succ_right_eq_Icc`：Ico_succ_right_eq_Icc (a b : α) : Ico a (s
ucc b) = Icc a b
-/
lemma Ico_add_one_right_eq_Icc (a b : α) : Ico a (b + 1) = Icc a b := by
  simpa [succ_eq_add_one] using Ico_succ_right_eq_Icc a b
/-
**Finset.Ioo_add_one_right_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioo_add_one_right_eq_Ioc (a b : α) : Ioo a (b + 1) = Ioc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.Ioo_succ_right_eq_Ioc`：Ioo_succ_right_eq_Ioc (a b : α) : Ioo a (s
ucc b) = Ioc a b
-/
lemma Ioo_add_one_right_eq_Ioc (a b : α) : Ioo a (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ioo_succ_right_eq_Ioc a b
/-
**Finset.Ico_add_one_add_one_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ico_add_one_add_one_eq_Ioc (a b : α) : Ico (a + 1) (b + 1) = Ioc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.Ico_succ_succ_eq_Ioc`：Ico_succ_succ_eq_Ioc (a b : α) : Ico (succ 
a) (succ b) = Ioc a b
-/
lemma Ico_add_one_add_one_eq_Ioc (a b : α) : Ico (a + 1) (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ico_succ_succ_eq_Ioc a b

/-! ##### Inserting into intervals -/

/-
**Finset.insert_Ico_right_eq_Ico_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Ico_right_eq_Ico_add_one (h : a <= b) : insert b (Ico a b) = Ico a 
(b + 1)
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.insert_Ico_right_eq_Ico_succ`：insert_Ico_right_eq_Ico_succ (h : a
 <= b) : insert b (Ico a b) = Ico a (succ b)

--- 原说明 ---
##### Inserting into intervals
-/
lemma insert_Ico_right_eq_Ico_add_one (h : a ≤ b) : insert b (Ico a b) = Ico a (b + 1) := by
  simpa [succ_eq_add_one] using insert_Ico_right_eq_Ico_succ h
/-
**Finset.insert_Ioc_right_eq_Ioc_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Ioc_right_eq_Ioc_add_one (h : a <= b) : insert (b + 1) (Ioc a b) = 
Ioc a (b + 1)
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.insert_Ioc_right_eq_Ioc_add_one_of_not_isMax`：insert_Ioc_right_eq
_Ioc_add_one_of_not_isMax (h : a <= b) (hb : ¬ IsMax b) : insert (b + 1) (Ioc a 
b) = Ioc a (b + 1)
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
lemma insert_Ioc_right_eq_Ioc_add_one (h : a ≤ b) : insert (b + 1) (Ioc a b) = Ioc a (b + 1) :=
  insert_Ioc_right_eq_Ioc_add_one_of_not_isMax h (not_isMax _)

end SuccAddOrder

section PredSubOrder
variable [Sub α] [PredSubOrder α] {a b : α}

/-!
#### Orders possibly with minimal elements

##### Equalities of intervals
-/

/-
**Finset.Ioc_sub_one_right_eq_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioc_sub_one_right_eq_Ioo (a b : α) : Ioc a (b - 1) = Ioo a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.Ioc_pred_right_eq_Ioo`：Ioc_pred_right_eq_Ioo (a b : α) : Ioc a (p
red b) = Ioo a b

--- 原说明 ---
#### Orders possibly with minimal elements

##### Equalities of intervals
-/
lemma Ioc_sub_one_right_eq_Ioo (a b : α) : Ioc a (b - 1) = Ioo a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_right_eq_Ioo a b
/-
**Finset.Icc_sub_one_right_eq_Ico_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Finset
`。
形式化陈述：Icc_sub_one_right_eq_Ico_of_not_isMin (hb : ¬ IsMin b) (a : α) : Icc a (b 
- 1) = Ico a b
参数：hb : ¬ IsMin b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.Icc_pred_right_eq_Ico_of_not_isMin`：Icc_pred_right_eq_Ico_of_not_
isMin (hb : ¬ IsMin b) (a : α) : Icc a (pred b) = Ico a b
-/
lemma Icc_sub_one_right_eq_Ico_of_not_isMin (hb : ¬ IsMin b) (a : α) : Icc a (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Icc_pred_right_eq_Ico_of_not_isMin hb a
/-
**Finset.Ioc_sub_one_left_eq_Icc_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Finset`
。
形式化陈述：Ioc_sub_one_left_eq_Icc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioc (a - 1
) b = Icc a b
参数：ha : ¬ IsMin a；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.Ioc_pred_left_eq_Icc_of_not_isMin`：Ioc_pred_left_eq_Icc_of_not_is
Min (ha : ¬ IsMin a) (b : α) : Ioc (pred a) b = Icc a b
-/
lemma Ioc_sub_one_left_eq_Icc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioc (a - 1) b = Icc a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_left_eq_Icc_of_not_isMin ha b
/-
**Finset.Ioo_sub_one_left_eq_Ioc_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Finset`
。
形式化陈述：Ioo_sub_one_left_eq_Ioc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioo (a - 1
) b = Ico a b
参数：ha : ¬ IsMin a；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.Ioo_pred_left_eq_Ioc_of_not_isMin`：Ioo_pred_left_eq_Ioc_of_not_is
Min (ha : ¬ IsMin a) (b : α) : Ioo (pred a) b = Ico a b
-/
lemma Ioo_sub_one_left_eq_Ioc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioo (a - 1) b = Ico a b := by
  simpa [pred_eq_sub_one] using Ioo_pred_left_eq_Ioc_of_not_isMin ha b
/-
**Finset.Ioc_sub_one_sub_one_eq_Ico_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Fins
et`。
形式化陈述：Ioc_sub_one_sub_one_eq_Ico_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioc (a 
- 1) (b - 1) = Ico a b
参数：ha : ¬ IsMin a；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.Ioc_pred_pred_eq_Ico_of_not_isMin`：Ioc_pred_pred_eq_Ico_of_not_is
Min (ha : ¬ IsMin a) (b : α) : Ioc (pred a) (pred b) = Ico a b
-/
lemma Ioc_sub_one_sub_one_eq_Ico_of_not_isMin (ha : ¬ IsMin a) (b : α) :
    Ioc (a - 1) (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_pred_eq_Ico_of_not_isMin ha b

/-! ##### Inserting into intervals -/

/-
**Finset.insert_Icc_sub_one_right_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Icc_sub_one_right_eq_Icc (h : a <= b) : insert b (Icc a (b - 1)) = 
Icc a b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.insert_Icc_pred_right_eq_Icc`：insert_Icc_pred_right_eq_Icc (h : a
 <= b) : insert b (Icc a (pred b)) = Icc a b

--- 原说明 ---
##### Inserting into intervals
-/
lemma insert_Icc_sub_one_right_eq_Icc (h : a ≤ b) : insert b (Icc a (b - 1)) = Icc a b := by
  simpa [pred_eq_sub_one] using insert_Icc_pred_right_eq_Icc h
/-
**Finset.insert_Icc_left_eq_Icc_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Icc_left_eq_Icc_sub_one (h : a - 1 <= b) : insert (a - 1) (Icc a b)
 = Icc (a - 1) b
参数：h : a - 1 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.insert_Icc_left_eq_Icc_pred`：insert_Icc_left_eq_Icc_pred (h : pre
d a <= b) : insert (pred a) (Icc a b) = Icc (pred a) b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
-/
lemma insert_Icc_left_eq_Icc_sub_one (h : a - 1 ≤ b) :
    insert (a - 1) (Icc a b) = Icc (a - 1) b := by
  simpa [← pred_eq_sub_one] using insert_Icc_left_eq_Icc_pred (pred_eq_sub_one a ▸ h)
/-
**Finset.insert_Ioc_left_eq_Ioc_sub_one_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `
Finset`。
形式化陈述：insert_Ioc_left_eq_Ioc_sub_one_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) 
: insert a (Ioc a b) = Ioc (a - 1) b
参数：h : a <= b；ha : ¬ IsMin a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.insert_Ioc_left_eq_Ioc_pred_of_not_isMin`：insert_Ioc_left_eq_Ioc_
pred_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) : insert a (Ioc a b) = Ioc (pred
 a) b
-/
lemma insert_Ioc_left_eq_Ioc_sub_one_of_not_isMin (h : a ≤ b) (ha : ¬ IsMin a) :
    insert a (Ioc a b) = Ioc (a - 1) b := by
  simpa [pred_eq_sub_one] using insert_Ioc_left_eq_Ioc_pred_of_not_isMin h ha
/-
**Finset.insert_Ioc_sub_one_right_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Ioc_sub_one_right_eq_Ioc (h : a < b) : insert b (Ioc a (b - 1)) = I
oc a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.insert_Ioc_pred_right_eq_Ioc`：insert_Ioc_pred_right_eq_Ioc (h : a
 < b) : insert b (Ioc a (pred b)) = Ioc a b
-/
lemma insert_Ioc_sub_one_right_eq_Ioc (h : a < b) : insert b (Ioc a (b - 1)) = Ioc a b := by
  simpa [pred_eq_sub_one] using insert_Ioc_pred_right_eq_Ioc h
/-
**Finset.insert_Ico_left_eq_Ico_sub_one_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `
Finset`。
形式化陈述：insert_Ico_left_eq_Ico_sub_one_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) 
: insert (a - 1) (Ico a b) = Ico (a - 1) b
参数：h : a <= b；ha : ¬ IsMin a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.insert_Ico_left_eq_Ico_pred_of_not_isMin`：insert_Ico_left_eq_Ico_
pred_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) : insert (pred a) (Ico a b) = Ic
o (pred a) b
-/
lemma insert_Ico_left_eq_Ico_sub_one_of_not_isMin (h : a ≤ b) (ha : ¬ IsMin a) :
    insert (a - 1) (Ico a b) = Ico (a - 1) b := by
  simpa [pred_eq_sub_one] using insert_Ico_left_eq_Ico_pred_of_not_isMin h ha
/-
**Finset.insert_Ico_sub_one_right_eq_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Ico_sub_one_right_eq_Ico (h : a < b) : insert (b - 1) (Ico a (b - 1
)) = Ico a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.insert_Ico_pred_right_eq_Ico`：insert_Ico_pred_right_eq_Ico (h : a
 < b) : insert (pred b) (Ico a (pred b)) = Ico a b
-/
lemma insert_Ico_sub_one_right_eq_Ico (h : a < b) : insert (b - 1) (Ico a (b - 1)) = Ico a b := by
  simpa [pred_eq_sub_one] using insert_Ico_pred_right_eq_Ico h

/-!
#### Orders with no minimal elements

##### Equalities of intervals
-/

variable [NoMinOrder α]

/-
**Finset.Icc_sub_one_right_eq_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Icc_sub_one_right_eq_Ico (a b : α) : Icc a (b - 1) = Ico a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.Icc_pred_right_eq_Ico`：Icc_pred_right_eq_Ico (a b : α) : Icc a (p
red b) = Ico a b
-/
lemma Icc_sub_one_right_eq_Ico (a b : α) : Icc a (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Icc_pred_right_eq_Ico a b
/-
**Finset.Ioc_sub_one_left_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioc_sub_one_left_eq_Icc (a b : α) : Ioc (a - 1) b = Icc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.Ioc_pred_left_eq_Icc`：Ioc_pred_left_eq_Icc (a b : α) : Ioc (pred 
a) b = Icc a b
-/
lemma Ioc_sub_one_left_eq_Icc (a b : α) : Ioc (a - 1) b = Icc a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_left_eq_Icc a b
/-
**Finset.Ioo_sub_one_left_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioo_sub_one_left_eq_Ioc (a b : α) : Ioo (a - 1) b = Ico a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.Ioo_pred_left_eq_Ioc`：Ioo_pred_left_eq_Ioc (a b : α) : Ioo (pred 
a) b = Ico a b
-/
lemma Ioo_sub_one_left_eq_Ioc (a b : α) : Ioo (a - 1) b = Ico a b := by
  simpa [pred_eq_sub_one] using Ioo_pred_left_eq_Ioc a b
/-
**Finset.Ioc_sub_one_sub_one_eq_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioc_sub_one_sub_one_eq_Ico (a b : α) : Ioc (a - 1) (b - 1) = Ico a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.Ioc_pred_pred_eq_Ico`：Ioc_pred_pred_eq_Ico (a b : α) : Ioc (pred 
a) (pred b) = Ico a b
-/
lemma Ioc_sub_one_sub_one_eq_Ico (a b : α) : Ioc (a - 1) (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_pred_eq_Ico a b

/-! ##### Inserting into intervals -/

/-
**Finset.insert_Ioc_left_eq_Ioc_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Ioc_left_eq_Ioc_sub_one (h : a <= b) : insert a (Ioc a b) = Ioc (a 
- 1) b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.insert_Ioc_left_eq_Ioc_pred`：insert_Ioc_left_eq_Ioc_pred (h : a <
= b) : insert a (Ioc a b) = Ioc (pred a) b

--- 原说明 ---
##### Inserting into intervals
-/
lemma insert_Ioc_left_eq_Ioc_sub_one (h : a ≤ b) : insert a (Ioc a b) = Ioc (a - 1) b := by
  simpa [pred_eq_sub_one] using insert_Ioc_left_eq_Ioc_pred h
/-
**Finset.insert_Ico_left_eq_Ico_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：insert_Ico_left_eq_Ico_sub_one (h : a <= b) : insert (a - 1) (Ico a b) = I
co (a - 1) b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.insert_Ico_left_eq_Ico_sub_one_of_not_isMin`：insert_Ico_left_eq_I
co_sub_one_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) : insert (a - 1) (Ico a b)
 = Ico (a - 1) b
· 使用定理 `not_isMin`：not_isMin [NoMinOrder α] (a : α) : ¬IsMin a
-/
lemma insert_Ico_left_eq_Ico_sub_one (h : a ≤ b) : insert (a - 1) (Ico a b) = Ico (a - 1) b :=
  insert_Ico_left_eq_Ico_sub_one_of_not_isMin h (not_isMin _)

end PredSubOrder

section SuccAddPredSubOrder
variable [Add α] [Sub α] [SuccAddOrder α] [PredSubOrder α] [Nontrivial α]

/-
**Finset.Icc_add_one_sub_one_eq_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Icc_add_one_sub_one_eq_Ioo (a b : α) : Icc (a + 1) (b - 1) = Ioo a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.Icc_succ_pred_eq_Ioo`：Icc_succ_pred_eq_Ioo (a b : α) : Icc (succ 
a) (pred b) = Ioo a b
-/
lemma Icc_add_one_sub_one_eq_Ioo (a b : α) : Icc (a + 1) (b - 1) = Ioo a b := by
  simpa [succ_eq_add_one, pred_eq_sub_one] using Icc_succ_pred_eq_Ioo a b

end SuccAddPredSubOrder
end LocallyFiniteOrder

/-! ### One-sided interval towards `⊥` -/

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α]

section SuccAddOrder
variable [Add α] [SuccAddOrder α] {b : α}

/-
**Finset.Iio_add_one_eq_Iic_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Iio_add_one_eq_Iic_of_not_isMax (hb : ¬ IsMax b) : Iio (b + 1) = Iic b
参数：hb : ¬ IsMax b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.Iio_succ_eq_Iic_of_not_isMax`：Iio_succ_eq_Iic_of_not_isMax (hb : 
¬ IsMax b) : Iio (succ b) = Iic b
-/
lemma Iio_add_one_eq_Iic_of_not_isMax (hb : ¬ IsMax b) : Iio (b + 1) = Iic b := by
  simpa [succ_eq_add_one] using Iio_succ_eq_Iic_of_not_isMax hb

variable [NoMaxOrder α]
/-
**Finset.Iio_add_one_eq_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Iio_add_one_eq_Iic (b : α) : Iio (b + 1) = Iic b
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.Iio_succ_eq_Iic`：Iio_succ_eq_Iic (b : α) : Iio (succ b) = Iic b
-/
lemma Iio_add_one_eq_Iic (b : α) : Iio (b + 1) = Iic b := by
  simpa [succ_eq_add_one] using Iio_succ_eq_Iic b

end SuccAddOrder

section PredSubOrder
variable [Sub α] [PredSubOrder α] {a b : α}

/-
**Finset.Iic_sub_one_eq_Iio_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Iic_sub_one_eq_Iio_of_not_isMin (hb : ¬ IsMin b) : Iic (b - 1) = Iio b
参数：hb : ¬ IsMin b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.Iic_pred_eq_Iio_of_not_isMin`：Iic_pred_eq_Iio_of_not_isMin (hb : 
¬ IsMin b) : Iic (pred b) = Iio b
-/
lemma Iic_sub_one_eq_Iio_of_not_isMin (hb : ¬ IsMin b) : Iic (b - 1) = Iio b := by
  simpa [pred_eq_sub_one] using Iic_pred_eq_Iio_of_not_isMin hb

variable [NoMinOrder α]
/-
**Finset.Iic_sub_one_eq_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Iic_sub_one_eq_Iio (b : α) : Iic (b - 1) = Iio b
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.Iic_pred_eq_Iio`：Iic_pred_eq_Iio (b : α) : Iic (pred b) = Iio b
-/
lemma Iic_sub_one_eq_Iio (b : α) : Iic (b - 1) = Iio b := by
  simpa [pred_eq_sub_one] using Iic_pred_eq_Iio b

end PredSubOrder
end LocallyFiniteOrderBot

/-! ### One-sided interval towards `⊤` -/

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α]

section SuccAddOrder
variable [Add α] [SuccAddOrder α] {a : α}

/-
**Finset.Ici_add_one_eq_Ioi_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ici_add_one_eq_Ioi_of_not_isMax (ha : ¬ IsMax a) : Ici (a + 1) = Ioi a
参数：ha : ¬ IsMax a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.Ici_succ_eq_Ioi_of_not_isMax`：Ici_succ_eq_Ioi_of_not_isMax (ha : 
¬ IsMax a) : Ici (succ a) = Ioi a
-/
lemma Ici_add_one_eq_Ioi_of_not_isMax (ha : ¬ IsMax a) : Ici (a + 1) = Ioi a := by
  simpa [succ_eq_add_one] using Ici_succ_eq_Ioi_of_not_isMax ha

variable [NoMaxOrder α]
/-
**Finset.Ici_add_one_eq_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ici_add_one_eq_Ioi (a : α) : Ici (a + 1) = Ioi a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Finset.Ici_succ_eq_Ioi`：Ici_succ_eq_Ioi (a : α) : Ici (succ a) = Ioi a
-/
lemma Ici_add_one_eq_Ioi (a : α) : Ici (a + 1) = Ioi a := by
  simpa [succ_eq_add_one] using Ici_succ_eq_Ioi a

end SuccAddOrder

section PredSubOrder
variable [Sub α] [PredSubOrder α] {a a : α}

/-
**Finset.Ioi_sub_one_eq_Ici_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioi_sub_one_eq_Ici_of_not_isMin (ha : ¬ IsMin a) : Ioi (a - 1) = Ici a
参数：ha : ¬ IsMin a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.Ioi_pred_eq_Ici_of_not_isMin`：Ioi_pred_eq_Ici_of_not_isMin (ha : 
¬ IsMin a) : Ioi (pred a) = Ici a
-/
lemma Ioi_sub_one_eq_Ici_of_not_isMin (ha : ¬ IsMin a) : Ioi (a - 1) = Ici a := by
  simpa [pred_eq_sub_one] using Ioi_pred_eq_Ici_of_not_isMin ha

variable [NoMinOrder α]
/-
**Finset.Ioi_sub_one_eq_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioi_sub_one_eq_Ici (a : α) : Ioi (a - 1) = Ici a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `Finset.Ioi_pred_eq_Ici`：Ioi_pred_eq_Ici (a : α) : Ioi (pred a) = Ici a
-/
lemma Ioi_sub_one_eq_Ici (a : α) : Ioi (a - 1) = Ici a := by
  simpa [pred_eq_sub_one] using Ioi_pred_eq_Ici a

end PredSubOrder
end LocallyFiniteOrderTop
end Finset

