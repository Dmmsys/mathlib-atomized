/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Order.SuccPred.WithBot

/-!
# Algebraic properties of the successor function on `WithBot`
-/

public section

namespace WithBot
variable {α : Type*} [Preorder α] [OrderBot α] [AddMonoidWithOne α] [SuccAddOrder α]

/-
**WithBot.succ_natCast** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：succ_natCast (n : Nat) : succ (n : WithBot α) = n + 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_natCast`：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ),
 ↑↑n = ↑n
· 使用定理 `WithBot.succ_coe`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBo
t α] [inst_2 : SuccOrder α] (a : α), (↑a).succ = Order.succ a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
-/
lemma succ_natCast (n : ℕ) : succ (n : WithBot α) = n + 1 := by
  rw [← WithBot.coe_natCast, succ_coe, Order.succ_eq_add_one]
/-
**WithBot.succ_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] [inst_2 : AddMo
noidWithOne α] [inst_3 : SuccAddOrder α],   WithBot.succ 0 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `WithBot.succ_natCast`：succ_natCast (n : Nat) : succ (n : WithBot α) = n 
+ 1
-/
@[simp] lemma succ_zero : succ (0 : WithBot α) = 1 := by simpa using succ_natCast (α := α) 0

@[simp]
/-
**WithBot.succ_one** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：succ_one : succ (1 : WithBot α) = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用引理 `WithBot.succ_natCast`：succ_natCast (n : Nat) : succ (n : WithBot α) = n 
+ 1
-/
lemma succ_one : succ (1 : WithBot α) = 2 := by
  simpa [one_add_one_eq_two] using succ_natCast (α := α) 1

@[simp]
/-
**WithBot.succ_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：succ_ofNat (n : Nat) [n.AtLeastTwo] : succ (ofNat(n) : WithBot α) = ofNat(
n) + 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.succ_natCast`：succ_natCast (n : Nat) : succ (n : WithBot α) = n 
+ 1
-/
lemma succ_ofNat (n : ℕ) [n.AtLeastTwo] :
    succ (ofNat(n) : WithBot α) = ofNat(n) + 1 := succ_natCast n
/-
**WithBot.one_le_iff_pos** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：one_le_iff_pos {α : Type*} [PartialOrder α] [AddMonoidWithOne α] [ZeroLEOn
eClass α] [NeZero (1 : α)] [SuccAddOrder α] (a : WithBot α) : 1 <= a ↔ 0 < a
参数：1 : α；a : WithBot α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma one_le_iff_pos {α : Type*} [PartialOrder α] [AddMonoidWithOne α]
    [ZeroLEOneClass α] [NeZero (1 : α)] [SuccAddOrder α] (a : WithBot α) : 1 ≤ a ↔ 0 < a := by
  cases a <;> simp [Order.one_le_iff_pos]

end WithBot

