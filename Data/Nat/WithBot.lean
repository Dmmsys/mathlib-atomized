/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Nat.Cast.WithTop
public import Mathlib.Order.Nat

/-!
# `WithBot ℕ`

Lemmas about the type of natural numbers with a bottom element adjoined.
-/

public section


namespace Nat

namespace WithBot

/-
**Nat.WithBot.** 是 Mathlib 中的一个实例，位于命名空间 `Nat.WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WellFoundedRelation (WithBot ℕ) where
  rel := (· < ·)
  wf := IsWellFounded.wf
/-
**Nat.WithBot.add_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.WithBot`。
形式化陈述：add_eq_zero_iff {n m : WithBot Nat} : n + m = 0 ↔ n = 0 ∧ m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem add_eq_zero_iff {n m : WithBot ℕ} : n + m = 0 ↔ n = 0 ∧ m = 0 := by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add]
/-
**Nat.WithBot.add_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.WithBot`。
形式化陈述：add_eq_one_iff {n m : WithBot Nat} : n + m = 1 ↔ n = 0 ∧ m = 1 ∨ n = 1 ∧ m
 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem add_eq_one_iff {n m : WithBot ℕ} : n + m = 1 ↔ n = 0 ∧ m = 1 ∨ n = 1 ∧ m = 0 := by
  cases n
  · simp
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_one_iff]
/-
**Nat.WithBot.add_eq_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.WithBot`。
形式化陈述：add_eq_two_iff {n m : WithBot Nat} : n + m = 2 ↔ n = 0 ∧ m = 2 ∨ n = 1 ∧ m
 = 1 ∨ n = 2 ∧ m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem add_eq_two_iff {n m : WithBot ℕ} :
    n + m = 2 ↔ n = 0 ∧ m = 2 ∨ n = 1 ∧ m = 1 ∨ n = 2 ∧ m = 0 := by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_two_iff]
/-
**Nat.WithBot.add_eq_three_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.WithBot`。
形式化陈述：add_eq_three_iff {n m : WithBot Nat} : n + m = 3 ↔ n = 0 ∧ m = 3 ∨ n = 1 ∧
 m = 2 ∨ n = 2 ∧ m = 1 ∨ n = 3 ∧ m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem add_eq_three_iff {n m : WithBot ℕ} :
    n + m = 3 ↔ n = 0 ∧ m = 3 ∨ n = 1 ∧ m = 2 ∨ n = 2 ∧ m = 1 ∨ n = 3 ∧ m = 0 := by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_three_iff]
/-
**Nat.WithBot.coe_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Nat.WithBot`。
形式化陈述：coe_nonneg {n : Nat} : 0 <= (n : WithBot Nat)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_zero`：∀ {α : Type u} [inst : Zero α], ↑0 = 0
· 使用定理 `Nat.cast_withBot`：Nat.cast_withBot (n : Nat) : Nat.cast n = WithBot.some
 n
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem coe_nonneg {n : ℕ} : 0 ≤ (n : WithBot ℕ) := by
  rw [← WithBot.coe_zero, cast_withBot, WithBot.coe_le_coe]
  exact n.zero_le

@[simp]
/-
**Nat.WithBot.lt_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.WithBot`。
形式化陈述：lt_zero_iff {n : WithBot Nat} : n < 0 ↔ n = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.lt_coe_bot`：lt_coe_bot [OrderBot α] : x < (⊥ : α) ↔ x = ⊥
-/
theorem lt_zero_iff {n : WithBot ℕ} : n < 0 ↔ n = ⊥ := WithBot.lt_coe_bot
/-
**Nat.WithBot.one_le_iff_zero_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat.WithBot`。
形式化陈述：one_le_iff_zero_lt {x : WithBot Nat} : 1 <= x ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `not_lt_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {a 
: α}, ¬a < ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.coe_one`：∀ {α : Type u} [inst : One α], ↑1 = 1
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `WithBot.coe_zero`：∀ {α : Type u} [inst : Zero α], ↑0 = 0
-/
theorem one_le_iff_zero_lt {x : WithBot ℕ} : 1 ≤ x ↔ 0 < x := by
  refine ⟨zero_lt_one.trans_le, fun h => ?_⟩
  cases x
  · exact (not_lt_bot h).elim
  · rwa [← WithBot.coe_zero, WithBot.coe_lt_coe, ← Nat.add_one_le_iff, zero_add,
      ← WithBot.coe_le_coe, WithBot.coe_one] at h
/-
**Nat.WithBot.lt_one_iff_le_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat.WithBot`。
形式化陈述：lt_one_iff_le_zero {x : WithBot Nat} : x < 1 ↔ x <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.WithBot.one_le_iff_zero_lt`：one_le_iff_zero_lt {x : WithBot Nat} : 1
 <= x ↔ 0 < x
-/
theorem lt_one_iff_le_zero {x : WithBot ℕ} : x < 1 ↔ x ≤ 0 :=
  not_iff_not.mp (by simpa using one_le_iff_zero_lt)
/-
**Nat.WithBot.add_one_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat.WithBot`。
形式化陈述：add_one_le_of_lt {n m : WithBot Nat} (h : n < m) : n + 1 <= m
参数：h : n < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {a 
: α}, ¬a < ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.coe_one`：∀ {α : Type u} [inst : One α], ↑1 = 1
· 使用定理 `WithBot.coe_add`：∀ {α : Type u} [inst : Add α] (a b : α), ↑(a + b) = ↑a 
+ ↑b
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
-/
theorem add_one_le_of_lt {n m : WithBot ℕ} (h : n < m) : n + 1 ≤ m := by
  cases n
  · simp only [WithBot.bot_add, bot_le]
  cases m
  · exact (not_lt_bot h).elim
  · rwa [WithBot.coe_lt_coe, ← Nat.add_one_le_iff, ← WithBot.coe_le_coe, WithBot.coe_add,
      WithBot.coe_one] at h

end WithBot

end Nat

