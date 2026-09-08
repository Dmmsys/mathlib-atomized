/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Order.BooleanAlgebra.Set

/-!
# The natural numbers form an ordered semiring

This file contains the commutative linear ordered semiring instance on the natural numbers.

See note [foundational algebra order theory].
-/

public section

namespace Nat

/-! ### Instances -/

/-
**Nat.instIsStrictOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instIsStrictOrderedRing : IsStrictOrderedRing Nat where mul_lt_mul_of_pos_
left _a ha _b _c hbc
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_lt_mul_of_pos_left`：∀ {n m k : ℕ}, n < m → k > 0 → k * n < k * m
· 使用定理 `Nat.mul_lt_mul_of_pos_right`：∀ {n m k : ℕ}, n < m → k > 0 → n * k < m * 
k

--- 原说明 ---
### Instances
-/
instance instIsStrictOrderedRing : IsStrictOrderedRing ℕ where
  mul_lt_mul_of_pos_left _a ha _b _c hbc := Nat.mul_lt_mul_of_pos_left hbc ha
  mul_lt_mul_of_pos_right _a ha _b _c hbc := Nat.mul_lt_mul_of_pos_right hbc ha
/-
**Nat.instLinearOrderedCommMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instLinearOrderedCommMonoidWithZero : LinearOrderedCommMonoidWithZero Nat 
where bot
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
instance instLinearOrderedCommMonoidWithZero : LinearOrderedCommMonoidWithZero ℕ where
  bot := 0
  bot_le := zero_le
  isBot_zero := zero_le

/-! ### Miscellaneous lemmas -/

/-
**Nat.isCompl_even_odd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：isCompl_even_odd : IsCompl { n : Nat | Even n } { n | Odd n }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
### Miscellaneous lemmas
-/
lemma isCompl_even_odd : IsCompl { n : ℕ | Even n } { n | Odd n } := by
  simp only [← Set.compl_ofPred, isCompl_compl, ← not_even_iff_odd]

end Nat

