/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Sub.Defs

/-!
# The naturals form a linear ordered monoid

This file contains the linear ordered monoid instance on the natural numbers.

See note [foundational algebra order theory].
-/

public section

namespace Nat

/-! ### Instances -/

/-
**Nat.instIsOrderedAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instIsOrderedAddMonoid : IsOrderedAddMonoid Nat where add_le_add_left
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.add_le_add_right`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), n + k ≤ m + k

--- 原说明 ---
### Instances
-/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid ℕ where
  add_le_add_left := @Nat.add_le_add_right
/-
**Nat.instIsOrderedCancelAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid Nat where add_le_a
dd_left
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.add_le_add_right`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), n + k ≤ m + k
· 使用定理 `Nat.le_of_add_le_add_left`：∀ {a b c : ℕ}, a + b ≤ a + c → b ≤ c
-/
instance instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid ℕ where
  add_le_add_left := @Nat.add_le_add_right
  le_of_add_le_add_left := @Nat.le_of_add_le_add_left
/-
**Nat.instCanonicallyOrderedAdd** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instCanonicallyOrderedAdd : CanonicallyOrderedAdd Nat where le_add_self
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
instance instCanonicallyOrderedAdd : CanonicallyOrderedAdd ℕ where
  le_add_self := Nat.le_add_left
  le_self_add := Nat.le_add_right
  exists_add_of_le := Nat.exists_eq_add_of_le
/-
**Nat.instOrderedSub** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instOrderedSub : OrderedSub Nat
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.succ_add`：∀ (n m : ℕ), n.succ + m = (n + m).succ
-/
instance instOrderedSub : OrderedSub ℕ := by
  refine ⟨fun m n k ↦ ?_⟩
  induction n generalizing k with
  | zero => simp
  | succ n ih => simp only [sub_succ, pred_le_iff, ih, succ_add, add_succ]

/-! ### Miscellaneous lemmas -/

variable {α : Type*} {n : ℕ} {f : α → ℕ}

/-- See also `pow_left_strictMonoOn₀`. -/
/-
**Nat.pow_left_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n ≠ 0 → StrictMono fun x => x ^ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pow_lt_pow_left`：∀ {a b n : ℕ}, a < b → n ≠ 0 → a ^ n < b ^ n

--- 原说明 ---
See also `pow_left_strictMonoOn₀`.
-/
protected lemma pow_left_strictMono (hn : n ≠ 0) : StrictMono (· ^ n : ℕ → ℕ) :=
  fun _ _ h ↦ Nat.pow_lt_pow_left h hn
/-
**Nat._root_.StrictMono.nat_pow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.StrictMono.nat_pow [Preorder α] (hn : n ≠ 0) (hf : StrictMono f) :
    StrictMono (f · ^ n) := (Nat.pow_left_strictMono hn).comp hf

end Nat

