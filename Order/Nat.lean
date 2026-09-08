/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Find
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Bounds.Defs

/-!
# The natural numbers form a linear order

This file contains the linear order instance on the natural numbers.

See note [foundational algebra order theory].

## TODO

Move the `LinearOrder ℕ` instance here (https://github.com/leanprover-community/mathlib4/pull/13092).
-/

public section

namespace Nat

/-
**Nat.instOrderBot** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instOrderBot : OrderBot Nat where bot
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
instance instOrderBot : OrderBot ℕ where
  bot := 0
  bot_le := zero_le
/-
**Nat.instNoMaxOrder** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instNoMaxOrder : NoMaxOrder Nat where exists_gt n
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
instance instNoMaxOrder : NoMaxOrder ℕ where
  exists_gt n := ⟨n + 1, n.lt_succ_self⟩

/-! ### Miscellaneous lemmas -/

/-
**Nat.bot_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：⊥ = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Miscellaneous lemmas
-/
@[simp high] protected lemma bot_eq_zero : ⊥ = 0 := rfl

/-- `Nat.find` is the minimum natural number satisfying a predicate `p`. -/
/-
**Nat.isLeast_find** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：isLeast_find {p : Nat -> Prop} [DecidablePred p] (hp : exists n, p n) : Is
Least {n | p n} (Nat.find hp)
参数：hp : exists n, p n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m

--- 原说明 ---
`Nat.find` is the minimum natural number satisfying a predicate `p`.
-/
lemma isLeast_find {p : ℕ → Prop} [DecidablePred p] (hp : ∃ n, p n) :
    IsLeast {n | p n} (Nat.find hp) :=
  ⟨Nat.find_spec hp, fun _ ↦ Nat.find_min' hp⟩

end Nat

/-- `Nat.find` is the minimum element of a nonempty set of natural numbers. -/
/-
**Set.Nonempty.isLeast_natFind** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Nonempty.isLeast_natFind {s : Set Nat} [DecidablePred (· in s)] (hs : 
s.Nonempty) : IsLeast s (Nat.find hs)
参数：· in s；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.isLeast_find`：isLeast_find {p : Nat -> Prop} [DecidablePred p] (hp :
 exists n, p n) : IsLeast {n | p n} (Nat.find hp)

--- 原说明 ---
`Nat.find` is the minimum element of a nonempty set of natural numbers.
-/
lemma Set.Nonempty.isLeast_natFind {s : Set ℕ} [DecidablePred (· ∈ s)] (hs : s.Nonempty) :
    IsLeast s (Nat.find hs) :=
  Nat.isLeast_find hs
