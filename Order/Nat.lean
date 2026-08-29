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

/--
Instance `instOrderBot` / 实例 `instOrderBot`

English:
instance instOrderBot
  signature: : OrderBot Nat where
  body: 0
  bot_le := zero_le

中文:
实例 instOrderBot
  签名: : 有底序 自然数 where
  定义体: 0
  bot_le := zero_le
-/
instance instOrderBot : OrderBot Nat where
  bot := 0
  bot_le := zero_le

/--
Instance `instNoMaxOrder` / 实例 `instNoMaxOrder`

English:
instance instNoMaxOrder
  signature: : NoMaxOrder Nat where
  body: ⟨n + 1, n.lt_succ_self⟩

中文:
实例 instNoMaxOrder
  签名: : NoMax序 自然数 where
  定义体: ⟨n + 1, n.lt_succ_self⟩

Depends on / 依赖: lt_succ_self, n.lt_succ_self
-/
instance instNoMaxOrder : NoMaxOrder Nat where
  exists_gt n := ⟨n + 1, n.lt_succ_self⟩


/--
lemma `bot_eq_zero` / 引理 `bot_eq_zero`

English:
lemma bot_eq_zero
  statement: ⊥ = 0
  proof: rfl

中文:
引理 bot_eq_zero
  结论: ⊥ = 0
  证明: rfl
-/
@[simp high] protected lemma bot_eq_zero : ⊥ = 0 := rfl

/--
lemma `isLeast_find` / 引理 `isLeast_find`

English:
lemma isLeast_find
  given: {p : Nat -> Prop} [DecidablePred p] (hp : exists n, p n)
  proof: ⟨Nat.find_spec hp, fun _ => Nat.find_min' hp⟩

中文:
引理 isLeast_find
  条件: {p : 自然数 -> 命题} [DecidablePred p] (hp : 存在 n, p n)
  证明: ⟨Nat.find_spec hp, fun _ => Nat.find_min' hp⟩

Depends on / 依赖: Nat.find_min, Nat.find_spec, find_min, find_spec
-/
lemma isLeast_find {p : Nat -> Prop} [DecidablePred p] (hp : exists n, p n) :
    IsLeast {n | p n} (Nat.find hp) :=
  ⟨Nat.find_spec hp, fun _ => Nat.find_min' hp⟩

end Nat

/--
lemma `Set.Nonempty.isLeast_natFind` / 引理 `Set.Nonempty.isLeast_natFind`

English:
lemma Set.Nonempty.isLeast_natFind
  given: {s : Set Nat} [DecidablePred (· in s)] (hs : s.Nonempty)
  proof: Nat.isLeast_find hs

中文:
引理 集合.非空.isLeast_natFind
  条件: {s : 集合 自然数} [DecidablePred (· in s)] (hs : s.非空)
  证明: Nat.isLeast_find hs

Depends on / 依赖: Nat.isLeast_find, isLeast_find
-/
lemma Set.Nonempty.isLeast_natFind {s : Set Nat} [DecidablePred (· in s)] (hs : s.Nonempty) :
    IsLeast s (Nat.find hs) :=
  Nat.isLeast_find hs
