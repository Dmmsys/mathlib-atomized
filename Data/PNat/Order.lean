/-
Copyright (c) 2025 Javier Burroni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Javier Burroni
-/
module

public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.PNat.Basic

/-!
# Order related instances for `ℕ+`
-/

public section

namespace PNat
open Nat

/--
Instance `instSuccOrder` / 实例 `instSuccOrder`

English:
instance instSuccOrder
  signature: : SuccOrder Nat+
  body: .ofSuccLeIff (· + 1) Iff.rfl

中文:
实例 instSuccOrder
  签名: : SuccOrder 自然数+
  定义体: .ofSuccLeIff (· + 1) Iff.rfl

Depends on / 依赖: Iff.rfl, ofSuccLeIff
-/
instance instSuccOrder : SuccOrder Nat+ :=
  .ofSuccLeIff (· + 1) Iff.rfl

/--
Instance `instSuccAddOrder` / 实例 `instSuccAddOrder`

English:
instance instSuccAddOrder
  signature: : SuccAddOrder Nat+ where
  body: rfl

中文:
实例 instSuccAddOrder
  签名: : SuccAddOrder 自然数+ where
  定义体: rfl
-/
instance instSuccAddOrder : SuccAddOrder Nat+ where
  succ_eq_add_one _ := rfl

/--
Instance `instNoMaxOrder` / 实例 `instNoMaxOrder`

English:
instance instNoMaxOrder
  signature: : NoMaxOrder Nat+ where
  body: ⟨n + 1, lt_succ_self n⟩

@[simp]

中文:
实例 instNoMaxOrder
  签名: : NoMaxOrder 自然数+ where
  定义体: ⟨n + 1, lt_succ_self n⟩

@[simp]

Depends on / 依赖: lt_succ_self
-/
instance instNoMaxOrder : NoMaxOrder Nat+ where
  exists_gt n := ⟨n + 1, lt_succ_self n⟩

@[simp]
/--
lemma `succ_eq_add_one` / 引理 `succ_eq_add_one`

English:
lemma succ_eq_add_one
  given: (n : Nat+)
  statement: Order.succ n = n + 1
  proof: rfl

中文:
引理 succ_eq_add_one
  条件: (n : 自然数+)
  结论: Order.succ n = n + 1
  证明: rfl
-/
lemma succ_eq_add_one (n : Nat+) : Order.succ n = n + 1 := rfl

end PNat
