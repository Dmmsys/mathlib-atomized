/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Oliver Nash, Yaël Dillies
-/
module

public import Mathlib.Order.Circular
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.ZMod.Defs

/-!
# The circular order on `ZMod n`

This file defines the circular order on `ZMod n`.
-/

public section

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CircularOrder Int
  body: LinearOrder.toCircularOrder _

中文:
实例 :
  签名: CircularOrder 整数
  定义体: LinearOrder.toCircularOrder _

Depends on / 依赖: LinearOrder, LinearOrder.toCircularOrder, toCircularOrder
-/
instance : CircularOrder Int := LinearOrder.toCircularOrder _

variable {a b c : Int}

/--
lemma `Int.btw_iff` / 引理 `Int.btw_iff`

English:
lemma Int.btw_iff
  statement: btw a b c ↔ a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ a <= b
  proof: .rfl

中文:
引理 Int.btw_iff
  结论: btw a b c ↔ a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ a <= b
  证明: .rfl
-/
lemma Int.btw_iff : btw a b c ↔ a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ a <= b := .rfl
/--
lemma `Int.sbtw_iff` / 引理 `Int.sbtw_iff`

English:
lemma Int.sbtw_iff
  statement: sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
  proof: .rfl

中文:
引理 Int.sbtw_iff
  结论: sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
  证明: .rfl
-/
lemma Int.sbtw_iff : sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b := .rfl

instance (n : Nat) : CircularOrder (Fin n) := LinearOrder.toCircularOrder _

variable {n : Nat} {a b c : Fin n}

/--
lemma `Fin.btw_iff` / 引理 `Fin.btw_iff`

English:
lemma Fin.btw_iff
  statement: btw a b c ↔ a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ a <= b
  proof: .rfl

中文:
引理 Fin.btw_iff
  结论: btw a b c ↔ a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ a <= b
  证明: .rfl
-/
lemma Fin.btw_iff : btw a b c ↔ a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ a <= b := .rfl
/--
lemma `Fin.sbtw_iff` / 引理 `Fin.sbtw_iff`

English:
lemma Fin.sbtw_iff
  statement: sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
  proof: .rfl

中文:
引理 Fin.sbtw_iff
  结论: sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
  证明: .rfl
-/
lemma Fin.sbtw_iff : sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b := .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: forall (n : Nat), CircularOrder (ZMod n)

中文:
实例 :
  签名: 对任意 (n : 自然数), CircularOrder (ZMod n)
-/
instance : forall (n : Nat), CircularOrder (ZMod n)
| 0 => inferInstanceAs CircularOrder Int
| n + 1 => inferInstanceAs CircularOrder Fin n + 1
