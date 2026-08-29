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

/--
lemma `succ_natCast` / 引理 `succ_natCast`

English:
lemma succ_natCast
  given: (n : Nat)
  statement: succ (n : WithBot α) = n + 1
  proof: by
  rw [← WithBot.coe_natCast]; rw [succ_coe]; rw [Order.succ_eq_add_one]

中文:
引理 succ_natCast
  条件: (n : 自然数)
  结论: succ (n : WithBot α) = n + 1
  证明: by
  rw [← WithBot.coe_natCast]; rw [succ_coe]; rw [Order.succ_eq_add_one]

Depends on / 依赖: Order.succ_eq_add_one, WithBot, WithBot.coe_natCast, coe_natCast, succ_coe, succ_eq_add_one
-/
lemma succ_natCast (n : Nat) : succ (n : WithBot α) = n + 1 := by
  rw [← WithBot.coe_natCast]; rw [succ_coe]; rw [Order.succ_eq_add_one]

/--
lemma `succ_zero` / 引理 `succ_zero`

English:
lemma succ_zero
  statement: succ (0 : WithBot α) = 1
  proof: by simpa using succ_natCast (α := α) 0

@[simp]

中文:
引理 succ_zero
  结论: succ (0 : WithBot α) = 1
  证明: by simpa using succ_natCast (α := α) 0

@[simp]
-/
@[simp] lemma succ_zero : succ (0 : WithBot α) = 1 := by simpa using succ_natCast (α := α) 0

@[simp]
/--
lemma `succ_one` / 引理 `succ_one`

English:
lemma succ_one
  statement: succ (1 : WithBot α) = 2
  proof: by
  simpa [one_add_one_eq_two] using succ_natCast (α := α) 1

@[simp]

中文:
引理 succ_one
  结论: succ (1 : WithBot α) = 2
  证明: by
  simpa [one_add_one_eq_two] using succ_natCast (α := α) 1

@[simp]

Depends on / 依赖: one_add_one_eq_two, succ_natCast
-/
lemma succ_one : succ (1 : WithBot α) = 2 := by
  simpa [one_add_one_eq_two] using succ_natCast (α := α) 1

@[simp]
/--
lemma `succ_ofNat` / 引理 `succ_ofNat`

English:
lemma succ_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: succ_natCast n

中文:
引理 succ_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: succ_natCast n

Depends on / 依赖: succ_natCast
-/
lemma succ_ofNat (n : Nat) [n.AtLeastTwo] :
    succ (ofNat(n) : WithBot α) = ofNat(n) + 1 := succ_natCast n

/--
lemma `one_le_iff_pos` / 引理 `one_le_iff_pos`

English:
lemma one_le_iff_pos
  statement: {α : Type*} [PartialOrder α] [AddMonoidWithOne α]
  proof: by
  cases a <;> simp [Order.one_le_iff_pos]

中文:
引理 one_le_iff_pos
  结论: {α : 类型} [偏序 α] [加法带幺幺半群 α]
  证明: by
  cases a <;> simp [Order.one_le_iff_pos]

Depends on / 依赖: Order.one_le_iff_pos, one_le_iff_pos
-/
lemma one_le_iff_pos {α : Type*} [PartialOrder α] [AddMonoidWithOne α]
    [ZeroLEOneClass α] [NeZero (1 : α)] [SuccAddOrder α] (a : WithBot α) : 1 <= a ↔ 0 < a := by
  cases a <;> simp [Order.one_le_iff_pos]

end WithBot
