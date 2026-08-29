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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WellFoundedRelation (WithBot Nat)
  body: (· < ·)
  wf := IsWellFounded.wf

中文:
实例 :
  签名: 良基关系 (WithBot 自然数)
  定义体: (· < ·)
  wf := IsWellFounded.wf
-/
instance : WellFoundedRelation (WithBot Nat) where
  rel := (· < ·)
  wf := IsWellFounded.wf

/--
theorem `add_eq_zero_iff` / 定理 `add_eq_zero_iff`

English:
theorem add_eq_zero_iff
  given: {n m : WithBot Nat}
  statement: n + m = 0 ↔ n = 0 ∧ m = 0
  proof: by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add]

中文:
定理 add_eq_zero_iff
  条件: {n m : WithBot 自然数}
  结论: n + m = 0 ↔ n = 0 ∧ m = 0
  证明: by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add]

Depends on / 依赖: WithBot, WithBot.add_bot, WithBot.bot_add, WithBot.coe_add, add_bot, bot_add, coe_add
-/
theorem add_eq_zero_iff {n m : WithBot Nat} : n + m = 0 ↔ n = 0 ∧ m = 0 := by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add]

/--
theorem `add_eq_one_iff` / 定理 `add_eq_one_iff`

English:
theorem add_eq_one_iff
  given: {n m : WithBot Nat}
  statement: n + m = 1 ↔ n = 0 ∧ m = 1 ∨ n = 1 ∧ m = 0
  proof: by
  cases n
  · simp
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_one_iff]

中文:
定理 add_eq_one_iff
  条件: {n m : WithBot 自然数}
  结论: n + m = 1 ↔ n = 0 ∧ m = 1 ∨ n = 1 ∧ m = 0
  证明: by
  cases n
  · simp
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_one_iff]

Depends on / 依赖: Nat.add_eq_one_iff, WithBot, WithBot.add_bot, WithBot.coe_add, add_bot, add_eq_one_iff, coe_add
-/
theorem add_eq_one_iff {n m : WithBot Nat} : n + m = 1 ↔ n = 0 ∧ m = 1 ∨ n = 1 ∧ m = 0 := by
  cases n
  · simp
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_one_iff]

/--
theorem `add_eq_two_iff` / 定理 `add_eq_two_iff`

English:
theorem add_eq_two_iff
  given: {n m : WithBot Nat}
  proof: by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_two_iff]

中文:
定理 add_eq_two_iff
  条件: {n m : WithBot 自然数}
  证明: by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_two_iff]

Depends on / 依赖: Nat.add_eq_two_iff, WithBot, WithBot.add_bot, WithBot.bot_add, WithBot.coe_add, add_bot, add_eq_two_iff, bot_add, coe_add
-/
theorem add_eq_two_iff {n m : WithBot Nat} :
    n + m = 2 ↔ n = 0 ∧ m = 2 ∨ n = 1 ∧ m = 1 ∨ n = 2 ∧ m = 0 := by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_two_iff]

/--
theorem `add_eq_three_iff` / 定理 `add_eq_three_iff`

English:
theorem add_eq_three_iff
  given: {n m : WithBot Nat}
  proof: by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_three_iff]

中文:
定理 add_eq_three_iff
  条件: {n m : WithBot 自然数}
  证明: by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_three_iff]

Depends on / 依赖: Nat.add_eq_three_iff, WithBot, WithBot.add_bot, WithBot.bot_add, WithBot.coe_add, add_bot, add_eq_three_iff, bot_add, coe_add
-/
theorem add_eq_three_iff {n m : WithBot Nat} :
    n + m = 3 ↔ n = 0 ∧ m = 3 ∨ n = 1 ∧ m = 2 ∨ n = 2 ∧ m = 1 ∨ n = 3 ∧ m = 0 := by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_three_iff]

/--
theorem `coe_nonneg` / 定理 `coe_nonneg`

English:
theorem coe_nonneg
  given: {n : Nat}
  statement: 0 <= (n : WithBot Nat)
  proof: by
  rw [← WithBot.coe_zero]; rw [cast_withBot]; rw [WithBot.coe_le_coe]
  exact n.zero_le

@[simp]

中文:
定理 coe_nonneg
  条件: {n : 自然数}
  结论: 0 <= (n : WithBot 自然数)
  证明: by
  rw [← WithBot.coe_zero]; rw [cast_withBot]; rw [WithBot.coe_le_coe]
  exact n.zero_le

@[simp]

Depends on / 依赖: WithBot, WithBot.coe_le_coe, WithBot.coe_zero, cast_withBot, coe_le_coe, coe_zero, n.zero_le, zero_le
-/
theorem coe_nonneg {n : Nat} : 0 <= (n : WithBot Nat) := by
  rw [← WithBot.coe_zero]; rw [cast_withBot]; rw [WithBot.coe_le_coe]
  exact n.zero_le

@[simp]
/--
theorem `lt_zero_iff` / 定理 `lt_zero_iff`

English:
theorem lt_zero_iff
  given: {n : WithBot Nat}
  statement: n < 0 ↔ n = ⊥
  proof: WithBot.lt_coe_bot

中文:
定理 lt_zero_iff
  条件: {n : WithBot 自然数}
  结论: n < 0 ↔ n = ⊥
  证明: WithBot.lt_coe_bot

Depends on / 依赖: WithBot, WithBot.lt_coe_bot, lt_coe_bot
-/
theorem lt_zero_iff {n : WithBot Nat} : n < 0 ↔ n = ⊥ := WithBot.lt_coe_bot

/--
theorem `one_le_iff_zero_lt` / 定理 `one_le_iff_zero_lt`

English:
theorem one_le_iff_zero_lt
  given: {x : WithBot Nat}
  statement: 1 <= x ↔ 0 < x
  proof: by
  refine ⟨zero_lt_one.trans_le, fun h => ?_⟩
  cases x
  · exact (not_lt_bot h).elim
  · rwa [← WithBot.coe_zero, WithBot.coe_lt_coe, ← Nat.add_one_le_iff, zero_add,
      ← WithBot.coe_le_coe, WithBot.coe_one] at h

中文:
定理 one_le_iff_zero_lt
  条件: {x : WithBot 自然数}
  结论: 1 <= x ↔ 0 < x
  证明: by
  refine ⟨zero_lt_one.trans_le, fun h => ?_⟩
  cases x
  · exact (not_lt_bot h).elim
  · rwa [← WithBot.coe_zero, WithBot.coe_lt_coe, ← Nat.add_one_le_iff, zero_add,
      ← WithBot.coe_le_coe, WithBot.coe_one] at h

Depends on / 依赖: Nat.add_one_le_iff, WithBot, WithBot.coe_le_coe, WithBot.coe_lt_coe, WithBot.coe_one, WithBot.coe_zero, add_one_le_iff, coe_le_coe, coe_lt_coe, coe_one, coe_zero, not_lt_bot, trans_le, zero_add, zero_lt_one, zero_lt_one.trans_le
-/
theorem one_le_iff_zero_lt {x : WithBot Nat} : 1 <= x ↔ 0 < x := by
  refine ⟨zero_lt_one.trans_le, fun h => ?_⟩
  cases x
  · exact (not_lt_bot h).elim
  · rwa [← WithBot.coe_zero, WithBot.coe_lt_coe, ← Nat.add_one_le_iff, zero_add,
      ← WithBot.coe_le_coe, WithBot.coe_one] at h

/--
theorem `lt_one_iff_le_zero` / 定理 `lt_one_iff_le_zero`

English:
theorem lt_one_iff_le_zero
  given: {x : WithBot Nat}
  statement: x < 1 ↔ x <= 0
  proof: not_iff_not.mp (by simpa using one_le_iff_zero_lt)

中文:
定理 lt_one_iff_le_zero
  条件: {x : WithBot 自然数}
  结论: x < 1 ↔ x <= 0
  证明: not_iff_not.mp (by simpa using one_le_iff_zero_lt)

Depends on / 依赖: not_iff_not, not_iff_not.mp, one_le_iff_zero_lt
-/
theorem lt_one_iff_le_zero {x : WithBot Nat} : x < 1 ↔ x <= 0 :=
  not_iff_not.mp (by simpa using one_le_iff_zero_lt)

/--
theorem `add_one_le_of_lt` / 定理 `add_one_le_of_lt`

English:
theorem add_one_le_of_lt
  given: {n m : WithBot Nat} (h : n < m)
  statement: n + 1 <= m
  proof: by
  cases n
  · simp only [WithBot.bot_add, bot_le]
  cases m
  · exact (not_lt_bot h).elim
  · rwa [WithBot.coe_lt_coe, ← Nat.add_one_le_iff, ← WithBot.coe_le_coe, WithBot.coe_add,
      WithBot.coe_one] at h

中文:
定理 add_one_le_of_lt
  条件: {n m : WithBot 自然数} (h : n < m)
  结论: n + 1 <= m
  证明: by
  cases n
  · simp only [WithBot.bot_add, bot_le]
  cases m
  · exact (not_lt_bot h).elim
  · rwa [WithBot.coe_lt_coe, ← Nat.add_one_le_iff, ← WithBot.coe_le_coe, WithBot.coe_add,
      WithBot.coe_one] at h

Depends on / 依赖: Nat.add_one_le_iff, WithBot, WithBot.bot_add, WithBot.coe_add, WithBot.coe_le_coe, WithBot.coe_lt_coe, WithBot.coe_one, add_one_le_iff, bot_add, bot_le, coe_add, coe_le_coe, coe_lt_coe, coe_one, not_lt_bot
-/
theorem add_one_le_of_lt {n m : WithBot Nat} (h : n < m) : n + 1 <= m := by
  cases n
  · simp only [WithBot.bot_add, bot_le]
  cases m
  · exact (not_lt_bot h).elim
  · rwa [WithBot.coe_lt_coe, ← Nat.add_one_le_iff, ← WithBot.coe_le_coe, WithBot.coe_add,
      WithBot.coe_one] at h

end WithBot

end Nat
