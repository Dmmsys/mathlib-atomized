/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Patrick Stevens
-/
module

public import Mathlib.Algebra.Order.Field.Basic

/-!
# Cast of naturals into ordered fields

This file concerns the canonical homomorphism `ℕ → F`, where `F` is a `LinearOrderedSemifield`.

## Main results

* `Nat.cast_div_le`: in all cases, `↑(m / n) ≤ ↑m / ↑ n`
-/

public section


namespace Nat

section LinearOrderedSemifield

variable {α : Type*} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]

/--
lemma `cast_inv_le_one` / 引理 `cast_inv_le_one`

English:
lemma cast_inv_le_one
  statement: forall n : Nat, (n⁻¹ : α) <= 1

中文:
引理 cast_inv_le_one
  结论: 对任意 n : 自然数, (n⁻¹ : α) <= 1
-/
lemma cast_inv_le_one : forall n : Nat, (n⁻¹ : α) <= 1
  | 0 => by simp
| n + 1 => inv_le_one_of_one_le₀ by simp [Nat.cast_nonneg]

/--
theorem `cast_div_le` / 定理 `cast_div_le`

English:
theorem cast_div_le
  given: {m n : Nat}
  statement: ((m / n : Nat) : α) <= m / n
  proof: by
  cases n
  · rw [cast_zero, div_zero, Nat.div_zero, cast_zero]
  rw [le_div_iff₀]; rw [← Nat.cast_mul]; rw [@Nat.cast_le]
  · exact Nat.div_mul_le_self m _
  · exact Nat.cast_pos.2 (Nat.succ_pos _)

中文:
定理 cast_div_le
  条件: {m n : 自然数}
  结论: ((m / n : 自然数) : α) <= m / n
  证明: by
  cases n
  · rw [cast_zero, div_zero, Nat.div_zero, cast_zero]
  rw [le_div_iff₀]; rw [← Nat.cast_mul]; rw [@Nat.cast_le]
  · exact Nat.div_mul_le_self m _
  · exact Nat.cast_pos.2 (Nat.succ_pos _)

Depends on / 依赖: Nat.cast_le, Nat.cast_mul, Nat.cast_pos, Nat.div_mul_le_self, Nat.div_zero, Nat.succ_pos, cast_le, cast_mul, cast_pos, cast_zero, div_mul_le_self, div_zero, succ_pos
-/
theorem cast_div_le {m n : Nat} : ((m / n : Nat) : α) <= m / n := by
  cases n
  · rw [cast_zero, div_zero, Nat.div_zero, cast_zero]
  rw [le_div_iff₀]; rw [← Nat.cast_mul]; rw [@Nat.cast_le]
  · exact Nat.div_mul_le_self m _
  · exact Nat.cast_pos.2 (Nat.succ_pos _)

/--
theorem `inv_pos_of_nat` / 定理 `inv_pos_of_nat`

English:
theorem inv_pos_of_nat
  given: {n : Nat}
  statement: 0 < ((n : α) + 1)⁻¹
  proof: inv_pos.2 add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

中文:
定理 inv_pos_of_nat
  条件: {n : 自然数}
  结论: 0 < ((n : α) + 1)⁻¹
  证明: inv_pos.2 add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

Depends on / 依赖: add_pos_of_nonneg_of_pos, cast_nonneg, inv_pos, n.cast_nonneg, zero_lt_one
-/
theorem inv_pos_of_nat {n : Nat} : 0 < ((n : α) + 1)⁻¹ :=
inv_pos.2 add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

/--
theorem `one_div_pos_of_nat` / 定理 `one_div_pos_of_nat`

English:
theorem one_div_pos_of_nat
  given: {n : Nat}
  statement: 0 < 1 / ((n : α) + 1)
  proof: by
  rw [one_div]
  exact inv_pos_of_nat

中文:
定理 one_div_pos_of_nat
  条件: {n : 自然数}
  结论: 0 < 1 / ((n : α) + 1)
  证明: by
  rw [one_div]
  exact inv_pos_of_nat

Depends on / 依赖: inv_pos_of_nat, one_div
-/
theorem one_div_pos_of_nat {n : Nat} : 0 < 1 / ((n : α) + 1) := by
  rw [one_div]
  exact inv_pos_of_nat

/--
theorem `one_div_le_one_div` / 定理 `one_div_le_one_div`

English:
theorem one_div_le_one_div
  given: {n m : Nat} (h : n <= m)
  statement: 1 / ((m : α) + 1) <= 1 / ((n : α) + 1)
  proof: by
  refine one_div_le_one_div_of_le ?_ ?_
  · exact Nat.cast_add_one_pos _
  · simpa

中文:
定理 one_div_le_one_div
  条件: {n m : 自然数} (h : n <= m)
  结论: 1 / ((m : α) + 1) <= 1 / ((n : α) + 1)
  证明: by
  refine one_div_le_one_div_of_le ?_ ?_
  · exact Nat.cast_add_one_pos _
  · simpa

Depends on / 依赖: Nat.cast_add_one_pos, cast_add_one_pos, one_div_le_one_div_of_le
-/
theorem one_div_le_one_div {n m : Nat} (h : n <= m) : 1 / ((m : α) + 1) <= 1 / ((n : α) + 1) := by
  refine one_div_le_one_div_of_le ?_ ?_
  · exact Nat.cast_add_one_pos _
  · simpa

/--
theorem `one_div_lt_one_div` / 定理 `one_div_lt_one_div`

English:
theorem one_div_lt_one_div
  given: {n m : Nat} (h : n < m)
  statement: 1 / ((m : α) + 1) < 1 / ((n : α) + 1)
  proof: by
  refine one_div_lt_one_div_of_lt ?_ ?_
  · exact Nat.cast_add_one_pos _
  · simpa

中文:
定理 one_div_lt_one_div
  条件: {n m : 自然数} (h : n < m)
  结论: 1 / ((m : α) + 1) < 1 / ((n : α) + 1)
  证明: by
  refine one_div_lt_one_div_of_lt ?_ ?_
  · exact Nat.cast_add_one_pos _
  · simpa

Depends on / 依赖: Nat.cast_add_one_pos, cast_add_one_pos, one_div_lt_one_div_of_lt
-/
theorem one_div_lt_one_div {n m : Nat} (h : n < m) : 1 / ((m : α) + 1) < 1 / ((n : α) + 1) := by
  refine one_div_lt_one_div_of_lt ?_ ?_
  · exact Nat.cast_add_one_pos _
  · simpa

/--
theorem `one_div_cast_pos` / 定理 `one_div_cast_pos`

English:
theorem one_div_cast_pos
  given: {n : Nat} (hn : n != 0)
  statement: 0 < 1 / (n : α)
  proof: one_div_pos.mpr (cast_pos.mpr (Nat.pos_of_ne_zero hn))

中文:
定理 one_div_cast_pos
  条件: {n : 自然数} (hn : n != 0)
  结论: 0 < 1 / (n : α)
  证明: one_div_pos.mpr (cast_pos.mpr (Nat.pos_of_ne_zero hn))

Depends on / 依赖: Nat.pos_of_ne_zero, cast_pos, cast_pos.mpr, one_div_pos, one_div_pos.mpr, pos_of_ne_zero
-/
theorem one_div_cast_pos {n : Nat} (hn : n != 0) : 0 < 1 / (n : α) :=
  one_div_pos.mpr (cast_pos.mpr (Nat.pos_of_ne_zero hn))

/--
theorem `one_div_cast_nonneg` / 定理 `one_div_cast_nonneg`

English:
theorem one_div_cast_nonneg
  given: (n : Nat)
  statement: 0 <= 1 / (n : α)
  proof: one_div_nonneg.mpr (cast_nonneg' n)

中文:
定理 one_div_cast_nonneg
  条件: (n : 自然数)
  结论: 0 <= 1 / (n : α)
  证明: one_div_nonneg.mpr (cast_nonneg' n)

Depends on / 依赖: cast_nonneg, one_div_nonneg, one_div_nonneg.mpr
-/
theorem one_div_cast_nonneg (n : Nat) : 0 <= 1 / (n : α) := one_div_nonneg.mpr (cast_nonneg' n)

/--
theorem `one_div_cast_ne_zero` / 定理 `one_div_cast_ne_zero`

English:
theorem one_div_cast_ne_zero
  given: {n : Nat} (hn : n != 0)
  statement: 1 / (n : α) != 0
  proof: _root_.ne_of_gt (one_div_cast_pos hn)

中文:
定理 one_div_cast_ne_zero
  条件: {n : 自然数} (hn : n != 0)
  结论: 1 / (n : α) != 0
  证明: _root_.ne_of_gt (one_div_cast_pos hn)

Depends on / 依赖: _root_, _root_.ne_of_gt, ne_of_gt, one_div_cast_pos
-/
theorem one_div_cast_ne_zero {n : Nat} (hn : n != 0) : 1 / (n : α) != 0 :=
  _root_.ne_of_gt (one_div_cast_pos hn)

end LinearOrderedSemifield

section LinearOrderedField

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/--
theorem `one_sub_one_div_cast_nonneg` / 定理 `one_sub_one_div_cast_nonneg`

English:
theorem one_sub_one_div_cast_nonneg
  given: [AddRightMono α] (n : Nat)
  statement: 0 <= 1 - 1 / (n : α)
  proof: by
  rw [sub_nonneg]; rw [one_div]
  exact cast_inv_le_one n

中文:
定理 one_sub_one_div_cast_nonneg
  条件: [AddRightMono α] (n : 自然数)
  结论: 0 <= 1 - 1 / (n : α)
  证明: by
  rw [sub_nonneg]; rw [one_div]
  exact cast_inv_le_one n

Depends on / 依赖: cast_inv_le_one, one_div, sub_nonneg
-/
theorem one_sub_one_div_cast_nonneg [AddRightMono α] (n : Nat) : 0 <= 1 - 1 / (n : α) := by
  rw [sub_nonneg]; rw [one_div]
  exact cast_inv_le_one n

/--
theorem `one_sub_one_div_cast_le_one` / 定理 `one_sub_one_div_cast_le_one`

English:
theorem one_sub_one_div_cast_le_one
  given: [AddLeftMono α] (n : Nat)
  statement: 1 - 1 / (n : α) <= 1
  proof: by
  rw [sub_le_self_iff]
  exact one_div_cast_nonneg n

中文:
定理 one_sub_one_div_cast_le_one
  条件: [AddLeftMono α] (n : 自然数)
  结论: 1 - 1 / (n : α) <= 1
  证明: by
  rw [sub_le_self_iff]
  exact one_div_cast_nonneg n

Depends on / 依赖: one_div_cast_nonneg, sub_le_self_iff
-/
theorem one_sub_one_div_cast_le_one [AddLeftMono α] (n : Nat) : 1 - 1 / (n : α) <= 1 := by
  rw [sub_le_self_iff]
  exact one_div_cast_nonneg n

end LinearOrderedField

end Nat
