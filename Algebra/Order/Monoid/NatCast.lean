/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Yuyang Zhao
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Data.Nat.Cast.Defs

/-!
# Order of numerals in an `AddMonoidWithOne`.
-/

public section

variable {α : Type*}

open Function

/--
lemma `lt_add_one` / 引理 `lt_add_one`

English:
lemma lt_add_one
  statement: [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α]
  proof: lt_add_of_pos_right _ zero_lt_one

中文:
引理 lt_add_one
  结论: [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α]
  证明: lt_add_of_pos_right _ zero_lt_one

Depends on / 依赖: lt_add_of_pos_right, zero_lt_one
-/
lemma lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α]
    [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1 :=
  lt_add_of_pos_right _ zero_lt_one

/--
lemma `lt_one_add` / 引理 `lt_one_add`

English:
lemma lt_one_add
  statement: [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α]
  proof: lt_add_of_pos_left _ zero_lt_one

中文:
引理 lt_one_add
  结论: [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α]
  证明: lt_add_of_pos_left _ zero_lt_one

Depends on / 依赖: lt_add_of_pos_left, zero_lt_one
-/
lemma lt_one_add [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α]
    [NeZero (1 : α)] [AddRightStrictMono α] (a : α) : a < 1 + a :=
  lt_add_of_pos_left _ zero_lt_one

variable [AddMonoidWithOne α]

/--
lemma `zero_le_two` / 引理 `zero_le_two`

English:
lemma zero_le_two
  given: [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
  proof: by
  rw [← one_add_one_eq_two]
  exact add_nonneg zero_le_one zero_le_one

中文:
引理 zero_le_two
  条件: [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
  证明: by
  rw [← one_add_one_eq_two]
  exact add_nonneg zero_le_one zero_le_one

Depends on / 依赖: add_nonneg, one_add_one_eq_two, zero_le_one
-/
lemma zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α] :
    (0 : α) <= 2 := by
  rw [← one_add_one_eq_two]
  exact add_nonneg zero_le_one zero_le_one

/--
lemma `zero_le_three` / 引理 `zero_le_three`

English:
lemma zero_le_three
  given: [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
  proof: by
  rw [← two_add_one_eq_three]
  exact add_nonneg zero_le_two zero_le_one

中文:
引理 zero_le_three
  条件: [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
  证明: by
  rw [← two_add_one_eq_three]
  exact add_nonneg zero_le_two zero_le_one

Depends on / 依赖: add_nonneg, two_add_one_eq_three, zero_le_one, zero_le_two
-/
lemma zero_le_three [Preorder α] [ZeroLEOneClass α] [AddLeftMono α] :
    (0 : α) <= 3 := by
  rw [← two_add_one_eq_three]
  exact add_nonneg zero_le_two zero_le_one

/--
lemma `zero_le_four` / 引理 `zero_le_four`

English:
lemma zero_le_four
  given: [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
  proof: by
  rw [← three_add_one_eq_four]
  exact add_nonneg zero_le_three zero_le_one

中文:
引理 zero_le_four
  条件: [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
  证明: by
  rw [← three_add_one_eq_four]
  exact add_nonneg zero_le_three zero_le_one

Depends on / 依赖: add_nonneg, three_add_one_eq_four, zero_le_one, zero_le_three
-/
lemma zero_le_four [Preorder α] [ZeroLEOneClass α] [AddLeftMono α] :
    (0 : α) <= 4 := by
  rw [← three_add_one_eq_four]
  exact add_nonneg zero_le_three zero_le_one

/--
lemma `one_le_two` / 引理 `one_le_two`

English:
lemma one_le_two
  given: [LE α] [ZeroLEOneClass α] [AddLeftMono α]
  proof: calc (1 : α) = 1 + 0 := (add_zero 1).symm
     _ <= 1 + 1 := by gcongr; exact zero_le_one
     _ = 2 := one_add_one_eq_two

中文:
引理 one_le_two
  条件: [LE α] [ZeroLEOneClass α] [AddLeftMono α]
  证明: calc (1 : α) = 1 + 0 := (add_zero 1).symm
     _ <= 1 + 1 := by gcongr; exact zero_le_one
     _ = 2 := one_add_one_eq_two

Depends on / 依赖: add_zero, one_add_one_eq_two, zero_le_one
-/
lemma one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] :
    (1 : α) <= 2 :=
  calc (1 : α) = 1 + 0 := (add_zero 1).symm
     _ <= 1 + 1 := by gcongr; exact zero_le_one
     _ = 2 := one_add_one_eq_two

/--
lemma `one_le_two'` / 引理 `one_le_two'`

English:
lemma one_le_two'
  given: [LE α] [ZeroLEOneClass α] [AddRightMono α]
  proof: calc (1 : α) = 0 + 1 := (zero_add 1).symm
     _ <= 1 + 1 := by gcongr; exact zero_le_one
     _ = 2 := one_add_one_eq_two

中文:
引理 one_le_two'
  条件: [LE α] [ZeroLEOneClass α] [AddRightMono α]
  证明: calc (1 : α) = 0 + 1 := (zero_add 1).symm
     _ <= 1 + 1 := by gcongr; exact zero_le_one
     _ = 2 := one_add_one_eq_two

Depends on / 依赖: one_add_one_eq_two, zero_add, zero_le_one
-/
lemma one_le_two' [LE α] [ZeroLEOneClass α] [AddRightMono α] :
    (1 : α) <= 2 :=
  calc (1 : α) = 0 + 1 := (zero_add 1).symm
     _ <= 1 + 1 := by gcongr; exact zero_le_one
     _ = 2 := one_add_one_eq_two

section
variable [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]

section
variable [AddLeftMono α]

/--
lemma `zero_lt_two` / 引理 `zero_lt_two`

English:
lemma zero_lt_two
  statement: (0 : α) < 2
  proof: zero_lt_one.trans_le one_le_two

中文:
引理 zero_lt_two
  结论: (0 : α) < 2
  证明: zero_lt_one.trans_le one_le_two
-/
@[simp] lemma zero_lt_two : (0 : α) < 2 := zero_lt_one.trans_le one_le_two

/--
lemma `zero_lt_three` / 引理 `zero_lt_three`

English:
lemma zero_lt_three
  statement: (0 : α) < 3
  proof: by
  rw [← two_add_one_eq_three]
  exact lt_add_of_lt_of_nonneg zero_lt_two zero_le_one

中文:
引理 zero_lt_three
  结论: (0 : α) < 3
  证明: by
  rw [← two_add_one_eq_three]
  exact lt_add_of_lt_of_nonneg zero_lt_two zero_le_one
-/
@[simp] lemma zero_lt_three : (0 : α) < 3 := by
  rw [← two_add_one_eq_three]
  exact lt_add_of_lt_of_nonneg zero_lt_two zero_le_one

/--
lemma `zero_lt_four` / 引理 `zero_lt_four`

English:
lemma zero_lt_four
  statement: (0 : α) < 4
  proof: by
  rw [← three_add_one_eq_four]
  exact lt_add_of_lt_of_nonneg zero_lt_three zero_le_one

中文:
引理 zero_lt_four
  结论: (0 : α) < 4
  证明: by
  rw [← three_add_one_eq_four]
  exact lt_add_of_lt_of_nonneg zero_lt_three zero_le_one
-/
@[simp] lemma zero_lt_four : (0 : α) < 4 := by
  rw [← three_add_one_eq_four]
  exact lt_add_of_lt_of_nonneg zero_lt_three zero_le_one

variable (α)

/--
lemma `zero_lt_two'` / 引理 `zero_lt_two'`

English:
lemma zero_lt_two'
  statement: (0 : α) < 2
  proof: zero_lt_two

中文:
引理 zero_lt_two'
  结论: (0 : α) < 2
  证明: zero_lt_two

Depends on / 依赖: zero_lt_two
-/
lemma zero_lt_two' : (0 : α) < 2 := zero_lt_two

/--
lemma `zero_lt_three'` / 引理 `zero_lt_three'`

English:
lemma zero_lt_three'
  statement: (0 : α) < 3
  proof: zero_lt_three

中文:
引理 zero_lt_three'
  结论: (0 : α) < 3
  证明: zero_lt_three

Depends on / 依赖: zero_lt_three
-/
lemma zero_lt_three' : (0 : α) < 3 := zero_lt_three

/--
lemma `zero_lt_four'` / 引理 `zero_lt_four'`

English:
lemma zero_lt_four'
  statement: (0 : α) < 4
  proof: zero_lt_four

中文:
引理 zero_lt_four'
  结论: (0 : α) < 4
  证明: zero_lt_four

Depends on / 依赖: zero_lt_four
-/
lemma zero_lt_four' : (0 : α) < 4 := zero_lt_four

/--
Instance `ZeroLEOneClass.neZero.two` / 实例 `ZeroLEOneClass.neZero.two`

English:
instance ZeroLEOneClass.neZero.two
  signature: : NeZero (2 : α)
  body: ⟨zero_lt_two.ne'⟩

中文:
实例 ZeroLEOneClass.neZero.two
  签名: : NeZero (2 : α)
  定义体: ⟨zero_lt_two.ne'⟩

Depends on / 依赖: zero_lt_two, zero_lt_two.ne
-/
instance ZeroLEOneClass.neZero.two : NeZero (2 : α) := ⟨zero_lt_two.ne'⟩
/--
Instance `ZeroLEOneClass.neZero.three` / 实例 `ZeroLEOneClass.neZero.three`

English:
instance ZeroLEOneClass.neZero.three
  signature: : NeZero (3 : α)
  body: ⟨zero_lt_three.ne'⟩

中文:
实例 ZeroLEOneClass.neZero.three
  签名: : NeZero (3 : α)
  定义体: ⟨zero_lt_three.ne'⟩

Depends on / 依赖: zero_lt_three, zero_lt_three.ne
-/
instance ZeroLEOneClass.neZero.three : NeZero (3 : α) := ⟨zero_lt_three.ne'⟩
/--
Instance `ZeroLEOneClass.neZero.four` / 实例 `ZeroLEOneClass.neZero.four`

English:
instance ZeroLEOneClass.neZero.four
  signature: : NeZero (4 : α)
  body: ⟨zero_lt_four.ne'⟩

中文:
实例 ZeroLEOneClass.neZero.four
  签名: : NeZero (4 : α)
  定义体: ⟨zero_lt_four.ne'⟩

Depends on / 依赖: zero_lt_four, zero_lt_four.ne
-/
instance ZeroLEOneClass.neZero.four : NeZero (4 : α) := ⟨zero_lt_four.ne'⟩

end

/--
lemma `one_lt_two` / 引理 `one_lt_two`

English:
lemma one_lt_two
  given: [AddLeftStrictMono α]
  statement: (1 : α) < 2
  proof: by
  rw [← one_add_one_eq_two]
  exact lt_add_one _

中文:
引理 one_lt_two
  条件: [AddLeftStrictMono α]
  结论: (1 : α) < 2
  证明: by
  rw [← one_add_one_eq_two]
  exact lt_add_one _

Depends on / 依赖: lt_add_one, one_add_one_eq_two
-/
lemma one_lt_two [AddLeftStrictMono α] : (1 : α) < 2 := by
  rw [← one_add_one_eq_two]
  exact lt_add_one _

end

alias two_pos := zero_lt_two

alias three_pos := zero_lt_three

alias four_pos := zero_lt_four
