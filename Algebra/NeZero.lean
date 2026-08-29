/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Logic.Basic
public import Mathlib.Order.Defs.PartialOrder

/-!
# `NeZero` typeclass

We give basic facts about the `NeZero n` typeclass.

-/

public section

variable {R : Type*} [Zero R]

/--
theorem `not_neZero` / 定理 `not_neZero`

English:
theorem not_neZero
  given: {n : R}
  statement: ¬NeZero n ↔ n = 0
  proof: by simp [neZero_iff]

中文:
定理 not_neZero
  条件: {n : R}
  结论: ¬NeZero n ↔ n = 0
  证明: by simp [neZero_iff]

Depends on / 依赖: neZero_iff
-/
theorem not_neZero {n : R} : ¬NeZero n ↔ n = 0 := by simp [neZero_iff]

/--
theorem `eq_zero_or_neZero` / 定理 `eq_zero_or_neZero`

English:
theorem eq_zero_or_neZero
  given: (a : R)
  statement: a = 0 ∨ NeZero a
  proof: (eq_or_ne a 0).imp_right NeZero.mk

中文:
定理 eq_zero_or_neZero
  条件: (a : R)
  结论: a = 0 ∨ NeZero a
  证明: (eq_or_ne a 0).imp_right NeZero.mk

Depends on / 依赖: NeZero, NeZero.mk, eq_or_ne, imp_right
-/
theorem eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a :=
  (eq_or_ne a 0).imp_right NeZero.mk

section
variable {α : Type*} [Zero α]

/--
lemma `zero_ne_one` / 引理 `zero_ne_one`

English:
lemma zero_ne_one
  given: [One α] [NeZero (1 : α)]
  statement: (0 : α) != 1
  proof: NeZero.ne' (1 : α)

中文:
引理 zero_ne_one
  条件: [幺 α] [NeZero (1 : α)]
  结论: (0 : α) != 1
  证明: NeZero.ne' (1 : α)
-/
@[simp] lemma zero_ne_one [One α] [NeZero (1 : α)] : (0 : α) != 1 := NeZero.ne' (1 : α)

/--
lemma `one_ne_zero` / 引理 `one_ne_zero`

English:
lemma one_ne_zero
  given: [One α] [NeZero (1 : α)]
  statement: (1 : α) != 0
  proof: NeZero.ne (1 : α)

中文:
引理 one_ne_zero
  条件: [幺 α] [NeZero (1 : α)]
  结论: (1 : α) != 0
  证明: NeZero.ne (1 : α)
-/
@[simp] lemma one_ne_zero [One α] [NeZero (1 : α)] : (1 : α) != 0 := NeZero.ne (1 : α)

/--
lemma `ne_zero_of_eq_one` / 引理 `ne_zero_of_eq_one`

English:
lemma ne_zero_of_eq_one
  given: [One α] [NeZero (1 : α)] {a : α} (h : a = 1)
  statement: a != 0
  proof: h ▸ one_ne_zero

中文:
引理 ne_zero_of_eq_one
  条件: [幺 α] [NeZero (1 : α)] {a : α} (h : a = 1)
  结论: a != 0
  证明: h ▸ one_ne_zero

Depends on / 依赖: one_ne_zero
-/
lemma ne_zero_of_eq_one [One α] [NeZero (1 : α)] {a : α} (h : a = 1) : a != 0 := h ▸ one_ne_zero

/--
lemma `two_ne_zero` / 引理 `two_ne_zero`

English:
lemma two_ne_zero
  given: [OfNat α 2] [NeZero (2 : α)]
  statement: (2 : α) != 0
  proof: NeZero.ne (2 : α)

中文:
引理 two_ne_zero
  条件: [Of自然数 α 2] [NeZero (2 : α)]
  结论: (2 : α) != 0
  证明: NeZero.ne (2 : α)

Depends on / 依赖: NeZero, NeZero.ne
-/
lemma two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0 := NeZero.ne (2 : α)

/--
lemma `three_ne_zero` / 引理 `three_ne_zero`

English:
lemma three_ne_zero
  given: [OfNat α 3] [NeZero (3 : α)]
  statement: (3 : α) != 0
  proof: NeZero.ne (3 : α)

中文:
引理 three_ne_zero
  条件: [Of自然数 α 3] [NeZero (3 : α)]
  结论: (3 : α) != 0
  证明: NeZero.ne (3 : α)

Depends on / 依赖: NeZero, NeZero.ne
-/
lemma three_ne_zero [OfNat α 3] [NeZero (3 : α)] : (3 : α) != 0 := NeZero.ne (3 : α)

/--
lemma `four_ne_zero` / 引理 `four_ne_zero`

English:
lemma four_ne_zero
  given: [OfNat α 4] [NeZero (4 : α)]
  statement: (4 : α) != 0
  proof: NeZero.ne (4 : α)

中文:
引理 four_ne_zero
  条件: [Of自然数 α 4] [NeZero (4 : α)]
  结论: (4 : α) != 0
  证明: NeZero.ne (4 : α)

Depends on / 依赖: NeZero, NeZero.ne
-/
lemma four_ne_zero [OfNat α 4] [NeZero (4 : α)] : (4 : α) != 0 := NeZero.ne (4 : α)

variable (α)

/--
lemma `zero_ne_one'` / 引理 `zero_ne_one'`

English:
lemma zero_ne_one'
  given: [One α] [NeZero (1 : α)]
  statement: (0 : α) != 1
  proof: zero_ne_one

中文:
引理 zero_ne_one'
  条件: [幺 α] [NeZero (1 : α)]
  结论: (0 : α) != 1
  证明: zero_ne_one

Depends on / 依赖: zero_ne_one
-/
lemma zero_ne_one' [One α] [NeZero (1 : α)] : (0 : α) != 1 := zero_ne_one

/--
lemma `one_ne_zero'` / 引理 `one_ne_zero'`

English:
lemma one_ne_zero'
  given: [One α] [NeZero (1 : α)]
  statement: (1 : α) != 0
  proof: one_ne_zero

中文:
引理 one_ne_zero'
  条件: [幺 α] [NeZero (1 : α)]
  结论: (1 : α) != 0
  证明: one_ne_zero

Depends on / 依赖: one_ne_zero
-/
lemma one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0 := one_ne_zero

/--
lemma `two_ne_zero'` / 引理 `two_ne_zero'`

English:
lemma two_ne_zero'
  given: [OfNat α 2] [NeZero (2 : α)]
  statement: (2 : α) != 0
  proof: two_ne_zero

中文:
引理 two_ne_zero'
  条件: [Of自然数 α 2] [NeZero (2 : α)]
  结论: (2 : α) != 0
  证明: two_ne_zero

Depends on / 依赖: two_ne_zero
-/
lemma two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0 := two_ne_zero

/--
lemma `three_ne_zero'` / 引理 `three_ne_zero'`

English:
lemma three_ne_zero'
  given: [OfNat α 3] [NeZero (3 : α)]
  statement: (3 : α) != 0
  proof: three_ne_zero

中文:
引理 three_ne_zero'
  条件: [Of自然数 α 3] [NeZero (3 : α)]
  结论: (3 : α) != 0
  证明: three_ne_zero

Depends on / 依赖: three_ne_zero
-/
lemma three_ne_zero' [OfNat α 3] [NeZero (3 : α)] : (3 : α) != 0 := three_ne_zero

/--
lemma `four_ne_zero'` / 引理 `four_ne_zero'`

English:
lemma four_ne_zero'
  given: [OfNat α 4] [NeZero (4 : α)]
  statement: (4 : α) != 0
  proof: four_ne_zero

中文:
引理 four_ne_zero'
  条件: [Of自然数 α 4] [NeZero (4 : α)]
  结论: (4 : α) != 0
  证明: four_ne_zero

Depends on / 依赖: four_ne_zero
-/
lemma four_ne_zero' [OfNat α 4] [NeZero (4 : α)] : (4 : α) != 0 := four_ne_zero

end

namespace NeZero

variable {M : Type*} {x : M}

/--
theorem `of_pos` / 定理 `of_pos`

English:
theorem of_pos
  given: [Preorder M] [Zero M] (h : 0 < x)
  statement: NeZero x
  proof: ⟨ne_of_gt h⟩

中文:
定理 of_pos
  条件: [预序 M] [零 M] (h : 0 < x)
  结论: NeZero x
  证明: ⟨ne_of_gt h⟩

Depends on / 依赖: ne_of_gt
-/
theorem of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x := ⟨ne_of_gt h⟩

end NeZero
