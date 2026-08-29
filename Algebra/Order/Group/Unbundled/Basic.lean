/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Sub.Defs

/-!
# Ordered groups

This file develops the basics of unbundled ordered groups.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/

public section

assert_not_exists IsOrderedMonoid

open Function

universe u

variable {α : Type u}

section Group

variable [Group α]

section MulLeftMono

variable [LE α] [MulLeftMono α] {a b c : α}

/-- Uses `left` co(ntra)variant. -/
@[to_additive (attr := simp) /-- Uses `left` co(ntra)variant. -/]
/--
theorem `Left.inv_le_one_iff` / 定理 `Left.inv_le_one_iff`

English:
theorem Left.inv_le_one_iff
  statement: a⁻¹ <= 1 ↔ 1 <= a
  proof: by
  rw [← mul_le_mul_iff_left a]
  simp

中文:
定理 Left.inv_le_one_iff
  结论: a⁻¹ <= 1 ↔ 1 <= a
  证明: by
  rw [← mul_le_mul_iff_left a]
  simp

Depends on / 依赖: mul_le_mul_iff_left
-/
theorem Left.inv_le_one_iff : a⁻¹ <= 1 ↔ 1 <= a := by
  rw [← mul_le_mul_iff_left a]
  simp

/-- Uses `left` co(ntra)variant. -/
@[to_additive (attr := simp) /-- Uses `left` co(ntra)variant. -/]
/--
theorem `Left.one_le_inv_iff` / 定理 `Left.one_le_inv_iff`

English:
theorem Left.one_le_inv_iff
  statement: 1 <= a⁻¹ ↔ a <= 1
  proof: by
  rw [← mul_le_mul_iff_left a]
  simp

@[to_additive (attr := simp)]

中文:
定理 Left.one_le_inv_iff
  结论: 1 <= a⁻¹ ↔ a <= 1
  证明: by
  rw [← mul_le_mul_iff_left a]
  simp

@[to_additive (attr := simp)]

Depends on / 依赖: mul_le_mul_iff_left
-/
theorem Left.one_le_inv_iff : 1 <= a⁻¹ ↔ a <= 1 := by
  rw [← mul_le_mul_iff_left a]
  simp

@[to_additive (attr := simp)]
/--
theorem `le_inv_mul_iff_mul_le` / 定理 `le_inv_mul_iff_mul_le`

English:
theorem le_inv_mul_iff_mul_le
  statement: b <= a⁻¹ * c ↔ a * b <= c
  proof: by
  rw [← mul_le_mul_iff_left a]
  simp

@[to_additive (attr := simp)]

中文:
定理 le_inv_mul_iff_mul_le
  结论: b <= a⁻¹ * c ↔ a * b <= c
  证明: by
  rw [← mul_le_mul_iff_left a]
  simp

@[to_additive (attr := simp)]

Depends on / 依赖: mul_le_mul_iff_left
-/
theorem le_inv_mul_iff_mul_le : b <= a⁻¹ * c ↔ a * b <= c := by
  rw [← mul_le_mul_iff_left a]
  simp

@[to_additive (attr := simp)]
/--
theorem `inv_mul_le_iff_le_mul` / 定理 `inv_mul_le_iff_le_mul`

English:
theorem inv_mul_le_iff_le_mul
  statement: b⁻¹ * a <= c ↔ a <= b * c
  proof: by
  rw [← mul_le_mul_iff_left b]; rw [mul_inv_cancel_left]

@[to_additive neg_le_iff_add_nonneg']

中文:
定理 inv_mul_le_iff_le_mul
  结论: b⁻¹ * a <= c ↔ a <= b * c
  证明: by
  rw [← mul_le_mul_iff_left b]; rw [mul_inv_cancel_left]

@[to_additive neg_le_iff_add_nonneg']

Depends on / 依赖: mul_inv_cancel_left, mul_le_mul_iff_left
-/
theorem inv_mul_le_iff_le_mul : b⁻¹ * a <= c ↔ a <= b * c := by
  rw [← mul_le_mul_iff_left b]; rw [mul_inv_cancel_left]

@[to_additive neg_le_iff_add_nonneg']
/--
theorem `inv_le_iff_one_le_mul'` / 定理 `inv_le_iff_one_le_mul'`

English:
theorem inv_le_iff_one_le_mul'
  statement: a⁻¹ <= b ↔ 1 <= a * b
  proof: (mul_le_mul_iff_left a).symm.trans by rw [mul_inv_cancel]

@[to_additive]

中文:
定理 inv_le_iff_one_le_mul'
  结论: a⁻¹ <= b ↔ 1 <= a * b
  证明: (mul_le_mul_iff_left a).symm.trans by rw [mul_inv_cancel]

@[to_additive]

Depends on / 依赖: mul_inv_cancel, mul_le_mul_iff_left, symm.trans
-/
theorem inv_le_iff_one_le_mul' : a⁻¹ <= b ↔ 1 <= a * b :=
(mul_le_mul_iff_left a).symm.trans by rw [mul_inv_cancel]

@[to_additive]
/--
theorem `le_inv_iff_mul_le_one_left` / 定理 `le_inv_iff_mul_le_one_left`

English:
theorem le_inv_iff_mul_le_one_left
  statement: a <= b⁻¹ ↔ b * a <= 1
  proof: (mul_le_mul_iff_left b).symm.trans by rw [mul_inv_cancel]

@[to_additive]

中文:
定理 le_inv_iff_mul_le_one_left
  结论: a <= b⁻¹ ↔ b * a <= 1
  证明: (mul_le_mul_iff_left b).symm.trans by rw [mul_inv_cancel]

@[to_additive]

Depends on / 依赖: mul_inv_cancel, mul_le_mul_iff_left, symm.trans
-/
theorem le_inv_iff_mul_le_one_left : a <= b⁻¹ ↔ b * a <= 1 :=
(mul_le_mul_iff_left b).symm.trans by rw [mul_inv_cancel]

@[to_additive]
/--
theorem `le_inv_mul_iff_le` / 定理 `le_inv_mul_iff_le`

English:
theorem le_inv_mul_iff_le
  statement: 1 <= b⁻¹ * a ↔ b <= a
  proof: by
  rw [← mul_le_mul_iff_left b]; rw [mul_one]; rw [mul_inv_cancel_left]

@[to_additive]

中文:
定理 le_inv_mul_iff_le
  结论: 1 <= b⁻¹ * a ↔ b <= a
  证明: by
  rw [← mul_le_mul_iff_left b]; rw [mul_one]; rw [mul_inv_cancel_left]

@[to_additive]

Depends on / 依赖: mul_inv_cancel_left, mul_le_mul_iff_left, mul_one
-/
theorem le_inv_mul_iff_le : 1 <= b⁻¹ * a ↔ b <= a := by
  rw [← mul_le_mul_iff_left b]; rw [mul_one]; rw [mul_inv_cancel_left]

@[to_additive]
/--
theorem `inv_mul_le_one_iff` / 定理 `inv_mul_le_one_iff`

English:
theorem inv_mul_le_one_iff
  statement: a⁻¹ * b <= 1 ↔ b <= a
  proof: inv_mul_le_iff_le_mul.trans by rw [mul_one]

中文:
定理 inv_mul_le_one_iff
  结论: a⁻¹ * b <= 1 ↔ b <= a
  证明: inv_mul_le_iff_le_mul.trans by rw [mul_one]

Depends on / 依赖: inv_mul_le_iff_le_mul, inv_mul_le_iff_le_mul.trans, mul_one
-/
theorem inv_mul_le_one_iff : a⁻¹ * b <= 1 ↔ b <= a :=
inv_mul_le_iff_le_mul.trans by rw [mul_one]

end MulLeftMono

section MulLeftStrictMono

variable [LT α] [MulLeftStrictMono α] {a b c : α}

/-- Uses `left` co(ntra)variant. -/
@[to_additive (attr := simp) Left.neg_pos_iff /-- Uses `left` co(ntra)variant. -/]
/--
theorem `Left.one_lt_inv_iff` / 定理 `Left.one_lt_inv_iff`

English:
theorem Left.one_lt_inv_iff
  statement: 1 < a⁻¹ ↔ a < 1
  proof: by
  rw [← mul_lt_mul_iff_left a]; rw [mul_inv_cancel]; rw [mul_one]

中文:
定理 Left.one_lt_inv_iff
  结论: 1 < a⁻¹ ↔ a < 1
  证明: by
  rw [← mul_lt_mul_iff_left a]; rw [mul_inv_cancel]; rw [mul_one]

Depends on / 依赖: mul_inv_cancel, mul_lt_mul_iff_left, mul_one
-/
theorem Left.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1 := by
  rw [← mul_lt_mul_iff_left a]; rw [mul_inv_cancel]; rw [mul_one]

/-- Uses `left` co(ntra)variant. -/
@[to_additive (attr := simp) /-- Uses `left` co(ntra)variant. -/]
/--
theorem `Left.inv_lt_one_iff` / 定理 `Left.inv_lt_one_iff`

English:
theorem Left.inv_lt_one_iff
  statement: a⁻¹ < 1 ↔ 1 < a
  proof: by
  rw [← mul_lt_mul_iff_left a]; rw [mul_inv_cancel]; rw [mul_one]

@[to_additive (attr := simp)]

中文:
定理 Left.inv_lt_one_iff
  结论: a⁻¹ < 1 ↔ 1 < a
  证明: by
  rw [← mul_lt_mul_iff_left a]; rw [mul_inv_cancel]; rw [mul_one]

@[to_additive (attr := simp)]

Depends on / 依赖: mul_inv_cancel, mul_lt_mul_iff_left, mul_one
-/
theorem Left.inv_lt_one_iff : a⁻¹ < 1 ↔ 1 < a := by
  rw [← mul_lt_mul_iff_left a]; rw [mul_inv_cancel]; rw [mul_one]

@[to_additive (attr := simp)]
/--
theorem `lt_inv_mul_iff_mul_lt` / 定理 `lt_inv_mul_iff_mul_lt`

English:
theorem lt_inv_mul_iff_mul_lt
  statement: b < a⁻¹ * c ↔ a * b < c
  proof: by
  rw [← mul_lt_mul_iff_left a]
  simp

@[to_additive (attr := simp)]

中文:
定理 lt_inv_mul_iff_mul_lt
  结论: b < a⁻¹ * c ↔ a * b < c
  证明: by
  rw [← mul_lt_mul_iff_left a]
  simp

@[to_additive (attr := simp)]

Depends on / 依赖: mul_lt_mul_iff_left
-/
theorem lt_inv_mul_iff_mul_lt : b < a⁻¹ * c ↔ a * b < c := by
  rw [← mul_lt_mul_iff_left a]
  simp

@[to_additive (attr := simp)]
/--
theorem `inv_mul_lt_iff_lt_mul` / 定理 `inv_mul_lt_iff_lt_mul`

English:
theorem inv_mul_lt_iff_lt_mul
  statement: b⁻¹ * a < c ↔ a < b * c
  proof: by
  rw [← mul_lt_mul_iff_left b]; rw [mul_inv_cancel_left]

@[to_additive]

中文:
定理 inv_mul_lt_iff_lt_mul
  结论: b⁻¹ * a < c ↔ a < b * c
  证明: by
  rw [← mul_lt_mul_iff_left b]; rw [mul_inv_cancel_left]

@[to_additive]

Depends on / 依赖: mul_inv_cancel_left, mul_lt_mul_iff_left
-/
theorem inv_mul_lt_iff_lt_mul : b⁻¹ * a < c ↔ a < b * c := by
  rw [← mul_lt_mul_iff_left b]; rw [mul_inv_cancel_left]

@[to_additive]
/--
theorem `inv_lt_iff_one_lt_mul'` / 定理 `inv_lt_iff_one_lt_mul'`

English:
theorem inv_lt_iff_one_lt_mul'
  statement: a⁻¹ < b ↔ 1 < a * b
  proof: (mul_lt_mul_iff_left a).symm.trans by rw [mul_inv_cancel]

@[to_additive]

中文:
定理 inv_lt_iff_one_lt_mul'
  结论: a⁻¹ < b ↔ 1 < a * b
  证明: (mul_lt_mul_iff_left a).symm.trans by rw [mul_inv_cancel]

@[to_additive]

Depends on / 依赖: mul_inv_cancel, mul_lt_mul_iff_left, symm.trans
-/
theorem inv_lt_iff_one_lt_mul' : a⁻¹ < b ↔ 1 < a * b :=
(mul_lt_mul_iff_left a).symm.trans by rw [mul_inv_cancel]

@[to_additive]
/--
theorem `lt_inv_iff_mul_lt_one'` / 定理 `lt_inv_iff_mul_lt_one'`

English:
theorem lt_inv_iff_mul_lt_one'
  statement: a < b⁻¹ ↔ b * a < 1
  proof: (mul_lt_mul_iff_left b).symm.trans by rw [mul_inv_cancel]

@[to_additive]

中文:
定理 lt_inv_iff_mul_lt_one'
  结论: a < b⁻¹ ↔ b * a < 1
  证明: (mul_lt_mul_iff_left b).symm.trans by rw [mul_inv_cancel]

@[to_additive]

Depends on / 依赖: mul_inv_cancel, mul_lt_mul_iff_left, symm.trans
-/
theorem lt_inv_iff_mul_lt_one' : a < b⁻¹ ↔ b * a < 1 :=
(mul_lt_mul_iff_left b).symm.trans by rw [mul_inv_cancel]

@[to_additive]
/--
theorem `lt_inv_mul_iff_lt` / 定理 `lt_inv_mul_iff_lt`

English:
theorem lt_inv_mul_iff_lt
  statement: 1 < b⁻¹ * a ↔ b < a
  proof: by
  rw [← mul_lt_mul_iff_left b]; rw [mul_one]; rw [mul_inv_cancel_left]

@[to_additive]

中文:
定理 lt_inv_mul_iff_lt
  结论: 1 < b⁻¹ * a ↔ b < a
  证明: by
  rw [← mul_lt_mul_iff_left b]; rw [mul_one]; rw [mul_inv_cancel_left]

@[to_additive]

Depends on / 依赖: mul_inv_cancel_left, mul_lt_mul_iff_left, mul_one
-/
theorem lt_inv_mul_iff_lt : 1 < b⁻¹ * a ↔ b < a := by
  rw [← mul_lt_mul_iff_left b]; rw [mul_one]; rw [mul_inv_cancel_left]

@[to_additive]
/--
theorem `inv_mul_lt_one_iff` / 定理 `inv_mul_lt_one_iff`

English:
theorem inv_mul_lt_one_iff
  statement: a⁻¹ * b < 1 ↔ b < a
  proof: _root_.trans inv_mul_lt_iff_lt_mul by rw [mul_one]

中文:
定理 inv_mul_lt_one_iff
  结论: a⁻¹ * b < 1 ↔ b < a
  证明: _root_.trans inv_mul_lt_iff_lt_mul by rw [mul_one]

Depends on / 依赖: _root_, _root_.trans, inv_mul_lt_iff_lt_mul, mul_one
-/
theorem inv_mul_lt_one_iff : a⁻¹ * b < 1 ↔ b < a :=
_root_.trans inv_mul_lt_iff_lt_mul by rw [mul_one]

end MulLeftStrictMono

section MulRightMono

variable [LE α] [MulRightMono α] {a b c : α}

/-- Uses `right` co(ntra)variant. -/
@[to_additive (attr := simp) /-- Uses `right` co(ntra)variant. -/]
/--
theorem `Right.inv_le_one_iff` / 定理 `Right.inv_le_one_iff`

English:
theorem Right.inv_le_one_iff
  statement: a⁻¹ <= 1 ↔ 1 <= a
  proof: by
  rw [← mul_le_mul_iff_right a]
  simp

中文:
定理 Right.inv_le_one_iff
  结论: a⁻¹ <= 1 ↔ 1 <= a
  证明: by
  rw [← mul_le_mul_iff_right a]
  simp

Depends on / 依赖: mul_le_mul_iff_right
-/
theorem Right.inv_le_one_iff : a⁻¹ <= 1 ↔ 1 <= a := by
  rw [← mul_le_mul_iff_right a]
  simp

/-- Uses `right` co(ntra)variant. -/
@[to_additive (attr := simp) /-- Uses `right` co(ntra)variant. -/]
/--
theorem `Right.one_le_inv_iff` / 定理 `Right.one_le_inv_iff`

English:
theorem Right.one_le_inv_iff
  statement: 1 <= a⁻¹ ↔ a <= 1
  proof: by
  rw [← mul_le_mul_iff_right a]
  simp

@[to_additive neg_le_iff_add_nonneg]

中文:
定理 Right.one_le_inv_iff
  结论: 1 <= a⁻¹ ↔ a <= 1
  证明: by
  rw [← mul_le_mul_iff_right a]
  simp

@[to_additive neg_le_iff_add_nonneg]

Depends on / 依赖: mul_le_mul_iff_right
-/
theorem Right.one_le_inv_iff : 1 <= a⁻¹ ↔ a <= 1 := by
  rw [← mul_le_mul_iff_right a]
  simp

@[to_additive neg_le_iff_add_nonneg]
/--
theorem `inv_le_iff_one_le_mul` / 定理 `inv_le_iff_one_le_mul`

English:
theorem inv_le_iff_one_le_mul
  statement: a⁻¹ <= b ↔ 1 <= b * a
  proof: (mul_le_mul_iff_right a).symm.trans by rw [inv_mul_cancel]

@[to_additive]

中文:
定理 inv_le_iff_one_le_mul
  结论: a⁻¹ <= b ↔ 1 <= b * a
  证明: (mul_le_mul_iff_right a).symm.trans by rw [inv_mul_cancel]

@[to_additive]

Depends on / 依赖: inv_mul_cancel, mul_le_mul_iff_right, symm.trans
-/
theorem inv_le_iff_one_le_mul : a⁻¹ <= b ↔ 1 <= b * a :=
(mul_le_mul_iff_right a).symm.trans by rw [inv_mul_cancel]

@[to_additive]
/--
theorem `le_inv_iff_mul_le_one_right` / 定理 `le_inv_iff_mul_le_one_right`

English:
theorem le_inv_iff_mul_le_one_right
  statement: a <= b⁻¹ ↔ a * b <= 1
  proof: (mul_le_mul_iff_right b).symm.trans by rw [inv_mul_cancel]

@[to_additive (attr := simp)]

中文:
定理 le_inv_iff_mul_le_one_right
  结论: a <= b⁻¹ ↔ a * b <= 1
  证明: (mul_le_mul_iff_right b).symm.trans by rw [inv_mul_cancel]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_mul_cancel, mul_le_mul_iff_right, symm.trans
-/
theorem le_inv_iff_mul_le_one_right : a <= b⁻¹ ↔ a * b <= 1 :=
(mul_le_mul_iff_right b).symm.trans by rw [inv_mul_cancel]

@[to_additive (attr := simp)]
/--
theorem `mul_inv_le_iff_le_mul` / 定理 `mul_inv_le_iff_le_mul`

English:
theorem mul_inv_le_iff_le_mul
  statement: a * b⁻¹ <= c ↔ a <= c * b
  proof: (mul_le_mul_iff_right b).symm.trans by rw [inv_mul_cancel_right]

@[to_additive (attr := simp)]

中文:
定理 mul_inv_le_iff_le_mul
  结论: a * b⁻¹ <= c ↔ a <= c * b
  证明: (mul_le_mul_iff_right b).symm.trans by rw [inv_mul_cancel_right]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_mul_cancel_right, mul_le_mul_iff_right, symm.trans
-/
theorem mul_inv_le_iff_le_mul : a * b⁻¹ <= c ↔ a <= c * b :=
(mul_le_mul_iff_right b).symm.trans by rw [inv_mul_cancel_right]

@[to_additive (attr := simp)]
/--
theorem `le_mul_inv_iff_mul_le` / 定理 `le_mul_inv_iff_mul_le`

English:
theorem le_mul_inv_iff_mul_le
  statement: c <= a * b⁻¹ ↔ c * b <= a
  proof: (mul_le_mul_iff_right b).symm.trans by rw [inv_mul_cancel_right]

@[to_additive]

中文:
定理 le_mul_inv_iff_mul_le
  结论: c <= a * b⁻¹ ↔ c * b <= a
  证明: (mul_le_mul_iff_right b).symm.trans by rw [inv_mul_cancel_right]

@[to_additive]

Depends on / 依赖: inv_mul_cancel_right, mul_le_mul_iff_right, symm.trans
-/
theorem le_mul_inv_iff_mul_le : c <= a * b⁻¹ ↔ c * b <= a :=
(mul_le_mul_iff_right b).symm.trans by rw [inv_mul_cancel_right]

@[to_additive]
/--
theorem `mul_inv_le_one_iff_le` / 定理 `mul_inv_le_one_iff_le`

English:
theorem mul_inv_le_one_iff_le
  statement: a * b⁻¹ <= 1 ↔ a <= b
  proof: mul_inv_le_iff_le_mul.trans by rw [one_mul]

@[to_additive]

中文:
定理 mul_inv_le_one_iff_le
  结论: a * b⁻¹ <= 1 ↔ a <= b
  证明: mul_inv_le_iff_le_mul.trans by rw [one_mul]

@[to_additive]

Depends on / 依赖: mul_inv_le_iff_le_mul, mul_inv_le_iff_le_mul.trans, one_mul
-/
theorem mul_inv_le_one_iff_le : a * b⁻¹ <= 1 ↔ a <= b :=
mul_inv_le_iff_le_mul.trans by rw [one_mul]

@[to_additive]
/--
theorem `le_mul_inv_iff_le` / 定理 `le_mul_inv_iff_le`

English:
theorem le_mul_inv_iff_le
  statement: 1 <= a * b⁻¹ ↔ b <= a
  proof: by
  rw [← mul_le_mul_iff_right b]; rw [one_mul]; rw [inv_mul_cancel_right]

@[to_additive]

中文:
定理 le_mul_inv_iff_le
  结论: 1 <= a * b⁻¹ ↔ b <= a
  证明: by
  rw [← mul_le_mul_iff_right b]; rw [one_mul]; rw [inv_mul_cancel_right]

@[to_additive]

Depends on / 依赖: inv_mul_cancel_right, mul_le_mul_iff_right, one_mul
-/
theorem le_mul_inv_iff_le : 1 <= a * b⁻¹ ↔ b <= a := by
  rw [← mul_le_mul_iff_right b]; rw [one_mul]; rw [inv_mul_cancel_right]

@[to_additive]
/--
theorem `mul_inv_le_one_iff` / 定理 `mul_inv_le_one_iff`

English:
theorem mul_inv_le_one_iff
  statement: b * a⁻¹ <= 1 ↔ b <= a
  proof: _root_.trans mul_inv_le_iff_le_mul by rw [one_mul]

中文:
定理 mul_inv_le_one_iff
  结论: b * a⁻¹ <= 1 ↔ b <= a
  证明: _root_.trans mul_inv_le_iff_le_mul by rw [one_mul]

Depends on / 依赖: _root_, _root_.trans, mul_inv_le_iff_le_mul, one_mul
-/
theorem mul_inv_le_one_iff : b * a⁻¹ <= 1 ↔ b <= a :=
_root_.trans mul_inv_le_iff_le_mul by rw [one_mul]

end MulRightMono

section MulRightStrictMono

variable [LT α] [MulRightStrictMono α] {a b c : α}

/-- Uses `right` co(ntra)variant. -/
@[to_additive (attr := simp) /-- Uses `right` co(ntra)variant. -/]
/--
theorem `Right.inv_lt_one_iff` / 定理 `Right.inv_lt_one_iff`

English:
theorem Right.inv_lt_one_iff
  statement: a⁻¹ < 1 ↔ 1 < a
  proof: by
  rw [← mul_lt_mul_iff_right a]; rw [inv_mul_cancel]; rw [one_mul]

中文:
定理 Right.inv_lt_one_iff
  结论: a⁻¹ < 1 ↔ 1 < a
  证明: by
  rw [← mul_lt_mul_iff_right a]; rw [inv_mul_cancel]; rw [one_mul]

Depends on / 依赖: inv_mul_cancel, mul_lt_mul_iff_right, one_mul
-/
theorem Right.inv_lt_one_iff : a⁻¹ < 1 ↔ 1 < a := by
  rw [← mul_lt_mul_iff_right a]; rw [inv_mul_cancel]; rw [one_mul]

/-- Uses `right` co(ntra)variant. -/
@[to_additive (attr := simp) Right.neg_pos_iff /-- Uses `right` co(ntra)variant. -/]
/--
theorem `Right.one_lt_inv_iff` / 定理 `Right.one_lt_inv_iff`

English:
theorem Right.one_lt_inv_iff
  statement: 1 < a⁻¹ ↔ a < 1
  proof: by
  rw [← mul_lt_mul_iff_right a]; rw [inv_mul_cancel]; rw [one_mul]

@[to_additive]

中文:
定理 Right.one_lt_inv_iff
  结论: 1 < a⁻¹ ↔ a < 1
  证明: by
  rw [← mul_lt_mul_iff_right a]; rw [inv_mul_cancel]; rw [one_mul]

@[to_additive]

Depends on / 依赖: inv_mul_cancel, mul_lt_mul_iff_right, one_mul
-/
theorem Right.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1 := by
  rw [← mul_lt_mul_iff_right a]; rw [inv_mul_cancel]; rw [one_mul]

@[to_additive]
/--
theorem `inv_lt_iff_one_lt_mul` / 定理 `inv_lt_iff_one_lt_mul`

English:
theorem inv_lt_iff_one_lt_mul
  statement: a⁻¹ < b ↔ 1 < b * a
  proof: (mul_lt_mul_iff_right a).symm.trans by rw [inv_mul_cancel]

@[to_additive]

中文:
定理 inv_lt_iff_one_lt_mul
  结论: a⁻¹ < b ↔ 1 < b * a
  证明: (mul_lt_mul_iff_right a).symm.trans by rw [inv_mul_cancel]

@[to_additive]

Depends on / 依赖: inv_mul_cancel, mul_lt_mul_iff_right, symm.trans
-/
theorem inv_lt_iff_one_lt_mul : a⁻¹ < b ↔ 1 < b * a :=
(mul_lt_mul_iff_right a).symm.trans by rw [inv_mul_cancel]

@[to_additive]
/--
theorem `lt_inv_iff_mul_lt_one` / 定理 `lt_inv_iff_mul_lt_one`

English:
theorem lt_inv_iff_mul_lt_one
  statement: a < b⁻¹ ↔ a * b < 1
  proof: (mul_lt_mul_iff_right b).symm.trans by rw [inv_mul_cancel]

@[to_additive (attr := simp)]

中文:
定理 lt_inv_iff_mul_lt_one
  结论: a < b⁻¹ ↔ a * b < 1
  证明: (mul_lt_mul_iff_right b).symm.trans by rw [inv_mul_cancel]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_mul_cancel, mul_lt_mul_iff_right, symm.trans
-/
theorem lt_inv_iff_mul_lt_one : a < b⁻¹ ↔ a * b < 1 :=
(mul_lt_mul_iff_right b).symm.trans by rw [inv_mul_cancel]

@[to_additive (attr := simp)]
/--
theorem `mul_inv_lt_iff_lt_mul` / 定理 `mul_inv_lt_iff_lt_mul`

English:
theorem mul_inv_lt_iff_lt_mul
  statement: a * b⁻¹ < c ↔ a < c * b
  proof: by
  rw [← mul_lt_mul_iff_right b]; rw [inv_mul_cancel_right]

@[to_additive (attr := simp)]

中文:
定理 mul_inv_lt_iff_lt_mul
  结论: a * b⁻¹ < c ↔ a < c * b
  证明: by
  rw [← mul_lt_mul_iff_right b]; rw [inv_mul_cancel_right]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_mul_cancel_right, mul_lt_mul_iff_right
-/
theorem mul_inv_lt_iff_lt_mul : a * b⁻¹ < c ↔ a < c * b := by
  rw [← mul_lt_mul_iff_right b]; rw [inv_mul_cancel_right]

@[to_additive (attr := simp)]
/--
theorem `lt_mul_inv_iff_mul_lt` / 定理 `lt_mul_inv_iff_mul_lt`

English:
theorem lt_mul_inv_iff_mul_lt
  statement: c < a * b⁻¹ ↔ c * b < a
  proof: (mul_lt_mul_iff_right b).symm.trans by rw [inv_mul_cancel_right]

@[to_additive]

中文:
定理 lt_mul_inv_iff_mul_lt
  结论: c < a * b⁻¹ ↔ c * b < a
  证明: (mul_lt_mul_iff_right b).symm.trans by rw [inv_mul_cancel_right]

@[to_additive]

Depends on / 依赖: inv_mul_cancel_right, mul_lt_mul_iff_right, symm.trans
-/
theorem lt_mul_inv_iff_mul_lt : c < a * b⁻¹ ↔ c * b < a :=
(mul_lt_mul_iff_right b).symm.trans by rw [inv_mul_cancel_right]

@[to_additive]
/--
theorem `inv_mul_lt_one_iff_lt` / 定理 `inv_mul_lt_one_iff_lt`

English:
theorem inv_mul_lt_one_iff_lt
  statement: a * b⁻¹ < 1 ↔ a < b
  proof: by
  rw [← mul_lt_mul_iff_right b]; rw [inv_mul_cancel_right]; rw [one_mul]

@[to_additive]

中文:
定理 inv_mul_lt_one_iff_lt
  结论: a * b⁻¹ < 1 ↔ a < b
  证明: by
  rw [← mul_lt_mul_iff_right b]; rw [inv_mul_cancel_right]; rw [one_mul]

@[to_additive]

Depends on / 依赖: inv_mul_cancel_right, mul_lt_mul_iff_right, one_mul
-/
theorem inv_mul_lt_one_iff_lt : a * b⁻¹ < 1 ↔ a < b := by
  rw [← mul_lt_mul_iff_right b]; rw [inv_mul_cancel_right]; rw [one_mul]

@[to_additive]
/--
theorem `lt_mul_inv_iff_lt` / 定理 `lt_mul_inv_iff_lt`

English:
theorem lt_mul_inv_iff_lt
  statement: 1 < a * b⁻¹ ↔ b < a
  proof: by
  rw [← mul_lt_mul_iff_right b]; rw [one_mul]; rw [inv_mul_cancel_right]

@[to_additive]

中文:
定理 lt_mul_inv_iff_lt
  结论: 1 < a * b⁻¹ ↔ b < a
  证明: by
  rw [← mul_lt_mul_iff_right b]; rw [one_mul]; rw [inv_mul_cancel_right]

@[to_additive]

Depends on / 依赖: inv_mul_cancel_right, mul_lt_mul_iff_right, one_mul
-/
theorem lt_mul_inv_iff_lt : 1 < a * b⁻¹ ↔ b < a := by
  rw [← mul_lt_mul_iff_right b]; rw [one_mul]; rw [inv_mul_cancel_right]

@[to_additive]
/--
theorem `mul_inv_lt_one_iff` / 定理 `mul_inv_lt_one_iff`

English:
theorem mul_inv_lt_one_iff
  statement: b * a⁻¹ < 1 ↔ b < a
  proof: _root_.trans mul_inv_lt_iff_lt_mul by rw [one_mul]

中文:
定理 mul_inv_lt_one_iff
  结论: b * a⁻¹ < 1 ↔ b < a
  证明: _root_.trans mul_inv_lt_iff_lt_mul by rw [one_mul]

Depends on / 依赖: _root_, _root_.trans, mul_inv_lt_iff_lt_mul, one_mul
-/
theorem mul_inv_lt_one_iff : b * a⁻¹ < 1 ↔ b < a :=
_root_.trans mul_inv_lt_iff_lt_mul by rw [one_mul]

end MulRightStrictMono

section MulLeftMono_MulRightMono

variable [LE α] [MulLeftMono α] {a b c d : α}

@[to_additive (attr := simp)]
/--
theorem `div_le_self_iff` / 定理 `div_le_self_iff`

English:
theorem div_le_self_iff
  given: (a : α) {b : α}
  statement: a / b <= a ↔ 1 <= b
  proof: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 div_le_self_iff
  条件: (a : α) {b : α}
  结论: a / b <= a ↔ 1 <= b
  证明: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem div_le_self_iff (a : α) {b : α} : a / b <= a ↔ 1 <= b := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `le_div_self_iff` / 定理 `le_div_self_iff`

English:
theorem le_div_self_iff
  given: (a : α) {b : α}
  statement: a <= a / b ↔ b <= 1
  proof: by
  simp [div_eq_mul_inv]

alias ⟨_, sub_le_self⟩ := sub_le_self_iff

中文:
定理 le_div_self_iff
  条件: (a : α) {b : α}
  结论: a <= a / b ↔ b <= 1
  证明: by
  simp [div_eq_mul_inv]

alias ⟨_, sub_le_self⟩ := sub_le_self_iff

Depends on / 依赖: div_eq_mul_inv
-/
theorem le_div_self_iff (a : α) {b : α} : a <= a / b ↔ b <= 1 := by
  simp [div_eq_mul_inv]

alias ⟨_, sub_le_self⟩ := sub_le_self_iff

variable [MulRightMono α]

@[to_additive (attr := simp)]
/--
theorem `inv_le_inv_iff` / 定理 `inv_le_inv_iff`

English:
theorem inv_le_inv_iff
  statement: a⁻¹ <= b⁻¹ ↔ b <= a
  proof: by
  rw [← mul_le_mul_iff_left a]; rw [← mul_le_mul_iff_right b]
  simp

alias ⟨le_of_neg_le_neg, _⟩ := neg_le_neg_iff

@[to_additive]

中文:
定理 inv_le_inv_iff
  结论: a⁻¹ <= b⁻¹ ↔ b <= a
  证明: by
  rw [← mul_le_mul_iff_left a]; rw [← mul_le_mul_iff_right b]
  simp

alias ⟨le_of_neg_le_neg, _⟩ := neg_le_neg_iff

@[to_additive]

Depends on / 依赖: mul_le_mul_iff_left, mul_le_mul_iff_right
-/
theorem inv_le_inv_iff : a⁻¹ <= b⁻¹ ↔ b <= a := by
  rw [← mul_le_mul_iff_left a]; rw [← mul_le_mul_iff_right b]
  simp

alias ⟨le_of_neg_le_neg, _⟩ := neg_le_neg_iff

@[to_additive]
/--
theorem `mul_inv_le_inv_mul_iff` / 定理 `mul_inv_le_inv_mul_iff`

English:
theorem mul_inv_le_inv_mul_iff
  statement: a * b⁻¹ <= d⁻¹ * c ↔ d * a <= c * b
  proof: by
  rw [← mul_le_mul_iff_left d]; rw [← mul_le_mul_iff_right b]; rw [mul_inv_cancel_left]; rw [mul_assoc]; rw [inv_mul_cancel_right]

中文:
定理 mul_inv_le_inv_mul_iff
  结论: a * b⁻¹ <= d⁻¹ * c ↔ d * a <= c * b
  证明: by
  rw [← mul_le_mul_iff_left d]; rw [← mul_le_mul_iff_right b]; rw [mul_inv_cancel_left]; rw [mul_assoc]; rw [inv_mul_cancel_right]

Depends on / 依赖: inv_mul_cancel_right, mul_assoc, mul_inv_cancel_left, mul_le_mul_iff_left, mul_le_mul_iff_right
-/
theorem mul_inv_le_inv_mul_iff : a * b⁻¹ <= d⁻¹ * c ↔ d * a <= c * b := by
  rw [← mul_le_mul_iff_left d]; rw [← mul_le_mul_iff_right b]; rw [mul_inv_cancel_left]; rw [mul_assoc]; rw [inv_mul_cancel_right]

end MulLeftMono_MulRightMono

section MulLeftStrictMono_MulRightStrictMono

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

@[to_additive (attr := simp)]
/--
theorem `div_lt_self_iff` / 定理 `div_lt_self_iff`

English:
theorem div_lt_self_iff
  given: (a : α) {b : α}
  statement: a / b < a ↔ 1 < b
  proof: by
  simp [div_eq_mul_inv]

alias ⟨_, sub_lt_self⟩ := sub_lt_self_iff

中文:
定理 div_lt_self_iff
  条件: (a : α) {b : α}
  结论: a / b < a ↔ 1 < b
  证明: by
  simp [div_eq_mul_inv]

alias ⟨_, sub_lt_self⟩ := sub_lt_self_iff

Depends on / 依赖: div_eq_mul_inv
-/
theorem div_lt_self_iff (a : α) {b : α} : a / b < a ↔ 1 < b := by
  simp [div_eq_mul_inv]

alias ⟨_, sub_lt_self⟩ := sub_lt_self_iff

variable [MulRightStrictMono α]

@[to_additive (attr := simp)]
/--
theorem `inv_lt_inv_iff` / 定理 `inv_lt_inv_iff`

English:
theorem inv_lt_inv_iff
  statement: a⁻¹ < b⁻¹ ↔ b < a
  proof: by
  rw [← mul_lt_mul_iff_left a]; rw [← mul_lt_mul_iff_right b]
  simp

@[to_additive neg_lt]

中文:
定理 inv_lt_inv_iff
  结论: a⁻¹ < b⁻¹ ↔ b < a
  证明: by
  rw [← mul_lt_mul_iff_left a]; rw [← mul_lt_mul_iff_right b]
  simp

@[to_additive neg_lt]

Depends on / 依赖: mul_lt_mul_iff_left, mul_lt_mul_iff_right
-/
theorem inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a := by
  rw [← mul_lt_mul_iff_left a]; rw [← mul_lt_mul_iff_right b]
  simp

@[to_additive neg_lt]
/--
theorem `inv_lt'` / 定理 `inv_lt'`

English:
theorem inv_lt'
  statement: a⁻¹ < b ↔ b⁻¹ < a
  proof: by rw [← inv_lt_inv_iff, inv_inv]

@[to_additive lt_neg]

中文:
定理 inv_lt'
  结论: a⁻¹ < b ↔ b⁻¹ < a
  证明: by rw [← inv_lt_inv_iff, inv_inv]

@[to_additive lt_neg]

Depends on / 依赖: inv_inv, inv_lt_inv_iff
-/
theorem inv_lt' : a⁻¹ < b ↔ b⁻¹ < a := by rw [← inv_lt_inv_iff, inv_inv]

@[to_additive lt_neg]
/--
theorem `lt_inv'` / 定理 `lt_inv'`

English:
theorem lt_inv'
  statement: a < b⁻¹ ↔ b < a⁻¹
  proof: by rw [← inv_lt_inv_iff, inv_inv]

alias ⟨lt_inv_of_lt_inv, _⟩ := lt_inv'

中文:
定理 lt_inv'
  结论: a < b⁻¹ ↔ b < a⁻¹
  证明: by rw [← inv_lt_inv_iff, inv_inv]

alias ⟨lt_inv_of_lt_inv, _⟩ := lt_inv'

Depends on / 依赖: inv_inv, inv_lt_inv_iff
-/
theorem lt_inv' : a < b⁻¹ ↔ b < a⁻¹ := by rw [← inv_lt_inv_iff, inv_inv]

alias ⟨lt_inv_of_lt_inv, _⟩ := lt_inv'

attribute [to_additive] lt_inv_of_lt_inv

alias ⟨inv_lt_of_inv_lt', _⟩ := inv_lt'

attribute [to_additive neg_lt_of_neg_lt] inv_lt_of_inv_lt'

@[to_additive]
/--
theorem `mul_inv_lt_inv_mul_iff` / 定理 `mul_inv_lt_inv_mul_iff`

English:
theorem mul_inv_lt_inv_mul_iff
  statement: a * b⁻¹ < d⁻¹ * c ↔ d * a < c * b
  proof: by
  rw [← mul_lt_mul_iff_left d]; rw [← mul_lt_mul_iff_right b]; rw [mul_inv_cancel_left]; rw [mul_assoc]; rw [inv_mul_cancel_right]

中文:
定理 mul_inv_lt_inv_mul_iff
  结论: a * b⁻¹ < d⁻¹ * c ↔ d * a < c * b
  证明: by
  rw [← mul_lt_mul_iff_left d]; rw [← mul_lt_mul_iff_right b]; rw [mul_inv_cancel_left]; rw [mul_assoc]; rw [inv_mul_cancel_right]

Depends on / 依赖: inv_mul_cancel_right, mul_assoc, mul_inv_cancel_left, mul_lt_mul_iff_left, mul_lt_mul_iff_right
-/
theorem mul_inv_lt_inv_mul_iff : a * b⁻¹ < d⁻¹ * c ↔ d * a < c * b := by
  rw [← mul_lt_mul_iff_left d]; rw [← mul_lt_mul_iff_right b]; rw [mul_inv_cancel_left]; rw [mul_assoc]; rw [inv_mul_cancel_right]

end MulLeftStrictMono_MulRightStrictMono

section Preorder

variable [Preorder α]

section LeftLE

variable [MulLeftMono α] {a : α}

@[to_additive]
/--
theorem `Left.inv_le_self` / 定理 `Left.inv_le_self`

English:
theorem Left.inv_le_self
  given: (h : 1 <= a)
  statement: a⁻¹ <= a
  proof: le_trans (Left.inv_le_one_iff.mpr h) h

alias neg_le_self := Left.neg_le_self

@[to_additive]

中文:
定理 Left.inv_le_self
  条件: (h : 1 <= a)
  结论: a⁻¹ <= a
  证明: le_trans (Left.inv_le_one_iff.mpr h) h

alias neg_le_self := Left.neg_le_self

@[to_additive]

Depends on / 依赖: Left.inv_le_one_iff.mpr, inv_le_one_iff, le_trans
-/
theorem Left.inv_le_self (h : 1 <= a) : a⁻¹ <= a :=
  le_trans (Left.inv_le_one_iff.mpr h) h

alias neg_le_self := Left.neg_le_self

@[to_additive]
/--
theorem `Left.self_le_inv` / 定理 `Left.self_le_inv`

English:
theorem Left.self_le_inv
  given: (h : a <= 1)
  statement: a <= a⁻¹
  proof: le_trans h (Left.one_le_inv_iff.mpr h)

中文:
定理 Left.self_le_inv
  条件: (h : a <= 1)
  结论: a <= a⁻¹
  证明: le_trans h (Left.one_le_inv_iff.mpr h)

Depends on / 依赖: Left.one_le_inv_iff.mpr, le_trans, one_le_inv_iff
-/
theorem Left.self_le_inv (h : a <= 1) : a <= a⁻¹ :=
  le_trans h (Left.one_le_inv_iff.mpr h)

end LeftLE

section LeftLT

variable [MulLeftStrictMono α] {a : α}

@[to_additive]
/--
theorem `Left.inv_lt_self` / 定理 `Left.inv_lt_self`

English:
theorem Left.inv_lt_self
  given: (h : 1 < a)
  statement: a⁻¹ < a
  proof: (Left.inv_lt_one_iff.mpr h).trans h

alias neg_lt_self := Left.neg_lt_self

@[to_additive]

中文:
定理 Left.inv_lt_self
  条件: (h : 1 < a)
  结论: a⁻¹ < a
  证明: (Left.inv_lt_one_iff.mpr h).trans h

alias neg_lt_self := Left.neg_lt_self

@[to_additive]

Depends on / 依赖: Left.inv_lt_one_iff.mpr, inv_lt_one_iff
-/
theorem Left.inv_lt_self (h : 1 < a) : a⁻¹ < a :=
  (Left.inv_lt_one_iff.mpr h).trans h

alias neg_lt_self := Left.neg_lt_self

@[to_additive]
/--
theorem `Left.self_lt_inv` / 定理 `Left.self_lt_inv`

English:
theorem Left.self_lt_inv
  given: (h : a < 1)
  statement: a < a⁻¹
  proof: lt_trans h (Left.one_lt_inv_iff.mpr h)

中文:
定理 Left.self_lt_inv
  条件: (h : a < 1)
  结论: a < a⁻¹
  证明: lt_trans h (Left.one_lt_inv_iff.mpr h)

Depends on / 依赖: Left.one_lt_inv_iff.mpr, lt_trans, one_lt_inv_iff
-/
theorem Left.self_lt_inv (h : a < 1) : a < a⁻¹ :=
  lt_trans h (Left.one_lt_inv_iff.mpr h)

end LeftLT

section RightLE

variable [MulRightMono α] {a : α}

@[to_additive]
/--
theorem `Right.inv_le_self` / 定理 `Right.inv_le_self`

English:
theorem Right.inv_le_self
  given: (h : 1 <= a)
  statement: a⁻¹ <= a
  proof: le_trans (Right.inv_le_one_iff.mpr h) h

@[to_additive]

中文:
定理 Right.inv_le_self
  条件: (h : 1 <= a)
  结论: a⁻¹ <= a
  证明: le_trans (Right.inv_le_one_iff.mpr h) h

@[to_additive]

Depends on / 依赖: Right.inv_le_one_iff.mpr, inv_le_one_iff, le_trans
-/
theorem Right.inv_le_self (h : 1 <= a) : a⁻¹ <= a :=
  le_trans (Right.inv_le_one_iff.mpr h) h

@[to_additive]
/--
theorem `Right.self_le_inv` / 定理 `Right.self_le_inv`

English:
theorem Right.self_le_inv
  given: (h : a <= 1)
  statement: a <= a⁻¹
  proof: le_trans h (Right.one_le_inv_iff.mpr h)

中文:
定理 Right.self_le_inv
  条件: (h : a <= 1)
  结论: a <= a⁻¹
  证明: le_trans h (Right.one_le_inv_iff.mpr h)

Depends on / 依赖: Right.one_le_inv_iff.mpr, le_trans, one_le_inv_iff
-/
theorem Right.self_le_inv (h : a <= 1) : a <= a⁻¹ :=
  le_trans h (Right.one_le_inv_iff.mpr h)

end RightLE

section RightLT

variable [MulRightStrictMono α] {a : α}

@[to_additive]
/--
theorem `Right.inv_lt_self` / 定理 `Right.inv_lt_self`

English:
theorem Right.inv_lt_self
  given: (h : 1 < a)
  statement: a⁻¹ < a
  proof: (Right.inv_lt_one_iff.mpr h).trans h

@[to_additive]

中文:
定理 Right.inv_lt_self
  条件: (h : 1 < a)
  结论: a⁻¹ < a
  证明: (Right.inv_lt_one_iff.mpr h).trans h

@[to_additive]

Depends on / 依赖: Right.inv_lt_one_iff.mpr, inv_lt_one_iff
-/
theorem Right.inv_lt_self (h : 1 < a) : a⁻¹ < a :=
  (Right.inv_lt_one_iff.mpr h).trans h

@[to_additive]
/--
theorem `Right.self_lt_inv` / 定理 `Right.self_lt_inv`

English:
theorem Right.self_lt_inv
  given: (h : a < 1)
  statement: a < a⁻¹
  proof: lt_trans h (Right.one_lt_inv_iff.mpr h)

中文:
定理 Right.self_lt_inv
  条件: (h : a < 1)
  结论: a < a⁻¹
  证明: lt_trans h (Right.one_lt_inv_iff.mpr h)

Depends on / 依赖: Right.one_lt_inv_iff.mpr, lt_trans, one_lt_inv_iff
-/
theorem Right.self_lt_inv (h : a < 1) : a < a⁻¹ :=
  lt_trans h (Right.one_lt_inv_iff.mpr h)

end RightLT

end Preorder

end Group

section CommGroup

variable [CommGroup α]

section LE

variable [LE α] [MulLeftMono α] {a b c d : α}

@[to_additive]
/--
theorem `inv_mul_le_iff_le_mul'` / 定理 `inv_mul_le_iff_le_mul'`

English:
theorem inv_mul_le_iff_le_mul'
  statement: c⁻¹ * a <= b ↔ a <= b * c
  proof: by rw [inv_mul_le_iff_le_mul, mul_comm]

@[to_additive]

中文:
定理 inv_mul_le_iff_le_mul'
  结论: c⁻¹ * a <= b ↔ a <= b * c
  证明: by rw [inv_mul_le_iff_le_mul, mul_comm]

@[to_additive]

Depends on / 依赖: inv_mul_le_iff_le_mul, mul_comm
-/
theorem inv_mul_le_iff_le_mul' : c⁻¹ * a <= b ↔ a <= b * c := by rw [inv_mul_le_iff_le_mul, mul_comm]

@[to_additive]
/--
theorem `mul_inv_le_iff_le_mul'` / 定理 `mul_inv_le_iff_le_mul'`

English:
theorem mul_inv_le_iff_le_mul'
  statement: a * b⁻¹ <= c ↔ a <= b * c
  proof: by
  rw [← inv_mul_le_iff_le_mul]; rw [mul_comm]

@[to_additive add_neg_le_add_neg_iff]

中文:
定理 mul_inv_le_iff_le_mul'
  结论: a * b⁻¹ <= c ↔ a <= b * c
  证明: by
  rw [← inv_mul_le_iff_le_mul]; rw [mul_comm]

@[to_additive add_neg_le_add_neg_iff]

Depends on / 依赖: inv_mul_le_iff_le_mul, mul_comm
-/
theorem mul_inv_le_iff_le_mul' : a * b⁻¹ <= c ↔ a <= b * c := by
  rw [← inv_mul_le_iff_le_mul]; rw [mul_comm]

@[to_additive add_neg_le_add_neg_iff]
/--
theorem `mul_inv_le_mul_inv_iff'` / 定理 `mul_inv_le_mul_inv_iff'`

English:
theorem mul_inv_le_mul_inv_iff'
  statement: a * b⁻¹ <= c * d⁻¹ ↔ a * d <= c * b
  proof: by
  rw [mul_comm c]; rw [mul_inv_le_inv_mul_iff]; rw [mul_comm]

中文:
定理 mul_inv_le_mul_inv_iff'
  结论: a * b⁻¹ <= c * d⁻¹ ↔ a * d <= c * b
  证明: by
  rw [mul_comm c]; rw [mul_inv_le_inv_mul_iff]; rw [mul_comm]

Depends on / 依赖: mul_comm, mul_inv_le_inv_mul_iff
-/
theorem mul_inv_le_mul_inv_iff' : a * b⁻¹ <= c * d⁻¹ ↔ a * d <= c * b := by
  rw [mul_comm c]; rw [mul_inv_le_inv_mul_iff]; rw [mul_comm]

end LE

section LT

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

@[to_additive]
/--
theorem `inv_mul_lt_iff_lt_mul'` / 定理 `inv_mul_lt_iff_lt_mul'`

English:
theorem inv_mul_lt_iff_lt_mul'
  statement: c⁻¹ * a < b ↔ a < b * c
  proof: by rw [inv_mul_lt_iff_lt_mul, mul_comm]

@[to_additive]

中文:
定理 inv_mul_lt_iff_lt_mul'
  结论: c⁻¹ * a < b ↔ a < b * c
  证明: by rw [inv_mul_lt_iff_lt_mul, mul_comm]

@[to_additive]

Depends on / 依赖: inv_mul_lt_iff_lt_mul, mul_comm
-/
theorem inv_mul_lt_iff_lt_mul' : c⁻¹ * a < b ↔ a < b * c := by rw [inv_mul_lt_iff_lt_mul, mul_comm]

@[to_additive]
/--
theorem `mul_inv_lt_iff_le_mul'` / 定理 `mul_inv_lt_iff_le_mul'`

English:
theorem mul_inv_lt_iff_le_mul'
  statement: a * b⁻¹ < c ↔ a < b * c
  proof: by
  rw [← inv_mul_lt_iff_lt_mul]; rw [mul_comm]

@[to_additive add_neg_lt_add_neg_iff]

中文:
定理 mul_inv_lt_iff_le_mul'
  结论: a * b⁻¹ < c ↔ a < b * c
  证明: by
  rw [← inv_mul_lt_iff_lt_mul]; rw [mul_comm]

@[to_additive add_neg_lt_add_neg_iff]

Depends on / 依赖: inv_mul_lt_iff_lt_mul, mul_comm
-/
theorem mul_inv_lt_iff_le_mul' : a * b⁻¹ < c ↔ a < b * c := by
  rw [← inv_mul_lt_iff_lt_mul]; rw [mul_comm]

@[to_additive add_neg_lt_add_neg_iff]
/--
theorem `mul_inv_lt_mul_inv_iff'` / 定理 `mul_inv_lt_mul_inv_iff'`

English:
theorem mul_inv_lt_mul_inv_iff'
  statement: a * b⁻¹ < c * d⁻¹ ↔ a * d < c * b
  proof: by
  rw [mul_comm c]; rw [mul_inv_lt_inv_mul_iff]; rw [mul_comm]

中文:
定理 mul_inv_lt_mul_inv_iff'
  结论: a * b⁻¹ < c * d⁻¹ ↔ a * d < c * b
  证明: by
  rw [mul_comm c]; rw [mul_inv_lt_inv_mul_iff]; rw [mul_comm]

Depends on / 依赖: mul_comm, mul_inv_lt_inv_mul_iff
-/
theorem mul_inv_lt_mul_inv_iff' : a * b⁻¹ < c * d⁻¹ ↔ a * d < c * b := by
  rw [mul_comm c]; rw [mul_inv_lt_inv_mul_iff]; rw [mul_comm]

end LT

end CommGroup

alias ⟨one_le_of_inv_le_one, _⟩ := Left.inv_le_one_iff

attribute [to_additive] one_le_of_inv_le_one

alias ⟨le_one_of_one_le_inv, _⟩ := Left.one_le_inv_iff

attribute [to_additive nonpos_of_neg_nonneg] le_one_of_one_le_inv

alias ⟨lt_of_inv_lt_inv, _⟩ := inv_lt_inv_iff

attribute [to_additive] lt_of_inv_lt_inv

alias ⟨one_lt_of_inv_lt_one, _⟩ := Left.inv_lt_one_iff

attribute [to_additive] one_lt_of_inv_lt_one

alias inv_lt_one_iff_one_lt := Left.inv_lt_one_iff

attribute [to_additive] inv_lt_one_iff_one_lt

alias inv_lt_one' := Left.inv_lt_one_iff

attribute [to_additive neg_lt_zero] inv_lt_one'

alias ⟨inv_of_one_lt_inv, _⟩ := Left.one_lt_inv_iff

attribute [to_additive neg_of_neg_pos] inv_of_one_lt_inv

alias ⟨_, one_lt_inv_of_inv⟩ := Left.one_lt_inv_iff

attribute [to_additive neg_pos_of_neg] one_lt_inv_of_inv

alias ⟨mul_le_of_le_inv_mul, _⟩ := le_inv_mul_iff_mul_le

attribute [to_additive] mul_le_of_le_inv_mul

alias ⟨_, le_inv_mul_of_mul_le⟩ := le_inv_mul_iff_mul_le

attribute [to_additive] le_inv_mul_of_mul_le

alias ⟨_, inv_mul_le_of_le_mul⟩ := inv_mul_le_iff_le_mul

attribute [to_additive] inv_mul_le_of_le_mul

alias ⟨mul_lt_of_lt_inv_mul, _⟩ := lt_inv_mul_iff_mul_lt

attribute [to_additive] mul_lt_of_lt_inv_mul

alias ⟨_, lt_inv_mul_of_mul_lt⟩ := lt_inv_mul_iff_mul_lt

attribute [to_additive] lt_inv_mul_of_mul_lt

alias ⟨lt_mul_of_inv_mul_lt, inv_mul_lt_of_lt_mul⟩ := inv_mul_lt_iff_lt_mul

attribute [to_additive] lt_mul_of_inv_mul_lt

attribute [to_additive] inv_mul_lt_of_lt_mul

alias lt_mul_of_inv_mul_lt_left := lt_mul_of_inv_mul_lt

attribute [to_additive] lt_mul_of_inv_mul_lt_left

alias inv_le_one' := Left.inv_le_one_iff

attribute [to_additive neg_nonpos] inv_le_one'

alias one_le_inv' := Left.one_le_inv_iff

attribute [to_additive neg_nonneg] one_le_inv'

alias one_lt_inv' := Left.one_lt_inv_iff

attribute [to_additive neg_pos] one_lt_inv'

-- Most of the lemmas that are primed in this section appear in ordered_field.
-- I (DT) did not try to minimise the assumptions.
section Group

variable [Group α] [LE α]

section Right

variable [MulRightMono α] {a b c : α}

@[to_additive]
/--
theorem `div_le_div_iff_right` / 定理 `div_le_div_iff_right`

English:
theorem div_le_div_iff_right
  given: (c : α)
  statement: a / c <= b / c ↔ a <= b
  proof: by
  simpa only [div_eq_mul_inv] using mul_le_mul_iff_right _

@[to_additive (attr := gcongr) sub_le_sub_right]

中文:
定理 div_le_div_iff_right
  条件: (c : α)
  结论: a / c <= b / c ↔ a <= b
  证明: by
  simpa only [div_eq_mul_inv] using mul_le_mul_iff_right _

@[to_additive (attr := gcongr) sub_le_sub_right]

Depends on / 依赖: div_eq_mul_inv, mul_le_mul_iff_right
-/
theorem div_le_div_iff_right (c : α) : a / c <= b / c ↔ a <= b := by
  simpa only [div_eq_mul_inv] using mul_le_mul_iff_right _

@[to_additive (attr := gcongr) sub_le_sub_right]
/--
theorem `div_le_div_right'` / 定理 `div_le_div_right'`

English:
theorem div_le_div_right'
  given: (h : a <= b) (c : α)
  statement: a / c <= b / c
  proof: (div_le_div_iff_right c).2 h

@[to_additive (attr := simp) sub_nonneg]

中文:
定理 div_le_div_right'
  条件: (h : a <= b) (c : α)
  结论: a / c <= b / c
  证明: (div_le_div_iff_right c).2 h

@[to_additive (attr := simp) sub_nonneg]

Depends on / 依赖: div_le_div_iff_right
-/
theorem div_le_div_right' (h : a <= b) (c : α) : a / c <= b / c :=
  (div_le_div_iff_right c).2 h

@[to_additive (attr := simp) sub_nonneg]
/--
theorem `one_le_div'` / 定理 `one_le_div'`

English:
theorem one_le_div'
  statement: 1 <= a / b ↔ b <= a
  proof: by
  rw [← mul_le_mul_iff_right b]; rw [one_mul]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨le_of_sub_nonneg, sub_nonneg_of_le⟩ := sub_nonneg

@[to_additive sub_nonpos]

中文:
定理 one_le_div'
  结论: 1 <= a / b ↔ b <= a
  证明: by
  rw [← mul_le_mul_iff_right b]; rw [one_mul]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨le_of_sub_nonneg, sub_nonneg_of_le⟩ := sub_nonneg

@[to_additive sub_nonpos]

Depends on / 依赖: div_eq_mul_inv, inv_mul_cancel_right, mul_le_mul_iff_right, one_mul
-/
theorem one_le_div' : 1 <= a / b ↔ b <= a := by
  rw [← mul_le_mul_iff_right b]; rw [one_mul]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨le_of_sub_nonneg, sub_nonneg_of_le⟩ := sub_nonneg

@[to_additive sub_nonpos]
/--
theorem `div_le_one'` / 定理 `div_le_one'`

English:
theorem div_le_one'
  statement: a / b <= 1 ↔ a <= b
  proof: by
  rw [← mul_le_mul_iff_right b]; rw [one_mul]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨le_of_sub_nonpos, sub_nonpos_of_le⟩ := sub_nonpos

@[to_additive]

中文:
定理 div_le_one'
  结论: a / b <= 1 ↔ a <= b
  证明: by
  rw [← mul_le_mul_iff_right b]; rw [one_mul]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨le_of_sub_nonpos, sub_nonpos_of_le⟩ := sub_nonpos

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, inv_mul_cancel_right, mul_le_mul_iff_right, one_mul
-/
theorem div_le_one' : a / b <= 1 ↔ a <= b := by
  rw [← mul_le_mul_iff_right b]; rw [one_mul]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨le_of_sub_nonpos, sub_nonpos_of_le⟩ := sub_nonpos

@[to_additive]
/--
theorem `le_div_iff_mul_le` / 定理 `le_div_iff_mul_le`

English:
theorem le_div_iff_mul_le
  statement: a <= c / b ↔ a * b <= c
  proof: by
  rw [← mul_le_mul_iff_right b]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨add_le_of_le_sub_right, le_sub_right_of_add_le⟩ := le_sub_iff_add_le

@[to_additive]

中文:
定理 le_div_iff_mul_le
  结论: a <= c / b ↔ a * b <= c
  证明: by
  rw [← mul_le_mul_iff_right b]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨add_le_of_le_sub_right, le_sub_right_of_add_le⟩ := le_sub_iff_add_le

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, inv_mul_cancel_right, mul_le_mul_iff_right
-/
theorem le_div_iff_mul_le : a <= c / b ↔ a * b <= c := by
  rw [← mul_le_mul_iff_right b]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨add_le_of_le_sub_right, le_sub_right_of_add_le⟩ := le_sub_iff_add_le

@[to_additive]
/--
theorem `div_le_iff_le_mul` / 定理 `div_le_iff_le_mul`

English:
theorem div_le_iff_le_mul
  statement: a / c <= b ↔ a <= b * c
  proof: by
  rw [← mul_le_mul_iff_right c]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

中文:
定理 div_le_iff_le_mul
  结论: a / c <= b ↔ a <= b * c
  证明: by
  rw [← mul_le_mul_iff_right c]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

Depends on / 依赖: div_eq_mul_inv, inv_mul_cancel_right, mul_le_mul_iff_right
-/
theorem div_le_iff_le_mul : a / c <= b ↔ a <= b * c := by
  rw [← mul_le_mul_iff_right c]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

-- Note: we intentionally don't have `@[simp]` for the additive version,
-- since the LHS simplifies with `tsub_le_iff_right`
attribute [simp] div_le_iff_le_mul

-- TODO: Should we get rid of `sub_le_iff_le_add` in favor of
-- (a renamed version of) `tsub_le_iff_right`?
-- see Note [lower instance priority]
instance (priority := 100) AddGroup.toOrderedSub {α : Type*} [AddGroup α] [LE α]
    [AddRightMono α] : OrderedSub α :=
  ⟨fun _ _ _ => sub_le_iff_le_add⟩

end Right

section Left

variable [MulLeftMono α] [MulRightMono α] {a b c : α}

@[to_additive]
/--
theorem `div_le_div_iff_left` / 定理 `div_le_div_iff_left`

English:
theorem div_le_div_iff_left
  given: (a : α)
  statement: a / b <= a / c ↔ c <= b
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← mul_le_mul_iff_left a⁻¹]; rw [inv_mul_cancel_left]; rw [inv_mul_cancel_left]; rw [inv_le_inv_iff]

@[to_additive (attr := gcongr) sub_le_sub_left]

中文:
定理 div_le_div_iff_left
  条件: (a : α)
  结论: a / b <= a / c ↔ c <= b
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← mul_le_mul_iff_left a⁻¹]; rw [inv_mul_cancel_left]; rw [inv_mul_cancel_left]; rw [inv_le_inv_iff]

@[to_additive (attr := gcongr) sub_le_sub_left]

Depends on / 依赖: div_eq_mul_inv, inv_le_inv_iff, inv_mul_cancel_left, mul_le_mul_iff_left
-/
theorem div_le_div_iff_left (a : α) : a / b <= a / c ↔ c <= b := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← mul_le_mul_iff_left a⁻¹]; rw [inv_mul_cancel_left]; rw [inv_mul_cancel_left]; rw [inv_le_inv_iff]

@[to_additive (attr := gcongr) sub_le_sub_left]
/--
theorem `div_le_div_left'` / 定理 `div_le_div_left'`

English:
theorem div_le_div_left'
  given: (h : a <= b) (c : α)
  statement: c / b <= c / a
  proof: (div_le_div_iff_left c).2 h

中文:
定理 div_le_div_left'
  条件: (h : a <= b) (c : α)
  结论: c / b <= c / a
  证明: (div_le_div_iff_left c).2 h

Depends on / 依赖: div_le_div_iff_left
-/
theorem div_le_div_left' (h : a <= b) (c : α) : c / b <= c / a :=
  (div_le_div_iff_left c).2 h

end Left

end Group

section CommGroup

variable [CommGroup α]

section LE

variable [LE α] [MulLeftMono α] {a b c d : α}

/-- See also `div_le_div_iff` for a version that works for `LinearOrderedSemifield` with
additional assumptions. -/
@[to_additive sub_le_sub_iff]
/--
theorem `div_le_div_iff'` / 定理 `div_le_div_iff'`

English:
theorem div_le_div_iff'
  statement: a / b <= c / d ↔ a * d <= c * b
  proof: by
  simpa only [div_eq_mul_inv] using mul_inv_le_mul_inv_iff'

@[to_additive]

中文:
定理 div_le_div_iff'
  结论: a / b <= c / d ↔ a * d <= c * b
  证明: by
  simpa only [div_eq_mul_inv] using mul_inv_le_mul_inv_iff'

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, mul_inv_le_mul_inv_iff
-/
theorem div_le_div_iff' : a / b <= c / d ↔ a * d <= c * b := by
  simpa only [div_eq_mul_inv] using mul_inv_le_mul_inv_iff'

@[to_additive]
/--
theorem `le_div_iff_mul_le'` / 定理 `le_div_iff_mul_le'`

English:
theorem le_div_iff_mul_le'
  statement: b <= c / a ↔ a * b <= c
  proof: by rw [le_div_iff_mul_le, mul_comm]

alias ⟨add_le_of_le_sub_left, le_sub_left_of_add_le⟩ := le_sub_iff_add_le'

@[to_additive]

中文:
定理 le_div_iff_mul_le'
  结论: b <= c / a ↔ a * b <= c
  证明: by rw [le_div_iff_mul_le, mul_comm]

alias ⟨add_le_of_le_sub_left, le_sub_left_of_add_le⟩ := le_sub_iff_add_le'

@[to_additive]

Depends on / 依赖: le_div_iff_mul_le, mul_comm
-/
theorem le_div_iff_mul_le' : b <= c / a ↔ a * b <= c := by rw [le_div_iff_mul_le, mul_comm]

alias ⟨add_le_of_le_sub_left, le_sub_left_of_add_le⟩ := le_sub_iff_add_le'

@[to_additive]
/--
theorem `div_le_iff_le_mul'` / 定理 `div_le_iff_le_mul'`

English:
theorem div_le_iff_le_mul'
  statement: a / b <= c ↔ a <= b * c
  proof: by rw [div_le_iff_le_mul, mul_comm]

alias ⟨le_add_of_sub_left_le, sub_left_le_of_le_add⟩ := sub_le_iff_le_add'

@[to_additive (attr := simp)]

中文:
定理 div_le_iff_le_mul'
  结论: a / b <= c ↔ a <= b * c
  证明: by rw [div_le_iff_le_mul, mul_comm]

alias ⟨le_add_of_sub_left_le, sub_left_le_of_le_add⟩ := sub_le_iff_le_add'

@[to_additive (attr := simp)]

Depends on / 依赖: div_le_iff_le_mul, mul_comm
-/
theorem div_le_iff_le_mul' : a / b <= c ↔ a <= b * c := by rw [div_le_iff_le_mul, mul_comm]

alias ⟨le_add_of_sub_left_le, sub_left_le_of_le_add⟩ := sub_le_iff_le_add'

@[to_additive (attr := simp)]
/--
theorem `inv_le_div_iff_le_mul` / 定理 `inv_le_div_iff_le_mul`

English:
theorem inv_le_div_iff_le_mul
  statement: b⁻¹ <= a / c ↔ c <= a * b
  proof: le_div_iff_mul_le.trans inv_mul_le_iff_le_mul'

@[to_additive]

中文:
定理 inv_le_div_iff_le_mul
  结论: b⁻¹ <= a / c ↔ c <= a * b
  证明: le_div_iff_mul_le.trans inv_mul_le_iff_le_mul'

@[to_additive]

Depends on / 依赖: inv_mul_le_iff_le_mul, le_div_iff_mul_le, le_div_iff_mul_le.trans
-/
theorem inv_le_div_iff_le_mul : b⁻¹ <= a / c ↔ c <= a * b :=
  le_div_iff_mul_le.trans inv_mul_le_iff_le_mul'

@[to_additive]
/--
theorem `inv_le_div_iff_le_mul'` / 定理 `inv_le_div_iff_le_mul'`

English:
theorem inv_le_div_iff_le_mul'
  statement: a⁻¹ <= b / c ↔ c <= a * b
  proof: by rw [inv_le_div_iff_le_mul, mul_comm]

@[to_additive]

中文:
定理 inv_le_div_iff_le_mul'
  结论: a⁻¹ <= b / c ↔ c <= a * b
  证明: by rw [inv_le_div_iff_le_mul, mul_comm]

@[to_additive]

Depends on / 依赖: inv_le_div_iff_le_mul, mul_comm
-/
theorem inv_le_div_iff_le_mul' : a⁻¹ <= b / c ↔ c <= a * b := by rw [inv_le_div_iff_le_mul, mul_comm]

@[to_additive]
/--
theorem `div_le_comm` / 定理 `div_le_comm`

English:
theorem div_le_comm
  statement: a / b <= c ↔ a / c <= b
  proof: div_le_iff_le_mul'.trans div_le_iff_le_mul.symm

@[to_additive]

中文:
定理 div_le_comm
  结论: a / b <= c ↔ a / c <= b
  证明: div_le_iff_le_mul'.trans div_le_iff_le_mul.symm

@[to_additive]

Depends on / 依赖: div_le_iff_le_mul, div_le_iff_le_mul.symm
-/
theorem div_le_comm : a / b <= c ↔ a / c <= b :=
  div_le_iff_le_mul'.trans div_le_iff_le_mul.symm

@[to_additive]
/--
theorem `le_div_comm` / 定理 `le_div_comm`

English:
theorem le_div_comm
  statement: a <= b / c ↔ c <= b / a
  proof: le_div_iff_mul_le'.trans le_div_iff_mul_le.symm

中文:
定理 le_div_comm
  结论: a <= b / c ↔ c <= b / a
  证明: le_div_iff_mul_le'.trans le_div_iff_mul_le.symm

Depends on / 依赖: le_div_iff_mul_le, le_div_iff_mul_le.symm
-/
theorem le_div_comm : a <= b / c ↔ c <= b / a :=
  le_div_iff_mul_le'.trans le_div_iff_mul_le.symm

end LE

section Preorder

variable [Preorder α] [MulLeftMono α] {a b c d : α}

@[to_additive (attr := gcongr) sub_le_sub]
/--
theorem `div_le_div''` / 定理 `div_le_div''`

English:
theorem div_le_div''
  given: (hab : a <= b) (hcd : c <= d)
  statement: a / d <= b / c
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_comm b]; rw [mul_inv_le_inv_mul_iff]; rw [mul_comm]
  exact mul_le_mul' hab hcd

中文:
定理 div_le_div''
  条件: (hab : a <= b) (hcd : c <= d)
  结论: a / d <= b / c
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_comm b]; rw [mul_inv_le_inv_mul_iff]; rw [mul_comm]
  exact mul_le_mul' hab hcd

Depends on / 依赖: div_eq_mul_inv, mul_comm, mul_inv_le_inv_mul_iff, mul_le_mul
-/
theorem div_le_div'' (hab : a <= b) (hcd : c <= d) : a / d <= b / c := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_comm b]; rw [mul_inv_le_inv_mul_iff]; rw [mul_comm]
  exact mul_le_mul' hab hcd

end Preorder

end CommGroup

-- Most of the lemmas that are primed in this section appear in ordered_field.
-- I (DT) did not try to minimise the assumptions.
section Group

variable [Group α] [LT α]

section Right

variable [MulRightStrictMono α] {a b c : α}

@[to_additive (attr := simp)]
/--
theorem `div_lt_div_iff_right` / 定理 `div_lt_div_iff_right`

English:
theorem div_lt_div_iff_right
  given: (c : α)
  statement: a / c < b / c ↔ a < b
  proof: by
  simpa only [div_eq_mul_inv] using mul_lt_mul_iff_right _

@[to_additive (attr := gcongr) sub_lt_sub_right]

中文:
定理 div_lt_div_iff_right
  条件: (c : α)
  结论: a / c < b / c ↔ a < b
  证明: by
  simpa only [div_eq_mul_inv] using mul_lt_mul_iff_right _

@[to_additive (attr := gcongr) sub_lt_sub_right]

Depends on / 依赖: div_eq_mul_inv, mul_lt_mul_iff_right
-/
theorem div_lt_div_iff_right (c : α) : a / c < b / c ↔ a < b := by
  simpa only [div_eq_mul_inv] using mul_lt_mul_iff_right _

@[to_additive (attr := gcongr) sub_lt_sub_right]
/--
theorem `div_lt_div_right'` / 定理 `div_lt_div_right'`

English:
theorem div_lt_div_right'
  given: (h : a < b) (c : α)
  statement: a / c < b / c
  proof: (div_lt_div_iff_right c).2 h

@[to_additive (attr := simp) sub_pos]

中文:
定理 div_lt_div_right'
  条件: (h : a < b) (c : α)
  结论: a / c < b / c
  证明: (div_lt_div_iff_right c).2 h

@[to_additive (attr := simp) sub_pos]

Depends on / 依赖: div_lt_div_iff_right
-/
theorem div_lt_div_right' (h : a < b) (c : α) : a / c < b / c :=
  (div_lt_div_iff_right c).2 h

@[to_additive (attr := simp) sub_pos]
/--
theorem `one_lt_div'` / 定理 `one_lt_div'`

English:
theorem one_lt_div'
  statement: 1 < a / b ↔ b < a
  proof: by
  rw [← mul_lt_mul_iff_right b]; rw [one_mul]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨lt_of_sub_pos, sub_pos_of_lt⟩ := sub_pos

@[to_additive (attr := simp) sub_neg /-- For `a - -b = a + b`, see `sub_neg_eq_add`. -/]

中文:
定理 one_lt_div'
  结论: 1 < a / b ↔ b < a
  证明: by
  rw [← mul_lt_mul_iff_right b]; rw [one_mul]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨lt_of_sub_pos, sub_pos_of_lt⟩ := sub_pos

@[to_additive (attr := simp) sub_neg /-- For `a - -b = a + b`, see `sub_neg_eq_add`. -/]

Depends on / 依赖: div_eq_mul_inv, inv_mul_cancel_right, mul_lt_mul_iff_right, one_mul
-/
theorem one_lt_div' : 1 < a / b ↔ b < a := by
  rw [← mul_lt_mul_iff_right b]; rw [one_mul]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨lt_of_sub_pos, sub_pos_of_lt⟩ := sub_pos

@[to_additive (attr := simp) sub_neg /-- For `a - -b = a + b`, see `sub_neg_eq_add`. -/]
/--
theorem `div_lt_one'` / 定理 `div_lt_one'`

English:
theorem div_lt_one'
  statement: a / b < 1 ↔ a < b
  proof: by
  rw [← mul_lt_mul_iff_right b]; rw [one_mul]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨lt_of_sub_neg, sub_neg_of_lt⟩ := sub_neg

alias sub_lt_zero := sub_neg

@[to_additive]

中文:
定理 div_lt_one'
  结论: a / b < 1 ↔ a < b
  证明: by
  rw [← mul_lt_mul_iff_right b]; rw [one_mul]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨lt_of_sub_neg, sub_neg_of_lt⟩ := sub_neg

alias sub_lt_zero := sub_neg

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, inv_mul_cancel_right, mul_lt_mul_iff_right, one_mul
-/
theorem div_lt_one' : a / b < 1 ↔ a < b := by
  rw [← mul_lt_mul_iff_right b]; rw [one_mul]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨lt_of_sub_neg, sub_neg_of_lt⟩ := sub_neg

alias sub_lt_zero := sub_neg

@[to_additive]
/--
theorem `lt_div_iff_mul_lt` / 定理 `lt_div_iff_mul_lt`

English:
theorem lt_div_iff_mul_lt
  statement: a < c / b ↔ a * b < c
  proof: by
  rw [← mul_lt_mul_iff_right b]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨add_lt_of_lt_sub_right, lt_sub_right_of_add_lt⟩ := lt_sub_iff_add_lt

@[to_additive]

中文:
定理 lt_div_iff_mul_lt
  结论: a < c / b ↔ a * b < c
  证明: by
  rw [← mul_lt_mul_iff_right b]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨add_lt_of_lt_sub_right, lt_sub_right_of_add_lt⟩ := lt_sub_iff_add_lt

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, inv_mul_cancel_right, mul_lt_mul_iff_right
-/
theorem lt_div_iff_mul_lt : a < c / b ↔ a * b < c := by
  rw [← mul_lt_mul_iff_right b]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨add_lt_of_lt_sub_right, lt_sub_right_of_add_lt⟩ := lt_sub_iff_add_lt

@[to_additive]
/--
theorem `div_lt_iff_lt_mul` / 定理 `div_lt_iff_lt_mul`

English:
theorem div_lt_iff_lt_mul
  statement: a / c < b ↔ a < b * c
  proof: by
  rw [← mul_lt_mul_iff_right c]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨lt_add_of_sub_right_lt, sub_right_lt_of_lt_add⟩ := sub_lt_iff_lt_add

中文:
定理 div_lt_iff_lt_mul
  结论: a / c < b ↔ a < b * c
  证明: by
  rw [← mul_lt_mul_iff_right c]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨lt_add_of_sub_right_lt, sub_right_lt_of_lt_add⟩ := sub_lt_iff_lt_add

Depends on / 依赖: div_eq_mul_inv, inv_mul_cancel_right, mul_lt_mul_iff_right
-/
theorem div_lt_iff_lt_mul : a / c < b ↔ a < b * c := by
  rw [← mul_lt_mul_iff_right c]; rw [div_eq_mul_inv]; rw [inv_mul_cancel_right]

alias ⟨lt_add_of_sub_right_lt, sub_right_lt_of_lt_add⟩ := sub_lt_iff_lt_add

end Right

section Left

variable [MulLeftStrictMono α] [MulRightStrictMono α]
  {a b c : α}

@[to_additive (attr := simp)]
/--
theorem `div_lt_div_iff_left` / 定理 `div_lt_div_iff_left`

English:
theorem div_lt_div_iff_left
  given: (a : α)
  statement: a / b < a / c ↔ c < b
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← mul_lt_mul_iff_left a⁻¹]; rw [inv_mul_cancel_left]; rw [inv_mul_cancel_left]; rw [inv_lt_inv_iff]

@[to_additive (attr := simp)]

中文:
定理 div_lt_div_iff_left
  条件: (a : α)
  结论: a / b < a / c ↔ c < b
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← mul_lt_mul_iff_left a⁻¹]; rw [inv_mul_cancel_left]; rw [inv_mul_cancel_left]; rw [inv_lt_inv_iff]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv, inv_lt_inv_iff, inv_mul_cancel_left, mul_lt_mul_iff_left
-/
theorem div_lt_div_iff_left (a : α) : a / b < a / c ↔ c < b := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← mul_lt_mul_iff_left a⁻¹]; rw [inv_mul_cancel_left]; rw [inv_mul_cancel_left]; rw [inv_lt_inv_iff]

@[to_additive (attr := simp)]
/--
theorem `inv_lt_div_iff_lt_mul` / 定理 `inv_lt_div_iff_lt_mul`

English:
theorem inv_lt_div_iff_lt_mul
  statement: a⁻¹ < b / c ↔ c < a * b
  proof: by
  rw [div_eq_mul_inv]; rw [lt_mul_inv_iff_mul_lt]; rw [inv_mul_lt_iff_lt_mul]

@[to_additive (attr := gcongr) sub_lt_sub_left]

中文:
定理 inv_lt_div_iff_lt_mul
  结论: a⁻¹ < b / c ↔ c < a * b
  证明: by
  rw [div_eq_mul_inv]; rw [lt_mul_inv_iff_mul_lt]; rw [inv_mul_lt_iff_lt_mul]

@[to_additive (attr := gcongr) sub_lt_sub_left]

Depends on / 依赖: div_eq_mul_inv, inv_mul_lt_iff_lt_mul, lt_mul_inv_iff_mul_lt
-/
theorem inv_lt_div_iff_lt_mul : a⁻¹ < b / c ↔ c < a * b := by
  rw [div_eq_mul_inv]; rw [lt_mul_inv_iff_mul_lt]; rw [inv_mul_lt_iff_lt_mul]

@[to_additive (attr := gcongr) sub_lt_sub_left]
/--
theorem `div_lt_div_left'` / 定理 `div_lt_div_left'`

English:
theorem div_lt_div_left'
  given: (h : a < b) (c : α)
  statement: c / b < c / a
  proof: (div_lt_div_iff_left c).2 h

中文:
定理 div_lt_div_left'
  条件: (h : a < b) (c : α)
  结论: c / b < c / a
  证明: (div_lt_div_iff_left c).2 h

Depends on / 依赖: div_lt_div_iff_left
-/
theorem div_lt_div_left' (h : a < b) (c : α) : c / b < c / a :=
  (div_lt_div_iff_left c).2 h

end Left

end Group

section CommGroup

variable [CommGroup α]

section LT

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

@[to_additive sub_lt_sub_iff]
/--
theorem `div_lt_div_iff'` / 定理 `div_lt_div_iff'`

English:
theorem div_lt_div_iff'
  statement: a / b < c / d ↔ a * d < c * b
  proof: by
  simpa only [div_eq_mul_inv] using mul_inv_lt_mul_inv_iff'

@[to_additive]

中文:
定理 div_lt_div_iff'
  结论: a / b < c / d ↔ a * d < c * b
  证明: by
  simpa only [div_eq_mul_inv] using mul_inv_lt_mul_inv_iff'

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, mul_inv_lt_mul_inv_iff
-/
theorem div_lt_div_iff' : a / b < c / d ↔ a * d < c * b := by
  simpa only [div_eq_mul_inv] using mul_inv_lt_mul_inv_iff'

@[to_additive]
/--
theorem `lt_div_iff_mul_lt'` / 定理 `lt_div_iff_mul_lt'`

English:
theorem lt_div_iff_mul_lt'
  statement: b < c / a ↔ a * b < c
  proof: by rw [lt_div_iff_mul_lt, mul_comm]

alias ⟨add_lt_of_lt_sub_left, lt_sub_left_of_add_lt⟩ := lt_sub_iff_add_lt'

@[to_additive]

中文:
定理 lt_div_iff_mul_lt'
  结论: b < c / a ↔ a * b < c
  证明: by rw [lt_div_iff_mul_lt, mul_comm]

alias ⟨add_lt_of_lt_sub_left, lt_sub_left_of_add_lt⟩ := lt_sub_iff_add_lt'

@[to_additive]

Depends on / 依赖: lt_div_iff_mul_lt, mul_comm
-/
theorem lt_div_iff_mul_lt' : b < c / a ↔ a * b < c := by rw [lt_div_iff_mul_lt, mul_comm]

alias ⟨add_lt_of_lt_sub_left, lt_sub_left_of_add_lt⟩ := lt_sub_iff_add_lt'

@[to_additive]
/--
theorem `div_lt_iff_lt_mul'` / 定理 `div_lt_iff_lt_mul'`

English:
theorem div_lt_iff_lt_mul'
  statement: a / b < c ↔ a < b * c
  proof: by rw [div_lt_iff_lt_mul, mul_comm]

alias ⟨lt_add_of_sub_left_lt, sub_left_lt_of_lt_add⟩ := sub_lt_iff_lt_add'

@[to_additive]

中文:
定理 div_lt_iff_lt_mul'
  结论: a / b < c ↔ a < b * c
  证明: by rw [div_lt_iff_lt_mul, mul_comm]

alias ⟨lt_add_of_sub_left_lt, sub_left_lt_of_lt_add⟩ := sub_lt_iff_lt_add'

@[to_additive]

Depends on / 依赖: div_lt_iff_lt_mul, mul_comm
-/
theorem div_lt_iff_lt_mul' : a / b < c ↔ a < b * c := by rw [div_lt_iff_lt_mul, mul_comm]

alias ⟨lt_add_of_sub_left_lt, sub_left_lt_of_lt_add⟩ := sub_lt_iff_lt_add'

@[to_additive]
/--
theorem `inv_lt_div_iff_lt_mul'` / 定理 `inv_lt_div_iff_lt_mul'`

English:
theorem inv_lt_div_iff_lt_mul'
  statement: b⁻¹ < a / c ↔ c < a * b
  proof: lt_div_iff_mul_lt.trans inv_mul_lt_iff_lt_mul'

@[to_additive]

中文:
定理 inv_lt_div_iff_lt_mul'
  结论: b⁻¹ < a / c ↔ c < a * b
  证明: lt_div_iff_mul_lt.trans inv_mul_lt_iff_lt_mul'

@[to_additive]

Depends on / 依赖: inv_mul_lt_iff_lt_mul, lt_div_iff_mul_lt, lt_div_iff_mul_lt.trans
-/
theorem inv_lt_div_iff_lt_mul' : b⁻¹ < a / c ↔ c < a * b :=
  lt_div_iff_mul_lt.trans inv_mul_lt_iff_lt_mul'

@[to_additive]
/--
theorem `div_lt_comm` / 定理 `div_lt_comm`

English:
theorem div_lt_comm
  statement: a / b < c ↔ a / c < b
  proof: div_lt_iff_lt_mul'.trans div_lt_iff_lt_mul.symm

@[to_additive]

中文:
定理 div_lt_comm
  结论: a / b < c ↔ a / c < b
  证明: div_lt_iff_lt_mul'.trans div_lt_iff_lt_mul.symm

@[to_additive]

Depends on / 依赖: div_lt_iff_lt_mul, div_lt_iff_lt_mul.symm
-/
theorem div_lt_comm : a / b < c ↔ a / c < b :=
  div_lt_iff_lt_mul'.trans div_lt_iff_lt_mul.symm

@[to_additive]
/--
theorem `lt_div_comm` / 定理 `lt_div_comm`

English:
theorem lt_div_comm
  statement: a < b / c ↔ c < b / a
  proof: lt_div_iff_mul_lt'.trans lt_div_iff_mul_lt.symm

中文:
定理 lt_div_comm
  结论: a < b / c ↔ c < b / a
  证明: lt_div_iff_mul_lt'.trans lt_div_iff_mul_lt.symm

Depends on / 依赖: lt_div_iff_mul_lt, lt_div_iff_mul_lt.symm
-/
theorem lt_div_comm : a < b / c ↔ c < b / a :=
  lt_div_iff_mul_lt'.trans lt_div_iff_mul_lt.symm

end LT

section Preorder

variable [Preorder α] [MulLeftStrictMono α] {a b c d : α}

@[to_additive (attr := gcongr) sub_lt_sub]
/--
theorem `div_lt_div''` / 定理 `div_lt_div''`

English:
theorem div_lt_div''
  given: (hab : a < b) (hcd : c < d)
  statement: a / d < b / c
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_comm b]; rw [mul_inv_lt_inv_mul_iff]; rw [mul_comm]
  exact mul_lt_mul_of_lt_of_lt hab hcd

中文:
定理 div_lt_div''
  条件: (hab : a < b) (hcd : c < d)
  结论: a / d < b / c
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_comm b]; rw [mul_inv_lt_inv_mul_iff]; rw [mul_comm]
  exact mul_lt_mul_of_lt_of_lt hab hcd

Depends on / 依赖: div_eq_mul_inv, mul_comm, mul_inv_lt_inv_mul_iff, mul_lt_mul_of_lt_of_lt
-/
theorem div_lt_div'' (hab : a < b) (hcd : c < d) : a / d < b / c := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_comm b]; rw [mul_inv_lt_inv_mul_iff]; rw [mul_comm]
  exact mul_lt_mul_of_lt_of_lt hab hcd

end Preorder

section LinearOrder
variable [LinearOrder α] [MulLeftMono α] {a b c d : α}

/--
lemma `lt_or_lt_of_div_lt_div` / 引理 `lt_or_lt_of_div_lt_div`

English:
lemma lt_or_lt_of_div_lt_div
  statement: a / d < b / c -> a < b ∨ c < d
  proof: by
  contrapose!; exact fun h => div_le_div'' h.1 h.2

中文:
引理 lt_or_lt_of_div_lt_div
  结论: a / d < b / c -> a < b ∨ c < d
  证明: by
  contrapose!; exact fun h => div_le_div'' h.1 h.2
-/
@[to_additive] lemma lt_or_lt_of_div_lt_div : a / d < b / c -> a < b ∨ c < d := by
  contrapose!; exact fun h => div_le_div'' h.1 h.2

end LinearOrder
end CommGroup

section LinearOrder

variable [Group α] [LinearOrder α]

@[to_additive (attr := simp) cmp_sub_zero]
/--
theorem `cmp_div_one'` / 定理 `cmp_div_one'`

English:
theorem cmp_div_one'
  given: [MulRightMono α] (a b : α)
  proof: by rw [← cmp_mul_right' _ _ b, one_mul, div_mul_cancel]

中文:
定理 cmp_div_one'
  条件: [MulRightMono α] (a b : α)
  证明: by rw [← cmp_mul_right' _ _ b, one_mul, div_mul_cancel]

Depends on / 依赖: cmp_mul_right, div_mul_cancel, one_mul
-/
theorem cmp_div_one' [MulRightMono α] (a b : α) :
    cmp (a / b) 1 = cmp a b := by rw [← cmp_mul_right' _ _ b, one_mul, div_mul_cancel]

variable [MulLeftMono α]

section VariableNames

variable {a b : α}

@[to_additive]
/--
theorem `le_of_forall_one_lt_lt_mul` / 定理 `le_of_forall_one_lt_lt_mul`

English:
theorem le_of_forall_one_lt_lt_mul
  given: (h : forall ε : α, 1 < ε -> a < b * ε)
  statement: a <= b
  proof: le_of_not_gt fun h₁ => lt_irrefl a (by simpa using h _ (lt_inv_mul_iff_lt.mpr h₁))

@[to_additive]

中文:
定理 le_of_forall_one_lt_lt_mul
  条件: (h : 对任意 ε : α, 1 < ε -> a < b * ε)
  结论: a <= b
  证明: le_of_not_gt fun h₁ => lt_irrefl a (by simpa using h _ (lt_inv_mul_iff_lt.mpr h₁))

@[to_additive]

Depends on / 依赖: le_of_not_gt, lt_inv_mul_iff_lt, lt_inv_mul_iff_lt.mpr, lt_irrefl
-/
theorem le_of_forall_one_lt_lt_mul (h : forall ε : α, 1 < ε -> a < b * ε) : a <= b :=
  le_of_not_gt fun h₁ => lt_irrefl a (by simpa using h _ (lt_inv_mul_iff_lt.mpr h₁))

@[to_additive]
/--
theorem `le_iff_forall_one_lt_lt_mul` / 定理 `le_iff_forall_one_lt_lt_mul`

English:
theorem le_iff_forall_one_lt_lt_mul
  statement: a <= b ↔ forall ε, 1 < ε -> a < b * ε
  proof: ⟨fun h _ => lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul⟩

中文:
定理 le_iff_forall_one_lt_lt_mul
  结论: a <= b ↔ 对任意 ε, 1 < ε -> a < b * ε
  证明: ⟨fun h _ => lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul⟩

Depends on / 依赖: le_of_forall_one_lt_lt_mul, lt_mul_of_le_of_one_lt
-/
theorem le_iff_forall_one_lt_lt_mul : a <= b ↔ forall ε, 1 < ε -> a < b * ε :=
  ⟨fun h _ => lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul⟩

/- I (DT) introduced this lemma to prove (the additive version `sub_le_sub_flip` of)
`div_le_div_flip` below. Now I wonder what is the point of either of these lemmas... -/
@[to_additive]
/--
theorem `div_le_inv_mul_iff` / 定理 `div_le_inv_mul_iff`

English:
theorem div_le_inv_mul_iff
  given: [MulRightMono α]
  proof: by
  rw [div_eq_mul_inv]; rw [mul_inv_le_inv_mul_iff]
  exact
    ⟨fun h => not_lt.mp fun k => not_lt.mpr h (mul_lt_mul_of_lt_of_lt k k), fun h =>
      mul_le_mul' h h⟩

中文:
定理 div_le_inv_mul_iff
  条件: [MulRightMono α]
  证明: by
  rw [div_eq_mul_inv]; rw [mul_inv_le_inv_mul_iff]
  exact
    ⟨fun h => not_lt.mp fun k => not_lt.mpr h (mul_lt_mul_of_lt_of_lt k k), fun h =>
      mul_le_mul' h h⟩

Depends on / 依赖: div_eq_mul_inv, mul_inv_le_inv_mul_iff, mul_le_mul, mul_lt_mul_of_lt_of_lt, not_lt, not_lt.mp, not_lt.mpr
-/
theorem div_le_inv_mul_iff [MulRightMono α] :
    a / b <= a⁻¹ * b ↔ a <= b := by
  rw [div_eq_mul_inv]; rw [mul_inv_le_inv_mul_iff]
  exact
    ⟨fun h => not_lt.mp fun k => not_lt.mpr h (mul_lt_mul_of_lt_of_lt k k), fun h =>
      mul_le_mul' h h⟩

-- What is the point of this lemma? See comment about `div_le_inv_mul_iff` above.
-- Note: we intentionally don't have `@[simp]` for the additive version,
-- since the LHS simplifies with `tsub_le_iff_right`
@[to_additive]
/--
theorem `div_le_div_flip` / 定理 `div_le_div_flip`

English:
theorem div_le_div_flip
  statement: {α : Type*} [CommGroup α] [LinearOrder α]
  proof: by
  rw [div_eq_mul_inv b]; rw [mul_comm]
  exact div_le_inv_mul_iff

中文:
定理 div_le_div_flip
  结论: {α : 类型} [CommGroup α] [LinearOrder α]
  证明: by
  rw [div_eq_mul_inv b]; rw [mul_comm]
  exact div_le_inv_mul_iff

Depends on / 依赖: div_eq_mul_inv, div_le_inv_mul_iff, mul_comm
-/
theorem div_le_div_flip {α : Type*} [CommGroup α] [LinearOrder α]
    [MulLeftMono α] {a b : α} : a / b <= b / a ↔ a <= b := by
  rw [div_eq_mul_inv b]; rw [mul_comm]
  exact div_le_inv_mul_iff

end VariableNames

end LinearOrder

section

variable {β : Type*} [Group α] [Preorder α] [MulLeftMono α]
  [MulRightMono α] [Preorder β] {f : β -> α} {s : Set β}

@[to_additive]
/--
theorem `Monotone.inv` / 定理 `Monotone.inv`

English:
theorem Monotone.inv
  given: (hf : Monotone f)
  statement: Antitone fun x => (f x)⁻¹
  proof: fun _ _ hxy =>
  inv_le_inv_iff.2 (hf hxy)

@[to_additive]

中文:
定理 Monotone.inv
  条件: (hf : Monotone f)
  结论: Antitone fun x => (f x)⁻¹
  证明: fun _ _ hxy =>
  inv_le_inv_iff.2 (hf hxy)

@[to_additive]
-/
theorem Monotone.inv (hf : Monotone f) : Antitone fun x => (f x)⁻¹ := fun _ _ hxy =>
  inv_le_inv_iff.2 (hf hxy)

@[to_additive]
/--
theorem `Antitone.inv` / 定理 `Antitone.inv`

English:
theorem Antitone.inv
  given: (hf : Antitone f)
  statement: Monotone fun x => (f x)⁻¹
  proof: fun _ _ hxy =>
  inv_le_inv_iff.2 (hf hxy)

@[to_additive]

中文:
定理 Antitone.inv
  条件: (hf : Antitone f)
  结论: Monotone fun x => (f x)⁻¹
  证明: fun _ _ hxy =>
  inv_le_inv_iff.2 (hf hxy)

@[to_additive]
-/
theorem Antitone.inv (hf : Antitone f) : Monotone fun x => (f x)⁻¹ := fun _ _ hxy =>
  inv_le_inv_iff.2 (hf hxy)

@[to_additive]
/--
theorem `MonotoneOn.inv` / 定理 `MonotoneOn.inv`

English:
theorem MonotoneOn.inv
  given: (hf : MonotoneOn f s)
  statement: AntitoneOn (fun x => (f x)⁻¹) s
  proof: fun _ hx _ hy hxy => inv_le_inv_iff.2 (hf hx hy hxy)

@[to_additive]

中文:
定理 MonotoneOn.inv
  条件: (hf : MonotoneOn f s)
  结论: AntitoneOn (fun x => (f x)⁻¹) s
  证明: fun _ hx _ hy hxy => inv_le_inv_iff.2 (hf hx hy hxy)

@[to_additive]

Depends on / 依赖: inv_le_inv_iff
-/
theorem MonotoneOn.inv (hf : MonotoneOn f s) : AntitoneOn (fun x => (f x)⁻¹) s :=
  fun _ hx _ hy hxy => inv_le_inv_iff.2 (hf hx hy hxy)

@[to_additive]
/--
theorem `AntitoneOn.inv` / 定理 `AntitoneOn.inv`

English:
theorem AntitoneOn.inv
  given: (hf : AntitoneOn f s)
  statement: MonotoneOn (fun x => (f x)⁻¹) s
  proof: fun _ hx _ hy hxy => inv_le_inv_iff.2 (hf hx hy hxy)

中文:
定理 AntitoneOn.inv
  条件: (hf : AntitoneOn f s)
  结论: MonotoneOn (fun x => (f x)⁻¹) s
  证明: fun _ hx _ hy hxy => inv_le_inv_iff.2 (hf hx hy hxy)

Depends on / 依赖: inv_le_inv_iff
-/
theorem AntitoneOn.inv (hf : AntitoneOn f s) : MonotoneOn (fun x => (f x)⁻¹) s :=
  fun _ hx _ hy hxy => inv_le_inv_iff.2 (hf hx hy hxy)

end

section

variable {β : Type*} [Group α] [Preorder α] [MulLeftStrictMono α]
  [MulRightStrictMono α] [Preorder β] {f : β -> α} {s : Set β}

@[to_additive]
/--
theorem `StrictMono.inv` / 定理 `StrictMono.inv`

English:
theorem StrictMono.inv
  given: (hf : StrictMono f)
  statement: StrictAnti fun x => (f x)⁻¹
  proof: fun _ _ hxy =>
  inv_lt_inv_iff.2 (hf hxy)

@[to_additive]

中文:
定理 StrictMono.inv
  条件: (hf : StrictMono f)
  结论: StrictAnti fun x => (f x)⁻¹
  证明: fun _ _ hxy =>
  inv_lt_inv_iff.2 (hf hxy)

@[to_additive]
-/
theorem StrictMono.inv (hf : StrictMono f) : StrictAnti fun x => (f x)⁻¹ := fun _ _ hxy =>
  inv_lt_inv_iff.2 (hf hxy)

@[to_additive]
/--
theorem `StrictAnti.inv` / 定理 `StrictAnti.inv`

English:
theorem StrictAnti.inv
  given: (hf : StrictAnti f)
  statement: StrictMono fun x => (f x)⁻¹
  proof: fun _ _ hxy =>
  inv_lt_inv_iff.2 (hf hxy)

@[to_additive]

中文:
定理 StrictAnti.inv
  条件: (hf : StrictAnti f)
  结论: StrictMono fun x => (f x)⁻¹
  证明: fun _ _ hxy =>
  inv_lt_inv_iff.2 (hf hxy)

@[to_additive]
-/
theorem StrictAnti.inv (hf : StrictAnti f) : StrictMono fun x => (f x)⁻¹ := fun _ _ hxy =>
  inv_lt_inv_iff.2 (hf hxy)

@[to_additive]
/--
theorem `StrictMonoOn.inv` / 定理 `StrictMonoOn.inv`

English:
theorem StrictMonoOn.inv
  given: (hf : StrictMonoOn f s)
  statement: StrictAntiOn (fun x => (f x)⁻¹) s
  proof: fun _ hx _ hy hxy => inv_lt_inv_iff.2 (hf hx hy hxy)

@[to_additive]

中文:
定理 StrictMonoOn.inv
  条件: (hf : StrictMonoOn f s)
  结论: StrictAntiOn (fun x => (f x)⁻¹) s
  证明: fun _ hx _ hy hxy => inv_lt_inv_iff.2 (hf hx hy hxy)

@[to_additive]

Depends on / 依赖: inv_lt_inv_iff
-/
theorem StrictMonoOn.inv (hf : StrictMonoOn f s) : StrictAntiOn (fun x => (f x)⁻¹) s :=
  fun _ hx _ hy hxy => inv_lt_inv_iff.2 (hf hx hy hxy)

@[to_additive]
/--
theorem `StrictAntiOn.inv` / 定理 `StrictAntiOn.inv`

English:
theorem StrictAntiOn.inv
  given: (hf : StrictAntiOn f s)
  statement: StrictMonoOn (fun x => (f x)⁻¹) s
  proof: fun _ hx _ hy hxy => inv_lt_inv_iff.2 (hf hx hy hxy)

中文:
定理 StrictAntiOn.inv
  条件: (hf : StrictAntiOn f s)
  结论: StrictMonoOn (fun x => (f x)⁻¹) s
  证明: fun _ hx _ hy hxy => inv_lt_inv_iff.2 (hf hx hy hxy)

Depends on / 依赖: inv_lt_inv_iff
-/
theorem StrictAntiOn.inv (hf : StrictAntiOn f s) : StrictMonoOn (fun x => (f x)⁻¹) s :=
  fun _ hx _ hy hxy => inv_lt_inv_iff.2 (hf hx hy hxy)

end
