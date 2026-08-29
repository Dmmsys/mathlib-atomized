/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public meta import Batteries.Tactic.Lint.Basic
public meta import Mathlib.Data.Ineq
public import Mathlib.Data.Ineq
public import Mathlib.Data.Nat.Cast.Order.Ring
public meta import Mathlib.Tactic.ToAdditive

/-!
# Lemmas for `linarith`.

Those in the `Linarith` namespace should stay here.

Those outside the `Linarith` namespace may be deleted as they are ported to mathlib4.
-/

public meta section

namespace Mathlib.Tactic.Linarith

universe u
/--
theorem `lt_irrefl` / 定理 `lt_irrefl`

English:
theorem lt_irrefl
  given: {α : Type u} [Preorder α] {a : α}
  statement: ¬a < a
  proof: _root_.lt_irrefl a

中文:
定理 lt_irrefl
  条件: {α : 类型u} [预序 α] {a : α}
  结论: ¬a < a
  证明: _root_.lt_irrefl a

Depends on / 依赖: _root_, _root_.lt_irrefl, lt_irrefl
-/
theorem lt_irrefl {α : Type u} [Preorder α] {a : α} : ¬a < a := _root_.lt_irrefl a

/--
theorem `eq_of_eq_of_eq` / 定理 `eq_of_eq_of_eq`

English:
theorem eq_of_eq_of_eq
  given: {α} [Semiring α] {a b : α} (ha : a = 0) (hb : b = 0)
  statement: a + b = 0
  proof: by
  simp [*]

中文:
定理 eq_of_eq_of_eq
  条件: {α} [半环 α] {a b : α} (ha : a = 0) (hb : b = 0)
  结论: a + b = 0
  证明: by
  simp [*]
-/
theorem eq_of_eq_of_eq {α} [Semiring α] {a b : α} (ha : a = 0) (hb : b = 0) : a + b = 0 := by
  simp [*]

section Semiring
variable {α : Type u} [Semiring α] [PartialOrder α]

/--
theorem `zero_lt_one` / 定理 `zero_lt_one`

English:
theorem zero_lt_one
  given: [IsStrictOrderedRing α]
  statement: (0:α) < 1
  proof: _root_.zero_lt_one

中文:
定理 zero_lt_one
  条件: [是StrictOrdered环 α]
  结论: (0:α) < 1
  证明: _root_.zero_lt_one

Depends on / 依赖: _root_, _root_.zero_lt_one, zero_lt_one
-/
theorem zero_lt_one [IsStrictOrderedRing α] : (0:α) < 1 :=
  _root_.zero_lt_one

/--
theorem `le_of_eq_of_le` / 定理 `le_of_eq_of_le`

English:
theorem le_of_eq_of_le
  given: {a b : α} (ha : a = 0) (hb : b <= 0)
  statement: a + b <= 0
  proof: by
  simp [*]

中文:
定理 le_of_eq_of_le
  条件: {a b : α} (ha : a = 0) (hb : b <= 0)
  结论: a + b <= 0
  证明: by
  simp [*]
-/
theorem le_of_eq_of_le {a b : α} (ha : a = 0) (hb : b <= 0) : a + b <= 0 := by
  simp [*]

/--
theorem `lt_of_eq_of_lt` / 定理 `lt_of_eq_of_lt`

English:
theorem lt_of_eq_of_lt
  given: {a b : α} (ha : a = 0) (hb : b < 0)
  statement: a + b < 0
  proof: by
  simp [*]

中文:
定理 lt_of_eq_of_lt
  条件: {a b : α} (ha : a = 0) (hb : b < 0)
  结论: a + b < 0
  证明: by
  simp [*]
-/
theorem lt_of_eq_of_lt {a b : α} (ha : a = 0) (hb : b < 0) : a + b < 0 := by
  simp [*]

/--
theorem `le_of_le_of_eq` / 定理 `le_of_le_of_eq`

English:
theorem le_of_le_of_eq
  given: {a b : α} (ha : a <= 0) (hb : b = 0)
  statement: a + b <= 0
  proof: by
  simp [*]

中文:
定理 le_of_le_of_eq
  条件: {a b : α} (ha : a <= 0) (hb : b = 0)
  结论: a + b <= 0
  证明: by
  simp [*]
-/
theorem le_of_le_of_eq {a b : α} (ha : a <= 0) (hb : b = 0) : a + b <= 0 := by
  simp [*]

/--
theorem `lt_of_lt_of_eq` / 定理 `lt_of_lt_of_eq`

English:
theorem lt_of_lt_of_eq
  given: {a b : α} (ha : a < 0) (hb : b = 0)
  statement: a + b < 0
  proof: by
  simp [*]

中文:
定理 lt_of_lt_of_eq
  条件: {a b : α} (ha : a < 0) (hb : b = 0)
  结论: a + b < 0
  证明: by
  simp [*]
-/
theorem lt_of_lt_of_eq {a b : α} (ha : a < 0) (hb : b = 0) : a + b < 0 := by
  simp [*]

/--
theorem `add_nonpos` / 定理 `add_nonpos`

English:
theorem add_nonpos
  given: [IsOrderedRing α] {a b : α} (ha : a <= 0) (hb : b <= 0)
  proof: _root_.add_nonpos ha hb

中文:
定理 add_nonpos
  条件: [是Ordered环 α] {a b : α} (ha : a <= 0) (hb : b <= 0)
  证明: _root_.add_nonpos ha hb

Depends on / 依赖: _root_, _root_.add_nonpos, add_nonpos
-/
theorem add_nonpos [IsOrderedRing α] {a b : α} (ha : a <= 0) (hb : b <= 0) :
    a + b <= 0 :=
  _root_.add_nonpos ha hb

/--
theorem `add_lt_of_le_of_neg` / 定理 `add_lt_of_le_of_neg`

English:
theorem add_lt_of_le_of_neg
  statement: [IsStrictOrderedRing α] {a b c : α} (hbc : b <= c)
  proof: _root_.add_lt_of_le_of_neg hbc ha

中文:
定理 add_lt_of_le_of_neg
  结论: [是StrictOrdered环 α] {a b c : α} (hbc : b <= c)
  证明: _root_.add_lt_of_le_of_neg hbc ha

Depends on / 依赖: _root_, _root_.add_lt_of_le_of_neg, add_lt_of_le_of_neg
-/
theorem add_lt_of_le_of_neg [IsStrictOrderedRing α] {a b c : α} (hbc : b <= c)
    (ha : a < 0) : b + a < c :=
  _root_.add_lt_of_le_of_neg hbc ha

/--
theorem `add_lt_of_neg_of_le` / 定理 `add_lt_of_neg_of_le`

English:
theorem add_lt_of_neg_of_le
  statement: [IsStrictOrderedRing α] {a b c : α} (ha : a < 0)
  proof: _root_.add_lt_of_neg_of_le ha hbc

中文:
定理 add_lt_of_neg_of_le
  结论: [是StrictOrdered环 α] {a b c : α} (ha : a < 0)
  证明: _root_.add_lt_of_neg_of_le ha hbc

Depends on / 依赖: _root_, _root_.add_lt_of_neg_of_le, add_lt_of_neg_of_le
-/
theorem add_lt_of_neg_of_le [IsStrictOrderedRing α] {a b c : α} (ha : a < 0)
    (hbc : b <= c) : a + b < c :=
  _root_.add_lt_of_neg_of_le ha hbc

/--
theorem `add_neg` / 定理 `add_neg`

English:
theorem add_neg
  statement: [IsStrictOrderedRing α] {a b : α} (ha : a < 0)
  proof: _root_.add_neg ha hb

中文:
定理 add_neg
  结论: [是StrictOrdered环 α] {a b : α} (ha : a < 0)
  证明: _root_.add_neg ha hb

Depends on / 依赖: _root_, _root_.add_neg, add_neg
-/
theorem add_neg [IsStrictOrderedRing α] {a b : α} (ha : a < 0)
    (hb : b < 0) : a + b < 0 :=
  _root_.add_neg ha hb

variable (α) in
/--
lemma `natCast_nonneg` / 引理 `natCast_nonneg`

English:
lemma natCast_nonneg
  given: [IsOrderedRing α] (n : Nat)
  statement: (0 : α) <= n
  proof: Nat.cast_nonneg n

中文:
引理 natCast_nonneg
  条件: [是Ordered环 α] (n : 自然数)
  结论: (0 : α) <= n
  证明: Nat.cast_nonneg n

Depends on / 依赖: Nat.cast_nonneg, cast_nonneg
-/
lemma natCast_nonneg [IsOrderedRing α] (n : Nat) : (0 : α) <= n := Nat.cast_nonneg n

-- used alongside `mul_neg` and `mul_nonpos`, so has the same argument pattern for uniformity
@[nolint unusedArguments]
/--
theorem `mul_eq` / 定理 `mul_eq`

English:
theorem mul_eq
  given: [IsOrderedRing α] {a b : α} (ha : a = 0) (_ : 0 < b)
  statement: b * a = 0
  proof: by
  simp [*]

中文:
定理 mul_eq
  条件: [是Ordered环 α] {a b : α} (ha : a = 0) (_ : 0 < b)
  结论: b * a = 0
  证明: by
  simp [*]
-/
theorem mul_eq [IsOrderedRing α] {a b : α} (ha : a = 0) (_ : 0 < b) : b * a = 0 := by
  simp [*]

end Semiring

section Ring
variable {α : Type u} [Ring α] [PartialOrder α]

/--
theorem `mul_neg` / 定理 `mul_neg`

English:
theorem mul_neg
  given: [IsStrictOrderedRing α] {a b : α} (ha : a < 0) (hb : 0 < b)
  statement: b * a < 0
  proof: have : (-b)*a > 0 := mul_pos_of_neg_of_neg (neg_neg_of_pos hb) ha
  neg_of_neg_pos (by simpa)

中文:
定理 mul_neg
  条件: [是StrictOrdered环 α] {a b : α} (ha : a < 0) (hb : 0 < b)
  结论: b * a < 0
  证明: have : (-b)*a > 0 := mul_pos_of_neg_of_neg (neg_neg_of_pos hb) ha
  neg_of_neg_pos (by simpa)

Depends on / 依赖: mul_pos_of_neg_of_neg, neg_neg_of_pos, neg_of_neg_pos
-/
theorem mul_neg [IsStrictOrderedRing α] {a b : α} (ha : a < 0) (hb : 0 < b) : b * a < 0 :=
  have : (-b)*a > 0 := mul_pos_of_neg_of_neg (neg_neg_of_pos hb) ha
  neg_of_neg_pos (by simpa)

/--
theorem `mul_nonpos` / 定理 `mul_nonpos`

English:
theorem mul_nonpos
  given: [IsOrderedRing α] {a b : α} (ha : a <= 0) (hb : 0 < b)
  statement: b * a <= 0
  proof: have : (-b)*a >= 0 := mul_nonneg_of_nonpos_of_nonpos (le_of_lt (neg_neg_of_pos hb)) ha
  by simpa

中文:
定理 mul_nonpos
  条件: [是Ordered环 α] {a b : α} (ha : a <= 0) (hb : 0 < b)
  结论: b * a <= 0
  证明: have : (-b)*a >= 0 := mul_nonneg_of_nonpos_of_nonpos (le_of_lt (neg_neg_of_pos hb)) ha
  by simpa

Depends on / 依赖: le_of_lt, mul_nonneg_of_nonpos_of_nonpos, neg_neg_of_pos
-/
theorem mul_nonpos [IsOrderedRing α] {a b : α} (ha : a <= 0) (hb : 0 < b) : b * a <= 0 :=
  have : (-b)*a >= 0 := mul_nonneg_of_nonpos_of_nonpos (le_of_lt (neg_neg_of_pos hb)) ha
  by simpa

/--
theorem `sub_nonpos_of_le` / 定理 `sub_nonpos_of_le`

English:
theorem sub_nonpos_of_le
  given: [IsOrderedRing α] {a b : α}
  statement: a <= b -> a - b <= 0
  proof: _root_.sub_nonpos_of_le

中文:
定理 sub_nonpos_of_le
  条件: [是Ordered环 α] {a b : α}
  结论: a <= b -> a - b <= 0
  证明: _root_.sub_nonpos_of_le

Depends on / 依赖: _root_, _root_.sub_nonpos_of_le, sub_nonpos_of_le
-/
theorem sub_nonpos_of_le [IsOrderedRing α] {a b : α} : a <= b -> a - b <= 0 :=
  _root_.sub_nonpos_of_le

/--
theorem `sub_neg_of_lt` / 定理 `sub_neg_of_lt`

English:
theorem sub_neg_of_lt
  given: [IsOrderedRing α] {a b : α}
  statement: a < b -> a - b < 0
  proof: _root_.sub_neg_of_lt

中文:
定理 sub_neg_of_lt
  条件: [是Ordered环 α] {a b : α}
  结论: a < b -> a - b < 0
  证明: _root_.sub_neg_of_lt

Depends on / 依赖: _root_, _root_.sub_neg_of_lt, sub_neg_of_lt
-/
theorem sub_neg_of_lt [IsOrderedRing α] {a b : α} : a < b -> a - b < 0 :=
  _root_.sub_neg_of_lt

end Ring

/--
Definition of `_root_.Mathlib.Ineq.toConstMulName` / `_root_.Mathlib.Ineq.toConstMulName` 的定义

English:
definition _root_.Mathlib.Ineq.toConstMulName
  signature: : Ineq -> Lean.Name

中文:
定义 _root_.Mathlib.Ineq.toConstMulName
  签名: : Ineq -> Lean.Name
-/
def _root_.Mathlib.Ineq.toConstMulName : Ineq -> Lean.Name
  | .lt => ``mul_neg
  | .le => ``mul_nonpos
  | .eq => ``mul_eq

/--
lemma `eq_of_not_lt_of_not_gt` / 引理 `eq_of_not_lt_of_not_gt`

English:
lemma eq_of_not_lt_of_not_gt
  given: {α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a)
  statement: a = b
  proof: le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)

中文:
引理 eq_of_not_lt_of_not_gt
  条件: {α} [线性序 α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a)
  结论: a = b
  证明: le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)

Depends on / 依赖: le_antisymm, le_of_not_gt
-/
lemma eq_of_not_lt_of_not_gt {α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b :=
  le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.
@[nolint unusedArguments]
/--
lemma `mul_zero_eq` / 引理 `mul_zero_eq`

English:
lemma mul_zero_eq
  given: {α} {R : α -> α -> Prop} [Semiring α] {a b : α} (_ : R a 0) (h : b = 0)
  proof: by
  simp [h]

中文:
引理 mul_zero_eq
  条件: {α} {R : α -> α -> 命题} [半环 α] {a b : α} (_ : R a 0) (h : b = 0)
  证明: by
  simp [h]
-/
lemma mul_zero_eq {α} {R : α -> α -> Prop} [Semiring α] {a b : α} (_ : R a 0) (h : b = 0) :
    a * b = 0 := by
  simp [h]

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.
@[nolint unusedArguments]
/--
lemma `zero_mul_eq` / 引理 `zero_mul_eq`

English:
lemma zero_mul_eq
  given: {α} {R : α -> α -> Prop} [Semiring α] {a b : α} (h : a = 0) (_ : R b 0)
  proof: by
  simp [h]

中文:
引理 zero_mul_eq
  条件: {α} {R : α -> α -> 命题} [半环 α] {a b : α} (h : a = 0) (_ : R b 0)
  证明: by
  simp [h]
-/
lemma zero_mul_eq {α} {R : α -> α -> Prop} [Semiring α] {a b : α} (h : a = 0) (_ : R b 0) :
    a * b = 0 := by
  simp [h]

end Mathlib.Tactic.Linarith
