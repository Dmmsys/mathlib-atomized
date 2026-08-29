/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Order.Monoid.Defs

/-!
# Order instances for `MulOpposite`/`AddOpposite`

This file transfers order instances and ordered monoid/group instances from `α` to `αᵐᵒᵖ` and
`αᵃᵒᵖ`.
-/

public section

variable {α : Type*}

namespace MulOpposite
section Preorder
variable [Preorder α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder αᵐᵒᵖ
  body: Preorder.lift unop

中文:
实例 :
  签名: Preorder αᵐᵒᵖ
  定义体: Preorder.lift unop
-/
@[to_additive] instance : Preorder αᵐᵒᵖ := Preorder.lift unop

/--
lemma `unop_le_unop` / 引理 `unop_le_unop`

English:
lemma unop_le_unop
  given: {a b : αᵐᵒᵖ}
  statement: a.unop <= b.unop ↔ a <= b
  proof: .rfl

中文:
引理 unop_le_unop
  条件: {a b : αᵐᵒᵖ}
  结论: a.unop <= b.unop ↔ a <= b
  证明: .rfl
-/
@[to_additive (attr := simp)] lemma unop_le_unop {a b : αᵐᵒᵖ} : a.unop <= b.unop ↔ a <= b := .rfl
/--
lemma `op_le_op` / 引理 `op_le_op`

English:
lemma op_le_op
  given: {a b : α}
  statement: op a <= op b ↔ a <= b
  proof: .rfl

中文:
引理 op_le_op
  条件: {a b : α}
  结论: op a <= op b ↔ a <= b
  证明: .rfl
-/
@[to_additive (attr := simp)] lemma op_le_op {a b : α} : op a <= op b ↔ a <= b := .rfl

end Preorder

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: α] : PartialOrder αᵐᵒᵖ
  body: PartialOrder.lift _ unop_injective

中文:
实例 [PartialOrder
  签名: α] : PartialOrder αᵐᵒᵖ
  定义体: PartialOrder.lift _ unop_injective
-/
@[to_additive] instance [PartialOrder α] : PartialOrder αᵐᵒᵖ := PartialOrder.lift _ unop_injective

section OrderedCommMonoid
variable [CommMonoid α] [PartialOrder α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsOrderedMonoid
  signature: α] : IsOrderedMonoid αᵐᵒᵖ where
  body: mul_le_mul_right (by simpa) c.unop

中文:
实例 [IsOrderedMonoid
  签名: α] : IsOrderedMonoid αᵐᵒᵖ where
  定义体: mul_le_mul_right (by simpa) c.unop
-/
@[to_additive] instance [IsOrderedMonoid α] : IsOrderedMonoid αᵐᵒᵖ where
  mul_le_mul_left a b hab c := mul_le_mul_right (by simpa) c.unop

/--
lemma `unop_le_one` / 引理 `unop_le_one`

English:
lemma unop_le_one
  given: {a : αᵐᵒᵖ}
  statement: unop a <= 1 ↔ a <= 1
  proof: .rfl

中文:
引理 unop_le_one
  条件: {a : αᵐᵒᵖ}
  结论: unop a <= 1 ↔ a <= 1
  证明: .rfl
-/
@[to_additive (attr := simp)] lemma unop_le_one {a : αᵐᵒᵖ} : unop a <= 1 ↔ a <= 1 := .rfl
/--
lemma `one_le_unop` / 引理 `one_le_unop`

English:
lemma one_le_unop
  given: {a : αᵐᵒᵖ}
  statement: 1 <= unop a ↔ 1 <= a
  proof: .rfl

中文:
引理 one_le_unop
  条件: {a : αᵐᵒᵖ}
  结论: 1 <= unop a ↔ 1 <= a
  证明: .rfl
-/
@[to_additive (attr := simp)] lemma one_le_unop {a : αᵐᵒᵖ} : 1 <= unop a ↔ 1 <= a := .rfl
/--
lemma `op_le_one` / 引理 `op_le_one`

English:
lemma op_le_one
  given: {a : α}
  statement: op a <= 1 ↔ a <= 1
  proof: .rfl

中文:
引理 op_le_one
  条件: {a : α}
  结论: op a <= 1 ↔ a <= 1
  证明: .rfl
-/
@[to_additive (attr := simp)] lemma op_le_one {a : α} : op a <= 1 ↔ a <= 1 := .rfl
/--
lemma `one_le_op` / 引理 `one_le_op`

English:
lemma one_le_op
  given: {a : α}
  statement: 1 <= op a ↔ 1 <= a
  proof: .rfl

中文:
引理 one_le_op
  条件: {a : α}
  结论: 1 <= op a ↔ 1 <= a
  证明: .rfl
-/
@[to_additive (attr := simp)] lemma one_le_op {a : α} : 1 <= op a ↔ 1 <= a := .rfl

end OrderedCommMonoid

section OrderedAddCommMonoid
variable [AddCommMonoid α] [PartialOrder α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsOrderedAddMonoid
  signature: α] : IsOrderedAddMonoid αᵐᵒᵖ where
  body: add_le_add_left (by simpa) c.unop

中文:
实例 [IsOrderedAddMonoid
  签名: α] : IsOrderedAddMonoid αᵐᵒᵖ where
  定义体: add_le_add_left (by simpa) c.unop

Depends on / 依赖: add_le_add_left, c.unop
-/
instance [IsOrderedAddMonoid α] : IsOrderedAddMonoid αᵐᵒᵖ where
  add_le_add_left a b hab c := add_le_add_left (by simpa) c.unop

/--
lemma `unop_nonpos` / 引理 `unop_nonpos`

English:
lemma unop_nonpos
  given: {a : αᵐᵒᵖ}
  statement: unop a <= 0 ↔ a <= 0
  proof: .rfl

中文:
引理 unop_nonpos
  条件: {a : αᵐᵒᵖ}
  结论: unop a <= 0 ↔ a <= 0
  证明: .rfl
-/
@[simp] lemma unop_nonpos {a : αᵐᵒᵖ} : unop a <= 0 ↔ a <= 0 := .rfl
/--
lemma `unop_nonneg` / 引理 `unop_nonneg`

English:
lemma unop_nonneg
  given: {a : αᵐᵒᵖ}
  statement: 0 <= unop a ↔ 0 <= a
  proof: .rfl

中文:
引理 unop_nonneg
  条件: {a : αᵐᵒᵖ}
  结论: 0 <= unop a ↔ 0 <= a
  证明: .rfl
-/
@[simp] lemma unop_nonneg {a : αᵐᵒᵖ} : 0 <= unop a ↔ 0 <= a := .rfl
/--
lemma `op_nonpos` / 引理 `op_nonpos`

English:
lemma op_nonpos
  given: {a : α}
  statement: op a <= 0 ↔ a <= 0
  proof: .rfl

中文:
引理 op_nonpos
  条件: {a : α}
  结论: op a <= 0 ↔ a <= 0
  证明: .rfl
-/
@[simp] lemma op_nonpos {a : α} : op a <= 0 ↔ a <= 0 := .rfl
/--
lemma `op_nonneg` / 引理 `op_nonneg`

English:
lemma op_nonneg
  given: {a : α}
  statement: 0 <= op a ↔ 0 <= a
  proof: .rfl

中文:
引理 op_nonneg
  条件: {a : α}
  结论: 0 <= op a ↔ 0 <= a
  证明: .rfl
-/
@[simp] lemma op_nonneg {a : α} : 0 <= op a ↔ 0 <= a := .rfl

end OrderedAddCommMonoid

end MulOpposite

namespace AddOpposite
section OrderedCommMonoid
variable [CommMonoid α] [PartialOrder α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsOrderedMonoid
  signature: α] : IsOrderedMonoid αᵃᵒᵖ where
  body: mul_le_mul_left (by simpa) c.unop

中文:
实例 [IsOrderedMonoid
  签名: α] : IsOrderedMonoid αᵃᵒᵖ where
  定义体: mul_le_mul_left (by simpa) c.unop

Depends on / 依赖: c.unop, mul_le_mul_left
-/
instance [IsOrderedMonoid α] : IsOrderedMonoid αᵃᵒᵖ where
  mul_le_mul_left a b hab c := mul_le_mul_left (by simpa) c.unop

/--
lemma `unop_le_one` / 引理 `unop_le_one`

English:
lemma unop_le_one
  given: {a : αᵃᵒᵖ}
  statement: unop a <= 1 ↔ a <= 1
  proof: .rfl

中文:
引理 unop_le_one
  条件: {a : αᵃᵒᵖ}
  结论: unop a <= 1 ↔ a <= 1
  证明: .rfl
-/
@[simp] lemma unop_le_one {a : αᵃᵒᵖ} : unop a <= 1 ↔ a <= 1 := .rfl
/--
lemma `one_le_unop` / 引理 `one_le_unop`

English:
lemma one_le_unop
  given: {a : αᵃᵒᵖ}
  statement: 1 <= unop a ↔ 1 <= a
  proof: .rfl

中文:
引理 one_le_unop
  条件: {a : αᵃᵒᵖ}
  结论: 1 <= unop a ↔ 1 <= a
  证明: .rfl
-/
@[simp] lemma one_le_unop {a : αᵃᵒᵖ} : 1 <= unop a ↔ 1 <= a := .rfl
/--
lemma `op_le_one` / 引理 `op_le_one`

English:
lemma op_le_one
  given: {a : α}
  statement: op a <= 1 ↔ a <= 1
  proof: .rfl

中文:
引理 op_le_one
  条件: {a : α}
  结论: op a <= 1 ↔ a <= 1
  证明: .rfl
-/
@[simp] lemma op_le_one {a : α} : op a <= 1 ↔ a <= 1 := .rfl
/--
lemma `one_le_op` / 引理 `one_le_op`

English:
lemma one_le_op
  given: {a : α}
  statement: 1 <= op a ↔ 1 <= a
  proof: .rfl

中文:
引理 one_le_op
  条件: {a : α}
  结论: 1 <= op a ↔ 1 <= a
  证明: .rfl
-/
@[simp] lemma one_le_op {a : α} : 1 <= op a ↔ 1 <= a := .rfl

end OrderedCommMonoid

end AddOpposite
