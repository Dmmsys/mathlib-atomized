/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Algebra.Group.Units.Defs

/-!
# Units in ordered monoids
-/

@[expose] public section

namespace Units

variable {α : Type*}

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] [Preorder α] : Preorder αˣ
  body: Preorder.lift val

@[to_additive (attr := simp, norm_cast)]

中文:
实例 [Monoid
  签名: α] [Preorder α] : Preorder αˣ
  定义体: Preorder.lift val

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Preorder, Preorder.lift
-/
instance [Monoid α] [Preorder α] : Preorder αˣ :=
  Preorder.lift val

@[to_additive (attr := simp, norm_cast)]
/--
theorem `val_le_val` / 定理 `val_le_val`

English:
theorem val_le_val
  given: [Monoid α] [Preorder α] {a b : αˣ}
  statement: (a : α) <= b ↔ a <= b
  proof: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 val_le_val
  条件: [Monoid α] [Preorder α] {a b : αˣ}
  结论: (a : α) <= b ↔ a <= b
  证明: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Iff.rfl
-/
theorem val_le_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α) <= b ↔ a <= b :=
  Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `val_lt_val` / 定理 `val_lt_val`

English:
theorem val_lt_val
  given: [Monoid α] [Preorder α] {a b : αˣ}
  statement: (a : α) < b ↔ a < b
  proof: Iff.rfl

@[to_additive]

中文:
定理 val_lt_val
  条件: [Monoid α] [Preorder α] {a b : αˣ}
  结论: (a : α) < b ↔ a < b
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem val_lt_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α) < b ↔ a < b :=
  Iff.rfl

@[to_additive]
/--
Instance `instPartialOrderUnits` / 实例 `instPartialOrderUnits`

English:
instance instPartialOrderUnits
  signature: [Monoid α] [PartialOrder α]
  body: PartialOrder.lift val val_injective

@[to_additive]

中文:
实例 instPartialOrderUnits
  签名: [Monoid α] [PartialOrder α]
  定义体: PartialOrder.lift val val_injective

@[to_additive]

Depends on / 依赖: PartialOrder, PartialOrder.lift, val_injective
-/
instance instPartialOrderUnits [Monoid α] [PartialOrder α] : PartialOrder αˣ :=
  PartialOrder.lift val val_injective

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] [LinearOrder α] : Max αˣ where
  body: if a <= b then b else a

@[to_additive]

中文:
实例 [Monoid
  签名: α] [LinearOrder α] : Max αˣ where
  定义体: if a <= b then b else a

@[to_additive]
-/
instance [Monoid α] [LinearOrder α] : Max αˣ where
  max a b := if a <= b then b else a

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] [LinearOrder α] : Min αˣ where
  body: if a <= b then a else b


@[to_additive (attr := simp, norm_cast)]

中文:
实例 [Monoid
  签名: α] [LinearOrder α] : Min αˣ where
  定义体: if a <= b then a else b


@[to_additive (attr := simp, norm_cast)]
-/
instance [Monoid α] [LinearOrder α] : Min αˣ where
  min a b := if a <= b then a else b


@[to_additive (attr := simp, norm_cast)]
/--
theorem `max_val` / 定理 `max_val`

English:
theorem max_val
  given: [Monoid α] [LinearOrder α] (a b : αˣ)
  statement: (max a b).val = max a.val b.val
  proof: by
  simp_rw [max_def, val_le_val, ← apply_ite]
  rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 max_val
  条件: [Monoid α] [LinearOrder α] (a b : αˣ)
  结论: (max a b).val = max a.val b.val
  证明: by
  simp_rw [max_def, val_le_val, ← apply_ite]
  rfl

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: apply_ite, max_def, simp_rw, val_le_val
-/
theorem max_val [Monoid α] [LinearOrder α] (a b : αˣ) : (max a b).val = max a.val b.val := by
  simp_rw [max_def, val_le_val, ← apply_ite]
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `min_val` / 定理 `min_val`

English:
theorem min_val
  given: [Monoid α] [LinearOrder α] (a b : αˣ)
  statement: (min a b).val = min a.val b.val
  proof: by
  simp_rw [min_def, val_le_val, ← apply_ite]
  rfl

@[to_additive]

中文:
定理 min_val
  条件: [Monoid α] [LinearOrder α] (a b : αˣ)
  结论: (min a b).val = min a.val b.val
  证明: by
  simp_rw [min_def, val_le_val, ← apply_ite]
  rfl

@[to_additive]

Depends on / 依赖: apply_ite, min_def, simp_rw, val_le_val
-/
theorem min_val [Monoid α] [LinearOrder α] (a b : αˣ) : (min a b).val = min a.val b.val := by
  simp_rw [min_def, val_le_val, ← apply_ite]
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] [Ord α] : Ord αˣ where
  body: compare a.val b.val

@[to_additive]

中文:
实例 [Monoid
  签名: α] [Ord α] : Ord αˣ where
  定义体: compare a.val b.val

@[to_additive]

Depends on / 依赖: a.val, b.val, compare
-/
instance [Monoid α] [Ord α] : Ord αˣ where
  compare a b := compare a.val b.val

@[to_additive]
/--
theorem `compare_val` / 定理 `compare_val`

English:
theorem compare_val
  given: [Monoid α] [Ord α] (a b : αˣ)
  statement: compare a.val b.val = compare a b
  proof: rfl

@[to_additive]

中文:
定理 compare_val
  条件: [Monoid α] [Ord α] (a b : αˣ)
  结论: compare a.val b.val = compare a b
  证明: rfl

@[to_additive]
-/
theorem compare_val [Monoid α] [Ord α] (a b : αˣ) : compare a.val b.val = compare a b := rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] [LinearOrder α] : LinearOrder αˣ
  body: val_injective.linearOrder _ val_le_val val_lt_val min_val max_val compare_val

中文:
实例 [Monoid
  签名: α] [LinearOrder α] : LinearOrder αˣ
  定义体: val_injective.linearOrder _ val_le_val val_lt_val min_val max_val compare_val

Depends on / 依赖: compare_val, linearOrder, max_val, min_val, val_injective, val_injective.linearOrder, val_le_val, val_lt_val
-/
instance [Monoid α] [LinearOrder α] : LinearOrder αˣ :=
  val_injective.linearOrder _ val_le_val val_lt_val min_val max_val compare_val

/-- `val : αˣ → α` as an order embedding. -/
@[to_additive (attr := simps -fullyApplied)
  /-- `val : add_units α → α` as an order embedding. -/]
/--
Definition of `orderEmbeddingVal` / `orderEmbeddingVal` 的定义

English:
definition orderEmbeddingVal
  signature: [Monoid α] [LinearOrder α]
  body: ⟨⟨val, val_injective⟩, .rfl⟩

中文:
定义 orderEmbeddingVal
  签名: [Monoid α] [LinearOrder α]
  定义体: ⟨⟨val, val_injective⟩, .rfl⟩

Depends on / 依赖: val_injective
-/
def orderEmbeddingVal [Monoid α] [LinearOrder α] : αˣ ↪o α :=
  ⟨⟨val, val_injective⟩, .rfl⟩

end Units
