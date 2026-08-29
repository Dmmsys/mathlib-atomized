/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-! # Adjoining top/bottom elements to ordered monoids.
-/

public section

universe u

variable {α : Type u}

open Function

namespace WithTop

/--
Instance `isOrderedAddMonoid` / 实例 `isOrderedAddMonoid`

English:
instance isOrderedAddMonoid
  signature: [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
  body: add_le_add_left

中文:
实例 isOrderedAddMonoid
  签名: [加法交换幺半群 α] [偏序 α] [是OrderedAdd幺半群 α]
  定义体: add_le_add_left

Depends on / 依赖: add_le_add_left
-/
instance isOrderedAddMonoid [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] :
    IsOrderedAddMonoid (WithTop α) where
  add_le_add_left _ _ := add_le_add_left

/--
Instance `canonicallyOrderedAdd` / 实例 `canonicallyOrderedAdd`

English:
instance canonicallyOrderedAdd
  signature: [Add α] [Preorder α] [CanonicallyOrderedAdd α]

中文:
实例 canonicallyOrderedAdd
  签名: [加法 α] [预序 α] [典范有序加法 α]

Depends on / 依赖: mul_smul, smul_eq_mul
-/
instance canonicallyOrderedAdd [Add α] [Preorder α] [CanonicallyOrderedAdd α] :
    CanonicallyOrderedAdd (WithTop α) where
  le_self_add
  | ⊤, _ => le_rfl
  | (a : α), ⊤ => le_top
  | (a : α), (b : α) => WithTop.coe_le_coe.2 le_self_add
  le_add_self
  | ⊤, ⊤ | ⊤, (b : α) => le_rfl
  | (a : α), ⊤ => le_top
  | (a : α), (b : α) => WithTop.coe_le_coe.2 le_add_self

end WithTop

namespace WithBot

/--
Instance `isOrderedAddMonoid` / 实例 `isOrderedAddMonoid`

English:
instance isOrderedAddMonoid
  signature: [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
  body: { add_le_add_left := fun _ _ h c => add_le_add_left h c }

中文:
实例 isOrderedAddMonoid
  签名: [加法交换幺半群 α] [偏序 α] [是OrderedAdd幺半群 α]
  定义体: { add_le_add_left := fun _ _ h c => add_le_add_left h c }

Depends on / 依赖: add_le_add_left
-/
instance isOrderedAddMonoid [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] :
    IsOrderedAddMonoid (WithBot α) :=
  { add_le_add_left := fun _ _ h c => add_le_add_left h c }

/--
theorem `le_self_add` / 定理 `le_self_add`

English:
theorem le_self_add
  statement: [Add α] [LE α] [CanonicallyOrderedAdd α]
  proof: by
  induction x
  · simp at hx
  induction y
  · simp
  · rw [← WithBot.coe_add, WithBot.coe_le_coe]
    exact le_self_add

中文:
定理 le_self_add
  结论: [加法 α] [LE α] [典范有序加法 α]
  证明: by
  induction x
  · simp at hx
  induction y
  · simp
  · rw [← WithBot.coe_add, WithBot.coe_le_coe]
    exact le_self_add
-/
protected theorem le_self_add [Add α] [LE α] [CanonicallyOrderedAdd α]
    {x : WithBot α} (hx : x != ⊥) (y : WithBot α) :
    y <= y + x := by
  induction x
  · simp at hx
  induction y
  · simp
  · rw [← WithBot.coe_add, WithBot.coe_le_coe]
    exact le_self_add

/--
theorem `le_add_self` / 定理 `le_add_self`

English:
theorem le_add_self
  statement: [AddCommMagma α] [LE α] [CanonicallyOrderedAdd α]
  proof: by
  induction x
  · simp at hx
  induction y
  · simp
  · rw [← WithBot.coe_add, WithBot.coe_le_coe]
    exact le_add_self

中文:
定理 le_add_self
  结论: [加法交换原群 α] [LE α] [典范有序加法 α]
  证明: by
  induction x
  · simp at hx
  induction y
  · simp
  · rw [← WithBot.coe_add, WithBot.coe_le_coe]
    exact le_add_self
-/
protected theorem le_add_self [AddCommMagma α] [LE α] [CanonicallyOrderedAdd α]
    {x : WithBot α} (hx : x != ⊥) (y : WithBot α) :
    y <= x + y := by
  induction x
  · simp at hx
  induction y
  · simp
  · rw [← WithBot.coe_add, WithBot.coe_le_coe]
    exact le_add_self

/--
lemma `lt_zero_iff_eq_bot` / 引理 `lt_zero_iff_eq_bot`

English:
lemma lt_zero_iff_eq_bot
  statement: {α : Type*} [AddMonoid α] [Preorder α] [CanonicallyOrderedAdd α]
  proof: by
  induction a <;> simp

中文:
引理 lt_zero_iff_eq_bot
  结论: {α : 类型} [加法幺半群 α] [预序 α] [典范有序加法 α]
  证明: by
  induction a <;> simp
-/
lemma lt_zero_iff_eq_bot {α : Type*} [AddMonoid α] [Preorder α] [CanonicallyOrderedAdd α]
    (a : WithBot α) : a < 0 ↔ a = ⊥ := by
  induction a <;> simp

end WithBot
