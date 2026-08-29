/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Yuyang Zhao
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Ordered monoids

This file provides the definitions of ordered monoids.

-/

public section


open Function

variable {α : Type*}

-- TODO: assume weaker typeclasses

/--
Definition of `IsOrderedAddMonoid` / `IsOrderedAddMonoid` 的定义

English:
class IsOrderedAddMonoid
  parameters: (α : Type*) [AddCommMonoid α] [Preorder α]
  axioms and operations (2):
    - add_le_add_left((a b : α)) : a <= b -> forall c, a + c <= b + c
    - add_le_add_right((a b : α)) : a <= b -> forall c, c + a <= c + b  [default: fun h c => by rw [add_comm c]; rw [add_comm c]; exact add_le]

中文:
类 IsOrderedAddMonoid
  参数: (α : 类型) [AddCommMonoid α] [Preorder α]
  公理与运算 (2 个):
    - add_le_add_left((a b : α)) : a <= b -> 对任意 c, a + c <= b + c
    - add_le_add_right((a b : α)) : a <= b -> 对任意 c, c + a <= c + b  [默认: fun h c => by rw [add_comm c]; rw [add_comm c]; exact add_le]

Depends on / 依赖: add_comm, add_le_add_left
-/
class IsOrderedAddMonoid (α : Type*) [AddCommMonoid α] [Preorder α] where
  protected add_le_add_left (a b : α) : a <= b -> forall c, a + c <= b + c
  protected add_le_add_right (a b : α) : a <= b -> forall c, c + a <= c + b := fun h c => by
    rw [add_comm c]; rw [add_comm c]; exact add_le_add_left a b h c

/-- An ordered monoid is a monoid with a preorder such that multiplication is monotone. -/
@[to_additive]
/--
Definition of `IsOrderedMonoid` / `IsOrderedMonoid` 的定义

English:
class IsOrderedMonoid
  parameters: (α : Type*) [CommMonoid α] [Preorder α]
  axioms and operations (2):
    - mul_le_mul_left((a b : α)) : a <= b -> forall c, a * c <= b * c
    - mul_le_mul_right((a b : α)) : a <= b -> forall c, c * a <= c * b  [default: fun h c => by rw [mul_comm c]; rw [mul_comm c]; exact mul_le]

中文:
类 IsOrderedMonoid
  参数: (α : 类型) [CommMonoid α] [Preorder α]
  公理与运算 (2 个):
    - mul_le_mul_left((a b : α)) : a <= b -> 对任意 c, a * c <= b * c
    - mul_le_mul_right((a b : α)) : a <= b -> 对任意 c, c * a <= c * b  [默认: fun h c => by rw [mul_comm c]; rw [mul_comm c]; exact mul_le]

Depends on / 依赖: mul_comm, mul_le_mul_left
-/
class IsOrderedMonoid (α : Type*) [CommMonoid α] [Preorder α] where
  protected mul_le_mul_left (a b : α) : a <= b -> forall c, a * c <= b * c
  protected mul_le_mul_right (a b : α) : a <= b -> forall c, c * a <= c * b := fun h c => by
    rw [mul_comm c]; rw [mul_comm c]; exact mul_le_mul_left a b h c

section IsOrderedMonoid
variable [CommMonoid α] [Preorder α] [IsOrderedMonoid α]

@[to_additive]
instance (priority := 900) IsOrderedMonoid.toMulLeftMono : MulLeftMono α where
  elim := fun a _ _ bc => IsOrderedMonoid.mul_le_mul_right _ _ bc a

@[to_additive]
instance (priority := 900) IsOrderedMonoid.toMulRightMono : MulRightMono α where
  elim := fun a _ _ bc => IsOrderedMonoid.mul_le_mul_left _ _ bc a

end IsOrderedMonoid

/--
Definition of `IsOrderedCancelAddMonoid` / `IsOrderedCancelAddMonoid` 的定义

English:
class IsOrderedCancelAddMonoid
  parameters: (α : Type*) [AddCommMonoid α] [Preorder α]
  axioms and operations (2):
    - le_of_add_le_add_left : forall a b c : α, a + b <= a + c -> b <= c
    - le_of_add_le_add_right : forall a b c : α, b + a <= c + a -> b <= c  [default: fun a b c h => by rw [add_comm _ a]; rw [add_comm _ a] at h;]

中文:
类 IsOrderedCancelAddMonoid
  参数: (α : 类型) [AddCommMonoid α] [Preorder α]
  公理与运算 (2 个):
    - le_of_add_le_add_left : 对任意 a b c : α, a + b <= a + c -> b <= c
    - le_of_add_le_add_right : 对任意 a b c : α, b + a <= c + a -> b <= c  [默认: fun a b c h => by rw [add_comm _ a]; rw [add_comm _ a] at h;]

Depends on / 依赖: add_comm, le_of_add_le_add_left
-/
class IsOrderedCancelAddMonoid (α : Type*) [AddCommMonoid α] [Preorder α] extends
    IsOrderedAddMonoid α where
  protected le_of_add_le_add_left : forall a b c : α, a + b <= a + c -> b <= c
  protected le_of_add_le_add_right : forall a b c : α, b + a <= c + a -> b <= c := fun a b c h => by
    rw [add_comm _ a]; rw [add_comm _ a] at h; exact le_of_add_le_add_left a b c h

/-- An ordered cancellative monoid is an ordered monoid in which
multiplication is cancellative and monotone. -/
@[to_additive IsOrderedCancelAddMonoid]
/--
Definition of `IsOrderedCancelMonoid` / `IsOrderedCancelMonoid` 的定义

English:
class IsOrderedCancelMonoid
  parameters: (α : Type*) [CommMonoid α] [Preorder α]
  axioms and operations (2):
    - le_of_mul_le_mul_left : forall a b c : α, a * b <= a * c -> b <= c
    - le_of_mul_le_mul_right : forall a b c : α, b * a <= c * a -> b <= c  [default: fun a b c h => by rw [mul_comm _ a]; rw [mul_comm _ a] at h;]

中文:
类 IsOrderedCancelMonoid
  参数: (α : 类型) [CommMonoid α] [Preorder α]
  公理与运算 (2 个):
    - le_of_mul_le_mul_left : 对任意 a b c : α, a * b <= a * c -> b <= c
    - le_of_mul_le_mul_right : 对任意 a b c : α, b * a <= c * a -> b <= c  [默认: fun a b c h => by rw [mul_comm _ a]; rw [mul_comm _ a] at h;]

Depends on / 依赖: le_of_mul_le_mul_left, mul_comm
-/
class IsOrderedCancelMonoid (α : Type*) [CommMonoid α] [Preorder α] extends
    IsOrderedMonoid α where
  protected le_of_mul_le_mul_left : forall a b c : α, a * b <= a * c -> b <= c
  protected le_of_mul_le_mul_right : forall a b c : α, b * a <= c * a -> b <= c := fun a b c h => by
    rw [mul_comm _ a]; rw [mul_comm _ a] at h; exact le_of_mul_le_mul_left a b c h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: α] [PartialOrder α] [IsOrderedCancelAddMonoid α] :
  body: ⟨
    fun h => IsOrderedAddMonoid.add_le_add_left a b h c,
    IsOrderedCancelAddMonoid.le_of_add_le_add_right c a b⟩

中文:
实例 [AddCommMonoid
  签名: α] [PartialOrder α] [IsOrderedCancelAddMonoid α] :
  定义体: ⟨
    fun h => IsOrderedAddMonoid.add_le_add_left a b h c,
    IsOrderedCancelAddMonoid.le_of_add_le_add_right c a b⟩
-/
instance [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] :
    Lean.Grind.OrderedAdd α where
  add_le_left_iff {a b} c := ⟨
    fun h => IsOrderedAddMonoid.add_le_add_left a b h c,
    IsOrderedCancelAddMonoid.le_of_add_le_add_right c a b⟩

section IsOrderedCancelMonoid
variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]

-- See note [lower instance priority]
@[to_additive]
instance (priority := 200) IsOrderedCancelMonoid.toMulLeftReflectLE
  {α : Type*} [CommMonoid α] [Preorder α] [IsOrderedCancelMonoid α] : MulLeftReflectLE α where
  le_of_mul_le_mul_left' := IsOrderedCancelMonoid.le_of_mul_le_mul_left _ _ _

@[to_additive]
instance (priority := 900) IsOrderedCancelMonoid.toMulLeftReflectLT : MulLeftReflectLT α where
  elim := contravariant_lt_of_contravariant_le α α _ fun _ => MulLeftReflectLE.le_of_mul_le_mul_left'

@[to_additive]
/--
theorem `IsOrderedCancelMonoid.toMulRightReflectLT` / 定理 `IsOrderedCancelMonoid.toMulRightReflectLT`

English:
theorem IsOrderedCancelMonoid.toMulRightReflectLT
  statement: MulRightReflectLT α
  proof: inferInstance

中文:
定理 IsOrderedCancelMonoid.toMulRightReflectLT
  结论: MulRightReflectLT α
  证明: inferInstance
-/
theorem IsOrderedCancelMonoid.toMulRightReflectLT : MulRightReflectLT α :=
  inferInstance

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) IsOrderedCancelMonoid.toIsCancelMul : IsCancelMul α where
  mul_left_cancel _ _ _ h :=
(le_of_mul_le_mul_left' h.le).antisymm le_of_mul_le_mul_left' h.ge
  mul_right_cancel _ _ _ h :=
(le_of_mul_le_mul_right' h.le).antisymm le_of_mul_le_mul_right' h.ge

@[to_additive]
/--
theorem `IsOrderedCancelMonoid.of_mul_lt_mul_left` / 定理 `IsOrderedCancelMonoid.of_mul_lt_mul_left`

English:
theorem IsOrderedCancelMonoid.of_mul_lt_mul_left
  statement: {α : Type*} [CommMonoid α] [LinearOrder α]
  proof: by
    obtain rfl | h := eq_or_lt_of_le h
    · simp
    · simpa [mul_comm] using (hmul _ _ _ h).le
  le_of_mul_le_mul_left a b c h := by
    contrapose! h
    exact hmul _ _ _ h

中文:
定理 IsOrderedCancelMonoid.of_mul_lt_mul_left
  结论: {α : 类型} [CommMonoid α] [LinearOrder α]
  证明: by
    obtain rfl | h := eq_or_lt_of_le h
    · simp
    · simpa [mul_comm] using (hmul _ _ _ h).le
  le_of_mul_le_mul_left a b c h := by
    contrapose! h
    exact hmul _ _ _ h

Depends on / 依赖: contrapose, eq_or_lt_of_le, le_of_mul_le_mul_left, mul_comm
-/
theorem IsOrderedCancelMonoid.of_mul_lt_mul_left {α : Type*} [CommMonoid α] [LinearOrder α]
    (hmul : forall a b c : α, b < c -> a * b < a * c) : IsOrderedCancelMonoid α where
  mul_le_mul_left a b h c := by
    obtain rfl | h := eq_or_lt_of_le h
    · simp
    · simpa [mul_comm] using (hmul _ _ _ h).le
  le_of_mul_le_mul_left a b c h := by
    contrapose! h
    exact hmul _ _ _ h

end IsOrderedCancelMonoid

variable [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α] {a : α}

@[to_additive (attr := simp)]
/--
theorem `one_le_mul_self_iff` / 定理 `one_le_mul_self_iff`

English:
theorem one_le_mul_self_iff
  statement: 1 <= a * a ↔ 1 <= a
  proof: ⟨fun h => by contrapose! h; exact mul_lt_one' h h, fun h => one_le_mul h h⟩

@[to_additive (attr := simp)]

中文:
定理 one_le_mul_self_iff
  结论: 1 <= a * a ↔ 1 <= a
  证明: ⟨fun h => by contrapose! h; exact mul_lt_one' h h, fun h => one_le_mul h h⟩

@[to_additive (attr := simp)]

Depends on / 依赖: contrapose, mul_lt_one, one_le_mul
-/
theorem one_le_mul_self_iff : 1 <= a * a ↔ 1 <= a :=
  ⟨fun h => by contrapose! h; exact mul_lt_one' h h, fun h => one_le_mul h h⟩

@[to_additive (attr := simp)]
/--
theorem `one_lt_mul_self_iff` / 定理 `one_lt_mul_self_iff`

English:
theorem one_lt_mul_self_iff
  statement: 1 < a * a ↔ 1 < a
  proof: ⟨fun h => by contrapose! h; exact mul_le_one' h h, fun h => one_lt_mul'' h h⟩

@[to_additive (attr := simp)]

中文:
定理 one_lt_mul_self_iff
  结论: 1 < a * a ↔ 1 < a
  证明: ⟨fun h => by contrapose! h; exact mul_le_one' h h, fun h => one_lt_mul'' h h⟩

@[to_additive (attr := simp)]

Depends on / 依赖: contrapose, mul_le_one, one_lt_mul
-/
theorem one_lt_mul_self_iff : 1 < a * a ↔ 1 < a :=
  ⟨fun h => by contrapose! h; exact mul_le_one' h h, fun h => one_lt_mul'' h h⟩

@[to_additive (attr := simp)]
/--
theorem `mul_self_le_one_iff` / 定理 `mul_self_le_one_iff`

English:
theorem mul_self_le_one_iff
  statement: a * a <= 1 ↔ a <= 1
  proof: by contrapose!; exact one_lt_mul_self_iff

@[to_additive (attr := simp)]

中文:
定理 mul_self_le_one_iff
  结论: a * a <= 1 ↔ a <= 1
  证明: by contrapose!; exact one_lt_mul_self_iff

@[to_additive (attr := simp)]

Depends on / 依赖: contrapose, one_lt_mul_self_iff
-/
theorem mul_self_le_one_iff : a * a <= 1 ↔ a <= 1 := by contrapose!; exact one_lt_mul_self_iff

@[to_additive (attr := simp)]
/--
theorem `mul_self_lt_one_iff` / 定理 `mul_self_lt_one_iff`

English:
theorem mul_self_lt_one_iff
  statement: a * a < 1 ↔ a < 1
  proof: by contrapose!; exact one_le_mul_self_iff

中文:
定理 mul_self_lt_one_iff
  结论: a * a < 1 ↔ a < 1
  证明: by contrapose!; exact one_le_mul_self_iff

Depends on / 依赖: contrapose, one_le_mul_self_iff
-/
theorem mul_self_lt_one_iff : a * a < 1 ↔ a < 1 := by contrapose!; exact one_le_mul_self_iff
