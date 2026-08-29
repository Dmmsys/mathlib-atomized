/-
Copyright (c) 2021 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Order.MinMax

/-!
# Unbundled and weaker forms of canonically ordered monoids

This file provides a Prop-valued mixin for monoids satisfying a one-sided cancellativity property,
namely that there is some `c` such that `b = a + c` if `a ≤ b`. This is particularly useful for
generalising statements from groups/rings/fields that don't mention negation or subtraction to
monoids/semirings/semifields.
-/

public section

universe u
variable {α : Type u}

/--
Definition of `ExistsAddOfLE` / `ExistsAddOfLE` 的定义

English:
class ExistsAddOfLE
  parameters: (α : Type u) [Add α] [LE α]
  axioms and operations (1):
    - exists_add_of_le : forall {a b : α}, a <= b -> exists c : α, b = a + c

中文:
类 ExistsAddOfLE
  参数: (α : 类型u) [加法 α] [LE α]
  公理与运算 (1 个):
    - exists_add_of_le : 对任意 {a b : α}, a <= b -> 存在 c : α, b = a + c
-/
class ExistsAddOfLE (α : Type u) [Add α] [LE α] : Prop where
  /-- For `a ≤ b`, there is a `c` so `b = a + c`. -/
  exists_add_of_le : forall {a b : α}, a <= b -> exists c : α, b = a + c

/-- An ordered monoid with one-sided 'division' in the sense that
if `a ≤ b`, there is some `c` for which `a * c = b`. This is a weaker version
of the condition on canonical orderings defined by `CanonicallyOrderedMul`. -/
@[to_additive]
/--
Definition of `ExistsMulOfLE` / `ExistsMulOfLE` 的定义

English:
class ExistsMulOfLE
  parameters: (α : Type u) [Mul α] [LE α]
  axioms and operations (1):
    - exists_mul_of_le : forall {a b : α}, a <= b -> exists c : α, b = a * c

中文:
类 ExistsMulOfLE
  参数: (α : 类型u) [乘法 α] [LE α]
  公理与运算 (1 个):
    - exists_mul_of_le : 对任意 {a b : α}, a <= b -> 存在 c : α, b = a * c
-/
class ExistsMulOfLE (α : Type u) [Mul α] [LE α] : Prop where
  /-- For `a ≤ b`, `a` left divides `b` -/
  exists_mul_of_le : forall {a b : α}, a <= b -> exists c : α, b = a * c

export ExistsMulOfLE (exists_mul_of_le)
export ExistsAddOfLE (exists_add_of_le)

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) Group.existsMulOfLE (α : Type u) [Group α] [LE α] : ExistsMulOfLE α :=
  ⟨fun {a b} _ => ⟨a⁻¹ * b, (mul_inv_cancel_left _ _).symm⟩⟩

section MulOneClass
variable [MulOneClass α] [Preorder α] [ExistsMulOfLE α] {a b : α}

/--
lemma `exists_one_le_mul_of_le` / 引理 `exists_one_le_mul_of_le`

English:
lemma exists_one_le_mul_of_le
  given: [MulLeftReflectLE α] (h : a <= b)
  proof: by
  obtain ⟨c, rfl⟩ := exists_mul_of_le h; exact ⟨c, one_le_of_le_mul_right h, rfl⟩

中文:
引理 存在_one_le_mul_of_le
  条件: [MulLeftReflectLE α] (h : a <= b)
  证明: by
  obtain ⟨c, rfl⟩ := exists_mul_of_le h; exact ⟨c, one_le_of_le_mul_right h, rfl⟩
-/
@[to_additive] lemma exists_one_le_mul_of_le [MulLeftReflectLE α] (h : a <= b) :
    exists c, 1 <= c ∧ a * c = b := by
  obtain ⟨c, rfl⟩ := exists_mul_of_le h; exact ⟨c, one_le_of_le_mul_right h, rfl⟩

/--
lemma `exists_one_lt_mul_of_lt'` / 引理 `exists_one_lt_mul_of_lt'`

English:
lemma exists_one_lt_mul_of_lt'
  given: [MulLeftReflectLT α] (h : a < b)
  proof: by
  obtain ⟨c, rfl⟩ := exists_mul_of_le h.le; exact ⟨c, one_lt_of_lt_mul_right h, rfl⟩

中文:
引理 存在_one_lt_mul_of_lt'
  条件: [MulLeftReflectLT α] (h : a < b)
  证明: by
  obtain ⟨c, rfl⟩ := exists_mul_of_le h.le; exact ⟨c, one_lt_of_lt_mul_right h, rfl⟩
-/
@[to_additive] lemma exists_one_lt_mul_of_lt' [MulLeftReflectLT α] (h : a < b) :
    exists c, 1 < c ∧ a * c = b := by
  obtain ⟨c, rfl⟩ := exists_mul_of_le h.le; exact ⟨c, one_lt_of_lt_mul_right h, rfl⟩

/--
lemma `le_iff_exists_one_le_mul` / 引理 `le_iff_exists_one_le_mul`

English:
lemma le_iff_exists_one_le_mul
  statement: [MulLeftMono α]
  proof: ⟨exists_one_le_mul_of_le, by rintro ⟨c, hc, rfl⟩; exact le_mul_of_one_le_right' hc⟩

中文:
引理 le_iff_存在_one_le_mul
  结论: [MulLeftMono α]
  证明: ⟨exists_one_le_mul_of_le, by rintro ⟨c, hc, rfl⟩; exact le_mul_of_one_le_right' hc⟩
-/
@[to_additive] lemma le_iff_exists_one_le_mul [MulLeftMono α]
    [MulLeftReflectLE α] : a <= b ↔ exists c, 1 <= c ∧ a * c = b :=
  ⟨exists_one_le_mul_of_le, by rintro ⟨c, hc, rfl⟩; exact le_mul_of_one_le_right' hc⟩

/--
lemma `lt_iff_exists_one_lt_mul` / 引理 `lt_iff_exists_one_lt_mul`

English:
lemma lt_iff_exists_one_lt_mul
  statement: [MulLeftStrictMono α]
  proof: ⟨exists_one_lt_mul_of_lt', by rintro ⟨c, hc, rfl⟩; exact lt_mul_of_one_lt_right' _ hc⟩

中文:
引理 lt_iff_存在_one_lt_mul
  结论: [MulLeftStrictMono α]
  证明: ⟨exists_one_lt_mul_of_lt', by rintro ⟨c, hc, rfl⟩; exact lt_mul_of_one_lt_right' _ hc⟩
-/
@[to_additive] lemma lt_iff_exists_one_lt_mul [MulLeftStrictMono α]
    [MulLeftReflectLT α] : a < b ↔ exists c, 1 < c ∧ a * c = b :=
  ⟨exists_one_lt_mul_of_lt', by rintro ⟨c, hc, rfl⟩; exact lt_mul_of_one_lt_right' _ hc⟩

end MulOneClass

section ExistsMulOfLE

variable [LinearOrder α] [DenselyOrdered α] [Monoid α] [ExistsMulOfLE α]
  [MulLeftReflectLT α] {a b : α}

@[to_additive]
/--
theorem `le_of_forall_one_lt_le_mul` / 定理 `le_of_forall_one_lt_le_mul`

English:
theorem le_of_forall_one_lt_le_mul
  given: (h : forall ε : α, 1 < ε -> a <= b * ε)
  statement: a <= b
  proof: le_of_forall_gt_imp_ge_of_dense fun x hxb => by
    obtain ⟨ε, rfl⟩ := exists_mul_of_le hxb.le
    exact h _ (one_lt_of_lt_mul_right hxb)

@[to_additive]

中文:
定理 le_of_对任意_one_lt_le_mul
  条件: (h : 对任意 ε : α, 1 < ε -> a <= b * ε)
  结论: a <= b
  证明: le_of_forall_gt_imp_ge_of_dense fun x hxb => by
    obtain ⟨ε, rfl⟩ := exists_mul_of_le hxb.le
    exact h _ (one_lt_of_lt_mul_right hxb)

@[to_additive]

Depends on / 依赖: exists_mul_of_le, hxb.le, le_of_forall_gt_imp_ge_of_dense, one_lt_of_lt_mul_right
-/
theorem le_of_forall_one_lt_le_mul (h : forall ε : α, 1 < ε -> a <= b * ε) : a <= b :=
  le_of_forall_gt_imp_ge_of_dense fun x hxb => by
    obtain ⟨ε, rfl⟩ := exists_mul_of_le hxb.le
    exact h _ (one_lt_of_lt_mul_right hxb)

@[to_additive]
/--
theorem `le_of_forall_one_lt_lt_mul'` / 定理 `le_of_forall_one_lt_lt_mul'`

English:
theorem le_of_forall_one_lt_lt_mul'
  given: (h : forall ε : α, 1 < ε -> a < b * ε)
  statement: a <= b
  proof: le_of_forall_one_lt_le_mul fun ε hε => (h ε hε).le

@[to_additive]

中文:
定理 le_of_对任意_one_lt_lt_mul'
  条件: (h : 对任意 ε : α, 1 < ε -> a < b * ε)
  结论: a <= b
  证明: le_of_forall_one_lt_le_mul fun ε hε => (h ε hε).le

@[to_additive]

Depends on / 依赖: le_of_forall_one_lt_le_mul
-/
theorem le_of_forall_one_lt_lt_mul' (h : forall ε : α, 1 < ε -> a < b * ε) : a <= b :=
  le_of_forall_one_lt_le_mul fun ε hε => (h ε hε).le

@[to_additive]
/--
theorem `le_iff_forall_one_lt_lt_mul'` / 定理 `le_iff_forall_one_lt_lt_mul'`

English:
theorem le_iff_forall_one_lt_lt_mul'
  given: [MulLeftStrictMono α]
  proof: ⟨fun h _ => lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul'⟩

@[to_additive]

中文:
定理 le_iff_对任意_one_lt_lt_mul'
  条件: [MulLeftStrictMono α]
  证明: ⟨fun h _ => lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul'⟩

@[to_additive]

Depends on / 依赖: le_of_forall_one_lt_lt_mul, lt_mul_of_le_of_one_lt
-/
theorem le_iff_forall_one_lt_lt_mul' [MulLeftStrictMono α] :
    a <= b ↔ forall ε, 1 < ε -> a < b * ε :=
  ⟨fun h _ => lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul'⟩

@[to_additive]
/--
theorem `le_iff_forall_one_lt_le_mul` / 定理 `le_iff_forall_one_lt_le_mul`

English:
theorem le_iff_forall_one_lt_le_mul
  given: [MulLeftStrictMono α]
  proof: .le, le_of_forall_one_lt_le_mul⟩ ⟨fun h _ hε => lt_mul_of_le_of_one_lt h hε

中文:
定理 le_iff_对任意_one_lt_le_mul
  条件: [MulLeftStrictMono α]
  证明: .le, le_of_forall_one_lt_le_mul⟩ ⟨fun h _ hε => lt_mul_of_le_of_one_lt h hε

Depends on / 依赖: le_of_forall_one_lt_le_mul, lt_mul_of_le_of_one_lt
-/
theorem le_iff_forall_one_lt_le_mul [MulLeftStrictMono α] :
    a <= b ↔ forall ε, 1 < ε -> a <= b * ε :=
.le, le_of_forall_one_lt_le_mul⟩ ⟨fun h _ hε => lt_mul_of_le_of_one_lt h hε

end ExistsMulOfLE
