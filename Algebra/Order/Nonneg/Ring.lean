/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Nonneg.Basic
public import Mathlib.Algebra.Order.Nonneg.Lattice
public import Mathlib.Algebra.Order.Ring.InjSurj
public import Mathlib.Tactic.FastInstance

/-!
# Bundled ordered algebra instance on the type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

Currently we only state instances and states some `simp`/`norm_cast` lemmas.

When `α` is `ℝ`, this will give us some properties about `ℝ≥0`.

## Implementation Notes

Instead of `{x : α // 0 ≤ x}` we could also use `Set.Ici (0 : α)`, which is definitionally equal.
However, using the explicit subtype has a big advantage: when writing an element explicitly
with a proof of nonnegativity as `⟨x, hx⟩`, the `hx` is expected to have type `0 ≤ x`. If we would
use `Ici 0`, then the type is expected to be `x ∈ Ici 0`. Although these types are definitionally
equal, this often confuses the elaborator. Similar problems arise when doing cases on an element.

The disadvantage is that we have to duplicate some instances about `Set.Ici` to this subtype.
-/

public section

open Set

variable {α : Type*}

namespace Nonneg

/--
Instance `isOrderedAddMonoid` / 实例 `isOrderedAddMonoid`

English:
instance isOrderedAddMonoid
  signature: [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
  body: Function.Injective.isOrderedAddMonoid Subtype.val Nonneg.coe_add .rfl

中文:
实例 isOrderedAddMonoid
  签名: [加法交换幺半群 α] [偏序 α] [是OrderedAdd幺半群 α]
  定义体: Function.Injective.isOrderedAddMonoid Subtype.val Nonneg.coe_add .rfl

Depends on / 依赖: Function, Function.Injective.isOrderedAddMonoid, Injective, Nonneg, Nonneg.coe_add, Subtype, Subtype.val, coe_add, isOrderedAddMonoid
-/
instance isOrderedAddMonoid [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] :
    IsOrderedAddMonoid { x : α // 0 <= x } :=
  Function.Injective.isOrderedAddMonoid Subtype.val Nonneg.coe_add .rfl

/--
Instance `isOrderedCancelAddMonoid` / 实例 `isOrderedCancelAddMonoid`

English:
instance isOrderedCancelAddMonoid
  signature: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  body: Function.Injective.isOrderedCancelAddMonoid _ Nonneg.coe_add .rfl

中文:
实例 isOrderedCancelAddMonoid
  签名: [加法交换幺半群 α] [偏序 α] [是OrderedCancelAdd幺半群 α]
  定义体: Function.Injective.isOrderedCancelAddMonoid _ Nonneg.coe_add .rfl

Depends on / 依赖: Function, Function.Injective.isOrderedCancelAddMonoid, Injective, Nonneg, Nonneg.coe_add, coe_add, isOrderedCancelAddMonoid
-/
instance isOrderedCancelAddMonoid [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] :
    IsOrderedCancelAddMonoid { x : α // 0 <= x } :=
  Function.Injective.isOrderedCancelAddMonoid _ Nonneg.coe_add .rfl

/--
Instance `isOrderedRing` / 实例 `isOrderedRing`

English:
instance isOrderedRing
  signature: [Semiring α] [PartialOrder α] [IsOrderedRing α]
  body: Function.Injective.isOrderedRing Subtype.val Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add
    Nonneg.coe_mul .rfl

中文:
实例 isOrderedRing
  签名: [半环 α] [偏序 α] [是Ordered环 α]
  定义体: Function.Injective.isOrderedRing Subtype.val Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add
    Nonneg.coe_mul .rfl

Depends on / 依赖: Function, Function.Injective.isOrderedRing, Injective, Nonneg, Nonneg.coe_add, Nonneg.coe_mul, Nonneg.coe_one, Nonneg.coe_zero, Subtype, Subtype.val, coe_add, coe_mul, coe_one, coe_zero, isOrderedRing
-/
instance isOrderedRing [Semiring α] [PartialOrder α] [IsOrderedRing α] :
    IsOrderedRing { x : α // 0 <= x } :=
  Function.Injective.isOrderedRing Subtype.val Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add
    Nonneg.coe_mul .rfl

/--
Instance `isStrictOrderedRing` / 实例 `isStrictOrderedRing`

English:
instance isStrictOrderedRing
  signature: [Semiring α] [PartialOrder α] [IsStrictOrderedRing α]
  body: Function.Injective.isStrictOrderedRing Subtype.val Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add
    Nonneg.coe_mul .rfl .rfl

中文:
实例 isStrictOrderedRing
  签名: [半环 α] [偏序 α] [是StrictOrdered环 α]
  定义体: Function.Injective.isStrictOrderedRing Subtype.val Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add
    Nonneg.coe_mul .rfl .rfl

Depends on / 依赖: Function, Function.Injective.isStrictOrderedRing, Injective, Nonneg, Nonneg.coe_add, Nonneg.coe_mul, Nonneg.coe_one, Nonneg.coe_zero, Subtype, Subtype.val, coe_add, coe_mul, coe_one, coe_zero, isStrictOrderedRing
-/
instance isStrictOrderedRing [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] :
    IsStrictOrderedRing { x : α // 0 <= x } :=
  Function.Injective.isStrictOrderedRing Subtype.val Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add
    Nonneg.coe_mul .rfl .rfl

/--
Instance `existsAddOfLE` / 实例 `existsAddOfLE`

English:
instance existsAddOfLE
  signature: [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  body: ⟨fun {a b} h => by
    rw [← Subtype.coe_le_coe] at h
    obtain ⟨c, hc⟩ := exists_add_of_le h
    refine ⟨⟨c, ?_⟩, by simp [Subtype.ext_iff, hc]⟩
    rw [← add_zero a.val]; rw [hc] at h
    exact le_of_add_le_add_left h⟩

中文:
实例 存在AddOfLE
  签名: [半环 α] [偏序 α] [是StrictOrdered环 α] [ExistsAddOfLE α]
  定义体: ⟨fun {a b} h => by
    rw [← Subtype.coe_le_coe] at h
    obtain ⟨c, hc⟩ := exists_add_of_le h
    refine ⟨⟨c, ?_⟩, by simp [Subtype.ext_iff, hc]⟩
    rw [← add_zero a.val]; rw [hc] at h
    exact le_of_add_le_add_left h⟩

Depends on / 依赖: Subtype, Subtype.coe_le_coe, Subtype.ext_iff, a.val, add_zero, coe_le_coe, exists_add_of_le, ext_iff, le_of_add_le_add_left
-/
instance existsAddOfLE [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] :
    ExistsAddOfLE { x : α // 0 <= x } :=
  ⟨fun {a b} h => by
    rw [← Subtype.coe_le_coe] at h
    obtain ⟨c, hc⟩ := exists_add_of_le h
    refine ⟨⟨c, ?_⟩, by simp [Subtype.ext_iff, hc]⟩
    rw [← add_zero a.val]; rw [hc] at h
    exact le_of_add_le_add_left h⟩

/--
Instance `nontrivial` / 实例 `nontrivial`

English:
instance nontrivial
  signature: [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
  body: ⟨⟨0, 1, fun h => zero_ne_one (congr_arg Subtype.val h)⟩⟩

中文:
实例 nontrivial
  签名: [半环 α] [线性序 α] [是StrictOrdered环 α]
  定义体: ⟨⟨0, 1, fun h => zero_ne_one (congr_arg Subtype.val h)⟩⟩

Depends on / 依赖: Subtype, Subtype.val, congr_arg, zero_ne_one
-/
instance nontrivial [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] :
    Nontrivial { x : α // 0 <= x } :=
  ⟨⟨0, 1, fun h => zero_ne_one (congr_arg Subtype.val h)⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: α] [AddGroup α] [LinearOrder α] [AddLeftMono α] :
  body: by
  have ⟨a, ha⟩ := exists_ne (0 : α)
  obtain lt | lt := ha.lt_or_gt
  · exact ⟨0, ⟨-a, neg_nonneg.mpr lt.le⟩, Subtype.coe_ne_coe.mp (neg_ne_zero.mpr ha).symm⟩
  · exact ⟨0, ⟨a, lt.le⟩, Subtype.coe_ne_coe.mp ha.symm⟩

中文:
实例 [非平凡
  签名: α] [加法群 α] [线性序 α] [AddLeftMono α] :
  定义体: by
  have ⟨a, ha⟩ := exists_ne (0 : α)
  obtain lt | lt := ha.lt_or_gt
  · exact ⟨0, ⟨-a, neg_nonneg.mpr lt.le⟩, Subtype.coe_ne_coe.mp (neg_ne_zero.mpr ha).symm⟩
  · exact ⟨0, ⟨a, lt.le⟩, Subtype.coe_ne_coe.mp ha.symm⟩

Depends on / 依赖: Subtype, Subtype.coe_ne_coe.mp, coe_ne_coe, exists_ne, ha.lt_or_gt, ha.symm, lt.le, lt_or_gt, neg_ne_zero, neg_ne_zero.mpr, neg_nonneg, neg_nonneg.mpr
-/
instance [Nontrivial α] [AddGroup α] [LinearOrder α] [AddLeftMono α] :
    Nontrivial { x : α // 0 <= x } := by
  have ⟨a, ha⟩ := exists_ne (0 : α)
  obtain lt | lt := ha.lt_or_gt
  · exact ⟨0, ⟨-a, neg_nonneg.mpr lt.le⟩, Subtype.coe_ne_coe.mp (neg_ne_zero.mpr ha).symm⟩
  · exact ⟨0, ⟨a, lt.le⟩, Subtype.coe_ne_coe.mp ha.symm⟩

/--
Instance `linearOrderedCommMonoidWithZero` / 实例 `linearOrderedCommMonoidWithZero`

English:
instance linearOrderedCommMonoidWithZero
  signature: [CommSemiring α] [LinearOrder α] [IsStrictOrderedRing α]
  body: a.2

中文:
实例 linearOrderedCommMonoidWithZero
  签名: [交换半环 α] [线性序 α] [是StrictOrdered环 α]
  定义体: a.2
-/
instance linearOrderedCommMonoidWithZero [CommSemiring α] [LinearOrder α] [IsStrictOrderedRing α] :
    LinearOrderedCommMonoidWithZero { x : α // 0 <= x } where
  isBot_zero a := a.2

/--
Instance `canonicallyOrderedAdd` / 实例 `canonicallyOrderedAdd`

English:
instance canonicallyOrderedAdd
  signature: [Ring α] [PartialOrder α] [IsOrderedRing α]
  body: le_add_of_nonneg_left b.2
  le_self_add _ b := le_add_of_nonneg_right b.2
  exists_add_of_le := fun {a b} h =>
    ⟨⟨b - a, sub_nonneg_of_le h⟩, Subtype.ext (add_sub_cancel _ _).symm⟩

中文:
实例 canonicallyOrderedAdd
  签名: [环 α] [偏序 α] [是Ordered环 α]
  定义体: le_add_of_nonneg_left b.2
  le_self_add _ b := le_add_of_nonneg_right b.2
  exists_add_of_le := fun {a b} h =>
    ⟨⟨b - a, sub_nonneg_of_le h⟩, Subtype.ext (add_sub_cancel _ _).symm⟩

Depends on / 依赖: le_add_of_nonneg_left
-/
instance canonicallyOrderedAdd [Ring α] [PartialOrder α] [IsOrderedRing α] :
    CanonicallyOrderedAdd { x : α // 0 <= x } where
  le_add_self _ b := le_add_of_nonneg_left b.2
  le_self_add _ b := le_add_of_nonneg_right b.2
  exists_add_of_le := fun {a b} h =>
    ⟨⟨b - a, sub_nonneg_of_le h⟩, Subtype.ext (add_sub_cancel _ _).symm⟩

/--
Instance `noZeroDivisors` / 实例 `noZeroDivisors`

English:
instance noZeroDivisors
  signature: [Semiring α] [PartialOrder α] [IsOrderedRing α] [NoZeroDivisors α]
  body: { eq_zero_or_eq_zero_of_mul_eq_zero := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      simp only [mk_mul_mk, mk_eq_zero, mul_eq_zero, imp_self] }

中文:
实例 noZeroDivisors
  签名: [半环 α] [偏序 α] [是Ordered环 α] [无零因子 α]
  定义体: { eq_zero_or_eq_zero_of_mul_eq_zero := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      simp only [mk_mul_mk, mk_eq_zero, mul_eq_zero, imp_self] }

Depends on / 依赖: eq_zero_or_eq_zero_of_mul_eq_zero, imp_self, mk_eq_zero, mk_mul_mk, mul_eq_zero
-/
instance noZeroDivisors [Semiring α] [PartialOrder α] [IsOrderedRing α] [NoZeroDivisors α] :
    NoZeroDivisors { x : α // 0 <= x } :=
  { eq_zero_or_eq_zero_of_mul_eq_zero := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      simp only [mk_mul_mk, mk_eq_zero, mul_eq_zero, imp_self] }

/--
Instance `orderedSub` / 实例 `orderedSub`

English:
instance orderedSub
  signature: [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  body: ⟨by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    simp only [sub_le_iff_le_add, Subtype.mk_le_mk, mk_sub_mk, mk_add_mk, toNonneg_le]⟩

中文:
实例 orderedSub
  签名: [环 α] [线性序 α] [是StrictOrdered环 α]
  定义体: ⟨by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    simp only [sub_le_iff_le_add, Subtype.mk_le_mk, mk_sub_mk, mk_add_mk, toNonneg_le]⟩

Depends on / 依赖: Subtype, Subtype.mk_le_mk, mk_add_mk, mk_le_mk, mk_sub_mk, sub_le_iff_le_add, toNonneg_le
-/
instance orderedSub [Ring α] [LinearOrder α] [IsStrictOrderedRing α] :
    OrderedSub { x : α // 0 <= x } :=
  ⟨by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    simp only [sub_le_iff_le_add, Subtype.mk_le_mk, mk_sub_mk, mk_add_mk, toNonneg_le]⟩

end Nonneg
