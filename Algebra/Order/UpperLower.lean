/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Lattice
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Algebra.Order.Monoid.OrderDual
public import Mathlib.Order.UpperLower.Closure

/-!
# Algebraic operations on upper/lower sets

Upper/lower sets are preserved under pointwise algebraic operations in ordered groups.
-/

public section

open Set
open scoped Pointwise

section OrderedCommMonoid

variable {α : Type*} [CommMonoid α] [Preorder α] [IsOrderedMonoid α] {s : Set α} {x : α}

@[to_additive]
/--
theorem `IsUpperSet.smul_subset` / 定理 `IsUpperSet.smul_subset`

English:
theorem IsUpperSet.smul_subset
  given: (hs : IsUpperSet s) (hx : 1 <= x)
  statement: x • s subseteq s
  proof: smul_set_subset_iff.2 fun _ => hs le_mul_of_one_le_left' hx

@[to_additive]

中文:
定理 是上集.smul_subset
  条件: (hs : 是上集 s) (hx : 1 <= x)
  结论: x • s subseteq s
  证明: smul_set_subset_iff.2 fun _ => hs le_mul_of_one_le_left' hx

@[to_additive]

Depends on / 依赖: le_mul_of_one_le_left, smul_set_subset_iff
-/
theorem IsUpperSet.smul_subset (hs : IsUpperSet s) (hx : 1 <= x) : x • s subseteq s :=
smul_set_subset_iff.2 fun _ => hs le_mul_of_one_le_left' hx

@[to_additive]
/--
theorem `IsLowerSet.smul_subset` / 定理 `IsLowerSet.smul_subset`

English:
theorem IsLowerSet.smul_subset
  given: (hs : IsLowerSet s) (hx : x <= 1)
  statement: x • s subseteq s
  proof: smul_set_subset_iff.2 fun _ => hs mul_le_of_le_one_left' hx

中文:
定理 是下集.smul_subset
  条件: (hs : 是下集 s) (hx : x <= 1)
  结论: x • s subseteq s
  证明: smul_set_subset_iff.2 fun _ => hs mul_le_of_le_one_left' hx

Depends on / 依赖: mul_le_of_le_one_left, smul_set_subset_iff
-/
theorem IsLowerSet.smul_subset (hs : IsLowerSet s) (hx : x <= 1) : x • s subseteq s :=
smul_set_subset_iff.2 fun _ => hs mul_le_of_le_one_left' hx

end OrderedCommMonoid

section OrderedCommGroup

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

@[to_additive]
/--
theorem `IsUpperSet.smul` / 定理 `IsUpperSet.smul`

English:
theorem IsUpperSet.smul
  given: (hs : IsUpperSet s)
  statement: IsUpperSet (a • s)
  proof: hs.image OrderIso.mulLeft _

@[to_additive]

中文:
定理 是上集.smul
  条件: (hs : 是上集 s)
  结论: 是上集 (a • s)
  证明: hs.image OrderIso.mulLeft _

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.mulLeft, hs.image, mulLeft
-/
theorem IsUpperSet.smul (hs : IsUpperSet s) : IsUpperSet (a • s) := hs.image OrderIso.mulLeft _

@[to_additive]
/--
theorem `IsLowerSet.smul` / 定理 `IsLowerSet.smul`

English:
theorem IsLowerSet.smul
  given: (hs : IsLowerSet s)
  statement: IsLowerSet (a • s)
  proof: hs.image OrderIso.mulLeft _

@[to_additive]

中文:
定理 是下集.smul
  条件: (hs : 是下集 s)
  结论: 是下集 (a • s)
  证明: hs.image OrderIso.mulLeft _

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.mulLeft, hs.image, mulLeft
-/
theorem IsLowerSet.smul (hs : IsLowerSet s) : IsLowerSet (a • s) := hs.image OrderIso.mulLeft _

@[to_additive]
/--
theorem `Set.OrdConnected.smul` / 定理 `Set.OrdConnected.smul`

English:
theorem Set.OrdConnected.smul
  given: (hs : s.OrdConnected)
  statement: (a • s).OrdConnected
  proof: by
  rw [← hs.upperClosure_inter_lowerClosure]; rw [smul_set_inter]
  exact (upperClosure _).upper.smul.ordConnected.inter (lowerClosure _).lower.smul.ordConnected

@[to_additive]

中文:
定理 集合.序连通.smul
  条件: (hs : s.序连通)
  结论: (a • s).序连通
  证明: by
  rw [← hs.upperClosure_inter_lowerClosure]; rw [smul_set_inter]
  exact (upperClosure _).upper.smul.ordConnected.inter (lowerClosure _).lower.smul.ordConnected

@[to_additive]

Depends on / 依赖: hs.upperClosure_inter_lowerClosure, lower.smul.ordConnected, lowerClosure, ordConnected, smul_set_inter, upper.smul.ordConnected.inter, upperClosure, upperClosure_inter_lowerClosure
-/
theorem Set.OrdConnected.smul (hs : s.OrdConnected) : (a • s).OrdConnected := by
  rw [← hs.upperClosure_inter_lowerClosure]; rw [smul_set_inter]
  exact (upperClosure _).upper.smul.ordConnected.inter (lowerClosure _).lower.smul.ordConnected

@[to_additive]
/--
theorem `IsUpperSet.mul_left` / 定理 `IsUpperSet.mul_left`

English:
theorem IsUpperSet.mul_left
  given: (ht : IsUpperSet t)
  statement: IsUpperSet (s * t)
  proof: by
  rw [← smul_eq_mul]; rw [← Set.iUnion_smul_set]
  exact isUpperSet_iUnion₂ fun x _ => ht.smul

@[to_additive]

中文:
定理 是上集.mul_left
  条件: (ht : 是上集 t)
  结论: 是上集 (s * t)
  证明: by
  rw [← smul_eq_mul]; rw [← Set.iUnion_smul_set]
  exact isUpperSet_iUnion₂ fun x _ => ht.smul

@[to_additive]

Depends on / 依赖: Set.iUnion_smul_set, ht.smul, iUnion_smul_set, smul_eq_mul
-/
theorem IsUpperSet.mul_left (ht : IsUpperSet t) : IsUpperSet (s * t) := by
  rw [← smul_eq_mul]; rw [← Set.iUnion_smul_set]
  exact isUpperSet_iUnion₂ fun x _ => ht.smul

@[to_additive]
/--
theorem `IsUpperSet.mul_right` / 定理 `IsUpperSet.mul_right`

English:
theorem IsUpperSet.mul_right
  given: (hs : IsUpperSet s)
  statement: IsUpperSet (s * t)
  proof: by
  rw [mul_comm]
  exact hs.mul_left

@[to_additive]

中文:
定理 是上集.mul_right
  条件: (hs : 是上集 s)
  结论: 是上集 (s * t)
  证明: by
  rw [mul_comm]
  exact hs.mul_left

@[to_additive]

Depends on / 依赖: hs.mul_left, mul_comm, mul_left
-/
theorem IsUpperSet.mul_right (hs : IsUpperSet s) : IsUpperSet (s * t) := by
  rw [mul_comm]
  exact hs.mul_left

@[to_additive]
/--
theorem `IsLowerSet.mul_left` / 定理 `IsLowerSet.mul_left`

English:
theorem IsLowerSet.mul_left
  given: (ht : IsLowerSet t)
  statement: IsLowerSet (s * t)
  proof: ht.toDual.mul_left

@[to_additive]

中文:
定理 是下集.mul_left
  条件: (ht : 是下集 t)
  结论: 是下集 (s * t)
  证明: ht.toDual.mul_left

@[to_additive]

Depends on / 依赖: ht.toDual.mul_left, mul_left, toDual
-/
theorem IsLowerSet.mul_left (ht : IsLowerSet t) : IsLowerSet (s * t) := ht.toDual.mul_left

@[to_additive]
/--
theorem `IsLowerSet.mul_right` / 定理 `IsLowerSet.mul_right`

English:
theorem IsLowerSet.mul_right
  given: (hs : IsLowerSet s)
  statement: IsLowerSet (s * t)
  proof: hs.toDual.mul_right

@[to_additive]

中文:
定理 是下集.mul_right
  条件: (hs : 是下集 s)
  结论: 是下集 (s * t)
  证明: hs.toDual.mul_right

@[to_additive]

Depends on / 依赖: hs.toDual.mul_right, mul_right, toDual
-/
theorem IsLowerSet.mul_right (hs : IsLowerSet s) : IsLowerSet (s * t) := hs.toDual.mul_right

@[to_additive]
/--
theorem `IsUpperSet.inv` / 定理 `IsUpperSet.inv`

English:
theorem IsUpperSet.inv
  statement: {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
  proof: fun _ _ h => hs inv_le_inv' h

@[to_additive]

中文:
定理 是上集.inv
  结论: {α : 类型} [交换群 α] [偏序 α] [是Ordered幺半群 α]
  证明: fun _ _ h => hs inv_le_inv' h

@[to_additive]

Depends on / 依赖: inv_le_inv
-/
theorem IsUpperSet.inv {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
{s : Set α} (hs : IsUpperSet s) : IsLowerSet s⁻¹ := fun _ _ h => hs inv_le_inv' h

@[to_additive]
/--
theorem `IsLowerSet.inv` / 定理 `IsLowerSet.inv`

English:
theorem IsLowerSet.inv
  statement: {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
  proof: fun _ _ h => hs inv_le_inv' h

@[to_additive]

中文:
定理 是下集.inv
  结论: {α : 类型} [交换群 α] [偏序 α] [是Ordered幺半群 α]
  证明: fun _ _ h => hs inv_le_inv' h

@[to_additive]

Depends on / 依赖: inv_le_inv
-/
theorem IsLowerSet.inv {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
{s : Set α} (hs : IsLowerSet s) : IsUpperSet s⁻¹ := fun _ _ h => hs inv_le_inv' h

@[to_additive]
/--
theorem `IsUpperSet.div_left` / 定理 `IsUpperSet.div_left`

English:
theorem IsUpperSet.div_left
  statement: {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
  proof: by
  rw [div_eq_mul_inv]
  exact ht.inv.mul_left

@[to_additive]

中文:
定理 是上集.div_left
  结论: {α : 类型} [交换群 α] [偏序 α] [是Ordered幺半群 α]
  证明: by
  rw [div_eq_mul_inv]
  exact ht.inv.mul_left

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, ht.inv.mul_left, mul_left
-/
theorem IsUpperSet.div_left {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
    {s t : Set α} (ht : IsUpperSet t) : IsLowerSet (s / t) := by
  rw [div_eq_mul_inv]
  exact ht.inv.mul_left

@[to_additive]
/--
theorem `IsUpperSet.div_right` / 定理 `IsUpperSet.div_right`

English:
theorem IsUpperSet.div_right
  given: (hs : IsUpperSet s)
  statement: IsUpperSet (s / t)
  proof: by
  rw [div_eq_mul_inv]
  exact hs.mul_right

@[to_additive]

中文:
定理 是上集.div_right
  条件: (hs : 是上集 s)
  结论: 是上集 (s / t)
  证明: by
  rw [div_eq_mul_inv]
  exact hs.mul_right

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, hs.mul_right, mul_right
-/
theorem IsUpperSet.div_right (hs : IsUpperSet s) : IsUpperSet (s / t) := by
  rw [div_eq_mul_inv]
  exact hs.mul_right

@[to_additive]
/--
theorem `IsLowerSet.div_left` / 定理 `IsLowerSet.div_left`

English:
theorem IsLowerSet.div_left
  statement: {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
  proof: ht.toDual.div_left

@[to_additive]

中文:
定理 是下集.div_left
  结论: {α : 类型} [交换群 α] [偏序 α] [是Ordered幺半群 α]
  证明: ht.toDual.div_left

@[to_additive]

Depends on / 依赖: div_left, ht.toDual.div_left, toDual
-/
theorem IsLowerSet.div_left {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
  {s t : Set α} (ht : IsLowerSet t) : IsUpperSet (s / t) := ht.toDual.div_left

@[to_additive]
/--
theorem `IsLowerSet.div_right` / 定理 `IsLowerSet.div_right`

English:
theorem IsLowerSet.div_right
  given: (hs : IsLowerSet s)
  statement: IsLowerSet (s / t)
  proof: hs.toDual.div_right

中文:
定理 是下集.div_right
  条件: (hs : 是下集 s)
  结论: 是下集 (s / t)
  证明: hs.toDual.div_right

Depends on / 依赖: div_right, hs.toDual.div_right, toDual
-/
theorem IsLowerSet.div_right (hs : IsLowerSet s) : IsLowerSet (s / t) := hs.toDual.div_right

namespace UpperSet

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (UpperSet α)
  body: ⟨Ici 1⟩

@[to_additive]

中文:
实例 :
  签名: 幺 (上集 α)
  定义体: ⟨Ici 1⟩

@[to_additive]
-/
instance : One (UpperSet α) :=
  ⟨Ici 1⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (UpperSet α)
  body: ⟨fun s t => ⟨image2 (· * ·) s t, s.2.mul_right⟩⟩

@[to_additive]

中文:
实例 :
  签名: 乘法 (上集 α)
  定义体: ⟨fun s t => ⟨image2 (· * ·) s t, s.2.mul_right⟩⟩

@[to_additive]

Depends on / 依赖: image2, mul_right
-/
instance : Mul (UpperSet α) :=
  ⟨fun s t => ⟨image2 (· * ·) s t, s.2.mul_right⟩⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div (UpperSet α)
  body: ⟨fun s t => ⟨image2 (· / ·) s t, s.2.div_right⟩⟩

@[to_additive]

中文:
实例 :
  签名: 除法 (上集 α)
  定义体: ⟨fun s t => ⟨image2 (· / ·) s t, s.2.div_right⟩⟩

@[to_additive]

Depends on / 依赖: div_right, image2
-/
instance : Div (UpperSet α) :=
  ⟨fun s t => ⟨image2 (· / ·) s t, s.2.div_right⟩⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul α (UpperSet α)
  body: ⟨fun a s => ⟨(a • ·) '' s, s.2.smul⟩⟩

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp, norm_cast)]

中文:
实例 :
  签名: 标量乘法 α (上集 α)
  定义体: ⟨fun a s => ⟨(a • ·) '' s, s.2.smul⟩⟩

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp, norm_cast)]
-/
instance : SMul α (UpperSet α) :=
  ⟨fun a s => ⟨(a • ·) '' s, s.2.smul⟩⟩

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : UpperSet α) : Set α) = Set.Ici 1
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_one
  结论: ((1 : 上集 α) : 集合 α) = 集合.左闭右无界区间 1
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_one : ((1 : UpperSet α) : Set α) = Set.Ici 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (s t : UpperSet α)
  statement: (↑(s * t) : Set α) = s * t
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_mul
  条件: (s t : 上集 α)
  结论: (↑(s * t) : 集合 α) = s * t
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_mul (s t : UpperSet α) : (↑(s * t) : Set α) = s * t :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: (s t : UpperSet α)
  statement: (↑(s / t) : Set α) = s / t
  proof: rfl

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp)]

中文:
定理 coe_div
  条件: (s t : 上集 α)
  结论: (↑(s / t) : 集合 α) = s / t
  证明: rfl

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp)]
-/
theorem coe_div (s t : UpperSet α) : (↑(s / t) : Set α) = s / t :=
  rfl

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp)]
/--
theorem `Ici_one` / 定理 `Ici_one`

English:
theorem Ici_one
  statement: Ici (1 : α) = 1
  proof: rfl

@[to_additive]

中文:
定理 Ici_one
  结论: 左闭右无界区间 (1 : α) = 1
  证明: rfl

@[to_additive]
-/
theorem Ici_one : Ici (1 : α) = 1 :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction α (UpperSet α)
  body: SetLike.coe_injective.mulAction _ (fun _ _ => rfl)

@[to_additive]

中文:
实例 :
  签名: 乘法作用 α (上集 α)
  定义体: SetLike.coe_injective.mulAction _ (fun _ _ => rfl)

@[to_additive]

Depends on / 依赖: SetLike, SetLike.coe_injective.mulAction, coe_injective, mulAction
-/
instance : MulAction α (UpperSet α) :=
  SetLike.coe_injective.mulAction _ (fun _ _ => rfl)

@[to_additive]
/--
Instance `commSemigroup` / 实例 `commSemigroup`

English:
instance commSemigroup
  signature: : CommSemigroup (UpperSet α)
  body: { (SetLike.coe_injective.commSemigroup _ coe_mul : CommSemigroup (UpperSet α)) with }

@[to_additive]

中文:
实例 commSemigroup
  签名: : 交换半群 (上集 α)
  定义体: { (SetLike.coe_injective.commSemigroup _ coe_mul : CommSemigroup (UpperSet α)) with }

@[to_additive]

Depends on / 依赖: CommSemigroup, SetLike, SetLike.coe_injective.commSemigroup, UpperSet, coe_injective, coe_mul, commSemigroup
-/
instance commSemigroup : CommSemigroup (UpperSet α) :=
  { (SetLike.coe_injective.commSemigroup _ coe_mul : CommSemigroup (UpperSet α)) with }

@[to_additive]
/--
theorem `one_mul` / 定理 `one_mul`

English:
theorem one_mul
  given: (s : UpperSet α)
  statement: 1 * s = s
  proof: SetLike.coe_injective
(subset_mul_right _ self_mem_Ici).antisymm' by
      rw [← smul_eq_mul]; rw [← Set.iUnion_smul_set]
      exact Set.iUnion₂_subset fun _ => s.upper.smul_subset

@[to_additive]

中文:
定理 one_mul
  条件: (s : 上集 α)
  结论: 1 * s = s
  证明: SetLike.coe_injective
(subset_mul_right _ self_mem_Ici).antisymm' by
      rw [← smul_eq_mul]; rw [← Set.iUnion_smul_set]
      exact Set.iUnion₂_subset fun _ => s.upper.smul_subset

@[to_additive]
-/
private theorem one_mul (s : UpperSet α) : 1 * s = s :=
SetLike.coe_injective
(subset_mul_right _ self_mem_Ici).antisymm' by
      rw [← smul_eq_mul]; rw [← Set.iUnion_smul_set]
      exact Set.iUnion₂_subset fun _ => s.upper.smul_subset

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommMonoid (UpperSet α)
  body: { UpperSet.commSemigroup with
    one_mul := private one_mul
    mul_one := fun s => by
      rw [mul_comm]
      exact one_mul _ }

中文:
实例 :
  签名: 交换幺半群 (上集 α)
  定义体: { UpperSet.commSemigroup with
    one_mul := private one_mul
    mul_one := fun s => by
      rw [mul_comm]
      exact one_mul _ }

Depends on / 依赖: UpperSet, UpperSet.commSemigroup, commSemigroup, mul_comm, mul_one, one_mul, private
-/
instance : CommMonoid (UpperSet α) :=
  { UpperSet.commSemigroup with
    one_mul := private one_mul
    mul_one := fun s => by
      rw [mul_comm]
      exact one_mul _ }

end UpperSet

namespace LowerSet

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (LowerSet α)
  body: ⟨Iic 1⟩

@[to_additive]

中文:
实例 :
  签名: 幺 (下集 α)
  定义体: ⟨Iic 1⟩

@[to_additive]
-/
instance : One (LowerSet α) :=
  ⟨Iic 1⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (LowerSet α)
  body: ⟨fun s t => ⟨image2 (· * ·) s t, s.2.mul_right⟩⟩

@[to_additive]

中文:
实例 :
  签名: 乘法 (下集 α)
  定义体: ⟨fun s t => ⟨image2 (· * ·) s t, s.2.mul_right⟩⟩

@[to_additive]

Depends on / 依赖: image2, mul_right
-/
instance : Mul (LowerSet α) :=
  ⟨fun s t => ⟨image2 (· * ·) s t, s.2.mul_right⟩⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div (LowerSet α)
  body: ⟨fun s t => ⟨image2 (· / ·) s t, s.2.div_right⟩⟩

@[to_additive]

中文:
实例 :
  签名: 除法 (下集 α)
  定义体: ⟨fun s t => ⟨image2 (· / ·) s t, s.2.div_right⟩⟩

@[to_additive]

Depends on / 依赖: div_right, image2
-/
instance : Div (LowerSet α) :=
  ⟨fun s t => ⟨image2 (· / ·) s t, s.2.div_right⟩⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul α (LowerSet α)
  body: ⟨fun a s => ⟨(a • ·) '' s, s.2.smul⟩⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 :
  签名: 标量乘法 α (下集 α)
  定义体: ⟨fun a s => ⟨(a • ·) '' s, s.2.smul⟩⟩

@[to_additive (attr := simp, norm_cast)]
-/
instance : SMul α (LowerSet α) :=
  ⟨fun a s => ⟨(a • ·) '' s, s.2.smul⟩⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (s t : LowerSet α)
  statement: (↑(s * t) : Set α) = s * t
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_mul
  条件: (s t : 下集 α)
  结论: (↑(s * t) : 集合 α) = s * t
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_mul (s t : LowerSet α) : (↑(s * t) : Set α) = s * t :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: (s t : LowerSet α)
  statement: (↑(s / t) : Set α) = s / t
  proof: rfl

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp)]

中文:
定理 coe_div
  条件: (s t : 下集 α)
  结论: (↑(s / t) : 集合 α) = s / t
  证明: rfl

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp)]
-/
theorem coe_div (s t : LowerSet α) : (↑(s / t) : Set α) = s / t :=
  rfl

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp)]
/--
theorem `Iic_one` / 定理 `Iic_one`

English:
theorem Iic_one
  statement: Iic (1 : α) = 1
  proof: rfl

@[to_additive]

中文:
定理 Iic_one
  结论: 左无界右闭区间 (1 : α) = 1
  证明: rfl

@[to_additive]
-/
theorem Iic_one : Iic (1 : α) = 1 :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction α (LowerSet α)
  body: SetLike.coe_injective.mulAction _ (fun _ _ => rfl)

@[to_additive]

中文:
实例 :
  签名: 乘法作用 α (下集 α)
  定义体: SetLike.coe_injective.mulAction _ (fun _ _ => rfl)

@[to_additive]

Depends on / 依赖: SetLike, SetLike.coe_injective.mulAction, coe_injective, mulAction
-/
instance : MulAction α (LowerSet α) :=
  SetLike.coe_injective.mulAction _ (fun _ _ => rfl)

@[to_additive]
/--
Instance `commSemigroup` / 实例 `commSemigroup`

English:
instance commSemigroup
  signature: : CommSemigroup (LowerSet α)
  body: { (SetLike.coe_injective.commSemigroup _ coe_mul : CommSemigroup (LowerSet α)) with }

@[to_additive]

中文:
实例 commSemigroup
  签名: : 交换半群 (下集 α)
  定义体: { (SetLike.coe_injective.commSemigroup _ coe_mul : CommSemigroup (LowerSet α)) with }

@[to_additive]

Depends on / 依赖: CommSemigroup, LowerSet, SetLike, SetLike.coe_injective.commSemigroup, coe_injective, coe_mul, commSemigroup
-/
instance commSemigroup : CommSemigroup (LowerSet α) :=
  { (SetLike.coe_injective.commSemigroup _ coe_mul : CommSemigroup (LowerSet α)) with }

@[to_additive]
/--
theorem `one_mul` / 定理 `one_mul`

English:
theorem one_mul
  given: (s : LowerSet α)
  statement: 1 * s = s
  proof: SetLike.coe_injective
(subset_mul_right _ self_mem_Iic).antisymm' by
      rw [← smul_eq_mul]; rw [← Set.iUnion_smul_set]
      exact Set.iUnion₂_subset fun _ => s.lower.smul_subset

@[to_additive]

中文:
定理 one_mul
  条件: (s : 下集 α)
  结论: 1 * s = s
  证明: SetLike.coe_injective
(subset_mul_right _ self_mem_Iic).antisymm' by
      rw [← smul_eq_mul]; rw [← Set.iUnion_smul_set]
      exact Set.iUnion₂_subset fun _ => s.lower.smul_subset

@[to_additive]
-/
private theorem one_mul (s : LowerSet α) : 1 * s = s :=
SetLike.coe_injective
(subset_mul_right _ self_mem_Iic).antisymm' by
      rw [← smul_eq_mul]; rw [← Set.iUnion_smul_set]
      exact Set.iUnion₂_subset fun _ => s.lower.smul_subset

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommMonoid (LowerSet α)
  body: { LowerSet.commSemigroup with
    one_mul := private one_mul
    mul_one := fun s => by
      rw [mul_comm]
      exact one_mul _ }

中文:
实例 :
  签名: 交换幺半群 (下集 α)
  定义体: { LowerSet.commSemigroup with
    one_mul := private one_mul
    mul_one := fun s => by
      rw [mul_comm]
      exact one_mul _ }

Depends on / 依赖: LowerSet, LowerSet.commSemigroup, commSemigroup, mul_comm, mul_one, one_mul, private
-/
instance : CommMonoid (LowerSet α) :=
  { LowerSet.commSemigroup with
    one_mul := private one_mul
    mul_one := fun s => by
      rw [mul_comm]
      exact one_mul _ }

end LowerSet

variable (a s t)

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp)]
/--
theorem `upperClosure_one` / 定理 `upperClosure_one`

English:
theorem upperClosure_one
  statement: upperClosure (1 : Set α) = 1
  proof: upperClosure_singleton _

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp)]

中文:
定理 upperClosure_one
  结论: upperClosure (1 : 集合 α) = 1
  证明: upperClosure_singleton _

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp)]

Depends on / 依赖: upperClosure_singleton
-/
theorem upperClosure_one : upperClosure (1 : Set α) = 1 :=
  upperClosure_singleton _

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp)]
/--
theorem `lowerClosure_one` / 定理 `lowerClosure_one`

English:
theorem lowerClosure_one
  statement: lowerClosure (1 : Set α) = 1
  proof: lowerClosure_singleton _

@[to_additive (attr := simp)]

中文:
定理 lowerClosure_one
  结论: lowerClosure (1 : 集合 α) = 1
  证明: lowerClosure_singleton _

@[to_additive (attr := simp)]

Depends on / 依赖: lowerClosure_singleton
-/
theorem lowerClosure_one : lowerClosure (1 : Set α) = 1 :=
  lowerClosure_singleton _

@[to_additive (attr := simp)]
/--
theorem `upperClosure_smul` / 定理 `upperClosure_smul`

English:
theorem upperClosure_smul
  statement: upperClosure (a • s) = a • upperClosure s
  proof: upperClosure_image OrderIso.mulLeft a

@[to_additive (attr := simp)]

中文:
定理 upperClosure_smul
  结论: upperClosure (a • s) = a • upperClosure s
  证明: upperClosure_image OrderIso.mulLeft a

@[to_additive (attr := simp)]

Depends on / 依赖: OrderIso, OrderIso.mulLeft, mulLeft, upperClosure_image
-/
theorem upperClosure_smul : upperClosure (a • s) = a • upperClosure s :=
upperClosure_image OrderIso.mulLeft a

@[to_additive (attr := simp)]
/--
theorem `lowerClosure_smul` / 定理 `lowerClosure_smul`

English:
theorem lowerClosure_smul
  statement: lowerClosure (a • s) = a • lowerClosure s
  proof: lowerClosure_image OrderIso.mulLeft a

@[to_additive]

中文:
定理 lowerClosure_smul
  结论: lowerClosure (a • s) = a • lowerClosure s
  证明: lowerClosure_image OrderIso.mulLeft a

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.mulLeft, lowerClosure_image, mulLeft
-/
theorem lowerClosure_smul : lowerClosure (a • s) = a • lowerClosure s :=
lowerClosure_image OrderIso.mulLeft a

@[to_additive]
/--
theorem `mul_upperClosure` / 定理 `mul_upperClosure`

English:
theorem mul_upperClosure
  statement: s * upperClosure t = upperClosure (s * t)
  proof: by
  simp_rw [← smul_eq_mul, ← Set.iUnion_smul_set, upperClosure_iUnion, upperClosure_smul,
    UpperSet.coe_iInf₂]
  rfl

@[to_additive]

中文:
定理 mul_upperClosure
  结论: s * upperClosure t = upperClosure (s * t)
  证明: by
  simp_rw [← smul_eq_mul, ← Set.iUnion_smul_set, upperClosure_iUnion, upperClosure_smul,
    UpperSet.coe_iInf₂]
  rfl

@[to_additive]

Depends on / 依赖: Set.iUnion_smul_set, UpperSet, UpperSet.coe_iInf, iUnion_smul_set, simp_rw, smul_eq_mul, upperClosure_iUnion, upperClosure_smul
-/
theorem mul_upperClosure : s * upperClosure t = upperClosure (s * t) := by
  simp_rw [← smul_eq_mul, ← Set.iUnion_smul_set, upperClosure_iUnion, upperClosure_smul,
    UpperSet.coe_iInf₂]
  rfl

@[to_additive]
/--
theorem `mul_lowerClosure` / 定理 `mul_lowerClosure`

English:
theorem mul_lowerClosure
  statement: s * lowerClosure t = lowerClosure (s * t)
  proof: by
  simp_rw [← smul_eq_mul, ← Set.iUnion_smul_set, lowerClosure_iUnion, lowerClosure_smul,
    LowerSet.coe_iSup₂]
  rfl

@[to_additive]

中文:
定理 mul_lowerClosure
  结论: s * lowerClosure t = lowerClosure (s * t)
  证明: by
  simp_rw [← smul_eq_mul, ← Set.iUnion_smul_set, lowerClosure_iUnion, lowerClosure_smul,
    LowerSet.coe_iSup₂]
  rfl

@[to_additive]

Depends on / 依赖: LowerSet, LowerSet.coe_iSup, Set.iUnion_smul_set, iUnion_smul_set, lowerClosure_iUnion, lowerClosure_smul, simp_rw, smul_eq_mul
-/
theorem mul_lowerClosure : s * lowerClosure t = lowerClosure (s * t) := by
  simp_rw [← smul_eq_mul, ← Set.iUnion_smul_set, lowerClosure_iUnion, lowerClosure_smul,
    LowerSet.coe_iSup₂]
  rfl

@[to_additive]
/--
theorem `upperClosure_mul` / 定理 `upperClosure_mul`

English:
theorem upperClosure_mul
  statement: ↑(upperClosure s) * t = upperClosure (s * t)
  proof: by
  simp_rw [mul_comm _ t]
  exact mul_upperClosure _ _

@[to_additive]

中文:
定理 upperClosure_mul
  结论: ↑(upperClosure s) * t = upperClosure (s * t)
  证明: by
  simp_rw [mul_comm _ t]
  exact mul_upperClosure _ _

@[to_additive]

Depends on / 依赖: mul_comm, mul_upperClosure, simp_rw
-/
theorem upperClosure_mul : ↑(upperClosure s) * t = upperClosure (s * t) := by
  simp_rw [mul_comm _ t]
  exact mul_upperClosure _ _

@[to_additive]
/--
theorem `lowerClosure_mul` / 定理 `lowerClosure_mul`

English:
theorem lowerClosure_mul
  statement: ↑(lowerClosure s) * t = lowerClosure (s * t)
  proof: by
  simp_rw [mul_comm _ t]
  exact mul_lowerClosure _ _

@[to_additive (attr := simp)]

中文:
定理 lowerClosure_mul
  结论: ↑(lowerClosure s) * t = lowerClosure (s * t)
  证明: by
  simp_rw [mul_comm _ t]
  exact mul_lowerClosure _ _

@[to_additive (attr := simp)]

Depends on / 依赖: mul_comm, mul_lowerClosure, simp_rw
-/
theorem lowerClosure_mul : ↑(lowerClosure s) * t = lowerClosure (s * t) := by
  simp_rw [mul_comm _ t]
  exact mul_lowerClosure _ _

@[to_additive (attr := simp)]
/--
theorem `upperClosure_mul_distrib` / 定理 `upperClosure_mul_distrib`

English:
theorem upperClosure_mul_distrib
  statement: upperClosure (s * t) = upperClosure s * upperClosure t
  proof: SetLike.coe_injective by
    rw [UpperSet.coe_mul]; rw [mul_upperClosure]; rw [upperClosure_mul]; rw [UpperSet.upperClosure]

@[to_additive (attr := simp)]

中文:
定理 upperClosure_mul_distrib
  结论: upperClosure (s * t) = upperClosure s * upperClosure t
  证明: SetLike.coe_injective by
    rw [UpperSet.coe_mul]; rw [mul_upperClosure]; rw [upperClosure_mul]; rw [UpperSet.upperClosure]

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.coe_injective, UpperSet, UpperSet.coe_mul, UpperSet.upperClosure, coe_injective, coe_mul, mul_upperClosure, upperClosure, upperClosure_mul
-/
theorem upperClosure_mul_distrib : upperClosure (s * t) = upperClosure s * upperClosure t :=
SetLike.coe_injective by
    rw [UpperSet.coe_mul]; rw [mul_upperClosure]; rw [upperClosure_mul]; rw [UpperSet.upperClosure]

@[to_additive (attr := simp)]
/--
theorem `lowerClosure_mul_distrib` / 定理 `lowerClosure_mul_distrib`

English:
theorem lowerClosure_mul_distrib
  statement: lowerClosure (s * t) = lowerClosure s * lowerClosure t
  proof: SetLike.coe_injective by
    rw [LowerSet.coe_mul]; rw [mul_lowerClosure]; rw [lowerClosure_mul]; rw [LowerSet.lowerClosure]

中文:
定理 lowerClosure_mul_distrib
  结论: lowerClosure (s * t) = lowerClosure s * lowerClosure t
  证明: SetLike.coe_injective by
    rw [LowerSet.coe_mul]; rw [mul_lowerClosure]; rw [lowerClosure_mul]; rw [LowerSet.lowerClosure]

Depends on / 依赖: LowerSet, LowerSet.coe_mul, LowerSet.lowerClosure, SetLike, SetLike.coe_injective, coe_injective, coe_mul, lowerClosure, lowerClosure_mul, mul_lowerClosure
-/
theorem lowerClosure_mul_distrib : lowerClosure (s * t) = lowerClosure s * lowerClosure t :=
SetLike.coe_injective by
    rw [LowerSet.coe_mul]; rw [mul_lowerClosure]; rw [lowerClosure_mul]; rw [LowerSet.lowerClosure]

end OrderedCommGroup
