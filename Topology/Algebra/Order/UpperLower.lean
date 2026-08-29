/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.UpperLower
public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Topological facts about upper/lower/order-connected sets

The topological closure and interior of an upper/lower/order-connected set is an
upper/lower/order-connected set (with the notable exception of the closure of an order-connected
set).

## Implementation notes

The same lemmas are true in the additive/multiplicative worlds. To avoid code duplication, we
provide `HasUpperLowerClosure`, an ad hoc axiomatisation of the properties we need.
-/

public section


open Function Set

open scoped Pointwise

/--
Definition of `HasUpperLowerClosure` / `HasUpperLowerClosure` 的定义

English:
class HasUpperLowerClosure
  parameters: (α : Type*) [TopologicalSpace α] [Preorder α]
  axioms and operations (4):
    - isUpperSet_closure : forall s : Set α, IsUpperSet s -> IsUpperSet (closure s)
    - isLowerSet_closure : forall s : Set α, IsLowerSet s -> IsLowerSet (closure s)
    - isOpen_upperClosure : forall s : Set α, IsOpen s -> IsOpen (upperClosure s : Set α)
    - isOpen_lowerClosure : forall s : Set α, IsOpen s -> IsOpen (lowerClosure s : Set α)

中文:
类 有UpperLowerClosure
  参数: (α : 类型) [拓扑空间 α] [预序 α]
  公理与运算 (4 个):
    - isUpperSet_closure : 对任意 s : 集合 α, 是上集 s -> 是上集 (closure s)
    - isLowerSet_closure : 对任意 s : 集合 α, 是下集 s -> 是下集 (closure s)
    - isOpen_upperClosure : 对任意 s : 集合 α, 是开集 s -> 是开集 (upperClosure s : 集合 α)
    - isOpen_lowerClosure : 对任意 s : 集合 α, 是开集 s -> 是开集 (lowerClosure s : 集合 α)
-/
class HasUpperLowerClosure (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  isUpperSet_closure : forall s : Set α, IsUpperSet s -> IsUpperSet (closure s)
  isLowerSet_closure : forall s : Set α, IsLowerSet s -> IsLowerSet (closure s)
  isOpen_upperClosure : forall s : Set α, IsOpen s -> IsOpen (upperClosure s : Set α)
  isOpen_lowerClosure : forall s : Set α, IsOpen s -> IsOpen (lowerClosure s : Set α)

variable {α : Type*} [TopologicalSpace α]

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) IsOrderedMonoid.to_hasUpperLowerClosure
    [CommGroup α] [Preorder α] [IsOrderedMonoid α]
    [ContinuousConstSMul α α] : HasUpperLowerClosure α where
  isUpperSet_closure s h x y hxy hx :=
closure_mono (h.smul_subset <| one_le_div'.2 hxy) by
      rw [closure_smul]
      exact ⟨x, hx, div_mul_cancel _ _⟩
  isLowerSet_closure s h x y hxy hx :=
closure_mono (h.smul_subset <| div_le_one'.2 hxy) by
      rw [closure_smul]
      exact ⟨x, hx, div_mul_cancel _ _⟩
  isOpen_upperClosure s hs := by
    rw [← mul_one s]; rw [← mul_upperClosure]
    exact hs.mul_right
  isOpen_lowerClosure s hs := by
    rw [← mul_one s]; rw [← mul_lowerClosure]
    exact hs.mul_right

variable [Preorder α] [HasUpperLowerClosure α] {s : Set α}

/--
theorem `IsUpperSet.closure` / 定理 `IsUpperSet.closure`

English:
theorem IsUpperSet.closure
  statement: IsUpperSet s -> IsUpperSet (closure s)
  proof: HasUpperLowerClosure.isUpperSet_closure _

中文:
定理 是上集.closure
  结论: 是上集 s -> 是上集 (closure s)
  证明: HasUpperLowerClosure.isUpperSet_closure _
-/
protected theorem IsUpperSet.closure : IsUpperSet s -> IsUpperSet (closure s) :=
  HasUpperLowerClosure.isUpperSet_closure _

/--
theorem `IsLowerSet.closure` / 定理 `IsLowerSet.closure`

English:
theorem IsLowerSet.closure
  statement: IsLowerSet s -> IsLowerSet (closure s)
  proof: HasUpperLowerClosure.isLowerSet_closure _

中文:
定理 是下集.closure
  结论: 是下集 s -> 是下集 (closure s)
  证明: HasUpperLowerClosure.isLowerSet_closure _
-/
protected theorem IsLowerSet.closure : IsLowerSet s -> IsLowerSet (closure s) :=
  HasUpperLowerClosure.isLowerSet_closure _

/--
theorem `IsOpen.upperClosure` / 定理 `IsOpen.upperClosure`

English:
theorem IsOpen.upperClosure
  statement: IsOpen s -> IsOpen (upperClosure s : Set α)
  proof: HasUpperLowerClosure.isOpen_upperClosure _

中文:
定理 是开集.upperClosure
  结论: 是开集 s -> 是开集 (upperClosure s : 集合 α)
  证明: HasUpperLowerClosure.isOpen_upperClosure _
-/
protected theorem IsOpen.upperClosure : IsOpen s -> IsOpen (upperClosure s : Set α) :=
  HasUpperLowerClosure.isOpen_upperClosure _

/--
theorem `IsOpen.lowerClosure` / 定理 `IsOpen.lowerClosure`

English:
theorem IsOpen.lowerClosure
  statement: IsOpen s -> IsOpen (lowerClosure s : Set α)
  proof: HasUpperLowerClosure.isOpen_lowerClosure _

中文:
定理 是开集.lowerClosure
  结论: 是开集 s -> 是开集 (lowerClosure s : 集合 α)
  证明: HasUpperLowerClosure.isOpen_lowerClosure _
-/
protected theorem IsOpen.lowerClosure : IsOpen s -> IsOpen (lowerClosure s : Set α) :=
  HasUpperLowerClosure.isOpen_lowerClosure _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasUpperLowerClosure αᵒᵈ
  body: @IsLowerSet.closure α _ _ _
  isLowerSet_closure := @IsUpperSet.closure α _ _ _
  isOpen_upperClosure := @IsOpen.lowerClosure α _ _ _
  isOpen_lowerClosure := @IsOpen.upperClosure α _ _ _

中文:
实例 :
  签名: 有UpperLowerClosure αᵒᵈ
  定义体: @IsLowerSet.closure α _ _ _
  isLowerSet_closure := @IsUpperSet.closure α _ _ _
  isOpen_upperClosure := @IsOpen.lowerClosure α _ _ _
  isOpen_lowerClosure := @IsOpen.upperClosure α _ _ _

Depends on / 依赖: IsLowerSet, IsLowerSet.closure, closure
-/
instance : HasUpperLowerClosure αᵒᵈ where
  isUpperSet_closure := @IsLowerSet.closure α _ _ _
  isLowerSet_closure := @IsUpperSet.closure α _ _ _
  isOpen_upperClosure := @IsOpen.lowerClosure α _ _ _
  isOpen_lowerClosure := @IsOpen.upperClosure α _ _ _

/--
theorem `IsUpperSet.interior` / 定理 `IsUpperSet.interior`

English:
theorem IsUpperSet.interior
  given: (h : IsUpperSet s)
  statement: IsUpperSet (interior s)
  proof: by
  rw [← isLowerSet_compl]; rw [← closure_compl]
  exact h.compl.closure

中文:
定理 是上集.interior
  条件: (h : 是上集 s)
  结论: 是上集 (interior s)
  证明: by
  rw [← isLowerSet_compl]; rw [← closure_compl]
  exact h.compl.closure
-/
protected theorem IsUpperSet.interior (h : IsUpperSet s) : IsUpperSet (interior s) := by
  rw [← isLowerSet_compl]; rw [← closure_compl]
  exact h.compl.closure

/--
theorem `IsLowerSet.interior` / 定理 `IsLowerSet.interior`

English:
theorem IsLowerSet.interior
  given: (h : IsLowerSet s)
  statement: IsLowerSet (interior s)
  proof: h.toDual.interior

中文:
定理 是下集.interior
  条件: (h : 是下集 s)
  结论: 是下集 (interior s)
  证明: h.toDual.interior
-/
protected theorem IsLowerSet.interior (h : IsLowerSet s) : IsLowerSet (interior s) :=
  h.toDual.interior

/--
theorem `Set.OrdConnected.interior` / 定理 `Set.OrdConnected.interior`

English:
theorem Set.OrdConnected.interior
  given: (h : s.OrdConnected)
  statement: (interior s).OrdConnected
  proof: by
  rw [← h.upperClosure_inter_lowerClosure]; rw [interior_inter]
  exact
    (upperClosure s).upper.interior.ordConnected.inter (lowerClosure s).lower.interior.ordConnected

中文:
定理 集合.序连通.interior
  条件: (h : s.序连通)
  结论: (interior s).序连通
  证明: by
  rw [← h.upperClosure_inter_lowerClosure]; rw [interior_inter]
  exact
    (upperClosure s).upper.interior.ordConnected.inter (lowerClosure s).lower.interior.ordConnected
-/
protected theorem Set.OrdConnected.interior (h : s.OrdConnected) : (interior s).OrdConnected := by
  rw [← h.upperClosure_inter_lowerClosure]; rw [interior_inter]
  exact
    (upperClosure s).upper.interior.ordConnected.inter (lowerClosure s).lower.interior.ordConnected
