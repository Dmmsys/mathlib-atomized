/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod

/-!
# Products of `OrderedSub` types.
-/

public section

assert_not_exists MonoidWithZero

variable {α β : Type*}

/--
Instance `Prod.orderedSub` / 实例 `Prod.orderedSub`

English:
instance Prod.orderedSub
  body: ⟨fun w => ⟨tsub_le_iff_right.mp w.1, tsub_le_iff_right.mp w.2⟩,
   fun w => ⟨tsub_le_iff_right.mpr w.1, tsub_le_iff_right.mpr w.2⟩⟩

中文:
实例 Prod.orderedSub
  定义体: ⟨fun w => ⟨tsub_le_iff_right.mp w.1, tsub_le_iff_right.mp w.2⟩,
   fun w => ⟨tsub_le_iff_right.mpr w.1, tsub_le_iff_right.mpr w.2⟩⟩

Depends on / 依赖: tsub_le_iff_right, tsub_le_iff_right.mp, tsub_le_iff_right.mpr
-/
instance Prod.orderedSub
    [Preorder α] [Add α] [Sub α] [OrderedSub α] [Sub β] [Preorder β] [Add β] [OrderedSub β] :
    OrderedSub (α × β) where
  tsub_le_iff_right _ _ _ :=
  ⟨fun w => ⟨tsub_le_iff_right.mp w.1, tsub_le_iff_right.mp w.2⟩,
   fun w => ⟨tsub_le_iff_right.mpr w.1, tsub_le_iff_right.mpr w.2⟩⟩

/--
Instance `Pi.orderedSub` / 实例 `Pi.orderedSub`

English:
instance Pi.orderedSub
  signature: {ι : Type*} {α : ι -> Type*}
  body: ⟨fun w i => tsub_le_iff_right.mp (w i), fun w i => tsub_le_iff_right.mpr (w i)⟩

中文:
实例 Pi.orderedSub
  签名: {ι : 类型} {α : ι -> 类型}
  定义体: ⟨fun w i => tsub_le_iff_right.mp (w i), fun w i => tsub_le_iff_right.mpr (w i)⟩

Depends on / 依赖: tsub_le_iff_right, tsub_le_iff_right.mp, tsub_le_iff_right.mpr
-/
instance Pi.orderedSub {ι : Type*} {α : ι -> Type*}
    [forall i, Preorder (α i)] [forall i, Add (α i)] [forall i, Sub (α i)] [forall i, OrderedSub (α i)] :
    OrderedSub ((i : ι) -> α i) where
  tsub_le_iff_right _ _ _ :=
  ⟨fun w i => tsub_le_iff_right.mp (w i), fun w i => tsub_le_iff_right.mpr (w i)⟩
