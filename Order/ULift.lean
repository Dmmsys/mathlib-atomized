/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Logic.Function.ULift
public import Mathlib.Order.Basic

/-! # Ordered structures on `ULift.{v} α`

Once these basic instances are setup, the instances of more complex typeclasses should live next to
the corresponding `Prod` instances.
-/

public section

namespace ULift

open Batteries

universe v u

variable {α : Type u}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LE
  signature: α] : LE (ULift.{v} α) where le x y
  body: x.down <= y.down

中文:
实例 [LE
  签名: α] : LE (ULift.{v} α) where le x y
  定义体: x.down <= y.down

Depends on / 依赖: x.down, y.down
-/
instance [LE α] : LE (ULift.{v} α) where le x y := x.down <= y.down

/--
theorem `up_le` / 定理 `up_le`

English:
theorem up_le
  given: [LE α] {a b : α}
  statement: up a <= up b ↔ a <= b
  proof: Iff.rfl

中文:
定理 up_le
  条件: [LE α] {a b : α}
  结论: up a <= up b ↔ a <= b
  证明: Iff.rfl
-/
@[simp, to_dual self] theorem up_le [LE α] {a b : α} : up a <= up b ↔ a <= b := Iff.rfl
/--
theorem `down_le` / 定理 `down_le`

English:
theorem down_le
  given: [LE α] {a b : ULift α}
  statement: down a <= down b ↔ a <= b
  proof: Iff.rfl

中文:
定理 down_le
  条件: [LE α] {a b : ULift α}
  结论: down a <= down b ↔ a <= b
  证明: Iff.rfl
-/
@[simp, to_dual self] theorem down_le [LE α] {a b : ULift α} : down a <= down b ↔ a <= b := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: α] : LT (ULift.{v} α) where lt x y
  body: x.down < y.down

中文:
实例 [LT
  签名: α] : LT (ULift.{v} α) where lt x y
  定义体: x.down < y.down

Depends on / 依赖: x.down, y.down
-/
instance [LT α] : LT (ULift.{v} α) where lt x y := x.down < y.down

/--
theorem `up_lt` / 定理 `up_lt`

English:
theorem up_lt
  given: [LT α] {a b : α}
  statement: up a < up b ↔ a < b
  proof: Iff.rfl

中文:
定理 up_lt
  条件: [LT α] {a b : α}
  结论: up a < up b ↔ a < b
  证明: Iff.rfl
-/
@[simp, to_dual self] theorem up_lt [LT α] {a b : α} : up a < up b ↔ a < b := Iff.rfl
/--
theorem `down_lt` / 定理 `down_lt`

English:
theorem down_lt
  given: [LT α] {a b : ULift α}
  statement: down a < down b ↔ a < b
  proof: Iff.rfl

中文:
定理 down_lt
  条件: [LT α] {a b : ULift α}
  结论: down a < down b ↔ a < b
  证明: Iff.rfl
-/
@[simp, to_dual self] theorem down_lt [LT α] {a b : ULift α} : down a < down b ↔ a < b := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [BEq
  signature: α] : BEq (ULift.{v} α) where beq x y
  body: x.down == y.down

中文:
实例 [BEq
  签名: α] : BEq (ULift.{v} α) where beq x y
  定义体: x.down == y.down

Depends on / 依赖: x.down, y.down
-/
instance [BEq α] : BEq (ULift.{v} α) where beq x y := x.down == y.down

/--
theorem `up_beq` / 定理 `up_beq`

English:
theorem up_beq
  given: [BEq α] (a b : α)
  statement: (up a == up b) = (a == b)
  proof: rfl

中文:
定理 up_beq
  条件: [BEq α] (a b : α)
  结论: (up a == up b) = (a == b)
  证明: rfl
-/
@[simp] theorem up_beq [BEq α] (a b : α) : (up a == up b) = (a == b) := rfl
/--
theorem `down_beq` / 定理 `down_beq`

English:
theorem down_beq
  given: [BEq α] (a b : ULift α)
  statement: (down a == down b) = (a == b)
  proof: rfl

中文:
定理 down_beq
  条件: [BEq α] (a b : ULift α)
  结论: (down a == down b) = (a == b)
  证明: rfl
-/
@[simp] theorem down_beq [BEq α] (a b : ULift α) : (down a == down b) = (a == b) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ord
  signature: α] : Ord (ULift.{v} α) where compare x y
  body: compare x.down y.down

中文:
实例 [Ord
  签名: α] : Ord (ULift.{v} α) where compare x y
  定义体: compare x.down y.down

Depends on / 依赖: compare, x.down, y.down
-/
instance [Ord α] : Ord (ULift.{v} α) where compare x y := compare x.down y.down

/--
theorem `up_compare` / 定理 `up_compare`

English:
theorem up_compare
  given: [Ord α] (a b : α)
  statement: compare (up a) (up b) = compare a b
  proof: rfl

中文:
定理 up_compare
  条件: [Ord α] (a b : α)
  结论: compare (up a) (up b) = compare a b
  证明: rfl
-/
@[simp] theorem up_compare [Ord α] (a b : α) : compare (up a) (up b) = compare a b := rfl
/--
theorem `down_compare` / 定理 `down_compare`

English:
theorem down_compare
  given: [Ord α] (a b : ULift α)
  statement: compare (down a) (down b) = compare a b
  proof: rfl

@[to_dual]

中文:
定理 down_compare
  条件: [Ord α] (a b : ULift α)
  结论: compare (down a) (down b) = compare a b
  证明: rfl

@[to_dual]
-/
@[simp] theorem down_compare [Ord α] (a b : ULift α) : compare (down a) (down b) = compare a b :=
  rfl

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Max
  signature: α] : Max (ULift.{v} α) where max x y
  body: up x.down ⊔ y.down

@[to_dual (attr := simp)]

中文:
实例 [Max
  签名: α] : Max (ULift.{v} α) where max x y
  定义体: up x.down ⊔ y.down

@[to_dual (attr := simp)]

Depends on / 依赖: x.down, y.down
-/
instance [Max α] : Max (ULift.{v} α) where max x y := up x.down ⊔ y.down

@[to_dual (attr := simp)]
/--
theorem `up_sup` / 定理 `up_sup`

English:
theorem up_sup
  given: [Max α] (a b : α)
  statement: up (a ⊔ b) = up a ⊔ up b
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 up_sup
  条件: [Max α] (a b : α)
  结论: up (a ⊔ b) = up a ⊔ up b
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem up_sup [Max α] (a b : α) : up (a ⊔ b) = up a ⊔ up b := rfl

@[to_dual (attr := simp)]
/--
theorem `down_sup` / 定理 `down_sup`

English:
theorem down_sup
  given: [Max α] (a b : ULift α)
  statement: down (a ⊔ b) = down a ⊔ down b
  proof: rfl

中文:
定理 down_sup
  条件: [Max α] (a b : ULift α)
  结论: down (a ⊔ b) = down a ⊔ down b
  证明: rfl
-/
theorem down_sup [Max α] (a b : ULift α) : down (a ⊔ b) = down a ⊔ down b := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SDiff
  signature: α] : SDiff (ULift.{v} α) where sdiff x y
  body: up x.down \ y.down

中文:
实例 [SDiff
  签名: α] : SDiff (ULift.{v} α) where sdiff x y
  定义体: up x.down \ y.down

Depends on / 依赖: x.down, y.down
-/
instance [SDiff α] : SDiff (ULift.{v} α) where sdiff x y := up x.down \ y.down

/--
theorem `up_sdiff` / 定理 `up_sdiff`

English:
theorem up_sdiff
  given: [SDiff α] (a b : α)
  statement: up (a \ b) = up a \ up b
  proof: rfl

中文:
定理 up_sdiff
  条件: [SDiff α] (a b : α)
  结论: up (a \ b) = up a \ up b
  证明: rfl
-/
@[simp] theorem up_sdiff [SDiff α] (a b : α) : up (a \ b) = up a \ up b := rfl
/--
theorem `down_sdiff` / 定理 `down_sdiff`

English:
theorem down_sdiff
  given: [SDiff α] (a b : ULift α)
  statement: down (a \ b) = down a \ down b
  proof: rfl

中文:
定理 down_sdiff
  条件: [SDiff α] (a b : ULift α)
  结论: down (a \ b) = down a \ down b
  证明: rfl
-/
@[simp] theorem down_sdiff [SDiff α] (a b : ULift α) : down (a \ b) = down a \ down b := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Compl
  signature: α] : Compl (ULift.{v} α) where compl x
  body: up x.downᶜ

中文:
实例 [Compl
  签名: α] : Compl (ULift.{v} α) where compl x
  定义体: up x.downᶜ

Depends on / 依赖: x.down
-/
instance [Compl α] : Compl (ULift.{v} α) where compl x := up x.downᶜ

/--
theorem `up_compl` / 定理 `up_compl`

English:
theorem up_compl
  given: [Compl α] (a : α)
  statement: up (aᶜ) = (up a)ᶜ
  proof: rfl

中文:
定理 up_compl
  条件: [Compl α] (a : α)
  结论: up (aᶜ) = (up a)ᶜ
  证明: rfl
-/
@[simp] theorem up_compl [Compl α] (a : α) : up (aᶜ) = (up a)ᶜ := rfl
/--
theorem `down_compl` / 定理 `down_compl`

English:
theorem down_compl
  given: [Compl α] (a : ULift α)
  statement: down aᶜ = (down a)ᶜ
  proof: rfl

中文:
定理 down_compl
  条件: [Compl α] (a : ULift α)
  结论: down aᶜ = (down a)ᶜ
  证明: rfl
-/
@[simp] theorem down_compl [Compl α] (a : ULift α) : down aᶜ = (down a)ᶜ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ord
  signature: α] [inst
  body: inst.eq_swap

中文:
实例 [Ord
  签名: α] [inst
  定义体: inst.eq_swap

Depends on / 依赖: eq_swap, inst.eq_swap
-/
instance [Ord α] [inst : Std.OrientedOrd α] : Std.OrientedOrd (ULift.{v} α) where
  eq_swap := inst.eq_swap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ord
  signature: α] [inst
  body: inst.isLE_trans

中文:
实例 [Ord
  签名: α] [inst
  定义体: inst.isLE_trans

Depends on / 依赖: inst.isLE_trans, isLE_trans
-/
instance [Ord α] [inst : Std.TransOrd α] : Std.TransOrd (ULift.{v} α) where
  isLE_trans := inst.isLE_trans

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [BEq
  signature: α] [Ord α] [inst
  body: inst.compare_eq_iff_beq

中文:
实例 [BEq
  签名: α] [Ord α] [inst
  定义体: inst.compare_eq_iff_beq

Depends on / 依赖: compare_eq_iff_beq, inst.compare_eq_iff_beq
-/
instance [BEq α] [Ord α] [inst : Std.LawfulBEqOrd α] : Std.LawfulBEqOrd (ULift.{v} α) where
  compare_eq_iff_beq := inst.compare_eq_iff_beq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: α] [Ord α] [inst
  body: inst.eq_lt_iff_lt

中文:
实例 [LT
  签名: α] [Ord α] [inst
  定义体: inst.eq_lt_iff_lt

Depends on / 依赖: eq_lt_iff_lt, inst.eq_lt_iff_lt
-/
instance [LT α] [Ord α] [inst : Std.LawfulLTOrd α] : Std.LawfulLTOrd (ULift.{v} α) where
  eq_lt_iff_lt := inst.eq_lt_iff_lt

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LE
  signature: α] [Ord α] [inst
  body: inst.isLE_iff_le

中文:
实例 [LE
  签名: α] [Ord α] [inst
  定义体: inst.isLE_iff_le

Depends on / 依赖: inst.isLE_iff_le, isLE_iff_le
-/
instance [LE α] [Ord α] [inst : Std.LawfulLEOrd α] : Std.LawfulLEOrd (ULift.{v} α) where
  isLE_iff_le := inst.isLE_iff_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LE
  signature: α] [LT α] [BEq α] [Ord α] [inst
  body: inst.eq_lt_iff_lt
  isLE_iff_le := inst.isLE_iff_le

中文:
实例 [LE
  签名: α] [LT α] [BEq α] [Ord α] [inst
  定义体: inst.eq_lt_iff_lt
  isLE_iff_le := inst.isLE_iff_le

Depends on / 依赖: eq_lt_iff_lt, inst.eq_lt_iff_lt
-/
instance [LE α] [LT α] [BEq α] [Ord α] [inst : Std.LawfulBOrd α] :
    Std.LawfulBOrd (ULift.{v} α) where
  eq_lt_iff_lt := inst.eq_lt_iff_lt
  isLE_iff_le := inst.isLE_iff_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] : Preorder (ULift.{v} α)
  body: Preorder.lift ULift.down

中文:
实例 [Preorder
  签名: α] : Preorder (ULift.{v} α)
  定义体: Preorder.lift ULift.down
-/
instance [Preorder α] : Preorder (ULift.{v} α) :=
  Preorder.lift ULift.down

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: α] : PartialOrder (ULift.{v} α)
  body: PartialOrder.lift ULift.down ULift.down_injective

中文:
实例 [PartialOrder
  签名: α] : PartialOrder (ULift.{v} α)
  定义体: PartialOrder.lift ULift.down ULift.down_injective
-/
instance [PartialOrder α] : PartialOrder (ULift.{v} α) :=
  PartialOrder.lift ULift.down ULift.down_injective

end ULift
