/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Order.SuccPred.Limit
public import Mathlib.Order.SuccPred.WithBot

/-!
# Interaction between successors and arithmetic

We define the `SuccAddOrder` and `PredSubOrder` typeclasses, for orders satisfying `succ x = x + 1`
and `pred x = x - 1` respectively. This allows us to transfer the API for successors and
predecessors into these common arithmetical forms.
-/

public section

/--
Definition of `SuccAddOrder` / `SuccAddOrder` 的定义

English:
class SuccAddOrder
  parameters: (α : Type*) [Preorder α] [Add α] [One α]
  extends: SuccOrder α
  axioms and operations (1):
    - succ_eq_add_one((x : α)) : succ x = x + 1

中文:
类 SuccAddOrder
  参数: (α : 类型) [Preorder α] [Add α] [One α]
  继承: SuccOrder α
  公理与运算 (1 个):
    - succ_eq_add_one((x : α)) : succ x = x + 1
-/
class SuccAddOrder (α : Type*) [Preorder α] [Add α] [One α] extends SuccOrder α where
  succ_eq_add_one (x : α) : succ x = x + 1

/--
Definition of `PredSubOrder` / `PredSubOrder` 的定义

English:
class PredSubOrder
  parameters: (α : Type*) [Preorder α] [Sub α] [One α]
  extends: PredOrder α
  axioms and operations (1):
    - pred_eq_sub_one((x : α)) : pred x = x - 1

中文:
类 PredSubOrder
  参数: (α : 类型) [Preorder α] [Sub α] [One α]
  继承: PredOrder α
  公理与运算 (1 个):
    - pred_eq_sub_one((x : α)) : pred x = x - 1
-/
class PredSubOrder (α : Type*) [Preorder α] [Sub α] [One α] extends PredOrder α where
  pred_eq_sub_one (x : α) : pred x = x - 1

variable {α : Type*} {x y : α}

namespace Order

section Preorder

variable [Preorder α]

section Add

variable [Add α] [One α] [SuccAddOrder α]

@[simp]
/--
theorem `succ_eq_add_one` / 定理 `succ_eq_add_one`

English:
theorem succ_eq_add_one
  given: (x : α)
  statement: succ x = x + 1
  proof: SuccAddOrder.succ_eq_add_one x

中文:
定理 succ_eq_add_one
  条件: (x : α)
  结论: succ x = x + 1
  证明: SuccAddOrder.succ_eq_add_one x

Depends on / 依赖: SuccAddOrder, SuccAddOrder.succ_eq_add_one, succ_eq_add_one
-/
theorem succ_eq_add_one (x : α) : succ x = x + 1 :=
  SuccAddOrder.succ_eq_add_one x

/--
theorem `add_one_le_of_lt` / 定理 `add_one_le_of_lt`

English:
theorem add_one_le_of_lt
  given: (h : x < y)
  statement: x + 1 <= y
  proof: by
  rw [← succ_eq_add_one]
  exact succ_le_of_lt h

中文:
定理 add_one_le_of_lt
  条件: (h : x < y)
  结论: x + 1 <= y
  证明: by
  rw [← succ_eq_add_one]
  exact succ_le_of_lt h

Depends on / 依赖: succ_eq_add_one, succ_le_of_lt
-/
theorem add_one_le_of_lt (h : x < y) : x + 1 <= y := by
  rw [← succ_eq_add_one]
  exact succ_le_of_lt h

/--
theorem `add_one_le_iff_of_not_isMax` / 定理 `add_one_le_iff_of_not_isMax`

English:
theorem add_one_le_iff_of_not_isMax
  given: (hx : ¬ IsMax x)
  statement: x + 1 <= y ↔ x < y
  proof: by
  rw [← succ_eq_add_one]; rw [succ_le_iff_of_not_isMax hx]

中文:
定理 add_one_le_iff_of_not_isMax
  条件: (hx : ¬ IsMax x)
  结论: x + 1 <= y ↔ x < y
  证明: by
  rw [← succ_eq_add_one]; rw [succ_le_iff_of_not_isMax hx]

Depends on / 依赖: succ_eq_add_one, succ_le_iff_of_not_isMax
-/
theorem add_one_le_iff_of_not_isMax (hx : ¬ IsMax x) : x + 1 <= y ↔ x < y := by
  rw [← succ_eq_add_one]; rw [succ_le_iff_of_not_isMax hx]

/--
theorem `add_one_le_iff_of_not_isMax'` / 定理 `add_one_le_iff_of_not_isMax'`

English:
theorem add_one_le_iff_of_not_isMax'
  given: (hy : ¬ IsMax y)
  statement: x + 1 <= y ↔ x < y
  proof: by
  rw [← succ_eq_add_one]; rw [succ_le_iff_of_not_isMax' hy]

@[simp]

中文:
定理 add_one_le_iff_of_not_isMax'
  条件: (hy : ¬ IsMax y)
  结论: x + 1 <= y ↔ x < y
  证明: by
  rw [← succ_eq_add_one]; rw [succ_le_iff_of_not_isMax' hy]

@[simp]

Depends on / 依赖: succ_eq_add_one, succ_le_iff_of_not_isMax
-/
theorem add_one_le_iff_of_not_isMax' (hy : ¬ IsMax y) : x + 1 <= y ↔ x < y := by
  rw [← succ_eq_add_one]; rw [succ_le_iff_of_not_isMax' hy]

@[simp]
/--
theorem `add_one_le_iff` / 定理 `add_one_le_iff`

English:
theorem add_one_le_iff
  given: [NoMaxOrder α]
  statement: x + 1 <= y ↔ x < y
  proof: add_one_le_iff_of_not_isMax (not_isMax x)

@[simp]

中文:
定理 add_one_le_iff
  条件: [NoMaxOrder α]
  结论: x + 1 <= y ↔ x < y
  证明: add_one_le_iff_of_not_isMax (not_isMax x)

@[simp]

Depends on / 依赖: add_one_le_iff_of_not_isMax, not_isMax
-/
theorem add_one_le_iff [NoMaxOrder α] : x + 1 <= y ↔ x < y :=
  add_one_le_iff_of_not_isMax (not_isMax x)

@[simp]
/--
theorem `wcovBy_add_one` / 定理 `wcovBy_add_one`

English:
theorem wcovBy_add_one
  given: (x : α)
  statement: x ⩿ x + 1
  proof: by
  rw [← succ_eq_add_one]
  exact wcovBy_succ x

@[simp]

中文:
定理 wcovBy_add_one
  条件: (x : α)
  结论: x ⩿ x + 1
  证明: by
  rw [← succ_eq_add_one]
  exact wcovBy_succ x

@[simp]

Depends on / 依赖: succ_eq_add_one, wcovBy_succ
-/
theorem wcovBy_add_one (x : α) : x ⩿ x + 1 := by
  rw [← succ_eq_add_one]
  exact wcovBy_succ x

@[simp]
/--
theorem `covBy_add_one` / 定理 `covBy_add_one`

English:
theorem covBy_add_one
  given: [NoMaxOrder α] (x : α)
  statement: x ⋖ x + 1
  proof: by
  rw [← succ_eq_add_one]
  exact covBy_succ x

中文:
定理 covBy_add_one
  条件: [NoMaxOrder α] (x : α)
  结论: x ⋖ x + 1
  证明: by
  rw [← succ_eq_add_one]
  exact covBy_succ x

Depends on / 依赖: covBy_succ, succ_eq_add_one
-/
theorem covBy_add_one [NoMaxOrder α] (x : α) : x ⋖ x + 1 := by
  rw [← succ_eq_add_one]
  exact covBy_succ x

end Add

section Sub

variable [Sub α] [One α] [PredSubOrder α]

@[simp]
/--
theorem `pred_eq_sub_one` / 定理 `pred_eq_sub_one`

English:
theorem pred_eq_sub_one
  given: (x : α)
  statement: pred x = x - 1
  proof: PredSubOrder.pred_eq_sub_one x

中文:
定理 pred_eq_sub_one
  条件: (x : α)
  结论: pred x = x - 1
  证明: PredSubOrder.pred_eq_sub_one x

Depends on / 依赖: PredSubOrder, PredSubOrder.pred_eq_sub_one, pred_eq_sub_one
-/
theorem pred_eq_sub_one (x : α) : pred x = x - 1 :=
  PredSubOrder.pred_eq_sub_one x

/--
theorem `le_sub_one_of_lt` / 定理 `le_sub_one_of_lt`

English:
theorem le_sub_one_of_lt
  given: (h : x < y)
  statement: x <= y - 1
  proof: by
  rw [← pred_eq_sub_one]
  exact le_pred_of_lt h

中文:
定理 le_sub_one_of_lt
  条件: (h : x < y)
  结论: x <= y - 1
  证明: by
  rw [← pred_eq_sub_one]
  exact le_pred_of_lt h

Depends on / 依赖: le_pred_of_lt, pred_eq_sub_one
-/
theorem le_sub_one_of_lt (h : x < y) : x <= y - 1 := by
  rw [← pred_eq_sub_one]
  exact le_pred_of_lt h

/--
theorem `le_sub_one_iff_of_not_isMin` / 定理 `le_sub_one_iff_of_not_isMin`

English:
theorem le_sub_one_iff_of_not_isMin
  given: (hy : ¬ IsMin y)
  statement: x <= y - 1 ↔ x < y
  proof: by
  rw [← pred_eq_sub_one]; rw [le_pred_iff_of_not_isMin hy]

@[simp]

中文:
定理 le_sub_one_iff_of_not_isMin
  条件: (hy : ¬ IsMin y)
  结论: x <= y - 1 ↔ x < y
  证明: by
  rw [← pred_eq_sub_one]; rw [le_pred_iff_of_not_isMin hy]

@[simp]

Depends on / 依赖: le_pred_iff_of_not_isMin, pred_eq_sub_one
-/
theorem le_sub_one_iff_of_not_isMin (hy : ¬ IsMin y) : x <= y - 1 ↔ x < y := by
  rw [← pred_eq_sub_one]; rw [le_pred_iff_of_not_isMin hy]

@[simp]
/--
theorem `le_sub_one_iff` / 定理 `le_sub_one_iff`

English:
theorem le_sub_one_iff
  given: [NoMinOrder α]
  statement: x <= y - 1 ↔ x < y
  proof: le_sub_one_iff_of_not_isMin (not_isMin y)

@[simp]

中文:
定理 le_sub_one_iff
  条件: [NoMinOrder α]
  结论: x <= y - 1 ↔ x < y
  证明: le_sub_one_iff_of_not_isMin (not_isMin y)

@[simp]

Depends on / 依赖: le_sub_one_iff_of_not_isMin, not_isMin
-/
theorem le_sub_one_iff [NoMinOrder α] : x <= y - 1 ↔ x < y :=
  le_sub_one_iff_of_not_isMin (not_isMin y)

@[simp]
/--
theorem `sub_one_wcovBy` / 定理 `sub_one_wcovBy`

English:
theorem sub_one_wcovBy
  given: (x : α)
  statement: x - 1 ⩿ x
  proof: by
  rw [← pred_eq_sub_one]
  exact pred_wcovBy x

@[simp]

中文:
定理 sub_one_wcovBy
  条件: (x : α)
  结论: x - 1 ⩿ x
  证明: by
  rw [← pred_eq_sub_one]
  exact pred_wcovBy x

@[simp]

Depends on / 依赖: pred_eq_sub_one, pred_wcovBy
-/
theorem sub_one_wcovBy (x : α) : x - 1 ⩿ x := by
  rw [← pred_eq_sub_one]
  exact pred_wcovBy x

@[simp]
/--
theorem `sub_one_covBy` / 定理 `sub_one_covBy`

English:
theorem sub_one_covBy
  given: [NoMinOrder α] (x : α)
  statement: x - 1 ⋖ x
  proof: by
  rw [← pred_eq_sub_one]
  exact pred_covBy x

中文:
定理 sub_one_covBy
  条件: [NoMinOrder α] (x : α)
  结论: x - 1 ⋖ x
  证明: by
  rw [← pred_eq_sub_one]
  exact pred_covBy x

Depends on / 依赖: pred_covBy, pred_eq_sub_one
-/
theorem sub_one_covBy [NoMinOrder α] (x : α) : x - 1 ⋖ x := by
  rw [← pred_eq_sub_one]
  exact pred_covBy x

end Sub

@[simp]
/--
theorem `succ_iterate` / 定理 `succ_iterate`

English:
theorem succ_iterate
  given: [AddMonoidWithOne α] [SuccAddOrder α] (x : α) (n : Nat)
  proof: by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]; rw [Nat.cast_zero]; rw [add_zero]
  | succ n IH =>
    rw [Function.iterate_succ_apply']; rw [IH]; rw [Nat.cast_add]; rw [succ_eq_add_one]; rw [Nat.cast_one]; rw [add_assoc]

@[simp]

中文:
定理 succ_iterate
  条件: [AddMonoidWithOne α] [SuccAddOrder α] (x : α) (n : 自然数)
  证明: by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]; rw [Nat.cast_zero]; rw [add_zero]
  | succ n IH =>
    rw [Function.iterate_succ_apply']; rw [IH]; rw [Nat.cast_add]; rw [succ_eq_add_one]; rw [Nat.cast_one]; rw [add_assoc]

@[simp]

Depends on / 依赖: Function, Function.iterate_succ_apply, Function.iterate_zero_apply, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_assoc, add_zero, cast_add, cast_one, cast_zero, iterate_succ_apply, iterate_zero_apply, succ_eq_add_one
-/
theorem succ_iterate [AddMonoidWithOne α] [SuccAddOrder α] (x : α) (n : Nat) :
    succ^[n] x = x + n := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]; rw [Nat.cast_zero]; rw [add_zero]
  | succ n IH =>
    rw [Function.iterate_succ_apply']; rw [IH]; rw [Nat.cast_add]; rw [succ_eq_add_one]; rw [Nat.cast_one]; rw [add_assoc]

@[simp]
/--
theorem `pred_iterate` / 定理 `pred_iterate`

English:
theorem pred_iterate
  given: [AddCommGroupWithOne α] [PredSubOrder α] (x : α) (n : Nat)
  proof: by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]; rw [Nat.cast_zero]; rw [sub_zero]
  | succ n IH =>
    rw [Function.iterate_succ_apply']; rw [IH]; rw [Nat.cast_add]; rw [pred_eq_sub_one]; rw [Nat.cast_one]; rw [sub_sub]

中文:
定理 pred_iterate
  条件: [AddCommGroupWithOne α] [PredSubOrder α] (x : α) (n : 自然数)
  证明: by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]; rw [Nat.cast_zero]; rw [sub_zero]
  | succ n IH =>
    rw [Function.iterate_succ_apply']; rw [IH]; rw [Nat.cast_add]; rw [pred_eq_sub_one]; rw [Nat.cast_one]; rw [sub_sub]

Depends on / 依赖: Function, Function.iterate_succ_apply, Function.iterate_zero_apply, Nat.cast_add, Nat.cast_one, Nat.cast_zero, cast_add, cast_one, cast_zero, iterate_succ_apply, iterate_zero_apply, pred_eq_sub_one, sub_sub, sub_zero
-/
theorem pred_iterate [AddCommGroupWithOne α] [PredSubOrder α] (x : α) (n : Nat) :
    pred^[n] x = x - n := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]; rw [Nat.cast_zero]; rw [sub_zero]
  | succ n IH =>
    rw [Function.iterate_succ_apply']; rw [IH]; rw [Nat.cast_add]; rw [pred_eq_sub_one]; rw [Nat.cast_one]; rw [sub_sub]

end Preorder

section PartialOrder

variable [PartialOrder α]

/--
theorem `not_isMax_zero` / 定理 `not_isMax_zero`

English:
theorem not_isMax_zero
  given: [Zero α] [One α] [ZeroLEOneClass α] [NeZero (1 : α)]
  statement: ¬ IsMax (0 : α)
  proof: by
  rw [not_isMax_iff]
  exact ⟨1, one_pos⟩

中文:
定理 not_isMax_zero
  条件: [Zero α] [One α] [ZeroLEOneClass α] [NeZero (1 : α)]
  结论: ¬ IsMax (0 : α)
  证明: by
  rw [not_isMax_iff]
  exact ⟨1, one_pos⟩

Depends on / 依赖: not_isMax_iff, one_pos
-/
theorem not_isMax_zero [Zero α] [One α] [ZeroLEOneClass α] [NeZero (1 : α)] : ¬ IsMax (0 : α) := by
  rw [not_isMax_iff]
  exact ⟨1, one_pos⟩

/--
theorem `one_le_iff_pos` / 定理 `one_le_iff_pos`

English:
theorem one_le_iff_pos
  statement: [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)]
  proof: by
  rw [← succ_le_iff_of_not_isMax not_isMax_zero]; rw [succ_eq_add_one]; rw [zero_add]

中文:
定理 one_le_iff_pos
  结论: [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)]
  证明: by
  rw [← succ_le_iff_of_not_isMax not_isMax_zero]; rw [succ_eq_add_one]; rw [zero_add]

Depends on / 依赖: not_isMax_zero, succ_eq_add_one, succ_le_iff_of_not_isMax, zero_add
-/
theorem one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)]
    [SuccAddOrder α] : 1 <= x ↔ 0 < x := by
  rw [← succ_le_iff_of_not_isMax not_isMax_zero]; rw [succ_eq_add_one]; rw [zero_add]

/--
theorem `one_le_iff_ne_zero` / 定理 `one_le_iff_ne_zero`

English:
theorem one_le_iff_ne_zero
  statement: [AddMonoidWithOne α] [NeZero (1 : α)]
  proof: by
  rw [Order.one_le_iff_pos]; rw [pos_iff_ne_zero]

中文:
定理 one_le_iff_ne_zero
  结论: [AddMonoidWithOne α] [NeZero (1 : α)]
  证明: by
  rw [Order.one_le_iff_pos]; rw [pos_iff_ne_zero]

Depends on / 依赖: Order.one_le_iff_pos, one_le_iff_pos, pos_iff_ne_zero
-/
theorem one_le_iff_ne_zero [AddMonoidWithOne α] [NeZero (1 : α)]
    [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0 := by
  rw [Order.one_le_iff_pos]; rw [pos_iff_ne_zero]

/--
theorem `covBy_iff_add_one_eq` / 定理 `covBy_iff_add_one_eq`

English:
theorem covBy_iff_add_one_eq
  given: [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
  proof: by
  rw [← succ_eq_add_one]
  exact succ_eq_iff_covBy.symm

中文:
定理 covBy_iff_add_one_eq
  条件: [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
  证明: by
  rw [← succ_eq_add_one]
  exact succ_eq_iff_covBy.symm

Depends on / 依赖: succ_eq_add_one, succ_eq_iff_covBy, succ_eq_iff_covBy.symm
-/
theorem covBy_iff_add_one_eq [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] :
    x ⋖ y ↔ x + 1 = y := by
  rw [← succ_eq_add_one]
  exact succ_eq_iff_covBy.symm

/--
theorem `covBy_iff_sub_one_eq` / 定理 `covBy_iff_sub_one_eq`

English:
theorem covBy_iff_sub_one_eq
  given: [Sub α] [One α] [PredSubOrder α] [NoMinOrder α]
  proof: by
  rw [← pred_eq_sub_one]
  exact pred_eq_iff_covBy.symm

中文:
定理 covBy_iff_sub_one_eq
  条件: [Sub α] [One α] [PredSubOrder α] [NoMinOrder α]
  证明: by
  rw [← pred_eq_sub_one]
  exact pred_eq_iff_covBy.symm

Depends on / 依赖: pred_eq_iff_covBy, pred_eq_iff_covBy.symm, pred_eq_sub_one
-/
theorem covBy_iff_sub_one_eq [Sub α] [One α] [PredSubOrder α] [NoMinOrder α] :
    x ⋖ y ↔ y - 1 = x := by
  rw [← pred_eq_sub_one]
  exact pred_eq_iff_covBy.symm

/--
theorem `IsSuccPrelimit.add_one_lt` / 定理 `IsSuccPrelimit.add_one_lt`

English:
theorem IsSuccPrelimit.add_one_lt
  statement: [Add α] [One α] [SuccAddOrder α]
  proof: by
  rw [← succ_eq_add_one]
  exact hx.succ_lt hy

中文:
定理 IsSuccPrelimit.add_one_lt
  结论: [Add α] [One α] [SuccAddOrder α]
  证明: by
  rw [← succ_eq_add_one]
  exact hx.succ_lt hy

Depends on / 依赖: hx.succ_lt, succ_eq_add_one, succ_lt
-/
theorem IsSuccPrelimit.add_one_lt [Add α] [One α] [SuccAddOrder α]
    (hx : IsSuccPrelimit x) (hy : y < x) : y + 1 < x := by
  rw [← succ_eq_add_one]
  exact hx.succ_lt hy

/--
theorem `IsPredPrelimit.lt_sub_one` / 定理 `IsPredPrelimit.lt_sub_one`

English:
theorem IsPredPrelimit.lt_sub_one
  statement: [Sub α] [One α] [PredSubOrder α]
  proof: by
  rw [← pred_eq_sub_one]
  exact hx.lt_pred hy

中文:
定理 IsPredPrelimit.lt_sub_one
  结论: [Sub α] [One α] [PredSubOrder α]
  证明: by
  rw [← pred_eq_sub_one]
  exact hx.lt_pred hy

Depends on / 依赖: hx.lt_pred, lt_pred, pred_eq_sub_one
-/
theorem IsPredPrelimit.lt_sub_one [Sub α] [One α] [PredSubOrder α]
    (hx : IsPredPrelimit x) (hy : x < y) : x < y - 1 := by
  rw [← pred_eq_sub_one]
  exact hx.lt_pred hy

/--
theorem `IsSuccLimit.add_one_lt` / 定理 `IsSuccLimit.add_one_lt`

English:
theorem IsSuccLimit.add_one_lt
  statement: [Add α] [One α] [SuccAddOrder α]
  proof: hx.isSuccPrelimit.add_one_lt hy

中文:
定理 IsSuccLimit.add_one_lt
  结论: [Add α] [One α] [SuccAddOrder α]
  证明: hx.isSuccPrelimit.add_one_lt hy

Depends on / 依赖: add_one_lt, hx.isSuccPrelimit.add_one_lt, isSuccPrelimit
-/
theorem IsSuccLimit.add_one_lt [Add α] [One α] [SuccAddOrder α]
    (hx : IsSuccLimit x) (hy : y < x) : y + 1 < x :=
  hx.isSuccPrelimit.add_one_lt hy

/--
theorem `IsPredLimit.lt_sub_one` / 定理 `IsPredLimit.lt_sub_one`

English:
theorem IsPredLimit.lt_sub_one
  statement: [Sub α] [One α] [PredSubOrder α]
  proof: hx.isPredPrelimit.lt_sub_one hy

中文:
定理 IsPredLimit.lt_sub_one
  结论: [Sub α] [One α] [PredSubOrder α]
  证明: hx.isPredPrelimit.lt_sub_one hy

Depends on / 依赖: hx.isPredPrelimit.lt_sub_one, isPredPrelimit, lt_sub_one
-/
theorem IsPredLimit.lt_sub_one [Sub α] [One α] [PredSubOrder α]
    (hx : IsPredLimit x) (hy : x < y) : x < y - 1 :=
  hx.isPredPrelimit.lt_sub_one hy

/--
theorem `IsSuccPrelimit.add_natCast_lt` / 定理 `IsSuccPrelimit.add_natCast_lt`

English:
theorem IsSuccPrelimit.add_natCast_lt
  statement: [AddMonoidWithOne α] [SuccAddOrder α]

中文:
定理 IsSuccPrelimit.add_natCast_lt
  结论: [AddMonoidWithOne α] [SuccAddOrder α]
-/
theorem IsSuccPrelimit.add_natCast_lt [AddMonoidWithOne α] [SuccAddOrder α]
    (hx : IsSuccPrelimit x) (hy : y < x) : forall n : Nat, y + n < x
  | 0 => by simpa
  | n + 1 => by
    rw [Nat.cast_add_one]; rw [← add_assoc]
    exact hx.add_one_lt (hx.add_natCast_lt hy n)

/--
theorem `IsPredPrelimit.lt_sub_natCast` / 定理 `IsPredPrelimit.lt_sub_natCast`

English:
theorem IsPredPrelimit.lt_sub_natCast
  statement: [AddCommGroupWithOne α] [PredSubOrder α]

中文:
定理 IsPredPrelimit.lt_sub_natCast
  结论: [AddCommGroupWithOne α] [PredSubOrder α]
-/
theorem IsPredPrelimit.lt_sub_natCast [AddCommGroupWithOne α] [PredSubOrder α]
    (hx : IsPredPrelimit x) (hy : x < y) : forall n : Nat, x < y - n
  | 0 => by simpa
  | n + 1 => by
    rw [Nat.cast_add_one]; rw [← sub_sub]
    exact hx.lt_sub_one (hx.lt_sub_natCast hy n)

/--
theorem `IsSuccLimit.add_natCast_lt` / 定理 `IsSuccLimit.add_natCast_lt`

English:
theorem IsSuccLimit.add_natCast_lt
  statement: [AddMonoidWithOne α] [SuccAddOrder α]
  proof: hx.isSuccPrelimit.add_natCast_lt hy

中文:
定理 IsSuccLimit.add_natCast_lt
  结论: [AddMonoidWithOne α] [SuccAddOrder α]
  证明: hx.isSuccPrelimit.add_natCast_lt hy

Depends on / 依赖: add_natCast_lt, hx.isSuccPrelimit.add_natCast_lt, isSuccPrelimit
-/
theorem IsSuccLimit.add_natCast_lt [AddMonoidWithOne α] [SuccAddOrder α]
    (hx : IsSuccLimit x) (hy : y < x) : forall n : Nat, y + n < x :=
  hx.isSuccPrelimit.add_natCast_lt hy

/--
theorem `IsPredLimit.lt_sub_natCast` / 定理 `IsPredLimit.lt_sub_natCast`

English:
theorem IsPredLimit.lt_sub_natCast
  statement: [AddCommGroupWithOne α] [PredSubOrder α]
  proof: hx.isPredPrelimit.lt_sub_natCast hy

中文:
定理 IsPredLimit.lt_sub_natCast
  结论: [AddCommGroupWithOne α] [PredSubOrder α]
  证明: hx.isPredPrelimit.lt_sub_natCast hy

Depends on / 依赖: hx.isPredPrelimit.lt_sub_natCast, isPredPrelimit, lt_sub_natCast
-/
theorem IsPredLimit.lt_sub_natCast [AddCommGroupWithOne α] [PredSubOrder α]
    (hx : IsPredLimit x) (hy : x < y) : forall n : Nat, x < y - n :=
  hx.isPredPrelimit.lt_sub_natCast hy

/--
theorem `IsSuccLimit.natCast_lt` / 定理 `IsSuccLimit.natCast_lt`

English:
theorem IsSuccLimit.natCast_lt
  statement: [AddMonoidWithOne α] [SuccAddOrder α] [IsBotZeroClass α]
  proof: by
  simpa using hx.add_natCast_lt hx.pos

中文:
定理 IsSuccLimit.natCast_lt
  结论: [AddMonoidWithOne α] [SuccAddOrder α] [IsBotZeroClass α]
  证明: by
  simpa using hx.add_natCast_lt hx.pos

Depends on / 依赖: add_natCast_lt, hx.add_natCast_lt, hx.pos
-/
theorem IsSuccLimit.natCast_lt [AddMonoidWithOne α] [SuccAddOrder α] [IsBotZeroClass α]
    (hx : IsSuccLimit x) : forall n : Nat, n < x := by
  simpa using hx.add_natCast_lt hx.pos

/--
theorem `not_isSuccLimit_natCast` / 定理 `not_isSuccLimit_natCast`

English:
theorem not_isSuccLimit_natCast
  given: [AddMonoidWithOne α] [SuccAddOrder α] [IsBotZeroClass α] (n : Nat)
  proof: fun h => (h.natCast_lt n).false

@[simp]

中文:
定理 not_isSuccLimit_natCast
  条件: [AddMonoidWithOne α] [SuccAddOrder α] [IsBotZeroClass α] (n : 自然数)
  证明: fun h => (h.natCast_lt n).false

@[simp]

Depends on / 依赖: h.natCast_lt, natCast_lt
-/
theorem not_isSuccLimit_natCast [AddMonoidWithOne α] [SuccAddOrder α] [IsBotZeroClass α] (n : Nat) :
    ¬ IsSuccLimit (n : α) :=
  fun h => (h.natCast_lt n).false

@[simp]
/--
theorem `not_isSuccPrelimit_add_one` / 定理 `not_isSuccPrelimit_add_one`

English:
theorem not_isSuccPrelimit_add_one
  given: (a : α) [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
  proof: succ_eq_add_one a ▸ not_isSuccPrelimit_succ a

@[simp]

中文:
定理 not_isSuccPrelimit_add_one
  条件: (a : α) [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
  证明: succ_eq_add_one a ▸ not_isSuccPrelimit_succ a

@[simp]

Depends on / 依赖: not_isSuccPrelimit_succ, succ_eq_add_one
-/
theorem not_isSuccPrelimit_add_one (a : α) [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] :
    ¬ IsSuccPrelimit (a + 1) :=
  succ_eq_add_one a ▸ not_isSuccPrelimit_succ a

@[simp]
/--
theorem `not_isSuccLimit_add_one` / 定理 `not_isSuccLimit_add_one`

English:
theorem not_isSuccLimit_add_one
  given: (a : α) [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
  proof: succ_eq_add_one a ▸ not_isSuccLimit_succ a

@[simp]

中文:
定理 not_isSuccLimit_add_one
  条件: (a : α) [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
  证明: succ_eq_add_one a ▸ not_isSuccLimit_succ a

@[simp]

Depends on / 依赖: not_isSuccLimit_succ, succ_eq_add_one
-/
theorem not_isSuccLimit_add_one (a : α) [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] :
    ¬ IsSuccLimit (a + 1) :=
  succ_eq_add_one a ▸ not_isSuccLimit_succ a

@[simp]
/--
theorem `succ_eq_zero` / 定理 `succ_eq_zero`

English:
theorem succ_eq_zero
  statement: [AddZeroClass α] [OrderBot α] [IsBotZeroClass α] [One α] [NoMaxOrder α]
  proof: by
  cases a
  · simp [bot_eq_zero]
  · rename_i a
    simp only [WithBot.succ_coe, WithBot.coe_ne_bot, iff_false, succ_eq_add_one]
    by_contra h
    simpa [h] using max_of_succ_le (a := a)

中文:
定理 succ_eq_zero
  结论: [AddZeroClass α] [OrderBot α] [IsBotZeroClass α] [One α] [NoMaxOrder α]
  证明: by
  cases a
  · simp [bot_eq_zero]
  · rename_i a
    simp only [WithBot.succ_coe, WithBot.coe_ne_bot, iff_false, succ_eq_add_one]
    by_contra h
    simpa [h] using max_of_succ_le (a := a)

Depends on / 依赖: WithBot, WithBot.coe_ne_bot, WithBot.succ_coe, bot_eq_zero, coe_ne_bot, iff_false, max_of_succ_le, rename_i, succ_coe, succ_eq_add_one
-/
theorem succ_eq_zero [AddZeroClass α] [OrderBot α] [IsBotZeroClass α] [One α] [NoMaxOrder α]
    [SuccAddOrder α] {a : WithBot α} : WithBot.succ a = 0 ↔ a = ⊥ := by
  cases a
  · simp [bot_eq_zero]
  · rename_i a
    simp only [WithBot.succ_coe, WithBot.coe_ne_bot, iff_false, succ_eq_add_one]
    by_contra h
    simpa [h] using max_of_succ_le (a := a)

end PartialOrder

section LinearOrder

variable [LinearOrder α]

section Add

variable [Add α] [One α] [SuccAddOrder α]

/--
theorem `le_of_lt_add_one` / 定理 `le_of_lt_add_one`

English:
theorem le_of_lt_add_one
  given: (h : x < y + 1)
  statement: x <= y
  proof: by
  rw [← succ_eq_add_one] at h
  exact le_of_lt_succ h

中文:
定理 le_of_lt_add_one
  条件: (h : x < y + 1)
  结论: x <= y
  证明: by
  rw [← succ_eq_add_one] at h
  exact le_of_lt_succ h

Depends on / 依赖: le_of_lt_succ, succ_eq_add_one
-/
theorem le_of_lt_add_one (h : x < y + 1) : x <= y := by
  rw [← succ_eq_add_one] at h
  exact le_of_lt_succ h

/--
theorem `lt_add_one_iff_of_not_isMax` / 定理 `lt_add_one_iff_of_not_isMax`

English:
theorem lt_add_one_iff_of_not_isMax
  given: (hy : ¬ IsMax y)
  statement: x < y + 1 ↔ x <= y
  proof: by
  rw [← succ_eq_add_one]; rw [lt_succ_iff_of_not_isMax hy]

中文:
定理 lt_add_one_iff_of_not_isMax
  条件: (hy : ¬ IsMax y)
  结论: x < y + 1 ↔ x <= y
  证明: by
  rw [← succ_eq_add_one]; rw [lt_succ_iff_of_not_isMax hy]

Depends on / 依赖: lt_succ_iff_of_not_isMax, succ_eq_add_one
-/
theorem lt_add_one_iff_of_not_isMax (hy : ¬ IsMax y) : x < y + 1 ↔ x <= y := by
  rw [← succ_eq_add_one]; rw [lt_succ_iff_of_not_isMax hy]

/--
theorem `lt_add_one_iff_of_not_isMax'` / 定理 `lt_add_one_iff_of_not_isMax'`

English:
theorem lt_add_one_iff_of_not_isMax'
  given: (hx : ¬ IsMax x)
  statement: x < y + 1 ↔ x <= y
  proof: by
  rw [← succ_eq_add_one]; rw [lt_succ_iff_of_not_isMax' hx]

@[simp]

中文:
定理 lt_add_one_iff_of_not_isMax'
  条件: (hx : ¬ IsMax x)
  结论: x < y + 1 ↔ x <= y
  证明: by
  rw [← succ_eq_add_one]; rw [lt_succ_iff_of_not_isMax' hx]

@[simp]

Depends on / 依赖: lt_succ_iff_of_not_isMax, succ_eq_add_one
-/
theorem lt_add_one_iff_of_not_isMax' (hx : ¬ IsMax x) : x < y + 1 ↔ x <= y := by
  rw [← succ_eq_add_one]; rw [lt_succ_iff_of_not_isMax' hx]

@[simp]
/--
theorem `lt_add_one_iff` / 定理 `lt_add_one_iff`

English:
theorem lt_add_one_iff
  given: [NoMaxOrder α]
  statement: x < y + 1 ↔ x <= y
  proof: lt_add_one_iff_of_not_isMax (not_isMax y)

@[simp]

中文:
定理 lt_add_one_iff
  条件: [NoMaxOrder α]
  结论: x < y + 1 ↔ x <= y
  证明: lt_add_one_iff_of_not_isMax (not_isMax y)

@[simp]

Depends on / 依赖: lt_add_one_iff_of_not_isMax, not_isMax
-/
theorem lt_add_one_iff [NoMaxOrder α] : x < y + 1 ↔ x <= y :=
  lt_add_one_iff_of_not_isMax (not_isMax y)

@[simp]
/--
theorem `add_one_inj` / 定理 `add_one_inj`

English:
theorem add_one_inj
  given: [NoMaxOrder α]
  statement: x + 1 = y + 1 ↔ x = y
  proof: by
  simp [← succ_eq_add_one]

中文:
定理 add_one_inj
  条件: [NoMaxOrder α]
  结论: x + 1 = y + 1 ↔ x = y
  证明: by
  simp [← succ_eq_add_one]

Depends on / 依赖: succ_eq_add_one
-/
theorem add_one_inj [NoMaxOrder α] : x + 1 = y + 1 ↔ x = y := by
  simp [← succ_eq_add_one]

end Add

@[simp]
/--
theorem `lt_two_iff` / 定理 `lt_two_iff`

English:
theorem lt_two_iff
  given: [AddMonoidWithOne α] [SuccAddOrder α] [NoMaxOrder α]
  statement: x < 2 ↔ x <= 1
  proof: by
  rw [← one_add_one_eq_two]; rw [lt_add_one_iff]

中文:
定理 lt_two_iff
  条件: [AddMonoidWithOne α] [SuccAddOrder α] [NoMaxOrder α]
  结论: x < 2 ↔ x <= 1
  证明: by
  rw [← one_add_one_eq_two]; rw [lt_add_one_iff]

Depends on / 依赖: lt_add_one_iff, one_add_one_eq_two
-/
theorem lt_two_iff [AddMonoidWithOne α] [SuccAddOrder α] [NoMaxOrder α] : x < 2 ↔ x <= 1 := by
  rw [← one_add_one_eq_two]; rw [lt_add_one_iff]

section AddMonoidWithOne
variable [AddMonoidWithOne α] [SuccAddOrder α] [IsBotZeroClass α] [NeZero (1 : α)]

@[simp]
/--
theorem `lt_one_iff` / 定理 `lt_one_iff`

English:
theorem lt_one_iff
  statement: x < 1 ↔ x = 0
  proof: by
  simpa using (one_le_iff_ne_zero (x := x)).not

中文:
定理 lt_one_iff
  结论: x < 1 ↔ x = 0
  证明: by
  simpa using (one_le_iff_ne_zero (x := x)).not

Depends on / 依赖: one_le_iff_ne_zero
-/
theorem lt_one_iff : x < 1 ↔ x = 0 := by
  simpa using (one_le_iff_ne_zero (x := x)).not

/--
theorem `le_one_iff` / 定理 `le_one_iff`

English:
theorem le_one_iff
  statement: x <= 1 ↔ x = 0 ∨ x = 1
  proof: by
  rw [le_iff_lt_or_eq]; rw [lt_one_iff]

@[simp]

中文:
定理 le_one_iff
  结论: x <= 1 ↔ x = 0 ∨ x = 1
  证明: by
  rw [le_iff_lt_or_eq]; rw [lt_one_iff]

@[simp]

Depends on / 依赖: le_iff_lt_or_eq, lt_one_iff
-/
theorem le_one_iff : x <= 1 ↔ x = 0 ∨ x = 1 := by
  rw [le_iff_lt_or_eq]; rw [lt_one_iff]

@[simp]
/--
theorem `Iio_one` / 定理 `Iio_one`

English:
theorem Iio_one
  statement: Set.Iio (1 : α) = {0}
  proof: by
  ext; simp

中文:
定理 Iio_one
  结论: Set.Iio (1 : α) = {0}
  证明: by
  ext; simp
-/
theorem Iio_one : Set.Iio (1 : α) = {0} := by
  ext; simp

/--
theorem `Iic_one` / 定理 `Iic_one`

English:
theorem Iic_one
  statement: Set.Iic (1 : α) = {0, 1}
  proof: by
  ext; simp [le_one_iff]

中文:
定理 Iic_one
  结论: Set.Iic (1 : α) = {0, 1}
  证明: by
  ext; simp [le_one_iff]

Depends on / 依赖: le_one_iff
-/
theorem Iic_one : Set.Iic (1 : α) = {0, 1} := by
  ext; simp [le_one_iff]

variable [NoMaxOrder α]

/--
theorem `le_two_iff` / 定理 `le_two_iff`

English:
theorem le_two_iff
  statement: x <= 2 ↔ x = 0 ∨ x = 1 ∨ x = 2
  proof: by
  rw [le_iff_lt_or_eq]; rw [lt_two_iff]; rw [le_one_iff]; rw [or_assoc]

中文:
定理 le_two_iff
  结论: x <= 2 ↔ x = 0 ∨ x = 1 ∨ x = 2
  证明: by
  rw [le_iff_lt_or_eq]; rw [lt_two_iff]; rw [le_one_iff]; rw [or_assoc]

Depends on / 依赖: le_iff_lt_or_eq, le_one_iff, lt_two_iff, or_assoc
-/
theorem le_two_iff : x <= 2 ↔ x = 0 ∨ x = 1 ∨ x = 2 := by
  rw [le_iff_lt_or_eq]; rw [lt_two_iff]; rw [le_one_iff]; rw [or_assoc]

/--
theorem `Iio_two` / 定理 `Iio_two`

English:
theorem Iio_two
  statement: Set.Iio (2 : α) = {0, 1}
  proof: by
  ext; simp [le_one_iff]

中文:
定理 Iio_two
  结论: Set.Iio (2 : α) = {0, 1}
  证明: by
  ext; simp [le_one_iff]

Depends on / 依赖: le_one_iff
-/
theorem Iio_two : Set.Iio (2 : α) = {0, 1} := by
  ext; simp [le_one_iff]

/--
theorem `Iic_two` / 定理 `Iic_two`

English:
theorem Iic_two
  statement: Set.Iic (2 : α) = {0, 1, 2}
  proof: by
  ext; simp [le_two_iff]

中文:
定理 Iic_two
  结论: Set.Iic (2 : α) = {0, 1, 2}
  证明: by
  ext; simp [le_two_iff]

Depends on / 依赖: le_two_iff
-/
theorem Iic_two : Set.Iic (2 : α) = {0, 1, 2} := by
  ext; simp [le_two_iff]

end AddMonoidWithOne

section Sub

variable [Sub α] [One α] [PredSubOrder α]

/--
theorem `le_of_sub_one_lt` / 定理 `le_of_sub_one_lt`

English:
theorem le_of_sub_one_lt
  given: (h : x - 1 < y)
  statement: x <= y
  proof: by
  rw [← pred_eq_sub_one] at h
  exact le_of_pred_lt h

中文:
定理 le_of_sub_one_lt
  条件: (h : x - 1 < y)
  结论: x <= y
  证明: by
  rw [← pred_eq_sub_one] at h
  exact le_of_pred_lt h

Depends on / 依赖: le_of_pred_lt, pred_eq_sub_one
-/
theorem le_of_sub_one_lt (h : x - 1 < y) : x <= y := by
  rw [← pred_eq_sub_one] at h
  exact le_of_pred_lt h

/--
theorem `sub_one_lt_iff_of_not_isMin` / 定理 `sub_one_lt_iff_of_not_isMin`

English:
theorem sub_one_lt_iff_of_not_isMin
  given: (hx : ¬ IsMin x)
  statement: x - 1 < y ↔ x <= y
  proof: by
  rw [← pred_eq_sub_one]; rw [pred_lt_iff_of_not_isMin hx]

@[simp]

中文:
定理 sub_one_lt_iff_of_not_isMin
  条件: (hx : ¬ IsMin x)
  结论: x - 1 < y ↔ x <= y
  证明: by
  rw [← pred_eq_sub_one]; rw [pred_lt_iff_of_not_isMin hx]

@[simp]

Depends on / 依赖: pred_eq_sub_one, pred_lt_iff_of_not_isMin
-/
theorem sub_one_lt_iff_of_not_isMin (hx : ¬ IsMin x) : x - 1 < y ↔ x <= y := by
  rw [← pred_eq_sub_one]; rw [pred_lt_iff_of_not_isMin hx]

@[simp]
/--
theorem `sub_one_lt_iff` / 定理 `sub_one_lt_iff`

English:
theorem sub_one_lt_iff
  given: [NoMinOrder α]
  statement: x - 1 < y ↔ x <= y
  proof: sub_one_lt_iff_of_not_isMin (not_isMin x)

中文:
定理 sub_one_lt_iff
  条件: [NoMinOrder α]
  结论: x - 1 < y ↔ x <= y
  证明: sub_one_lt_iff_of_not_isMin (not_isMin x)

Depends on / 依赖: not_isMin, sub_one_lt_iff_of_not_isMin
-/
theorem sub_one_lt_iff [NoMinOrder α] : x - 1 < y ↔ x <= y :=
  sub_one_lt_iff_of_not_isMin (not_isMin x)

end Sub

/--
theorem `lt_one_iff_nonpos` / 定理 `lt_one_iff_nonpos`

English:
theorem lt_one_iff_nonpos
  statement: [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)]
  proof: by
  rw [← lt_succ_iff_of_not_isMax not_isMax_zero]; rw [succ_eq_add_one]; rw [zero_add]

中文:
定理 lt_one_iff_nonpos
  结论: [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)]
  证明: by
  rw [← lt_succ_iff_of_not_isMax not_isMax_zero]; rw [succ_eq_add_one]; rw [zero_add]

Depends on / 依赖: lt_succ_iff_of_not_isMax, not_isMax_zero, succ_eq_add_one, zero_add
-/
theorem lt_one_iff_nonpos [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)]
    [SuccAddOrder α] : x < 1 ↔ x <= 0 := by
  rw [← lt_succ_iff_of_not_isMax not_isMax_zero]; rw [succ_eq_add_one]; rw [zero_add]

end LinearOrder

end Order

section Monotone
variable {α β : Type*} [PartialOrder α] [Preorder β]

section SuccAddOrder
variable [Add α] [One α] [SuccAddOrder α] [IsSuccArchimedean α] {s : Set α} {f : α -> β}

/--
lemma `monotoneOn_of_le_add_one` / 引理 `monotoneOn_of_le_add_one`

English:
lemma monotoneOn_of_le_add_one
  given: (hs : s.OrdConnected)
  proof: by
  simpa [Order.succ_eq_add_one] using monotoneOn_of_le_succ hs (f := f)

中文:
引理 monotoneOn_of_le_add_one
  条件: (hs : s.OrdConnected)
  证明: by
  simpa [Order.succ_eq_add_one] using monotoneOn_of_le_succ hs (f := f)

Depends on / 依赖: Order.succ_eq_add_one, monotoneOn_of_le_succ, succ_eq_add_one
-/
lemma monotoneOn_of_le_add_one (hs : s.OrdConnected) :
    (forall a, ¬ IsMax a -> a in s -> a + 1 in s -> f a <= f (a + 1)) -> MonotoneOn f s := by
  simpa [Order.succ_eq_add_one] using monotoneOn_of_le_succ hs (f := f)

/--
lemma `antitoneOn_of_add_one_le` / 引理 `antitoneOn_of_add_one_le`

English:
lemma antitoneOn_of_add_one_le
  given: (hs : s.OrdConnected)
  proof: by
  simpa [Order.succ_eq_add_one] using antitoneOn_of_succ_le hs (f := f)

中文:
引理 antitoneOn_of_add_one_le
  条件: (hs : s.OrdConnected)
  证明: by
  simpa [Order.succ_eq_add_one] using antitoneOn_of_succ_le hs (f := f)

Depends on / 依赖: Order.succ_eq_add_one, antitoneOn_of_succ_le, succ_eq_add_one
-/
lemma antitoneOn_of_add_one_le (hs : s.OrdConnected) :
    (forall a, ¬ IsMax a -> a in s -> a + 1 in s -> f (a + 1) <= f a) -> AntitoneOn f s := by
  simpa [Order.succ_eq_add_one] using antitoneOn_of_succ_le hs (f := f)

/--
lemma `strictMonoOn_of_lt_add_one` / 引理 `strictMonoOn_of_lt_add_one`

English:
lemma strictMonoOn_of_lt_add_one
  given: (hs : s.OrdConnected)
  proof: by
  simpa [Order.succ_eq_add_one] using strictMonoOn_of_lt_succ hs (f := f)

中文:
引理 strictMonoOn_of_lt_add_one
  条件: (hs : s.OrdConnected)
  证明: by
  simpa [Order.succ_eq_add_one] using strictMonoOn_of_lt_succ hs (f := f)

Depends on / 依赖: Order.succ_eq_add_one, strictMonoOn_of_lt_succ, succ_eq_add_one
-/
lemma strictMonoOn_of_lt_add_one (hs : s.OrdConnected) :
    (forall a, ¬ IsMax a -> a in s -> a + 1 in s -> f a < f (a + 1)) -> StrictMonoOn f s := by
  simpa [Order.succ_eq_add_one] using strictMonoOn_of_lt_succ hs (f := f)

/--
lemma `strictAntiOn_of_add_one_lt` / 引理 `strictAntiOn_of_add_one_lt`

English:
lemma strictAntiOn_of_add_one_lt
  given: (hs : s.OrdConnected)
  proof: by
  simpa [Order.succ_eq_add_one] using strictAntiOn_of_succ_lt hs (f := f)

中文:
引理 strictAntiOn_of_add_one_lt
  条件: (hs : s.OrdConnected)
  证明: by
  simpa [Order.succ_eq_add_one] using strictAntiOn_of_succ_lt hs (f := f)

Depends on / 依赖: Order.succ_eq_add_one, strictAntiOn_of_succ_lt, succ_eq_add_one
-/
lemma strictAntiOn_of_add_one_lt (hs : s.OrdConnected) :
    (forall a, ¬ IsMax a -> a in s -> a + 1 in s -> f (a + 1) < f a) -> StrictAntiOn f s := by
  simpa [Order.succ_eq_add_one] using strictAntiOn_of_succ_lt hs (f := f)

/--
lemma `monotone_of_le_add_one` / 引理 `monotone_of_le_add_one`

English:
lemma monotone_of_le_add_one
  statement: (forall a, ¬ IsMax a -> f a <= f (a + 1)) -> Monotone f
  proof: by
  simpa [Order.succ_eq_add_one] using monotone_of_le_succ (f := f)

中文:
引理 monotone_of_le_add_one
  结论: (对任意 a, ¬ IsMax a -> f a <= f (a + 1)) -> Monotone f
  证明: by
  simpa [Order.succ_eq_add_one] using monotone_of_le_succ (f := f)

Depends on / 依赖: Order.succ_eq_add_one, monotone_of_le_succ, succ_eq_add_one
-/
lemma monotone_of_le_add_one : (forall a, ¬ IsMax a -> f a <= f (a + 1)) -> Monotone f := by
  simpa [Order.succ_eq_add_one] using monotone_of_le_succ (f := f)

/--
lemma `antitone_of_add_one_le` / 引理 `antitone_of_add_one_le`

English:
lemma antitone_of_add_one_le
  statement: (forall a, ¬ IsMax a -> f (a + 1) <= f a) -> Antitone f
  proof: by
  simpa [Order.succ_eq_add_one] using antitone_of_succ_le (f := f)

中文:
引理 antitone_of_add_one_le
  结论: (对任意 a, ¬ IsMax a -> f (a + 1) <= f a) -> Antitone f
  证明: by
  simpa [Order.succ_eq_add_one] using antitone_of_succ_le (f := f)

Depends on / 依赖: Order.succ_eq_add_one, antitone_of_succ_le, succ_eq_add_one
-/
lemma antitone_of_add_one_le : (forall a, ¬ IsMax a -> f (a + 1) <= f a) -> Antitone f := by
  simpa [Order.succ_eq_add_one] using antitone_of_succ_le (f := f)

/--
lemma `strictMono_of_lt_add_one` / 引理 `strictMono_of_lt_add_one`

English:
lemma strictMono_of_lt_add_one
  statement: (forall a, ¬ IsMax a -> f a < f (a + 1)) -> StrictMono f
  proof: by
  simpa [Order.succ_eq_add_one] using strictMono_of_lt_succ (f := f)

中文:
引理 strictMono_of_lt_add_one
  结论: (对任意 a, ¬ IsMax a -> f a < f (a + 1)) -> StrictMono f
  证明: by
  simpa [Order.succ_eq_add_one] using strictMono_of_lt_succ (f := f)

Depends on / 依赖: Order.succ_eq_add_one, strictMono_of_lt_succ, succ_eq_add_one
-/
lemma strictMono_of_lt_add_one : (forall a, ¬ IsMax a -> f a < f (a + 1)) -> StrictMono f := by
  simpa [Order.succ_eq_add_one] using strictMono_of_lt_succ (f := f)

/--
lemma `strictAnti_of_add_one_lt` / 引理 `strictAnti_of_add_one_lt`

English:
lemma strictAnti_of_add_one_lt
  statement: (forall a, ¬ IsMax a -> f (a + 1) < f a) -> StrictAnti f
  proof: by
  simpa [Order.succ_eq_add_one] using strictAnti_of_succ_lt (f := f)

中文:
引理 strictAnti_of_add_one_lt
  结论: (对任意 a, ¬ IsMax a -> f (a + 1) < f a) -> StrictAnti f
  证明: by
  simpa [Order.succ_eq_add_one] using strictAnti_of_succ_lt (f := f)

Depends on / 依赖: Order.succ_eq_add_one, strictAnti_of_succ_lt, succ_eq_add_one
-/
lemma strictAnti_of_add_one_lt : (forall a, ¬ IsMax a -> f (a + 1) < f a) -> StrictAnti f := by
  simpa [Order.succ_eq_add_one] using strictAnti_of_succ_lt (f := f)

end SuccAddOrder

section PredSubOrder
variable [Sub α] [One α] [PredSubOrder α] [IsPredArchimedean α] {s : Set α} {f : α -> β}

/--
lemma `monotoneOn_of_sub_one_le` / 引理 `monotoneOn_of_sub_one_le`

English:
lemma monotoneOn_of_sub_one_le
  given: (hs : s.OrdConnected)
  proof: by
  simpa [Order.pred_eq_sub_one] using monotoneOn_of_pred_le hs (f := f)

中文:
引理 monotoneOn_of_sub_one_le
  条件: (hs : s.OrdConnected)
  证明: by
  simpa [Order.pred_eq_sub_one] using monotoneOn_of_pred_le hs (f := f)

Depends on / 依赖: Order.pred_eq_sub_one, monotoneOn_of_pred_le, pred_eq_sub_one
-/
lemma monotoneOn_of_sub_one_le (hs : s.OrdConnected) :
    (forall a, ¬ IsMin a -> a in s -> a - 1 in s -> f (a - 1) <= f a) -> MonotoneOn f s := by
  simpa [Order.pred_eq_sub_one] using monotoneOn_of_pred_le hs (f := f)

/--
lemma `antitoneOn_of_le_sub_one` / 引理 `antitoneOn_of_le_sub_one`

English:
lemma antitoneOn_of_le_sub_one
  given: (hs : s.OrdConnected)
  proof: by
  simpa [Order.pred_eq_sub_one] using antitoneOn_of_le_pred hs (f := f)

中文:
引理 antitoneOn_of_le_sub_one
  条件: (hs : s.OrdConnected)
  证明: by
  simpa [Order.pred_eq_sub_one] using antitoneOn_of_le_pred hs (f := f)

Depends on / 依赖: Order.pred_eq_sub_one, antitoneOn_of_le_pred, pred_eq_sub_one
-/
lemma antitoneOn_of_le_sub_one (hs : s.OrdConnected) :
    (forall a, ¬ IsMin a -> a in s -> a - 1 in s -> f a <= f (a - 1)) -> AntitoneOn f s := by
  simpa [Order.pred_eq_sub_one] using antitoneOn_of_le_pred hs (f := f)

/--
lemma `strictMonoOn_of_sub_one_lt` / 引理 `strictMonoOn_of_sub_one_lt`

English:
lemma strictMonoOn_of_sub_one_lt
  given: (hs : s.OrdConnected)
  proof: by
  simpa [Order.pred_eq_sub_one] using strictMonoOn_of_pred_lt hs (f := f)

中文:
引理 strictMonoOn_of_sub_one_lt
  条件: (hs : s.OrdConnected)
  证明: by
  simpa [Order.pred_eq_sub_one] using strictMonoOn_of_pred_lt hs (f := f)

Depends on / 依赖: Order.pred_eq_sub_one, pred_eq_sub_one, strictMonoOn_of_pred_lt
-/
lemma strictMonoOn_of_sub_one_lt (hs : s.OrdConnected) :
    (forall a, ¬ IsMin a -> a in s -> a - 1 in s -> f (a - 1) < f a) -> StrictMonoOn f s := by
  simpa [Order.pred_eq_sub_one] using strictMonoOn_of_pred_lt hs (f := f)

/--
lemma `strictAntiOn_of_lt_sub_one` / 引理 `strictAntiOn_of_lt_sub_one`

English:
lemma strictAntiOn_of_lt_sub_one
  given: (hs : s.OrdConnected)
  proof: by
  simpa [Order.pred_eq_sub_one] using strictAntiOn_of_lt_pred hs (f := f)

中文:
引理 strictAntiOn_of_lt_sub_one
  条件: (hs : s.OrdConnected)
  证明: by
  simpa [Order.pred_eq_sub_one] using strictAntiOn_of_lt_pred hs (f := f)

Depends on / 依赖: Order.pred_eq_sub_one, pred_eq_sub_one, strictAntiOn_of_lt_pred
-/
lemma strictAntiOn_of_lt_sub_one (hs : s.OrdConnected) :
    (forall a, ¬ IsMin a -> a in s -> a - 1 in s -> f a < f (a - 1)) -> StrictAntiOn f s := by
  simpa [Order.pred_eq_sub_one] using strictAntiOn_of_lt_pred hs (f := f)

/--
lemma `monotone_of_sub_one_le` / 引理 `monotone_of_sub_one_le`

English:
lemma monotone_of_sub_one_le
  statement: (forall a, ¬ IsMin a -> f (a - 1) <= f a) -> Monotone f
  proof: by
  simpa [Order.pred_eq_sub_one] using monotone_of_pred_le (f := f)

中文:
引理 monotone_of_sub_one_le
  结论: (对任意 a, ¬ IsMin a -> f (a - 1) <= f a) -> Monotone f
  证明: by
  simpa [Order.pred_eq_sub_one] using monotone_of_pred_le (f := f)

Depends on / 依赖: Order.pred_eq_sub_one, monotone_of_pred_le, pred_eq_sub_one
-/
lemma monotone_of_sub_one_le : (forall a, ¬ IsMin a -> f (a - 1) <= f a) -> Monotone f := by
  simpa [Order.pred_eq_sub_one] using monotone_of_pred_le (f := f)

/--
lemma `antitone_of_le_sub_one` / 引理 `antitone_of_le_sub_one`

English:
lemma antitone_of_le_sub_one
  statement: (forall a, ¬ IsMin a -> f a <= f (a - 1)) -> Antitone f
  proof: by
  simpa [Order.pred_eq_sub_one] using antitone_of_le_pred (f := f)

中文:
引理 antitone_of_le_sub_one
  结论: (对任意 a, ¬ IsMin a -> f a <= f (a - 1)) -> Antitone f
  证明: by
  simpa [Order.pred_eq_sub_one] using antitone_of_le_pred (f := f)

Depends on / 依赖: Order.pred_eq_sub_one, antitone_of_le_pred, pred_eq_sub_one
-/
lemma antitone_of_le_sub_one : (forall a, ¬ IsMin a -> f a <= f (a - 1)) -> Antitone f := by
  simpa [Order.pred_eq_sub_one] using antitone_of_le_pred (f := f)

/--
lemma `strictMono_of_sub_one_lt` / 引理 `strictMono_of_sub_one_lt`

English:
lemma strictMono_of_sub_one_lt
  statement: (forall a, ¬ IsMin a -> f (a - 1) < f a) -> StrictMono f
  proof: by
  simpa [Order.pred_eq_sub_one] using strictMono_of_pred_lt (f := f)

中文:
引理 strictMono_of_sub_one_lt
  结论: (对任意 a, ¬ IsMin a -> f (a - 1) < f a) -> StrictMono f
  证明: by
  simpa [Order.pred_eq_sub_one] using strictMono_of_pred_lt (f := f)

Depends on / 依赖: Order.pred_eq_sub_one, pred_eq_sub_one, strictMono_of_pred_lt
-/
lemma strictMono_of_sub_one_lt : (forall a, ¬ IsMin a -> f (a - 1) < f a) -> StrictMono f := by
  simpa [Order.pred_eq_sub_one] using strictMono_of_pred_lt (f := f)

/--
lemma `strictAnti_of_lt_sub_one` / 引理 `strictAnti_of_lt_sub_one`

English:
lemma strictAnti_of_lt_sub_one
  statement: (forall a, ¬ IsMin a -> f a < f (a - 1)) -> StrictAnti f
  proof: by
  simpa [Order.pred_eq_sub_one] using strictAnti_of_lt_pred (f := f)

中文:
引理 strictAnti_of_lt_sub_one
  结论: (对任意 a, ¬ IsMin a -> f a < f (a - 1)) -> StrictAnti f
  证明: by
  simpa [Order.pred_eq_sub_one] using strictAnti_of_lt_pred (f := f)

Depends on / 依赖: Order.pred_eq_sub_one, pred_eq_sub_one, strictAnti_of_lt_pred
-/
lemma strictAnti_of_lt_sub_one : (forall a, ¬ IsMin a -> f a < f (a - 1)) -> StrictAnti f := by
  simpa [Order.pred_eq_sub_one] using strictAnti_of_lt_pred (f := f)

end PredSubOrder
end Monotone
