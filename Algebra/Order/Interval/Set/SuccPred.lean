/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Order.Interval.Set.SuccPred

/-!
# Set intervals in an additive successor-predecessor order

This file proves relations between the various set intervals in an additive successor/predecessor
order.

## Notes

Please keep in sync with:
* `Mathlib/Algebra/Order/Interval/Finset/SuccPred.lean`
* `Mathlib/Order/Interval/Finset/SuccPred.lean`
* `Mathlib/Order/Interval/Set/SuccPred.lean`

## TODO

Copy over `insert` lemmas from `Mathlib/Order/Interval/Finset/Nat.lean`.
-/

public section

open Function Order OrderDual

variable {ι α : Type*}

namespace Set
variable [LinearOrder α] [One α]

/-! ### Two-sided intervals -/

section SuccAddOrder
variable [Add α] [SuccAddOrder α] {a b : α}


/--
lemma `Ico_add_one_left_eq_Ioo` / 引理 `Ico_add_one_left_eq_Ioo`

English:
lemma Ico_add_one_left_eq_Ioo
  given: (a b : α)
  statement: Ico (a + 1) b = Ioo a b
  proof: by
  simpa [succ_eq_add_one] using Ico_succ_left_eq_Ioo a b

中文:
引理 Ico_add_one_left_eq_Ioo
  条件: (a b : α)
  结论: Ico (a + 1) b = Ioo a b
  证明: by
  simpa [succ_eq_add_one] using Ico_succ_left_eq_Ioo a b

Depends on / 依赖: Ico_succ_left_eq_Ioo, succ_eq_add_one
-/
lemma Ico_add_one_left_eq_Ioo (a b : α) : Ico (a + 1) b = Ioo a b := by
  simpa [succ_eq_add_one] using Ico_succ_left_eq_Ioo a b

/--
lemma `Icc_add_one_left_eq_Ioc_of_not_isMax` / 引理 `Icc_add_one_left_eq_Ioc_of_not_isMax`

English:
lemma Icc_add_one_left_eq_Ioc_of_not_isMax
  given: (ha : ¬ IsMax a) (b : α)
  statement: Icc (a + 1) b = Ioc a b
  proof: by
  simpa [succ_eq_add_one] using Icc_succ_left_eq_Ioc_of_not_isMax ha b

中文:
引理 Icc_add_one_left_eq_Ioc_of_not_isMax
  条件: (ha : ¬ IsMax a) (b : α)
  结论: Icc (a + 1) b = Ioc a b
  证明: by
  simpa [succ_eq_add_one] using Icc_succ_left_eq_Ioc_of_not_isMax ha b

Depends on / 依赖: Icc_succ_left_eq_Ioc_of_not_isMax, succ_eq_add_one
-/
lemma Icc_add_one_left_eq_Ioc_of_not_isMax (ha : ¬ IsMax a) (b : α) : Icc (a + 1) b = Ioc a b := by
  simpa [succ_eq_add_one] using Icc_succ_left_eq_Ioc_of_not_isMax ha b

/--
lemma `Ico_add_one_right_eq_Icc_of_not_isMax` / 引理 `Ico_add_one_right_eq_Icc_of_not_isMax`

English:
lemma Ico_add_one_right_eq_Icc_of_not_isMax
  given: (hb : ¬ IsMax b) (a : α)
  statement: Ico a (b + 1) = Icc a b
  proof: by
  simpa [succ_eq_add_one] using Ico_succ_right_eq_Icc_of_not_isMax hb a

中文:
引理 Ico_add_one_right_eq_Icc_of_not_isMax
  条件: (hb : ¬ IsMax b) (a : α)
  结论: Ico a (b + 1) = Icc a b
  证明: by
  simpa [succ_eq_add_one] using Ico_succ_right_eq_Icc_of_not_isMax hb a

Depends on / 依赖: Ico_succ_right_eq_Icc_of_not_isMax, succ_eq_add_one
-/
lemma Ico_add_one_right_eq_Icc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ico a (b + 1) = Icc a b := by
  simpa [succ_eq_add_one] using Ico_succ_right_eq_Icc_of_not_isMax hb a

/--
lemma `Ioo_add_one_right_eq_Ioc_of_not_isMax` / 引理 `Ioo_add_one_right_eq_Ioc_of_not_isMax`

English:
lemma Ioo_add_one_right_eq_Ioc_of_not_isMax
  given: (hb : ¬ IsMax b) (a : α)
  statement: Ioo a (b + 1) = Ioc a b
  proof: by
  simpa [succ_eq_add_one] using Ioo_succ_right_eq_Ioc_of_not_isMax hb a

中文:
引理 Ioo_add_one_right_eq_Ioc_of_not_isMax
  条件: (hb : ¬ IsMax b) (a : α)
  结论: Ioo a (b + 1) = Ioc a b
  证明: by
  simpa [succ_eq_add_one] using Ioo_succ_right_eq_Ioc_of_not_isMax hb a

Depends on / 依赖: Ioo_succ_right_eq_Ioc_of_not_isMax, succ_eq_add_one
-/
lemma Ioo_add_one_right_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ioo a (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ioo_succ_right_eq_Ioc_of_not_isMax hb a

/--
lemma `Ico_add_one_add_one_eq_Ioc_of_not_isMax` / 引理 `Ico_add_one_add_one_eq_Ioc_of_not_isMax`

English:
lemma Ico_add_one_add_one_eq_Ioc_of_not_isMax
  given: (hb : ¬ IsMax b) (a : α)
  proof: by
  simpa [succ_eq_add_one] using Ico_succ_succ_eq_Ioc_of_not_isMax hb a

中文:
引理 Ico_add_one_add_one_eq_Ioc_of_not_isMax
  条件: (hb : ¬ IsMax b) (a : α)
  证明: by
  simpa [succ_eq_add_one] using Ico_succ_succ_eq_Ioc_of_not_isMax hb a

Depends on / 依赖: Ico_succ_succ_eq_Ioc_of_not_isMax, succ_eq_add_one
-/
lemma Ico_add_one_add_one_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) :
    Ico (a + 1) (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ico_succ_succ_eq_Ioc_of_not_isMax hb a


/--
lemma `insert_Icc_add_one_left_eq_Icc` / 引理 `insert_Icc_add_one_left_eq_Icc`

English:
lemma insert_Icc_add_one_left_eq_Icc
  given: (h : a <= b)
  statement: insert a (Icc (a + 1) b) = Icc a b
  proof: by
  simpa [succ_eq_add_one] using insert_Icc_succ_left_eq_Icc h

中文:
引理 insert_Icc_add_one_left_eq_Icc
  条件: (h : a <= b)
  结论: insert a (Icc (a + 1) b) = Icc a b
  证明: by
  simpa [succ_eq_add_one] using insert_Icc_succ_left_eq_Icc h

Depends on / 依赖: insert_Icc_succ_left_eq_Icc, succ_eq_add_one
-/
lemma insert_Icc_add_one_left_eq_Icc (h : a <= b) : insert a (Icc (a + 1) b) = Icc a b := by
  simpa [succ_eq_add_one] using insert_Icc_succ_left_eq_Icc h

/--
lemma `insert_Icc_right_eq_Icc_add_one` / 引理 `insert_Icc_right_eq_Icc_add_one`

English:
lemma insert_Icc_right_eq_Icc_add_one
  given: (h : a <= b + 1)
  proof: by
  simpa [← succ_eq_add_one] using insert_Icc_right_eq_Icc_succ (succ_eq_add_one b ▸ h)

中文:
引理 insert_Icc_right_eq_Icc_add_one
  条件: (h : a <= b + 1)
  证明: by
  simpa [← succ_eq_add_one] using insert_Icc_right_eq_Icc_succ (succ_eq_add_one b ▸ h)

Depends on / 依赖: insert_Icc_right_eq_Icc_succ, succ_eq_add_one
-/
lemma insert_Icc_right_eq_Icc_add_one (h : a <= b + 1) :
    insert (b + 1) (Icc a b) = Icc a (b + 1) := by
  simpa [← succ_eq_add_one] using insert_Icc_right_eq_Icc_succ (succ_eq_add_one b ▸ h)

/--
lemma `insert_Ico_right_eq_Ico_add_one_of_not_isMax` / 引理 `insert_Ico_right_eq_Ico_add_one_of_not_isMax`

English:
lemma insert_Ico_right_eq_Ico_add_one_of_not_isMax
  given: (h : a <= b) (hb : ¬ IsMax b)
  proof: by
  simpa [succ_eq_add_one] using insert_Ico_right_eq_Ico_succ_of_not_isMax h hb

中文:
引理 insert_Ico_right_eq_Ico_add_one_of_not_isMax
  条件: (h : a <= b) (hb : ¬ IsMax b)
  证明: by
  simpa [succ_eq_add_one] using insert_Ico_right_eq_Ico_succ_of_not_isMax h hb

Depends on / 依赖: insert_Ico_right_eq_Ico_succ_of_not_isMax, succ_eq_add_one
-/
lemma insert_Ico_right_eq_Ico_add_one_of_not_isMax (h : a <= b) (hb : ¬ IsMax b) :
    insert b (Ico a b) = Ico a (b + 1) := by
  simpa [succ_eq_add_one] using insert_Ico_right_eq_Ico_succ_of_not_isMax h hb

/--
lemma `insert_Ico_add_one_left_eq_Ico` / 引理 `insert_Ico_add_one_left_eq_Ico`

English:
lemma insert_Ico_add_one_left_eq_Ico
  given: (h : a < b)
  statement: insert a (Ico (a + 1) b) = Ico a b
  proof: by
  simpa [succ_eq_add_one] using insert_Ico_succ_left_eq_Ico h

中文:
引理 insert_Ico_add_one_left_eq_Ico
  条件: (h : a < b)
  结论: insert a (Ico (a + 1) b) = Ico a b
  证明: by
  simpa [succ_eq_add_one] using insert_Ico_succ_left_eq_Ico h

Depends on / 依赖: insert_Ico_succ_left_eq_Ico, succ_eq_add_one
-/
lemma insert_Ico_add_one_left_eq_Ico (h : a < b) : insert a (Ico (a + 1) b) = Ico a b := by
  simpa [succ_eq_add_one] using insert_Ico_succ_left_eq_Ico h

/--
lemma `insert_Ioc_right_eq_Ioc_add_one_of_not_isMax` / 引理 `insert_Ioc_right_eq_Ioc_add_one_of_not_isMax`

English:
lemma insert_Ioc_right_eq_Ioc_add_one_of_not_isMax
  given: (h : a <= b) (hb : ¬ IsMax b)
  proof: by
  simpa [succ_eq_add_one] using insert_Ioc_right_eq_Ioc_succ_of_not_isMax h hb

中文:
引理 insert_Ioc_right_eq_Ioc_add_one_of_not_isMax
  条件: (h : a <= b) (hb : ¬ IsMax b)
  证明: by
  simpa [succ_eq_add_one] using insert_Ioc_right_eq_Ioc_succ_of_not_isMax h hb

Depends on / 依赖: insert_Ioc_right_eq_Ioc_succ_of_not_isMax, succ_eq_add_one
-/
lemma insert_Ioc_right_eq_Ioc_add_one_of_not_isMax (h : a <= b) (hb : ¬ IsMax b) :
    insert (b + 1) (Ioc a b) = Ioc a (b + 1) := by
  simpa [succ_eq_add_one] using insert_Ioc_right_eq_Ioc_succ_of_not_isMax h hb

/--
lemma `insert_Ioc_add_one_left_eq_Ioc` / 引理 `insert_Ioc_add_one_left_eq_Ioc`

English:
lemma insert_Ioc_add_one_left_eq_Ioc
  given: (h : a < b)
  statement: insert (a + 1) (Ioc (a + 1) b) = Ioc a b
  proof: by
  simpa [succ_eq_add_one] using insert_Ioc_succ_left_eq_Ioc h

中文:
引理 insert_Ioc_add_one_left_eq_Ioc
  条件: (h : a < b)
  结论: insert (a + 1) (Ioc (a + 1) b) = Ioc a b
  证明: by
  simpa [succ_eq_add_one] using insert_Ioc_succ_left_eq_Ioc h

Depends on / 依赖: insert_Ioc_succ_left_eq_Ioc, succ_eq_add_one
-/
lemma insert_Ioc_add_one_left_eq_Ioc (h : a < b) : insert (a + 1) (Ioc (a + 1) b) = Ioc a b := by
  simpa [succ_eq_add_one] using insert_Ioc_succ_left_eq_Ioc h

/-!
#### Orders with no maximal elements

##### Equalities of intervals
-/

variable [NoMaxOrder α]

/--
lemma `Icc_add_one_left_eq_Ioc` / 引理 `Icc_add_one_left_eq_Ioc`

English:
lemma Icc_add_one_left_eq_Ioc
  given: (a b : α)
  statement: Icc (a + 1) b = Ioc a b
  proof: by
  simpa [succ_eq_add_one] using Icc_succ_left_eq_Ioc a b

中文:
引理 Icc_add_one_left_eq_Ioc
  条件: (a b : α)
  结论: Icc (a + 1) b = Ioc a b
  证明: by
  simpa [succ_eq_add_one] using Icc_succ_left_eq_Ioc a b

Depends on / 依赖: Icc_succ_left_eq_Ioc, succ_eq_add_one
-/
lemma Icc_add_one_left_eq_Ioc (a b : α) : Icc (a + 1) b = Ioc a b := by
  simpa [succ_eq_add_one] using Icc_succ_left_eq_Ioc a b

/--
lemma `Ico_add_one_right_eq_Icc` / 引理 `Ico_add_one_right_eq_Icc`

English:
lemma Ico_add_one_right_eq_Icc
  given: (a b : α)
  statement: Ico a (b + 1) = Icc a b
  proof: by
  simpa [succ_eq_add_one] using Ico_succ_right_eq_Icc a b

中文:
引理 Ico_add_one_right_eq_Icc
  条件: (a b : α)
  结论: Ico a (b + 1) = Icc a b
  证明: by
  simpa [succ_eq_add_one] using Ico_succ_right_eq_Icc a b

Depends on / 依赖: Ico_succ_right_eq_Icc, succ_eq_add_one
-/
lemma Ico_add_one_right_eq_Icc (a b : α) : Ico a (b + 1) = Icc a b := by
  simpa [succ_eq_add_one] using Ico_succ_right_eq_Icc a b

/--
lemma `Ioo_add_one_right_eq_Ioc` / 引理 `Ioo_add_one_right_eq_Ioc`

English:
lemma Ioo_add_one_right_eq_Ioc
  given: (a b : α)
  statement: Ioo a (b + 1) = Ioc a b
  proof: by
  simpa [succ_eq_add_one] using Ioo_succ_right_eq_Ioc a b

中文:
引理 Ioo_add_one_right_eq_Ioc
  条件: (a b : α)
  结论: Ioo a (b + 1) = Ioc a b
  证明: by
  simpa [succ_eq_add_one] using Ioo_succ_right_eq_Ioc a b

Depends on / 依赖: Ioo_succ_right_eq_Ioc, succ_eq_add_one
-/
lemma Ioo_add_one_right_eq_Ioc (a b : α) : Ioo a (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ioo_succ_right_eq_Ioc a b

/--
lemma `Ico_add_one_add_one_eq_Ioc` / 引理 `Ico_add_one_add_one_eq_Ioc`

English:
lemma Ico_add_one_add_one_eq_Ioc
  given: (a b : α)
  statement: Ico (a + 1) (b + 1) = Ioc a b
  proof: by
  simpa [succ_eq_add_one] using Ico_succ_succ_eq_Ioc a b

中文:
引理 Ico_add_one_add_one_eq_Ioc
  条件: (a b : α)
  结论: Ico (a + 1) (b + 1) = Ioc a b
  证明: by
  simpa [succ_eq_add_one] using Ico_succ_succ_eq_Ioc a b

Depends on / 依赖: Ico_succ_succ_eq_Ioc, succ_eq_add_one
-/
lemma Ico_add_one_add_one_eq_Ioc (a b : α) : Ico (a + 1) (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ico_succ_succ_eq_Ioc a b


/--
lemma `insert_Ico_right_eq_Ico_add_one` / 引理 `insert_Ico_right_eq_Ico_add_one`

English:
lemma insert_Ico_right_eq_Ico_add_one
  given: (h : a <= b)
  statement: insert b (Ico a b) = Ico a (b + 1)
  proof: by
  simpa [succ_eq_add_one] using insert_Ico_right_eq_Ico_succ h

中文:
引理 insert_Ico_right_eq_Ico_add_one
  条件: (h : a <= b)
  结论: insert b (Ico a b) = Ico a (b + 1)
  证明: by
  simpa [succ_eq_add_one] using insert_Ico_right_eq_Ico_succ h

Depends on / 依赖: insert_Ico_right_eq_Ico_succ, succ_eq_add_one
-/
lemma insert_Ico_right_eq_Ico_add_one (h : a <= b) : insert b (Ico a b) = Ico a (b + 1) := by
  simpa [succ_eq_add_one] using insert_Ico_right_eq_Ico_succ h

/--
lemma `insert_Ioc_right_eq_Ioc_add_one` / 引理 `insert_Ioc_right_eq_Ioc_add_one`

English:
lemma insert_Ioc_right_eq_Ioc_add_one
  given: (h : a <= b)
  statement: insert (b + 1) (Ioc a b) = Ioc a (b + 1)
  proof: insert_Ioc_right_eq_Ioc_add_one_of_not_isMax h (not_isMax _)

中文:
引理 insert_Ioc_right_eq_Ioc_add_one
  条件: (h : a <= b)
  结论: insert (b + 1) (Ioc a b) = Ioc a (b + 1)
  证明: insert_Ioc_right_eq_Ioc_add_one_of_not_isMax h (not_isMax _)

Depends on / 依赖: insert_Ioc_right_eq_Ioc_add_one_of_not_isMax, not_isMax
-/
lemma insert_Ioc_right_eq_Ioc_add_one (h : a <= b) : insert (b + 1) (Ioc a b) = Ioc a (b + 1) :=
  insert_Ioc_right_eq_Ioc_add_one_of_not_isMax h (not_isMax _)

end SuccAddOrder

section PredSubOrder
variable [Sub α] [PredSubOrder α] {a b : α}


/--
lemma `Ioc_sub_one_right_eq_Ioo` / 引理 `Ioc_sub_one_right_eq_Ioo`

English:
lemma Ioc_sub_one_right_eq_Ioo
  given: (a b : α)
  statement: Ioc a (b - 1) = Ioo a b
  proof: by
  simpa [pred_eq_sub_one] using Ioc_pred_right_eq_Ioo a b

中文:
引理 Ioc_sub_one_right_eq_Ioo
  条件: (a b : α)
  结论: Ioc a (b - 1) = Ioo a b
  证明: by
  simpa [pred_eq_sub_one] using Ioc_pred_right_eq_Ioo a b

Depends on / 依赖: Ioc_pred_right_eq_Ioo, pred_eq_sub_one
-/
lemma Ioc_sub_one_right_eq_Ioo (a b : α) : Ioc a (b - 1) = Ioo a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_right_eq_Ioo a b

/--
lemma `Icc_sub_one_right_eq_Ico_of_not_isMin` / 引理 `Icc_sub_one_right_eq_Ico_of_not_isMin`

English:
lemma Icc_sub_one_right_eq_Ico_of_not_isMin
  given: (hb : ¬ IsMin b) (a : α)
  statement: Icc a (b - 1) = Ico a b
  proof: by
  simpa [pred_eq_sub_one] using Icc_pred_right_eq_Ico_of_not_isMin hb a

中文:
引理 Icc_sub_one_right_eq_Ico_of_not_isMin
  条件: (hb : ¬ IsMin b) (a : α)
  结论: Icc a (b - 1) = Ico a b
  证明: by
  simpa [pred_eq_sub_one] using Icc_pred_right_eq_Ico_of_not_isMin hb a

Depends on / 依赖: Icc_pred_right_eq_Ico_of_not_isMin, pred_eq_sub_one
-/
lemma Icc_sub_one_right_eq_Ico_of_not_isMin (hb : ¬ IsMin b) (a : α) : Icc a (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Icc_pred_right_eq_Ico_of_not_isMin hb a

/--
lemma `Ioc_sub_one_left_eq_Icc_of_not_isMin` / 引理 `Ioc_sub_one_left_eq_Icc_of_not_isMin`

English:
lemma Ioc_sub_one_left_eq_Icc_of_not_isMin
  given: (ha : ¬ IsMin a) (b : α)
  statement: Ioc (a - 1) b = Icc a b
  proof: by
  simpa [pred_eq_sub_one] using Ioc_pred_left_eq_Icc_of_not_isMin ha b

中文:
引理 Ioc_sub_one_left_eq_Icc_of_not_isMin
  条件: (ha : ¬ IsMin a) (b : α)
  结论: Ioc (a - 1) b = Icc a b
  证明: by
  simpa [pred_eq_sub_one] using Ioc_pred_left_eq_Icc_of_not_isMin ha b

Depends on / 依赖: Ioc_pred_left_eq_Icc_of_not_isMin, pred_eq_sub_one
-/
lemma Ioc_sub_one_left_eq_Icc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioc (a - 1) b = Icc a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_left_eq_Icc_of_not_isMin ha b

/--
lemma `Ioo_sub_one_left_eq_Ioc_of_not_isMin` / 引理 `Ioo_sub_one_left_eq_Ioc_of_not_isMin`

English:
lemma Ioo_sub_one_left_eq_Ioc_of_not_isMin
  given: (ha : ¬ IsMin a) (b : α)
  statement: Ioo (a - 1) b = Ico a b
  proof: by
  simpa [pred_eq_sub_one] using Ioo_pred_left_eq_Ioc_of_not_isMin ha b

中文:
引理 Ioo_sub_one_left_eq_Ioc_of_not_isMin
  条件: (ha : ¬ IsMin a) (b : α)
  结论: Ioo (a - 1) b = Ico a b
  证明: by
  simpa [pred_eq_sub_one] using Ioo_pred_left_eq_Ioc_of_not_isMin ha b

Depends on / 依赖: Ioo_pred_left_eq_Ioc_of_not_isMin, pred_eq_sub_one
-/
lemma Ioo_sub_one_left_eq_Ioc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioo (a - 1) b = Ico a b := by
  simpa [pred_eq_sub_one] using Ioo_pred_left_eq_Ioc_of_not_isMin ha b

/--
lemma `Ioc_sub_one_sub_one_eq_Ico_of_not_isMin` / 引理 `Ioc_sub_one_sub_one_eq_Ico_of_not_isMin`

English:
lemma Ioc_sub_one_sub_one_eq_Ico_of_not_isMin
  given: (ha : ¬ IsMin a) (b : α)
  proof: by
  simpa [pred_eq_sub_one] using Ioc_pred_pred_eq_Ico_of_not_isMin ha b

中文:
引理 Ioc_sub_one_sub_one_eq_Ico_of_not_isMin
  条件: (ha : ¬ IsMin a) (b : α)
  证明: by
  simpa [pred_eq_sub_one] using Ioc_pred_pred_eq_Ico_of_not_isMin ha b

Depends on / 依赖: Ioc_pred_pred_eq_Ico_of_not_isMin, pred_eq_sub_one
-/
lemma Ioc_sub_one_sub_one_eq_Ico_of_not_isMin (ha : ¬ IsMin a) (b : α) :
    Ioc (a - 1) (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_pred_eq_Ico_of_not_isMin ha b


/--
lemma `insert_Icc_sub_one_right_eq_Icc` / 引理 `insert_Icc_sub_one_right_eq_Icc`

English:
lemma insert_Icc_sub_one_right_eq_Icc
  given: (h : a <= b)
  statement: insert b (Icc a (b - 1)) = Icc a b
  proof: by
  simpa [pred_eq_sub_one] using insert_Icc_pred_right_eq_Icc h

中文:
引理 insert_Icc_sub_one_right_eq_Icc
  条件: (h : a <= b)
  结论: insert b (Icc a (b - 1)) = Icc a b
  证明: by
  simpa [pred_eq_sub_one] using insert_Icc_pred_right_eq_Icc h

Depends on / 依赖: insert_Icc_pred_right_eq_Icc, pred_eq_sub_one
-/
lemma insert_Icc_sub_one_right_eq_Icc (h : a <= b) : insert b (Icc a (b - 1)) = Icc a b := by
  simpa [pred_eq_sub_one] using insert_Icc_pred_right_eq_Icc h

/--
lemma `insert_Icc_left_eq_Icc_sub_one` / 引理 `insert_Icc_left_eq_Icc_sub_one`

English:
lemma insert_Icc_left_eq_Icc_sub_one
  given: (h : a - 1 <= b)
  proof: by
  simpa [← pred_eq_sub_one] using insert_Icc_left_eq_Icc_pred (pred_eq_sub_one a ▸ h)

中文:
引理 insert_Icc_left_eq_Icc_sub_one
  条件: (h : a - 1 <= b)
  证明: by
  simpa [← pred_eq_sub_one] using insert_Icc_left_eq_Icc_pred (pred_eq_sub_one a ▸ h)

Depends on / 依赖: insert_Icc_left_eq_Icc_pred, pred_eq_sub_one
-/
lemma insert_Icc_left_eq_Icc_sub_one (h : a - 1 <= b) :
    insert (a - 1) (Icc a b) = Icc (a - 1) b := by
  simpa [← pred_eq_sub_one] using insert_Icc_left_eq_Icc_pred (pred_eq_sub_one a ▸ h)

/--
lemma `insert_Ioc_left_eq_Ioc_sub_one_of_not_isMin` / 引理 `insert_Ioc_left_eq_Ioc_sub_one_of_not_isMin`

English:
lemma insert_Ioc_left_eq_Ioc_sub_one_of_not_isMin
  given: (h : a <= b) (ha : ¬ IsMin a)
  proof: by
  simpa [pred_eq_sub_one] using insert_Ioc_left_eq_Ioc_pred_of_not_isMin h ha

中文:
引理 insert_Ioc_left_eq_Ioc_sub_one_of_not_isMin
  条件: (h : a <= b) (ha : ¬ IsMin a)
  证明: by
  simpa [pred_eq_sub_one] using insert_Ioc_left_eq_Ioc_pred_of_not_isMin h ha

Depends on / 依赖: insert_Ioc_left_eq_Ioc_pred_of_not_isMin, pred_eq_sub_one
-/
lemma insert_Ioc_left_eq_Ioc_sub_one_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) :
    insert a (Ioc a b) = Ioc (a - 1) b := by
  simpa [pred_eq_sub_one] using insert_Ioc_left_eq_Ioc_pred_of_not_isMin h ha

/--
lemma `insert_Ioc_sub_one_right_eq_Ioc` / 引理 `insert_Ioc_sub_one_right_eq_Ioc`

English:
lemma insert_Ioc_sub_one_right_eq_Ioc
  given: (h : a < b)
  statement: insert b (Ioc a (b - 1)) = Ioc a b
  proof: by
  simpa [pred_eq_sub_one] using insert_Ioc_pred_right_eq_Ioc h

中文:
引理 insert_Ioc_sub_one_right_eq_Ioc
  条件: (h : a < b)
  结论: insert b (Ioc a (b - 1)) = Ioc a b
  证明: by
  simpa [pred_eq_sub_one] using insert_Ioc_pred_right_eq_Ioc h

Depends on / 依赖: insert_Ioc_pred_right_eq_Ioc, pred_eq_sub_one
-/
lemma insert_Ioc_sub_one_right_eq_Ioc (h : a < b) : insert b (Ioc a (b - 1)) = Ioc a b := by
  simpa [pred_eq_sub_one] using insert_Ioc_pred_right_eq_Ioc h

/--
lemma `insert_Ico_left_eq_Ico_sub_one_of_not_isMin` / 引理 `insert_Ico_left_eq_Ico_sub_one_of_not_isMin`

English:
lemma insert_Ico_left_eq_Ico_sub_one_of_not_isMin
  given: (h : a <= b) (ha : ¬ IsMin a)
  proof: by
  simpa [pred_eq_sub_one] using insert_Ico_left_eq_Ico_pred_of_not_isMin h ha

中文:
引理 insert_Ico_left_eq_Ico_sub_one_of_not_isMin
  条件: (h : a <= b) (ha : ¬ IsMin a)
  证明: by
  simpa [pred_eq_sub_one] using insert_Ico_left_eq_Ico_pred_of_not_isMin h ha

Depends on / 依赖: insert_Ico_left_eq_Ico_pred_of_not_isMin, pred_eq_sub_one
-/
lemma insert_Ico_left_eq_Ico_sub_one_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) :
    insert (a - 1) (Ico a b) = Ico (a - 1) b := by
  simpa [pred_eq_sub_one] using insert_Ico_left_eq_Ico_pred_of_not_isMin h ha

/--
lemma `insert_Ico_sub_one_right_eq_Ico` / 引理 `insert_Ico_sub_one_right_eq_Ico`

English:
lemma insert_Ico_sub_one_right_eq_Ico
  given: (h : a < b)
  statement: insert (b - 1) (Ico a (b - 1)) = Ico a b
  proof: by
  simpa [pred_eq_sub_one] using insert_Ico_pred_right_eq_Ico h

中文:
引理 insert_Ico_sub_one_right_eq_Ico
  条件: (h : a < b)
  结论: insert (b - 1) (Ico a (b - 1)) = Ico a b
  证明: by
  simpa [pred_eq_sub_one] using insert_Ico_pred_right_eq_Ico h

Depends on / 依赖: insert_Ico_pred_right_eq_Ico, pred_eq_sub_one
-/
lemma insert_Ico_sub_one_right_eq_Ico (h : a < b) : insert (b - 1) (Ico a (b - 1)) = Ico a b := by
  simpa [pred_eq_sub_one] using insert_Ico_pred_right_eq_Ico h

/-!
#### Orders with no minimal elements

##### Equalities of intervals
-/

variable [NoMinOrder α]

/--
lemma `Icc_sub_one_right_eq_Ico` / 引理 `Icc_sub_one_right_eq_Ico`

English:
lemma Icc_sub_one_right_eq_Ico
  given: (a b : α)
  statement: Icc a (b - 1) = Ico a b
  proof: by
  simpa [pred_eq_sub_one] using Icc_pred_right_eq_Ico a b

中文:
引理 Icc_sub_one_right_eq_Ico
  条件: (a b : α)
  结论: Icc a (b - 1) = Ico a b
  证明: by
  simpa [pred_eq_sub_one] using Icc_pred_right_eq_Ico a b

Depends on / 依赖: Icc_pred_right_eq_Ico, pred_eq_sub_one
-/
lemma Icc_sub_one_right_eq_Ico (a b : α) : Icc a (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Icc_pred_right_eq_Ico a b

/--
lemma `Ioc_sub_one_left_eq_Icc` / 引理 `Ioc_sub_one_left_eq_Icc`

English:
lemma Ioc_sub_one_left_eq_Icc
  given: (a b : α)
  statement: Ioc (a - 1) b = Icc a b
  proof: by
  simpa [pred_eq_sub_one] using Ioc_pred_left_eq_Icc a b

中文:
引理 Ioc_sub_one_left_eq_Icc
  条件: (a b : α)
  结论: Ioc (a - 1) b = Icc a b
  证明: by
  simpa [pred_eq_sub_one] using Ioc_pred_left_eq_Icc a b

Depends on / 依赖: Ioc_pred_left_eq_Icc, pred_eq_sub_one
-/
lemma Ioc_sub_one_left_eq_Icc (a b : α) : Ioc (a - 1) b = Icc a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_left_eq_Icc a b

/--
lemma `Ioo_sub_one_left_eq_Ioc` / 引理 `Ioo_sub_one_left_eq_Ioc`

English:
lemma Ioo_sub_one_left_eq_Ioc
  given: (a b : α)
  statement: Ioo (a - 1) b = Ico a b
  proof: by
  simpa [pred_eq_sub_one] using Ioo_pred_left_eq_Ioc a b

中文:
引理 Ioo_sub_one_left_eq_Ioc
  条件: (a b : α)
  结论: Ioo (a - 1) b = Ico a b
  证明: by
  simpa [pred_eq_sub_one] using Ioo_pred_left_eq_Ioc a b

Depends on / 依赖: Ioo_pred_left_eq_Ioc, pred_eq_sub_one
-/
lemma Ioo_sub_one_left_eq_Ioc (a b : α) : Ioo (a - 1) b = Ico a b := by
  simpa [pred_eq_sub_one] using Ioo_pred_left_eq_Ioc a b

/--
lemma `Ioc_sub_one_sub_one_eq_Ico` / 引理 `Ioc_sub_one_sub_one_eq_Ico`

English:
lemma Ioc_sub_one_sub_one_eq_Ico
  given: (a b : α)
  statement: Ioc (a - 1) (b - 1) = Ico a b
  proof: by
  simpa [pred_eq_sub_one] using Ioc_pred_pred_eq_Ico a b

中文:
引理 Ioc_sub_one_sub_one_eq_Ico
  条件: (a b : α)
  结论: Ioc (a - 1) (b - 1) = Ico a b
  证明: by
  simpa [pred_eq_sub_one] using Ioc_pred_pred_eq_Ico a b

Depends on / 依赖: Ioc_pred_pred_eq_Ico, pred_eq_sub_one
-/
lemma Ioc_sub_one_sub_one_eq_Ico (a b : α) : Ioc (a - 1) (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_pred_eq_Ico a b


/--
lemma `insert_Ioc_left_eq_Ioc_sub_one` / 引理 `insert_Ioc_left_eq_Ioc_sub_one`

English:
lemma insert_Ioc_left_eq_Ioc_sub_one
  given: (h : a <= b)
  statement: insert a (Ioc a b) = Ioc (a - 1) b
  proof: by
  simpa [pred_eq_sub_one] using insert_Ioc_left_eq_Ioc_pred h

中文:
引理 insert_Ioc_left_eq_Ioc_sub_one
  条件: (h : a <= b)
  结论: insert a (Ioc a b) = Ioc (a - 1) b
  证明: by
  simpa [pred_eq_sub_one] using insert_Ioc_left_eq_Ioc_pred h

Depends on / 依赖: insert_Ioc_left_eq_Ioc_pred, pred_eq_sub_one
-/
lemma insert_Ioc_left_eq_Ioc_sub_one (h : a <= b) : insert a (Ioc a b) = Ioc (a - 1) b := by
  simpa [pred_eq_sub_one] using insert_Ioc_left_eq_Ioc_pred h

/--
lemma `insert_Ico_left_eq_Ico_sub_one` / 引理 `insert_Ico_left_eq_Ico_sub_one`

English:
lemma insert_Ico_left_eq_Ico_sub_one
  given: (h : a <= b)
  statement: insert (a - 1) (Ico a b) = Ico (a - 1) b
  proof: insert_Ico_left_eq_Ico_sub_one_of_not_isMin h (not_isMin _)

中文:
引理 insert_Ico_left_eq_Ico_sub_one
  条件: (h : a <= b)
  结论: insert (a - 1) (Ico a b) = Ico (a - 1) b
  证明: insert_Ico_left_eq_Ico_sub_one_of_not_isMin h (not_isMin _)

Depends on / 依赖: insert_Ico_left_eq_Ico_sub_one_of_not_isMin, not_isMin
-/
lemma insert_Ico_left_eq_Ico_sub_one (h : a <= b) : insert (a - 1) (Ico a b) = Ico (a - 1) b :=
  insert_Ico_left_eq_Ico_sub_one_of_not_isMin h (not_isMin _)

end PredSubOrder

section SuccAddPredSubOrder
variable [Add α] [Sub α] [SuccAddOrder α] [PredSubOrder α] [Nontrivial α]

/--
lemma `Icc_add_one_sub_one_eq_Ioo` / 引理 `Icc_add_one_sub_one_eq_Ioo`

English:
lemma Icc_add_one_sub_one_eq_Ioo
  given: (a b : α)
  statement: Icc (a + 1) (b - 1) = Ioo a b
  proof: by
  simpa [succ_eq_add_one, pred_eq_sub_one] using Icc_succ_pred_eq_Ioo a b

中文:
引理 Icc_add_one_sub_one_eq_Ioo
  条件: (a b : α)
  结论: Icc (a + 1) (b - 1) = Ioo a b
  证明: by
  simpa [succ_eq_add_one, pred_eq_sub_one] using Icc_succ_pred_eq_Ioo a b

Depends on / 依赖: Icc_succ_pred_eq_Ioo, pred_eq_sub_one, succ_eq_add_one
-/
lemma Icc_add_one_sub_one_eq_Ioo (a b : α) : Icc (a + 1) (b - 1) = Ioo a b := by
  simpa [succ_eq_add_one, pred_eq_sub_one] using Icc_succ_pred_eq_Ioo a b

end SuccAddPredSubOrder

/-! ### One-sided interval towards `⊥` -/

section SuccAddOrder
variable [Add α] [SuccAddOrder α] {b : α}

/--
lemma `Iio_add_one_eq_Iic_of_not_isMax` / 引理 `Iio_add_one_eq_Iic_of_not_isMax`

English:
lemma Iio_add_one_eq_Iic_of_not_isMax
  given: (hb : ¬ IsMax b)
  statement: Iio (b + 1) = Iic b
  proof: by
  simpa [succ_eq_add_one] using Iio_succ_eq_Iic_of_not_isMax hb

中文:
引理 Iio_add_one_eq_Iic_of_not_isMax
  条件: (hb : ¬ IsMax b)
  结论: Iio (b + 1) = Iic b
  证明: by
  simpa [succ_eq_add_one] using Iio_succ_eq_Iic_of_not_isMax hb

Depends on / 依赖: Iio_succ_eq_Iic_of_not_isMax, succ_eq_add_one
-/
lemma Iio_add_one_eq_Iic_of_not_isMax (hb : ¬ IsMax b) : Iio (b + 1) = Iic b := by
  simpa [succ_eq_add_one] using Iio_succ_eq_Iic_of_not_isMax hb

variable [NoMaxOrder α]

/--
lemma `Iio_add_one_eq_Iic` / 引理 `Iio_add_one_eq_Iic`

English:
lemma Iio_add_one_eq_Iic
  given: (b : α)
  statement: Iio (b + 1) = Iic b
  proof: by
  simpa [succ_eq_add_one] using Iio_succ_eq_Iic b

中文:
引理 Iio_add_one_eq_Iic
  条件: (b : α)
  结论: Iio (b + 1) = Iic b
  证明: by
  simpa [succ_eq_add_one] using Iio_succ_eq_Iic b

Depends on / 依赖: Iio_succ_eq_Iic, succ_eq_add_one
-/
lemma Iio_add_one_eq_Iic (b : α) : Iio (b + 1) = Iic b := by
  simpa [succ_eq_add_one] using Iio_succ_eq_Iic b

end SuccAddOrder

section PredSubOrder
variable [Sub α] [PredSubOrder α] {a b : α}

/--
lemma `Iic_sub_one_eq_Iio_of_not_isMin` / 引理 `Iic_sub_one_eq_Iio_of_not_isMin`

English:
lemma Iic_sub_one_eq_Iio_of_not_isMin
  given: (hb : ¬ IsMin b)
  statement: Iic (b - 1) = Iio b
  proof: by
  simpa [pred_eq_sub_one] using Iic_pred_eq_Iio_of_not_isMin hb

中文:
引理 Iic_sub_one_eq_Iio_of_not_isMin
  条件: (hb : ¬ IsMin b)
  结论: Iic (b - 1) = Iio b
  证明: by
  simpa [pred_eq_sub_one] using Iic_pred_eq_Iio_of_not_isMin hb

Depends on / 依赖: Iic_pred_eq_Iio_of_not_isMin, pred_eq_sub_one
-/
lemma Iic_sub_one_eq_Iio_of_not_isMin (hb : ¬ IsMin b) : Iic (b - 1) = Iio b := by
  simpa [pred_eq_sub_one] using Iic_pred_eq_Iio_of_not_isMin hb

variable [NoMinOrder α]

/--
lemma `Iic_sub_one_eq_Iio` / 引理 `Iic_sub_one_eq_Iio`

English:
lemma Iic_sub_one_eq_Iio
  given: (b : α)
  statement: Iic (b - 1) = Iio b
  proof: by
  simpa [pred_eq_sub_one] using Iic_pred_eq_Iio b

中文:
引理 Iic_sub_one_eq_Iio
  条件: (b : α)
  结论: Iic (b - 1) = Iio b
  证明: by
  simpa [pred_eq_sub_one] using Iic_pred_eq_Iio b

Depends on / 依赖: Iic_pred_eq_Iio, pred_eq_sub_one
-/
lemma Iic_sub_one_eq_Iio (b : α) : Iic (b - 1) = Iio b := by
  simpa [pred_eq_sub_one] using Iic_pred_eq_Iio b

end PredSubOrder

/-! ### One-sided interval towards `⊤` -/

section SuccAddOrder
variable [Add α] [SuccAddOrder α] {a : α}

/--
lemma `Ici_add_one_eq_Ioi_of_not_isMax` / 引理 `Ici_add_one_eq_Ioi_of_not_isMax`

English:
lemma Ici_add_one_eq_Ioi_of_not_isMax
  given: (ha : ¬ IsMax a)
  statement: Ici (a + 1) = Ioi a
  proof: by
  simpa [succ_eq_add_one] using Ici_succ_eq_Ioi_of_not_isMax ha

中文:
引理 Ici_add_one_eq_Ioi_of_not_isMax
  条件: (ha : ¬ IsMax a)
  结论: Ici (a + 1) = Ioi a
  证明: by
  simpa [succ_eq_add_one] using Ici_succ_eq_Ioi_of_not_isMax ha

Depends on / 依赖: Ici_succ_eq_Ioi_of_not_isMax, succ_eq_add_one
-/
lemma Ici_add_one_eq_Ioi_of_not_isMax (ha : ¬ IsMax a) : Ici (a + 1) = Ioi a := by
  simpa [succ_eq_add_one] using Ici_succ_eq_Ioi_of_not_isMax ha

variable [NoMaxOrder α]

/--
lemma `Ici_add_one_eq_Ioi` / 引理 `Ici_add_one_eq_Ioi`

English:
lemma Ici_add_one_eq_Ioi
  given: (a : α)
  statement: Ici (a + 1) = Ioi a
  proof: by
  simpa [succ_eq_add_one] using Ici_succ_eq_Ioi a

中文:
引理 Ici_add_one_eq_Ioi
  条件: (a : α)
  结论: Ici (a + 1) = Ioi a
  证明: by
  simpa [succ_eq_add_one] using Ici_succ_eq_Ioi a

Depends on / 依赖: Ici_succ_eq_Ioi, succ_eq_add_one
-/
lemma Ici_add_one_eq_Ioi (a : α) : Ici (a + 1) = Ioi a := by
  simpa [succ_eq_add_one] using Ici_succ_eq_Ioi a

end SuccAddOrder

section PredSubOrder
variable [Sub α] [PredSubOrder α] {a a : α}

/--
lemma `Ioi_sub_one_eq_Ici_of_not_isMin` / 引理 `Ioi_sub_one_eq_Ici_of_not_isMin`

English:
lemma Ioi_sub_one_eq_Ici_of_not_isMin
  given: (ha : ¬ IsMin a)
  statement: Ioi (a - 1) = Ici a
  proof: by
  simpa [pred_eq_sub_one] using Ioi_pred_eq_Ici_of_not_isMin ha

中文:
引理 Ioi_sub_one_eq_Ici_of_not_isMin
  条件: (ha : ¬ IsMin a)
  结论: Ioi (a - 1) = Ici a
  证明: by
  simpa [pred_eq_sub_one] using Ioi_pred_eq_Ici_of_not_isMin ha

Depends on / 依赖: Ioi_pred_eq_Ici_of_not_isMin, pred_eq_sub_one
-/
lemma Ioi_sub_one_eq_Ici_of_not_isMin (ha : ¬ IsMin a) : Ioi (a - 1) = Ici a := by
  simpa [pred_eq_sub_one] using Ioi_pred_eq_Ici_of_not_isMin ha

variable [NoMinOrder α]

/--
lemma `Ioi_sub_one_eq_Ici` / 引理 `Ioi_sub_one_eq_Ici`

English:
lemma Ioi_sub_one_eq_Ici
  given: (a : α)
  statement: Ioi (a - 1) = Ici a
  proof: by
  simpa [pred_eq_sub_one] using Ioi_pred_eq_Ici a

中文:
引理 Ioi_sub_one_eq_Ici
  条件: (a : α)
  结论: Ioi (a - 1) = Ici a
  证明: by
  simpa [pred_eq_sub_one] using Ioi_pred_eq_Ici a

Depends on / 依赖: Ioi_pred_eq_Ici, pred_eq_sub_one
-/
lemma Ioi_sub_one_eq_Ici (a : α) : Ioi (a - 1) = Ici a := by
  simpa [pred_eq_sub_one] using Ioi_pred_eq_Ici a

end PredSubOrder
end Set
