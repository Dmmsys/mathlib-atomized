/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.SuccPred.Basic

/-!
# Set intervals in a successor-predecessor order

This file proves relations between the various set intervals in a successor/predecessor order.

## Notes

Please keep in sync with:
* `Mathlib/Algebra/Order/Interval/Finset/SuccPred.lean`
* `Mathlib/Algebra/Order/Interval/Set/SuccPred.lean`
* `Mathlib/Order/Interval/Finset/SuccPred.lean`

## TODO

Copy over `insert` lemmas from `Mathlib/Order/Interval/Finset/Nat.lean`.
-/

public section

assert_not_exists MonoidWithZero

open Order

namespace Set
variable {α : Type*} [LinearOrder α]

/-! ### Two-sided intervals -/

section SuccOrder
variable [SuccOrder α] {a b : α}


/--
lemma `Ico_succ_left_eq_Ioo` / 引理 `Ico_succ_left_eq_Ioo`

English:
lemma Ico_succ_left_eq_Ioo
  given: (a b : α)
  statement: Ico (succ a) b = Ioo a b
  proof: by
  by_cases ha : IsMax a
  · rw [Ico_eq_empty (ha.mono <| le_succ _).not_lt, Ioo_eq_empty ha.not_lt]
  · ext x
    rw [mem_Ico]; rw [mem_Ioo]; rw [succ_le_iff_of_not_isMax ha]

中文:
引理 Ico_succ_left_eq_Ioo
  条件: (a b : α)
  结论: Ico (succ a) b = Ioo a b
  证明: by
  by_cases ha : IsMax a
  · rw [Ico_eq_empty (ha.mono <| le_succ _).not_lt, Ioo_eq_empty ha.not_lt]
  · ext x
    rw [mem_Ico]; rw [mem_Ioo]; rw [succ_le_iff_of_not_isMax ha]

Depends on / 依赖: Ico_eq_empty, Ioo_eq_empty, ha.mono, ha.not_lt, le_succ, mem_Ico, mem_Ioo, not_lt, succ_le_iff_of_not_isMax
-/
lemma Ico_succ_left_eq_Ioo (a b : α) : Ico (succ a) b = Ioo a b := by
  by_cases ha : IsMax a
  · rw [Ico_eq_empty (ha.mono <| le_succ _).not_lt, Ioo_eq_empty ha.not_lt]
  · ext x
    rw [mem_Ico]; rw [mem_Ioo]; rw [succ_le_iff_of_not_isMax ha]

/--
lemma `Icc_succ_left_eq_Ioc_of_not_isMax` / 引理 `Icc_succ_left_eq_Ioc_of_not_isMax`

English:
lemma Icc_succ_left_eq_Ioc_of_not_isMax
  given: (ha : ¬ IsMax a) (b : α)
  statement: Icc (succ a) b = Ioc a b
  proof: by
  ext x; rw [mem_Icc, mem_Ioc, succ_le_iff_of_not_isMax ha]

中文:
引理 Icc_succ_left_eq_Ioc_of_not_isMax
  条件: (ha : ¬ IsMax a) (b : α)
  结论: Icc (succ a) b = Ioc a b
  证明: by
  ext x; rw [mem_Icc, mem_Ioc, succ_le_iff_of_not_isMax ha]

Depends on / 依赖: mem_Icc, mem_Ioc, succ_le_iff_of_not_isMax
-/
lemma Icc_succ_left_eq_Ioc_of_not_isMax (ha : ¬ IsMax a) (b : α) : Icc (succ a) b = Ioc a b := by
  ext x; rw [mem_Icc, mem_Ioc, succ_le_iff_of_not_isMax ha]

/--
lemma `Ico_succ_right_eq_Icc_of_not_isMax` / 引理 `Ico_succ_right_eq_Icc_of_not_isMax`

English:
lemma Ico_succ_right_eq_Icc_of_not_isMax
  given: (hb : ¬ IsMax b) (a : α)
  statement: Ico a (succ b) = Icc a b
  proof: by
  ext x; rw [mem_Ico, mem_Icc, lt_succ_iff_of_not_isMax hb]

中文:
引理 Ico_succ_right_eq_Icc_of_not_isMax
  条件: (hb : ¬ IsMax b) (a : α)
  结论: Ico a (succ b) = Icc a b
  证明: by
  ext x; rw [mem_Ico, mem_Icc, lt_succ_iff_of_not_isMax hb]

Depends on / 依赖: lt_succ_iff_of_not_isMax, mem_Icc, mem_Ico
-/
lemma Ico_succ_right_eq_Icc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ico a (succ b) = Icc a b := by
  ext x; rw [mem_Ico, mem_Icc, lt_succ_iff_of_not_isMax hb]

/--
lemma `Ioo_succ_right_eq_Ioc_of_not_isMax` / 引理 `Ioo_succ_right_eq_Ioc_of_not_isMax`

English:
lemma Ioo_succ_right_eq_Ioc_of_not_isMax
  given: (hb : ¬ IsMax b) (a : α)
  statement: Ioo a (succ b) = Ioc a b
  proof: by
  ext x; rw [mem_Ioo, mem_Ioc, lt_succ_iff_of_not_isMax hb]

中文:
引理 Ioo_succ_right_eq_Ioc_of_not_isMax
  条件: (hb : ¬ IsMax b) (a : α)
  结论: Ioo a (succ b) = Ioc a b
  证明: by
  ext x; rw [mem_Ioo, mem_Ioc, lt_succ_iff_of_not_isMax hb]

Depends on / 依赖: lt_succ_iff_of_not_isMax, mem_Ioc, mem_Ioo
-/
lemma Ioo_succ_right_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ioo a (succ b) = Ioc a b := by
  ext x; rw [mem_Ioo, mem_Ioc, lt_succ_iff_of_not_isMax hb]

/--
lemma `Ico_succ_succ_eq_Ioc_of_not_isMax` / 引理 `Ico_succ_succ_eq_Ioc_of_not_isMax`

English:
lemma Ico_succ_succ_eq_Ioc_of_not_isMax
  given: (hb : ¬ IsMax b) (a : α)
  proof: by
  rw [Ico_succ_left_eq_Ioo]; rw [Ioo_succ_right_eq_Ioc_of_not_isMax hb]

中文:
引理 Ico_succ_succ_eq_Ioc_of_not_isMax
  条件: (hb : ¬ IsMax b) (a : α)
  证明: by
  rw [Ico_succ_left_eq_Ioo]; rw [Ioo_succ_right_eq_Ioc_of_not_isMax hb]

Depends on / 依赖: Ico_succ_left_eq_Ioo, Ioo_succ_right_eq_Ioc_of_not_isMax
-/
lemma Ico_succ_succ_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) :
    Ico (succ a) (succ b) = Ioc a b := by
  rw [Ico_succ_left_eq_Ioo]; rw [Ioo_succ_right_eq_Ioc_of_not_isMax hb]


/--
lemma `insert_Icc_succ_left_eq_Icc` / 引理 `insert_Icc_succ_left_eq_Icc`

English:
lemma insert_Icc_succ_left_eq_Icc
  given: (h : a <= b)
  statement: insert a (Icc (succ a) b) = Icc a b
  proof: by
  ext x; simp [or_and_left, eq_comm, ← le_iff_eq_or_succ_le]; aesop

中文:
引理 insert_Icc_succ_left_eq_Icc
  条件: (h : a <= b)
  结论: insert a (Icc (succ a) b) = Icc a b
  证明: by
  ext x; simp [or_and_left, eq_comm, ← le_iff_eq_or_succ_le]; aesop

Depends on / 依赖: eq_comm, le_iff_eq_or_succ_le, or_and_left
-/
lemma insert_Icc_succ_left_eq_Icc (h : a <= b) : insert a (Icc (succ a) b) = Icc a b := by
  ext x; simp [or_and_left, eq_comm, ← le_iff_eq_or_succ_le]; aesop

/--
lemma `insert_Icc_right_eq_Icc_succ` / 引理 `insert_Icc_right_eq_Icc_succ`

English:
lemma insert_Icc_right_eq_Icc_succ
  given: (h : a <= succ b)
  proof: by
  ext x; simp [or_and_left, le_succ_iff_eq_or_le]; simp_all

中文:
引理 insert_Icc_right_eq_Icc_succ
  条件: (h : a <= succ b)
  证明: by
  ext x; simp [or_and_left, le_succ_iff_eq_or_le]; simp_all

Depends on / 依赖: le_succ_iff_eq_or_le, or_and_left
-/
lemma insert_Icc_right_eq_Icc_succ (h : a <= succ b) :
    insert (succ b) (Icc a b) = Icc a (succ b) := by
  ext x; simp [or_and_left, le_succ_iff_eq_or_le]; simp_all

/--
lemma `insert_Ico_right_eq_Ico_succ_of_not_isMax` / 引理 `insert_Ico_right_eq_Ico_succ_of_not_isMax`

English:
lemma insert_Ico_right_eq_Ico_succ_of_not_isMax
  given: (h : a <= b) (hb : ¬ IsMax b)
  proof: by
  rw [Ico_succ_right_of_not_isMax hb]; rw [← Ico_insert_right h]

中文:
引理 insert_Ico_right_eq_Ico_succ_of_not_isMax
  条件: (h : a <= b) (hb : ¬ IsMax b)
  证明: by
  rw [Ico_succ_right_of_not_isMax hb]; rw [← Ico_insert_right h]

Depends on / 依赖: Ico_insert_right, Ico_succ_right_of_not_isMax
-/
lemma insert_Ico_right_eq_Ico_succ_of_not_isMax (h : a <= b) (hb : ¬ IsMax b) :
    insert b (Ico a b) = Ico a (succ b) := by
  rw [Ico_succ_right_of_not_isMax hb]; rw [← Ico_insert_right h]

/--
lemma `insert_Ico_succ_left_eq_Ico` / 引理 `insert_Ico_succ_left_eq_Ico`

English:
lemma insert_Ico_succ_left_eq_Ico
  given: (h : a < b)
  statement: insert a (Ico (succ a) b) = Ico a b
  proof: by
  rw [Ico_succ_left_of_not_isMax h.not_isMax]; rw [← Ioo_insert_left h]

中文:
引理 insert_Ico_succ_left_eq_Ico
  条件: (h : a < b)
  结论: insert a (Ico (succ a) b) = Ico a b
  证明: by
  rw [Ico_succ_left_of_not_isMax h.not_isMax]; rw [← Ioo_insert_left h]

Depends on / 依赖: Ico_succ_left_of_not_isMax, Ioo_insert_left, h.not_isMax, not_isMax
-/
lemma insert_Ico_succ_left_eq_Ico (h : a < b) : insert a (Ico (succ a) b) = Ico a b := by
  rw [Ico_succ_left_of_not_isMax h.not_isMax]; rw [← Ioo_insert_left h]

/--
lemma `insert_Ioc_right_eq_Ioc_succ_of_not_isMax` / 引理 `insert_Ioc_right_eq_Ioc_succ_of_not_isMax`

English:
lemma insert_Ioc_right_eq_Ioc_succ_of_not_isMax
  given: (h : a <= b) (hb : ¬ IsMax b)
  proof: by
  ext x; simp +contextual [or_and_left, le_succ_iff_eq_or_le, lt_succ_of_le_of_not_isMax h hb]

中文:
引理 insert_Ioc_right_eq_Ioc_succ_of_not_isMax
  条件: (h : a <= b) (hb : ¬ IsMax b)
  证明: by
  ext x; simp +contextual [or_and_left, le_succ_iff_eq_or_le, lt_succ_of_le_of_not_isMax h hb]

Depends on / 依赖: contextual, le_succ_iff_eq_or_le, lt_succ_of_le_of_not_isMax, or_and_left
-/
lemma insert_Ioc_right_eq_Ioc_succ_of_not_isMax (h : a <= b) (hb : ¬ IsMax b) :
    insert (succ b) (Ioc a b) = Ioc a (succ b) := by
  ext x; simp +contextual [or_and_left, le_succ_iff_eq_or_le, lt_succ_of_le_of_not_isMax h hb]

/--
lemma `insert_Ioc_succ_left_eq_Ioc` / 引理 `insert_Ioc_succ_left_eq_Ioc`

English:
lemma insert_Ioc_succ_left_eq_Ioc
  given: (h : a < b)
  statement: insert (succ a) (Ioc (succ a) b) = Ioc a b
  proof: by
  rw [Ioc_insert_left (succ_le_of_lt h)]; rw [Icc_succ_left_of_not_isMax h.not_isMax]

中文:
引理 insert_Ioc_succ_left_eq_Ioc
  条件: (h : a < b)
  结论: insert (succ a) (Ioc (succ a) b) = Ioc a b
  证明: by
  rw [Ioc_insert_left (succ_le_of_lt h)]; rw [Icc_succ_left_of_not_isMax h.not_isMax]

Depends on / 依赖: Icc_succ_left_of_not_isMax, Ioc_insert_left, h.not_isMax, not_isMax, succ_le_of_lt
-/
lemma insert_Ioc_succ_left_eq_Ioc (h : a < b) : insert (succ a) (Ioc (succ a) b) = Ioc a b := by
  rw [Ioc_insert_left (succ_le_of_lt h)]; rw [Icc_succ_left_of_not_isMax h.not_isMax]

/-!
#### Orders with no maximal elements

##### Equalities of intervals
-/

variable [NoMaxOrder α]

/--
lemma `Icc_succ_left_eq_Ioc` / 引理 `Icc_succ_left_eq_Ioc`

English:
lemma Icc_succ_left_eq_Ioc
  given: (a b : α)
  statement: Icc (succ a) b = Ioc a b
  proof: Icc_succ_left_eq_Ioc_of_not_isMax (not_isMax _) _

中文:
引理 Icc_succ_left_eq_Ioc
  条件: (a b : α)
  结论: Icc (succ a) b = Ioc a b
  证明: Icc_succ_left_eq_Ioc_of_not_isMax (not_isMax _) _

Depends on / 依赖: Icc_succ_left_eq_Ioc_of_not_isMax, not_isMax
-/
lemma Icc_succ_left_eq_Ioc (a b : α) : Icc (succ a) b = Ioc a b :=
  Icc_succ_left_eq_Ioc_of_not_isMax (not_isMax _) _

/--
lemma `Ico_succ_right_eq_Icc` / 引理 `Ico_succ_right_eq_Icc`

English:
lemma Ico_succ_right_eq_Icc
  given: (a b : α)
  statement: Ico a (succ b) = Icc a b
  proof: Ico_succ_right_eq_Icc_of_not_isMax (not_isMax _) _

中文:
引理 Ico_succ_right_eq_Icc
  条件: (a b : α)
  结论: Ico a (succ b) = Icc a b
  证明: Ico_succ_right_eq_Icc_of_not_isMax (not_isMax _) _

Depends on / 依赖: Ico_succ_right_eq_Icc_of_not_isMax, not_isMax
-/
lemma Ico_succ_right_eq_Icc (a b : α) : Ico a (succ b) = Icc a b :=
  Ico_succ_right_eq_Icc_of_not_isMax (not_isMax _) _

/--
lemma `Ioo_succ_right_eq_Ioc` / 引理 `Ioo_succ_right_eq_Ioc`

English:
lemma Ioo_succ_right_eq_Ioc
  given: (a b : α)
  statement: Ioo a (succ b) = Ioc a b
  proof: Ioo_succ_right_eq_Ioc_of_not_isMax (not_isMax _) _

中文:
引理 Ioo_succ_right_eq_Ioc
  条件: (a b : α)
  结论: Ioo a (succ b) = Ioc a b
  证明: Ioo_succ_right_eq_Ioc_of_not_isMax (not_isMax _) _

Depends on / 依赖: Ioo_succ_right_eq_Ioc_of_not_isMax, not_isMax
-/
lemma Ioo_succ_right_eq_Ioc (a b : α) : Ioo a (succ b) = Ioc a b :=
  Ioo_succ_right_eq_Ioc_of_not_isMax (not_isMax _) _

/--
lemma `Ico_succ_succ_eq_Ioc` / 引理 `Ico_succ_succ_eq_Ioc`

English:
lemma Ico_succ_succ_eq_Ioc
  given: (a b : α)
  statement: Ico (succ a) (succ b) = Ioc a b
  proof: Ico_succ_succ_eq_Ioc_of_not_isMax (not_isMax _) _

中文:
引理 Ico_succ_succ_eq_Ioc
  条件: (a b : α)
  结论: Ico (succ a) (succ b) = Ioc a b
  证明: Ico_succ_succ_eq_Ioc_of_not_isMax (not_isMax _) _

Depends on / 依赖: Ico_succ_succ_eq_Ioc_of_not_isMax, not_isMax
-/
lemma Ico_succ_succ_eq_Ioc (a b : α) : Ico (succ a) (succ b) = Ioc a b :=
  Ico_succ_succ_eq_Ioc_of_not_isMax (not_isMax _) _


/--
lemma `insert_Ico_right_eq_Ico_succ` / 引理 `insert_Ico_right_eq_Ico_succ`

English:
lemma insert_Ico_right_eq_Ico_succ
  given: (h : a <= b)
  statement: insert b (Ico a b) = Ico a (succ b)
  proof: insert_Ico_right_eq_Ico_succ_of_not_isMax h (not_isMax _)

中文:
引理 insert_Ico_right_eq_Ico_succ
  条件: (h : a <= b)
  结论: insert b (Ico a b) = Ico a (succ b)
  证明: insert_Ico_right_eq_Ico_succ_of_not_isMax h (not_isMax _)

Depends on / 依赖: insert_Ico_right_eq_Ico_succ_of_not_isMax, not_isMax
-/
lemma insert_Ico_right_eq_Ico_succ (h : a <= b) : insert b (Ico a b) = Ico a (succ b) :=
  insert_Ico_right_eq_Ico_succ_of_not_isMax h (not_isMax _)

/--
lemma `insert_Ioc_right_eq_Ioc_succ` / 引理 `insert_Ioc_right_eq_Ioc_succ`

English:
lemma insert_Ioc_right_eq_Ioc_succ
  given: (h : a <= b)
  statement: insert (succ b) (Ioc a b) = Ioc a (succ b)
  proof: insert_Ioc_right_eq_Ioc_succ_of_not_isMax h (not_isMax _)

中文:
引理 insert_Ioc_right_eq_Ioc_succ
  条件: (h : a <= b)
  结论: insert (succ b) (Ioc a b) = Ioc a (succ b)
  证明: insert_Ioc_right_eq_Ioc_succ_of_not_isMax h (not_isMax _)

Depends on / 依赖: insert_Ioc_right_eq_Ioc_succ_of_not_isMax, not_isMax
-/
lemma insert_Ioc_right_eq_Ioc_succ (h : a <= b) : insert (succ b) (Ioc a b) = Ioc a (succ b) :=
  insert_Ioc_right_eq_Ioc_succ_of_not_isMax h (not_isMax _)

end SuccOrder

section PredOrder
variable [PredOrder α] {a b : α}


/--
lemma `Ioc_pred_right_eq_Ioo` / 引理 `Ioc_pred_right_eq_Ioo`

English:
lemma Ioc_pred_right_eq_Ioo
  given: (a b : α)
  statement: Ioc a (pred b) = Ioo a b
  proof: by
  by_cases hb : IsMin b
  · rw [Ioc_eq_empty (hb.mono <| pred_le _).not_lt, Ioo_eq_empty hb.not_lt]
  · ext x
    rw [mem_Ioc]; rw [mem_Ioo]; rw [le_pred_iff_of_not_isMin hb]

中文:
引理 Ioc_pred_right_eq_Ioo
  条件: (a b : α)
  结论: Ioc a (pred b) = Ioo a b
  证明: by
  by_cases hb : IsMin b
  · rw [Ioc_eq_empty (hb.mono <| pred_le _).not_lt, Ioo_eq_empty hb.not_lt]
  · ext x
    rw [mem_Ioc]; rw [mem_Ioo]; rw [le_pred_iff_of_not_isMin hb]

Depends on / 依赖: Ioc_eq_empty, Ioo_eq_empty, hb.mono, hb.not_lt, le_pred_iff_of_not_isMin, mem_Ioc, mem_Ioo, not_lt, pred_le
-/
lemma Ioc_pred_right_eq_Ioo (a b : α) : Ioc a (pred b) = Ioo a b := by
  by_cases hb : IsMin b
  · rw [Ioc_eq_empty (hb.mono <| pred_le _).not_lt, Ioo_eq_empty hb.not_lt]
  · ext x
    rw [mem_Ioc]; rw [mem_Ioo]; rw [le_pred_iff_of_not_isMin hb]

/--
lemma `Icc_pred_right_eq_Ico_of_not_isMin` / 引理 `Icc_pred_right_eq_Ico_of_not_isMin`

English:
lemma Icc_pred_right_eq_Ico_of_not_isMin
  given: (hb : ¬ IsMin b) (a : α)
  statement: Icc a (pred b) = Ico a b
  proof: by
  ext x; rw [mem_Icc, mem_Ico, le_pred_iff_of_not_isMin hb]

中文:
引理 Icc_pred_right_eq_Ico_of_not_isMin
  条件: (hb : ¬ IsMin b) (a : α)
  结论: Icc a (pred b) = Ico a b
  证明: by
  ext x; rw [mem_Icc, mem_Ico, le_pred_iff_of_not_isMin hb]

Depends on / 依赖: le_pred_iff_of_not_isMin, mem_Icc, mem_Ico
-/
lemma Icc_pred_right_eq_Ico_of_not_isMin (hb : ¬ IsMin b) (a : α) : Icc a (pred b) = Ico a b := by
  ext x; rw [mem_Icc, mem_Ico, le_pred_iff_of_not_isMin hb]

/--
lemma `Ioc_pred_left_eq_Icc_of_not_isMin` / 引理 `Ioc_pred_left_eq_Icc_of_not_isMin`

English:
lemma Ioc_pred_left_eq_Icc_of_not_isMin
  given: (ha : ¬ IsMin a) (b : α)
  statement: Ioc (pred a) b = Icc a b
  proof: by
  ext x; rw [mem_Ioc, mem_Icc, pred_lt_iff_of_not_isMin ha]

中文:
引理 Ioc_pred_left_eq_Icc_of_not_isMin
  条件: (ha : ¬ IsMin a) (b : α)
  结论: Ioc (pred a) b = Icc a b
  证明: by
  ext x; rw [mem_Ioc, mem_Icc, pred_lt_iff_of_not_isMin ha]

Depends on / 依赖: mem_Icc, mem_Ioc, pred_lt_iff_of_not_isMin
-/
lemma Ioc_pred_left_eq_Icc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioc (pred a) b = Icc a b := by
  ext x; rw [mem_Ioc, mem_Icc, pred_lt_iff_of_not_isMin ha]

/--
lemma `Ioo_pred_left_eq_Ioc_of_not_isMin` / 引理 `Ioo_pred_left_eq_Ioc_of_not_isMin`

English:
lemma Ioo_pred_left_eq_Ioc_of_not_isMin
  given: (ha : ¬ IsMin a) (b : α)
  statement: Ioo (pred a) b = Ico a b
  proof: by
  ext x; rw [mem_Ioo, mem_Ico, pred_lt_iff_of_not_isMin ha]

中文:
引理 Ioo_pred_left_eq_Ioc_of_not_isMin
  条件: (ha : ¬ IsMin a) (b : α)
  结论: Ioo (pred a) b = Ico a b
  证明: by
  ext x; rw [mem_Ioo, mem_Ico, pred_lt_iff_of_not_isMin ha]

Depends on / 依赖: mem_Ico, mem_Ioo, pred_lt_iff_of_not_isMin
-/
lemma Ioo_pred_left_eq_Ioc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioo (pred a) b = Ico a b := by
  ext x; rw [mem_Ioo, mem_Ico, pred_lt_iff_of_not_isMin ha]

/--
lemma `Ioc_pred_pred_eq_Ico_of_not_isMin` / 引理 `Ioc_pred_pred_eq_Ico_of_not_isMin`

English:
lemma Ioc_pred_pred_eq_Ico_of_not_isMin
  given: (ha : ¬ IsMin a) (b : α)
  proof: by
  rw [Ioc_pred_right_eq_Ioo]; rw [Ioo_pred_left_eq_Ioc_of_not_isMin ha]

中文:
引理 Ioc_pred_pred_eq_Ico_of_not_isMin
  条件: (ha : ¬ IsMin a) (b : α)
  证明: by
  rw [Ioc_pred_right_eq_Ioo]; rw [Ioo_pred_left_eq_Ioc_of_not_isMin ha]

Depends on / 依赖: Ioc_pred_right_eq_Ioo, Ioo_pred_left_eq_Ioc_of_not_isMin
-/
lemma Ioc_pred_pred_eq_Ico_of_not_isMin (ha : ¬ IsMin a) (b : α) :
    Ioc (pred a) (pred b) = Ico a b := by
  rw [Ioc_pred_right_eq_Ioo]; rw [Ioo_pred_left_eq_Ioc_of_not_isMin ha]


/--
lemma `insert_Icc_pred_right_eq_Icc` / 引理 `insert_Icc_pred_right_eq_Icc`

English:
lemma insert_Icc_pred_right_eq_Icc
  given: (h : a <= b)
  statement: insert b (Icc a (pred b)) = Icc a b
  proof: by
  ext x; simp [or_and_left, ← le_iff_eq_or_le_pred]; simp_all

中文:
引理 insert_Icc_pred_right_eq_Icc
  条件: (h : a <= b)
  结论: insert b (Icc a (pred b)) = Icc a b
  证明: by
  ext x; simp [or_and_left, ← le_iff_eq_or_le_pred]; simp_all

Depends on / 依赖: le_iff_eq_or_le_pred, or_and_left
-/
lemma insert_Icc_pred_right_eq_Icc (h : a <= b) : insert b (Icc a (pred b)) = Icc a b := by
  ext x; simp [or_and_left, ← le_iff_eq_or_le_pred]; simp_all

/--
lemma `insert_Icc_left_eq_Icc_pred` / 引理 `insert_Icc_left_eq_Icc_pred`

English:
lemma insert_Icc_left_eq_Icc_pred
  given: (h : pred a <= b)
  proof: by
  ext x; simp [or_and_left, pred_le_iff_eq_or_le]; simp_all

中文:
引理 insert_Icc_left_eq_Icc_pred
  条件: (h : pred a <= b)
  证明: by
  ext x; simp [or_and_left, pred_le_iff_eq_or_le]; simp_all

Depends on / 依赖: or_and_left, pred_le_iff_eq_or_le
-/
lemma insert_Icc_left_eq_Icc_pred (h : pred a <= b) :
    insert (pred a) (Icc a b) = Icc (pred a) b := by
  ext x; simp [or_and_left, pred_le_iff_eq_or_le]; simp_all

/--
lemma `insert_Ioc_left_eq_Ioc_pred_of_not_isMin` / 引理 `insert_Ioc_left_eq_Ioc_pred_of_not_isMin`

English:
lemma insert_Ioc_left_eq_Ioc_pred_of_not_isMin
  given: (h : a <= b) (ha : ¬ IsMin a)
  proof: by
  rw [Ioc_pred_left_of_not_isMin ha]; rw [Ioc_insert_left h]

中文:
引理 insert_Ioc_left_eq_Ioc_pred_of_not_isMin
  条件: (h : a <= b) (ha : ¬ IsMin a)
  证明: by
  rw [Ioc_pred_left_of_not_isMin ha]; rw [Ioc_insert_left h]

Depends on / 依赖: Ioc_insert_left, Ioc_pred_left_of_not_isMin
-/
lemma insert_Ioc_left_eq_Ioc_pred_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) :
    insert a (Ioc a b) = Ioc (pred a) b := by
  rw [Ioc_pred_left_of_not_isMin ha]; rw [Ioc_insert_left h]

/--
lemma `insert_Ioc_pred_right_eq_Ioc` / 引理 `insert_Ioc_pred_right_eq_Ioc`

English:
lemma insert_Ioc_pred_right_eq_Ioc
  given: (h : a < b)
  statement: insert b (Ioc a (pred b)) = Ioc a b
  proof: by
  rw [Ioc_pred_right_of_not_isMin h.not_isMin]; rw [Ioo_insert_right h]

中文:
引理 insert_Ioc_pred_right_eq_Ioc
  条件: (h : a < b)
  结论: insert b (Ioc a (pred b)) = Ioc a b
  证明: by
  rw [Ioc_pred_right_of_not_isMin h.not_isMin]; rw [Ioo_insert_right h]

Depends on / 依赖: Ioc_pred_right_of_not_isMin, Ioo_insert_right, h.not_isMin, not_isMin
-/
lemma insert_Ioc_pred_right_eq_Ioc (h : a < b) : insert b (Ioc a (pred b)) = Ioc a b := by
  rw [Ioc_pred_right_of_not_isMin h.not_isMin]; rw [Ioo_insert_right h]

/--
lemma `insert_Ico_left_eq_Ico_pred_of_not_isMin` / 引理 `insert_Ico_left_eq_Ico_pred_of_not_isMin`

English:
lemma insert_Ico_left_eq_Ico_pred_of_not_isMin
  given: (h : a <= b) (ha : ¬ IsMin a)
  proof: by
  ext x; simp +contextual [or_and_left, pred_le_iff_eq_or_le, pred_lt_of_le_of_not_isMin h ha]

中文:
引理 insert_Ico_left_eq_Ico_pred_of_not_isMin
  条件: (h : a <= b) (ha : ¬ IsMin a)
  证明: by
  ext x; simp +contextual [or_and_left, pred_le_iff_eq_or_le, pred_lt_of_le_of_not_isMin h ha]

Depends on / 依赖: contextual, or_and_left, pred_le_iff_eq_or_le, pred_lt_of_le_of_not_isMin
-/
lemma insert_Ico_left_eq_Ico_pred_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) :
    insert (pred a) (Ico a b) = Ico (pred a) b := by
  ext x; simp +contextual [or_and_left, pred_le_iff_eq_or_le, pred_lt_of_le_of_not_isMin h ha]

/--
lemma `insert_Ico_pred_right_eq_Ico` / 引理 `insert_Ico_pred_right_eq_Ico`

English:
lemma insert_Ico_pred_right_eq_Ico
  given: (h : a < b)
  statement: insert (pred b) (Ico a (pred b)) = Ico a b
  proof: by
  rw [Ico_insert_right (le_pred_of_lt h)]; rw [Icc_pred_right_of_not_isMin h.not_isMin]

中文:
引理 insert_Ico_pred_right_eq_Ico
  条件: (h : a < b)
  结论: insert (pred b) (Ico a (pred b)) = Ico a b
  证明: by
  rw [Ico_insert_right (le_pred_of_lt h)]; rw [Icc_pred_right_of_not_isMin h.not_isMin]

Depends on / 依赖: Icc_pred_right_of_not_isMin, Ico_insert_right, h.not_isMin, le_pred_of_lt, not_isMin
-/
lemma insert_Ico_pred_right_eq_Ico (h : a < b) : insert (pred b) (Ico a (pred b)) = Ico a b := by
  rw [Ico_insert_right (le_pred_of_lt h)]; rw [Icc_pred_right_of_not_isMin h.not_isMin]

/-!
#### Orders with no minimal elements

##### Equalities of intervals
-/

variable [NoMinOrder α]

/--
lemma `Icc_pred_right_eq_Ico` / 引理 `Icc_pred_right_eq_Ico`

English:
lemma Icc_pred_right_eq_Ico
  given: (a b : α)
  statement: Icc a (pred b) = Ico a b
  proof: Icc_pred_right_eq_Ico_of_not_isMin (not_isMin _) _

中文:
引理 Icc_pred_right_eq_Ico
  条件: (a b : α)
  结论: Icc a (pred b) = Ico a b
  证明: Icc_pred_right_eq_Ico_of_not_isMin (not_isMin _) _

Depends on / 依赖: Icc_pred_right_eq_Ico_of_not_isMin, not_isMin
-/
lemma Icc_pred_right_eq_Ico (a b : α) : Icc a (pred b) = Ico a b :=
  Icc_pred_right_eq_Ico_of_not_isMin (not_isMin _) _

/--
lemma `Ioc_pred_left_eq_Icc` / 引理 `Ioc_pred_left_eq_Icc`

English:
lemma Ioc_pred_left_eq_Icc
  given: (a b : α)
  statement: Ioc (pred a) b = Icc a b
  proof: Ioc_pred_left_eq_Icc_of_not_isMin (not_isMin _) _

中文:
引理 Ioc_pred_left_eq_Icc
  条件: (a b : α)
  结论: Ioc (pred a) b = Icc a b
  证明: Ioc_pred_left_eq_Icc_of_not_isMin (not_isMin _) _

Depends on / 依赖: Ioc_pred_left_eq_Icc_of_not_isMin, not_isMin
-/
lemma Ioc_pred_left_eq_Icc (a b : α) : Ioc (pred a) b = Icc a b :=
  Ioc_pred_left_eq_Icc_of_not_isMin (not_isMin _) _

/--
lemma `Ioo_pred_left_eq_Ioc` / 引理 `Ioo_pred_left_eq_Ioc`

English:
lemma Ioo_pred_left_eq_Ioc
  given: (a b : α)
  statement: Ioo (pred a) b = Ico a b
  proof: Ioo_pred_left_eq_Ioc_of_not_isMin (not_isMin _) _

中文:
引理 Ioo_pred_left_eq_Ioc
  条件: (a b : α)
  结论: Ioo (pred a) b = Ico a b
  证明: Ioo_pred_left_eq_Ioc_of_not_isMin (not_isMin _) _

Depends on / 依赖: Ioo_pred_left_eq_Ioc_of_not_isMin, not_isMin
-/
lemma Ioo_pred_left_eq_Ioc (a b : α) : Ioo (pred a) b = Ico a b :=
  Ioo_pred_left_eq_Ioc_of_not_isMin (not_isMin _) _

/--
lemma `Ioc_pred_pred_eq_Ico` / 引理 `Ioc_pred_pred_eq_Ico`

English:
lemma Ioc_pred_pred_eq_Ico
  given: (a b : α)
  statement: Ioc (pred a) (pred b) = Ico a b
  proof: Ioc_pred_pred_eq_Ico_of_not_isMin (not_isMin _) _

中文:
引理 Ioc_pred_pred_eq_Ico
  条件: (a b : α)
  结论: Ioc (pred a) (pred b) = Ico a b
  证明: Ioc_pred_pred_eq_Ico_of_not_isMin (not_isMin _) _

Depends on / 依赖: Ioc_pred_pred_eq_Ico_of_not_isMin, not_isMin
-/
lemma Ioc_pred_pred_eq_Ico (a b : α) : Ioc (pred a) (pred b) = Ico a b :=
  Ioc_pred_pred_eq_Ico_of_not_isMin (not_isMin _) _


/--
lemma `insert_Ioc_left_eq_Ioc_pred` / 引理 `insert_Ioc_left_eq_Ioc_pred`

English:
lemma insert_Ioc_left_eq_Ioc_pred
  given: (h : a <= b)
  statement: insert a (Ioc a b) = Ioc (pred a) b
  proof: insert_Ioc_left_eq_Ioc_pred_of_not_isMin h (not_isMin _)

中文:
引理 insert_Ioc_left_eq_Ioc_pred
  条件: (h : a <= b)
  结论: insert a (Ioc a b) = Ioc (pred a) b
  证明: insert_Ioc_left_eq_Ioc_pred_of_not_isMin h (not_isMin _)

Depends on / 依赖: insert_Ioc_left_eq_Ioc_pred_of_not_isMin, not_isMin
-/
lemma insert_Ioc_left_eq_Ioc_pred (h : a <= b) : insert a (Ioc a b) = Ioc (pred a) b :=
  insert_Ioc_left_eq_Ioc_pred_of_not_isMin h (not_isMin _)

/--
lemma `insert_Ico_left_eq_Ico_pred` / 引理 `insert_Ico_left_eq_Ico_pred`

English:
lemma insert_Ico_left_eq_Ico_pred
  given: (h : a <= b)
  statement: insert (pred a) (Ico a b) = Ico (pred a) b
  proof: insert_Ico_left_eq_Ico_pred_of_not_isMin h (not_isMin _)

中文:
引理 insert_Ico_left_eq_Ico_pred
  条件: (h : a <= b)
  结论: insert (pred a) (Ico a b) = Ico (pred a) b
  证明: insert_Ico_left_eq_Ico_pred_of_not_isMin h (not_isMin _)

Depends on / 依赖: insert_Ico_left_eq_Ico_pred_of_not_isMin, not_isMin
-/
lemma insert_Ico_left_eq_Ico_pred (h : a <= b) : insert (pred a) (Ico a b) = Ico (pred a) b :=
  insert_Ico_left_eq_Ico_pred_of_not_isMin h (not_isMin _)

end PredOrder

section SuccPredOrder
variable [SuccOrder α] [PredOrder α] [Nontrivial α]

/--
lemma `Icc_succ_pred_eq_Ioo` / 引理 `Icc_succ_pred_eq_Ioo`

English:
lemma Icc_succ_pred_eq_Ioo
  given: (a b : α)
  statement: Icc (succ a) (pred b) = Ioo a b
  proof: by
  by_cases hb : IsMin b
  · rw [Icc_eq_empty, Ioo_eq_empty hb.not_lt]
exact fun h => not_isMin_succ _ hb.mono h.trans pred_le _
  · rw [Icc_pred_right_eq_Ico_of_not_isMin hb, Ico_succ_left_eq_Ioo]

中文:
引理 Icc_succ_pred_eq_Ioo
  条件: (a b : α)
  结论: Icc (succ a) (pred b) = Ioo a b
  证明: by
  by_cases hb : IsMin b
  · rw [Icc_eq_empty, Ioo_eq_empty hb.not_lt]
exact fun h => not_isMin_succ _ hb.mono h.trans pred_le _
  · rw [Icc_pred_right_eq_Ico_of_not_isMin hb, Ico_succ_left_eq_Ioo]

Depends on / 依赖: Icc_eq_empty, Icc_pred_right_eq_Ico_of_not_isMin, Ico_succ_left_eq_Ioo, Ioo_eq_empty, h.trans, hb.mono, hb.not_lt, not_isMin_succ, not_lt, pred_le
-/
lemma Icc_succ_pred_eq_Ioo (a b : α) : Icc (succ a) (pred b) = Ioo a b := by
  by_cases hb : IsMin b
  · rw [Icc_eq_empty, Ioo_eq_empty hb.not_lt]
exact fun h => not_isMin_succ _ hb.mono h.trans pred_le _
  · rw [Icc_pred_right_eq_Ico_of_not_isMin hb, Ico_succ_left_eq_Ioo]

end SuccPredOrder

/-! ### One-sided interval towards `⊥` -/

section SuccOrder
variable [SuccOrder α] {b : α}

/--
lemma `Iio_succ_eq_Iic_of_not_isMax` / 引理 `Iio_succ_eq_Iic_of_not_isMax`

English:
lemma Iio_succ_eq_Iic_of_not_isMax
  given: (hb : ¬ IsMax b)
  statement: Iio (succ b) = Iic b
  proof: by
  ext x; rw [mem_Iio, mem_Iic, lt_succ_iff_of_not_isMax hb]

中文:
引理 Iio_succ_eq_Iic_of_not_isMax
  条件: (hb : ¬ IsMax b)
  结论: Iio (succ b) = Iic b
  证明: by
  ext x; rw [mem_Iio, mem_Iic, lt_succ_iff_of_not_isMax hb]

Depends on / 依赖: lt_succ_iff_of_not_isMax, mem_Iic, mem_Iio
-/
lemma Iio_succ_eq_Iic_of_not_isMax (hb : ¬ IsMax b) : Iio (succ b) = Iic b := by
  ext x; rw [mem_Iio, mem_Iic, lt_succ_iff_of_not_isMax hb]

variable [NoMaxOrder α]

/--
lemma `Iio_succ_eq_Iic` / 引理 `Iio_succ_eq_Iic`

English:
lemma Iio_succ_eq_Iic
  given: (b : α)
  statement: Iio (succ b) = Iic b
  proof: Iio_succ_eq_Iic_of_not_isMax (not_isMax _)

中文:
引理 Iio_succ_eq_Iic
  条件: (b : α)
  结论: Iio (succ b) = Iic b
  证明: Iio_succ_eq_Iic_of_not_isMax (not_isMax _)

Depends on / 依赖: Iio_succ_eq_Iic_of_not_isMax, not_isMax
-/
lemma Iio_succ_eq_Iic (b : α) : Iio (succ b) = Iic b := Iio_succ_eq_Iic_of_not_isMax (not_isMax _)

end SuccOrder

section PredOrder
variable [PredOrder α] {a b : α}

/--
lemma `Iic_pred_eq_Iio_of_not_isMin` / 引理 `Iic_pred_eq_Iio_of_not_isMin`

English:
lemma Iic_pred_eq_Iio_of_not_isMin
  given: (hb : ¬ IsMin b)
  statement: Iic (pred b) = Iio b
  proof: by
  ext x; rw [mem_Iic, mem_Iio, le_pred_iff_of_not_isMin hb]

中文:
引理 Iic_pred_eq_Iio_of_not_isMin
  条件: (hb : ¬ IsMin b)
  结论: Iic (pred b) = Iio b
  证明: by
  ext x; rw [mem_Iic, mem_Iio, le_pred_iff_of_not_isMin hb]

Depends on / 依赖: le_pred_iff_of_not_isMin, mem_Iic, mem_Iio
-/
lemma Iic_pred_eq_Iio_of_not_isMin (hb : ¬ IsMin b) : Iic (pred b) = Iio b := by
  ext x; rw [mem_Iic, mem_Iio, le_pred_iff_of_not_isMin hb]

variable [NoMinOrder α]

/--
lemma `Iic_pred_eq_Iio` / 引理 `Iic_pred_eq_Iio`

English:
lemma Iic_pred_eq_Iio
  given: (b : α)
  statement: Iic (pred b) = Iio b
  proof: Iic_pred_eq_Iio_of_not_isMin (not_isMin _)

中文:
引理 Iic_pred_eq_Iio
  条件: (b : α)
  结论: Iic (pred b) = Iio b
  证明: Iic_pred_eq_Iio_of_not_isMin (not_isMin _)

Depends on / 依赖: Iic_pred_eq_Iio_of_not_isMin, not_isMin
-/
lemma Iic_pred_eq_Iio (b : α) : Iic (pred b) = Iio b := Iic_pred_eq_Iio_of_not_isMin (not_isMin _)

end PredOrder

/-! ### One-sided interval towards `⊤` -/

section SuccOrder
variable [SuccOrder α] {a : α}

/--
lemma `Ici_succ_eq_Ioi_of_not_isMax` / 引理 `Ici_succ_eq_Ioi_of_not_isMax`

English:
lemma Ici_succ_eq_Ioi_of_not_isMax
  given: (ha : ¬ IsMax a)
  statement: Ici (succ a) = Ioi a
  proof: by
  ext x; rw [mem_Ici, mem_Ioi, succ_le_iff_of_not_isMax ha]

中文:
引理 Ici_succ_eq_Ioi_of_not_isMax
  条件: (ha : ¬ IsMax a)
  结论: Ici (succ a) = Ioi a
  证明: by
  ext x; rw [mem_Ici, mem_Ioi, succ_le_iff_of_not_isMax ha]

Depends on / 依赖: mem_Ici, mem_Ioi, succ_le_iff_of_not_isMax
-/
lemma Ici_succ_eq_Ioi_of_not_isMax (ha : ¬ IsMax a) : Ici (succ a) = Ioi a := by
  ext x; rw [mem_Ici, mem_Ioi, succ_le_iff_of_not_isMax ha]

variable [NoMaxOrder α]

/--
lemma `Ici_succ_eq_Ioi` / 引理 `Ici_succ_eq_Ioi`

English:
lemma Ici_succ_eq_Ioi
  given: (a : α)
  statement: Ici (succ a) = Ioi a
  proof: Ici_succ_eq_Ioi_of_not_isMax (not_isMax _)

中文:
引理 Ici_succ_eq_Ioi
  条件: (a : α)
  结论: Ici (succ a) = Ioi a
  证明: Ici_succ_eq_Ioi_of_not_isMax (not_isMax _)

Depends on / 依赖: Ici_succ_eq_Ioi_of_not_isMax, not_isMax
-/
lemma Ici_succ_eq_Ioi (a : α) : Ici (succ a) = Ioi a := Ici_succ_eq_Ioi_of_not_isMax (not_isMax _)

end SuccOrder

section PredOrder
variable [PredOrder α] {a a : α}

/--
lemma `Ioi_pred_eq_Ici_of_not_isMin` / 引理 `Ioi_pred_eq_Ici_of_not_isMin`

English:
lemma Ioi_pred_eq_Ici_of_not_isMin
  given: (ha : ¬ IsMin a)
  statement: Ioi (pred a) = Ici a
  proof: by
  ext x; rw [mem_Ioi, mem_Ici, pred_lt_iff_of_not_isMin ha]

中文:
引理 Ioi_pred_eq_Ici_of_not_isMin
  条件: (ha : ¬ IsMin a)
  结论: Ioi (pred a) = Ici a
  证明: by
  ext x; rw [mem_Ioi, mem_Ici, pred_lt_iff_of_not_isMin ha]

Depends on / 依赖: mem_Ici, mem_Ioi, pred_lt_iff_of_not_isMin
-/
lemma Ioi_pred_eq_Ici_of_not_isMin (ha : ¬ IsMin a) : Ioi (pred a) = Ici a := by
  ext x; rw [mem_Ioi, mem_Ici, pred_lt_iff_of_not_isMin ha]

variable [NoMinOrder α]

/--
lemma `Ioi_pred_eq_Ici` / 引理 `Ioi_pred_eq_Ici`

English:
lemma Ioi_pred_eq_Ici
  given: (a : α)
  statement: Ioi (pred a) = Ici a
  proof: Ioi_pred_eq_Ici_of_not_isMin (not_isMin _)

中文:
引理 Ioi_pred_eq_Ici
  条件: (a : α)
  结论: Ioi (pred a) = Ici a
  证明: Ioi_pred_eq_Ici_of_not_isMin (not_isMin _)

Depends on / 依赖: Ioi_pred_eq_Ici_of_not_isMin, not_isMin
-/
lemma Ioi_pred_eq_Ici (a : α) : Ioi (pred a) = Ici a := Ioi_pred_eq_Ici_of_not_isMin (not_isMin _)

end PredOrder
end Set
