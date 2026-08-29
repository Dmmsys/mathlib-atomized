/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Algebra.Group.ModEq
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Data.Int.SuccPred
public import Mathlib.Order.Circular
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.GroupTheory.QuotientGroup.ModEq

/-!
# Reducing to an interval modulo its length

This file defines operations that reduce a number (in an archimedean linearly ordered abelian group)
to a number in a given interval, modulo the length of that interval.

## Main definitions

* `toIcoDiv hp a b` (where `hp : 0 < p`): The unique integer such that this multiple of `p`,
  subtracted from `b`, is in `Ico a (a + p)`.
* `toIcoMod hp a b` (where `hp : 0 < p`): Reduce `b` to the interval `Ico a (a + p)`.
* `toIocDiv hp a b` (where `hp : 0 < p`): The unique integer such that this multiple of `p`,
  subtracted from `b`, is in `Ioc a (a + p)`.
* `toIocMod hp a b` (where `hp : 0 < p`): Reduce `b` to the interval `Ioc a (a + p)`.
-/

@[expose] public section

assert_not_exists TwoSidedIdeal

noncomputable section

section LinearOrderedAddCommGroup

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : Int}

section
include hp

/--
Definition of `toIcoDiv` / `toIcoDiv` 的定义

English:
definition toIcoDiv
  signature: (a b : α)
  body: (existsUnique_sub_zsmul_mem_Ico hp b a).choose

中文:
定义 toIcoDiv
  签名: (a b : α)
  定义体: (existsUnique_sub_zsmul_mem_Ico hp b a).choose

Depends on / 依赖: existsUnique_sub_zsmul_mem_Ico
-/
def toIcoDiv (a b : α) : Int :=
  (existsUnique_sub_zsmul_mem_Ico hp b a).choose

/--
theorem `sub_toIcoDiv_zsmul_mem_Ico` / 定理 `sub_toIcoDiv_zsmul_mem_Ico`

English:
theorem sub_toIcoDiv_zsmul_mem_Ico
  given: (a b : α)
  statement: b - toIcoDiv hp a b • p in Set.Ico a (a + p)
  proof: (existsUnique_sub_zsmul_mem_Ico hp b a).choose_spec.1

中文:
定理 sub_toIcoDiv_zsmul_mem_Ico
  条件: (a b : α)
  结论: b - toIcoDiv hp a b • p in 集合.左闭右开区间 a (a + p)
  证明: (existsUnique_sub_zsmul_mem_Ico hp b a).choose_spec.1

Depends on / 依赖: choose_spec, existsUnique_sub_zsmul_mem_Ico
-/
theorem sub_toIcoDiv_zsmul_mem_Ico (a b : α) : b - toIcoDiv hp a b • p in Set.Ico a (a + p) :=
  (existsUnique_sub_zsmul_mem_Ico hp b a).choose_spec.1

/--
theorem `toIcoDiv_eq_iff` / 定理 `toIcoDiv_eq_iff`

English:
theorem toIcoDiv_eq_iff
  statement: toIcoDiv hp a b = n ↔ b - n • p in Set.Ico a (a + p)
  proof: (existsUnique_sub_zsmul_mem_Ico hp b a).choose_eq_iff

alias ⟨_, toIcoDiv_eq_of_sub_zsmul_mem_Ico⟩ := toIcoDiv_eq_iff

中文:
定理 toIcoDiv_eq_iff
  结论: toIcoDiv hp a b = n ↔ b - n • p in 集合.左闭右开区间 a (a + p)
  证明: (existsUnique_sub_zsmul_mem_Ico hp b a).choose_eq_iff

alias ⟨_, toIcoDiv_eq_of_sub_zsmul_mem_Ico⟩ := toIcoDiv_eq_iff

Depends on / 依赖: choose_eq_iff, existsUnique_sub_zsmul_mem_Ico
-/
theorem toIcoDiv_eq_iff : toIcoDiv hp a b = n ↔ b - n • p in Set.Ico a (a + p) :=
  (existsUnique_sub_zsmul_mem_Ico hp b a).choose_eq_iff

alias ⟨_, toIcoDiv_eq_of_sub_zsmul_mem_Ico⟩ := toIcoDiv_eq_iff

/--
Definition of `toIocDiv` / `toIocDiv` 的定义

English:
definition toIocDiv
  signature: (a b : α)
  body: (existsUnique_sub_zsmul_mem_Ioc hp b a).choose

中文:
定义 toIocDiv
  签名: (a b : α)
  定义体: (existsUnique_sub_zsmul_mem_Ioc hp b a).choose

Depends on / 依赖: existsUnique_sub_zsmul_mem_Ioc
-/
def toIocDiv (a b : α) : Int :=
  (existsUnique_sub_zsmul_mem_Ioc hp b a).choose

/--
theorem `sub_toIocDiv_zsmul_mem_Ioc` / 定理 `sub_toIocDiv_zsmul_mem_Ioc`

English:
theorem sub_toIocDiv_zsmul_mem_Ioc
  given: (a b : α)
  statement: b - toIocDiv hp a b • p in Set.Ioc a (a + p)
  proof: (existsUnique_sub_zsmul_mem_Ioc hp b a).choose_spec.1

中文:
定理 sub_toIocDiv_zsmul_mem_Ioc
  条件: (a b : α)
  结论: b - toIocDiv hp a b • p in 集合.左开右闭区间 a (a + p)
  证明: (existsUnique_sub_zsmul_mem_Ioc hp b a).choose_spec.1

Depends on / 依赖: choose_spec, existsUnique_sub_zsmul_mem_Ioc
-/
theorem sub_toIocDiv_zsmul_mem_Ioc (a b : α) : b - toIocDiv hp a b • p in Set.Ioc a (a + p) :=
  (existsUnique_sub_zsmul_mem_Ioc hp b a).choose_spec.1

/--
theorem `toIocDiv_eq_iff` / 定理 `toIocDiv_eq_iff`

English:
theorem toIocDiv_eq_iff
  statement: toIocDiv hp a b = n ↔ b - n • p in Set.Ioc a (a + p)
  proof: (existsUnique_sub_zsmul_mem_Ioc hp b a).choose_eq_iff

alias ⟨_, toIocDiv_eq_of_sub_zsmul_mem_Ioc⟩ := toIocDiv_eq_iff

中文:
定理 toIocDiv_eq_iff
  结论: toIocDiv hp a b = n ↔ b - n • p in 集合.左开右闭区间 a (a + p)
  证明: (existsUnique_sub_zsmul_mem_Ioc hp b a).choose_eq_iff

alias ⟨_, toIocDiv_eq_of_sub_zsmul_mem_Ioc⟩ := toIocDiv_eq_iff

Depends on / 依赖: choose_eq_iff, existsUnique_sub_zsmul_mem_Ioc
-/
theorem toIocDiv_eq_iff : toIocDiv hp a b = n ↔ b - n • p in Set.Ioc a (a + p) :=
  (existsUnique_sub_zsmul_mem_Ioc hp b a).choose_eq_iff

alias ⟨_, toIocDiv_eq_of_sub_zsmul_mem_Ioc⟩ := toIocDiv_eq_iff

/--
Definition of `toIcoMod` / `toIcoMod` 的定义

English:
definition toIcoMod
  signature: (a b : α)
  body: b - toIcoDiv hp a b • p

中文:
定义 toIcoMod
  签名: (a b : α)
  定义体: b - toIcoDiv hp a b • p

Depends on / 依赖: toIcoDiv
-/
def toIcoMod (a b : α) : α :=
  b - toIcoDiv hp a b • p

/--
Definition of `toIocMod` / `toIocMod` 的定义

English:
definition toIocMod
  signature: (a b : α)
  body: b - toIocDiv hp a b • p

中文:
定义 toIocMod
  签名: (a b : α)
  定义体: b - toIocDiv hp a b • p

Depends on / 依赖: toIocDiv
-/
def toIocMod (a b : α) : α :=
  b - toIocDiv hp a b • p

/--
theorem `toIcoMod_mem_Ico` / 定理 `toIcoMod_mem_Ico`

English:
theorem toIcoMod_mem_Ico
  given: (a b : α)
  statement: toIcoMod hp a b in Set.Ico a (a + p)
  proof: sub_toIcoDiv_zsmul_mem_Ico hp a b

中文:
定理 toIcoMod_mem_Ico
  条件: (a b : α)
  结论: toIcoMod hp a b in 集合.左闭右开区间 a (a + p)
  证明: sub_toIcoDiv_zsmul_mem_Ico hp a b

Depends on / 依赖: sub_toIcoDiv_zsmul_mem_Ico
-/
theorem toIcoMod_mem_Ico (a b : α) : toIcoMod hp a b in Set.Ico a (a + p) :=
  sub_toIcoDiv_zsmul_mem_Ico hp a b

/--
theorem `toIcoMod_mem_Ico'` / 定理 `toIcoMod_mem_Ico'`

English:
theorem toIcoMod_mem_Ico'
  given: (b : α)
  statement: toIcoMod hp 0 b in Set.Ico 0 p
  proof: by
  convert! toIcoMod_mem_Ico hp 0 b
  exact (zero_add p).symm

中文:
定理 toIcoMod_mem_Ico'
  条件: (b : α)
  结论: toIcoMod hp 0 b in 集合.左闭右开区间 0 p
  证明: by
  convert! toIcoMod_mem_Ico hp 0 b
  exact (zero_add p).symm

Depends on / 依赖: convert, toIcoMod_mem_Ico, zero_add
-/
theorem toIcoMod_mem_Ico' (b : α) : toIcoMod hp 0 b in Set.Ico 0 p := by
  convert! toIcoMod_mem_Ico hp 0 b
  exact (zero_add p).symm

/--
theorem `toIocMod_mem_Ioc` / 定理 `toIocMod_mem_Ioc`

English:
theorem toIocMod_mem_Ioc
  given: (a b : α)
  statement: toIocMod hp a b in Set.Ioc a (a + p)
  proof: sub_toIocDiv_zsmul_mem_Ioc hp a b

中文:
定理 toIocMod_mem_Ioc
  条件: (a b : α)
  结论: toIocMod hp a b in 集合.左开右闭区间 a (a + p)
  证明: sub_toIocDiv_zsmul_mem_Ioc hp a b

Depends on / 依赖: sub_toIocDiv_zsmul_mem_Ioc
-/
theorem toIocMod_mem_Ioc (a b : α) : toIocMod hp a b in Set.Ioc a (a + p) :=
  sub_toIocDiv_zsmul_mem_Ioc hp a b

/--
theorem `left_le_toIcoMod` / 定理 `left_le_toIcoMod`

English:
theorem left_le_toIcoMod
  given: (a b : α)
  statement: a <= toIcoMod hp a b
  proof: (Set.mem_Ico.1 (toIcoMod_mem_Ico hp a b)).1

中文:
定理 left_le_toIcoMod
  条件: (a b : α)
  结论: a <= toIcoMod hp a b
  证明: (Set.mem_Ico.1 (toIcoMod_mem_Ico hp a b)).1

Depends on / 依赖: Set.mem_Ico, mem_Ico, toIcoMod_mem_Ico
-/
theorem left_le_toIcoMod (a b : α) : a <= toIcoMod hp a b :=
  (Set.mem_Ico.1 (toIcoMod_mem_Ico hp a b)).1

/--
theorem `left_lt_toIocMod` / 定理 `left_lt_toIocMod`

English:
theorem left_lt_toIocMod
  given: (a b : α)
  statement: a < toIocMod hp a b
  proof: (Set.mem_Ioc.1 (toIocMod_mem_Ioc hp a b)).1

中文:
定理 left_lt_toIocMod
  条件: (a b : α)
  结论: a < toIocMod hp a b
  证明: (Set.mem_Ioc.1 (toIocMod_mem_Ioc hp a b)).1

Depends on / 依赖: AEval.of, Set.mem_Ioc, mem_Ioc, toIocMod_mem_Ioc
-/
theorem left_lt_toIocMod (a b : α) : a < toIocMod hp a b :=
  (Set.mem_Ioc.1 (toIocMod_mem_Ioc hp a b)).1

/--
theorem `toIcoMod_lt_right` / 定理 `toIcoMod_lt_right`

English:
theorem toIcoMod_lt_right
  given: (a b : α)
  statement: toIcoMod hp a b < a + p
  proof: (Set.mem_Ico.1 (toIcoMod_mem_Ico hp a b)).2

中文:
定理 toIcoMod_lt_right
  条件: (a b : α)
  结论: toIcoMod hp a b < a + p
  证明: (Set.mem_Ico.1 (toIcoMod_mem_Ico hp a b)).2

Depends on / 依赖: Set.mem_Ico, mem_Ico, toIcoMod_mem_Ico
-/
theorem toIcoMod_lt_right (a b : α) : toIcoMod hp a b < a + p :=
  (Set.mem_Ico.1 (toIcoMod_mem_Ico hp a b)).2

/--
theorem `toIocMod_le_right` / 定理 `toIocMod_le_right`

English:
theorem toIocMod_le_right
  given: (a b : α)
  statement: toIocMod hp a b <= a + p
  proof: (Set.mem_Ioc.1 (toIocMod_mem_Ioc hp a b)).2

@[simp]

中文:
定理 toIocMod_le_right
  条件: (a b : α)
  结论: toIocMod hp a b <= a + p
  证明: (Set.mem_Ioc.1 (toIocMod_mem_Ioc hp a b)).2

@[simp]

Depends on / 依赖: AEval.X_smul_of, Set.mem_Ioc, X_smul_of, mem_Ioc, toIocMod_mem_Ioc
-/
theorem toIocMod_le_right (a b : α) : toIocMod hp a b <= a + p :=
  (Set.mem_Ioc.1 (toIocMod_mem_Ioc hp a b)).2

@[simp]
/--
theorem `self_sub_toIcoDiv_zsmul` / 定理 `self_sub_toIcoDiv_zsmul`

English:
theorem self_sub_toIcoDiv_zsmul
  given: (a b : α)
  statement: b - toIcoDiv hp a b • p = toIcoMod hp a b
  proof: rfl

@[simp]

中文:
定理 self_sub_toIcoDiv_zsmul
  条件: (a b : α)
  结论: b - toIcoDiv hp a b • p = toIcoMod hp a b
  证明: rfl

@[simp]

Depends on / 依赖: AEval.X_pow_smul_of, X_pow_smul_of
-/
theorem self_sub_toIcoDiv_zsmul (a b : α) : b - toIcoDiv hp a b • p = toIcoMod hp a b :=
  rfl

@[simp]
/--
theorem `self_sub_toIocDiv_zsmul` / 定理 `self_sub_toIocDiv_zsmul`

English:
theorem self_sub_toIocDiv_zsmul
  given: (a b : α)
  statement: b - toIocDiv hp a b • p = toIocMod hp a b
  proof: rfl

@[simp]

中文:
定理 self_sub_toIocDiv_zsmul
  条件: (a b : α)
  结论: b - toIocDiv hp a b • p = toIocMod hp a b
  证明: rfl

@[simp]

Depends on / 依赖: AEval.of_symm_X_smul, of_symm_X_smul
-/
theorem self_sub_toIocDiv_zsmul (a b : α) : b - toIocDiv hp a b • p = toIocMod hp a b :=
  rfl

@[simp]
/--
theorem `toIcoDiv_zsmul_sub_self` / 定理 `toIcoDiv_zsmul_sub_self`

English:
theorem toIcoDiv_zsmul_sub_self
  given: (a b : α)
  statement: toIcoDiv hp a b • p - b = -toIcoMod hp a b
  proof: by
  rw [toIcoMod]; rw [neg_sub]

@[simp]

中文:
定理 toIcoDiv_zsmul_sub_self
  条件: (a b : α)
  结论: toIcoDiv hp a b • p - b = -toIcoMod hp a b
  证明: by
  rw [toIcoMod]; rw [neg_sub]

@[simp]

Depends on / 依赖: neg_sub, toIcoMod
-/
theorem toIcoDiv_zsmul_sub_self (a b : α) : toIcoDiv hp a b • p - b = -toIcoMod hp a b := by
  rw [toIcoMod]; rw [neg_sub]

@[simp]
/--
theorem `toIocDiv_zsmul_sub_self` / 定理 `toIocDiv_zsmul_sub_self`

English:
theorem toIocDiv_zsmul_sub_self
  given: (a b : α)
  statement: toIocDiv hp a b • p - b = -toIocMod hp a b
  proof: by
  rw [toIocMod]; rw [neg_sub]

@[simp]

中文:
定理 toIocDiv_zsmul_sub_self
  条件: (a b : α)
  结论: toIocDiv hp a b • p - b = -toIocMod hp a b
  证明: by
  rw [toIocMod]; rw [neg_sub]

@[simp]

Depends on / 依赖: neg_sub, toIocMod
-/
theorem toIocDiv_zsmul_sub_self (a b : α) : toIocDiv hp a b • p - b = -toIocMod hp a b := by
  rw [toIocMod]; rw [neg_sub]

@[simp]
/--
theorem `toIcoMod_sub_self` / 定理 `toIcoMod_sub_self`

English:
theorem toIcoMod_sub_self
  given: (a b : α)
  statement: toIcoMod hp a b - b = -toIcoDiv hp a b • p
  proof: by
  rw [toIcoMod]; rw [sub_sub_cancel_left]; rw [neg_smul]

@[simp]

中文:
定理 toIcoMod_sub_self
  条件: (a b : α)
  结论: toIcoMod hp a b - b = -toIcoDiv hp a b • p
  证明: by
  rw [toIcoMod]; rw [sub_sub_cancel_left]; rw [neg_smul]

@[simp]

Depends on / 依赖: neg_smul, sub_sub_cancel_left, toIcoMod
-/
theorem toIcoMod_sub_self (a b : α) : toIcoMod hp a b - b = -toIcoDiv hp a b • p := by
  rw [toIcoMod]; rw [sub_sub_cancel_left]; rw [neg_smul]

@[simp]
/--
theorem `toIocMod_sub_self` / 定理 `toIocMod_sub_self`

English:
theorem toIocMod_sub_self
  given: (a b : α)
  statement: toIocMod hp a b - b = -toIocDiv hp a b • p
  proof: by
  rw [toIocMod]; rw [sub_sub_cancel_left]; rw [neg_smul]

@[simp]

中文:
定理 toIocMod_sub_self
  条件: (a b : α)
  结论: toIocMod hp a b - b = -toIocDiv hp a b • p
  证明: by
  rw [toIocMod]; rw [sub_sub_cancel_left]; rw [neg_smul]

@[simp]

Depends on / 依赖: neg_smul, sub_sub_cancel_left, toIocMod
-/
theorem toIocMod_sub_self (a b : α) : toIocMod hp a b - b = -toIocDiv hp a b • p := by
  rw [toIocMod]; rw [sub_sub_cancel_left]; rw [neg_smul]

@[simp]
/--
theorem `self_sub_toIcoMod` / 定理 `self_sub_toIcoMod`

English:
theorem self_sub_toIcoMod
  given: (a b : α)
  statement: b - toIcoMod hp a b = toIcoDiv hp a b • p
  proof: by
  rw [toIcoMod]; rw [sub_sub_cancel]

@[simp]

中文:
定理 self_sub_toIcoMod
  条件: (a b : α)
  结论: b - toIcoMod hp a b = toIcoDiv hp a b • p
  证明: by
  rw [toIcoMod]; rw [sub_sub_cancel]

@[simp]

Depends on / 依赖: sub_sub_cancel, toIcoMod
-/
theorem self_sub_toIcoMod (a b : α) : b - toIcoMod hp a b = toIcoDiv hp a b • p := by
  rw [toIcoMod]; rw [sub_sub_cancel]

@[simp]
/--
theorem `self_sub_toIocMod` / 定理 `self_sub_toIocMod`

English:
theorem self_sub_toIocMod
  given: (a b : α)
  statement: b - toIocMod hp a b = toIocDiv hp a b • p
  proof: by
  rw [toIocMod]; rw [sub_sub_cancel]

@[simp]

中文:
定理 self_sub_toIocMod
  条件: (a b : α)
  结论: b - toIocMod hp a b = toIocDiv hp a b • p
  证明: by
  rw [toIocMod]; rw [sub_sub_cancel]

@[simp]

Depends on / 依赖: sub_sub_cancel, toIocMod
-/
theorem self_sub_toIocMod (a b : α) : b - toIocMod hp a b = toIocDiv hp a b • p := by
  rw [toIocMod]; rw [sub_sub_cancel]

@[simp]
/--
theorem `toIcoMod_add_toIcoDiv_zsmul` / 定理 `toIcoMod_add_toIcoDiv_zsmul`

English:
theorem toIcoMod_add_toIcoDiv_zsmul
  given: (a b : α)
  statement: toIcoMod hp a b + toIcoDiv hp a b • p = b
  proof: by
  rw [toIcoMod]; rw [sub_add_cancel]

@[simp]

中文:
定理 toIcoMod_add_toIcoDiv_zsmul
  条件: (a b : α)
  结论: toIcoMod hp a b + toIcoDiv hp a b • p = b
  证明: by
  rw [toIcoMod]; rw [sub_add_cancel]

@[simp]

Depends on / 依赖: sub_add_cancel, toIcoMod
-/
theorem toIcoMod_add_toIcoDiv_zsmul (a b : α) : toIcoMod hp a b + toIcoDiv hp a b • p = b := by
  rw [toIcoMod]; rw [sub_add_cancel]

@[simp]
/--
theorem `toIocMod_add_toIocDiv_zsmul` / 定理 `toIocMod_add_toIocDiv_zsmul`

English:
theorem toIocMod_add_toIocDiv_zsmul
  given: (a b : α)
  statement: toIocMod hp a b + toIocDiv hp a b • p = b
  proof: by
  rw [toIocMod]; rw [sub_add_cancel]

@[simp]

中文:
定理 toIocMod_add_toIocDiv_zsmul
  条件: (a b : α)
  结论: toIocMod hp a b + toIocDiv hp a b • p = b
  证明: by
  rw [toIocMod]; rw [sub_add_cancel]

@[simp]

Depends on / 依赖: sub_add_cancel, toIocMod
-/
theorem toIocMod_add_toIocDiv_zsmul (a b : α) : toIocMod hp a b + toIocDiv hp a b • p = b := by
  rw [toIocMod]; rw [sub_add_cancel]

@[simp]
/--
theorem `toIcoDiv_zsmul_sub_toIcoMod` / 定理 `toIcoDiv_zsmul_sub_toIcoMod`

English:
theorem toIcoDiv_zsmul_sub_toIcoMod
  given: (a b : α)
  statement: toIcoDiv hp a b • p + toIcoMod hp a b = b
  proof: by
  rw [add_comm]; rw [toIcoMod_add_toIcoDiv_zsmul]

@[simp]

中文:
定理 toIcoDiv_zsmul_sub_toIcoMod
  条件: (a b : α)
  结论: toIcoDiv hp a b • p + toIcoMod hp a b = b
  证明: by
  rw [add_comm]; rw [toIcoMod_add_toIcoDiv_zsmul]

@[simp]

Depends on / 依赖: add_comm, toIcoMod_add_toIcoDiv_zsmul
-/
theorem toIcoDiv_zsmul_sub_toIcoMod (a b : α) : toIcoDiv hp a b • p + toIcoMod hp a b = b := by
  rw [add_comm]; rw [toIcoMod_add_toIcoDiv_zsmul]

@[simp]
/--
theorem `toIocDiv_zsmul_sub_toIocMod` / 定理 `toIocDiv_zsmul_sub_toIocMod`

English:
theorem toIocDiv_zsmul_sub_toIocMod
  given: (a b : α)
  statement: toIocDiv hp a b • p + toIocMod hp a b = b
  proof: by
  rw [add_comm]; rw [toIocMod_add_toIocDiv_zsmul]

中文:
定理 toIocDiv_zsmul_sub_toIocMod
  条件: (a b : α)
  结论: toIocDiv hp a b • p + toIocMod hp a b = b
  证明: by
  rw [add_comm]; rw [toIocMod_add_toIocDiv_zsmul]

Depends on / 依赖: add_comm, toIocMod_add_toIocDiv_zsmul
-/
theorem toIocDiv_zsmul_sub_toIocMod (a b : α) : toIocDiv hp a b • p + toIocMod hp a b = b := by
  rw [add_comm]; rw [toIocMod_add_toIocDiv_zsmul]

/--
theorem `toIcoMod_eq_iff` / 定理 `toIcoMod_eq_iff`

English:
theorem toIcoMod_eq_iff
  statement: toIcoMod hp a b = c ↔ c in Set.Ico a (a + p) ∧ exists z : Int, b = c + z • p
  proof: by
  refine
    ⟨fun h =>
      ⟨h ▸ toIcoMod_mem_Ico hp a b, toIcoDiv hp a b, h ▸ (toIcoMod_add_toIcoDiv_zsmul _ _ _).symm⟩,
      ?_⟩
  simp_rw [← @sub_eq_iff_eq_add]
  rintro ⟨hc, n, rfl⟩
  rw [← toIcoDiv_eq_of_sub_zsmul_mem_Ico hp hc]; rw [toIcoMod]

中文:
定理 toIcoMod_eq_iff
  结论: toIcoMod hp a b = c ↔ c in 集合.左闭右开区间 a (a + p) ∧ 存在 z : 整数, b = c + z • p
  证明: by
  refine
    ⟨fun h =>
      ⟨h ▸ toIcoMod_mem_Ico hp a b, toIcoDiv hp a b, h ▸ (toIcoMod_add_toIcoDiv_zsmul _ _ _).symm⟩,
      ?_⟩
  simp_rw [← @sub_eq_iff_eq_add]
  rintro ⟨hc, n, rfl⟩
  rw [← toIcoDiv_eq_of_sub_zsmul_mem_Ico hp hc]; rw [toIcoMod]

Depends on / 依赖: simp_rw, sub_eq_iff_eq_add, toIcoDiv, toIcoDiv_eq_of_sub_zsmul_mem_Ico, toIcoMod, toIcoMod_add_toIcoDiv_zsmul, toIcoMod_mem_Ico
-/
theorem toIcoMod_eq_iff : toIcoMod hp a b = c ↔ c in Set.Ico a (a + p) ∧ exists z : Int, b = c + z • p := by
  refine
    ⟨fun h =>
      ⟨h ▸ toIcoMod_mem_Ico hp a b, toIcoDiv hp a b, h ▸ (toIcoMod_add_toIcoDiv_zsmul _ _ _).symm⟩,
      ?_⟩
  simp_rw [← @sub_eq_iff_eq_add]
  rintro ⟨hc, n, rfl⟩
  rw [← toIcoDiv_eq_of_sub_zsmul_mem_Ico hp hc]; rw [toIcoMod]

/--
theorem `toIocMod_eq_iff` / 定理 `toIocMod_eq_iff`

English:
theorem toIocMod_eq_iff
  statement: toIocMod hp a b = c ↔ c in Set.Ioc a (a + p) ∧ exists z : Int, b = c + z • p
  proof: by
  refine
    ⟨fun h =>
      ⟨h ▸ toIocMod_mem_Ioc hp a b, toIocDiv hp a b, h ▸ (toIocMod_add_toIocDiv_zsmul hp _ _).symm⟩,
      ?_⟩
  simp_rw [← @sub_eq_iff_eq_add]
  rintro ⟨hc, n, rfl⟩
  rw [← toIocDiv_eq_of_sub_zsmul_mem_Ioc hp hc]; rw [toIocMod]

@[simp]

中文:
定理 toIocMod_eq_iff
  结论: toIocMod hp a b = c ↔ c in 集合.左开右闭区间 a (a + p) ∧ 存在 z : 整数, b = c + z • p
  证明: by
  refine
    ⟨fun h =>
      ⟨h ▸ toIocMod_mem_Ioc hp a b, toIocDiv hp a b, h ▸ (toIocMod_add_toIocDiv_zsmul hp _ _).symm⟩,
      ?_⟩
  simp_rw [← @sub_eq_iff_eq_add]
  rintro ⟨hc, n, rfl⟩
  rw [← toIocDiv_eq_of_sub_zsmul_mem_Ioc hp hc]; rw [toIocMod]

@[simp]

Depends on / 依赖: simp_rw, sub_eq_iff_eq_add, toIocDiv, toIocDiv_eq_of_sub_zsmul_mem_Ioc, toIocMod, toIocMod_add_toIocDiv_zsmul, toIocMod_mem_Ioc
-/
theorem toIocMod_eq_iff : toIocMod hp a b = c ↔ c in Set.Ioc a (a + p) ∧ exists z : Int, b = c + z • p := by
  refine
    ⟨fun h =>
      ⟨h ▸ toIocMod_mem_Ioc hp a b, toIocDiv hp a b, h ▸ (toIocMod_add_toIocDiv_zsmul hp _ _).symm⟩,
      ?_⟩
  simp_rw [← @sub_eq_iff_eq_add]
  rintro ⟨hc, n, rfl⟩
  rw [← toIocDiv_eq_of_sub_zsmul_mem_Ioc hp hc]; rw [toIocMod]

@[simp]
/--
theorem `toIcoDiv_apply_left` / 定理 `toIcoDiv_apply_left`

English:
theorem toIcoDiv_apply_left
  given: (a : α)
  statement: toIcoDiv hp a a = 0
  proof: toIcoDiv_eq_of_sub_zsmul_mem_Ico hp by simp [hp]

@[simp]

中文:
定理 toIcoDiv_apply_left
  条件: (a : α)
  结论: toIcoDiv hp a a = 0
  证明: toIcoDiv_eq_of_sub_zsmul_mem_Ico hp by simp [hp]

@[simp]

Depends on / 依赖: toIcoDiv_eq_of_sub_zsmul_mem_Ico
-/
theorem toIcoDiv_apply_left (a : α) : toIcoDiv hp a a = 0 :=
toIcoDiv_eq_of_sub_zsmul_mem_Ico hp by simp [hp]

@[simp]
/--
theorem `toIocDiv_apply_left` / 定理 `toIocDiv_apply_left`

English:
theorem toIocDiv_apply_left
  given: (a : α)
  statement: toIocDiv hp a a = -1
  proof: toIocDiv_eq_of_sub_zsmul_mem_Ioc hp by simp [hp]

@[simp]

中文:
定理 toIocDiv_apply_left
  条件: (a : α)
  结论: toIocDiv hp a a = -1
  证明: toIocDiv_eq_of_sub_zsmul_mem_Ioc hp by simp [hp]

@[simp]

Depends on / 依赖: toIocDiv_eq_of_sub_zsmul_mem_Ioc
-/
theorem toIocDiv_apply_left (a : α) : toIocDiv hp a a = -1 :=
toIocDiv_eq_of_sub_zsmul_mem_Ioc hp by simp [hp]

@[simp]
/--
theorem `toIcoMod_apply_left` / 定理 `toIcoMod_apply_left`

English:
theorem toIcoMod_apply_left
  given: (a : α)
  statement: toIcoMod hp a a = a
  proof: by
  rw [toIcoMod_eq_iff hp]; rw [Set.left_mem_Ico]
  exact ⟨lt_add_of_pos_right _ hp, 0, by simp⟩

@[simp]

中文:
定理 toIcoMod_apply_left
  条件: (a : α)
  结论: toIcoMod hp a a = a
  证明: by
  rw [toIcoMod_eq_iff hp]; rw [Set.left_mem_Ico]
  exact ⟨lt_add_of_pos_right _ hp, 0, by simp⟩

@[simp]

Depends on / 依赖: Set.left_mem_Ico, left_mem_Ico, lt_add_of_pos_right, toIcoMod_eq_iff
-/
theorem toIcoMod_apply_left (a : α) : toIcoMod hp a a = a := by
  rw [toIcoMod_eq_iff hp]; rw [Set.left_mem_Ico]
  exact ⟨lt_add_of_pos_right _ hp, 0, by simp⟩

@[simp]
/--
theorem `toIocMod_apply_left` / 定理 `toIocMod_apply_left`

English:
theorem toIocMod_apply_left
  given: (a : α)
  statement: toIocMod hp a a = a + p
  proof: by
  rw [toIocMod_eq_iff hp]; rw [Set.right_mem_Ioc]
  exact ⟨lt_add_of_pos_right _ hp, -1, by simp⟩

中文:
定理 toIocMod_apply_left
  条件: (a : α)
  结论: toIocMod hp a a = a + p
  证明: by
  rw [toIocMod_eq_iff hp]; rw [Set.right_mem_Ioc]
  exact ⟨lt_add_of_pos_right _ hp, -1, by simp⟩

Depends on / 依赖: Set.right_mem_Ioc, lt_add_of_pos_right, right_mem_Ioc, toIocMod_eq_iff
-/
theorem toIocMod_apply_left (a : α) : toIocMod hp a a = a + p := by
  rw [toIocMod_eq_iff hp]; rw [Set.right_mem_Ioc]
  exact ⟨lt_add_of_pos_right _ hp, -1, by simp⟩

/--
theorem `toIcoDiv_apply_right` / 定理 `toIcoDiv_apply_right`

English:
theorem toIcoDiv_apply_right
  given: (a : α)
  statement: toIcoDiv hp a (a + p) = 1
  proof: toIcoDiv_eq_of_sub_zsmul_mem_Ico hp by simp [hp]

中文:
定理 toIcoDiv_apply_right
  条件: (a : α)
  结论: toIcoDiv hp a (a + p) = 1
  证明: toIcoDiv_eq_of_sub_zsmul_mem_Ico hp by simp [hp]

Depends on / 依赖: toIcoDiv_eq_of_sub_zsmul_mem_Ico
-/
theorem toIcoDiv_apply_right (a : α) : toIcoDiv hp a (a + p) = 1 :=
toIcoDiv_eq_of_sub_zsmul_mem_Ico hp by simp [hp]

/--
theorem `toIocDiv_apply_right` / 定理 `toIocDiv_apply_right`

English:
theorem toIocDiv_apply_right
  given: (a : α)
  statement: toIocDiv hp a (a + p) = 0
  proof: toIocDiv_eq_of_sub_zsmul_mem_Ioc hp by simp [hp]

中文:
定理 toIocDiv_apply_right
  条件: (a : α)
  结论: toIocDiv hp a (a + p) = 0
  证明: toIocDiv_eq_of_sub_zsmul_mem_Ioc hp by simp [hp]

Depends on / 依赖: toIocDiv_eq_of_sub_zsmul_mem_Ioc
-/
theorem toIocDiv_apply_right (a : α) : toIocDiv hp a (a + p) = 0 :=
toIocDiv_eq_of_sub_zsmul_mem_Ioc hp by simp [hp]

/--
theorem `toIcoMod_apply_right` / 定理 `toIcoMod_apply_right`

English:
theorem toIcoMod_apply_right
  given: (a : α)
  statement: toIcoMod hp a (a + p) = a
  proof: by
  rw [toIcoMod_eq_iff hp]; rw [Set.left_mem_Ico]
  exact ⟨lt_add_of_pos_right _ hp, 1, by simp⟩

中文:
定理 toIcoMod_apply_right
  条件: (a : α)
  结论: toIcoMod hp a (a + p) = a
  证明: by
  rw [toIcoMod_eq_iff hp]; rw [Set.left_mem_Ico]
  exact ⟨lt_add_of_pos_right _ hp, 1, by simp⟩

Depends on / 依赖: Set.left_mem_Ico, left_mem_Ico, lt_add_of_pos_right, toIcoMod_eq_iff
-/
theorem toIcoMod_apply_right (a : α) : toIcoMod hp a (a + p) = a := by
  rw [toIcoMod_eq_iff hp]; rw [Set.left_mem_Ico]
  exact ⟨lt_add_of_pos_right _ hp, 1, by simp⟩

/--
theorem `toIocMod_apply_right` / 定理 `toIocMod_apply_right`

English:
theorem toIocMod_apply_right
  given: (a : α)
  statement: toIocMod hp a (a + p) = a + p
  proof: by
  rw [toIocMod_eq_iff hp]; rw [Set.right_mem_Ioc]
  exact ⟨lt_add_of_pos_right _ hp, 0, by simp⟩

@[simp]

中文:
定理 toIocMod_apply_right
  条件: (a : α)
  结论: toIocMod hp a (a + p) = a + p
  证明: by
  rw [toIocMod_eq_iff hp]; rw [Set.right_mem_Ioc]
  exact ⟨lt_add_of_pos_right _ hp, 0, by simp⟩

@[simp]

Depends on / 依赖: Set.right_mem_Ioc, lt_add_of_pos_right, right_mem_Ioc, toIocMod_eq_iff
-/
theorem toIocMod_apply_right (a : α) : toIocMod hp a (a + p) = a + p := by
  rw [toIocMod_eq_iff hp]; rw [Set.right_mem_Ioc]
  exact ⟨lt_add_of_pos_right _ hp, 0, by simp⟩

@[simp]
/--
theorem `toIcoDiv_add_zsmul` / 定理 `toIcoDiv_add_zsmul`

English:
theorem toIcoDiv_add_zsmul
  given: (a b : α) (m : Int)
  statement: toIcoDiv hp a (b + m • p) = toIcoDiv hp a b + m
  proof: toIcoDiv_eq_of_sub_zsmul_mem_Ico hp by
    simpa only [add_smul, add_sub_add_right_eq_sub] using sub_toIcoDiv_zsmul_mem_Ico hp a b

@[simp]

中文:
定理 toIcoDiv_add_zsmul
  条件: (a b : α) (m : 整数)
  结论: toIcoDiv hp a (b + m • p) = toIcoDiv hp a b + m
  证明: toIcoDiv_eq_of_sub_zsmul_mem_Ico hp by
    simpa only [add_smul, add_sub_add_right_eq_sub] using sub_toIcoDiv_zsmul_mem_Ico hp a b

@[simp]

Depends on / 依赖: add_smul, add_sub_add_right_eq_sub, sub_toIcoDiv_zsmul_mem_Ico, toIcoDiv_eq_of_sub_zsmul_mem_Ico
-/
theorem toIcoDiv_add_zsmul (a b : α) (m : Int) : toIcoDiv hp a (b + m • p) = toIcoDiv hp a b + m :=
toIcoDiv_eq_of_sub_zsmul_mem_Ico hp by
    simpa only [add_smul, add_sub_add_right_eq_sub] using sub_toIcoDiv_zsmul_mem_Ico hp a b

@[simp]
/--
theorem `toIcoDiv_add_nsmul` / 定理 `toIcoDiv_add_nsmul`

English:
theorem toIcoDiv_add_nsmul
  given: (a b : α) (m : Nat)
  statement: toIcoDiv hp a (b + m • p) = toIcoDiv hp a b + m
  proof: mod_cast toIcoDiv_add_zsmul hp a b m

@[simp]

中文:
定理 toIcoDiv_add_nsmul
  条件: (a b : α) (m : 自然数)
  结论: toIcoDiv hp a (b + m • p) = toIcoDiv hp a b + m
  证明: mod_cast toIcoDiv_add_zsmul hp a b m

@[simp]

Depends on / 依赖: coeffEquiv, isScalarTower, mod_cast, toIcoDiv_add_zsmul
-/
theorem toIcoDiv_add_nsmul (a b : α) (m : Nat) : toIcoDiv hp a (b + m • p) = toIcoDiv hp a b + m :=
  mod_cast toIcoDiv_add_zsmul hp a b m

@[simp]
/--
theorem `toIcoDiv_add_zsmul'` / 定理 `toIcoDiv_add_zsmul'`

English:
theorem toIcoDiv_add_zsmul'
  given: (a b : α) (m : Int)
  proof: by
  refine toIcoDiv_eq_of_sub_zsmul_mem_Ico _ ?_
  rw [sub_smul]; rw [← sub_add]; rw [add_right_comm]
  simpa using sub_toIcoDiv_zsmul_mem_Ico hp a b

@[simp]

中文:
定理 toIcoDiv_add_zsmul'
  条件: (a b : α) (m : 整数)
  证明: by
  refine toIcoDiv_eq_of_sub_zsmul_mem_Ico _ ?_
  rw [sub_smul]; rw [← sub_add]; rw [add_right_comm]
  simpa using sub_toIcoDiv_zsmul_mem_Ico hp a b

@[simp]

Depends on / 依赖: add_right_comm, sub_add, sub_smul, sub_toIcoDiv_zsmul_mem_Ico, toIcoDiv_eq_of_sub_zsmul_mem_Ico
-/
theorem toIcoDiv_add_zsmul' (a b : α) (m : Int) :
    toIcoDiv hp (a + m • p) b = toIcoDiv hp a b - m := by
  refine toIcoDiv_eq_of_sub_zsmul_mem_Ico _ ?_
  rw [sub_smul]; rw [← sub_add]; rw [add_right_comm]
  simpa using sub_toIcoDiv_zsmul_mem_Ico hp a b

@[simp]
/--
theorem `toIcoDiv_add_nsmul'` / 定理 `toIcoDiv_add_nsmul'`

English:
theorem toIcoDiv_add_nsmul'
  given: (a b : α) (m : Nat)
  statement: toIcoDiv hp (a + m • p) b = toIcoDiv hp a b - m
  proof: mod_cast toIcoDiv_add_zsmul' hp a b m

@[simp]

中文:
定理 toIcoDiv_add_nsmul'
  条件: (a b : α) (m : 自然数)
  结论: toIcoDiv hp (a + m • p) b = toIcoDiv hp a b - m
  证明: mod_cast toIcoDiv_add_zsmul' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoDiv_add_zsmul
-/
theorem toIcoDiv_add_nsmul' (a b : α) (m : Nat) : toIcoDiv hp (a + m • p) b = toIcoDiv hp a b - m :=
  mod_cast toIcoDiv_add_zsmul' hp a b m

@[simp]
/--
theorem `toIocDiv_add_zsmul` / 定理 `toIocDiv_add_zsmul`

English:
theorem toIocDiv_add_zsmul
  given: (a b : α) (m : Int)
  statement: toIocDiv hp a (b + m • p) = toIocDiv hp a b + m
  proof: toIocDiv_eq_of_sub_zsmul_mem_Ioc hp by
    simpa only [add_smul, add_sub_add_right_eq_sub] using sub_toIocDiv_zsmul_mem_Ioc hp a b

@[simp]

中文:
定理 toIocDiv_add_zsmul
  条件: (a b : α) (m : 整数)
  结论: toIocDiv hp a (b + m • p) = toIocDiv hp a b + m
  证明: toIocDiv_eq_of_sub_zsmul_mem_Ioc hp by
    simpa only [add_smul, add_sub_add_right_eq_sub] using sub_toIocDiv_zsmul_mem_Ioc hp a b

@[simp]

Depends on / 依赖: add_smul, add_sub_add_right_eq_sub, sub_toIocDiv_zsmul_mem_Ioc, toIocDiv_eq_of_sub_zsmul_mem_Ioc
-/
theorem toIocDiv_add_zsmul (a b : α) (m : Int) : toIocDiv hp a (b + m • p) = toIocDiv hp a b + m :=
toIocDiv_eq_of_sub_zsmul_mem_Ioc hp by
    simpa only [add_smul, add_sub_add_right_eq_sub] using sub_toIocDiv_zsmul_mem_Ioc hp a b

@[simp]
/--
theorem `toIocDiv_add_nsmul` / 定理 `toIocDiv_add_nsmul`

English:
theorem toIocDiv_add_nsmul
  given: (a b : α) (m : Nat)
  statement: toIocDiv hp a (b + m • p) = toIocDiv hp a b + m
  proof: mod_cast toIocDiv_add_zsmul hp a b m

@[simp]

中文:
定理 toIocDiv_add_nsmul
  条件: (a b : α) (m : 自然数)
  结论: toIocDiv hp a (b + m • p) = toIocDiv hp a b + m
  证明: mod_cast toIocDiv_add_zsmul hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocDiv_add_zsmul
-/
theorem toIocDiv_add_nsmul (a b : α) (m : Nat) : toIocDiv hp a (b + m • p) = toIocDiv hp a b + m :=
  mod_cast toIocDiv_add_zsmul hp a b m

@[simp]
/--
theorem `toIocDiv_add_zsmul'` / 定理 `toIocDiv_add_zsmul'`

English:
theorem toIocDiv_add_zsmul'
  given: (a b : α) (m : Int)
  proof: by
  refine toIocDiv_eq_of_sub_zsmul_mem_Ioc _ ?_
  rw [sub_smul]; rw [← sub_add]; rw [add_right_comm]
  simpa using sub_toIocDiv_zsmul_mem_Ioc hp a b

@[simp]

中文:
定理 toIocDiv_add_zsmul'
  条件: (a b : α) (m : 整数)
  证明: by
  refine toIocDiv_eq_of_sub_zsmul_mem_Ioc _ ?_
  rw [sub_smul]; rw [← sub_add]; rw [add_right_comm]
  simpa using sub_toIocDiv_zsmul_mem_Ioc hp a b

@[simp]

Depends on / 依赖: add_right_comm, sub_add, sub_smul, sub_toIocDiv_zsmul_mem_Ioc, toIocDiv_eq_of_sub_zsmul_mem_Ioc
-/
theorem toIocDiv_add_zsmul' (a b : α) (m : Int) :
    toIocDiv hp (a + m • p) b = toIocDiv hp a b - m := by
  refine toIocDiv_eq_of_sub_zsmul_mem_Ioc _ ?_
  rw [sub_smul]; rw [← sub_add]; rw [add_right_comm]
  simpa using sub_toIocDiv_zsmul_mem_Ioc hp a b

@[simp]
/--
theorem `toIocDiv_add_nsmul'` / 定理 `toIocDiv_add_nsmul'`

English:
theorem toIocDiv_add_nsmul'
  given: (a b : α) (m : Nat)
  statement: toIocDiv hp (a + m • p) b = toIocDiv hp a b - m
  proof: mod_cast toIocDiv_add_zsmul' hp a b m

@[simp]

中文:
定理 toIocDiv_add_nsmul'
  条件: (a b : α) (m : 自然数)
  结论: toIocDiv hp (a + m • p) b = toIocDiv hp a b - m
  证明: mod_cast toIocDiv_add_zsmul' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocDiv_add_zsmul
-/
theorem toIocDiv_add_nsmul' (a b : α) (m : Nat) : toIocDiv hp (a + m • p) b = toIocDiv hp a b - m :=
  mod_cast toIocDiv_add_zsmul' hp a b m

@[simp]
/--
theorem `toIcoDiv_zsmul_add` / 定理 `toIcoDiv_zsmul_add`

English:
theorem toIcoDiv_zsmul_add
  given: (a b : α) (m : Int)
  statement: toIcoDiv hp a (m • p + b) = m + toIcoDiv hp a b
  proof: by
  rw [add_comm]; rw [toIcoDiv_add_zsmul]; rw [add_comm]

@[simp]

中文:
定理 toIcoDiv_zsmul_add
  条件: (a b : α) (m : 整数)
  结论: toIcoDiv hp a (m • p + b) = m + toIcoDiv hp a b
  证明: by
  rw [add_comm]; rw [toIcoDiv_add_zsmul]; rw [add_comm]

@[simp]

Depends on / 依赖: add_comm, toIcoDiv_add_zsmul
-/
theorem toIcoDiv_zsmul_add (a b : α) (m : Int) : toIcoDiv hp a (m • p + b) = m + toIcoDiv hp a b := by
  rw [add_comm]; rw [toIcoDiv_add_zsmul]; rw [add_comm]

@[simp]
/--
theorem `toIcoDiv_nsmul_add` / 定理 `toIcoDiv_nsmul_add`

English:
theorem toIcoDiv_nsmul_add
  given: (a b : α) (m : Nat)
  statement: toIcoDiv hp a (m • p + b) = m + toIcoDiv hp a b
  proof: mod_cast toIcoDiv_zsmul_add hp a b m

中文:
定理 toIcoDiv_nsmul_add
  条件: (a b : α) (m : 自然数)
  结论: toIcoDiv hp a (m • p + b) = m + toIcoDiv hp a b
  证明: mod_cast toIcoDiv_zsmul_add hp a b m

Depends on / 依赖: mod_cast, toIcoDiv_zsmul_add
-/
theorem toIcoDiv_nsmul_add (a b : α) (m : Nat) : toIcoDiv hp a (m • p + b) = m + toIcoDiv hp a b :=
  mod_cast toIcoDiv_zsmul_add hp a b m

/-! Note we omit `toIcoDiv_zsmul_add'` as `-m + toIcoDiv hp a b` is not very convenient. -/


@[simp]
/--
theorem `toIocDiv_zsmul_add` / 定理 `toIocDiv_zsmul_add`

English:
theorem toIocDiv_zsmul_add
  given: (a b : α) (m : Int)
  statement: toIocDiv hp a (m • p + b) = m + toIocDiv hp a b
  proof: by
  rw [add_comm]; rw [toIocDiv_add_zsmul]; rw [add_comm]

@[simp]

中文:
定理 toIocDiv_zsmul_add
  条件: (a b : α) (m : 整数)
  结论: toIocDiv hp a (m • p + b) = m + toIocDiv hp a b
  证明: by
  rw [add_comm]; rw [toIocDiv_add_zsmul]; rw [add_comm]

@[simp]

Depends on / 依赖: add_comm, toIocDiv_add_zsmul
-/
theorem toIocDiv_zsmul_add (a b : α) (m : Int) : toIocDiv hp a (m • p + b) = m + toIocDiv hp a b := by
  rw [add_comm]; rw [toIocDiv_add_zsmul]; rw [add_comm]

@[simp]
/--
theorem `toIocDiv_nsmul_add` / 定理 `toIocDiv_nsmul_add`

English:
theorem toIocDiv_nsmul_add
  given: (a b : α) (m : Nat)
  statement: toIocDiv hp a (m • p + b) = m + toIocDiv hp a b
  proof: mod_cast toIocDiv_zsmul_add hp a b m

中文:
定理 toIocDiv_nsmul_add
  条件: (a b : α) (m : 自然数)
  结论: toIocDiv hp a (m • p + b) = m + toIocDiv hp a b
  证明: mod_cast toIocDiv_zsmul_add hp a b m

Depends on / 依赖: mod_cast, toIocDiv_zsmul_add
-/
theorem toIocDiv_nsmul_add (a b : α) (m : Nat) : toIocDiv hp a (m • p + b) = m + toIocDiv hp a b :=
  mod_cast toIocDiv_zsmul_add hp a b m

/-! Note we omit `toIocDiv_zsmul_add'` as `-m + toIocDiv hp a b` is not very convenient. -/


@[simp]
/--
theorem `toIcoDiv_sub_zsmul` / 定理 `toIcoDiv_sub_zsmul`

English:
theorem toIcoDiv_sub_zsmul
  given: (a b : α) (m : Int)
  statement: toIcoDiv hp a (b - m • p) = toIcoDiv hp a b - m
  proof: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIcoDiv_add_zsmul]; rw [sub_eq_add_neg]

@[simp]

中文:
定理 toIcoDiv_sub_zsmul
  条件: (a b : α) (m : 整数)
  结论: toIcoDiv hp a (b - m • p) = toIcoDiv hp a b - m
  证明: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIcoDiv_add_zsmul]; rw [sub_eq_add_neg]

@[simp]

Depends on / 依赖: neg_smul, sub_eq_add_neg, toIcoDiv_add_zsmul
-/
theorem toIcoDiv_sub_zsmul (a b : α) (m : Int) : toIcoDiv hp a (b - m • p) = toIcoDiv hp a b - m := by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIcoDiv_add_zsmul]; rw [sub_eq_add_neg]

@[simp]
/--
theorem `toIcoDiv_sub_nsmul` / 定理 `toIcoDiv_sub_nsmul`

English:
theorem toIcoDiv_sub_nsmul
  given: (a b : α) (m : Nat)
  statement: toIcoDiv hp a (b - m • p) = toIcoDiv hp a b - m
  proof: mod_cast toIcoDiv_sub_zsmul hp a b m

@[simp]

中文:
定理 toIcoDiv_sub_nsmul
  条件: (a b : α) (m : 自然数)
  结论: toIcoDiv hp a (b - m • p) = toIcoDiv hp a b - m
  证明: mod_cast toIcoDiv_sub_zsmul hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoDiv_sub_zsmul
-/
theorem toIcoDiv_sub_nsmul (a b : α) (m : Nat) : toIcoDiv hp a (b - m • p) = toIcoDiv hp a b - m :=
  mod_cast toIcoDiv_sub_zsmul hp a b m

@[simp]
/--
theorem `toIcoDiv_sub_zsmul'` / 定理 `toIcoDiv_sub_zsmul'`

English:
theorem toIcoDiv_sub_zsmul'
  given: (a b : α) (m : Int)
  proof: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIcoDiv_add_zsmul']; rw [sub_neg_eq_add]

@[simp]

中文:
定理 toIcoDiv_sub_zsmul'
  条件: (a b : α) (m : 整数)
  证明: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIcoDiv_add_zsmul']; rw [sub_neg_eq_add]

@[simp]

Depends on / 依赖: neg_smul, sub_eq_add_neg, sub_neg_eq_add, toIcoDiv_add_zsmul
-/
theorem toIcoDiv_sub_zsmul' (a b : α) (m : Int) :
    toIcoDiv hp (a - m • p) b = toIcoDiv hp a b + m := by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIcoDiv_add_zsmul']; rw [sub_neg_eq_add]

@[simp]
/--
theorem `toIcoDiv_sub_nsmul'` / 定理 `toIcoDiv_sub_nsmul'`

English:
theorem toIcoDiv_sub_nsmul'
  given: (a b : α) (m : Nat)
  statement: toIcoDiv hp (a - m • p) b = toIcoDiv hp a b + m
  proof: mod_cast toIcoDiv_sub_zsmul' hp a b m

@[simp]

中文:
定理 toIcoDiv_sub_nsmul'
  条件: (a b : α) (m : 自然数)
  结论: toIcoDiv hp (a - m • p) b = toIcoDiv hp a b + m
  证明: mod_cast toIcoDiv_sub_zsmul' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoDiv_sub_zsmul
-/
theorem toIcoDiv_sub_nsmul' (a b : α) (m : Nat) : toIcoDiv hp (a - m • p) b = toIcoDiv hp a b + m :=
  mod_cast toIcoDiv_sub_zsmul' hp a b m

@[simp]
/--
theorem `toIocDiv_sub_zsmul` / 定理 `toIocDiv_sub_zsmul`

English:
theorem toIocDiv_sub_zsmul
  given: (a b : α) (m : Int)
  statement: toIocDiv hp a (b - m • p) = toIocDiv hp a b - m
  proof: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIocDiv_add_zsmul]; rw [sub_eq_add_neg]

@[simp]

中文:
定理 toIocDiv_sub_zsmul
  条件: (a b : α) (m : 整数)
  结论: toIocDiv hp a (b - m • p) = toIocDiv hp a b - m
  证明: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIocDiv_add_zsmul]; rw [sub_eq_add_neg]

@[simp]

Depends on / 依赖: neg_smul, sub_eq_add_neg, toIocDiv_add_zsmul
-/
theorem toIocDiv_sub_zsmul (a b : α) (m : Int) : toIocDiv hp a (b - m • p) = toIocDiv hp a b - m := by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIocDiv_add_zsmul]; rw [sub_eq_add_neg]

@[simp]
/--
theorem `toIocDiv_sub_nsmul` / 定理 `toIocDiv_sub_nsmul`

English:
theorem toIocDiv_sub_nsmul
  given: (a b : α) (m : Nat)
  statement: toIocDiv hp a (b - m • p) = toIocDiv hp a b - m
  proof: mod_cast toIocDiv_sub_zsmul hp a b m

@[simp]

中文:
定理 toIocDiv_sub_nsmul
  条件: (a b : α) (m : 自然数)
  结论: toIocDiv hp a (b - m • p) = toIocDiv hp a b - m
  证明: mod_cast toIocDiv_sub_zsmul hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocDiv_sub_zsmul
-/
theorem toIocDiv_sub_nsmul (a b : α) (m : Nat) : toIocDiv hp a (b - m • p) = toIocDiv hp a b - m :=
  mod_cast toIocDiv_sub_zsmul hp a b m

@[simp]
/--
theorem `toIocDiv_sub_zsmul'` / 定理 `toIocDiv_sub_zsmul'`

English:
theorem toIocDiv_sub_zsmul'
  given: (a b : α) (m : Int)
  proof: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIocDiv_add_zsmul']; rw [sub_neg_eq_add]

@[simp]

中文:
定理 toIocDiv_sub_zsmul'
  条件: (a b : α) (m : 整数)
  证明: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIocDiv_add_zsmul']; rw [sub_neg_eq_add]

@[simp]

Depends on / 依赖: neg_smul, sub_eq_add_neg, sub_neg_eq_add, toIocDiv_add_zsmul
-/
theorem toIocDiv_sub_zsmul' (a b : α) (m : Int) :
    toIocDiv hp (a - m • p) b = toIocDiv hp a b + m := by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIocDiv_add_zsmul']; rw [sub_neg_eq_add]

@[simp]
/--
theorem `toIocDiv_sub_nsmul'` / 定理 `toIocDiv_sub_nsmul'`

English:
theorem toIocDiv_sub_nsmul'
  given: (a b : α) (m : Nat)
  statement: toIocDiv hp (a - m • p) b = toIocDiv hp a b + m
  proof: mod_cast toIocDiv_sub_zsmul' hp a b m

@[simp]

中文:
定理 toIocDiv_sub_nsmul'
  条件: (a b : α) (m : 自然数)
  结论: toIocDiv hp (a - m • p) b = toIocDiv hp a b + m
  证明: mod_cast toIocDiv_sub_zsmul' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocDiv_sub_zsmul
-/
theorem toIocDiv_sub_nsmul' (a b : α) (m : Nat) : toIocDiv hp (a - m • p) b = toIocDiv hp a b + m :=
  mod_cast toIocDiv_sub_zsmul' hp a b m

@[simp]
/--
theorem `toIcoDiv_add_right` / 定理 `toIcoDiv_add_right`

English:
theorem toIcoDiv_add_right
  given: (a b : α)
  statement: toIcoDiv hp a (b + p) = toIcoDiv hp a b + 1
  proof: by
  simpa only [one_zsmul] using toIcoDiv_add_zsmul hp a b 1

@[simp]

中文:
定理 toIcoDiv_add_right
  条件: (a b : α)
  结论: toIcoDiv hp a (b + p) = toIcoDiv hp a b + 1
  证明: by
  simpa only [one_zsmul] using toIcoDiv_add_zsmul hp a b 1

@[simp]

Depends on / 依赖: one_zsmul, toIcoDiv_add_zsmul
-/
theorem toIcoDiv_add_right (a b : α) : toIcoDiv hp a (b + p) = toIcoDiv hp a b + 1 := by
  simpa only [one_zsmul] using toIcoDiv_add_zsmul hp a b 1

@[simp]
/--
theorem `toIcoDiv_add_right'` / 定理 `toIcoDiv_add_right'`

English:
theorem toIcoDiv_add_right'
  given: (a b : α)
  statement: toIcoDiv hp (a + p) b = toIcoDiv hp a b - 1
  proof: by
  simpa only [one_zsmul] using toIcoDiv_add_zsmul' hp a b 1

@[simp]

中文:
定理 toIcoDiv_add_right'
  条件: (a b : α)
  结论: toIcoDiv hp (a + p) b = toIcoDiv hp a b - 1
  证明: by
  simpa only [one_zsmul] using toIcoDiv_add_zsmul' hp a b 1

@[simp]

Depends on / 依赖: one_zsmul, toIcoDiv_add_zsmul
-/
theorem toIcoDiv_add_right' (a b : α) : toIcoDiv hp (a + p) b = toIcoDiv hp a b - 1 := by
  simpa only [one_zsmul] using toIcoDiv_add_zsmul' hp a b 1

@[simp]
/--
theorem `toIocDiv_add_right` / 定理 `toIocDiv_add_right`

English:
theorem toIocDiv_add_right
  given: (a b : α)
  statement: toIocDiv hp a (b + p) = toIocDiv hp a b + 1
  proof: by
  simpa only [one_zsmul] using toIocDiv_add_zsmul hp a b 1

@[simp]

中文:
定理 toIocDiv_add_right
  条件: (a b : α)
  结论: toIocDiv hp a (b + p) = toIocDiv hp a b + 1
  证明: by
  simpa only [one_zsmul] using toIocDiv_add_zsmul hp a b 1

@[simp]

Depends on / 依赖: one_zsmul, toIocDiv_add_zsmul
-/
theorem toIocDiv_add_right (a b : α) : toIocDiv hp a (b + p) = toIocDiv hp a b + 1 := by
  simpa only [one_zsmul] using toIocDiv_add_zsmul hp a b 1

@[simp]
/--
theorem `toIocDiv_add_right'` / 定理 `toIocDiv_add_right'`

English:
theorem toIocDiv_add_right'
  given: (a b : α)
  statement: toIocDiv hp (a + p) b = toIocDiv hp a b - 1
  proof: by
  simpa only [one_zsmul] using toIocDiv_add_zsmul' hp a b 1

@[simp]

中文:
定理 toIocDiv_add_right'
  条件: (a b : α)
  结论: toIocDiv hp (a + p) b = toIocDiv hp a b - 1
  证明: by
  simpa only [one_zsmul] using toIocDiv_add_zsmul' hp a b 1

@[simp]

Depends on / 依赖: one_zsmul, toIocDiv_add_zsmul
-/
theorem toIocDiv_add_right' (a b : α) : toIocDiv hp (a + p) b = toIocDiv hp a b - 1 := by
  simpa only [one_zsmul] using toIocDiv_add_zsmul' hp a b 1

@[simp]
/--
theorem `toIcoDiv_add_left` / 定理 `toIcoDiv_add_left`

English:
theorem toIcoDiv_add_left
  given: (a b : α)
  statement: toIcoDiv hp a (p + b) = toIcoDiv hp a b + 1
  proof: by
  rw [add_comm]; rw [toIcoDiv_add_right]

@[simp]

中文:
定理 toIcoDiv_add_left
  条件: (a b : α)
  结论: toIcoDiv hp a (p + b) = toIcoDiv hp a b + 1
  证明: by
  rw [add_comm]; rw [toIcoDiv_add_right]

@[simp]

Depends on / 依赖: add_comm, toIcoDiv_add_right
-/
theorem toIcoDiv_add_left (a b : α) : toIcoDiv hp a (p + b) = toIcoDiv hp a b + 1 := by
  rw [add_comm]; rw [toIcoDiv_add_right]

@[simp]
/--
theorem `toIcoDiv_add_left'` / 定理 `toIcoDiv_add_left'`

English:
theorem toIcoDiv_add_left'
  given: (a b : α)
  statement: toIcoDiv hp (p + a) b = toIcoDiv hp a b - 1
  proof: by
  rw [add_comm]; rw [toIcoDiv_add_right']

@[simp]

中文:
定理 toIcoDiv_add_left'
  条件: (a b : α)
  结论: toIcoDiv hp (p + a) b = toIcoDiv hp a b - 1
  证明: by
  rw [add_comm]; rw [toIcoDiv_add_right']

@[simp]

Depends on / 依赖: add_comm, toIcoDiv_add_right
-/
theorem toIcoDiv_add_left' (a b : α) : toIcoDiv hp (p + a) b = toIcoDiv hp a b - 1 := by
  rw [add_comm]; rw [toIcoDiv_add_right']

@[simp]
/--
theorem `toIocDiv_add_left` / 定理 `toIocDiv_add_left`

English:
theorem toIocDiv_add_left
  given: (a b : α)
  statement: toIocDiv hp a (p + b) = toIocDiv hp a b + 1
  proof: by
  rw [add_comm]; rw [toIocDiv_add_right]

@[simp]

中文:
定理 toIocDiv_add_left
  条件: (a b : α)
  结论: toIocDiv hp a (p + b) = toIocDiv hp a b + 1
  证明: by
  rw [add_comm]; rw [toIocDiv_add_right]

@[simp]

Depends on / 依赖: add_comm, toIocDiv_add_right
-/
theorem toIocDiv_add_left (a b : α) : toIocDiv hp a (p + b) = toIocDiv hp a b + 1 := by
  rw [add_comm]; rw [toIocDiv_add_right]

@[simp]
/--
theorem `toIocDiv_add_left'` / 定理 `toIocDiv_add_left'`

English:
theorem toIocDiv_add_left'
  given: (a b : α)
  statement: toIocDiv hp (p + a) b = toIocDiv hp a b - 1
  proof: by
  rw [add_comm]; rw [toIocDiv_add_right']

@[simp]

中文:
定理 toIocDiv_add_left'
  条件: (a b : α)
  结论: toIocDiv hp (p + a) b = toIocDiv hp a b - 1
  证明: by
  rw [add_comm]; rw [toIocDiv_add_right']

@[simp]

Depends on / 依赖: add_comm, toIocDiv_add_right
-/
theorem toIocDiv_add_left' (a b : α) : toIocDiv hp (p + a) b = toIocDiv hp a b - 1 := by
  rw [add_comm]; rw [toIocDiv_add_right']

@[simp]
/--
theorem `toIcoDiv_sub` / 定理 `toIcoDiv_sub`

English:
theorem toIcoDiv_sub
  given: (a b : α)
  statement: toIcoDiv hp a (b - p) = toIcoDiv hp a b - 1
  proof: by
  simpa only [one_zsmul] using toIcoDiv_sub_zsmul hp a b 1

@[simp]

中文:
定理 toIcoDiv_sub
  条件: (a b : α)
  结论: toIcoDiv hp a (b - p) = toIcoDiv hp a b - 1
  证明: by
  simpa only [one_zsmul] using toIcoDiv_sub_zsmul hp a b 1

@[simp]

Depends on / 依赖: one_zsmul, toIcoDiv_sub_zsmul
-/
theorem toIcoDiv_sub (a b : α) : toIcoDiv hp a (b - p) = toIcoDiv hp a b - 1 := by
  simpa only [one_zsmul] using toIcoDiv_sub_zsmul hp a b 1

@[simp]
/--
theorem `toIcoDiv_sub'` / 定理 `toIcoDiv_sub'`

English:
theorem toIcoDiv_sub'
  given: (a b : α)
  statement: toIcoDiv hp (a - p) b = toIcoDiv hp a b + 1
  proof: by
  simpa only [one_zsmul] using toIcoDiv_sub_zsmul' hp a b 1

@[simp]

中文:
定理 toIcoDiv_sub'
  条件: (a b : α)
  结论: toIcoDiv hp (a - p) b = toIcoDiv hp a b + 1
  证明: by
  simpa only [one_zsmul] using toIcoDiv_sub_zsmul' hp a b 1

@[simp]

Depends on / 依赖: one_zsmul, toIcoDiv_sub_zsmul
-/
theorem toIcoDiv_sub' (a b : α) : toIcoDiv hp (a - p) b = toIcoDiv hp a b + 1 := by
  simpa only [one_zsmul] using toIcoDiv_sub_zsmul' hp a b 1

@[simp]
/--
theorem `toIocDiv_sub` / 定理 `toIocDiv_sub`

English:
theorem toIocDiv_sub
  given: (a b : α)
  statement: toIocDiv hp a (b - p) = toIocDiv hp a b - 1
  proof: by
  simpa only [one_zsmul] using toIocDiv_sub_zsmul hp a b 1

@[simp]

中文:
定理 toIocDiv_sub
  条件: (a b : α)
  结论: toIocDiv hp a (b - p) = toIocDiv hp a b - 1
  证明: by
  simpa only [one_zsmul] using toIocDiv_sub_zsmul hp a b 1

@[simp]

Depends on / 依赖: one_zsmul, toIocDiv_sub_zsmul
-/
theorem toIocDiv_sub (a b : α) : toIocDiv hp a (b - p) = toIocDiv hp a b - 1 := by
  simpa only [one_zsmul] using toIocDiv_sub_zsmul hp a b 1

@[simp]
/--
theorem `toIocDiv_sub'` / 定理 `toIocDiv_sub'`

English:
theorem toIocDiv_sub'
  given: (a b : α)
  statement: toIocDiv hp (a - p) b = toIocDiv hp a b + 1
  proof: by
  simpa only [one_zsmul] using toIocDiv_sub_zsmul' hp a b 1

中文:
定理 toIocDiv_sub'
  条件: (a b : α)
  结论: toIocDiv hp (a - p) b = toIocDiv hp a b + 1
  证明: by
  simpa only [one_zsmul] using toIocDiv_sub_zsmul' hp a b 1

Depends on / 依赖: one_zsmul, toIocDiv_sub_zsmul
-/
theorem toIocDiv_sub' (a b : α) : toIocDiv hp (a - p) b = toIocDiv hp a b + 1 := by
  simpa only [one_zsmul] using toIocDiv_sub_zsmul' hp a b 1

/--
theorem `toIcoDiv_sub_eq_toIcoDiv_add` / 定理 `toIcoDiv_sub_eq_toIcoDiv_add`

English:
theorem toIcoDiv_sub_eq_toIcoDiv_add
  given: (a b c : α)
  proof: by
  apply toIcoDiv_eq_of_sub_zsmul_mem_Ico
  rw [← sub_right_comm]; rw [Set.sub_mem_Ico_iff_left]; rw [add_right_comm]
  exact sub_toIcoDiv_zsmul_mem_Ico hp (a + c) b

中文:
定理 toIcoDiv_sub_eq_toIcoDiv_add
  条件: (a b c : α)
  证明: by
  apply toIcoDiv_eq_of_sub_zsmul_mem_Ico
  rw [← sub_right_comm]; rw [Set.sub_mem_Ico_iff_left]; rw [add_right_comm]
  exact sub_toIcoDiv_zsmul_mem_Ico hp (a + c) b

Depends on / 依赖: Set.sub_mem_Ico_iff_left, add_right_comm, sub_mem_Ico_iff_left, sub_right_comm, sub_toIcoDiv_zsmul_mem_Ico, toIcoDiv_eq_of_sub_zsmul_mem_Ico
-/
theorem toIcoDiv_sub_eq_toIcoDiv_add (a b c : α) :
    toIcoDiv hp a (b - c) = toIcoDiv hp (a + c) b := by
  apply toIcoDiv_eq_of_sub_zsmul_mem_Ico
  rw [← sub_right_comm]; rw [Set.sub_mem_Ico_iff_left]; rw [add_right_comm]
  exact sub_toIcoDiv_zsmul_mem_Ico hp (a + c) b

/--
theorem `toIocDiv_sub_eq_toIocDiv_add` / 定理 `toIocDiv_sub_eq_toIocDiv_add`

English:
theorem toIocDiv_sub_eq_toIocDiv_add
  given: (a b c : α)
  proof: by
  apply toIocDiv_eq_of_sub_zsmul_mem_Ioc
  rw [← sub_right_comm]; rw [Set.sub_mem_Ioc_iff_left]; rw [add_right_comm]
  exact sub_toIocDiv_zsmul_mem_Ioc hp (a + c) b

中文:
定理 toIocDiv_sub_eq_toIocDiv_add
  条件: (a b c : α)
  证明: by
  apply toIocDiv_eq_of_sub_zsmul_mem_Ioc
  rw [← sub_right_comm]; rw [Set.sub_mem_Ioc_iff_left]; rw [add_right_comm]
  exact sub_toIocDiv_zsmul_mem_Ioc hp (a + c) b

Depends on / 依赖: Set.sub_mem_Ioc_iff_left, add_right_comm, sub_mem_Ioc_iff_left, sub_right_comm, sub_toIocDiv_zsmul_mem_Ioc, toIocDiv_eq_of_sub_zsmul_mem_Ioc
-/
theorem toIocDiv_sub_eq_toIocDiv_add (a b c : α) :
    toIocDiv hp a (b - c) = toIocDiv hp (a + c) b := by
  apply toIocDiv_eq_of_sub_zsmul_mem_Ioc
  rw [← sub_right_comm]; rw [Set.sub_mem_Ioc_iff_left]; rw [add_right_comm]
  exact sub_toIocDiv_zsmul_mem_Ioc hp (a + c) b

/--
theorem `toIcoDiv_sub_eq_toIcoDiv_add'` / 定理 `toIcoDiv_sub_eq_toIcoDiv_add'`

English:
theorem toIcoDiv_sub_eq_toIcoDiv_add'
  given: (a b c : α)
  proof: by
  rw [← sub_neg_eq_add]; rw [toIcoDiv_sub_eq_toIcoDiv_add]; rw [sub_eq_add_neg]

中文:
定理 toIcoDiv_sub_eq_toIcoDiv_add'
  条件: (a b c : α)
  证明: by
  rw [← sub_neg_eq_add]; rw [toIcoDiv_sub_eq_toIcoDiv_add]; rw [sub_eq_add_neg]

Depends on / 依赖: sub_eq_add_neg, sub_neg_eq_add, toIcoDiv_sub_eq_toIcoDiv_add
-/
theorem toIcoDiv_sub_eq_toIcoDiv_add' (a b c : α) :
    toIcoDiv hp (a - c) b = toIcoDiv hp a (b + c) := by
  rw [← sub_neg_eq_add]; rw [toIcoDiv_sub_eq_toIcoDiv_add]; rw [sub_eq_add_neg]

/--
theorem `toIocDiv_sub_eq_toIocDiv_add'` / 定理 `toIocDiv_sub_eq_toIocDiv_add'`

English:
theorem toIocDiv_sub_eq_toIocDiv_add'
  given: (a b c : α)
  proof: by
  rw [← sub_neg_eq_add]; rw [toIocDiv_sub_eq_toIocDiv_add]; rw [sub_eq_add_neg]

中文:
定理 toIocDiv_sub_eq_toIocDiv_add'
  条件: (a b c : α)
  证明: by
  rw [← sub_neg_eq_add]; rw [toIocDiv_sub_eq_toIocDiv_add]; rw [sub_eq_add_neg]

Depends on / 依赖: sub_eq_add_neg, sub_neg_eq_add, toIocDiv_sub_eq_toIocDiv_add
-/
theorem toIocDiv_sub_eq_toIocDiv_add' (a b c : α) :
    toIocDiv hp (a - c) b = toIocDiv hp a (b + c) := by
  rw [← sub_neg_eq_add]; rw [toIocDiv_sub_eq_toIocDiv_add]; rw [sub_eq_add_neg]

/--
theorem `toIcoDiv_neg` / 定理 `toIcoDiv_neg`

English:
theorem toIcoDiv_neg
  given: (a b : α)
  statement: toIcoDiv hp a (-b) = -(toIocDiv hp (-a) b + 1)
  proof: by
  suffices toIcoDiv hp a (-b) = -toIocDiv hp (-(a + p)) b by
    rwa [neg_add, ← sub_eq_add_neg, toIocDiv_sub_eq_toIocDiv_add', toIocDiv_add_right] at this
  rw [← neg_eq_iff_eq_neg]; rw [eq_comm]
  apply toIocDiv_eq_of_sub_zsmul_mem_Ioc
  obtain ⟨hc, ho⟩ := sub_toIcoDiv_zsmul_mem_Ico hp a (-b)
 

中文:
定理 toIcoDiv_neg
  条件: (a b : α)
  结论: toIcoDiv hp a (-b) = -(toIocDiv hp (-a) b + 1)
  证明: by
  suffices toIcoDiv hp a (-b) = -toIocDiv hp (-(a + p)) b by
    rwa [neg_add, ← sub_eq_add_neg, toIocDiv_sub_eq_toIocDiv_add', toIocDiv_add_right] at this
  rw [← neg_eq_iff_eq_neg]; rw [eq_comm]
  apply toIocDiv_eq_of_sub_zsmul_mem_Ioc
  obtain ⟨hc, ho⟩ := sub_toIcoDiv_zsmul_mem_Ico hp a (-b)
 

Depends on / 依赖: eq_comm, hc.trans_eq, neg_add, neg_add_c, neg_eq_iff_eq_neg, neg_le_neg_iff, neg_lt_neg_iff, neg_neg, neg_smul, neg_sub, sub_eq_add_neg, sub_toIcoDiv_zsmul_mem_Ico, toIcoDiv, toIocDiv, toIocDiv_add_right, toIocDiv_eq_of_sub_zsmul_mem_Ioc, toIocDiv_sub_eq_toIocDiv_add, trans_eq
-/
theorem toIcoDiv_neg (a b : α) : toIcoDiv hp a (-b) = -(toIocDiv hp (-a) b + 1) := by
  suffices toIcoDiv hp a (-b) = -toIocDiv hp (-(a + p)) b by
    rwa [neg_add, ← sub_eq_add_neg, toIocDiv_sub_eq_toIocDiv_add', toIocDiv_add_right] at this
  rw [← neg_eq_iff_eq_neg]; rw [eq_comm]
  apply toIocDiv_eq_of_sub_zsmul_mem_Ioc
  obtain ⟨hc, ho⟩ := sub_toIcoDiv_zsmul_mem_Ico hp a (-b)
  rw [← neg_lt_neg_iff]; rw [neg_sub' (-b)]; rw [neg_neg]; rw [← neg_smul] at ho
  rw [← neg_le_neg_iff]; rw [neg_sub' (-b)]; rw [neg_neg]; rw [← neg_smul] at hc
  refine ⟨ho, hc.trans_eq ?_⟩
  rw [neg_add]; rw [neg_add_cancel_right]

/--
theorem `toIcoDiv_neg'` / 定理 `toIcoDiv_neg'`

English:
theorem toIcoDiv_neg'
  given: (a b : α)
  statement: toIcoDiv hp (-a) b = -(toIocDiv hp a (-b) + 1)
  proof: by
  simpa only [neg_neg] using toIcoDiv_neg hp (-a) (-b)

中文:
定理 toIcoDiv_neg'
  条件: (a b : α)
  结论: toIcoDiv hp (-a) b = -(toIocDiv hp a (-b) + 1)
  证明: by
  simpa only [neg_neg] using toIcoDiv_neg hp (-a) (-b)

Depends on / 依赖: neg_neg, toIcoDiv_neg
-/
theorem toIcoDiv_neg' (a b : α) : toIcoDiv hp (-a) b = -(toIocDiv hp a (-b) + 1) := by
  simpa only [neg_neg] using toIcoDiv_neg hp (-a) (-b)

/--
theorem `toIocDiv_neg` / 定理 `toIocDiv_neg`

English:
theorem toIocDiv_neg
  given: (a b : α)
  statement: toIocDiv hp a (-b) = -(toIcoDiv hp (-a) b + 1)
  proof: by
  rw [← neg_neg b]; rw [toIcoDiv_neg]; rw [neg_neg]; rw [neg_neg]; rw [neg_add']; rw [neg_neg]; rw [add_sub_cancel_right]

中文:
定理 toIocDiv_neg
  条件: (a b : α)
  结论: toIocDiv hp a (-b) = -(toIcoDiv hp (-a) b + 1)
  证明: by
  rw [← neg_neg b]; rw [toIcoDiv_neg]; rw [neg_neg]; rw [neg_neg]; rw [neg_add']; rw [neg_neg]; rw [add_sub_cancel_right]

Depends on / 依赖: add_sub_cancel_right, neg_add, neg_neg, toIcoDiv_neg
-/
theorem toIocDiv_neg (a b : α) : toIocDiv hp a (-b) = -(toIcoDiv hp (-a) b + 1) := by
  rw [← neg_neg b]; rw [toIcoDiv_neg]; rw [neg_neg]; rw [neg_neg]; rw [neg_add']; rw [neg_neg]; rw [add_sub_cancel_right]

/--
theorem `toIocDiv_neg'` / 定理 `toIocDiv_neg'`

English:
theorem toIocDiv_neg'
  given: (a b : α)
  statement: toIocDiv hp (-a) b = -(toIcoDiv hp a (-b) + 1)
  proof: by
  simpa only [neg_neg] using toIocDiv_neg hp (-a) (-b)

@[simp]

中文:
定理 toIocDiv_neg'
  条件: (a b : α)
  结论: toIocDiv hp (-a) b = -(toIcoDiv hp a (-b) + 1)
  证明: by
  simpa only [neg_neg] using toIocDiv_neg hp (-a) (-b)

@[simp]

Depends on / 依赖: neg_neg, toIocDiv_neg
-/
theorem toIocDiv_neg' (a b : α) : toIocDiv hp (-a) b = -(toIcoDiv hp a (-b) + 1) := by
  simpa only [neg_neg] using toIocDiv_neg hp (-a) (-b)

@[simp]
/--
theorem `toIcoMod_add_zsmul` / 定理 `toIcoMod_add_zsmul`

English:
theorem toIcoMod_add_zsmul
  given: (a b : α) (m : Int)
  statement: toIcoMod hp a (b + m • p) = toIcoMod hp a b
  proof: by
  rw [toIcoMod]; rw [toIcoDiv_add_zsmul]; rw [toIcoMod]; rw [add_smul]
  abel

@[simp]

中文:
定理 toIcoMod_add_zsmul
  条件: (a b : α) (m : 整数)
  结论: toIcoMod hp a (b + m • p) = toIcoMod hp a b
  证明: by
  rw [toIcoMod]; rw [toIcoDiv_add_zsmul]; rw [toIcoMod]; rw [add_smul]
  abel

@[simp]

Depends on / 依赖: add_smul, toIcoDiv_add_zsmul, toIcoMod
-/
theorem toIcoMod_add_zsmul (a b : α) (m : Int) : toIcoMod hp a (b + m • p) = toIcoMod hp a b := by
  rw [toIcoMod]; rw [toIcoDiv_add_zsmul]; rw [toIcoMod]; rw [add_smul]
  abel

@[simp]
/--
theorem `toIcoMod_add_nsmul` / 定理 `toIcoMod_add_nsmul`

English:
theorem toIcoMod_add_nsmul
  given: (a b : α) (m : Nat)
  statement: toIcoMod hp a (b + m • p) = toIcoMod hp a b
  proof: mod_cast toIcoMod_add_zsmul hp a b m

@[simp]

中文:
定理 toIcoMod_add_nsmul
  条件: (a b : α) (m : 自然数)
  结论: toIcoMod hp a (b + m • p) = toIcoMod hp a b
  证明: mod_cast toIcoMod_add_zsmul hp a b m

@[simp]

Depends on / 依赖: Monoid, Quotient, conGen, mod_cast, toIcoMod_add_zsmul
-/
theorem toIcoMod_add_nsmul (a b : α) (m : Nat) : toIcoMod hp a (b + m • p) = toIcoMod hp a b :=
  mod_cast toIcoMod_add_zsmul hp a b m

@[simp]
/--
theorem `toIcoMod_add_zsmul'` / 定理 `toIcoMod_add_zsmul'`

English:
theorem toIcoMod_add_zsmul'
  given: (a b : α) (m : Int)
  proof: by
  simp only [toIcoMod, toIcoDiv_add_zsmul', sub_smul, sub_add]

@[simp]

中文:
定理 toIcoMod_add_zsmul'
  条件: (a b : α) (m : 整数)
  证明: by
  simp only [toIcoMod, toIcoDiv_add_zsmul', sub_smul, sub_add]

@[simp]

Depends on / 依赖: sub_add, sub_smul, toIcoDiv_add_zsmul, toIcoMod
-/
theorem toIcoMod_add_zsmul' (a b : α) (m : Int) :
    toIcoMod hp (a + m • p) b = toIcoMod hp a b + m • p := by
  simp only [toIcoMod, toIcoDiv_add_zsmul', sub_smul, sub_add]

@[simp]
/--
theorem `toIcoMod_add_nsmul'` / 定理 `toIcoMod_add_nsmul'`

English:
theorem toIcoMod_add_nsmul'
  given: (a b : α) (m : Nat)
  proof: mod_cast toIcoMod_add_zsmul' hp a b m

@[simp]

中文:
定理 toIcoMod_add_nsmul'
  条件: (a b : α) (m : 自然数)
  证明: mod_cast toIcoMod_add_zsmul' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoMod_add_zsmul
-/
theorem toIcoMod_add_nsmul' (a b : α) (m : Nat) :
    toIcoMod hp (a + m • p) b = toIcoMod hp a b + m • p :=
  mod_cast toIcoMod_add_zsmul' hp a b m

@[simp]
/--
theorem `toIocMod_add_zsmul` / 定理 `toIocMod_add_zsmul`

English:
theorem toIocMod_add_zsmul
  given: (a b : α) (m : Int)
  statement: toIocMod hp a (b + m • p) = toIocMod hp a b
  proof: by
  rw [toIocMod]; rw [toIocDiv_add_zsmul]; rw [toIocMod]; rw [add_smul]
  abel

@[simp]

中文:
定理 toIocMod_add_zsmul
  条件: (a b : α) (m : 整数)
  结论: toIocMod hp a (b + m • p) = toIocMod hp a b
  证明: by
  rw [toIocMod]; rw [toIocDiv_add_zsmul]; rw [toIocMod]; rw [add_smul]
  abel

@[simp]

Depends on / 依赖: add_smul, toIocDiv_add_zsmul, toIocMod
-/
theorem toIocMod_add_zsmul (a b : α) (m : Int) : toIocMod hp a (b + m • p) = toIocMod hp a b := by
  rw [toIocMod]; rw [toIocDiv_add_zsmul]; rw [toIocMod]; rw [add_smul]
  abel

@[simp]
/--
theorem `toIocMod_add_nsmul` / 定理 `toIocMod_add_nsmul`

English:
theorem toIocMod_add_nsmul
  given: (a b : α) (m : Nat)
  statement: toIocMod hp a (b + m • p) = toIocMod hp a b
  proof: mod_cast toIocMod_add_zsmul hp a b m

@[simp]

中文:
定理 toIocMod_add_nsmul
  条件: (a b : α) (m : 自然数)
  结论: toIocMod hp a (b + m • p) = toIocMod hp a b
  证明: mod_cast toIocMod_add_zsmul hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocMod_add_zsmul
-/
theorem toIocMod_add_nsmul (a b : α) (m : Nat) : toIocMod hp a (b + m • p) = toIocMod hp a b :=
  mod_cast toIocMod_add_zsmul hp a b m

@[simp]
/--
theorem `toIocMod_add_zsmul'` / 定理 `toIocMod_add_zsmul'`

English:
theorem toIocMod_add_zsmul'
  given: (a b : α) (m : Int)
  proof: by
  simp only [toIocMod, toIocDiv_add_zsmul', sub_smul, sub_add]

@[simp]

中文:
定理 toIocMod_add_zsmul'
  条件: (a b : α) (m : 整数)
  证明: by
  simp only [toIocMod, toIocDiv_add_zsmul', sub_smul, sub_add]

@[simp]

Depends on / 依赖: sub_add, sub_smul, toIocDiv_add_zsmul, toIocMod
-/
theorem toIocMod_add_zsmul' (a b : α) (m : Int) :
    toIocMod hp (a + m • p) b = toIocMod hp a b + m • p := by
  simp only [toIocMod, toIocDiv_add_zsmul', sub_smul, sub_add]

@[simp]
/--
theorem `toIocMod_add_nsmul'` / 定理 `toIocMod_add_nsmul'`

English:
theorem toIocMod_add_nsmul'
  given: (a b : α) (m : Nat)
  proof: mod_cast toIocMod_add_zsmul' hp a b m

@[simp]

中文:
定理 toIocMod_add_nsmul'
  条件: (a b : α) (m : 自然数)
  证明: mod_cast toIocMod_add_zsmul' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocMod_add_zsmul
-/
theorem toIocMod_add_nsmul' (a b : α) (m : Nat) :
    toIocMod hp (a + m • p) b = toIocMod hp a b + m • p :=
  mod_cast toIocMod_add_zsmul' hp a b m

@[simp]
/--
theorem `toIcoMod_zsmul_add` / 定理 `toIcoMod_zsmul_add`

English:
theorem toIcoMod_zsmul_add
  given: (a b : α) (m : Int)
  statement: toIcoMod hp a (m • p + b) = toIcoMod hp a b
  proof: by
  rw [add_comm]; rw [toIcoMod_add_zsmul]

@[simp]

中文:
定理 toIcoMod_zsmul_add
  条件: (a b : α) (m : 整数)
  结论: toIcoMod hp a (m • p + b) = toIcoMod hp a b
  证明: by
  rw [add_comm]; rw [toIcoMod_add_zsmul]

@[simp]

Depends on / 依赖: add_comm, toIcoMod_add_zsmul
-/
theorem toIcoMod_zsmul_add (a b : α) (m : Int) : toIcoMod hp a (m • p + b) = toIcoMod hp a b := by
  rw [add_comm]; rw [toIcoMod_add_zsmul]

@[simp]
/--
theorem `toIcoMod_nsmul_add` / 定理 `toIcoMod_nsmul_add`

English:
theorem toIcoMod_nsmul_add
  given: (a b : α) (m : Nat)
  statement: toIcoMod hp a (m • p + b) = toIcoMod hp a b
  proof: mod_cast toIcoMod_zsmul_add hp a b m

@[simp]

中文:
定理 toIcoMod_nsmul_add
  条件: (a b : α) (m : 自然数)
  结论: toIcoMod hp a (m • p + b) = toIcoMod hp a b
  证明: mod_cast toIcoMod_zsmul_add hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoMod_zsmul_add
-/
theorem toIcoMod_nsmul_add (a b : α) (m : Nat) : toIcoMod hp a (m • p + b) = toIcoMod hp a b :=
  mod_cast toIcoMod_zsmul_add hp a b m

@[simp]
/--
theorem `toIcoMod_zsmul_add'` / 定理 `toIcoMod_zsmul_add'`

English:
theorem toIcoMod_zsmul_add'
  given: (a b : α) (m : Int)
  proof: by
  rw [add_comm]; rw [toIcoMod_add_zsmul']; rw [add_comm]

@[simp]

中文:
定理 toIcoMod_zsmul_add'
  条件: (a b : α) (m : 整数)
  证明: by
  rw [add_comm]; rw [toIcoMod_add_zsmul']; rw [add_comm]

@[simp]

Depends on / 依赖: add_comm, toIcoMod_add_zsmul
-/
theorem toIcoMod_zsmul_add' (a b : α) (m : Int) :
    toIcoMod hp (m • p + a) b = m • p + toIcoMod hp a b := by
  rw [add_comm]; rw [toIcoMod_add_zsmul']; rw [add_comm]

@[simp]
/--
theorem `toIcoMod_nsmul_add'` / 定理 `toIcoMod_nsmul_add'`

English:
theorem toIcoMod_nsmul_add'
  given: (a b : α) (m : Nat)
  proof: mod_cast toIcoMod_zsmul_add' hp a b m

@[simp]

中文:
定理 toIcoMod_nsmul_add'
  条件: (a b : α) (m : 自然数)
  证明: mod_cast toIcoMod_zsmul_add' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoMod_zsmul_add
-/
theorem toIcoMod_nsmul_add' (a b : α) (m : Nat) :
    toIcoMod hp (m • p + a) b = m • p + toIcoMod hp a b :=
  mod_cast toIcoMod_zsmul_add' hp a b m

@[simp]
/--
theorem `toIocMod_zsmul_add` / 定理 `toIocMod_zsmul_add`

English:
theorem toIocMod_zsmul_add
  given: (a b : α) (m : Int)
  statement: toIocMod hp a (m • p + b) = toIocMod hp a b
  proof: by
  rw [add_comm]; rw [toIocMod_add_zsmul]

@[simp]

中文:
定理 toIocMod_zsmul_add
  条件: (a b : α) (m : 整数)
  结论: toIocMod hp a (m • p + b) = toIocMod hp a b
  证明: by
  rw [add_comm]; rw [toIocMod_add_zsmul]

@[simp]

Depends on / 依赖: add_comm, toIocMod_add_zsmul
-/
theorem toIocMod_zsmul_add (a b : α) (m : Int) : toIocMod hp a (m • p + b) = toIocMod hp a b := by
  rw [add_comm]; rw [toIocMod_add_zsmul]

@[simp]
/--
theorem `toIocMod_nsmul_add` / 定理 `toIocMod_nsmul_add`

English:
theorem toIocMod_nsmul_add
  given: (a b : α) (m : Nat)
  statement: toIocMod hp a (m • p + b) = toIocMod hp a b
  proof: mod_cast toIocMod_zsmul_add hp a b m

@[simp]

中文:
定理 toIocMod_nsmul_add
  条件: (a b : α) (m : 自然数)
  结论: toIocMod hp a (m • p + b) = toIocMod hp a b
  证明: mod_cast toIocMod_zsmul_add hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocMod_zsmul_add
-/
theorem toIocMod_nsmul_add (a b : α) (m : Nat) : toIocMod hp a (m • p + b) = toIocMod hp a b :=
  mod_cast toIocMod_zsmul_add hp a b m

@[simp]
/--
theorem `toIocMod_zsmul_add'` / 定理 `toIocMod_zsmul_add'`

English:
theorem toIocMod_zsmul_add'
  given: (a b : α) (m : Int)
  proof: by
  rw [add_comm]; rw [toIocMod_add_zsmul']; rw [add_comm]

@[simp]

中文:
定理 toIocMod_zsmul_add'
  条件: (a b : α) (m : 整数)
  证明: by
  rw [add_comm]; rw [toIocMod_add_zsmul']; rw [add_comm]

@[simp]

Depends on / 依赖: add_comm, toIocMod_add_zsmul
-/
theorem toIocMod_zsmul_add' (a b : α) (m : Int) :
    toIocMod hp (m • p + a) b = m • p + toIocMod hp a b := by
  rw [add_comm]; rw [toIocMod_add_zsmul']; rw [add_comm]

@[simp]
/--
theorem `toIocMod_nsmul_add'` / 定理 `toIocMod_nsmul_add'`

English:
theorem toIocMod_nsmul_add'
  given: (a b : α) (m : Nat)
  proof: mod_cast toIocMod_zsmul_add' hp a b m

@[simp]

中文:
定理 toIocMod_nsmul_add'
  条件: (a b : α) (m : 自然数)
  证明: mod_cast toIocMod_zsmul_add' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocMod_zsmul_add
-/
theorem toIocMod_nsmul_add' (a b : α) (m : Nat) :
    toIocMod hp (m • p + a) b = m • p + toIocMod hp a b :=
  mod_cast toIocMod_zsmul_add' hp a b m

@[simp]
/--
theorem `toIcoMod_sub_zsmul` / 定理 `toIcoMod_sub_zsmul`

English:
theorem toIcoMod_sub_zsmul
  given: (a b : α) (m : Int)
  statement: toIcoMod hp a (b - m • p) = toIcoMod hp a b
  proof: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIcoMod_add_zsmul]

@[simp]

中文:
定理 toIcoMod_sub_zsmul
  条件: (a b : α) (m : 整数)
  结论: toIcoMod hp a (b - m • p) = toIcoMod hp a b
  证明: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIcoMod_add_zsmul]

@[simp]

Depends on / 依赖: neg_smul, sub_eq_add_neg, toIcoMod_add_zsmul
-/
theorem toIcoMod_sub_zsmul (a b : α) (m : Int) : toIcoMod hp a (b - m • p) = toIcoMod hp a b := by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIcoMod_add_zsmul]

@[simp]
/--
theorem `toIcoMod_sub_nsmul` / 定理 `toIcoMod_sub_nsmul`

English:
theorem toIcoMod_sub_nsmul
  given: (a b : α) (m : Nat)
  statement: toIcoMod hp a (b - m • p) = toIcoMod hp a b
  proof: mod_cast toIcoMod_sub_zsmul hp a b m

@[simp]

中文:
定理 toIcoMod_sub_nsmul
  条件: (a b : α) (m : 自然数)
  结论: toIcoMod hp a (b - m • p) = toIcoMod hp a b
  证明: mod_cast toIcoMod_sub_zsmul hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoMod_sub_zsmul
-/
theorem toIcoMod_sub_nsmul (a b : α) (m : Nat) : toIcoMod hp a (b - m • p) = toIcoMod hp a b :=
  mod_cast toIcoMod_sub_zsmul hp a b m

@[simp]
/--
theorem `toIcoMod_sub_zsmul'` / 定理 `toIcoMod_sub_zsmul'`

English:
theorem toIcoMod_sub_zsmul'
  given: (a b : α) (m : Int)
  proof: by
  simp_rw [sub_eq_add_neg, ← neg_smul, toIcoMod_add_zsmul']

@[simp]

中文:
定理 toIcoMod_sub_zsmul'
  条件: (a b : α) (m : 整数)
  证明: by
  simp_rw [sub_eq_add_neg, ← neg_smul, toIcoMod_add_zsmul']

@[simp]

Depends on / 依赖: neg_smul, simp_rw, sub_eq_add_neg, toIcoMod_add_zsmul
-/
theorem toIcoMod_sub_zsmul' (a b : α) (m : Int) :
    toIcoMod hp (a - m • p) b = toIcoMod hp a b - m • p := by
  simp_rw [sub_eq_add_neg, ← neg_smul, toIcoMod_add_zsmul']

@[simp]
/--
theorem `toIcoMod_sub_nsmul'` / 定理 `toIcoMod_sub_nsmul'`

English:
theorem toIcoMod_sub_nsmul'
  given: (a b : α) (m : Nat)
  proof: mod_cast toIcoMod_sub_zsmul' hp a b m

@[simp]

中文:
定理 toIcoMod_sub_nsmul'
  条件: (a b : α) (m : 自然数)
  证明: mod_cast toIcoMod_sub_zsmul' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoMod_sub_zsmul
-/
theorem toIcoMod_sub_nsmul' (a b : α) (m : Nat) :
    toIcoMod hp (a - m • p) b = toIcoMod hp a b - m • p :=
  mod_cast toIcoMod_sub_zsmul' hp a b m

@[simp]
/--
theorem `toIocMod_sub_zsmul` / 定理 `toIocMod_sub_zsmul`

English:
theorem toIocMod_sub_zsmul
  given: (a b : α) (m : Int)
  statement: toIocMod hp a (b - m • p) = toIocMod hp a b
  proof: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIocMod_add_zsmul]

@[simp]

中文:
定理 toIocMod_sub_zsmul
  条件: (a b : α) (m : 整数)
  结论: toIocMod hp a (b - m • p) = toIocMod hp a b
  证明: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIocMod_add_zsmul]

@[simp]

Depends on / 依赖: neg_smul, sub_eq_add_neg, toIocMod_add_zsmul
-/
theorem toIocMod_sub_zsmul (a b : α) (m : Int) : toIocMod hp a (b - m • p) = toIocMod hp a b := by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [toIocMod_add_zsmul]

@[simp]
/--
theorem `toIocMod_sub_nsmul` / 定理 `toIocMod_sub_nsmul`

English:
theorem toIocMod_sub_nsmul
  given: (a b : α) (m : Nat)
  statement: toIocMod hp a (b - m • p) = toIocMod hp a b
  proof: mod_cast toIocMod_sub_zsmul hp a b m

@[simp]

中文:
定理 toIocMod_sub_nsmul
  条件: (a b : α) (m : 自然数)
  结论: toIocMod hp a (b - m • p) = toIocMod hp a b
  证明: mod_cast toIocMod_sub_zsmul hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocMod_sub_zsmul
-/
theorem toIocMod_sub_nsmul (a b : α) (m : Nat) : toIocMod hp a (b - m • p) = toIocMod hp a b :=
  mod_cast toIocMod_sub_zsmul hp a b m

@[simp]
/--
theorem `toIocMod_sub_zsmul'` / 定理 `toIocMod_sub_zsmul'`

English:
theorem toIocMod_sub_zsmul'
  given: (a b : α) (m : Int)
  proof: by
  simp_rw [sub_eq_add_neg, ← neg_smul, toIocMod_add_zsmul']

@[simp]

中文:
定理 toIocMod_sub_zsmul'
  条件: (a b : α) (m : 整数)
  证明: by
  simp_rw [sub_eq_add_neg, ← neg_smul, toIocMod_add_zsmul']

@[simp]

Depends on / 依赖: neg_smul, simp_rw, sub_eq_add_neg, toIocMod_add_zsmul
-/
theorem toIocMod_sub_zsmul' (a b : α) (m : Int) :
    toIocMod hp (a - m • p) b = toIocMod hp a b - m • p := by
  simp_rw [sub_eq_add_neg, ← neg_smul, toIocMod_add_zsmul']

@[simp]
/--
theorem `toIocMod_sub_nsmul'` / 定理 `toIocMod_sub_nsmul'`

English:
theorem toIocMod_sub_nsmul'
  given: (a b : α) (m : Nat)
  proof: mod_cast toIocMod_sub_zsmul' hp a b m

@[simp]

中文:
定理 toIocMod_sub_nsmul'
  条件: (a b : α) (m : 自然数)
  证明: mod_cast toIocMod_sub_zsmul' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocMod_sub_zsmul
-/
theorem toIocMod_sub_nsmul' (a b : α) (m : Nat) :
    toIocMod hp (a - m • p) b = toIocMod hp a b - m • p :=
  mod_cast toIocMod_sub_zsmul' hp a b m

@[simp]
/--
theorem `toIcoMod_add_right` / 定理 `toIcoMod_add_right`

English:
theorem toIcoMod_add_right
  given: (a b : α)
  statement: toIcoMod hp a (b + p) = toIcoMod hp a b
  proof: by
  simpa only [one_zsmul] using toIcoMod_add_zsmul hp a b 1

@[simp]

中文:
定理 toIcoMod_add_right
  条件: (a b : α)
  结论: toIcoMod hp a (b + p) = toIcoMod hp a b
  证明: by
  simpa only [one_zsmul] using toIcoMod_add_zsmul hp a b 1

@[simp]

Depends on / 依赖: one_zsmul, toIcoMod_add_zsmul
-/
theorem toIcoMod_add_right (a b : α) : toIcoMod hp a (b + p) = toIcoMod hp a b := by
  simpa only [one_zsmul] using toIcoMod_add_zsmul hp a b 1

@[simp]
/--
theorem `toIcoMod_add_right'` / 定理 `toIcoMod_add_right'`

English:
theorem toIcoMod_add_right'
  given: (a b : α)
  statement: toIcoMod hp (a + p) b = toIcoMod hp a b + p
  proof: by
  simpa only [one_zsmul] using toIcoMod_add_zsmul' hp a b 1

@[simp]

中文:
定理 toIcoMod_add_right'
  条件: (a b : α)
  结论: toIcoMod hp (a + p) b = toIcoMod hp a b + p
  证明: by
  simpa only [one_zsmul] using toIcoMod_add_zsmul' hp a b 1

@[simp]

Depends on / 依赖: one_zsmul, toIcoMod_add_zsmul
-/
theorem toIcoMod_add_right' (a b : α) : toIcoMod hp (a + p) b = toIcoMod hp a b + p := by
  simpa only [one_zsmul] using toIcoMod_add_zsmul' hp a b 1

@[simp]
/--
theorem `toIocMod_add_right` / 定理 `toIocMod_add_right`

English:
theorem toIocMod_add_right
  given: (a b : α)
  statement: toIocMod hp a (b + p) = toIocMod hp a b
  proof: by
  simpa only [one_zsmul] using toIocMod_add_zsmul hp a b 1

@[simp]

中文:
定理 toIocMod_add_right
  条件: (a b : α)
  结论: toIocMod hp a (b + p) = toIocMod hp a b
  证明: by
  simpa only [one_zsmul] using toIocMod_add_zsmul hp a b 1

@[simp]

Depends on / 依赖: one_zsmul, toIocMod_add_zsmul
-/
theorem toIocMod_add_right (a b : α) : toIocMod hp a (b + p) = toIocMod hp a b := by
  simpa only [one_zsmul] using toIocMod_add_zsmul hp a b 1

@[simp]
/--
theorem `toIocMod_add_right'` / 定理 `toIocMod_add_right'`

English:
theorem toIocMod_add_right'
  given: (a b : α)
  statement: toIocMod hp (a + p) b = toIocMod hp a b + p
  proof: by
  simpa only [one_zsmul] using toIocMod_add_zsmul' hp a b 1

@[simp]

中文:
定理 toIocMod_add_right'
  条件: (a b : α)
  结论: toIocMod hp (a + p) b = toIocMod hp a b + p
  证明: by
  simpa only [one_zsmul] using toIocMod_add_zsmul' hp a b 1

@[simp]

Depends on / 依赖: one_zsmul, toIocMod_add_zsmul
-/
theorem toIocMod_add_right' (a b : α) : toIocMod hp (a + p) b = toIocMod hp a b + p := by
  simpa only [one_zsmul] using toIocMod_add_zsmul' hp a b 1

@[simp]
/--
theorem `toIcoMod_add_left` / 定理 `toIcoMod_add_left`

English:
theorem toIcoMod_add_left
  given: (a b : α)
  statement: toIcoMod hp a (p + b) = toIcoMod hp a b
  proof: by
  rw [add_comm]; rw [toIcoMod_add_right]

@[simp]

中文:
定理 toIcoMod_add_left
  条件: (a b : α)
  结论: toIcoMod hp a (p + b) = toIcoMod hp a b
  证明: by
  rw [add_comm]; rw [toIcoMod_add_right]

@[simp]

Depends on / 依赖: add_comm, toIcoMod_add_right
-/
theorem toIcoMod_add_left (a b : α) : toIcoMod hp a (p + b) = toIcoMod hp a b := by
  rw [add_comm]; rw [toIcoMod_add_right]

@[simp]
/--
theorem `toIcoMod_add_left'` / 定理 `toIcoMod_add_left'`

English:
theorem toIcoMod_add_left'
  given: (a b : α)
  statement: toIcoMod hp (p + a) b = p + toIcoMod hp a b
  proof: by
  rw [add_comm]; rw [toIcoMod_add_right']; rw [add_comm]

@[simp]

中文:
定理 toIcoMod_add_left'
  条件: (a b : α)
  结论: toIcoMod hp (p + a) b = p + toIcoMod hp a b
  证明: by
  rw [add_comm]; rw [toIcoMod_add_right']; rw [add_comm]

@[simp]

Depends on / 依赖: add_comm, toIcoMod_add_right
-/
theorem toIcoMod_add_left' (a b : α) : toIcoMod hp (p + a) b = p + toIcoMod hp a b := by
  rw [add_comm]; rw [toIcoMod_add_right']; rw [add_comm]

@[simp]
/--
theorem `toIocMod_add_left` / 定理 `toIocMod_add_left`

English:
theorem toIocMod_add_left
  given: (a b : α)
  statement: toIocMod hp a (p + b) = toIocMod hp a b
  proof: by
  rw [add_comm]; rw [toIocMod_add_right]

@[simp]

中文:
定理 toIocMod_add_left
  条件: (a b : α)
  结论: toIocMod hp a (p + b) = toIocMod hp a b
  证明: by
  rw [add_comm]; rw [toIocMod_add_right]

@[simp]

Depends on / 依赖: add_comm, toIocMod_add_right
-/
theorem toIocMod_add_left (a b : α) : toIocMod hp a (p + b) = toIocMod hp a b := by
  rw [add_comm]; rw [toIocMod_add_right]

@[simp]
/--
theorem `toIocMod_add_left'` / 定理 `toIocMod_add_left'`

English:
theorem toIocMod_add_left'
  given: (a b : α)
  statement: toIocMod hp (p + a) b = p + toIocMod hp a b
  proof: by
  rw [add_comm]; rw [toIocMod_add_right']; rw [add_comm]

@[simp]

中文:
定理 toIocMod_add_left'
  条件: (a b : α)
  结论: toIocMod hp (p + a) b = p + toIocMod hp a b
  证明: by
  rw [add_comm]; rw [toIocMod_add_right']; rw [add_comm]

@[simp]

Depends on / 依赖: add_comm, toIocMod_add_right
-/
theorem toIocMod_add_left' (a b : α) : toIocMod hp (p + a) b = p + toIocMod hp a b := by
  rw [add_comm]; rw [toIocMod_add_right']; rw [add_comm]

@[simp]
/--
theorem `toIcoMod_sub` / 定理 `toIcoMod_sub`

English:
theorem toIcoMod_sub
  given: (a b : α)
  statement: toIcoMod hp a (b - p) = toIcoMod hp a b
  proof: by
  simpa only [one_zsmul] using toIcoMod_sub_zsmul hp a b 1

@[simp]

中文:
定理 toIcoMod_sub
  条件: (a b : α)
  结论: toIcoMod hp a (b - p) = toIcoMod hp a b
  证明: by
  simpa only [one_zsmul] using toIcoMod_sub_zsmul hp a b 1

@[simp]

Depends on / 依赖: one_zsmul, toIcoMod_sub_zsmul
-/
theorem toIcoMod_sub (a b : α) : toIcoMod hp a (b - p) = toIcoMod hp a b := by
  simpa only [one_zsmul] using toIcoMod_sub_zsmul hp a b 1

@[simp]
/--
theorem `toIcoMod_sub'` / 定理 `toIcoMod_sub'`

English:
theorem toIcoMod_sub'
  given: (a b : α)
  statement: toIcoMod hp (a - p) b = toIcoMod hp a b - p
  proof: by
  simpa only [one_zsmul] using toIcoMod_sub_zsmul' hp a b 1

@[simp]

中文:
定理 toIcoMod_sub'
  条件: (a b : α)
  结论: toIcoMod hp (a - p) b = toIcoMod hp a b - p
  证明: by
  simpa only [one_zsmul] using toIcoMod_sub_zsmul' hp a b 1

@[simp]

Depends on / 依赖: one_zsmul, toIcoMod_sub_zsmul
-/
theorem toIcoMod_sub' (a b : α) : toIcoMod hp (a - p) b = toIcoMod hp a b - p := by
  simpa only [one_zsmul] using toIcoMod_sub_zsmul' hp a b 1

@[simp]
/--
theorem `toIocMod_sub` / 定理 `toIocMod_sub`

English:
theorem toIocMod_sub
  given: (a b : α)
  statement: toIocMod hp a (b - p) = toIocMod hp a b
  proof: by
  simpa only [one_zsmul] using toIocMod_sub_zsmul hp a b 1

@[simp]

中文:
定理 toIocMod_sub
  条件: (a b : α)
  结论: toIocMod hp a (b - p) = toIocMod hp a b
  证明: by
  simpa only [one_zsmul] using toIocMod_sub_zsmul hp a b 1

@[simp]

Depends on / 依赖: one_zsmul, toIocMod_sub_zsmul
-/
theorem toIocMod_sub (a b : α) : toIocMod hp a (b - p) = toIocMod hp a b := by
  simpa only [one_zsmul] using toIocMod_sub_zsmul hp a b 1

@[simp]
/--
theorem `toIocMod_sub'` / 定理 `toIocMod_sub'`

English:
theorem toIocMod_sub'
  given: (a b : α)
  statement: toIocMod hp (a - p) b = toIocMod hp a b - p
  proof: by
  simpa only [one_zsmul] using toIocMod_sub_zsmul' hp a b 1

中文:
定理 toIocMod_sub'
  条件: (a b : α)
  结论: toIocMod hp (a - p) b = toIocMod hp a b - p
  证明: by
  simpa only [one_zsmul] using toIocMod_sub_zsmul' hp a b 1

Depends on / 依赖: one_zsmul, toIocMod_sub_zsmul
-/
theorem toIocMod_sub' (a b : α) : toIocMod hp (a - p) b = toIocMod hp a b - p := by
  simpa only [one_zsmul] using toIocMod_sub_zsmul' hp a b 1

/--
theorem `toIcoMod_sub_eq_sub` / 定理 `toIcoMod_sub_eq_sub`

English:
theorem toIcoMod_sub_eq_sub
  given: (a b c : α)
  statement: toIcoMod hp a (b - c) = toIcoMod hp (a + c) b - c
  proof: by
  simp_rw [toIcoMod, toIcoDiv_sub_eq_toIcoDiv_add, sub_right_comm]

中文:
定理 toIcoMod_sub_eq_sub
  条件: (a b c : α)
  结论: toIcoMod hp a (b - c) = toIcoMod hp (a + c) b - c
  证明: by
  simp_rw [toIcoMod, toIcoDiv_sub_eq_toIcoDiv_add, sub_right_comm]

Depends on / 依赖: simp_rw, sub_right_comm, toIcoDiv_sub_eq_toIcoDiv_add, toIcoMod
-/
theorem toIcoMod_sub_eq_sub (a b c : α) : toIcoMod hp a (b - c) = toIcoMod hp (a + c) b - c := by
  simp_rw [toIcoMod, toIcoDiv_sub_eq_toIcoDiv_add, sub_right_comm]

/--
theorem `toIocMod_sub_eq_sub` / 定理 `toIocMod_sub_eq_sub`

English:
theorem toIocMod_sub_eq_sub
  given: (a b c : α)
  statement: toIocMod hp a (b - c) = toIocMod hp (a + c) b - c
  proof: by
  simp_rw [toIocMod, toIocDiv_sub_eq_toIocDiv_add, sub_right_comm]

中文:
定理 toIocMod_sub_eq_sub
  条件: (a b c : α)
  结论: toIocMod hp a (b - c) = toIocMod hp (a + c) b - c
  证明: by
  simp_rw [toIocMod, toIocDiv_sub_eq_toIocDiv_add, sub_right_comm]

Depends on / 依赖: simp_rw, sub_right_comm, toIocDiv_sub_eq_toIocDiv_add, toIocMod
-/
theorem toIocMod_sub_eq_sub (a b c : α) : toIocMod hp a (b - c) = toIocMod hp (a + c) b - c := by
  simp_rw [toIocMod, toIocDiv_sub_eq_toIocDiv_add, sub_right_comm]

/--
theorem `toIcoMod_add_right_eq_add` / 定理 `toIcoMod_add_right_eq_add`

English:
theorem toIcoMod_add_right_eq_add
  given: (a b c : α)
  proof: by
  simp_rw [toIcoMod, toIcoDiv_sub_eq_toIcoDiv_add', sub_add_eq_add_sub]

中文:
定理 toIcoMod_add_right_eq_add
  条件: (a b c : α)
  证明: by
  simp_rw [toIcoMod, toIcoDiv_sub_eq_toIcoDiv_add', sub_add_eq_add_sub]

Depends on / 依赖: simp_rw, sub_add_eq_add_sub, toIcoDiv_sub_eq_toIcoDiv_add, toIcoMod
-/
theorem toIcoMod_add_right_eq_add (a b c : α) :
    toIcoMod hp a (b + c) = toIcoMod hp (a - c) b + c := by
  simp_rw [toIcoMod, toIcoDiv_sub_eq_toIcoDiv_add', sub_add_eq_add_sub]

/--
theorem `toIocMod_add_right_eq_add` / 定理 `toIocMod_add_right_eq_add`

English:
theorem toIocMod_add_right_eq_add
  given: (a b c : α)
  proof: by
  simp_rw [toIocMod, toIocDiv_sub_eq_toIocDiv_add', sub_add_eq_add_sub]

中文:
定理 toIocMod_add_right_eq_add
  条件: (a b c : α)
  证明: by
  simp_rw [toIocMod, toIocDiv_sub_eq_toIocDiv_add', sub_add_eq_add_sub]

Depends on / 依赖: simp_rw, sub_add_eq_add_sub, toIocDiv_sub_eq_toIocDiv_add, toIocMod
-/
theorem toIocMod_add_right_eq_add (a b c : α) :
    toIocMod hp a (b + c) = toIocMod hp (a - c) b + c := by
  simp_rw [toIocMod, toIocDiv_sub_eq_toIocDiv_add', sub_add_eq_add_sub]

/--
theorem `toIcoMod_neg` / 定理 `toIcoMod_neg`

English:
theorem toIcoMod_neg
  given: (a b : α)
  statement: toIcoMod hp a (-b) = p - toIocMod hp (-a) b
  proof: by
  simp_rw [toIcoMod, toIocMod, toIcoDiv_neg, neg_smul, add_smul]
  abel

中文:
定理 toIcoMod_neg
  条件: (a b : α)
  结论: toIcoMod hp a (-b) = p - toIocMod hp (-a) b
  证明: by
  simp_rw [toIcoMod, toIocMod, toIcoDiv_neg, neg_smul, add_smul]
  abel

Depends on / 依赖: add_smul, neg_smul, simp_rw, toIcoDiv_neg, toIcoMod, toIocMod
-/
theorem toIcoMod_neg (a b : α) : toIcoMod hp a (-b) = p - toIocMod hp (-a) b := by
  simp_rw [toIcoMod, toIocMod, toIcoDiv_neg, neg_smul, add_smul]
  abel

/--
theorem `toIcoMod_neg'` / 定理 `toIcoMod_neg'`

English:
theorem toIcoMod_neg'
  given: (a b : α)
  statement: toIcoMod hp (-a) b = p - toIocMod hp a (-b)
  proof: by
  simpa only [neg_neg] using toIcoMod_neg hp (-a) (-b)

中文:
定理 toIcoMod_neg'
  条件: (a b : α)
  结论: toIcoMod hp (-a) b = p - toIocMod hp a (-b)
  证明: by
  simpa only [neg_neg] using toIcoMod_neg hp (-a) (-b)

Depends on / 依赖: neg_neg, toIcoMod_neg
-/
theorem toIcoMod_neg' (a b : α) : toIcoMod hp (-a) b = p - toIocMod hp a (-b) := by
  simpa only [neg_neg] using toIcoMod_neg hp (-a) (-b)

/--
theorem `toIocMod_neg` / 定理 `toIocMod_neg`

English:
theorem toIocMod_neg
  given: (a b : α)
  statement: toIocMod hp a (-b) = p - toIcoMod hp (-a) b
  proof: by
  simp_rw [toIocMod, toIcoMod, toIocDiv_neg, neg_smul, add_smul]
  abel

中文:
定理 toIocMod_neg
  条件: (a b : α)
  结论: toIocMod hp a (-b) = p - toIcoMod hp (-a) b
  证明: by
  simp_rw [toIocMod, toIcoMod, toIocDiv_neg, neg_smul, add_smul]
  abel

Depends on / 依赖: add_smul, neg_smul, simp_rw, toIcoMod, toIocDiv_neg, toIocMod
-/
theorem toIocMod_neg (a b : α) : toIocMod hp a (-b) = p - toIcoMod hp (-a) b := by
  simp_rw [toIocMod, toIcoMod, toIocDiv_neg, neg_smul, add_smul]
  abel

/--
theorem `toIocMod_neg'` / 定理 `toIocMod_neg'`

English:
theorem toIocMod_neg'
  given: (a b : α)
  statement: toIocMod hp (-a) b = p - toIcoMod hp a (-b)
  proof: by
  simpa only [neg_neg] using toIocMod_neg hp (-a) (-b)

中文:
定理 toIocMod_neg'
  条件: (a b : α)
  结论: toIocMod hp (-a) b = p - toIcoMod hp a (-b)
  证明: by
  simpa only [neg_neg] using toIocMod_neg hp (-a) (-b)

Depends on / 依赖: neg_neg, toIocMod_neg
-/
theorem toIocMod_neg' (a b : α) : toIocMod hp (-a) b = p - toIcoMod hp a (-b) := by
  simpa only [neg_neg] using toIocMod_neg hp (-a) (-b)

/--
theorem `toIcoMod_eq_toIcoMod` / 定理 `toIcoMod_eq_toIcoMod`

English:
theorem toIcoMod_eq_toIcoMod
  statement: toIcoMod hp a b = toIcoMod hp a c ↔ exists n : Int, c - b = n • p
  proof: by
  refine ⟨fun h => ⟨toIcoDiv hp a c - toIcoDiv hp a b, ?_⟩, fun h => ?_⟩
  · conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hp a b, ← toIcoMod_add_toIcoDiv_zsmul hp a c]
    rw [h]; rw [sub_smul]
    abel
  · rcases h with ⟨z, hz⟩
    rw [sub_eq_iff_eq_add] at hz
    rw [hz]; rw [toIcoMod_zsmul_ad

中文:
定理 toIcoMod_eq_toIcoMod
  结论: toIcoMod hp a b = toIcoMod hp a c ↔ 存在 n : 整数, c - b = n • p
  证明: by
  refine ⟨fun h => ⟨toIcoDiv hp a c - toIcoDiv hp a b, ?_⟩, fun h => ?_⟩
  · conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hp a b, ← toIcoMod_add_toIcoDiv_zsmul hp a c]
    rw [h]; rw [sub_smul]
    abel
  · rcases h with ⟨z, hz⟩
    rw [sub_eq_iff_eq_add] at hz
    rw [hz]; rw [toIcoMod_zsmul_ad

Depends on / 依赖: conv_lhs, sub_eq_iff_eq_add, sub_smul, toIcoDiv, toIcoMod_add_toIcoDiv_zsmul, toIcoMod_zsmul_add
-/
theorem toIcoMod_eq_toIcoMod : toIcoMod hp a b = toIcoMod hp a c ↔ exists n : Int, c - b = n • p := by
  refine ⟨fun h => ⟨toIcoDiv hp a c - toIcoDiv hp a b, ?_⟩, fun h => ?_⟩
  · conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hp a b, ← toIcoMod_add_toIcoDiv_zsmul hp a c]
    rw [h]; rw [sub_smul]
    abel
  · rcases h with ⟨z, hz⟩
    rw [sub_eq_iff_eq_add] at hz
    rw [hz]; rw [toIcoMod_zsmul_add]

/--
theorem `toIocMod_eq_toIocMod` / 定理 `toIocMod_eq_toIocMod`

English:
theorem toIocMod_eq_toIocMod
  statement: toIocMod hp a b = toIocMod hp a c ↔ exists n : Int, c - b = n • p
  proof: by
  refine ⟨fun h => ⟨toIocDiv hp a c - toIocDiv hp a b, ?_⟩, fun h => ?_⟩
  · conv_lhs => rw [← toIocMod_add_toIocDiv_zsmul hp a b, ← toIocMod_add_toIocDiv_zsmul hp a c]
    rw [h]; rw [sub_smul]
    abel
  · rcases h with ⟨z, hz⟩
    rw [sub_eq_iff_eq_add] at hz
    rw [hz]; rw [toIocMod_zsmul_ad

中文:
定理 toIocMod_eq_toIocMod
  结论: toIocMod hp a b = toIocMod hp a c ↔ 存在 n : 整数, c - b = n • p
  证明: by
  refine ⟨fun h => ⟨toIocDiv hp a c - toIocDiv hp a b, ?_⟩, fun h => ?_⟩
  · conv_lhs => rw [← toIocMod_add_toIocDiv_zsmul hp a b, ← toIocMod_add_toIocDiv_zsmul hp a c]
    rw [h]; rw [sub_smul]
    abel
  · rcases h with ⟨z, hz⟩
    rw [sub_eq_iff_eq_add] at hz
    rw [hz]; rw [toIocMod_zsmul_ad

Depends on / 依赖: conv_lhs, sub_eq_iff_eq_add, sub_smul, toIocDiv, toIocMod_add_toIocDiv_zsmul, toIocMod_zsmul_add
-/
theorem toIocMod_eq_toIocMod : toIocMod hp a b = toIocMod hp a c ↔ exists n : Int, c - b = n • p := by
  refine ⟨fun h => ⟨toIocDiv hp a c - toIocDiv hp a b, ?_⟩, fun h => ?_⟩
  · conv_lhs => rw [← toIocMod_add_toIocDiv_zsmul hp a b, ← toIocMod_add_toIocDiv_zsmul hp a c]
    rw [h]; rw [sub_smul]
    abel
  · rcases h with ⟨z, hz⟩
    rw [sub_eq_iff_eq_add] at hz
    rw [hz]; rw [toIocMod_zsmul_add]

/-! ### Links between the `Ico` and `Ioc` variants applied to the same element -/


section IcoIoc

namespace AddCommGroup

/--
theorem `modEq_iff_toIcoMod_eq_left` / 定理 `modEq_iff_toIcoMod_eq_left`

English:
theorem modEq_iff_toIcoMod_eq_left
  statement: a ≡ b [PMOD p] ↔ toIcoMod hp a b = a
  proof: modEq_iff_eq_add_zsmul.trans
    ⟨by
      rintro ⟨n, rfl⟩
      rw [toIcoMod_add_zsmul]; rw [toIcoMod_apply_left], fun h => ⟨toIcoDiv hp a b, eq_add_of_sub_eq h⟩⟩

中文:
定理 modEq_iff_toIcoMod_eq_left
  结论: a ≡ b [PMOD p] ↔ toIcoMod hp a b = a
  证明: modEq_iff_eq_add_zsmul.trans
    ⟨by
      rintro ⟨n, rfl⟩
      rw [toIcoMod_add_zsmul]; rw [toIcoMod_apply_left], fun h => ⟨toIcoDiv hp a b, eq_add_of_sub_eq h⟩⟩

Depends on / 依赖: eq_add_of_sub_eq, modEq_iff_eq_add_zsmul, modEq_iff_eq_add_zsmul.trans, toIcoDiv, toIcoMod_add_zsmul, toIcoMod_apply_left
-/
theorem modEq_iff_toIcoMod_eq_left : a ≡ b [PMOD p] ↔ toIcoMod hp a b = a :=
  modEq_iff_eq_add_zsmul.trans
    ⟨by
      rintro ⟨n, rfl⟩
      rw [toIcoMod_add_zsmul]; rw [toIcoMod_apply_left], fun h => ⟨toIcoDiv hp a b, eq_add_of_sub_eq h⟩⟩

/--
theorem `modEq_iff_toIocMod_eq_right` / 定理 `modEq_iff_toIocMod_eq_right`

English:
theorem modEq_iff_toIocMod_eq_right
  statement: a ≡ b [PMOD p] ↔ toIocMod hp a b = a + p
  proof: by
  refine modEq_iff_eq_add_zsmul.trans ⟨?_, fun h => ⟨toIocDiv hp a b + 1, ?_⟩⟩
  · rintro ⟨z, rfl⟩
    rw [toIocMod_add_zsmul]; rw [toIocMod_apply_left]
  · rwa [add_one_zsmul, add_left_comm, ← sub_eq_iff_eq_add']

alias ⟨ModEq.toIcoMod_eq_left, _⟩ := modEq_iff_toIcoMod_eq_left

alias ⟨ModEq.toIc

中文:
定理 modEq_iff_toIocMod_eq_right
  结论: a ≡ b [PMOD p] ↔ toIocMod hp a b = a + p
  证明: by
  refine modEq_iff_eq_add_zsmul.trans ⟨?_, fun h => ⟨toIocDiv hp a b + 1, ?_⟩⟩
  · rintro ⟨z, rfl⟩
    rw [toIocMod_add_zsmul]; rw [toIocMod_apply_left]
  · rwa [add_one_zsmul, add_left_comm, ← sub_eq_iff_eq_add']

alias ⟨ModEq.toIcoMod_eq_left, _⟩ := modEq_iff_toIcoMod_eq_left

alias ⟨ModEq.toIc

Depends on / 依赖: add_left_comm, add_one_zsmul, modEq_iff_eq_add_zsmul, modEq_iff_eq_add_zsmul.trans, sub_eq_iff_eq_add, toIocDiv, toIocMod_add_zsmul, toIocMod_apply_left
-/
theorem modEq_iff_toIocMod_eq_right : a ≡ b [PMOD p] ↔ toIocMod hp a b = a + p := by
  refine modEq_iff_eq_add_zsmul.trans ⟨?_, fun h => ⟨toIocDiv hp a b + 1, ?_⟩⟩
  · rintro ⟨z, rfl⟩
    rw [toIocMod_add_zsmul]; rw [toIocMod_apply_left]
  · rwa [add_one_zsmul, add_left_comm, ← sub_eq_iff_eq_add']

alias ⟨ModEq.toIcoMod_eq_left, _⟩ := modEq_iff_toIcoMod_eq_left

alias ⟨ModEq.toIcoMod_eq_right, _⟩ := modEq_iff_toIocMod_eq_right

variable (a b)

open List in
/--
theorem `tfae_modEq` / 定理 `tfae_modEq`

English:
theorem tfae_modEq
  proof: by
  rw [modEq_iff_toIcoMod_eq_left hp]
  tfae_have 3 -> 2 := by
    rw [← not_exists]; rw [not_imp_not]
    exact fun ⟨i, hi⟩ =>
      ((toIcoMod_eq_iff hp).2 ⟨Set.Ioo_subset_Ico_self hi, i, (sub_add_cancel b _).symm⟩).trans
        ((toIocMod_eq_iff hp).2 ⟨Set.Ioo_subset_Ioc_self hi, i, (sub_add_c

中文:
定理 tfae_modEq
  证明: by
  rw [modEq_iff_toIcoMod_eq_left hp]
  tfae_have 3 -> 2 := by
    rw [← not_exists]; rw [not_imp_not]
    exact fun ⟨i, hi⟩ =>
      ((toIcoMod_eq_iff hp).2 ⟨Set.Ioo_subset_Ico_self hi, i, (sub_add_cancel b _).symm⟩).trans
        ((toIocMod_eq_iff hp).2 ⟨Set.Ioo_subset_Ioc_self hi, i, (sub_add_c

Depends on / 依赖: Ioo_subset_Ico_self, Ioo_subset_Ioc_self, Set.Ioo_subset_Ico_self, Set.Ioo_subset_Ioc_self, Set.right_mem_Ioc, add_eq_left, eq_comm, hp.ne, lt_add_of_p, modEq_iff_toIcoMod_eq_left, not_exists, not_imp_not, right_mem_Ioc, sub_add_cancel, tfae_have, toIcoMod_eq_iff, toIocMod_eq_iff
-/
theorem tfae_modEq :
    TFAE
      [a ≡ b [PMOD p], forall z : Int, b - z • p ∉ Set.Ioo a (a + p), toIcoMod hp a b != toIocMod hp a b,
        toIcoMod hp a b + p = toIocMod hp a b] := by
  rw [modEq_iff_toIcoMod_eq_left hp]
  tfae_have 3 -> 2 := by
    rw [← not_exists]; rw [not_imp_not]
    exact fun ⟨i, hi⟩ =>
      ((toIcoMod_eq_iff hp).2 ⟨Set.Ioo_subset_Ico_self hi, i, (sub_add_cancel b _).symm⟩).trans
        ((toIocMod_eq_iff hp).2 ⟨Set.Ioo_subset_Ioc_self hi, i, (sub_add_cancel b _).symm⟩).symm
  tfae_have 4 -> 3
  | h => by
    rw [← h]; rw [Ne]; rw [eq_comm]; rw [add_eq_left]
    exact hp.ne'
  tfae_have 1 -> 4
  | h => by
    rw [h]; rw [eq_comm]; rw [toIocMod_eq_iff]; rw [Set.right_mem_Ioc]
    refine ⟨lt_add_of_pos_right a hp, toIcoDiv hp a b - 1, ?_⟩
    rw [sub_one_zsmul]; rw [add_add_add_comm]; rw [add_neg_cancel]; rw [add_zero]
    conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hp a b, h]
  tfae_have 2 -> 1 := by
    rw [← not_exists]; rw [not_imp_comm]
    have h' := toIcoMod_mem_Ico hp a b
    exact fun h => ⟨_, h'.1.lt_of_ne' h, h'.2⟩
  tfae_finish

variable {a b}

/--
theorem `modEq_iff_forall_notMem_Ioo_mod` / 定理 `modEq_iff_forall_notMem_Ioo_mod`

English:
theorem modEq_iff_forall_notMem_Ioo_mod
  proof: (tfae_modEq hp a b).out 0 1

中文:
定理 modEq_iff_对任意_notMem_Ioo_mod
  证明: (tfae_modEq hp a b).out 0 1

Depends on / 依赖: tfae_modEq
-/
theorem modEq_iff_forall_notMem_Ioo_mod :
    a ≡ b [PMOD p] ↔ forall z : Int, b - z • p ∉ Set.Ioo a (a + p) :=
  (tfae_modEq hp a b).out 0 1

/--
theorem `modEq_iff_toIcoMod_ne_toIocMod` / 定理 `modEq_iff_toIcoMod_ne_toIocMod`

English:
theorem modEq_iff_toIcoMod_ne_toIocMod
  statement: a ≡ b [PMOD p] ↔ toIcoMod hp a b != toIocMod hp a b
  proof: (tfae_modEq hp a b).out 0 2

中文:
定理 modEq_iff_toIcoMod_ne_toIocMod
  结论: a ≡ b [PMOD p] ↔ toIcoMod hp a b != toIocMod hp a b
  证明: (tfae_modEq hp a b).out 0 2

Depends on / 依赖: tfae_modEq
-/
theorem modEq_iff_toIcoMod_ne_toIocMod : a ≡ b [PMOD p] ↔ toIcoMod hp a b != toIocMod hp a b :=
  (tfae_modEq hp a b).out 0 2

/--
theorem `modEq_iff_toIcoMod_add_period_eq_toIocMod` / 定理 `modEq_iff_toIcoMod_add_period_eq_toIocMod`

English:
theorem modEq_iff_toIcoMod_add_period_eq_toIocMod
  proof: (tfae_modEq hp a b).out 0 3

中文:
定理 modEq_iff_toIcoMod_add_period_eq_toIocMod
  证明: (tfae_modEq hp a b).out 0 3

Depends on / 依赖: tfae_modEq
-/
theorem modEq_iff_toIcoMod_add_period_eq_toIocMod :
    a ≡ b [PMOD p] ↔ toIcoMod hp a b + p = toIocMod hp a b :=
  (tfae_modEq hp a b).out 0 3

/--
theorem `not_modEq_iff_toIcoMod_eq_toIocMod` / 定理 `not_modEq_iff_toIcoMod_eq_toIocMod`

English:
theorem not_modEq_iff_toIcoMod_eq_toIocMod
  statement: ¬a ≡ b [PMOD p] ↔ toIcoMod hp a b = toIocMod hp a b
  proof: (modEq_iff_toIcoMod_ne_toIocMod _).not_left

中文:
定理 not_modEq_iff_toIcoMod_eq_toIocMod
  结论: ¬a ≡ b [PMOD p] ↔ toIcoMod hp a b = toIocMod hp a b
  证明: (modEq_iff_toIcoMod_ne_toIocMod _).not_left

Depends on / 依赖: modEq_iff_toIcoMod_ne_toIocMod, not_left
-/
theorem not_modEq_iff_toIcoMod_eq_toIocMod : ¬a ≡ b [PMOD p] ↔ toIcoMod hp a b = toIocMod hp a b :=
  (modEq_iff_toIcoMod_ne_toIocMod _).not_left

/--
theorem `not_modEq_iff_toIcoDiv_eq_toIocDiv` / 定理 `not_modEq_iff_toIcoDiv_eq_toIocDiv`

English:
theorem not_modEq_iff_toIcoDiv_eq_toIocDiv
  proof: by
  rw [not_modEq_iff_toIcoMod_eq_toIocMod hp]; rw [toIcoMod]; rw [toIocMod]; rw [sub_right_inj]; rw [zsmul_left_inj hp]

中文:
定理 not_modEq_iff_toIcoDiv_eq_toIocDiv
  证明: by
  rw [not_modEq_iff_toIcoMod_eq_toIocMod hp]; rw [toIcoMod]; rw [toIocMod]; rw [sub_right_inj]; rw [zsmul_left_inj hp]

Depends on / 依赖: not_modEq_iff_toIcoMod_eq_toIocMod, sub_right_inj, toIcoMod, toIocMod, zsmul_left_inj
-/
theorem not_modEq_iff_toIcoDiv_eq_toIocDiv :
    ¬a ≡ b [PMOD p] ↔ toIcoDiv hp a b = toIocDiv hp a b := by
  rw [not_modEq_iff_toIcoMod_eq_toIocMod hp]; rw [toIcoMod]; rw [toIocMod]; rw [sub_right_inj]; rw [zsmul_left_inj hp]

/--
theorem `modEq_iff_toIcoDiv_eq_toIocDiv_add_one` / 定理 `modEq_iff_toIcoDiv_eq_toIocDiv_add_one`

English:
theorem modEq_iff_toIcoDiv_eq_toIocDiv_add_one
  proof: by
  rw [modEq_iff_toIcoMod_add_period_eq_toIocMod hp]; rw [toIcoMod]; rw [toIocMod]; rw [← eq_sub_iff_add_eq]; rw [sub_sub]; rw [sub_right_inj]; rw [← add_one_zsmul]; rw [zsmul_left_inj hp]

中文:
定理 modEq_iff_toIcoDiv_eq_toIocDiv_add_one
  证明: by
  rw [modEq_iff_toIcoMod_add_period_eq_toIocMod hp]; rw [toIcoMod]; rw [toIocMod]; rw [← eq_sub_iff_add_eq]; rw [sub_sub]; rw [sub_right_inj]; rw [← add_one_zsmul]; rw [zsmul_left_inj hp]

Depends on / 依赖: add_one_zsmul, eq_sub_iff_add_eq, modEq_iff_toIcoMod_add_period_eq_toIocMod, sub_right_inj, sub_sub, toIcoMod, toIocMod, zsmul_left_inj
-/
theorem modEq_iff_toIcoDiv_eq_toIocDiv_add_one :
    a ≡ b [PMOD p] ↔ toIcoDiv hp a b = toIocDiv hp a b + 1 := by
  rw [modEq_iff_toIcoMod_add_period_eq_toIocMod hp]; rw [toIcoMod]; rw [toIocMod]; rw [← eq_sub_iff_add_eq]; rw [sub_sub]; rw [sub_right_inj]; rw [← add_one_zsmul]; rw [zsmul_left_inj hp]

end AddCommGroup

open AddCommGroup

/-- If `a` and `b` fall within the same cycle w.r.t. `c`, then they are congruent modulo `p`. -/
@[simp]
/--
theorem `toIcoMod_inj` / 定理 `toIcoMod_inj`

English:
theorem toIcoMod_inj
  given: {c : α}
  statement: toIcoMod hp c a = toIcoMod hp c b ↔ a ≡ b [PMOD p]
  proof: by
  rw [toIcoMod_eq_toIcoMod]; rw [AddCommGroup.modEq_iff_zsmul']

alias ⟨_, AddCommGroup.ModEq.toIcoMod_eq_toIcoMod⟩ := toIcoMod_inj

中文:
定理 toIcoMod_inj
  条件: {c : α}
  结论: toIcoMod hp c a = toIcoMod hp c b ↔ a ≡ b [PMOD p]
  证明: by
  rw [toIcoMod_eq_toIcoMod]; rw [AddCommGroup.modEq_iff_zsmul']

alias ⟨_, AddCommGroup.ModEq.toIcoMod_eq_toIcoMod⟩ := toIcoMod_inj

Depends on / 依赖: AddCommGroup, AddCommGroup.modEq_iff_zsmul, modEq_iff_zsmul, toIcoMod_eq_toIcoMod
-/
theorem toIcoMod_inj {c : α} : toIcoMod hp c a = toIcoMod hp c b ↔ a ≡ b [PMOD p] := by
  rw [toIcoMod_eq_toIcoMod]; rw [AddCommGroup.modEq_iff_zsmul']

alias ⟨_, AddCommGroup.ModEq.toIcoMod_eq_toIcoMod⟩ := toIcoMod_inj

/--
theorem `Ico_eq_locus_Ioc_eq_iUnion_Ioo` / 定理 `Ico_eq_locus_Ioc_eq_iUnion_Ioo`

English:
theorem Ico_eq_locus_Ioc_eq_iUnion_Ioo
  proof: by
  ext1
  simp_rw [Set.mem_ofPred, Set.mem_iUnion, ← Set.sub_mem_Ioo_iff_left, ←
    not_modEq_iff_toIcoMod_eq_toIocMod, modEq_iff_forall_notMem_Ioo_mod hp, not_forall,
    Classical.not_not]

中文:
定理 Ico_eq_locus_Ioc_eq_iUnion_Ioo
  证明: by
  ext1
  simp_rw [Set.mem_ofPred, Set.mem_iUnion, ← Set.sub_mem_Ioo_iff_left, ←
    not_modEq_iff_toIcoMod_eq_toIocMod, modEq_iff_forall_notMem_Ioo_mod hp, not_forall,
    Classical.not_not]

Depends on / 依赖: Classical, Classical.not_not, Set.mem_iUnion, Set.mem_ofPred, Set.sub_mem_Ioo_iff_left, mem_iUnion, mem_ofPred, modEq_iff_forall_notMem_Ioo_mod, not_forall, not_modEq_iff_toIcoMod_eq_toIocMod, not_not, simp_rw, sub_mem_Ioo_iff_left
-/
theorem Ico_eq_locus_Ioc_eq_iUnion_Ioo :
    { b | toIcoMod hp a b = toIocMod hp a b } = ⋃ z : Int, Set.Ioo (a + z • p) (a + p + z • p) := by
  ext1
  simp_rw [Set.mem_ofPred, Set.mem_iUnion, ← Set.sub_mem_Ioo_iff_left, ←
    not_modEq_iff_toIcoMod_eq_toIocMod, modEq_iff_forall_notMem_Ioo_mod hp, not_forall,
    Classical.not_not]

/--
theorem `toIocDiv_wcovBy_toIcoDiv` / 定理 `toIocDiv_wcovBy_toIcoDiv`

English:
theorem toIocDiv_wcovBy_toIcoDiv
  given: (a b : α)
  statement: toIocDiv hp a b ⩿ toIcoDiv hp a b
  proof: by
  suffices toIocDiv hp a b = toIcoDiv hp a b ∨ toIocDiv hp a b + 1 = toIcoDiv hp a b by
    rwa [wcovBy_iff_eq_or_covBy, ← Order.succ_eq_iff_covBy]
  rw [eq_comm]; rw [← not_modEq_iff_toIcoDiv_eq_toIocDiv]; rw [eq_comm]; rw [←
    modEq_iff_toIcoDiv_eq_toIocDiv_add_one]
  exact em' _

中文:
定理 toIocDiv_wcovBy_toIcoDiv
  条件: (a b : α)
  结论: toIocDiv hp a b ⩿ toIcoDiv hp a b
  证明: by
  suffices toIocDiv hp a b = toIcoDiv hp a b ∨ toIocDiv hp a b + 1 = toIcoDiv hp a b by
    rwa [wcovBy_iff_eq_or_covBy, ← Order.succ_eq_iff_covBy]
  rw [eq_comm]; rw [← not_modEq_iff_toIcoDiv_eq_toIocDiv]; rw [eq_comm]; rw [←
    modEq_iff_toIcoDiv_eq_toIocDiv_add_one]
  exact em' _

Depends on / 依赖: Order.succ_eq_iff_covBy, eq_comm, modEq_iff_toIcoDiv_eq_toIocDiv_add_one, not_modEq_iff_toIcoDiv_eq_toIocDiv, succ_eq_iff_covBy, toIcoDiv, toIocDiv, wcovBy_iff_eq_or_covBy
-/
theorem toIocDiv_wcovBy_toIcoDiv (a b : α) : toIocDiv hp a b ⩿ toIcoDiv hp a b := by
  suffices toIocDiv hp a b = toIcoDiv hp a b ∨ toIocDiv hp a b + 1 = toIcoDiv hp a b by
    rwa [wcovBy_iff_eq_or_covBy, ← Order.succ_eq_iff_covBy]
  rw [eq_comm]; rw [← not_modEq_iff_toIcoDiv_eq_toIocDiv]; rw [eq_comm]; rw [←
    modEq_iff_toIcoDiv_eq_toIocDiv_add_one]
  exact em' _

/--
theorem `toIcoMod_le_toIocMod` / 定理 `toIcoMod_le_toIocMod`

English:
theorem toIcoMod_le_toIocMod
  given: (a b : α)
  statement: toIcoMod hp a b <= toIocMod hp a b
  proof: by
  rw [toIcoMod]; rw [toIocMod]; rw [sub_le_sub_iff_left]
  exact zsmul_left_mono hp.le (toIocDiv_wcovBy_toIcoDiv _ _ _).le

中文:
定理 toIcoMod_le_toIocMod
  条件: (a b : α)
  结论: toIcoMod hp a b <= toIocMod hp a b
  证明: by
  rw [toIcoMod]; rw [toIocMod]; rw [sub_le_sub_iff_left]
  exact zsmul_left_mono hp.le (toIocDiv_wcovBy_toIcoDiv _ _ _).le

Depends on / 依赖: hp.le, sub_le_sub_iff_left, toIcoMod, toIocDiv_wcovBy_toIcoDiv, toIocMod, zsmul_left_mono
-/
theorem toIcoMod_le_toIocMod (a b : α) : toIcoMod hp a b <= toIocMod hp a b := by
  rw [toIcoMod]; rw [toIocMod]; rw [sub_le_sub_iff_left]
  exact zsmul_left_mono hp.le (toIocDiv_wcovBy_toIcoDiv _ _ _).le

/--
theorem `toIocMod_le_toIcoMod_add` / 定理 `toIocMod_le_toIcoMod_add`

English:
theorem toIocMod_le_toIcoMod_add
  given: (a b : α)
  statement: toIocMod hp a b <= toIcoMod hp a b + p
  proof: by
  rw [toIcoMod]; rw [toIocMod]; rw [sub_add]; rw [sub_le_sub_iff_left]; rw [sub_le_iff_le_add]; rw [← add_one_zsmul]; rw [(zsmul_left_strictMono hp).le_iff_le]
  apply (toIocDiv_wcovBy_toIcoDiv _ _ _).le_succ

中文:
定理 toIocMod_le_toIcoMod_add
  条件: (a b : α)
  结论: toIocMod hp a b <= toIcoMod hp a b + p
  证明: by
  rw [toIcoMod]; rw [toIocMod]; rw [sub_add]; rw [sub_le_sub_iff_left]; rw [sub_le_iff_le_add]; rw [← add_one_zsmul]; rw [(zsmul_left_strictMono hp).le_iff_le]
  apply (toIocDiv_wcovBy_toIcoDiv _ _ _).le_succ

Depends on / 依赖: add_one_zsmul, le_iff_le, le_succ, sub_add, sub_le_iff_le_add, sub_le_sub_iff_left, toIcoMod, toIocDiv_wcovBy_toIcoDiv, toIocMod, zsmul_left_strictMono
-/
theorem toIocMod_le_toIcoMod_add (a b : α) : toIocMod hp a b <= toIcoMod hp a b + p := by
  rw [toIcoMod]; rw [toIocMod]; rw [sub_add]; rw [sub_le_sub_iff_left]; rw [sub_le_iff_le_add]; rw [← add_one_zsmul]; rw [(zsmul_left_strictMono hp).le_iff_le]
  apply (toIocDiv_wcovBy_toIcoDiv _ _ _).le_succ

end IcoIoc

open AddCommGroup

/--
theorem `toIcoMod_eq_self` / 定理 `toIcoMod_eq_self`

English:
theorem toIcoMod_eq_self
  statement: toIcoMod hp a b = b ↔ b in Set.Ico a (a + p)
  proof: by
  rw [toIcoMod_eq_iff]; rw [and_iff_left]
  exact ⟨0, by simp⟩

中文:
定理 toIcoMod_eq_self
  结论: toIcoMod hp a b = b ↔ b in 集合.左闭右开区间 a (a + p)
  证明: by
  rw [toIcoMod_eq_iff]; rw [and_iff_left]
  exact ⟨0, by simp⟩

Depends on / 依赖: and_iff_left, toIcoMod_eq_iff
-/
theorem toIcoMod_eq_self : toIcoMod hp a b = b ↔ b in Set.Ico a (a + p) := by
  rw [toIcoMod_eq_iff]; rw [and_iff_left]
  exact ⟨0, by simp⟩

/--
theorem `toIocMod_eq_self` / 定理 `toIocMod_eq_self`

English:
theorem toIocMod_eq_self
  statement: toIocMod hp a b = b ↔ b in Set.Ioc a (a + p)
  proof: by
  rw [toIocMod_eq_iff]; rw [and_iff_left]
  exact ⟨0, by simp⟩

@[simp]

中文:
定理 toIocMod_eq_self
  结论: toIocMod hp a b = b ↔ b in 集合.左开右闭区间 a (a + p)
  证明: by
  rw [toIocMod_eq_iff]; rw [and_iff_left]
  exact ⟨0, by simp⟩

@[simp]

Depends on / 依赖: and_iff_left, toIocMod_eq_iff
-/
theorem toIocMod_eq_self : toIocMod hp a b = b ↔ b in Set.Ioc a (a + p) := by
  rw [toIocMod_eq_iff]; rw [and_iff_left]
  exact ⟨0, by simp⟩

@[simp]
/--
theorem `toIcoMod_toIcoMod` / 定理 `toIcoMod_toIcoMod`

English:
theorem toIcoMod_toIcoMod
  given: (a₁ a₂ b : α)
  statement: toIcoMod hp a₁ (toIcoMod hp a₂ b) = toIcoMod hp a₁ b
  proof: (toIcoMod_eq_toIcoMod _).2 ⟨toIcoDiv hp a₂ b, self_sub_toIcoMod hp a₂ b⟩

@[simp]

中文:
定理 toIcoMod_toIcoMod
  条件: (a₁ a₂ b : α)
  结论: toIcoMod hp a₁ (toIcoMod hp a₂ b) = toIcoMod hp a₁ b
  证明: (toIcoMod_eq_toIcoMod _).2 ⟨toIcoDiv hp a₂ b, self_sub_toIcoMod hp a₂ b⟩

@[simp]

Depends on / 依赖: self_sub_toIcoMod, toIcoDiv, toIcoMod_eq_toIcoMod
-/
theorem toIcoMod_toIcoMod (a₁ a₂ b : α) : toIcoMod hp a₁ (toIcoMod hp a₂ b) = toIcoMod hp a₁ b :=
  (toIcoMod_eq_toIcoMod _).2 ⟨toIcoDiv hp a₂ b, self_sub_toIcoMod hp a₂ b⟩

@[simp]
/--
theorem `toIcoMod_toIocMod` / 定理 `toIcoMod_toIocMod`

English:
theorem toIcoMod_toIocMod
  given: (a₁ a₂ b : α)
  statement: toIcoMod hp a₁ (toIocMod hp a₂ b) = toIcoMod hp a₁ b
  proof: (toIcoMod_eq_toIcoMod _).2 ⟨toIocDiv hp a₂ b, self_sub_toIocMod hp a₂ b⟩

@[simp]

中文:
定理 toIcoMod_toIocMod
  条件: (a₁ a₂ b : α)
  结论: toIcoMod hp a₁ (toIocMod hp a₂ b) = toIcoMod hp a₁ b
  证明: (toIcoMod_eq_toIcoMod _).2 ⟨toIocDiv hp a₂ b, self_sub_toIocMod hp a₂ b⟩

@[simp]

Depends on / 依赖: self_sub_toIocMod, toIcoMod_eq_toIcoMod, toIocDiv
-/
theorem toIcoMod_toIocMod (a₁ a₂ b : α) : toIcoMod hp a₁ (toIocMod hp a₂ b) = toIcoMod hp a₁ b :=
  (toIcoMod_eq_toIcoMod _).2 ⟨toIocDiv hp a₂ b, self_sub_toIocMod hp a₂ b⟩

@[simp]
/--
theorem `toIocMod_toIocMod` / 定理 `toIocMod_toIocMod`

English:
theorem toIocMod_toIocMod
  given: (a₁ a₂ b : α)
  statement: toIocMod hp a₁ (toIocMod hp a₂ b) = toIocMod hp a₁ b
  proof: (toIocMod_eq_toIocMod _).2 ⟨toIocDiv hp a₂ b, self_sub_toIocMod hp a₂ b⟩

@[simp]

中文:
定理 toIocMod_toIocMod
  条件: (a₁ a₂ b : α)
  结论: toIocMod hp a₁ (toIocMod hp a₂ b) = toIocMod hp a₁ b
  证明: (toIocMod_eq_toIocMod _).2 ⟨toIocDiv hp a₂ b, self_sub_toIocMod hp a₂ b⟩

@[simp]

Depends on / 依赖: self_sub_toIocMod, toIocDiv, toIocMod_eq_toIocMod
-/
theorem toIocMod_toIocMod (a₁ a₂ b : α) : toIocMod hp a₁ (toIocMod hp a₂ b) = toIocMod hp a₁ b :=
  (toIocMod_eq_toIocMod _).2 ⟨toIocDiv hp a₂ b, self_sub_toIocMod hp a₂ b⟩

@[simp]
/--
theorem `toIocMod_toIcoMod` / 定理 `toIocMod_toIcoMod`

English:
theorem toIocMod_toIcoMod
  given: (a₁ a₂ b : α)
  statement: toIocMod hp a₁ (toIcoMod hp a₂ b) = toIocMod hp a₁ b
  proof: (toIocMod_eq_toIocMod _).2 ⟨toIcoDiv hp a₂ b, self_sub_toIcoMod hp a₂ b⟩

中文:
定理 toIocMod_toIcoMod
  条件: (a₁ a₂ b : α)
  结论: toIocMod hp a₁ (toIcoMod hp a₂ b) = toIocMod hp a₁ b
  证明: (toIocMod_eq_toIocMod _).2 ⟨toIcoDiv hp a₂ b, self_sub_toIcoMod hp a₂ b⟩

Depends on / 依赖: self_sub_toIcoMod, toIcoDiv, toIocMod_eq_toIocMod
-/
theorem toIocMod_toIcoMod (a₁ a₂ b : α) : toIocMod hp a₁ (toIcoMod hp a₂ b) = toIocMod hp a₁ b :=
  (toIocMod_eq_toIocMod _).2 ⟨toIcoDiv hp a₂ b, self_sub_toIcoMod hp a₂ b⟩

/--
theorem `toIcoMod_periodic` / 定理 `toIcoMod_periodic`

English:
theorem toIcoMod_periodic
  given: (a : α)
  statement: Function.Periodic (toIcoMod hp a) p
  proof: toIcoMod_add_right hp a

中文:
定理 toIcoMod_periodic
  条件: (a : α)
  结论: 函数.周期 (toIcoMod hp a) p
  证明: toIcoMod_add_right hp a

Depends on / 依赖: toIcoMod_add_right
-/
theorem toIcoMod_periodic (a : α) : Function.Periodic (toIcoMod hp a) p :=
  toIcoMod_add_right hp a

/--
theorem `toIocMod_periodic` / 定理 `toIocMod_periodic`

English:
theorem toIocMod_periodic
  given: (a : α)
  statement: Function.Periodic (toIocMod hp a) p
  proof: toIocMod_add_right hp a

中文:
定理 toIocMod_periodic
  条件: (a : α)
  结论: 函数.周期 (toIocMod hp a) p
  证明: toIocMod_add_right hp a

Depends on / 依赖: toIocMod_add_right
-/
theorem toIocMod_periodic (a : α) : Function.Periodic (toIocMod hp a) p :=
  toIocMod_add_right hp a

-- helper lemmas for when `a = 0`
section Zero

/--
theorem `toIcoMod_zero_sub_comm` / 定理 `toIcoMod_zero_sub_comm`

English:
theorem toIcoMod_zero_sub_comm
  given: (a b : α)
  statement: toIcoMod hp 0 (a - b) = p - toIocMod hp 0 (b - a)
  proof: by
  rw [← neg_sub]; rw [toIcoMod_neg]; rw [neg_zero]

中文:
定理 toIcoMod_zero_sub_comm
  条件: (a b : α)
  结论: toIcoMod hp 0 (a - b) = p - toIocMod hp 0 (b - a)
  证明: by
  rw [← neg_sub]; rw [toIcoMod_neg]; rw [neg_zero]

Depends on / 依赖: neg_sub, neg_zero, toIcoMod_neg
-/
theorem toIcoMod_zero_sub_comm (a b : α) : toIcoMod hp 0 (a - b) = p - toIocMod hp 0 (b - a) := by
  rw [← neg_sub]; rw [toIcoMod_neg]; rw [neg_zero]

/--
theorem `toIocMod_zero_sub_comm` / 定理 `toIocMod_zero_sub_comm`

English:
theorem toIocMod_zero_sub_comm
  given: (a b : α)
  statement: toIocMod hp 0 (a - b) = p - toIcoMod hp 0 (b - a)
  proof: by
  rw [← neg_sub]; rw [toIocMod_neg]; rw [neg_zero]

中文:
定理 toIocMod_zero_sub_comm
  条件: (a b : α)
  结论: toIocMod hp 0 (a - b) = p - toIcoMod hp 0 (b - a)
  证明: by
  rw [← neg_sub]; rw [toIocMod_neg]; rw [neg_zero]

Depends on / 依赖: neg_sub, neg_zero, toIocMod_neg
-/
theorem toIocMod_zero_sub_comm (a b : α) : toIocMod hp 0 (a - b) = p - toIcoMod hp 0 (b - a) := by
  rw [← neg_sub]; rw [toIocMod_neg]; rw [neg_zero]

/--
theorem `toIcoDiv_eq_sub` / 定理 `toIcoDiv_eq_sub`

English:
theorem toIcoDiv_eq_sub
  given: (a b : α)
  statement: toIcoDiv hp a b = toIcoDiv hp 0 (b - a)
  proof: by
  rw [toIcoDiv_sub_eq_toIcoDiv_add]; rw [zero_add]

中文:
定理 toIcoDiv_eq_sub
  条件: (a b : α)
  结论: toIcoDiv hp a b = toIcoDiv hp 0 (b - a)
  证明: by
  rw [toIcoDiv_sub_eq_toIcoDiv_add]; rw [zero_add]

Depends on / 依赖: toIcoDiv_sub_eq_toIcoDiv_add, zero_add
-/
theorem toIcoDiv_eq_sub (a b : α) : toIcoDiv hp a b = toIcoDiv hp 0 (b - a) := by
  rw [toIcoDiv_sub_eq_toIcoDiv_add]; rw [zero_add]

/--
theorem `toIocDiv_eq_sub` / 定理 `toIocDiv_eq_sub`

English:
theorem toIocDiv_eq_sub
  given: (a b : α)
  statement: toIocDiv hp a b = toIocDiv hp 0 (b - a)
  proof: by
  rw [toIocDiv_sub_eq_toIocDiv_add]; rw [zero_add]

中文:
定理 toIocDiv_eq_sub
  条件: (a b : α)
  结论: toIocDiv hp a b = toIocDiv hp 0 (b - a)
  证明: by
  rw [toIocDiv_sub_eq_toIocDiv_add]; rw [zero_add]

Depends on / 依赖: toIocDiv_sub_eq_toIocDiv_add, zero_add
-/
theorem toIocDiv_eq_sub (a b : α) : toIocDiv hp a b = toIocDiv hp 0 (b - a) := by
  rw [toIocDiv_sub_eq_toIocDiv_add]; rw [zero_add]

/--
theorem `toIcoMod_eq_sub` / 定理 `toIcoMod_eq_sub`

English:
theorem toIcoMod_eq_sub
  given: (a b : α)
  statement: toIcoMod hp a b = toIcoMod hp 0 (b - a) + a
  proof: by
  rw [toIcoMod_sub_eq_sub]; rw [zero_add]; rw [sub_add_cancel]

中文:
定理 toIcoMod_eq_sub
  条件: (a b : α)
  结论: toIcoMod hp a b = toIcoMod hp 0 (b - a) + a
  证明: by
  rw [toIcoMod_sub_eq_sub]; rw [zero_add]; rw [sub_add_cancel]

Depends on / 依赖: sub_add_cancel, toIcoMod_sub_eq_sub, zero_add
-/
theorem toIcoMod_eq_sub (a b : α) : toIcoMod hp a b = toIcoMod hp 0 (b - a) + a := by
  rw [toIcoMod_sub_eq_sub]; rw [zero_add]; rw [sub_add_cancel]

/--
theorem `toIocMod_eq_sub` / 定理 `toIocMod_eq_sub`

English:
theorem toIocMod_eq_sub
  given: (a b : α)
  statement: toIocMod hp a b = toIocMod hp 0 (b - a) + a
  proof: by
  rw [toIocMod_sub_eq_sub]; rw [zero_add]; rw [sub_add_cancel]

中文:
定理 toIocMod_eq_sub
  条件: (a b : α)
  结论: toIocMod hp a b = toIocMod hp 0 (b - a) + a
  证明: by
  rw [toIocMod_sub_eq_sub]; rw [zero_add]; rw [sub_add_cancel]

Depends on / 依赖: sub_add_cancel, toIocMod_sub_eq_sub, zero_add
-/
theorem toIocMod_eq_sub (a b : α) : toIocMod hp a b = toIocMod hp 0 (b - a) + a := by
  rw [toIocMod_sub_eq_sub]; rw [zero_add]; rw [sub_add_cancel]

/--
theorem `toIcoMod_add_toIocMod_zero` / 定理 `toIcoMod_add_toIocMod_zero`

English:
theorem toIcoMod_add_toIocMod_zero
  given: (a b : α)
  proof: by
  rw [toIcoMod_zero_sub_comm]; rw [sub_add_cancel]

中文:
定理 toIcoMod_add_toIocMod_zero
  条件: (a b : α)
  证明: by
  rw [toIcoMod_zero_sub_comm]; rw [sub_add_cancel]

Depends on / 依赖: sub_add_cancel, toIcoMod_zero_sub_comm
-/
theorem toIcoMod_add_toIocMod_zero (a b : α) :
    toIcoMod hp 0 (a - b) + toIocMod hp 0 (b - a) = p := by
  rw [toIcoMod_zero_sub_comm]; rw [sub_add_cancel]

/--
theorem `toIocMod_add_toIcoMod_zero` / 定理 `toIocMod_add_toIcoMod_zero`

English:
theorem toIocMod_add_toIcoMod_zero
  given: (a b : α)
  proof: by
  rw [_root_.add_comm]; rw [toIcoMod_add_toIocMod_zero]

中文:
定理 toIocMod_add_toIcoMod_zero
  条件: (a b : α)
  证明: by
  rw [_root_.add_comm]; rw [toIcoMod_add_toIocMod_zero]

Depends on / 依赖: _root_, _root_.add_comm, add_comm, toIcoMod_add_toIocMod_zero
-/
theorem toIocMod_add_toIcoMod_zero (a b : α) :
    toIocMod hp 0 (a - b) + toIcoMod hp 0 (b - a) = p := by
  rw [_root_.add_comm]; rw [toIcoMod_add_toIocMod_zero]

end Zero

/-- `toIcoMod` as an equiv from the quotient. -/
@[simps symm_apply]
/--
Definition of `QuotientAddGroup.equivIcoMod` / `QuotientAddGroup.equivIcoMod` 的定义

English:
definition QuotientAddGroup.equivIcoMod
  signature: (a : α)
  body: ⟨(toIcoMod_periodic hp a).lift b, QuotientAddGroup.induction_on b toIcoMod_mem_Ico hp a⟩
  invFun := (↑)
right_inv b := Subtype.ext (toIcoMod_eq_self hp).mpr b.prop
  left_inv b := by
    induction b using QuotientAddGroup.induction_on
    dsimp
    rw [QuotientAddGroup.eq_iff_sub_mem]; rw [toIcoMod

中文:
定义 QuotientAddGroup.equivIcoMod
  签名: (a : α)
  定义体: ⟨(toIcoMod_periodic hp a).lift b, QuotientAddGroup.induction_on b toIcoMod_mem_Ico hp a⟩
  invFun := (↑)
right_inv b := Subtype.ext (toIcoMod_eq_self hp).mpr b.prop
  left_inv b := by
    induction b using QuotientAddGroup.induction_on
    dsimp
    rw [QuotientAddGroup.eq_iff_sub_mem]; rw [toIcoMod

Depends on / 依赖: AddSubgroup, AddSubgroup.zsmul_mem_zmultiples, QuotientAddGroup, QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.induction_on, Subtype, Subtype.ext, b.prop, eq_iff_sub_mem, induction_on, invFun, left_inv, right_inv, toIcoMod_eq_self, toIcoMod_mem_Ico, toIcoMod_periodic, toIcoMod_sub_self, zsmul_mem_zmultiples
-/
def QuotientAddGroup.equivIcoMod (a : α) : α ⧸ AddSubgroup.zmultiples p ≃ Set.Ico a (a + p) where
  toFun b :=
⟨(toIcoMod_periodic hp a).lift b, QuotientAddGroup.induction_on b toIcoMod_mem_Ico hp a⟩
  invFun := (↑)
right_inv b := Subtype.ext (toIcoMod_eq_self hp).mpr b.prop
  left_inv b := by
    induction b using QuotientAddGroup.induction_on
    dsimp
    rw [QuotientAddGroup.eq_iff_sub_mem]; rw [toIcoMod_sub_self]
    apply AddSubgroup.zsmul_mem_zmultiples

@[simp]
/--
theorem `QuotientAddGroup.equivIcoMod_coe` / 定理 `QuotientAddGroup.equivIcoMod_coe`

English:
theorem QuotientAddGroup.equivIcoMod_coe
  given: (a b : α)
  proof: rfl

@[simp]

中文:
定理 QuotientAddGroup.equivIcoMod_coe
  条件: (a b : α)
  证明: rfl

@[simp]
-/
theorem QuotientAddGroup.equivIcoMod_coe (a b : α) :
    QuotientAddGroup.equivIcoMod hp a ↑b = ⟨toIcoMod hp a b, toIcoMod_mem_Ico hp a _⟩ :=
  rfl

@[simp]
/--
theorem `QuotientAddGroup.equivIcoMod_zero` / 定理 `QuotientAddGroup.equivIcoMod_zero`

English:
theorem QuotientAddGroup.equivIcoMod_zero
  given: (a : α)
  proof: rfl

中文:
定理 QuotientAddGroup.equivIcoMod_zero
  条件: (a : α)
  证明: rfl
-/
theorem QuotientAddGroup.equivIcoMod_zero (a : α) :
    QuotientAddGroup.equivIcoMod hp a 0 = ⟨toIcoMod hp a 0, toIcoMod_mem_Ico hp a _⟩ :=
  rfl

/-- `toIocMod` as an equiv from the quotient. -/
@[simps symm_apply]
/--
Definition of `QuotientAddGroup.equivIocMod` / `QuotientAddGroup.equivIocMod` 的定义

English:
definition QuotientAddGroup.equivIocMod
  signature: (a : α)
  body: ⟨(toIocMod_periodic hp a).lift b, QuotientAddGroup.induction_on b toIocMod_mem_Ioc hp a⟩
  invFun := (↑)
right_inv b := Subtype.ext (toIocMod_eq_self hp).mpr b.prop
  left_inv b := by
    induction b using QuotientAddGroup.induction_on
    dsimp
    rw [QuotientAddGroup.eq_iff_sub_mem]; rw [toIocMod

中文:
定义 QuotientAddGroup.equivIocMod
  签名: (a : α)
  定义体: ⟨(toIocMod_periodic hp a).lift b, QuotientAddGroup.induction_on b toIocMod_mem_Ioc hp a⟩
  invFun := (↑)
right_inv b := Subtype.ext (toIocMod_eq_self hp).mpr b.prop
  left_inv b := by
    induction b using QuotientAddGroup.induction_on
    dsimp
    rw [QuotientAddGroup.eq_iff_sub_mem]; rw [toIocMod

Depends on / 依赖: AddSubgroup, AddSubgroup.zsmul_mem_zmultiples, QuotientAddGroup, QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.induction_on, Subtype, Subtype.ext, b.prop, eq_iff_sub_mem, induction_on, invFun, left_inv, right_inv, toIocMod_eq_self, toIocMod_mem_Ioc, toIocMod_periodic, toIocMod_sub_self, zsmul_mem_zmultiples
-/
def QuotientAddGroup.equivIocMod (a : α) : α ⧸ AddSubgroup.zmultiples p ≃ Set.Ioc a (a + p) where
  toFun b :=
⟨(toIocMod_periodic hp a).lift b, QuotientAddGroup.induction_on b toIocMod_mem_Ioc hp a⟩
  invFun := (↑)
right_inv b := Subtype.ext (toIocMod_eq_self hp).mpr b.prop
  left_inv b := by
    induction b using QuotientAddGroup.induction_on
    dsimp
    rw [QuotientAddGroup.eq_iff_sub_mem]; rw [toIocMod_sub_self]
    apply AddSubgroup.zsmul_mem_zmultiples

@[simp]
/--
theorem `QuotientAddGroup.equivIocMod_coe` / 定理 `QuotientAddGroup.equivIocMod_coe`

English:
theorem QuotientAddGroup.equivIocMod_coe
  given: (a b : α)
  proof: rfl

@[simp]

中文:
定理 QuotientAddGroup.equivIocMod_coe
  条件: (a b : α)
  证明: rfl

@[simp]
-/
theorem QuotientAddGroup.equivIocMod_coe (a b : α) :
    QuotientAddGroup.equivIocMod hp a ↑b = ⟨toIocMod hp a b, toIocMod_mem_Ioc hp a _⟩ :=
  rfl

@[simp]
/--
theorem `QuotientAddGroup.equivIocMod_zero` / 定理 `QuotientAddGroup.equivIocMod_zero`

English:
theorem QuotientAddGroup.equivIocMod_zero
  given: (a : α)
  proof: rfl

中文:
定理 QuotientAddGroup.equivIocMod_zero
  条件: (a : α)
  证明: rfl
-/
theorem QuotientAddGroup.equivIocMod_zero (a : α) :
    QuotientAddGroup.equivIocMod hp a 0 = ⟨toIocMod hp a 0, toIocMod_mem_Ioc hp a _⟩ :=
  rfl
end

/-!
### The circular order structure on `α ⧸ AddSubgroup.zmultiples p`
-/


section Circular

open AddCommGroup

/--
theorem `toIxxMod_iff` / 定理 `toIxxMod_iff`

English:
theorem toIxxMod_iff
  given: (x₁ x₂ x₃ : α)
  statement: toIcoMod hp x₁ x₂ <= toIocMod hp x₁ x₃ ↔
  proof: by
  rw [toIcoMod_eq_sub]; rw [toIocMod_eq_sub _ x₁]; rw [add_le_add_iff_right]; rw [← neg_sub x₁ x₃]; rw [toIocMod_neg]; rw [neg_zero]; rw [le_sub_iff_add_le]

中文:
定理 toIxxMod_iff
  条件: (x₁ x₂ x₃ : α)
  结论: toIcoMod hp x₁ x₂ <= toIocMod hp x₁ x₃ ↔
  证明: by
  rw [toIcoMod_eq_sub]; rw [toIocMod_eq_sub _ x₁]; rw [add_le_add_iff_right]; rw [← neg_sub x₁ x₃]; rw [toIocMod_neg]; rw [neg_zero]; rw [le_sub_iff_add_le]
-/
private theorem toIxxMod_iff (x₁ x₂ x₃ : α) : toIcoMod hp x₁ x₂ <= toIocMod hp x₁ x₃ ↔
    toIcoMod hp 0 (x₂ - x₁) + toIcoMod hp 0 (x₁ - x₃) <= p := by
  rw [toIcoMod_eq_sub]; rw [toIocMod_eq_sub _ x₁]; rw [add_le_add_iff_right]; rw [← neg_sub x₁ x₃]; rw [toIocMod_neg]; rw [neg_zero]; rw [le_sub_iff_add_le]

/--
theorem `toIxxMod_cyclic_left` / 定理 `toIxxMod_cyclic_left`

English:
theorem toIxxMod_cyclic_left
  given: {x₁ x₂ x₃ : α} (h : toIcoMod hp x₁ x₂ <= toIocMod hp x₁ x₃)
  proof: by
  let x₂' := toIcoMod hp x₁ x₂
  let x₃' := toIcoMod hp x₂' x₃
  have h : x₂' <= toIocMod hp x₁ x₃' := by simpa [x₃']
  have h₂₁ : x₂' < x₁ + p := toIcoMod_lt_right _ _ _
  have h₃₂ : x₃' - p < x₂' := sub_lt_iff_lt_add.2 (toIcoMod_lt_right _ _ _)
  suffices hequiv : x₃' <= toIocMod hp x₂' x₁ by
 

中文:
定理 toIxxMod_cyclic_left
  条件: {x₁ x₂ x₃ : α} (h : toIcoMod hp x₁ x₂ <= toIocMod hp x₁ x₃)
  证明: by
  let x₂' := toIcoMod hp x₁ x₂
  let x₃' := toIcoMod hp x₂' x₃
  have h : x₂' <= toIocMod hp x₁ x₃' := by simpa [x₃']
  have h₂₁ : x₂' < x₁ + p := toIcoMod_lt_right _ _ _
  have h₃₂ : x₃' - p < x₂' := sub_lt_iff_lt_add.2 (toIcoMod_lt_right _ _ _)
  suffices hequiv : x₃' <= toIocMod hp x₂' x₁ by
 
-/
private theorem toIxxMod_cyclic_left {x₁ x₂ x₃ : α} (h : toIcoMod hp x₁ x₂ <= toIocMod hp x₁ x₃) :
    toIcoMod hp x₂ x₃ <= toIocMod hp x₂ x₁ := by
  let x₂' := toIcoMod hp x₁ x₂
  let x₃' := toIcoMod hp x₂' x₃
  have h : x₂' <= toIocMod hp x₁ x₃' := by simpa [x₃']
  have h₂₁ : x₂' < x₁ + p := toIcoMod_lt_right _ _ _
  have h₃₂ : x₃' - p < x₂' := sub_lt_iff_lt_add.2 (toIcoMod_lt_right _ _ _)
  suffices hequiv : x₃' <= toIocMod hp x₂' x₁ by
    obtain ⟨z, hd⟩ : exists z : Int, x₂ = x₂' + z • p := ((toIcoMod_eq_iff hp).1 rfl).2
    simpa [hd, toIocMod_add_zsmul', toIcoMod_add_zsmul', add_le_add_iff_right]
  rcases le_or_gt x₃' (x₁ + p) with h₃₁ | h₁₃
  · suffices hIoc₂₁ : toIocMod hp x₂' x₁ = x₁ + p from hIoc₂₁.trans_ge h₃₁
    apply (toIocMod_eq_iff hp).2
    exact ⟨⟨h₂₁, by simp [x₂', left_le_toIcoMod]⟩, -1, by simp⟩
  have hIoc₁₃ : toIocMod hp x₁ x₃' = x₃' - p := by
    apply (toIocMod_eq_iff hp).2
    exact ⟨⟨lt_sub_iff_add_lt.2 h₁₃, le_of_lt (h₃₂.trans h₂₁)⟩, 1, by simp⟩
  have not_h₃₂ := (h.trans hIoc₁₃.le).not_gt
  contradiction

/--
theorem `toIxxMod_antisymm` / 定理 `toIxxMod_antisymm`

English:
theorem toIxxMod_antisymm
  statement: (h₁₂₃ : toIcoMod hp a b <= toIocMod hp a c)
  proof: by
  by_contra! h
  rw [modEq_comm] at h
  rw [← (not_modEq_iff_toIcoMod_eq_toIocMod hp).mp h.2.2] at h₁₂₃
  rw [← (not_modEq_iff_toIcoMod_eq_toIocMod hp).mp h.1] at h₁₃₂
  exact h.2.1 ((toIcoMod_inj _).1 <| h₁₃₂.antisymm h₁₂₃)

中文:
定理 toIxxMod_antisymm
  结论: (h₁₂₃ : toIcoMod hp a b <= toIocMod hp a c)
  证明: by
  by_contra! h
  rw [modEq_comm] at h
  rw [← (not_modEq_iff_toIcoMod_eq_toIocMod hp).mp h.2.2] at h₁₂₃
  rw [← (not_modEq_iff_toIcoMod_eq_toIocMod hp).mp h.1] at h₁₃₂
  exact h.2.1 ((toIcoMod_inj _).1 <| h₁₃₂.antisymm h₁₂₃)
-/
private theorem toIxxMod_antisymm (h₁₂₃ : toIcoMod hp a b <= toIocMod hp a c)
    (h₁₃₂ : toIcoMod hp a c <= toIocMod hp a b) :
    b ≡ a [PMOD p] ∨ c ≡ b [PMOD p] ∨ a ≡ c [PMOD p] := by
  by_contra! h
  rw [modEq_comm] at h
  rw [← (not_modEq_iff_toIcoMod_eq_toIocMod hp).mp h.2.2] at h₁₂₃
  rw [← (not_modEq_iff_toIcoMod_eq_toIocMod hp).mp h.1] at h₁₃₂
  exact h.2.1 ((toIcoMod_inj _).1 <| h₁₃₂.antisymm h₁₂₃)

/--
theorem `toIxxMod_total'` / 定理 `toIxxMod_total'`

English:
theorem toIxxMod_total'
  given: (a b c : α)
  proof: by
  /- an essential ingredient is the lemma saying {a-b} + {b-a} = period if a ≠ b (and = 0 if a = b).
    Thus if a ≠ b and b ≠ c then ({a-b} + {b-c}) + ({c-b} + {b-a}) = 2 * period, so one of
    `{a-b} + {b-c}` and `{c-b} + {b-a}` must be `≤ period` -/
  have := congr_arg₂ (· + ·) (toIcoMod_add_

中文:
定理 toIxxMod_total'
  条件: (a b c : α)
  证明: by
  /- an essential ingredient is the lemma saying {a-b} + {b-a} = period if a ≠ b (and = 0 if a = b).
    Thus if a ≠ b and b ≠ c then ({a-b} + {b-c}) + ({c-b} + {b-a}) = 2 * period, so one of
    `{a-b} + {b-c}` and `{c-b} + {b-a}` must be `≤ period` -/
  have := congr_arg₂ (· + ·) (toIcoMod_add_
-/
private theorem toIxxMod_total' (a b c : α) :
    toIcoMod hp b a <= toIocMod hp b c ∨ toIcoMod hp b c <= toIocMod hp b a := by
  /- an essential ingredient is the lemma saying {a-b} + {b-a} = period if a ≠ b (and = 0 if a = b).
    Thus if a ≠ b and b ≠ c then ({a-b} + {b-c}) + ({c-b} + {b-a}) = 2 * period, so one of
    `{a-b} + {b-c}` and `{c-b} + {b-a}` must be `≤ period` -/
  have := congr_arg₂ (· + ·) (toIcoMod_add_toIocMod_zero hp a b) (toIcoMod_add_toIocMod_zero hp c b)
  simp only [add_add_add_comm] at this
  rw [_root_.add_comm (toIocMod _ _ _)]; rw [add_add_add_comm]; rw [← two_nsmul] at this
  replace := min_le_of_add_le_two_nsmul this.le
  rw [min_le_iff] at this
  rw [toIxxMod_iff]; rw [toIxxMod_iff]
  grw [← toIcoMod_le_toIocMod, ← toIcoMod_le_toIocMod] at this
  exact this

/--
theorem `toIxxMod_total` / 定理 `toIxxMod_total`

English:
theorem toIxxMod_total
  given: (a b c : α)
  proof: (toIxxMod_total' _ _ _ _).imp_right toIxxMod_cyclic_left _

中文:
定理 toIxxMod_total
  条件: (a b c : α)
  证明: (toIxxMod_total' _ _ _ _).imp_right toIxxMod_cyclic_left _
-/
private theorem toIxxMod_total (a b c : α) :
    toIcoMod hp a b <= toIocMod hp a c ∨ toIcoMod hp c b <= toIocMod hp c a :=
(toIxxMod_total' _ _ _ _).imp_right toIxxMod_cyclic_left _

/--
theorem `toIxxMod_trans` / 定理 `toIxxMod_trans`

English:
theorem toIxxMod_trans
  statement: {x₁ x₂ x₃ x₄ : α}
  proof: by
  constructor
  · suffices h : ¬x₃ ≡ x₂ [PMOD p] by
      have h₁₂₃' := toIxxMod_cyclic_left _ (toIxxMod_cyclic_left _ h₁₂₃.1)
      have h₂₃₄' := toIxxMod_cyclic_left _ (toIxxMod_cyclic_left _ h₂₃₄.1)
      rw [(not_modEq_iff_toIcoMod_eq_toIocMod hp).1 h] at h₂₃₄'
      exact toIxxMod_cyclic_lef

中文:
定理 toIxxMod_trans
  结论: {x₁ x₂ x₃ x₄ : α}
  证明: by
  constructor
  · suffices h : ¬x₃ ≡ x₂ [PMOD p] by
      have h₁₂₃' := toIxxMod_cyclic_left _ (toIxxMod_cyclic_left _ h₁₂₃.1)
      have h₂₃₄' := toIxxMod_cyclic_left _ (toIxxMod_cyclic_left _ h₂₃₄.1)
      rw [(not_modEq_iff_toIcoMod_eq_toIocMod hp).1 h] at h₂₃₄'
      exact toIxxMod_cyclic_lef
-/
private theorem toIxxMod_trans {x₁ x₂ x₃ x₄ : α}
    (h₁₂₃ : toIcoMod hp x₁ x₂ <= toIocMod hp x₁ x₃ ∧ ¬toIcoMod hp x₃ x₂ <= toIocMod hp x₃ x₁)
    (h₂₃₄ : toIcoMod hp x₂ x₄ <= toIocMod hp x₂ x₃ ∧ ¬toIcoMod hp x₃ x₄ <= toIocMod hp x₃ x₂) :
    toIcoMod hp x₁ x₄ <= toIocMod hp x₁ x₃ ∧ ¬toIcoMod hp x₃ x₄ <= toIocMod hp x₃ x₁ := by
  constructor
  · suffices h : ¬x₃ ≡ x₂ [PMOD p] by
      have h₁₂₃' := toIxxMod_cyclic_left _ (toIxxMod_cyclic_left _ h₁₂₃.1)
      have h₂₃₄' := toIxxMod_cyclic_left _ (toIxxMod_cyclic_left _ h₂₃₄.1)
      rw [(not_modEq_iff_toIcoMod_eq_toIocMod hp).1 h] at h₂₃₄'
      exact toIxxMod_cyclic_left _ (h₁₂₃'.trans h₂₃₄')
    by_contra h
    rw [(modEq_iff_toIcoMod_eq_left hp).1 h] at h₁₂₃
    exact h₁₂₃.2 (left_lt_toIocMod _ _ _).le
  · rw [not_le] at h₁₂₃ h₂₃₄ ⊢
    exact (h₁₂₃.2.trans_le (toIcoMod_le_toIocMod _ x₃ x₂)).trans h₂₃₄.2

namespace QuotientAddGroup

variable [hp' : Fact (0 < p)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Btw (α ⧸ AddSubgroup.zmultiples p)
  body: (equivIcoMod hp'.out 0 (x₂ - x₁) : α) <= equivIocMod hp'.out 0 (x₃ - x₁)

中文:
实例 :
  签名: Btw (α ⧸ 加法子群.zmultiples p)
  定义体: (equivIcoMod hp'.out 0 (x₂ - x₁) : α) <= equivIocMod hp'.out 0 (x₃ - x₁)

Depends on / 依赖: equivIcoMod, equivIocMod
-/
instance : Btw (α ⧸ AddSubgroup.zmultiples p) where
  btw x₁ x₂ x₃ := (equivIcoMod hp'.out 0 (x₂ - x₁) : α) <= equivIocMod hp'.out 0 (x₃ - x₁)

/--
theorem `btw_coe_iff'` / 定理 `btw_coe_iff'`

English:
theorem btw_coe_iff'
  given: {x₁ x₂ x₃ : α}
  proof: Iff.rfl

中文:
定理 btw_coe_iff'
  条件: {x₁ x₂ x₃ : α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem btw_coe_iff' {x₁ x₂ x₃ : α} :
    Btw.btw (x₁ : α ⧸ AddSubgroup.zmultiples p) x₂ x₃ ↔
      toIcoMod hp'.out 0 (x₂ - x₁) <= toIocMod hp'.out 0 (x₃ - x₁) :=
  Iff.rfl

-- maybe harder to use than the primed one?
/--
theorem `btw_coe_iff` / 定理 `btw_coe_iff`

English:
theorem btw_coe_iff
  given: {x₁ x₂ x₃ : α}
  proof: by
  rw [btw_coe_iff']; rw [toIocMod_sub_eq_sub]; rw [toIcoMod_sub_eq_sub]; rw [zero_add]; rw [sub_le_sub_iff_right]

中文:
定理 btw_coe_iff
  条件: {x₁ x₂ x₃ : α}
  证明: by
  rw [btw_coe_iff']; rw [toIocMod_sub_eq_sub]; rw [toIcoMod_sub_eq_sub]; rw [zero_add]; rw [sub_le_sub_iff_right]

Depends on / 依赖: btw_coe_iff, sub_le_sub_iff_right, toIcoMod_sub_eq_sub, toIocMod_sub_eq_sub, zero_add
-/
theorem btw_coe_iff {x₁ x₂ x₃ : α} :
    Btw.btw (x₁ : α ⧸ AddSubgroup.zmultiples p) x₂ x₃ ↔
      toIcoMod hp'.out x₁ x₂ <= toIocMod hp'.out x₁ x₃ := by
  rw [btw_coe_iff']; rw [toIocMod_sub_eq_sub]; rw [toIcoMod_sub_eq_sub]; rw [zero_add]; rw [sub_le_sub_iff_right]

/--
Instance `circularPreorder` / 实例 `circularPreorder`

English:
instance circularPreorder
  signature: : CircularPreorder (α ⧸ AddSubgroup.zmultiples p) where
  body: show _ <= _ by simp [sub_self, hp'.out.le]
  btw_cyclic_left {x₁ x₂ x₃} h := by
    induction x₁ using QuotientAddGroup.induction_on
    induction x₂ using QuotientAddGroup.induction_on
    induction x₃ using QuotientAddGroup.induction_on
    simp_rw [btw_coe_iff] at h ⊢
    apply toIxxMod_cyclic_le

中文:
实例 circularPreorder
  签名: : 循环预序 (α ⧸ 加法子群.zmultiples p) where
  定义体: show _ <= _ by simp [sub_self, hp'.out.le]
  btw_cyclic_left {x₁ x₂ x₃} h := by
    induction x₁ using QuotientAddGroup.induction_on
    induction x₂ using QuotientAddGroup.induction_on
    induction x₃ using QuotientAddGroup.induction_on
    simp_rw [btw_coe_iff] at h ⊢
    apply toIxxMod_cyclic_le

Depends on / 依赖: out.le, sub_self
-/
instance circularPreorder : CircularPreorder (α ⧸ AddSubgroup.zmultiples p) where
  btw_refl x := show _ <= _ by simp [sub_self, hp'.out.le]
  btw_cyclic_left {x₁ x₂ x₃} h := by
    induction x₁ using QuotientAddGroup.induction_on
    induction x₂ using QuotientAddGroup.induction_on
    induction x₃ using QuotientAddGroup.induction_on
    simp_rw [btw_coe_iff] at h ⊢
    apply toIxxMod_cyclic_left _ h
  sbtw := _
  sbtw_iff_btw_not_btw := Iff.rfl
  sbtw_trans_left {x₁ x₂ x₃ x₄} (h₁₂₃ : _ ∧ _) (h₂₃₄ : _ ∧ _) :=
    show _ ∧ _ by
      induction x₁ using QuotientAddGroup.induction_on
      induction x₂ using QuotientAddGroup.induction_on
      induction x₃ using QuotientAddGroup.induction_on
      induction x₄ using QuotientAddGroup.induction_on
      simp_rw [btw_coe_iff] at h₁₂₃ h₂₃₄ ⊢
      apply toIxxMod_trans _ h₁₂₃ h₂₃₄

/--
Instance `circularOrder` / 实例 `circularOrder`

English:
instance circularOrder
  signature: : CircularOrder (α ⧸ AddSubgroup.zmultiples p)
  body: { QuotientAddGroup.circularPreorder with
    btw_antisymm := fun {x₁ x₂ x₃} h₁₂₃ h₃₂₁ => by
      induction x₁ using QuotientAddGroup.induction_on
      induction x₂ using QuotientAddGroup.induction_on
      induction x₃ using QuotientAddGroup.induction_on
      rw [btw_cyclic] at h₃₂₁
      simp_rw

中文:
实例 circularOrder
  签名: : Circular序 (α ⧸ 加法子群.zmultiples p)
  定义体: { QuotientAddGroup.circularPreorder with
    btw_antisymm := fun {x₁ x₂ x₃} h₁₂₃ h₃₂₁ => by
      induction x₁ using QuotientAddGroup.induction_on
      induction x₂ using QuotientAddGroup.induction_on
      induction x₃ using QuotientAddGroup.induction_on
      rw [btw_cyclic] at h₃₂₁
      simp_rw

Depends on / 依赖: Quotie, QuotientAddGroup, QuotientAddGroup.circularPreorder, QuotientAddGroup.induction_on, btw_antisymm, btw_coe_iff, btw_cyclic, btw_total, circularPreorder, induction_on, modEq_comm, modEq_iff_eq_mod_zmultiples, simp_rw, toIxxMod_antisymm
-/
instance circularOrder : CircularOrder (α ⧸ AddSubgroup.zmultiples p) :=
  { QuotientAddGroup.circularPreorder with
    btw_antisymm := fun {x₁ x₂ x₃} h₁₂₃ h₃₂₁ => by
      induction x₁ using QuotientAddGroup.induction_on
      induction x₂ using QuotientAddGroup.induction_on
      induction x₃ using QuotientAddGroup.induction_on
      rw [btw_cyclic] at h₃₂₁
      simp_rw [btw_coe_iff] at h₁₂₃ h₃₂₁
      simp_rw [← modEq_iff_eq_mod_zmultiples]
      simpa only [modEq_comm] using toIxxMod_antisymm _ h₁₂₃ h₃₂₁
    btw_total := fun x₁ x₂ x₃ => by
      induction x₁ using QuotientAddGroup.induction_on
      induction x₂ using QuotientAddGroup.induction_on
      induction x₃ using QuotientAddGroup.induction_on
      simp_rw [btw_coe_iff]
      apply toIxxMod_total }

end QuotientAddGroup

end Circular

end LinearOrderedAddCommGroup

/-!
### `simp` confluence lemmas for rings

In rings, we simplify `(m : ℤ) • x` to `↑m * x`, so we need to restate some lemmas
using `↑m * x` instead of `m • x`. In some lemmas, `m` is a variable,
in other lemmas `m = toIcoDiv _ _ _` or `m = toIocDiv _ _ _`.
-/

section Ring

variable {R : Type*} [NonAssocRing R] [LinearOrder R] [IsOrderedAddMonoid R] [Archimedean R] {p : R}
  (hp : 0 < p)

@[simp]
/--
theorem `self_sub_toIcoDiv_mul` / 定理 `self_sub_toIcoDiv_mul`

English:
theorem self_sub_toIcoDiv_mul
  given: (a b : R)
  statement: b - toIcoDiv hp a b * p = toIcoMod hp a b
  proof: by
  simpa using self_sub_toIcoDiv_zsmul hp a b

@[simp]

中文:
定理 self_sub_toIcoDiv_mul
  条件: (a b : R)
  结论: b - toIcoDiv hp a b * p = toIcoMod hp a b
  证明: by
  simpa using self_sub_toIcoDiv_zsmul hp a b

@[simp]

Depends on / 依赖: self_sub_toIcoDiv_zsmul
-/
theorem self_sub_toIcoDiv_mul (a b : R) : b - toIcoDiv hp a b * p = toIcoMod hp a b := by
  simpa using self_sub_toIcoDiv_zsmul hp a b

@[simp]
/--
theorem `self_sub_toIocDiv_mul` / 定理 `self_sub_toIocDiv_mul`

English:
theorem self_sub_toIocDiv_mul
  given: (a b : R)
  statement: b - toIocDiv hp a b * p = toIocMod hp a b
  proof: by
  simpa using self_sub_toIocDiv_zsmul hp a b

@[simp]

中文:
定理 self_sub_toIocDiv_mul
  条件: (a b : R)
  结论: b - toIocDiv hp a b * p = toIocMod hp a b
  证明: by
  simpa using self_sub_toIocDiv_zsmul hp a b

@[simp]

Depends on / 依赖: self_sub_toIocDiv_zsmul
-/
theorem self_sub_toIocDiv_mul (a b : R) : b - toIocDiv hp a b * p = toIocMod hp a b := by
  simpa using self_sub_toIocDiv_zsmul hp a b

@[simp]
/--
theorem `toIcoDiv_mul_sub_self` / 定理 `toIcoDiv_mul_sub_self`

English:
theorem toIcoDiv_mul_sub_self
  given: (a b : R)
  statement: toIcoDiv hp a b * p - b = -toIcoMod hp a b
  proof: by
  simpa using toIcoDiv_zsmul_sub_self hp a b

@[simp]

中文:
定理 toIcoDiv_mul_sub_self
  条件: (a b : R)
  结论: toIcoDiv hp a b * p - b = -toIcoMod hp a b
  证明: by
  simpa using toIcoDiv_zsmul_sub_self hp a b

@[simp]

Depends on / 依赖: toIcoDiv_zsmul_sub_self
-/
theorem toIcoDiv_mul_sub_self (a b : R) : toIcoDiv hp a b * p - b = -toIcoMod hp a b := by
  simpa using toIcoDiv_zsmul_sub_self hp a b

@[simp]
/--
theorem `toIocDiv_mul_sub_self` / 定理 `toIocDiv_mul_sub_self`

English:
theorem toIocDiv_mul_sub_self
  given: (a b : R)
  statement: toIocDiv hp a b * p - b = -toIocMod hp a b
  proof: by
  simpa using toIocDiv_zsmul_sub_self hp a b

中文:
定理 toIocDiv_mul_sub_self
  条件: (a b : R)
  结论: toIocDiv hp a b * p - b = -toIocMod hp a b
  证明: by
  simpa using toIocDiv_zsmul_sub_self hp a b

Depends on / 依赖: toIocDiv_zsmul_sub_self
-/
theorem toIocDiv_mul_sub_self (a b : R) : toIocDiv hp a b * p - b = -toIocMod hp a b := by
  simpa using toIocDiv_zsmul_sub_self hp a b

/--
theorem `toIcoMod_sub_self_eq_mul` / 定理 `toIcoMod_sub_self_eq_mul`

English:
theorem toIcoMod_sub_self_eq_mul
  given: (a b : R)
  statement: toIcoMod hp a b - b = -toIcoDiv hp a b * p
  proof: by
  simp

中文:
定理 toIcoMod_sub_self_eq_mul
  条件: (a b : R)
  结论: toIcoMod hp a b - b = -toIcoDiv hp a b * p
  证明: by
  simp
-/
theorem toIcoMod_sub_self_eq_mul (a b : R) : toIcoMod hp a b - b = -toIcoDiv hp a b * p := by
  simp

/--
theorem `toIocMod_sub_self_eq_mul` / 定理 `toIocMod_sub_self_eq_mul`

English:
theorem toIocMod_sub_self_eq_mul
  given: (a b : R)
  statement: toIocMod hp a b - b = -toIocDiv hp a b * p
  proof: by
  simp

中文:
定理 toIocMod_sub_self_eq_mul
  条件: (a b : R)
  结论: toIocMod hp a b - b = -toIocDiv hp a b * p
  证明: by
  simp
-/
theorem toIocMod_sub_self_eq_mul (a b : R) : toIocMod hp a b - b = -toIocDiv hp a b * p := by
  simp

/--
theorem `self_sub_toIcoMod_eq_mul` / 定理 `self_sub_toIcoMod_eq_mul`

English:
theorem self_sub_toIcoMod_eq_mul
  given: (a b : R)
  statement: b - toIcoMod hp a b = toIcoDiv hp a b * p
  proof: by
  simp

中文:
定理 self_sub_toIcoMod_eq_mul
  条件: (a b : R)
  结论: b - toIcoMod hp a b = toIcoDiv hp a b * p
  证明: by
  simp
-/
theorem self_sub_toIcoMod_eq_mul (a b : R) : b - toIcoMod hp a b = toIcoDiv hp a b * p := by
  simp

/--
theorem `self_sub_toIocMod_eq_mul` / 定理 `self_sub_toIocMod_eq_mul`

English:
theorem self_sub_toIocMod_eq_mul
  given: (a b : R)
  statement: b - toIocMod hp a b = toIocDiv hp a b * p
  proof: by
  simp

@[simp]

中文:
定理 self_sub_toIocMod_eq_mul
  条件: (a b : R)
  结论: b - toIocMod hp a b = toIocDiv hp a b * p
  证明: by
  simp

@[simp]
-/
theorem self_sub_toIocMod_eq_mul (a b : R) : b - toIocMod hp a b = toIocDiv hp a b * p := by
  simp

@[simp]
/--
theorem `toIcoMod_add_toIcoDiv_mul` / 定理 `toIcoMod_add_toIcoDiv_mul`

English:
theorem toIcoMod_add_toIcoDiv_mul
  given: (a b : R)
  statement: toIcoMod hp a b + toIcoDiv hp a b * p = b
  proof: by
  simpa using toIcoMod_add_toIcoDiv_zsmul hp a b

@[simp]

中文:
定理 toIcoMod_add_toIcoDiv_mul
  条件: (a b : R)
  结论: toIcoMod hp a b + toIcoDiv hp a b * p = b
  证明: by
  simpa using toIcoMod_add_toIcoDiv_zsmul hp a b

@[simp]

Depends on / 依赖: toIcoMod_add_toIcoDiv_zsmul
-/
theorem toIcoMod_add_toIcoDiv_mul (a b : R) : toIcoMod hp a b + toIcoDiv hp a b * p = b := by
  simpa using toIcoMod_add_toIcoDiv_zsmul hp a b

@[simp]
/--
theorem `toIocMod_add_toIocDiv_mul` / 定理 `toIocMod_add_toIocDiv_mul`

English:
theorem toIocMod_add_toIocDiv_mul
  given: (a b : R)
  statement: toIocMod hp a b + toIocDiv hp a b * p = b
  proof: by
  simpa using toIocMod_add_toIocDiv_zsmul hp a b

@[simp]

中文:
定理 toIocMod_add_toIocDiv_mul
  条件: (a b : R)
  结论: toIocMod hp a b + toIocDiv hp a b * p = b
  证明: by
  simpa using toIocMod_add_toIocDiv_zsmul hp a b

@[simp]

Depends on / 依赖: toIocMod_add_toIocDiv_zsmul
-/
theorem toIocMod_add_toIocDiv_mul (a b : R) : toIocMod hp a b + toIocDiv hp a b * p = b := by
  simpa using toIocMod_add_toIocDiv_zsmul hp a b

@[simp]
/--
theorem `toIcoDiv_mul_sub_toIcoMod` / 定理 `toIcoDiv_mul_sub_toIcoMod`

English:
theorem toIcoDiv_mul_sub_toIcoMod
  given: (a b : R)
  statement: toIcoDiv hp a b * p + toIcoMod hp a b = b
  proof: by
  rw [add_comm]; rw [toIcoMod_add_toIcoDiv_mul]

@[simp]

中文:
定理 toIcoDiv_mul_sub_toIcoMod
  条件: (a b : R)
  结论: toIcoDiv hp a b * p + toIcoMod hp a b = b
  证明: by
  rw [add_comm]; rw [toIcoMod_add_toIcoDiv_mul]

@[simp]

Depends on / 依赖: add_comm, toIcoMod_add_toIcoDiv_mul
-/
theorem toIcoDiv_mul_sub_toIcoMod (a b : R) : toIcoDiv hp a b * p + toIcoMod hp a b = b := by
  rw [add_comm]; rw [toIcoMod_add_toIcoDiv_mul]

@[simp]
/--
theorem `toIocDiv_mul_sub_toIocMod` / 定理 `toIocDiv_mul_sub_toIocMod`

English:
theorem toIocDiv_mul_sub_toIocMod
  given: (a b : R)
  statement: toIocDiv hp a b * p + toIocMod hp a b = b
  proof: by
  rw [add_comm]; rw [toIocMod_add_toIocDiv_mul]

@[simp]

中文:
定理 toIocDiv_mul_sub_toIocMod
  条件: (a b : R)
  结论: toIocDiv hp a b * p + toIocMod hp a b = b
  证明: by
  rw [add_comm]; rw [toIocMod_add_toIocDiv_mul]

@[simp]

Depends on / 依赖: add_comm, toIocMod_add_toIocDiv_mul
-/
theorem toIocDiv_mul_sub_toIocMod (a b : R) : toIocDiv hp a b * p + toIocMod hp a b = b := by
  rw [add_comm]; rw [toIocMod_add_toIocDiv_mul]

@[simp]
/--
theorem `toIcoDiv_add_intCast_mul` / 定理 `toIcoDiv_add_intCast_mul`

English:
theorem toIcoDiv_add_intCast_mul
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIcoDiv_add_zsmul hp a b m

@[simp]

中文:
定理 toIcoDiv_add_intCast_mul
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIcoDiv_add_zsmul hp a b m

@[simp]

Depends on / 依赖: toIcoDiv_add_zsmul
-/
theorem toIcoDiv_add_intCast_mul (a b : R) (m : Int) :
    toIcoDiv hp a (b + m * p) = toIcoDiv hp a b + m := by
  simpa using toIcoDiv_add_zsmul hp a b m

@[simp]
/--
theorem `toIcoDiv_add_natCast_mul` / 定理 `toIcoDiv_add_natCast_mul`

English:
theorem toIcoDiv_add_natCast_mul
  given: (a b : R) (m : Nat)
  proof: mod_cast toIcoDiv_add_intCast_mul hp a b m

@[simp]

中文:
定理 toIcoDiv_add_natCast_mul
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIcoDiv_add_intCast_mul hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoDiv_add_intCast_mul
-/
theorem toIcoDiv_add_natCast_mul (a b : R) (m : Nat) :
    toIcoDiv hp a (b + m * p) = toIcoDiv hp a b + m :=
  mod_cast toIcoDiv_add_intCast_mul hp a b m

@[simp]
/--
theorem `toIcoDiv_add_ofNat_mul` / 定理 `toIcoDiv_add_ofNat_mul`

English:
theorem toIcoDiv_add_ofNat_mul
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIcoDiv_add_natCast_mul hp a b m

@[simp]

中文:
定理 toIcoDiv_add_of自然数_mul
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIcoDiv_add_natCast_mul hp a b m

@[simp]

Depends on / 依赖: toIcoDiv_add_natCast_mul
-/
theorem toIcoDiv_add_ofNat_mul (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIcoDiv hp a (b + ofNat(m) * p) = toIcoDiv hp a b + ofNat(m) :=
  toIcoDiv_add_natCast_mul hp a b m

@[simp]
/--
theorem `toIcoDiv_add_intCast_mul'` / 定理 `toIcoDiv_add_intCast_mul'`

English:
theorem toIcoDiv_add_intCast_mul'
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIcoDiv_add_zsmul' hp a b m

@[simp]

中文:
定理 toIcoDiv_add_intCast_mul'
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIcoDiv_add_zsmul' hp a b m

@[simp]

Depends on / 依赖: toIcoDiv_add_zsmul
-/
theorem toIcoDiv_add_intCast_mul' (a b : R) (m : Int) :
    toIcoDiv hp (a + m * p) b = toIcoDiv hp a b - m := by
  simpa using toIcoDiv_add_zsmul' hp a b m

@[simp]
/--
theorem `toIcoDiv_add_natCast_mul'` / 定理 `toIcoDiv_add_natCast_mul'`

English:
theorem toIcoDiv_add_natCast_mul'
  given: (a b : R) (m : Nat)
  proof: mod_cast toIcoDiv_add_intCast_mul' hp a b m

@[simp]

中文:
定理 toIcoDiv_add_natCast_mul'
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIcoDiv_add_intCast_mul' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoDiv_add_intCast_mul
-/
theorem toIcoDiv_add_natCast_mul' (a b : R) (m : Nat) :
    toIcoDiv hp (a + m * p) b = toIcoDiv hp a b - m :=
  mod_cast toIcoDiv_add_intCast_mul' hp a b m

@[simp]
/--
theorem `toIcoDiv_add_ofNat_mul'` / 定理 `toIcoDiv_add_ofNat_mul'`

English:
theorem toIcoDiv_add_ofNat_mul'
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIcoDiv_add_natCast_mul' hp a b m

@[simp]

中文:
定理 toIcoDiv_add_of自然数_mul'
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIcoDiv_add_natCast_mul' hp a b m

@[simp]

Depends on / 依赖: toIcoDiv_add_natCast_mul
-/
theorem toIcoDiv_add_ofNat_mul' (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIcoDiv hp (a + ofNat(m) * p) b = toIcoDiv hp a b - ofNat(m) :=
  toIcoDiv_add_natCast_mul' hp a b m

@[simp]
/--
theorem `toIocDiv_add_intCast_mul` / 定理 `toIocDiv_add_intCast_mul`

English:
theorem toIocDiv_add_intCast_mul
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIocDiv_add_zsmul hp a b m

@[simp]

中文:
定理 toIocDiv_add_intCast_mul
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIocDiv_add_zsmul hp a b m

@[simp]

Depends on / 依赖: toIocDiv_add_zsmul
-/
theorem toIocDiv_add_intCast_mul (a b : R) (m : Int) :
    toIocDiv hp a (b + m * p) = toIocDiv hp a b + m := by
  simpa using toIocDiv_add_zsmul hp a b m

@[simp]
/--
theorem `toIocDiv_add_natCast_mul` / 定理 `toIocDiv_add_natCast_mul`

English:
theorem toIocDiv_add_natCast_mul
  given: (a b : R) (m : Nat)
  proof: mod_cast toIocDiv_add_intCast_mul hp a b m

@[simp]

中文:
定理 toIocDiv_add_natCast_mul
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIocDiv_add_intCast_mul hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocDiv_add_intCast_mul
-/
theorem toIocDiv_add_natCast_mul (a b : R) (m : Nat) :
    toIocDiv hp a (b + m * p) = toIocDiv hp a b + m :=
  mod_cast toIocDiv_add_intCast_mul hp a b m

@[simp]
/--
theorem `toIocDiv_add_ofNat_mul` / 定理 `toIocDiv_add_ofNat_mul`

English:
theorem toIocDiv_add_ofNat_mul
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIocDiv_add_natCast_mul hp a b m

@[simp]

中文:
定理 toIocDiv_add_of自然数_mul
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIocDiv_add_natCast_mul hp a b m

@[simp]

Depends on / 依赖: toIocDiv_add_natCast_mul
-/
theorem toIocDiv_add_ofNat_mul (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIocDiv hp a (b + ofNat(m) * p) = toIocDiv hp a b + ofNat(m) :=
  toIocDiv_add_natCast_mul hp a b m

@[simp]
/--
theorem `toIocDiv_add_intCast_mul'` / 定理 `toIocDiv_add_intCast_mul'`

English:
theorem toIocDiv_add_intCast_mul'
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIocDiv_add_zsmul' hp a b m

@[simp]

中文:
定理 toIocDiv_add_intCast_mul'
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIocDiv_add_zsmul' hp a b m

@[simp]

Depends on / 依赖: toIocDiv_add_zsmul
-/
theorem toIocDiv_add_intCast_mul' (a b : R) (m : Int) :
    toIocDiv hp (a + m * p) b = toIocDiv hp a b - m := by
  simpa using toIocDiv_add_zsmul' hp a b m

@[simp]
/--
theorem `toIocDiv_add_natCast_mul'` / 定理 `toIocDiv_add_natCast_mul'`

English:
theorem toIocDiv_add_natCast_mul'
  given: (a b : R) (m : Nat)
  proof: mod_cast toIocDiv_add_intCast_mul' hp a b m

@[simp]

中文:
定理 toIocDiv_add_natCast_mul'
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIocDiv_add_intCast_mul' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocDiv_add_intCast_mul
-/
theorem toIocDiv_add_natCast_mul' (a b : R) (m : Nat) :
    toIocDiv hp (a + m * p) b = toIocDiv hp a b - m :=
  mod_cast toIocDiv_add_intCast_mul' hp a b m

@[simp]
/--
theorem `toIocDiv_add_ofNat_mul'` / 定理 `toIocDiv_add_ofNat_mul'`

English:
theorem toIocDiv_add_ofNat_mul'
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIocDiv_add_natCast_mul' hp a b m

@[simp]

中文:
定理 toIocDiv_add_of自然数_mul'
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIocDiv_add_natCast_mul' hp a b m

@[simp]

Depends on / 依赖: toIocDiv_add_natCast_mul
-/
theorem toIocDiv_add_ofNat_mul' (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIocDiv hp (a + ofNat(m) * p) b = toIocDiv hp a b - ofNat(m) :=
  toIocDiv_add_natCast_mul' hp a b m

@[simp]
/--
theorem `toIcoDiv_intCast_mul_add` / 定理 `toIcoDiv_intCast_mul_add`

English:
theorem toIcoDiv_intCast_mul_add
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIcoDiv_zsmul_add hp a b m

@[simp]

中文:
定理 toIcoDiv_intCast_mul_add
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIcoDiv_zsmul_add hp a b m

@[simp]

Depends on / 依赖: toIcoDiv_zsmul_add
-/
theorem toIcoDiv_intCast_mul_add (a b : R) (m : Int) :
    toIcoDiv hp a (m * p + b) = m + toIcoDiv hp a b := by
  simpa using toIcoDiv_zsmul_add hp a b m

@[simp]
/--
theorem `toIcoDiv_natCast_mul_add` / 定理 `toIcoDiv_natCast_mul_add`

English:
theorem toIcoDiv_natCast_mul_add
  given: (a b : R) (m : Nat)
  proof: mod_cast toIcoDiv_intCast_mul_add hp a b m

@[simp]

中文:
定理 toIcoDiv_natCast_mul_add
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIcoDiv_intCast_mul_add hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoDiv_intCast_mul_add
-/
theorem toIcoDiv_natCast_mul_add (a b : R) (m : Nat) :
    toIcoDiv hp a (m * p + b) = m + toIcoDiv hp a b :=
  mod_cast toIcoDiv_intCast_mul_add hp a b m

@[simp]
/--
theorem `toIcoDiv_ofNat_mul_add` / 定理 `toIcoDiv_ofNat_mul_add`

English:
theorem toIcoDiv_ofNat_mul_add
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIcoDiv_natCast_mul_add hp a b m

中文:
定理 toIcoDiv_of自然数_mul_add
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIcoDiv_natCast_mul_add hp a b m

Depends on / 依赖: toIcoDiv_natCast_mul_add
-/
theorem toIcoDiv_ofNat_mul_add (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIcoDiv hp a (ofNat(m) * p + b) = ofNat(m) + toIcoDiv hp a b :=
  toIcoDiv_natCast_mul_add hp a b m

/-! Note we omit `toIcoDiv_intCast_mul_add'` as `-m + toIcoDiv hp a b` is not very convenient. -/

@[simp]
/--
theorem `toIocDiv_intCast_mul_add` / 定理 `toIocDiv_intCast_mul_add`

English:
theorem toIocDiv_intCast_mul_add
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIocDiv_zsmul_add hp a b m

@[simp]

中文:
定理 toIocDiv_intCast_mul_add
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIocDiv_zsmul_add hp a b m

@[simp]

Depends on / 依赖: toIocDiv_zsmul_add
-/
theorem toIocDiv_intCast_mul_add (a b : R) (m : Int) :
    toIocDiv hp a (m * p + b) = m + toIocDiv hp a b := by
  simpa using toIocDiv_zsmul_add hp a b m

@[simp]
/--
theorem `toIocDiv_natCast_mul_add` / 定理 `toIocDiv_natCast_mul_add`

English:
theorem toIocDiv_natCast_mul_add
  given: (a b : R) (m : Nat)
  proof: mod_cast toIocDiv_intCast_mul_add hp a b m

@[simp]

中文:
定理 toIocDiv_natCast_mul_add
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIocDiv_intCast_mul_add hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocDiv_intCast_mul_add
-/
theorem toIocDiv_natCast_mul_add (a b : R) (m : Nat) :
    toIocDiv hp a (m * p + b) = m + toIocDiv hp a b :=
  mod_cast toIocDiv_intCast_mul_add hp a b m

@[simp]
/--
theorem `toIocDiv_ofNat_mul_add` / 定理 `toIocDiv_ofNat_mul_add`

English:
theorem toIocDiv_ofNat_mul_add
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIocDiv_natCast_mul_add hp a b m

中文:
定理 toIocDiv_of自然数_mul_add
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIocDiv_natCast_mul_add hp a b m

Depends on / 依赖: toIocDiv_natCast_mul_add
-/
theorem toIocDiv_ofNat_mul_add (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIocDiv hp a (ofNat(m) * p + b) = ofNat(m) + toIocDiv hp a b :=
  toIocDiv_natCast_mul_add hp a b m

/-! Note we omit `toIocDiv_intCast_mul_add'` as `-m + toIocDiv hp a b` is not very convenient. -/

@[simp]
/--
theorem `toIcoDiv_sub_intCast_mul` / 定理 `toIcoDiv_sub_intCast_mul`

English:
theorem toIcoDiv_sub_intCast_mul
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIcoDiv_sub_zsmul hp a b m

@[simp]

中文:
定理 toIcoDiv_sub_intCast_mul
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIcoDiv_sub_zsmul hp a b m

@[simp]

Depends on / 依赖: toIcoDiv_sub_zsmul
-/
theorem toIcoDiv_sub_intCast_mul (a b : R) (m : Int) :
    toIcoDiv hp a (b - m * p) = toIcoDiv hp a b - m := by
  simpa using toIcoDiv_sub_zsmul hp a b m

@[simp]
/--
theorem `toIcoDiv_sub_natCast_mul` / 定理 `toIcoDiv_sub_natCast_mul`

English:
theorem toIcoDiv_sub_natCast_mul
  given: (a b : R) (m : Nat)
  proof: mod_cast toIcoDiv_sub_intCast_mul hp a b m

@[simp]

中文:
定理 toIcoDiv_sub_natCast_mul
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIcoDiv_sub_intCast_mul hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoDiv_sub_intCast_mul
-/
theorem toIcoDiv_sub_natCast_mul (a b : R) (m : Nat) :
    toIcoDiv hp a (b - m * p) = toIcoDiv hp a b - m :=
  mod_cast toIcoDiv_sub_intCast_mul hp a b m

@[simp]
/--
theorem `toIcoDiv_sub_ofNat_mul` / 定理 `toIcoDiv_sub_ofNat_mul`

English:
theorem toIcoDiv_sub_ofNat_mul
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIcoDiv_sub_natCast_mul hp a b m

@[simp]

中文:
定理 toIcoDiv_sub_of自然数_mul
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIcoDiv_sub_natCast_mul hp a b m

@[simp]

Depends on / 依赖: toIcoDiv_sub_natCast_mul
-/
theorem toIcoDiv_sub_ofNat_mul (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIcoDiv hp a (b - ofNat(m) * p) = toIcoDiv hp a b - ofNat(m) :=
  toIcoDiv_sub_natCast_mul hp a b m

@[simp]
/--
theorem `toIcoDiv_sub_intCast_mul'` / 定理 `toIcoDiv_sub_intCast_mul'`

English:
theorem toIcoDiv_sub_intCast_mul'
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIcoDiv_sub_zsmul' hp a b m

@[simp]

中文:
定理 toIcoDiv_sub_intCast_mul'
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIcoDiv_sub_zsmul' hp a b m

@[simp]

Depends on / 依赖: toIcoDiv_sub_zsmul
-/
theorem toIcoDiv_sub_intCast_mul' (a b : R) (m : Int) :
    toIcoDiv hp (a - m * p) b = toIcoDiv hp a b + m := by
  simpa using toIcoDiv_sub_zsmul' hp a b m

@[simp]
/--
theorem `toIcoDiv_sub_natCast_mul'` / 定理 `toIcoDiv_sub_natCast_mul'`

English:
theorem toIcoDiv_sub_natCast_mul'
  given: (a b : R) (m : Nat)
  proof: mod_cast toIcoDiv_sub_intCast_mul' hp a b m

@[simp]

中文:
定理 toIcoDiv_sub_natCast_mul'
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIcoDiv_sub_intCast_mul' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoDiv_sub_intCast_mul
-/
theorem toIcoDiv_sub_natCast_mul' (a b : R) (m : Nat) :
    toIcoDiv hp (a - m * p) b = toIcoDiv hp a b + m :=
  mod_cast toIcoDiv_sub_intCast_mul' hp a b m

@[simp]
/--
theorem `toIcoDiv_sub_ofNat_mul'` / 定理 `toIcoDiv_sub_ofNat_mul'`

English:
theorem toIcoDiv_sub_ofNat_mul'
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIcoDiv_sub_natCast_mul' hp a b m

@[simp]

中文:
定理 toIcoDiv_sub_of自然数_mul'
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIcoDiv_sub_natCast_mul' hp a b m

@[simp]

Depends on / 依赖: toIcoDiv_sub_natCast_mul
-/
theorem toIcoDiv_sub_ofNat_mul' (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIcoDiv hp (a - ofNat(m) * p) b = toIcoDiv hp a b + ofNat(m) :=
  toIcoDiv_sub_natCast_mul' hp a b m

@[simp]
/--
theorem `toIocDiv_sub_intCast_mul` / 定理 `toIocDiv_sub_intCast_mul`

English:
theorem toIocDiv_sub_intCast_mul
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIocDiv_sub_zsmul hp a b m

@[simp]

中文:
定理 toIocDiv_sub_intCast_mul
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIocDiv_sub_zsmul hp a b m

@[simp]

Depends on / 依赖: toIocDiv_sub_zsmul
-/
theorem toIocDiv_sub_intCast_mul (a b : R) (m : Int) :
    toIocDiv hp a (b - m * p) = toIocDiv hp a b - m := by
  simpa using toIocDiv_sub_zsmul hp a b m

@[simp]
/--
theorem `toIocDiv_sub_natCast_mul` / 定理 `toIocDiv_sub_natCast_mul`

English:
theorem toIocDiv_sub_natCast_mul
  given: (a b : R) (m : Nat)
  proof: mod_cast toIocDiv_sub_intCast_mul hp a b m

@[simp]

中文:
定理 toIocDiv_sub_natCast_mul
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIocDiv_sub_intCast_mul hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocDiv_sub_intCast_mul
-/
theorem toIocDiv_sub_natCast_mul (a b : R) (m : Nat) :
    toIocDiv hp a (b - m * p) = toIocDiv hp a b - m :=
  mod_cast toIocDiv_sub_intCast_mul hp a b m

@[simp]
/--
theorem `toIocDiv_sub_ofNat_mul` / 定理 `toIocDiv_sub_ofNat_mul`

English:
theorem toIocDiv_sub_ofNat_mul
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIocDiv_sub_natCast_mul hp a b m

@[simp]

中文:
定理 toIocDiv_sub_of自然数_mul
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIocDiv_sub_natCast_mul hp a b m

@[simp]

Depends on / 依赖: toIocDiv_sub_natCast_mul
-/
theorem toIocDiv_sub_ofNat_mul (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIocDiv hp a (b - ofNat(m) * p) = toIocDiv hp a b - ofNat(m) :=
  toIocDiv_sub_natCast_mul hp a b m

@[simp]
/--
theorem `toIocDiv_sub_intCast_mul'` / 定理 `toIocDiv_sub_intCast_mul'`

English:
theorem toIocDiv_sub_intCast_mul'
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIocDiv_sub_zsmul' hp a b m

@[simp]

中文:
定理 toIocDiv_sub_intCast_mul'
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIocDiv_sub_zsmul' hp a b m

@[simp]

Depends on / 依赖: toIocDiv_sub_zsmul
-/
theorem toIocDiv_sub_intCast_mul' (a b : R) (m : Int) :
    toIocDiv hp (a - m * p) b = toIocDiv hp a b + m := by
  simpa using toIocDiv_sub_zsmul' hp a b m

@[simp]
/--
theorem `toIocDiv_sub_natCast_mul'` / 定理 `toIocDiv_sub_natCast_mul'`

English:
theorem toIocDiv_sub_natCast_mul'
  given: (a b : R) (m : Nat)
  proof: mod_cast toIocDiv_sub_intCast_mul' hp a b m

@[simp]

中文:
定理 toIocDiv_sub_natCast_mul'
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIocDiv_sub_intCast_mul' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocDiv_sub_intCast_mul
-/
theorem toIocDiv_sub_natCast_mul' (a b : R) (m : Nat) :
    toIocDiv hp (a - m * p) b = toIocDiv hp a b + m :=
  mod_cast toIocDiv_sub_intCast_mul' hp a b m

@[simp]
/--
theorem `toIocDiv_sub_ofNat_mul'` / 定理 `toIocDiv_sub_ofNat_mul'`

English:
theorem toIocDiv_sub_ofNat_mul'
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIocDiv_sub_natCast_mul' hp a b m

@[simp]

中文:
定理 toIocDiv_sub_of自然数_mul'
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIocDiv_sub_natCast_mul' hp a b m

@[simp]

Depends on / 依赖: toIocDiv_sub_natCast_mul
-/
theorem toIocDiv_sub_ofNat_mul' (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIocDiv hp (a - ofNat(m) * p) b = toIocDiv hp a b + ofNat(m) :=
  toIocDiv_sub_natCast_mul' hp a b m

@[simp]
/--
theorem `toIcoMod_add_intCast_mul` / 定理 `toIcoMod_add_intCast_mul`

English:
theorem toIcoMod_add_intCast_mul
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIcoMod_add_zsmul hp a b m

@[simp]

中文:
定理 toIcoMod_add_intCast_mul
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIcoMod_add_zsmul hp a b m

@[simp]

Depends on / 依赖: toIcoMod_add_zsmul
-/
theorem toIcoMod_add_intCast_mul (a b : R) (m : Int) :
    toIcoMod hp a (b + m * p) = toIcoMod hp a b := by
  simpa using toIcoMod_add_zsmul hp a b m

@[simp]
/--
theorem `toIcoMod_add_natCast_mul` / 定理 `toIcoMod_add_natCast_mul`

English:
theorem toIcoMod_add_natCast_mul
  given: (a b : R) (m : Nat)
  proof: mod_cast toIcoMod_add_intCast_mul hp a b m

@[simp]

中文:
定理 toIcoMod_add_natCast_mul
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIcoMod_add_intCast_mul hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoMod_add_intCast_mul
-/
theorem toIcoMod_add_natCast_mul (a b : R) (m : Nat) :
    toIcoMod hp a (b + m * p) = toIcoMod hp a b :=
  mod_cast toIcoMod_add_intCast_mul hp a b m

@[simp]
/--
theorem `toIcoMod_add_ofNat_mul` / 定理 `toIcoMod_add_ofNat_mul`

English:
theorem toIcoMod_add_ofNat_mul
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: mod_cast toIcoMod_add_intCast_mul hp a b m

@[simp]

中文:
定理 toIcoMod_add_of自然数_mul
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: mod_cast toIcoMod_add_intCast_mul hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoMod_add_intCast_mul
-/
theorem toIcoMod_add_ofNat_mul (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIcoMod hp a (b + ofNat(m) * p) = toIcoMod hp a b :=
  mod_cast toIcoMod_add_intCast_mul hp a b m

@[simp]
/--
theorem `toIcoMod_add_intCast_mul'` / 定理 `toIcoMod_add_intCast_mul'`

English:
theorem toIcoMod_add_intCast_mul'
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIcoMod_add_zsmul' hp a b m

@[simp]

中文:
定理 toIcoMod_add_intCast_mul'
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIcoMod_add_zsmul' hp a b m

@[simp]

Depends on / 依赖: toIcoMod_add_zsmul
-/
theorem toIcoMod_add_intCast_mul' (a b : R) (m : Int) :
    toIcoMod hp (a + m * p) b = toIcoMod hp a b + m * p := by
  simpa using toIcoMod_add_zsmul' hp a b m

@[simp]
/--
theorem `toIcoMod_add_natCast_mul'` / 定理 `toIcoMod_add_natCast_mul'`

English:
theorem toIcoMod_add_natCast_mul'
  given: (a b : R) (m : Nat)
  proof: mod_cast toIcoMod_add_intCast_mul' hp a b m

@[simp]

中文:
定理 toIcoMod_add_natCast_mul'
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIcoMod_add_intCast_mul' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoMod_add_intCast_mul
-/
theorem toIcoMod_add_natCast_mul' (a b : R) (m : Nat) :
    toIcoMod hp (a + m * p) b = toIcoMod hp a b + m * p :=
  mod_cast toIcoMod_add_intCast_mul' hp a b m

@[simp]
/--
theorem `toIcoMod_add_ofNat_mul'` / 定理 `toIcoMod_add_ofNat_mul'`

English:
theorem toIcoMod_add_ofNat_mul'
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIcoMod_add_natCast_mul' hp a b m

@[simp]

中文:
定理 toIcoMod_add_of自然数_mul'
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIcoMod_add_natCast_mul' hp a b m

@[simp]

Depends on / 依赖: toIcoMod_add_natCast_mul
-/
theorem toIcoMod_add_ofNat_mul' (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIcoMod hp (a + ofNat(m) * p) b = toIcoMod hp a b + ofNat(m) * p :=
  toIcoMod_add_natCast_mul' hp a b m

@[simp]
/--
theorem `toIocMod_add_intCast_mul` / 定理 `toIocMod_add_intCast_mul`

English:
theorem toIocMod_add_intCast_mul
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIocMod_add_zsmul hp a b m

@[simp]

中文:
定理 toIocMod_add_intCast_mul
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIocMod_add_zsmul hp a b m

@[simp]

Depends on / 依赖: toIocMod_add_zsmul
-/
theorem toIocMod_add_intCast_mul (a b : R) (m : Int) :
    toIocMod hp a (b + m * p) = toIocMod hp a b := by
  simpa using toIocMod_add_zsmul hp a b m

@[simp]
/--
theorem `toIocMod_add_natCast_mul` / 定理 `toIocMod_add_natCast_mul`

English:
theorem toIocMod_add_natCast_mul
  given: (a b : R) (m : Nat)
  proof: mod_cast toIocMod_add_intCast_mul hp a b m

@[simp]

中文:
定理 toIocMod_add_natCast_mul
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIocMod_add_intCast_mul hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocMod_add_intCast_mul
-/
theorem toIocMod_add_natCast_mul (a b : R) (m : Nat) :
    toIocMod hp a (b + m * p) = toIocMod hp a b :=
  mod_cast toIocMod_add_intCast_mul hp a b m

@[simp]
/--
theorem `toIocMod_add_ofNat_mul` / 定理 `toIocMod_add_ofNat_mul`

English:
theorem toIocMod_add_ofNat_mul
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIocMod_add_natCast_mul hp a b m

@[simp]

中文:
定理 toIocMod_add_of自然数_mul
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIocMod_add_natCast_mul hp a b m

@[simp]

Depends on / 依赖: toIocMod_add_natCast_mul
-/
theorem toIocMod_add_ofNat_mul (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIocMod hp a (b + ofNat(m) * p) = toIocMod hp a b :=
  toIocMod_add_natCast_mul hp a b m

@[simp]
/--
theorem `toIocMod_add_intCast_mul'` / 定理 `toIocMod_add_intCast_mul'`

English:
theorem toIocMod_add_intCast_mul'
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIocMod_add_zsmul' hp a b m

@[simp]

中文:
定理 toIocMod_add_intCast_mul'
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIocMod_add_zsmul' hp a b m

@[simp]

Depends on / 依赖: toIocMod_add_zsmul
-/
theorem toIocMod_add_intCast_mul' (a b : R) (m : Int) :
    toIocMod hp (a + m * p) b = toIocMod hp a b + m * p := by
  simpa using toIocMod_add_zsmul' hp a b m

@[simp]
/--
theorem `toIocMod_add_natCast_mul'` / 定理 `toIocMod_add_natCast_mul'`

English:
theorem toIocMod_add_natCast_mul'
  given: (a b : R) (m : Nat)
  proof: mod_cast toIocMod_add_intCast_mul' hp a b m

@[simp]

中文:
定理 toIocMod_add_natCast_mul'
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIocMod_add_intCast_mul' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocMod_add_intCast_mul
-/
theorem toIocMod_add_natCast_mul' (a b : R) (m : Nat) :
    toIocMod hp (a + m * p) b = toIocMod hp a b + m * p :=
  mod_cast toIocMod_add_intCast_mul' hp a b m

@[simp]
/--
theorem `toIocMod_add_ofNat_mul'` / 定理 `toIocMod_add_ofNat_mul'`

English:
theorem toIocMod_add_ofNat_mul'
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIocMod_add_natCast_mul' hp a b m

@[simp]

中文:
定理 toIocMod_add_of自然数_mul'
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIocMod_add_natCast_mul' hp a b m

@[simp]

Depends on / 依赖: toIocMod_add_natCast_mul
-/
theorem toIocMod_add_ofNat_mul' (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIocMod hp (a + ofNat(m) * p) b = toIocMod hp a b + ofNat(m) * p :=
  toIocMod_add_natCast_mul' hp a b m

@[simp]
/--
theorem `toIcoMod_intCast_mul_add` / 定理 `toIcoMod_intCast_mul_add`

English:
theorem toIcoMod_intCast_mul_add
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIcoMod_zsmul_add hp a b m

@[simp]

中文:
定理 toIcoMod_intCast_mul_add
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIcoMod_zsmul_add hp a b m

@[simp]

Depends on / 依赖: toIcoMod_zsmul_add
-/
theorem toIcoMod_intCast_mul_add (a b : R) (m : Int) :
    toIcoMod hp a (m * p + b) = toIcoMod hp a b := by
  simpa using toIcoMod_zsmul_add hp a b m

@[simp]
/--
theorem `toIcoMod_natCast_mul_add` / 定理 `toIcoMod_natCast_mul_add`

English:
theorem toIcoMod_natCast_mul_add
  given: (a b : R) (m : Nat)
  proof: mod_cast toIcoMod_intCast_mul_add hp a b m

@[simp]

中文:
定理 toIcoMod_natCast_mul_add
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIcoMod_intCast_mul_add hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoMod_intCast_mul_add
-/
theorem toIcoMod_natCast_mul_add (a b : R) (m : Nat) :
    toIcoMod hp a (m * p + b) = toIcoMod hp a b :=
  mod_cast toIcoMod_intCast_mul_add hp a b m

@[simp]
/--
theorem `toIcoMod_ofNat_mul_add` / 定理 `toIcoMod_ofNat_mul_add`

English:
theorem toIcoMod_ofNat_mul_add
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIcoMod_natCast_mul_add hp a b m

@[simp]

中文:
定理 toIcoMod_of自然数_mul_add
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIcoMod_natCast_mul_add hp a b m

@[simp]

Depends on / 依赖: toIcoMod_natCast_mul_add
-/
theorem toIcoMod_ofNat_mul_add (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIcoMod hp a (ofNat(m) * p + b) = toIcoMod hp a b :=
  toIcoMod_natCast_mul_add hp a b m

@[simp]
/--
theorem `toIcoMod_intCast_mul_add'` / 定理 `toIcoMod_intCast_mul_add'`

English:
theorem toIcoMod_intCast_mul_add'
  given: (a b : R) (m : Int)
  proof: by
  rw [add_comm]; rw [toIcoMod_add_intCast_mul']; rw [add_comm]

@[simp]

中文:
定理 toIcoMod_intCast_mul_add'
  条件: (a b : R) (m : 整数)
  证明: by
  rw [add_comm]; rw [toIcoMod_add_intCast_mul']; rw [add_comm]

@[simp]

Depends on / 依赖: add_comm, toIcoMod_add_intCast_mul
-/
theorem toIcoMod_intCast_mul_add' (a b : R) (m : Int) :
    toIcoMod hp (m * p + a) b = m * p + toIcoMod hp a b := by
  rw [add_comm]; rw [toIcoMod_add_intCast_mul']; rw [add_comm]

@[simp]
/--
theorem `toIcoMod_natCast_mul_add'` / 定理 `toIcoMod_natCast_mul_add'`

English:
theorem toIcoMod_natCast_mul_add'
  given: (a b : R) (m : Nat)
  proof: mod_cast toIcoMod_intCast_mul_add' hp a b m

@[simp]

中文:
定理 toIcoMod_natCast_mul_add'
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIcoMod_intCast_mul_add' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoMod_intCast_mul_add
-/
theorem toIcoMod_natCast_mul_add' (a b : R) (m : Nat) :
    toIcoMod hp (m * p + a) b = m * p + toIcoMod hp a b :=
  mod_cast toIcoMod_intCast_mul_add' hp a b m

@[simp]
/--
theorem `toIcoMod_ofNat_mul_add'` / 定理 `toIcoMod_ofNat_mul_add'`

English:
theorem toIcoMod_ofNat_mul_add'
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIcoMod_natCast_mul_add' hp a b m

@[simp]

中文:
定理 toIcoMod_of自然数_mul_add'
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIcoMod_natCast_mul_add' hp a b m

@[simp]

Depends on / 依赖: toIcoMod_natCast_mul_add
-/
theorem toIcoMod_ofNat_mul_add' (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIcoMod hp (ofNat(m) * p + a) b = ofNat(m) * p + toIcoMod hp a b :=
  toIcoMod_natCast_mul_add' hp a b m

@[simp]
/--
theorem `toIocMod_intCast_mul_add` / 定理 `toIocMod_intCast_mul_add`

English:
theorem toIocMod_intCast_mul_add
  given: (a b : R) (m : Int)
  proof: by
  rw [add_comm]; rw [toIocMod_add_intCast_mul]

@[simp]

中文:
定理 toIocMod_intCast_mul_add
  条件: (a b : R) (m : 整数)
  证明: by
  rw [add_comm]; rw [toIocMod_add_intCast_mul]

@[simp]

Depends on / 依赖: add_comm, toIocMod_add_intCast_mul
-/
theorem toIocMod_intCast_mul_add (a b : R) (m : Int) :
    toIocMod hp a (m * p + b) = toIocMod hp a b := by
  rw [add_comm]; rw [toIocMod_add_intCast_mul]

@[simp]
/--
theorem `toIocMod_natCast_mul_add` / 定理 `toIocMod_natCast_mul_add`

English:
theorem toIocMod_natCast_mul_add
  given: (a b : R) (m : Nat)
  proof: mod_cast toIocMod_intCast_mul_add hp a b m

@[simp]

中文:
定理 toIocMod_natCast_mul_add
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIocMod_intCast_mul_add hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocMod_intCast_mul_add
-/
theorem toIocMod_natCast_mul_add (a b : R) (m : Nat) :
    toIocMod hp a (m * p + b) = toIocMod hp a b :=
  mod_cast toIocMod_intCast_mul_add hp a b m

@[simp]
/--
theorem `toIocMod_ofNat_mul_add` / 定理 `toIocMod_ofNat_mul_add`

English:
theorem toIocMod_ofNat_mul_add
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIocMod_natCast_mul_add hp a b m

@[simp]

中文:
定理 toIocMod_of自然数_mul_add
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIocMod_natCast_mul_add hp a b m

@[simp]

Depends on / 依赖: toIocMod_natCast_mul_add
-/
theorem toIocMod_ofNat_mul_add (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIocMod hp a (ofNat(m) * p + b) = toIocMod hp a b :=
  toIocMod_natCast_mul_add hp a b m

@[simp]
/--
theorem `toIocMod_intCast_mul_add'` / 定理 `toIocMod_intCast_mul_add'`

English:
theorem toIocMod_intCast_mul_add'
  given: (a b : R) (m : Int)
  proof: by
  rw [add_comm]; rw [toIocMod_add_intCast_mul']; rw [add_comm]

@[simp]

中文:
定理 toIocMod_intCast_mul_add'
  条件: (a b : R) (m : 整数)
  证明: by
  rw [add_comm]; rw [toIocMod_add_intCast_mul']; rw [add_comm]

@[simp]

Depends on / 依赖: add_comm, toIocMod_add_intCast_mul
-/
theorem toIocMod_intCast_mul_add' (a b : R) (m : Int) :
    toIocMod hp (m * p + a) b = m * p + toIocMod hp a b := by
  rw [add_comm]; rw [toIocMod_add_intCast_mul']; rw [add_comm]

@[simp]
/--
theorem `toIocMod_natCast_mul_add'` / 定理 `toIocMod_natCast_mul_add'`

English:
theorem toIocMod_natCast_mul_add'
  given: (a b : R) (m : Nat)
  proof: mod_cast toIocMod_intCast_mul_add' hp a b m

@[simp]

中文:
定理 toIocMod_natCast_mul_add'
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIocMod_intCast_mul_add' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocMod_intCast_mul_add
-/
theorem toIocMod_natCast_mul_add' (a b : R) (m : Nat) :
    toIocMod hp (m * p + a) b = m * p + toIocMod hp a b :=
  mod_cast toIocMod_intCast_mul_add' hp a b m

@[simp]
/--
theorem `toIocMod_ofNat_mul_add'` / 定理 `toIocMod_ofNat_mul_add'`

English:
theorem toIocMod_ofNat_mul_add'
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIocMod_natCast_mul_add' hp a b m

@[simp]

中文:
定理 toIocMod_of自然数_mul_add'
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIocMod_natCast_mul_add' hp a b m

@[simp]

Depends on / 依赖: toIocMod_natCast_mul_add
-/
theorem toIocMod_ofNat_mul_add' (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIocMod hp (ofNat(m) * p + a) b = ofNat(m) * p + toIocMod hp a b :=
  toIocMod_natCast_mul_add' hp a b m

@[simp]
/--
theorem `toIcoMod_sub_intCast_mul` / 定理 `toIcoMod_sub_intCast_mul`

English:
theorem toIcoMod_sub_intCast_mul
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIcoMod_sub_zsmul hp a b m

@[simp]

中文:
定理 toIcoMod_sub_intCast_mul
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIcoMod_sub_zsmul hp a b m

@[simp]

Depends on / 依赖: toIcoMod_sub_zsmul
-/
theorem toIcoMod_sub_intCast_mul (a b : R) (m : Int) :
    toIcoMod hp a (b - m * p) = toIcoMod hp a b := by
  simpa using toIcoMod_sub_zsmul hp a b m

@[simp]
/--
theorem `toIcoMod_sub_natCast_mul` / 定理 `toIcoMod_sub_natCast_mul`

English:
theorem toIcoMod_sub_natCast_mul
  given: (a b : R) (m : Nat)
  proof: mod_cast toIcoMod_sub_intCast_mul hp a b m

@[simp]

中文:
定理 toIcoMod_sub_natCast_mul
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIcoMod_sub_intCast_mul hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoMod_sub_intCast_mul
-/
theorem toIcoMod_sub_natCast_mul (a b : R) (m : Nat) :
    toIcoMod hp a (b - m * p) = toIcoMod hp a b :=
  mod_cast toIcoMod_sub_intCast_mul hp a b m

@[simp]
/--
theorem `toIcoMod_sub_ofNat_mul` / 定理 `toIcoMod_sub_ofNat_mul`

English:
theorem toIcoMod_sub_ofNat_mul
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIcoMod_sub_natCast_mul hp a b m

@[simp]

中文:
定理 toIcoMod_sub_of自然数_mul
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIcoMod_sub_natCast_mul hp a b m

@[simp]

Depends on / 依赖: toIcoMod_sub_natCast_mul
-/
theorem toIcoMod_sub_ofNat_mul (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIcoMod hp a (b - ofNat(m) * p) = toIcoMod hp a b :=
  toIcoMod_sub_natCast_mul hp a b m

@[simp]
/--
theorem `toIcoMod_sub_intCast_mul'` / 定理 `toIcoMod_sub_intCast_mul'`

English:
theorem toIcoMod_sub_intCast_mul'
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIcoMod_sub_zsmul' hp a b m

@[simp]

中文:
定理 toIcoMod_sub_intCast_mul'
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIcoMod_sub_zsmul' hp a b m

@[simp]

Depends on / 依赖: toIcoMod_sub_zsmul
-/
theorem toIcoMod_sub_intCast_mul' (a b : R) (m : Int) :
    toIcoMod hp (a - m * p) b = toIcoMod hp a b - m * p := by
  simpa using toIcoMod_sub_zsmul' hp a b m

@[simp]
/--
theorem `toIcoMod_sub_natCast_mul'` / 定理 `toIcoMod_sub_natCast_mul'`

English:
theorem toIcoMod_sub_natCast_mul'
  given: (a b : R) (m : Nat)
  proof: mod_cast toIcoMod_sub_intCast_mul' hp a b m

@[simp]

中文:
定理 toIcoMod_sub_natCast_mul'
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIcoMod_sub_intCast_mul' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIcoMod_sub_intCast_mul
-/
theorem toIcoMod_sub_natCast_mul' (a b : R) (m : Nat) :
    toIcoMod hp (a - m * p) b = toIcoMod hp a b - m * p :=
  mod_cast toIcoMod_sub_intCast_mul' hp a b m

@[simp]
/--
theorem `toIcoMod_sub_ofNat_mul'` / 定理 `toIcoMod_sub_ofNat_mul'`

English:
theorem toIcoMod_sub_ofNat_mul'
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIcoMod_sub_natCast_mul' hp a b m

@[simp]

中文:
定理 toIcoMod_sub_of自然数_mul'
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIcoMod_sub_natCast_mul' hp a b m

@[simp]

Depends on / 依赖: toIcoMod_sub_natCast_mul
-/
theorem toIcoMod_sub_ofNat_mul' (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIcoMod hp (a - ofNat(m) * p) b = toIcoMod hp a b - ofNat(m) * p :=
  toIcoMod_sub_natCast_mul' hp a b m

@[simp]
/--
theorem `toIocMod_sub_intCast_mul` / 定理 `toIocMod_sub_intCast_mul`

English:
theorem toIocMod_sub_intCast_mul
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIocMod_sub_zsmul hp a b m

@[simp]

中文:
定理 toIocMod_sub_intCast_mul
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIocMod_sub_zsmul hp a b m

@[simp]

Depends on / 依赖: toIocMod_sub_zsmul
-/
theorem toIocMod_sub_intCast_mul (a b : R) (m : Int) :
    toIocMod hp a (b - m * p) = toIocMod hp a b := by
  simpa using toIocMod_sub_zsmul hp a b m

@[simp]
/--
theorem `toIocMod_sub_natCast_mul` / 定理 `toIocMod_sub_natCast_mul`

English:
theorem toIocMod_sub_natCast_mul
  given: (a b : R) (m : Nat)
  proof: mod_cast toIocMod_sub_intCast_mul hp a b m

@[simp]

中文:
定理 toIocMod_sub_natCast_mul
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIocMod_sub_intCast_mul hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocMod_sub_intCast_mul
-/
theorem toIocMod_sub_natCast_mul (a b : R) (m : Nat) :
    toIocMod hp a (b - m * p) = toIocMod hp a b :=
  mod_cast toIocMod_sub_intCast_mul hp a b m

@[simp]
/--
theorem `toIocMod_sub_ofNat_mul` / 定理 `toIocMod_sub_ofNat_mul`

English:
theorem toIocMod_sub_ofNat_mul
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIocMod_sub_natCast_mul hp a b m

@[simp]

中文:
定理 toIocMod_sub_of自然数_mul
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIocMod_sub_natCast_mul hp a b m

@[simp]

Depends on / 依赖: toIocMod_sub_natCast_mul
-/
theorem toIocMod_sub_ofNat_mul (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIocMod hp a (b - ofNat(m) * p) = toIocMod hp a b :=
  toIocMod_sub_natCast_mul hp a b m

@[simp]
/--
theorem `toIocMod_sub_intCast_mul'` / 定理 `toIocMod_sub_intCast_mul'`

English:
theorem toIocMod_sub_intCast_mul'
  given: (a b : R) (m : Int)
  proof: by
  simpa using toIocMod_sub_zsmul' hp a b m

@[simp]

中文:
定理 toIocMod_sub_intCast_mul'
  条件: (a b : R) (m : 整数)
  证明: by
  simpa using toIocMod_sub_zsmul' hp a b m

@[simp]

Depends on / 依赖: toIocMod_sub_zsmul
-/
theorem toIocMod_sub_intCast_mul' (a b : R) (m : Int) :
    toIocMod hp (a - m * p) b = toIocMod hp a b - m * p := by
  simpa using toIocMod_sub_zsmul' hp a b m

@[simp]
/--
theorem `toIocMod_sub_natCast_mul'` / 定理 `toIocMod_sub_natCast_mul'`

English:
theorem toIocMod_sub_natCast_mul'
  given: (a b : R) (m : Nat)
  proof: mod_cast toIocMod_sub_intCast_mul' hp a b m

@[simp]

中文:
定理 toIocMod_sub_natCast_mul'
  条件: (a b : R) (m : 自然数)
  证明: mod_cast toIocMod_sub_intCast_mul' hp a b m

@[simp]

Depends on / 依赖: mod_cast, toIocMod_sub_intCast_mul
-/
theorem toIocMod_sub_natCast_mul' (a b : R) (m : Nat) :
    toIocMod hp (a - m * p) b = toIocMod hp a b - m * p :=
  mod_cast toIocMod_sub_intCast_mul' hp a b m

@[simp]
/--
theorem `toIocMod_sub_ofNat_mul'` / 定理 `toIocMod_sub_ofNat_mul'`

English:
theorem toIocMod_sub_ofNat_mul'
  given: (a b : R) (m : Nat) [m.AtLeastTwo]
  proof: toIocMod_sub_natCast_mul' hp a b m

中文:
定理 toIocMod_sub_of自然数_mul'
  条件: (a b : R) (m : 自然数) [m.AtLeastTwo]
  证明: toIocMod_sub_natCast_mul' hp a b m

Depends on / 依赖: toIocMod_sub_natCast_mul
-/
theorem toIocMod_sub_ofNat_mul' (a b : R) (m : Nat) [m.AtLeastTwo] :
    toIocMod hp (a - ofNat(m) * p) b = toIocMod hp a b - ofNat(m) * p :=
  toIocMod_sub_natCast_mul' hp a b m

end Ring

/-!
### Connections to `Int.floor` and `Int.fract`
-/


section LinearOrderedField

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {p : α} (hp : 0 < p)

/--
theorem `toIcoDiv_eq_floor` / 定理 `toIcoDiv_eq_floor`

English:
theorem toIcoDiv_eq_floor
  given: (a b : α)
  statement: toIcoDiv hp a b = ⌊(b - a) / p⌋
  proof: by
  refine toIcoDiv_eq_of_sub_zsmul_mem_Ico hp ?_
  rw [Set.mem_Ico]; rw [zsmul_eq_mul]; rw [← sub_nonneg]; rw [add_comm]; rw [sub_right_comm]; rw [← sub_lt_iff_lt_add]; rw [sub_right_comm _ _ a]
  exact ⟨Int.sub_floor_div_mul_nonneg _ hp, Int.sub_floor_div_mul_lt _ hp⟩

中文:
定理 toIcoDiv_eq_floor
  条件: (a b : α)
  结论: toIcoDiv hp a b = ⌊(b - a) / p⌋
  证明: by
  refine toIcoDiv_eq_of_sub_zsmul_mem_Ico hp ?_
  rw [Set.mem_Ico]; rw [zsmul_eq_mul]; rw [← sub_nonneg]; rw [add_comm]; rw [sub_right_comm]; rw [← sub_lt_iff_lt_add]; rw [sub_right_comm _ _ a]
  exact ⟨Int.sub_floor_div_mul_nonneg _ hp, Int.sub_floor_div_mul_lt _ hp⟩

Depends on / 依赖: Int.sub_floor_div_mul_lt, Int.sub_floor_div_mul_nonneg, Set.mem_Ico, add_comm, mem_Ico, sub_floor_div_mul_lt, sub_floor_div_mul_nonneg, sub_lt_iff_lt_add, sub_nonneg, sub_right_comm, toIcoDiv_eq_of_sub_zsmul_mem_Ico, zsmul_eq_mul
-/
theorem toIcoDiv_eq_floor (a b : α) : toIcoDiv hp a b = ⌊(b - a) / p⌋ := by
  refine toIcoDiv_eq_of_sub_zsmul_mem_Ico hp ?_
  rw [Set.mem_Ico]; rw [zsmul_eq_mul]; rw [← sub_nonneg]; rw [add_comm]; rw [sub_right_comm]; rw [← sub_lt_iff_lt_add]; rw [sub_right_comm _ _ a]
  exact ⟨Int.sub_floor_div_mul_nonneg _ hp, Int.sub_floor_div_mul_lt _ hp⟩

/--
theorem `toIocDiv_eq_neg_floor` / 定理 `toIocDiv_eq_neg_floor`

English:
theorem toIocDiv_eq_neg_floor
  given: (a b : α)
  statement: toIocDiv hp a b = -⌊(a + p - b) / p⌋
  proof: by
  refine toIocDiv_eq_of_sub_zsmul_mem_Ioc hp ?_
  rw [Set.mem_Ioc]; rw [zsmul_eq_mul]; rw [Int.cast_neg]; rw [neg_mul]; rw [sub_neg_eq_add]; rw [← sub_nonneg]; rw [sub_add_eq_sub_sub]
  refine ⟨?_, Int.sub_floor_div_mul_nonneg _ hp⟩
  rw [← add_lt_add_iff_right p]; rw [add_assoc]; rw [add_comm b]

中文:
定理 toIocDiv_eq_neg_floor
  条件: (a b : α)
  结论: toIocDiv hp a b = -⌊(a + p - b) / p⌋
  证明: by
  refine toIocDiv_eq_of_sub_zsmul_mem_Ioc hp ?_
  rw [Set.mem_Ioc]; rw [zsmul_eq_mul]; rw [Int.cast_neg]; rw [neg_mul]; rw [sub_neg_eq_add]; rw [← sub_nonneg]; rw [sub_add_eq_sub_sub]
  refine ⟨?_, Int.sub_floor_div_mul_nonneg _ hp⟩
  rw [← add_lt_add_iff_right p]; rw [add_assoc]; rw [add_comm b]

Depends on / 依赖: Int.cast_neg, Int.sub_floor_div_mul_lt, Int.sub_floor_div_mul_nonneg, Set.mem_Ioc, add_assoc, add_comm, add_lt_add_iff_right, cast_neg, mem_Ioc, neg_mul, sub_add_eq_sub_sub, sub_floor_div_mul_lt, sub_floor_div_mul_nonneg, sub_lt_iff_lt_add, sub_neg_eq_add, sub_nonneg, toIocDiv_eq_of_sub_zsmul_mem_Ioc, zsmul_eq_mul
-/
theorem toIocDiv_eq_neg_floor (a b : α) : toIocDiv hp a b = -⌊(a + p - b) / p⌋ := by
  refine toIocDiv_eq_of_sub_zsmul_mem_Ioc hp ?_
  rw [Set.mem_Ioc]; rw [zsmul_eq_mul]; rw [Int.cast_neg]; rw [neg_mul]; rw [sub_neg_eq_add]; rw [← sub_nonneg]; rw [sub_add_eq_sub_sub]
  refine ⟨?_, Int.sub_floor_div_mul_nonneg _ hp⟩
  rw [← add_lt_add_iff_right p]; rw [add_assoc]; rw [add_comm b]; rw [← sub_lt_iff_lt_add]; rw [add_comm (_ * _)]; rw [←
    sub_lt_iff_lt_add]
  exact Int.sub_floor_div_mul_lt _ hp

/--
theorem `toIcoDiv_zero_one` / 定理 `toIcoDiv_zero_one`

English:
theorem toIcoDiv_zero_one
  given: (b : α)
  statement: toIcoDiv (zero_lt_one' α) 0 b = ⌊b⌋
  proof: by
  simp [toIcoDiv_eq_floor]

中文:
定理 toIcoDiv_zero_one
  条件: (b : α)
  结论: toIcoDiv (zero_lt_one' α) 0 b = ⌊b⌋
  证明: by
  simp [toIcoDiv_eq_floor]

Depends on / 依赖: toIcoDiv_eq_floor
-/
theorem toIcoDiv_zero_one (b : α) : toIcoDiv (zero_lt_one' α) 0 b = ⌊b⌋ := by
  simp [toIcoDiv_eq_floor]

/--
theorem `toIcoMod_eq_add_fract_mul` / 定理 `toIcoMod_eq_add_fract_mul`

English:
theorem toIcoMod_eq_add_fract_mul
  given: (a b : α)
  proof: by
  rw [toIcoMod]; rw [toIcoDiv_eq_floor]; rw [Int.fract]
  simp [field, -Int.self_sub_floor]
  ring

中文:
定理 toIcoMod_eq_add_fract_mul
  条件: (a b : α)
  证明: by
  rw [toIcoMod]; rw [toIcoDiv_eq_floor]; rw [Int.fract]
  simp [field, -Int.self_sub_floor]
  ring

Depends on / 依赖: Int.fract, Int.self_sub_floor, self_sub_floor, toIcoDiv_eq_floor, toIcoMod
-/
theorem toIcoMod_eq_add_fract_mul (a b : α) :
    toIcoMod hp a b = a + Int.fract ((b - a) / p) * p := by
  rw [toIcoMod]; rw [toIcoDiv_eq_floor]; rw [Int.fract]
  simp [field, -Int.self_sub_floor]
  ring

/--
theorem `toIcoMod_eq_fract_mul` / 定理 `toIcoMod_eq_fract_mul`

English:
theorem toIcoMod_eq_fract_mul
  given: (b : α)
  statement: toIcoMod hp 0 b = Int.fract (b / p) * p
  proof: by
  simp [toIcoMod_eq_add_fract_mul]

中文:
定理 toIcoMod_eq_fract_mul
  条件: (b : α)
  结论: toIcoMod hp 0 b = 整数.fract (b / p) * p
  证明: by
  simp [toIcoMod_eq_add_fract_mul]

Depends on / 依赖: toIcoMod_eq_add_fract_mul
-/
theorem toIcoMod_eq_fract_mul (b : α) : toIcoMod hp 0 b = Int.fract (b / p) * p := by
  simp [toIcoMod_eq_add_fract_mul]

/--
theorem `toIocMod_eq_sub_fract_mul` / 定理 `toIocMod_eq_sub_fract_mul`

English:
theorem toIocMod_eq_sub_fract_mul
  given: (a b : α)
  proof: by
  rw [toIocMod]; rw [toIocDiv_eq_neg_floor]; rw [Int.fract]
  simp [field, -Int.self_sub_floor]
  ring

中文:
定理 toIocMod_eq_sub_fract_mul
  条件: (a b : α)
  证明: by
  rw [toIocMod]; rw [toIocDiv_eq_neg_floor]; rw [Int.fract]
  simp [field, -Int.self_sub_floor]
  ring

Depends on / 依赖: Int.fract, Int.self_sub_floor, self_sub_floor, toIocDiv_eq_neg_floor, toIocMod
-/
theorem toIocMod_eq_sub_fract_mul (a b : α) :
    toIocMod hp a b = a + p - Int.fract ((a + p - b) / p) * p := by
  rw [toIocMod]; rw [toIocDiv_eq_neg_floor]; rw [Int.fract]
  simp [field, -Int.self_sub_floor]
  ring

/--
theorem `toIcoMod_zero_one` / 定理 `toIcoMod_zero_one`

English:
theorem toIcoMod_zero_one
  given: (b : α)
  statement: toIcoMod (zero_lt_one' α) 0 b = Int.fract b
  proof: by
  simp [toIcoMod_eq_add_fract_mul]

中文:
定理 toIcoMod_zero_one
  条件: (b : α)
  结论: toIcoMod (zero_lt_one' α) 0 b = 整数.fract b
  证明: by
  simp [toIcoMod_eq_add_fract_mul]

Depends on / 依赖: toIcoMod_eq_add_fract_mul
-/
theorem toIcoMod_zero_one (b : α) : toIcoMod (zero_lt_one' α) 0 b = Int.fract b := by
  simp [toIcoMod_eq_add_fract_mul]

end LinearOrderedField

/-! ### Lemmas about unions of translates of intervals -/


section Union

open Set Int

section LinearOrderedAddCommGroup

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [Archimedean α]
  {p : α} (hp : 0 < p) (a : α)
include hp

/--
theorem `iUnion_Ioc_add_zsmul` / 定理 `iUnion_Ioc_add_zsmul`

English:
theorem iUnion_Ioc_add_zsmul
  statement: ⋃ n : Int, Ioc (a + n • p) (a + (n + 1) • p) = univ
  proof: by
  refine eq_univ_iff_forall.mpr fun b => mem_iUnion.mpr ?_
  rcases sub_toIocDiv_zsmul_mem_Ioc hp a b with ⟨hl, hr⟩
  refine ⟨toIocDiv hp a b, ⟨lt_sub_iff_add_lt.mp hl, ?_⟩⟩
  rw [add_smul]; rw [one_smul]; rw [← add_assoc]
  convert! sub_le_iff_le_add.mp hr using 1; abel

中文:
定理 iUnion_Ioc_add_zsmul
  结论: ⋃ n : 整数, 左开右闭区间 (a + n • p) (a + (n + 1) • p) = univ
  证明: by
  refine eq_univ_iff_forall.mpr fun b => mem_iUnion.mpr ?_
  rcases sub_toIocDiv_zsmul_mem_Ioc hp a b with ⟨hl, hr⟩
  refine ⟨toIocDiv hp a b, ⟨lt_sub_iff_add_lt.mp hl, ?_⟩⟩
  rw [add_smul]; rw [one_smul]; rw [← add_assoc]
  convert! sub_le_iff_le_add.mp hr using 1; abel

Depends on / 依赖: add_assoc, add_smul, convert, eq_univ_iff_forall, eq_univ_iff_forall.mpr, lt_sub_iff_add_lt, lt_sub_iff_add_lt.mp, mem_iUnion, mem_iUnion.mpr, one_smul, sub_le_iff_le_add, sub_le_iff_le_add.mp, sub_toIocDiv_zsmul_mem_Ioc, toIocDiv
-/
theorem iUnion_Ioc_add_zsmul : ⋃ n : Int, Ioc (a + n • p) (a + (n + 1) • p) = univ := by
  refine eq_univ_iff_forall.mpr fun b => mem_iUnion.mpr ?_
  rcases sub_toIocDiv_zsmul_mem_Ioc hp a b with ⟨hl, hr⟩
  refine ⟨toIocDiv hp a b, ⟨lt_sub_iff_add_lt.mp hl, ?_⟩⟩
  rw [add_smul]; rw [one_smul]; rw [← add_assoc]
  convert! sub_le_iff_le_add.mp hr using 1; abel

/--
theorem `iUnion_Ico_add_zsmul` / 定理 `iUnion_Ico_add_zsmul`

English:
theorem iUnion_Ico_add_zsmul
  statement: ⋃ n : Int, Ico (a + n • p) (a + (n + 1) • p) = univ
  proof: by
  refine eq_univ_iff_forall.mpr fun b => mem_iUnion.mpr ?_
  rcases sub_toIcoDiv_zsmul_mem_Ico hp a b with ⟨hl, hr⟩
  refine ⟨toIcoDiv hp a b, ⟨le_sub_iff_add_le.mp hl, ?_⟩⟩
  rw [add_smul]; rw [one_smul]; rw [← add_assoc]
  convert! sub_lt_iff_lt_add.mp hr using 1; abel

中文:
定理 iUnion_Ico_add_zsmul
  结论: ⋃ n : 整数, 左闭右开区间 (a + n • p) (a + (n + 1) • p) = univ
  证明: by
  refine eq_univ_iff_forall.mpr fun b => mem_iUnion.mpr ?_
  rcases sub_toIcoDiv_zsmul_mem_Ico hp a b with ⟨hl, hr⟩
  refine ⟨toIcoDiv hp a b, ⟨le_sub_iff_add_le.mp hl, ?_⟩⟩
  rw [add_smul]; rw [one_smul]; rw [← add_assoc]
  convert! sub_lt_iff_lt_add.mp hr using 1; abel

Depends on / 依赖: add_assoc, add_smul, convert, eq_univ_iff_forall, eq_univ_iff_forall.mpr, le_sub_iff_add_le, le_sub_iff_add_le.mp, mem_iUnion, mem_iUnion.mpr, one_smul, sub_lt_iff_lt_add, sub_lt_iff_lt_add.mp, sub_toIcoDiv_zsmul_mem_Ico, toIcoDiv
-/
theorem iUnion_Ico_add_zsmul : ⋃ n : Int, Ico (a + n • p) (a + (n + 1) • p) = univ := by
  refine eq_univ_iff_forall.mpr fun b => mem_iUnion.mpr ?_
  rcases sub_toIcoDiv_zsmul_mem_Ico hp a b with ⟨hl, hr⟩
  refine ⟨toIcoDiv hp a b, ⟨le_sub_iff_add_le.mp hl, ?_⟩⟩
  rw [add_smul]; rw [one_smul]; rw [← add_assoc]
  convert! sub_lt_iff_lt_add.mp hr using 1; abel

/--
theorem `iUnion_Icc_add_zsmul` / 定理 `iUnion_Icc_add_zsmul`

English:
theorem iUnion_Icc_add_zsmul
  statement: ⋃ n : Int, Icc (a + n • p) (a + (n + 1) • p) = univ
  proof: by
  simpa only [iUnion_Ioc_add_zsmul hp a, univ_subset_iff] using
    iUnion_mono fun n : Int => (Ioc_subset_Icc_self : Ioc (a + n • p) (a + (n + 1) • p) subseteq Icc _ _)

中文:
定理 iUnion_Icc_add_zsmul
  结论: ⋃ n : 整数, 闭区间 (a + n • p) (a + (n + 1) • p) = univ
  证明: by
  simpa only [iUnion_Ioc_add_zsmul hp a, univ_subset_iff] using
    iUnion_mono fun n : Int => (Ioc_subset_Icc_self : Ioc (a + n • p) (a + (n + 1) • p) subseteq Icc _ _)

Depends on / 依赖: Ioc_subset_Icc_self, iUnion_Ioc_add_zsmul, iUnion_mono, subseteq, univ_subset_iff
-/
theorem iUnion_Icc_add_zsmul : ⋃ n : Int, Icc (a + n • p) (a + (n + 1) • p) = univ := by
  simpa only [iUnion_Ioc_add_zsmul hp a, univ_subset_iff] using
    iUnion_mono fun n : Int => (Ioc_subset_Icc_self : Ioc (a + n • p) (a + (n + 1) • p) subseteq Icc _ _)

/--
theorem `iUnion_Ioc_zsmul` / 定理 `iUnion_Ioc_zsmul`

English:
theorem iUnion_Ioc_zsmul
  statement: ⋃ n : Int, Ioc (n • p) ((n + 1) • p) = univ
  proof: by
  simpa only [zero_add] using iUnion_Ioc_add_zsmul hp 0

中文:
定理 iUnion_Ioc_zsmul
  结论: ⋃ n : 整数, 左开右闭区间 (n • p) ((n + 1) • p) = univ
  证明: by
  simpa only [zero_add] using iUnion_Ioc_add_zsmul hp 0

Depends on / 依赖: iUnion_Ioc_add_zsmul, zero_add
-/
theorem iUnion_Ioc_zsmul : ⋃ n : Int, Ioc (n • p) ((n + 1) • p) = univ := by
  simpa only [zero_add] using iUnion_Ioc_add_zsmul hp 0

/--
theorem `iUnion_Ico_zsmul` / 定理 `iUnion_Ico_zsmul`

English:
theorem iUnion_Ico_zsmul
  statement: ⋃ n : Int, Ico (n • p) ((n + 1) • p) = univ
  proof: by
  simpa only [zero_add] using iUnion_Ico_add_zsmul hp 0

中文:
定理 iUnion_Ico_zsmul
  结论: ⋃ n : 整数, 左闭右开区间 (n • p) ((n + 1) • p) = univ
  证明: by
  simpa only [zero_add] using iUnion_Ico_add_zsmul hp 0

Depends on / 依赖: iUnion_Ico_add_zsmul, zero_add
-/
theorem iUnion_Ico_zsmul : ⋃ n : Int, Ico (n • p) ((n + 1) • p) = univ := by
  simpa only [zero_add] using iUnion_Ico_add_zsmul hp 0

/--
theorem `iUnion_Icc_zsmul` / 定理 `iUnion_Icc_zsmul`

English:
theorem iUnion_Icc_zsmul
  statement: ⋃ n : Int, Icc (n • p) ((n + 1) • p) = univ
  proof: by
  simpa only [zero_add] using iUnion_Icc_add_zsmul hp 0

中文:
定理 iUnion_Icc_zsmul
  结论: ⋃ n : 整数, 闭区间 (n • p) ((n + 1) • p) = univ
  证明: by
  simpa only [zero_add] using iUnion_Icc_add_zsmul hp 0

Depends on / 依赖: iUnion_Icc_add_zsmul, zero_add
-/
theorem iUnion_Icc_zsmul : ⋃ n : Int, Icc (n • p) ((n + 1) • p) = univ := by
  simpa only [zero_add] using iUnion_Icc_add_zsmul hp 0

end LinearOrderedAddCommGroup

section LinearOrderedRing

variable {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Archimedean α] (a : α)

/--
theorem `iUnion_Ioc_add_intCast` / 定理 `iUnion_Ioc_add_intCast`

English:
theorem iUnion_Ioc_add_intCast
  statement: ⋃ n : Int, Ioc (a + n) (a + n + 1) = Set.univ
  proof: by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    iUnion_Ioc_add_zsmul zero_lt_one a

中文:
定理 iUnion_Ioc_add_intCast
  结论: ⋃ n : 整数, 左开右闭区间 (a + n) (a + n + 1) = 集合.univ
  证明: by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    iUnion_Ioc_add_zsmul zero_lt_one a

Depends on / 依赖: Int.cast_add, Int.cast_one, add_assoc, cast_add, cast_one, iUnion_Ioc_add_zsmul, zero_lt_one, zsmul_one
-/
theorem iUnion_Ioc_add_intCast : ⋃ n : Int, Ioc (a + n) (a + n + 1) = Set.univ := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    iUnion_Ioc_add_zsmul zero_lt_one a

/--
theorem `iUnion_Ico_add_intCast` / 定理 `iUnion_Ico_add_intCast`

English:
theorem iUnion_Ico_add_intCast
  statement: ⋃ n : Int, Ico (a + n) (a + n + 1) = Set.univ
  proof: by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    iUnion_Ico_add_zsmul zero_lt_one a

中文:
定理 iUnion_Ico_add_intCast
  结论: ⋃ n : 整数, 左闭右开区间 (a + n) (a + n + 1) = 集合.univ
  证明: by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    iUnion_Ico_add_zsmul zero_lt_one a

Depends on / 依赖: Int.cast_add, Int.cast_one, add_assoc, cast_add, cast_one, iUnion_Ico_add_zsmul, zero_lt_one, zsmul_one
-/
theorem iUnion_Ico_add_intCast : ⋃ n : Int, Ico (a + n) (a + n + 1) = Set.univ := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    iUnion_Ico_add_zsmul zero_lt_one a

/--
theorem `iUnion_Icc_add_intCast` / 定理 `iUnion_Icc_add_intCast`

English:
theorem iUnion_Icc_add_intCast
  statement: ⋃ n : Int, Icc (a + n) (a + n + 1) = Set.univ
  proof: by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    iUnion_Icc_add_zsmul zero_lt_one a

中文:
定理 iUnion_Icc_add_intCast
  结论: ⋃ n : 整数, 闭区间 (a + n) (a + n + 1) = 集合.univ
  证明: by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    iUnion_Icc_add_zsmul zero_lt_one a

Depends on / 依赖: Int.cast_add, Int.cast_one, add_assoc, cast_add, cast_one, iUnion_Icc_add_zsmul, zero_lt_one, zsmul_one
-/
theorem iUnion_Icc_add_intCast : ⋃ n : Int, Icc (a + n) (a + n + 1) = Set.univ := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    iUnion_Icc_add_zsmul zero_lt_one a

variable (α)

/--
theorem `iUnion_Ioc_intCast` / 定理 `iUnion_Ioc_intCast`

English:
theorem iUnion_Ioc_intCast
  statement: ⋃ n : Int, Ioc (n : α) (n + 1) = Set.univ
  proof: by
  simpa only [zero_add] using iUnion_Ioc_add_intCast (0 : α)

中文:
定理 iUnion_Ioc_intCast
  结论: ⋃ n : 整数, 左开右闭区间 (n : α) (n + 1) = 集合.univ
  证明: by
  simpa only [zero_add] using iUnion_Ioc_add_intCast (0 : α)

Depends on / 依赖: iUnion_Ioc_add_intCast, zero_add
-/
theorem iUnion_Ioc_intCast : ⋃ n : Int, Ioc (n : α) (n + 1) = Set.univ := by
  simpa only [zero_add] using iUnion_Ioc_add_intCast (0 : α)

/--
theorem `iUnion_Ico_intCast` / 定理 `iUnion_Ico_intCast`

English:
theorem iUnion_Ico_intCast
  statement: ⋃ n : Int, Ico (n : α) (n + 1) = Set.univ
  proof: by
  simpa only [zero_add] using iUnion_Ico_add_intCast (0 : α)

中文:
定理 iUnion_Ico_intCast
  结论: ⋃ n : 整数, 左闭右开区间 (n : α) (n + 1) = 集合.univ
  证明: by
  simpa only [zero_add] using iUnion_Ico_add_intCast (0 : α)

Depends on / 依赖: iUnion_Ico_add_intCast, zero_add
-/
theorem iUnion_Ico_intCast : ⋃ n : Int, Ico (n : α) (n + 1) = Set.univ := by
  simpa only [zero_add] using iUnion_Ico_add_intCast (0 : α)

/--
theorem `iUnion_Icc_intCast` / 定理 `iUnion_Icc_intCast`

English:
theorem iUnion_Icc_intCast
  statement: ⋃ n : Int, Icc (n : α) (n + 1) = Set.univ
  proof: by
  simpa only [zero_add] using iUnion_Icc_add_intCast (0 : α)

中文:
定理 iUnion_Icc_intCast
  结论: ⋃ n : 整数, 闭区间 (n : α) (n + 1) = 集合.univ
  证明: by
  simpa only [zero_add] using iUnion_Icc_add_intCast (0 : α)

Depends on / 依赖: iUnion_Icc_add_intCast, zero_add
-/
theorem iUnion_Icc_intCast : ⋃ n : Int, Icc (n : α) (n + 1) = Set.univ := by
  simpa only [zero_add] using iUnion_Icc_add_intCast (0 : α)

end LinearOrderedRing

end Union
