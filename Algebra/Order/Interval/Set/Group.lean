/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Logic.Pairwise

/-! ### Lemmas about arithmetic operations and intervals. -/

public section


variable {α : Type*}

namespace Set

section OrderedCommGroup

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {a c d : α}

/-! `inv_mem_Ixx_iff`, `sub_mem_Ixx_iff` -/


@[to_additive]
/--
theorem `inv_mem_Icc_iff` / 定理 `inv_mem_Icc_iff`

English:
theorem inv_mem_Icc_iff
  statement: a⁻¹ in Set.Icc c d ↔ a in Set.Icc d⁻¹ c⁻¹
  proof: and_comm.trans and_congr inv_le' le_inv'

@[to_additive]

中文:
定理 inv_mem_Icc_iff
  结论: a⁻¹ in Set.Icc c d ↔ a in Set.Icc d⁻¹ c⁻¹
  证明: and_comm.trans and_congr inv_le' le_inv'

@[to_additive]

Depends on / 依赖: and_comm, and_comm.trans, and_congr, inv_le, le_inv
-/
theorem inv_mem_Icc_iff : a⁻¹ in Set.Icc c d ↔ a in Set.Icc d⁻¹ c⁻¹ :=
and_comm.trans and_congr inv_le' le_inv'

@[to_additive]
/--
theorem `inv_mem_Ico_iff` / 定理 `inv_mem_Ico_iff`

English:
theorem inv_mem_Ico_iff
  statement: a⁻¹ in Set.Ico c d ↔ a in Set.Ioc d⁻¹ c⁻¹
  proof: and_comm.trans and_congr inv_lt' le_inv'

@[to_additive]

中文:
定理 inv_mem_Ico_iff
  结论: a⁻¹ in Set.Ico c d ↔ a in Set.Ioc d⁻¹ c⁻¹
  证明: and_comm.trans and_congr inv_lt' le_inv'

@[to_additive]

Depends on / 依赖: and_comm, and_comm.trans, and_congr, inv_lt, le_inv
-/
theorem inv_mem_Ico_iff : a⁻¹ in Set.Ico c d ↔ a in Set.Ioc d⁻¹ c⁻¹ :=
and_comm.trans and_congr inv_lt' le_inv'

@[to_additive]
/--
theorem `inv_mem_Ioc_iff` / 定理 `inv_mem_Ioc_iff`

English:
theorem inv_mem_Ioc_iff
  statement: a⁻¹ in Set.Ioc c d ↔ a in Set.Ico d⁻¹ c⁻¹
  proof: and_comm.trans and_congr inv_le' lt_inv'

@[to_additive]

中文:
定理 inv_mem_Ioc_iff
  结论: a⁻¹ in Set.Ioc c d ↔ a in Set.Ico d⁻¹ c⁻¹
  证明: and_comm.trans and_congr inv_le' lt_inv'

@[to_additive]

Depends on / 依赖: and_comm, and_comm.trans, and_congr, inv_le, lt_inv
-/
theorem inv_mem_Ioc_iff : a⁻¹ in Set.Ioc c d ↔ a in Set.Ico d⁻¹ c⁻¹ :=
and_comm.trans and_congr inv_le' lt_inv'

@[to_additive]
/--
theorem `inv_mem_Ioo_iff` / 定理 `inv_mem_Ioo_iff`

English:
theorem inv_mem_Ioo_iff
  statement: a⁻¹ in Set.Ioo c d ↔ a in Set.Ioo d⁻¹ c⁻¹
  proof: and_comm.trans and_congr inv_lt' lt_inv'

中文:
定理 inv_mem_Ioo_iff
  结论: a⁻¹ in Set.Ioo c d ↔ a in Set.Ioo d⁻¹ c⁻¹
  证明: and_comm.trans and_congr inv_lt' lt_inv'

Depends on / 依赖: and_comm, and_comm.trans, and_congr, inv_lt, lt_inv
-/
theorem inv_mem_Ioo_iff : a⁻¹ in Set.Ioo c d ↔ a in Set.Ioo d⁻¹ c⁻¹ :=
and_comm.trans and_congr inv_lt' lt_inv'

end OrderedCommGroup

section OrderedAddCommGroup

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b c d : α}


/--
theorem `add_mem_Icc_iff_left` / 定理 `add_mem_Icc_iff_left`

English:
theorem add_mem_Icc_iff_left
  statement: a + b in Set.Icc c d ↔ a in Set.Icc (c - b) (d - b)
  proof: (and_congr sub_le_iff_le_add le_sub_iff_add_le).symm

中文:
定理 add_mem_Icc_iff_left
  结论: a + b in Set.Icc c d ↔ a in Set.Icc (c - b) (d - b)
  证明: (and_congr sub_le_iff_le_add le_sub_iff_add_le).symm

Depends on / 依赖: and_congr, le_sub_iff_add_le, sub_le_iff_le_add
-/
theorem add_mem_Icc_iff_left : a + b in Set.Icc c d ↔ a in Set.Icc (c - b) (d - b) :=
  (and_congr sub_le_iff_le_add le_sub_iff_add_le).symm

/--
theorem `add_mem_Ico_iff_left` / 定理 `add_mem_Ico_iff_left`

English:
theorem add_mem_Ico_iff_left
  statement: a + b in Set.Ico c d ↔ a in Set.Ico (c - b) (d - b)
  proof: (and_congr sub_le_iff_le_add lt_sub_iff_add_lt).symm

中文:
定理 add_mem_Ico_iff_left
  结论: a + b in Set.Ico c d ↔ a in Set.Ico (c - b) (d - b)
  证明: (and_congr sub_le_iff_le_add lt_sub_iff_add_lt).symm

Depends on / 依赖: and_congr, lt_sub_iff_add_lt, sub_le_iff_le_add
-/
theorem add_mem_Ico_iff_left : a + b in Set.Ico c d ↔ a in Set.Ico (c - b) (d - b) :=
  (and_congr sub_le_iff_le_add lt_sub_iff_add_lt).symm

/--
theorem `add_mem_Ioc_iff_left` / 定理 `add_mem_Ioc_iff_left`

English:
theorem add_mem_Ioc_iff_left
  statement: a + b in Set.Ioc c d ↔ a in Set.Ioc (c - b) (d - b)
  proof: (and_congr sub_lt_iff_lt_add le_sub_iff_add_le).symm

中文:
定理 add_mem_Ioc_iff_left
  结论: a + b in Set.Ioc c d ↔ a in Set.Ioc (c - b) (d - b)
  证明: (and_congr sub_lt_iff_lt_add le_sub_iff_add_le).symm

Depends on / 依赖: and_congr, le_sub_iff_add_le, sub_lt_iff_lt_add
-/
theorem add_mem_Ioc_iff_left : a + b in Set.Ioc c d ↔ a in Set.Ioc (c - b) (d - b) :=
  (and_congr sub_lt_iff_lt_add le_sub_iff_add_le).symm

/--
theorem `add_mem_Ioo_iff_left` / 定理 `add_mem_Ioo_iff_left`

English:
theorem add_mem_Ioo_iff_left
  statement: a + b in Set.Ioo c d ↔ a in Set.Ioo (c - b) (d - b)
  proof: (and_congr sub_lt_iff_lt_add lt_sub_iff_add_lt).symm

中文:
定理 add_mem_Ioo_iff_left
  结论: a + b in Set.Ioo c d ↔ a in Set.Ioo (c - b) (d - b)
  证明: (and_congr sub_lt_iff_lt_add lt_sub_iff_add_lt).symm

Depends on / 依赖: and_congr, lt_sub_iff_add_lt, sub_lt_iff_lt_add
-/
theorem add_mem_Ioo_iff_left : a + b in Set.Ioo c d ↔ a in Set.Ioo (c - b) (d - b) :=
  (and_congr sub_lt_iff_lt_add lt_sub_iff_add_lt).symm


/--
theorem `add_mem_Icc_iff_right` / 定理 `add_mem_Icc_iff_right`

English:
theorem add_mem_Icc_iff_right
  statement: a + b in Set.Icc c d ↔ b in Set.Icc (c - a) (d - a)
  proof: (and_congr sub_le_iff_le_add' le_sub_iff_add_le').symm

中文:
定理 add_mem_Icc_iff_right
  结论: a + b in Set.Icc c d ↔ b in Set.Icc (c - a) (d - a)
  证明: (and_congr sub_le_iff_le_add' le_sub_iff_add_le').symm

Depends on / 依赖: and_congr, le_sub_iff_add_le, sub_le_iff_le_add
-/
theorem add_mem_Icc_iff_right : a + b in Set.Icc c d ↔ b in Set.Icc (c - a) (d - a) :=
  (and_congr sub_le_iff_le_add' le_sub_iff_add_le').symm

/--
theorem `add_mem_Ico_iff_right` / 定理 `add_mem_Ico_iff_right`

English:
theorem add_mem_Ico_iff_right
  statement: a + b in Set.Ico c d ↔ b in Set.Ico (c - a) (d - a)
  proof: (and_congr sub_le_iff_le_add' lt_sub_iff_add_lt').symm

中文:
定理 add_mem_Ico_iff_right
  结论: a + b in Set.Ico c d ↔ b in Set.Ico (c - a) (d - a)
  证明: (and_congr sub_le_iff_le_add' lt_sub_iff_add_lt').symm

Depends on / 依赖: StarOrderedRing, StarOrderedRing.lt_iff, StarOrderedRing.pos_iff, add_smul, and_congr, lt_iff, lt_sub_iff_add_lt, pos_iff, smul_mem_closure_star_mul, smul_ne_zero, sub_le_iff_le_add
-/
theorem add_mem_Ico_iff_right : a + b in Set.Ico c d ↔ b in Set.Ico (c - a) (d - a) :=
  (and_congr sub_le_iff_le_add' lt_sub_iff_add_lt').symm

/--
theorem `add_mem_Ioc_iff_right` / 定理 `add_mem_Ioc_iff_right`

English:
theorem add_mem_Ioc_iff_right
  statement: a + b in Set.Ioc c d ↔ b in Set.Ioc (c - a) (d - a)
  proof: (and_congr sub_lt_iff_lt_add' le_sub_iff_add_le').symm

中文:
定理 add_mem_Ioc_iff_right
  结论: a + b in Set.Ioc c d ↔ b in Set.Ioc (c - a) (d - a)
  证明: (and_congr sub_lt_iff_lt_add' le_sub_iff_add_le').symm

Depends on / 依赖: and_congr, le_sub_iff_add_le, sub_lt_iff_lt_add
-/
theorem add_mem_Ioc_iff_right : a + b in Set.Ioc c d ↔ b in Set.Ioc (c - a) (d - a) :=
  (and_congr sub_lt_iff_lt_add' le_sub_iff_add_le').symm

/--
theorem `add_mem_Ioo_iff_right` / 定理 `add_mem_Ioo_iff_right`

English:
theorem add_mem_Ioo_iff_right
  statement: a + b in Set.Ioo c d ↔ b in Set.Ioo (c - a) (d - a)
  proof: (and_congr sub_lt_iff_lt_add' lt_sub_iff_add_lt').symm

中文:
定理 add_mem_Ioo_iff_right
  结论: a + b in Set.Ioo c d ↔ b in Set.Ioo (c - a) (d - a)
  证明: (and_congr sub_lt_iff_lt_add' lt_sub_iff_add_lt').symm

Depends on / 依赖: FunLike, StarRingHomClass, StarRingHomClass.instOrderHomClass, and_congr, instOrderHomClass, lt_sub_iff_add_lt, sub_lt_iff_lt_add
-/
theorem add_mem_Ioo_iff_right : a + b in Set.Ioo c d ↔ b in Set.Ioo (c - a) (d - a) :=
  (and_congr sub_lt_iff_lt_add' lt_sub_iff_add_lt').symm


/--
theorem `sub_mem_Icc_iff_left` / 定理 `sub_mem_Icc_iff_left`

English:
theorem sub_mem_Icc_iff_left
  statement: a - b in Set.Icc c d ↔ a in Set.Icc (c + b) (d + b)
  proof: and_congr le_sub_iff_add_le sub_le_iff_le_add

中文:
定理 sub_mem_Icc_iff_left
  结论: a - b in Set.Icc c d ↔ a in Set.Icc (c + b) (d + b)
  证明: and_congr le_sub_iff_add_le sub_le_iff_le_add

Depends on / 依赖: EquivLike, StarRingEquivClass, StarRingEquivClass.instOrderIsoClass, and_congr, instOrderIsoClass, le_sub_iff_add_le, sub_le_iff_le_add
-/
theorem sub_mem_Icc_iff_left : a - b in Set.Icc c d ↔ a in Set.Icc (c + b) (d + b) :=
  and_congr le_sub_iff_add_le sub_le_iff_le_add

/--
theorem `sub_mem_Ico_iff_left` / 定理 `sub_mem_Ico_iff_left`

English:
theorem sub_mem_Ico_iff_left
  statement: a - b in Set.Ico c d ↔ a in Set.Ico (c + b) (d + b)
  proof: and_congr le_sub_iff_add_le sub_lt_iff_lt_add

中文:
定理 sub_mem_Ico_iff_left
  结论: a - b in Set.Ico c d ↔ a in Set.Ico (c + b) (d + b)
  证明: and_congr le_sub_iff_add_le sub_lt_iff_lt_add

Depends on / 依赖: and_congr, le_sub_iff_add_le, sub_lt_iff_lt_add
-/
theorem sub_mem_Ico_iff_left : a - b in Set.Ico c d ↔ a in Set.Ico (c + b) (d + b) :=
  and_congr le_sub_iff_add_le sub_lt_iff_lt_add

/--
theorem `sub_mem_Ioc_iff_left` / 定理 `sub_mem_Ioc_iff_left`

English:
theorem sub_mem_Ioc_iff_left
  statement: a - b in Set.Ioc c d ↔ a in Set.Ioc (c + b) (d + b)
  proof: and_congr lt_sub_iff_add_lt sub_le_iff_le_add

中文:
定理 sub_mem_Ioc_iff_left
  结论: a - b in Set.Ioc c d ↔ a in Set.Ioc (c + b) (d + b)
  证明: and_congr lt_sub_iff_add_lt sub_le_iff_le_add

Depends on / 依赖: and_congr, lt_sub_iff_add_lt, sub_le_iff_le_add
-/
theorem sub_mem_Ioc_iff_left : a - b in Set.Ioc c d ↔ a in Set.Ioc (c + b) (d + b) :=
  and_congr lt_sub_iff_add_lt sub_le_iff_le_add

/--
theorem `sub_mem_Ioo_iff_left` / 定理 `sub_mem_Ioo_iff_left`

English:
theorem sub_mem_Ioo_iff_left
  statement: a - b in Set.Ioo c d ↔ a in Set.Ioo (c + b) (d + b)
  proof: and_congr lt_sub_iff_add_lt sub_lt_iff_lt_add

中文:
定理 sub_mem_Ioo_iff_left
  结论: a - b in Set.Ioo c d ↔ a in Set.Ioo (c + b) (d + b)
  证明: and_congr lt_sub_iff_add_lt sub_lt_iff_lt_add

Depends on / 依赖: and_congr, lt_sub_iff_add_lt, sub_lt_iff_lt_add
-/
theorem sub_mem_Ioo_iff_left : a - b in Set.Ioo c d ↔ a in Set.Ioo (c + b) (d + b) :=
  and_congr lt_sub_iff_add_lt sub_lt_iff_lt_add


/--
theorem `sub_mem_Icc_iff_right` / 定理 `sub_mem_Icc_iff_right`

English:
theorem sub_mem_Icc_iff_right
  statement: a - b in Set.Icc c d ↔ b in Set.Icc (a - d) (a - c)
  proof: and_comm.trans and_congr sub_le_comm le_sub_comm

中文:
定理 sub_mem_Icc_iff_right
  结论: a - b in Set.Icc c d ↔ b in Set.Icc (a - d) (a - c)
  证明: and_comm.trans and_congr sub_le_comm le_sub_comm

Depends on / 依赖: and_comm, and_comm.trans, and_congr, le_sub_comm, sub_le_comm
-/
theorem sub_mem_Icc_iff_right : a - b in Set.Icc c d ↔ b in Set.Icc (a - d) (a - c) :=
and_comm.trans and_congr sub_le_comm le_sub_comm

/--
theorem `sub_mem_Ico_iff_right` / 定理 `sub_mem_Ico_iff_right`

English:
theorem sub_mem_Ico_iff_right
  statement: a - b in Set.Ico c d ↔ b in Set.Ioc (a - d) (a - c)
  proof: and_comm.trans and_congr sub_lt_comm le_sub_comm

中文:
定理 sub_mem_Ico_iff_right
  结论: a - b in Set.Ico c d ↔ b in Set.Ioc (a - d) (a - c)
  证明: and_comm.trans and_congr sub_lt_comm le_sub_comm

Depends on / 依赖: and_comm, and_comm.trans, and_congr, le_sub_comm, sub_lt_comm
-/
theorem sub_mem_Ico_iff_right : a - b in Set.Ico c d ↔ b in Set.Ioc (a - d) (a - c) :=
and_comm.trans and_congr sub_lt_comm le_sub_comm

/--
theorem `sub_mem_Ioc_iff_right` / 定理 `sub_mem_Ioc_iff_right`

English:
theorem sub_mem_Ioc_iff_right
  statement: a - b in Set.Ioc c d ↔ b in Set.Ico (a - d) (a - c)
  proof: and_comm.trans and_congr sub_le_comm lt_sub_comm

中文:
定理 sub_mem_Ioc_iff_right
  结论: a - b in Set.Ioc c d ↔ b in Set.Ico (a - d) (a - c)
  证明: and_comm.trans and_congr sub_le_comm lt_sub_comm

Depends on / 依赖: and_comm, and_comm.trans, and_congr, lt_sub_comm, sub_le_comm
-/
theorem sub_mem_Ioc_iff_right : a - b in Set.Ioc c d ↔ b in Set.Ico (a - d) (a - c) :=
and_comm.trans and_congr sub_le_comm lt_sub_comm

/--
theorem `sub_mem_Ioo_iff_right` / 定理 `sub_mem_Ioo_iff_right`

English:
theorem sub_mem_Ioo_iff_right
  statement: a - b in Set.Ioo c d ↔ b in Set.Ioo (a - d) (a - c)
  proof: and_comm.trans and_congr sub_lt_comm lt_sub_comm

中文:
定理 sub_mem_Ioo_iff_right
  结论: a - b in Set.Ioo c d ↔ b in Set.Ioo (a - d) (a - c)
  证明: and_comm.trans and_congr sub_lt_comm lt_sub_comm

Depends on / 依赖: and_comm, and_comm.trans, and_congr, lt_sub_comm, sub_lt_comm
-/
theorem sub_mem_Ioo_iff_right : a - b in Set.Ioo c d ↔ b in Set.Ioo (a - d) (a - c) :=
and_comm.trans and_congr sub_lt_comm lt_sub_comm

-- I think that symmetric intervals deserve attention and API: they arise all the time,
-- for instance when considering metric balls in `ℝ`.
/--
theorem `mem_Icc_iff_abs_le` / 定理 `mem_Icc_iff_abs_le`

English:
theorem mem_Icc_iff_abs_le
  statement: {R : Type*}
  proof: abs_le.trans and_comm.trans and_congr sub_le_comm neg_le_sub_iff_le_add

中文:
定理 mem_Icc_iff_abs_le
  结论: {R : 类型}
  证明: abs_le.trans and_comm.trans and_congr sub_le_comm neg_le_sub_iff_le_add

Depends on / 依赖: abs_le, abs_le.trans, and_comm, and_comm.trans, and_congr, hr.star_eq, neg_le_sub_iff_le_add, star_eq, sub_le_comm
-/
theorem mem_Icc_iff_abs_le {R : Type*}
    [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R] {x y z : R} :
    |x - y| <= z ↔ y in Icc (x - z) (x + z) :=
abs_le.trans and_comm.trans and_congr sub_le_comm neg_le_sub_iff_le_add


/--
theorem `sub_mem_Icc_zero_iff_right` / 定理 `sub_mem_Icc_zero_iff_right`

English:
theorem sub_mem_Icc_zero_iff_right
  statement: b - a in Icc 0 b ↔ a in Icc 0 b
  proof: by
  simp only [sub_mem_Icc_iff_right, sub_self, sub_zero]

中文:
定理 sub_mem_Icc_zero_iff_right
  结论: b - a in Icc 0 b ↔ a in Icc 0 b
  证明: by
  simp only [sub_mem_Icc_iff_right, sub_self, sub_zero]

Depends on / 依赖: sub_mem_Icc_iff_right, sub_self, sub_zero
-/
theorem sub_mem_Icc_zero_iff_right : b - a in Icc 0 b ↔ a in Icc 0 b := by
  simp only [sub_mem_Icc_iff_right, sub_self, sub_zero]

/--
theorem `sub_mem_Ico_zero_iff_right` / 定理 `sub_mem_Ico_zero_iff_right`

English:
theorem sub_mem_Ico_zero_iff_right
  statement: b - a in Ico 0 b ↔ a in Ioc 0 b
  proof: by
  simp only [sub_mem_Ico_iff_right, sub_self, sub_zero]

中文:
定理 sub_mem_Ico_zero_iff_right
  结论: b - a in Ico 0 b ↔ a in Ioc 0 b
  证明: by
  simp only [sub_mem_Ico_iff_right, sub_self, sub_zero]

Depends on / 依赖: sub_mem_Ico_iff_right, sub_self, sub_zero
-/
theorem sub_mem_Ico_zero_iff_right : b - a in Ico 0 b ↔ a in Ioc 0 b := by
  simp only [sub_mem_Ico_iff_right, sub_self, sub_zero]

/--
theorem `sub_mem_Ioc_zero_iff_right` / 定理 `sub_mem_Ioc_zero_iff_right`

English:
theorem sub_mem_Ioc_zero_iff_right
  statement: b - a in Ioc 0 b ↔ a in Ico 0 b
  proof: by
  simp only [sub_mem_Ioc_iff_right, sub_self, sub_zero]

中文:
定理 sub_mem_Ioc_zero_iff_right
  结论: b - a in Ioc 0 b ↔ a in Ico 0 b
  证明: by
  simp only [sub_mem_Ioc_iff_right, sub_self, sub_zero]

Depends on / 依赖: sub_mem_Ioc_iff_right, sub_self, sub_zero
-/
theorem sub_mem_Ioc_zero_iff_right : b - a in Ioc 0 b ↔ a in Ico 0 b := by
  simp only [sub_mem_Ioc_iff_right, sub_self, sub_zero]

/--
theorem `sub_mem_Ioo_zero_iff_right` / 定理 `sub_mem_Ioo_zero_iff_right`

English:
theorem sub_mem_Ioo_zero_iff_right
  statement: b - a in Ioo 0 b ↔ a in Ioo 0 b
  proof: by
  simp only [sub_mem_Ioo_iff_right, sub_self, sub_zero]

中文:
定理 sub_mem_Ioo_zero_iff_right
  结论: b - a in Ioo 0 b ↔ a in Ioo 0 b
  证明: by
  simp only [sub_mem_Ioo_iff_right, sub_self, sub_zero]

Depends on / 依赖: sub_mem_Ioo_iff_right, sub_self, sub_zero
-/
theorem sub_mem_Ioo_zero_iff_right : b - a in Ioo 0 b ↔ a in Ioo 0 b := by
  simp only [sub_mem_Ioo_iff_right, sub_self, sub_zero]

end OrderedAddCommGroup

section LinearOrderedAddCommGroup

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/--
theorem `nonempty_Ico_sdiff` / 定理 `nonempty_Ico_sdiff`

English:
theorem nonempty_Ico_sdiff
  given: {x dx y dy : α} (h : dy < dx) (hx : 0 < dx)
  proof: by
  rcases lt_or_ge x y with h' | h'
  · use x
    simp [*, not_le.2 h']
  · use max x (x + dy)
    simp [*]

中文:
定理 nonempty_Ico_sdiff
  条件: {x dx y dy : α} (h : dy < dx) (hx : 0 < dx)
  证明: by
  rcases lt_or_ge x y with h' | h'
  · use x
    simp [*, not_le.2 h']
  · use max x (x + dy)
    simp [*]

Depends on / 依赖: lt_or_ge, negPart_nonneg, not_le, posPart_nonneg
-/
theorem nonempty_Ico_sdiff {x dx y dy : α} (h : dy < dx) (hx : 0 < dx) :
    Nonempty ↑(Ico x (x + dx) \ Ico y (y + dy)) := by
  rcases lt_or_ge x y with h' | h'
  · use x
    simp [*, not_le.2 h']
  · use max x (x + dy)
    simp [*]

end LinearOrderedAddCommGroup

/-! ### Lemmas about disjointness of translates of intervals -/

open scoped Function -- required for scoped `on` notation
section PairwiseDisjoint

section OrderedCommGroup

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b : α)

@[to_additive]
/--
theorem `pairwise_disjoint_Ioc_mul_zpow` / 定理 `pairwise_disjoint_Ioc_mul_zpow`

English:
theorem pairwise_disjoint_Ioc_mul_zpow
  proof: by
  simp +unfoldPartialApp only [Function.onFun]
  simp_rw [Set.disjoint_iff]
  intro m n hmn x hx
  apply hmn
  have hb : 1 < b := by
    have : a * b ^ m < a * b ^ (m + 1) := hx.1.1.trans_le hx.1.2
    rwa [mul_lt_mul_iff_left, ← mul_one (b ^ m), zpow_add_one, mul_lt_mul_iff_left] at this
  have 

中文:
定理 pairwise_disjoint_Ioc_mul_zpow
  证明: by
  simp +unfoldPartialApp only [Function.onFun]
  simp_rw [Set.disjoint_iff]
  intro m n hmn x hx
  apply hmn
  have hb : 1 < b := by
    have : a * b ^ m < a * b ^ (m + 1) := hx.1.1.trans_le hx.1.2
    rwa [mul_lt_mul_iff_left, ← mul_one (b ^ m), zpow_add_one, mul_lt_mul_iff_left] at this
  have 

Depends on / 依赖: Function, Function.onFun, Int.lt_add_one_iff, Set.disjoint_iff, disjoint_iff, le_antisymm, lt_add_one_iff, mul_lt_mul_iff_left, mul_one, simp_rw, trans_le, unfoldPartialApp, zpow_add_one, zpow_lt_zpow_iff_right
-/
theorem pairwise_disjoint_Ioc_mul_zpow :
    Pairwise (Disjoint on fun n : Int => Ioc (a * b ^ n) (a * b ^ (n + 1))) := by
  simp +unfoldPartialApp only [Function.onFun]
  simp_rw [Set.disjoint_iff]
  intro m n hmn x hx
  apply hmn
  have hb : 1 < b := by
    have : a * b ^ m < a * b ^ (m + 1) := hx.1.1.trans_le hx.1.2
    rwa [mul_lt_mul_iff_left, ← mul_one (b ^ m), zpow_add_one, mul_lt_mul_iff_left] at this
  have i1 := hx.1.1.trans_le hx.2.2
  have i2 := hx.2.1.trans_le hx.1.2
  rw [mul_lt_mul_iff_left]; rw [zpow_lt_zpow_iff_right hb]; rw [Int.lt_add_one_iff] at i1 i2
  exact le_antisymm i1 i2

@[to_additive]
/--
theorem `pairwise_disjoint_Ico_mul_zpow` / 定理 `pairwise_disjoint_Ico_mul_zpow`

English:
theorem pairwise_disjoint_Ico_mul_zpow
  proof: by
  simp +unfoldPartialApp only [Function.onFun]
  simp_rw [Set.disjoint_iff]
  intro m n hmn x hx
  apply hmn
  have hb : 1 < b := by
    have : a * b ^ m < a * b ^ (m + 1) := hx.1.1.trans_lt hx.1.2
    rwa [mul_lt_mul_iff_left, ← mul_one (b ^ m), zpow_add_one, mul_lt_mul_iff_left] at this
  have 

中文:
定理 pairwise_disjoint_Ico_mul_zpow
  证明: by
  simp +unfoldPartialApp only [Function.onFun]
  simp_rw [Set.disjoint_iff]
  intro m n hmn x hx
  apply hmn
  have hb : 1 < b := by
    have : a * b ^ m < a * b ^ (m + 1) := hx.1.1.trans_lt hx.1.2
    rwa [mul_lt_mul_iff_left, ← mul_one (b ^ m), zpow_add_one, mul_lt_mul_iff_left] at this
  have 

Depends on / 依赖: Function, Function.onFun, Int.lt_add_one_iff, Set.disjoint_iff, disjoint_iff, le_antisymm, lt_add_one_iff, mul_lt_mul_iff_left, mul_one, simp_rw, trans_lt, unfoldPartialApp, zpow_add_one, zpow_lt_zpow_iff_right
-/
theorem pairwise_disjoint_Ico_mul_zpow :
    Pairwise (Disjoint on fun n : Int => Ico (a * b ^ n) (a * b ^ (n + 1))) := by
  simp +unfoldPartialApp only [Function.onFun]
  simp_rw [Set.disjoint_iff]
  intro m n hmn x hx
  apply hmn
  have hb : 1 < b := by
    have : a * b ^ m < a * b ^ (m + 1) := hx.1.1.trans_lt hx.1.2
    rwa [mul_lt_mul_iff_left, ← mul_one (b ^ m), zpow_add_one, mul_lt_mul_iff_left] at this
  have i1 := hx.1.1.trans_lt hx.2.2
  have i2 := hx.2.1.trans_lt hx.1.2
  rw [mul_lt_mul_iff_left]; rw [zpow_lt_zpow_iff_right hb]; rw [Int.lt_add_one_iff] at i1 i2
  exact le_antisymm i1 i2

@[to_additive]
/--
theorem `pairwise_disjoint_Ioo_mul_zpow` / 定理 `pairwise_disjoint_Ioo_mul_zpow`

English:
theorem pairwise_disjoint_Ioo_mul_zpow
  proof: fun _ _ hmn =>
  (pairwise_disjoint_Ioc_mul_zpow a b hmn).mono Ioo_subset_Ioc_self Ioo_subset_Ioc_self

@[to_additive]

中文:
定理 pairwise_disjoint_Ioo_mul_zpow
  证明: fun _ _ hmn =>
  (pairwise_disjoint_Ioc_mul_zpow a b hmn).mono Ioo_subset_Ioc_self Ioo_subset_Ioc_self

@[to_additive]
-/
theorem pairwise_disjoint_Ioo_mul_zpow :
    Pairwise (Disjoint on fun n : Int => Ioo (a * b ^ n) (a * b ^ (n + 1))) := fun _ _ hmn =>
  (pairwise_disjoint_Ioc_mul_zpow a b hmn).mono Ioo_subset_Ioc_self Ioo_subset_Ioc_self

@[to_additive]
/--
theorem `pairwise_disjoint_Ioc_zpow` / 定理 `pairwise_disjoint_Ioc_zpow`

English:
theorem pairwise_disjoint_Ioc_zpow
  proof: by
  simpa only [one_mul] using pairwise_disjoint_Ioc_mul_zpow 1 b

@[to_additive]

中文:
定理 pairwise_disjoint_Ioc_zpow
  证明: by
  simpa only [one_mul] using pairwise_disjoint_Ioc_mul_zpow 1 b

@[to_additive]

Depends on / 依赖: one_mul, pairwise_disjoint_Ioc_mul_zpow
-/
theorem pairwise_disjoint_Ioc_zpow :
    Pairwise (Disjoint on fun n : Int => Ioc (b ^ n) (b ^ (n + 1))) := by
  simpa only [one_mul] using pairwise_disjoint_Ioc_mul_zpow 1 b

@[to_additive]
/--
theorem `pairwise_disjoint_Ico_zpow` / 定理 `pairwise_disjoint_Ico_zpow`

English:
theorem pairwise_disjoint_Ico_zpow
  proof: by
  simpa only [one_mul] using pairwise_disjoint_Ico_mul_zpow 1 b

@[to_additive]

中文:
定理 pairwise_disjoint_Ico_zpow
  证明: by
  simpa only [one_mul] using pairwise_disjoint_Ico_mul_zpow 1 b

@[to_additive]

Depends on / 依赖: one_mul, pairwise_disjoint_Ico_mul_zpow
-/
theorem pairwise_disjoint_Ico_zpow :
    Pairwise (Disjoint on fun n : Int => Ico (b ^ n) (b ^ (n + 1))) := by
  simpa only [one_mul] using pairwise_disjoint_Ico_mul_zpow 1 b

@[to_additive]
/--
theorem `pairwise_disjoint_Ioo_zpow` / 定理 `pairwise_disjoint_Ioo_zpow`

English:
theorem pairwise_disjoint_Ioo_zpow
  proof: by
  simpa only [one_mul] using pairwise_disjoint_Ioo_mul_zpow 1 b

中文:
定理 pairwise_disjoint_Ioo_zpow
  证明: by
  simpa only [one_mul] using pairwise_disjoint_Ioo_mul_zpow 1 b

Depends on / 依赖: one_mul, pairwise_disjoint_Ioo_mul_zpow
-/
theorem pairwise_disjoint_Ioo_zpow :
    Pairwise (Disjoint on fun n : Int => Ioo (b ^ n) (b ^ (n + 1))) := by
  simpa only [one_mul] using pairwise_disjoint_Ioo_mul_zpow 1 b

end OrderedCommGroup

section OrderedRing

variable [Ring α] [PartialOrder α] [IsOrderedRing α] (a : α)

/--
theorem `pairwise_disjoint_Ioc_add_intCast` / 定理 `pairwise_disjoint_Ioc_add_intCast`

English:
theorem pairwise_disjoint_Ioc_add_intCast
  proof: by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    pairwise_disjoint_Ioc_add_zsmul a (1 : α)

中文:
定理 pairwise_disjoint_Ioc_add_intCast
  证明: by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    pairwise_disjoint_Ioc_add_zsmul a (1 : α)

Depends on / 依赖: Int.cast_add, Int.cast_one, add_assoc, cast_add, cast_one, pairwise_disjoint_Ioc_add_zsmul, zsmul_one
-/
theorem pairwise_disjoint_Ioc_add_intCast :
    Pairwise (Disjoint on fun n : Int => Ioc (a + n) (a + n + 1)) := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    pairwise_disjoint_Ioc_add_zsmul a (1 : α)

/--
theorem `pairwise_disjoint_Ico_add_intCast` / 定理 `pairwise_disjoint_Ico_add_intCast`

English:
theorem pairwise_disjoint_Ico_add_intCast
  proof: by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    pairwise_disjoint_Ico_add_zsmul a (1 : α)

中文:
定理 pairwise_disjoint_Ico_add_intCast
  证明: by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    pairwise_disjoint_Ico_add_zsmul a (1 : α)

Depends on / 依赖: Int.cast_add, Int.cast_one, add_assoc, cast_add, cast_one, pairwise_disjoint_Ico_add_zsmul, zsmul_one
-/
theorem pairwise_disjoint_Ico_add_intCast :
    Pairwise (Disjoint on fun n : Int => Ico (a + n) (a + n + 1)) := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    pairwise_disjoint_Ico_add_zsmul a (1 : α)

/--
theorem `pairwise_disjoint_Ioo_add_intCast` / 定理 `pairwise_disjoint_Ioo_add_intCast`

English:
theorem pairwise_disjoint_Ioo_add_intCast
  proof: by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    pairwise_disjoint_Ioo_add_zsmul a (1 : α)

中文:
定理 pairwise_disjoint_Ioo_add_intCast
  证明: by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    pairwise_disjoint_Ioo_add_zsmul a (1 : α)

Depends on / 依赖: Int.cast_add, Int.cast_one, add_assoc, cast_add, cast_one, pairwise_disjoint_Ioo_add_zsmul, zsmul_one
-/
theorem pairwise_disjoint_Ioo_add_intCast :
    Pairwise (Disjoint on fun n : Int => Ioo (a + n) (a + n + 1)) := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    pairwise_disjoint_Ioo_add_zsmul a (1 : α)

variable (α)

/--
theorem `pairwise_disjoint_Ico_intCast` / 定理 `pairwise_disjoint_Ico_intCast`

English:
theorem pairwise_disjoint_Ico_intCast
  proof: by
  simpa only [zero_add] using pairwise_disjoint_Ico_add_intCast (0 : α)

中文:
定理 pairwise_disjoint_Ico_intCast
  证明: by
  simpa only [zero_add] using pairwise_disjoint_Ico_add_intCast (0 : α)

Depends on / 依赖: pairwise_disjoint_Ico_add_intCast, zero_add
-/
theorem pairwise_disjoint_Ico_intCast :
    Pairwise (Disjoint on fun n : Int => Ico (n : α) (n + 1)) := by
  simpa only [zero_add] using pairwise_disjoint_Ico_add_intCast (0 : α)

/--
theorem `pairwise_disjoint_Ioo_intCast` / 定理 `pairwise_disjoint_Ioo_intCast`

English:
theorem pairwise_disjoint_Ioo_intCast
  proof: by
  simpa only [zero_add] using pairwise_disjoint_Ioo_add_intCast (0 : α)

中文:
定理 pairwise_disjoint_Ioo_intCast
  证明: by
  simpa only [zero_add] using pairwise_disjoint_Ioo_add_intCast (0 : α)

Depends on / 依赖: pairwise_disjoint_Ioo_add_intCast, zero_add
-/
theorem pairwise_disjoint_Ioo_intCast :
    Pairwise (Disjoint on fun n : Int => Ioo (n : α) (n + 1)) := by
  simpa only [zero_add] using pairwise_disjoint_Ioo_add_intCast (0 : α)

/--
theorem `pairwise_disjoint_Ioc_intCast` / 定理 `pairwise_disjoint_Ioc_intCast`

English:
theorem pairwise_disjoint_Ioc_intCast
  proof: by
  simpa only [zero_add] using pairwise_disjoint_Ioc_add_intCast (0 : α)

中文:
定理 pairwise_disjoint_Ioc_intCast
  证明: by
  simpa only [zero_add] using pairwise_disjoint_Ioc_add_intCast (0 : α)

Depends on / 依赖: pairwise_disjoint_Ioc_add_intCast, zero_add
-/
theorem pairwise_disjoint_Ioc_intCast :
    Pairwise (Disjoint on fun n : Int => Ioc (n : α) (n + 1)) := by
  simpa only [zero_add] using pairwise_disjoint_Ioc_add_intCast (0 : α)

end OrderedRing

end PairwiseDisjoint

end Set
