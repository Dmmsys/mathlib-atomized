/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Membership in intervals via `Int.floor` / `Nat.floor` / `Int.ceil` / `Nat.ceil`

For a `FloorRing` (resp. `FloorSemiring`) `α`, we relate membership of a cast `↑n` in an interval
of `α` to membership of the integer (resp. natural number) `n` in the corresponding interval with
floor/ceil endpoints, for instance `Int.cast_mem_Ioc_iff : ↑n ∈ Set.Ioc a b ↔ n ∈ Set.Ioc ⌊a⌋ ⌊b⌋`.
If the right-hand side set is finite, we express it as `Finset` instead.

In the natural number case, non-negativity hypotheses are required when the `Nat.floor` function
is involved. In the `IsStrictOrderedRing` case, one of these hypotheses can be omitted.
-/

@[expose] public section

namespace Int

variable {α : Type*} [Ring α] [LinearOrder α] [FloorRing α] {a b : α} {n : Int}

/--
lemma `cast_mem_Ioc_iff` / 引理 `cast_mem_Ioc_iff`

English:
lemma cast_mem_Ioc_iff
  statement: ↑n in Set.Ioc a b ↔ n in Finset.Ioc ⌊a⌋ ⌊b⌋
  proof: by
  simp [floor_lt, le_floor]

中文:
引理 cast_mem_Ioc_iff
  结论: ↑n in 集合.左开右闭区间 a b ↔ n in 有限集.左开右闭区间 ⌊a⌋ ⌊b⌋
  证明: by
  simp [floor_lt, le_floor]

Depends on / 依赖: floor_lt, le_floor
-/
lemma cast_mem_Ioc_iff : ↑n in Set.Ioc a b ↔ n in Finset.Ioc ⌊a⌋ ⌊b⌋ := by
  simp [floor_lt, le_floor]

/--
lemma `cast_mem_Ico_iff` / 引理 `cast_mem_Ico_iff`

English:
lemma cast_mem_Ico_iff
  statement: ↑n in Set.Ico a b ↔ n in Finset.Ico ⌈a⌉ ⌈b⌉
  proof: by
  simp [ceil_le, lt_ceil]

中文:
引理 cast_mem_Ico_iff
  结论: ↑n in 集合.左闭右开区间 a b ↔ n in 有限集.左闭右开区间 ⌈a⌉ ⌈b⌉
  证明: by
  simp [ceil_le, lt_ceil]

Depends on / 依赖: ceil_le, lt_ceil
-/
lemma cast_mem_Ico_iff : ↑n in Set.Ico a b ↔ n in Finset.Ico ⌈a⌉ ⌈b⌉ := by
  simp [ceil_le, lt_ceil]

/--
lemma `cast_mem_Icc_iff` / 引理 `cast_mem_Icc_iff`

English:
lemma cast_mem_Icc_iff
  statement: ↑n in Set.Icc a b ↔ n in Finset.Icc ⌈a⌉ ⌊b⌋
  proof: by
  simp [ceil_le, le_floor]

中文:
引理 cast_mem_Icc_iff
  结论: ↑n in 集合.闭区间 a b ↔ n in 有限集.闭区间 ⌈a⌉ ⌊b⌋
  证明: by
  simp [ceil_le, le_floor]

Depends on / 依赖: ceil_le, le_floor
-/
lemma cast_mem_Icc_iff : ↑n in Set.Icc a b ↔ n in Finset.Icc ⌈a⌉ ⌊b⌋ := by
  simp [ceil_le, le_floor]

/--
lemma `cast_mem_Ioo_iff` / 引理 `cast_mem_Ioo_iff`

English:
lemma cast_mem_Ioo_iff
  statement: ↑n in Set.Ioo a b ↔ n in Finset.Ioo ⌊a⌋ ⌈b⌉
  proof: by
  simp [floor_lt, lt_ceil]

中文:
引理 cast_mem_Ioo_iff
  结论: ↑n in 集合.开区间 a b ↔ n in 有限集.开区间 ⌊a⌋ ⌈b⌉
  证明: by
  simp [floor_lt, lt_ceil]

Depends on / 依赖: floor_lt, lt_ceil
-/
lemma cast_mem_Ioo_iff : ↑n in Set.Ioo a b ↔ n in Finset.Ioo ⌊a⌋ ⌈b⌉ := by
  simp [floor_lt, lt_ceil]

/--
lemma `cast_mem_Ioi_iff` / 引理 `cast_mem_Ioi_iff`

English:
lemma cast_mem_Ioi_iff
  statement: ↑n in Set.Ioi a ↔ n in Set.Ioi ⌊a⌋
  proof: by simp [floor_lt]

中文:
引理 cast_mem_Ioi_iff
  结论: ↑n in 集合.左开右无界区间 a ↔ n in 集合.左开右无界区间 ⌊a⌋
  证明: by simp [floor_lt]

Depends on / 依赖: floor_lt
-/
lemma cast_mem_Ioi_iff : ↑n in Set.Ioi a ↔ n in Set.Ioi ⌊a⌋ := by simp [floor_lt]

/--
lemma `cast_mem_Ici_iff` / 引理 `cast_mem_Ici_iff`

English:
lemma cast_mem_Ici_iff
  statement: ↑n in Set.Ici a ↔ n in Set.Ici ⌈a⌉
  proof: by simp [ceil_le]

中文:
引理 cast_mem_Ici_iff
  结论: ↑n in 集合.左闭右无界区间 a ↔ n in 集合.左闭右无界区间 ⌈a⌉
  证明: by simp [ceil_le]

Depends on / 依赖: ceil_le
-/
lemma cast_mem_Ici_iff : ↑n in Set.Ici a ↔ n in Set.Ici ⌈a⌉ := by simp [ceil_le]

/--
lemma `cast_mem_Iic_iff` / 引理 `cast_mem_Iic_iff`

English:
lemma cast_mem_Iic_iff
  statement: ↑n in Set.Iic b ↔ n in Set.Iic ⌊b⌋
  proof: by simp [le_floor]

中文:
引理 cast_mem_Iic_iff
  结论: ↑n in 集合.左无界右闭区间 b ↔ n in 集合.左无界右闭区间 ⌊b⌋
  证明: by simp [le_floor]

Depends on / 依赖: le_floor
-/
lemma cast_mem_Iic_iff : ↑n in Set.Iic b ↔ n in Set.Iic ⌊b⌋ := by simp [le_floor]

/--
lemma `cast_mem_Iio_iff` / 引理 `cast_mem_Iio_iff`

English:
lemma cast_mem_Iio_iff
  statement: ↑n in Set.Iio b ↔ n in Set.Iio ⌈b⌉
  proof: by simp [lt_ceil]

中文:
引理 cast_mem_Iio_iff
  结论: ↑n in 集合.左无界右开区间 b ↔ n in 集合.左无界右开区间 ⌈b⌉
  证明: by simp [lt_ceil]

Depends on / 依赖: lt_ceil
-/
lemma cast_mem_Iio_iff : ↑n in Set.Iio b ↔ n in Set.Iio ⌈b⌉ := by simp [lt_ceil]

end Int

namespace Nat

variable {α : Type*} [Semiring α] [LinearOrder α] [FloorSemiring α] {a b : α} {n : Nat}

/--
lemma `cast_mem_Ioc_iff` / 引理 `cast_mem_Ioc_iff`

English:
lemma cast_mem_Ioc_iff
  given: (ha : 0 <= a) (hb : 0 <= b)
  proof: by simp [floor_lt ha, le_floor_iff hb]

中文:
引理 cast_mem_Ioc_iff
  条件: (ha : 0 <= a) (hb : 0 <= b)
  证明: by simp [floor_lt ha, le_floor_iff hb]

Depends on / 依赖: floor_lt, le_floor_iff
-/
lemma cast_mem_Ioc_iff (ha : 0 <= a) (hb : 0 <= b) :
    ↑n in Set.Ioc a b ↔ n in Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ := by simp [floor_lt ha, le_floor_iff hb]

/--
lemma `cast_mem_Ioc_iff'` / 引理 `cast_mem_Ioc_iff'`

English:
lemma cast_mem_Ioc_iff'
  given: [IsStrictOrderedRing α] (ha : 0 <= a)
  proof: by
  rcases le_or_gt 0 b with hb | hb
  · exact cast_mem_Ioc_iff ha hb
  · grind [floor_of_nonpos hb.le]

中文:
引理 cast_mem_Ioc_iff'
  条件: [是StrictOrdered环 α] (ha : 0 <= a)
  证明: by
  rcases le_or_gt 0 b with hb | hb
  · exact cast_mem_Ioc_iff ha hb
  · grind [floor_of_nonpos hb.le]

Depends on / 依赖: cast_mem_Ioc_iff, floor_of_nonpos, hb.le, le_or_gt
-/
lemma cast_mem_Ioc_iff' [IsStrictOrderedRing α] (ha : 0 <= a) :
    ↑n in Set.Ioc a b ↔ n in Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
  rcases le_or_gt 0 b with hb | hb
  · exact cast_mem_Ioc_iff ha hb
  · grind [floor_of_nonpos hb.le]

/--
lemma `cast_mem_Ico_iff` / 引理 `cast_mem_Ico_iff`

English:
lemma cast_mem_Ico_iff
  statement: ↑n in Set.Ico a b ↔ n in Finset.Ico ⌈a⌉₊ ⌈b⌉₊
  proof: by
  simp [ceil_le, lt_ceil]

中文:
引理 cast_mem_Ico_iff
  结论: ↑n in 集合.左闭右开区间 a b ↔ n in 有限集.左闭右开区间 ⌈a⌉₊ ⌈b⌉₊
  证明: by
  simp [ceil_le, lt_ceil]

Depends on / 依赖: ceil_le, lt_ceil
-/
lemma cast_mem_Ico_iff : ↑n in Set.Ico a b ↔ n in Finset.Ico ⌈a⌉₊ ⌈b⌉₊ := by
  simp [ceil_le, lt_ceil]

/--
lemma `cast_mem_Icc_iff` / 引理 `cast_mem_Icc_iff`

English:
lemma cast_mem_Icc_iff
  given: (hb : 0 <= b)
  statement: ↑n in Set.Icc a b ↔ n in Finset.Icc ⌈a⌉₊ ⌊b⌋₊
  proof: by
  simp [ceil_le, le_floor_iff hb]

中文:
引理 cast_mem_Icc_iff
  条件: (hb : 0 <= b)
  结论: ↑n in 集合.闭区间 a b ↔ n in 有限集.闭区间 ⌈a⌉₊ ⌊b⌋₊
  证明: by
  simp [ceil_le, le_floor_iff hb]

Depends on / 依赖: ceil_le, le_floor_iff
-/
lemma cast_mem_Icc_iff (hb : 0 <= b) : ↑n in Set.Icc a b ↔ n in Finset.Icc ⌈a⌉₊ ⌊b⌋₊ := by
  simp [ceil_le, le_floor_iff hb]

/--
lemma `cast_mem_Ioo_iff` / 引理 `cast_mem_Ioo_iff`

English:
lemma cast_mem_Ioo_iff
  given: (ha : 0 <= a)
  statement: ↑n in Set.Ioo a b ↔ n in Finset.Ioo ⌊a⌋₊ ⌈b⌉₊
  proof: by
  simp [floor_lt ha, lt_ceil]

中文:
引理 cast_mem_Ioo_iff
  条件: (ha : 0 <= a)
  结论: ↑n in 集合.开区间 a b ↔ n in 有限集.开区间 ⌊a⌋₊ ⌈b⌉₊
  证明: by
  simp [floor_lt ha, lt_ceil]

Depends on / 依赖: floor_lt, lt_ceil
-/
lemma cast_mem_Ioo_iff (ha : 0 <= a) : ↑n in Set.Ioo a b ↔ n in Finset.Ioo ⌊a⌋₊ ⌈b⌉₊ := by
  simp [floor_lt ha, lt_ceil]

/--
lemma `cast_mem_Iic_iff` / 引理 `cast_mem_Iic_iff`

English:
lemma cast_mem_Iic_iff
  given: (hb : 0 <= b)
  statement: ↑n in Set.Iic b ↔ n in Finset.Iic ⌊b⌋₊
  proof: by
  simp [le_floor_iff hb]

中文:
引理 cast_mem_Iic_iff
  条件: (hb : 0 <= b)
  结论: ↑n in 集合.左无界右闭区间 b ↔ n in 有限集.左无界右闭区间 ⌊b⌋₊
  证明: by
  simp [le_floor_iff hb]

Depends on / 依赖: le_floor_iff
-/
lemma cast_mem_Iic_iff (hb : 0 <= b) : ↑n in Set.Iic b ↔ n in Finset.Iic ⌊b⌋₊ := by
  simp [le_floor_iff hb]

/--
lemma `cast_mem_Iio_iff` / 引理 `cast_mem_Iio_iff`

English:
lemma cast_mem_Iio_iff
  statement: ↑n in Set.Iio b ↔ n in Finset.Iio ⌈b⌉₊
  proof: by simp [lt_ceil]

中文:
引理 cast_mem_Iio_iff
  结论: ↑n in 集合.左无界右开区间 b ↔ n in 有限集.左无界右开区间 ⌈b⌉₊
  证明: by simp [lt_ceil]

Depends on / 依赖: lt_ceil
-/
lemma cast_mem_Iio_iff : ↑n in Set.Iio b ↔ n in Finset.Iio ⌈b⌉₊ := by simp [lt_ceil]

/--
lemma `cast_mem_Ioi_iff` / 引理 `cast_mem_Ioi_iff`

English:
lemma cast_mem_Ioi_iff
  given: (ha : 0 <= a)
  statement: ↑n in Set.Ioi a ↔ n in Set.Ioi ⌊a⌋₊
  proof: by simp [floor_lt ha]

中文:
引理 cast_mem_Ioi_iff
  条件: (ha : 0 <= a)
  结论: ↑n in 集合.左开右无界区间 a ↔ n in 集合.左开右无界区间 ⌊a⌋₊
  证明: by simp [floor_lt ha]

Depends on / 依赖: floor_lt
-/
lemma cast_mem_Ioi_iff (ha : 0 <= a) : ↑n in Set.Ioi a ↔ n in Set.Ioi ⌊a⌋₊ := by simp [floor_lt ha]

/--
lemma `cast_mem_Ici_iff` / 引理 `cast_mem_Ici_iff`

English:
lemma cast_mem_Ici_iff
  statement: ↑n in Set.Ici a ↔ n in Set.Ici ⌈a⌉₊
  proof: by simp [ceil_le]

中文:
引理 cast_mem_Ici_iff
  结论: ↑n in 集合.左闭右无界区间 a ↔ n in 集合.左闭右无界区间 ⌈a⌉₊
  证明: by simp [ceil_le]

Depends on / 依赖: ceil_le
-/
lemma cast_mem_Ici_iff : ↑n in Set.Ici a ↔ n in Set.Ici ⌈a⌉₊ := by simp [ceil_le]

end Nat
