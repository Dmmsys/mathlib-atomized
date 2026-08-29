/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.Nat
public import Mathlib.Order.UpperLower.Basic

/-!
# Images of intervals under `Nat.cast : ℕ → ℤ`

In this file we prove that the image of each `Set.Ixx` interval under `Nat.cast : ℕ → ℤ`
is the corresponding interval in `ℤ`.
-/

public section

open Set

namespace Nat

@[simp]
/--
theorem `range_cast_int` / 定理 `range_cast_int`

English:
theorem range_cast_int
  statement: range ((↑) : Nat -> Int) = Ici 0
  proof: Subset.antisymm (range_subset_iff.2 Int.natCast_nonneg) CanLift.prf

中文:
定理 range_cast_int
  结论: range ((↑) : 自然数 -> 整数) = 左闭右无界区间 0
  证明: Subset.antisymm (range_subset_iff.2 Int.natCast_nonneg) CanLift.prf

Depends on / 依赖: CanLift, CanLift.prf, Int.natCast_nonneg, Subset, Subset.antisymm, antisymm, natCast_nonneg, range_subset_iff
-/
theorem range_cast_int : range ((↑) : Nat -> Int) = Ici 0 :=
  Subset.antisymm (range_subset_iff.2 Int.natCast_nonneg) CanLift.prf

/--
theorem `image_cast_int_Icc` / 定理 `image_cast_int_Icc`

English:
theorem image_cast_int_Icc
  given: (a b : Nat)
  statement: (↑) '' Icc a b = Icc (a : Int) b
  proof: (castOrderEmbedding (α := Int)).image_Icc (by simp [ordConnected_Ici]) a b

中文:
定理 image_cast_int_Icc
  条件: (a b : 自然数)
  结论: (↑) '' 闭区间 a b = 闭区间 (a : 整数) b
  证明: (castOrderEmbedding (α := Int)).image_Icc (by simp [ordConnected_Ici]) a b

Depends on / 依赖: castOrderEmbedding, image_Icc, ordConnected_Ici
-/
theorem image_cast_int_Icc (a b : Nat) : (↑) '' Icc a b = Icc (a : Int) b :=
  (castOrderEmbedding (α := Int)).image_Icc (by simp [ordConnected_Ici]) a b

/--
theorem `image_cast_int_Ico` / 定理 `image_cast_int_Ico`

English:
theorem image_cast_int_Ico
  given: (a b : Nat)
  statement: (↑) '' Ico a b = Ico (a : Int) b
  proof: (castOrderEmbedding (α := Int)).image_Ico (by simp [ordConnected_Ici]) a b

中文:
定理 image_cast_int_Ico
  条件: (a b : 自然数)
  结论: (↑) '' 左闭右开区间 a b = 左闭右开区间 (a : 整数) b
  证明: (castOrderEmbedding (α := Int)).image_Ico (by simp [ordConnected_Ici]) a b

Depends on / 依赖: castOrderEmbedding, image_Ico, ordConnected_Ici
-/
theorem image_cast_int_Ico (a b : Nat) : (↑) '' Ico a b = Ico (a : Int) b :=
  (castOrderEmbedding (α := Int)).image_Ico (by simp [ordConnected_Ici]) a b

/--
theorem `image_cast_int_Ioc` / 定理 `image_cast_int_Ioc`

English:
theorem image_cast_int_Ioc
  given: (a b : Nat)
  statement: (↑) '' Ioc a b = Ioc (a : Int) b
  proof: (castOrderEmbedding (α := Int)).image_Ioc (by simp [ordConnected_Ici]) a b

中文:
定理 image_cast_int_Ioc
  条件: (a b : 自然数)
  结论: (↑) '' 左开右闭区间 a b = 左开右闭区间 (a : 整数) b
  证明: (castOrderEmbedding (α := Int)).image_Ioc (by simp [ordConnected_Ici]) a b

Depends on / 依赖: castOrderEmbedding, image_Ioc, ordConnected_Ici
-/
theorem image_cast_int_Ioc (a b : Nat) : (↑) '' Ioc a b = Ioc (a : Int) b :=
  (castOrderEmbedding (α := Int)).image_Ioc (by simp [ordConnected_Ici]) a b

/--
theorem `image_cast_int_Ioo` / 定理 `image_cast_int_Ioo`

English:
theorem image_cast_int_Ioo
  given: (a b : Nat)
  statement: (↑) '' Ioo a b = Ioo (a : Int) b
  proof: (castOrderEmbedding (α := Int)).image_Ioo (by simp [ordConnected_Ici]) a b

中文:
定理 image_cast_int_Ioo
  条件: (a b : 自然数)
  结论: (↑) '' 开区间 a b = 开区间 (a : 整数) b
  证明: (castOrderEmbedding (α := Int)).image_Ioo (by simp [ordConnected_Ici]) a b

Depends on / 依赖: castOrderEmbedding, image_Ioo, ordConnected_Ici
-/
theorem image_cast_int_Ioo (a b : Nat) : (↑) '' Ioo a b = Ioo (a : Int) b :=
  (castOrderEmbedding (α := Int)).image_Ioo (by simp [ordConnected_Ici]) a b

/--
theorem `image_cast_int_Iic` / 定理 `image_cast_int_Iic`

English:
theorem image_cast_int_Iic
  given: (a : Nat)
  statement: (↑) '' Iic a = Icc (0 : Int) a
  proof: by
  rw [← Icc_bot]; rw [image_cast_int_Icc]; rfl

中文:
定理 image_cast_int_Iic
  条件: (a : 自然数)
  结论: (↑) '' 左无界右闭区间 a = 闭区间 (0 : 整数) a
  证明: by
  rw [← Icc_bot]; rw [image_cast_int_Icc]; rfl

Depends on / 依赖: Icc_bot, image_cast_int_Icc
-/
theorem image_cast_int_Iic (a : Nat) : (↑) '' Iic a = Icc (0 : Int) a := by
  rw [← Icc_bot]; rw [image_cast_int_Icc]; rfl

/--
theorem `image_cast_int_Iio` / 定理 `image_cast_int_Iio`

English:
theorem image_cast_int_Iio
  given: (a : Nat)
  statement: (↑) '' Iio a = Ico (0 : Int) a
  proof: by
  rw [← Ico_bot]; rw [image_cast_int_Ico]; rfl

中文:
定理 image_cast_int_Iio
  条件: (a : 自然数)
  结论: (↑) '' 左无界右开区间 a = 左闭右开区间 (0 : 整数) a
  证明: by
  rw [← Ico_bot]; rw [image_cast_int_Ico]; rfl

Depends on / 依赖: Ico_bot, image_cast_int_Ico
-/
theorem image_cast_int_Iio (a : Nat) : (↑) '' Iio a = Ico (0 : Int) a := by
  rw [← Ico_bot]; rw [image_cast_int_Ico]; rfl

/--
theorem `image_cast_int_Ici` / 定理 `image_cast_int_Ici`

English:
theorem image_cast_int_Ici
  given: (a : Nat)
  statement: (↑) '' Ici a = Ici (a : Int)
  proof: (castOrderEmbedding (α := Int)).image_Ici (by simp [isUpperSet_Ici]) a

中文:
定理 image_cast_int_Ici
  条件: (a : 自然数)
  结论: (↑) '' 左闭右无界区间 a = 左闭右无界区间 (a : 整数)
  证明: (castOrderEmbedding (α := Int)).image_Ici (by simp [isUpperSet_Ici]) a

Depends on / 依赖: castOrderEmbedding, image_Ici, isUpperSet_Ici
-/
theorem image_cast_int_Ici (a : Nat) : (↑) '' Ici a = Ici (a : Int) :=
  (castOrderEmbedding (α := Int)).image_Ici (by simp [isUpperSet_Ici]) a

/--
theorem `image_cast_int_Ioi` / 定理 `image_cast_int_Ioi`

English:
theorem image_cast_int_Ioi
  given: (a : Nat)
  statement: (↑) '' Ioi a = Ioi (a : Int)
  proof: (castOrderEmbedding (α := Int)).image_Ioi (by simp [isUpperSet_Ici]) a

中文:
定理 image_cast_int_Ioi
  条件: (a : 自然数)
  结论: (↑) '' 左开右无界区间 a = 左开右无界区间 (a : 整数)
  证明: (castOrderEmbedding (α := Int)).image_Ioi (by simp [isUpperSet_Ici]) a

Depends on / 依赖: castOrderEmbedding, image_Ioi, isUpperSet_Ici
-/
theorem image_cast_int_Ioi (a : Nat) : (↑) '' Ioi a = Ioi (a : Int) :=
  (castOrderEmbedding (α := Int)).image_Ioi (by simp [isUpperSet_Ici]) a

end Nat
