/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Ring.Cast

/-! # Intervals of integers in strict ordered rings

These statements could perhaps be generalized, or there could be other variations provided (e.g.,
for `ℕ` instead of `ℤ`, or a version for locally finite `SuccOrder`s with strictly monotone
functions), but for now these are the ones that have found utility in practice (e.g., for lemmas
about `Real.Angle`).
-/

public section

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/--
lemma `IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo` / 引理 `IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo`

English:
lemma IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo
  proof: by
  simp only [Set.mem_Ioo, mul_lt_mul_iff_right₀ hr, Int.cast_lt] at h
  grind [Int.lt_iff_add_one_le]

中文:
引理 IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo
  证明: by
  simp only [Set.mem_Ioo, mul_lt_mul_iff_right₀ hr, Int.cast_lt] at h
  grind [Int.lt_iff_add_one_le]

Depends on / 依赖: Int.cast_lt, Int.lt_iff_add_one_le, Set.mem_Ioo, cast_lt, lt_iff_add_one_le, mem_Ioo
-/
lemma IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo
    {r : R} (hr : 0 < r) {k m n : Int} (h : r * k in Set.Ioo (r * (m - 1 : Int)) (r * (n + 1 : Int))) :
    k in Finset.Icc m n := by
  simp only [Set.mem_Ioo, mul_lt_mul_iff_right₀ hr, Int.cast_lt] at h
  grind [Int.lt_iff_add_one_le]

/--
lemma `IsStrictOrderedRing.int_eq_of_mul_mem_Ioo` / 引理 `IsStrictOrderedRing.int_eq_of_mul_mem_Ioo`

English:
lemma IsStrictOrderedRing.int_eq_of_mul_mem_Ioo
  proof: by
  simpa using int_mem_Icc_of_mul_mem_Ioo hr h

中文:
引理 IsStrictOrderedRing.int_eq_of_mul_mem_Ioo
  证明: by
  simpa using int_mem_Icc_of_mul_mem_Ioo hr h

Depends on / 依赖: int_mem_Icc_of_mul_mem_Ioo
-/
lemma IsStrictOrderedRing.int_eq_of_mul_mem_Ioo
    {r : R} (hr : 0 < r) {k m : Int} (h : r * k in Set.Ioo (r * (m - 1 : Int)) (r * (m + 1 : Int))) :
    k = m := by
  simpa using int_mem_Icc_of_mul_mem_Ioo hr h
