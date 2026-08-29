/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Rat.NatSqrt.Defs

/-!
Comparisons between rational approximations to the square root of a natural number
and the real square root.
-/

public section

namespace Nat

/--
theorem `ratSqrt_le_realSqrt` / 定理 `ratSqrt_le_realSqrt`

English:
theorem ratSqrt_le_realSqrt
  given: (x : Nat) {prec : Nat} (h : 0 < prec)
  statement: ratSqrt x prec <= √x
  proof: by
  have := ratSqrt_sq_le (x := x) h
  have : (x.ratSqrt prec ^ 2 : Real) <= ↑x := by norm_cast
  have := Real.sqrt_monotone this
  rwa [Real.sqrt_sq] at this
  simpa only [Rat.cast_nonneg] using ratSqrt_nonneg _ _

中文:
定理 ratSqrt_le_realSqrt
  条件: (x : 自然数) {prec : 自然数} (h : 0 < prec)
  结论: ratSqrt x prec <= √x
  证明: by
  have := ratSqrt_sq_le (x := x) h
  have : (x.ratSqrt prec ^ 2 : Real) <= ↑x := by norm_cast
  have := Real.sqrt_monotone this
  rwa [Real.sqrt_sq] at this
  simpa only [Rat.cast_nonneg] using ratSqrt_nonneg _ _

Depends on / 依赖: Rat.cast_nonneg, Real.sqrt_monotone, Real.sqrt_sq, cast_nonneg, ratSqrt, ratSqrt_nonneg, ratSqrt_sq_le, sqrt_monotone, sqrt_sq, x.ratSqrt
-/
theorem ratSqrt_le_realSqrt (x : Nat) {prec : Nat} (h : 0 < prec) : ratSqrt x prec <= √x := by
  have := ratSqrt_sq_le (x := x) h
  have : (x.ratSqrt prec ^ 2 : Real) <= ↑x := by norm_cast
  have := Real.sqrt_monotone this
  rwa [Real.sqrt_sq] at this
  simpa only [Rat.cast_nonneg] using ratSqrt_nonneg _ _

/--
theorem `realSqrt_lt_ratSqrt_add_inv_prec` / 定理 `realSqrt_lt_ratSqrt_add_inv_prec`

English:
theorem realSqrt_lt_ratSqrt_add_inv_prec
  given: (x : Nat) {prec : Nat} (h : 0 < prec)
  proof: by
  have := lt_ratSqrt_add_inv_prec_sq (x := x) h
  have : (x : Real) < ↑((x.ratSqrt prec + 1 / prec) ^ 2 : Rat) := by norm_cast
  have := Real.sqrt_lt_sqrt (by simp) this
  rw [Rat.cast_pow]; rw [Real.sqrt_sq] at this
  · push_cast at this
    exact this
  · push_cast
    exact add_nonneg (by simp

中文:
定理 realSqrt_lt_ratSqrt_add_inv_prec
  条件: (x : 自然数) {prec : 自然数} (h : 0 < prec)
  证明: by
  have := lt_ratSqrt_add_inv_prec_sq (x := x) h
  have : (x : Real) < ↑((x.ratSqrt prec + 1 / prec) ^ 2 : Rat) := by norm_cast
  have := Real.sqrt_lt_sqrt (by simp) this
  rw [Rat.cast_pow]; rw [Real.sqrt_sq] at this
  · push_cast at this
    exact this
  · push_cast
    exact add_nonneg (by simp

Depends on / 依赖: Rat.cast_pow, Real.sqrt_lt_sqrt, Real.sqrt_sq, add_nonneg, cast_pow, lt_ratSqrt_add_inv_prec_sq, ratSqrt, ratSqrt_nonneg, sqrt_lt_sqrt, sqrt_sq, x.ratSqrt
-/
theorem realSqrt_lt_ratSqrt_add_inv_prec (x : Nat) {prec : Nat} (h : 0 < prec) :
    √x < ratSqrt x prec + 1 / prec := by
  have := lt_ratSqrt_add_inv_prec_sq (x := x) h
  have : (x : Real) < ↑((x.ratSqrt prec + 1 / prec) ^ 2 : Rat) := by norm_cast
  have := Real.sqrt_lt_sqrt (by simp) this
  rw [Rat.cast_pow]; rw [Real.sqrt_sq] at this
  · push_cast at this
    exact this
  · push_cast
    exact add_nonneg (by simpa using ratSqrt_nonneg _ _) (by simp)

/--
theorem `realSqrt_mem_Ico` / 定理 `realSqrt_mem_Ico`

English:
theorem realSqrt_mem_Ico
  given: (x : Nat) {prec : Nat} (h : 0 < prec)
  proof: by
  grind [ratSqrt_le_realSqrt, realSqrt_lt_ratSqrt_add_inv_prec]

#adaptation_note

中文:
定理 realSqrt_mem_Ico
  条件: (x : 自然数) {prec : 自然数} (h : 0 < prec)
  证明: by
  grind [ratSqrt_le_realSqrt, realSqrt_lt_ratSqrt_add_inv_prec]

#adaptation_note

Depends on / 依赖: FinitaryExtensive, Finite, ratSqrt_le_realSqrt, realSqrt_lt_ratSqrt_add_inv_prec
-/
theorem realSqrt_mem_Ico (x : Nat) {prec : Nat} (h : 0 < prec) :
    √x in Set.Ico (ratSqrt x prec : Real) (ratSqrt x prec + 1 / prec : Real) := by
  grind [ratSqrt_le_realSqrt, realSqrt_lt_ratSqrt_add_inv_prec]

#adaptation_note
/--
nightly-2025-09-11
We're investigating changing the `grind` heuristics for selecting patterns.
Under one heuristic, the next proof would fail if we just passed `realSqrt_lt_ratSqrt_add_inv_prec`
to `grind` in the next proof.
So for robustness I'm explicitly setting the pattern here.
-/
local grind_pattern realSqrt_lt_ratSqrt_add_inv_prec => (x.ratSqrt prec : Real)

/--
theorem `ratSqrt_mem_Ioc` / 定理 `ratSqrt_mem_Ioc`

English:
theorem ratSqrt_mem_Ioc
  given: (x : Nat) {prec : Nat} (h : 0 < prec)
  proof: by
  grind [ratSqrt_le_realSqrt]

中文:
定理 ratSqrt_mem_Ioc
  条件: (x : 自然数) {prec : 自然数} (h : 0 < prec)
  证明: by
  grind [ratSqrt_le_realSqrt]

Depends on / 依赖: ratSqrt_le_realSqrt
-/
theorem ratSqrt_mem_Ioc (x : Nat) {prec : Nat} (h : 0 < prec) :
    (ratSqrt x prec : Real) in Set.Ioc (√x - 1 / prec) √x := by
  grind [ratSqrt_le_realSqrt]

end Nat
