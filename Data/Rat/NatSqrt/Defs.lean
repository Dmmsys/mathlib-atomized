/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Tactic.Positivity
public import Mathlib.Algebra.Order.Field.Basic

/-!
Rational approximation of the square root of a natural number.

See also `Mathlib.Analysis.Rat.NatSqrt.Real` for comparisons with the real square root.
-/

@[expose] public section

namespace Nat

/--
Definition of `ratSqrt` / `ratSqrt` 的定义

English:
definition ratSqrt
  signature: (x : Nat) (prec : Nat)
  body: ((x * prec ^ 2).sqrt : Rat) / prec

中文:
定义 ratSqrt
  签名: (x : 自然数) (prec : 自然数)
  定义体: ((x * prec ^ 2).sqrt : Rat) / prec
-/
def ratSqrt (x : Nat) (prec : Nat) : Rat := ((x * prec ^ 2).sqrt : Rat) / prec

/--
theorem `ratSqrt_nonneg` / 定理 `ratSqrt_nonneg`

English:
theorem ratSqrt_nonneg
  given: (x prec : Nat)
  statement: 0 <= ratSqrt x prec
  proof: by
  unfold ratSqrt
  positivity

中文:
定理 ratSqrt_nonneg
  条件: (x prec : 自然数)
  结论: 0 <= ratSqrt x prec
  证明: by
  unfold ratSqrt
  positivity

Depends on / 依赖: ratSqrt
-/
theorem ratSqrt_nonneg (x prec : Nat) : 0 <= ratSqrt x prec := by
  unfold ratSqrt
  positivity

/--
theorem `ratSqrt_sq_le` / 定理 `ratSqrt_sq_le`

English:
theorem ratSqrt_sq_le
  given: (x : Nat) {prec : Nat} (h : 0 < prec)
  statement: (ratSqrt x prec) ^ 2 <= x
  proof: by
  unfold ratSqrt
  rw [div_pow]; rw [div_le_iff₀ (by positivity)]
  norm_cast
  exact sqrt_le' (x * prec ^ 2)

中文:
定理 ratSqrt_sq_le
  条件: (x : 自然数) {prec : 自然数} (h : 0 < prec)
  结论: (ratSqrt x prec) ^ 2 <= x
  证明: by
  unfold ratSqrt
  rw [div_pow]; rw [div_le_iff₀ (by positivity)]
  norm_cast
  exact sqrt_le' (x * prec ^ 2)

Depends on / 依赖: div_pow, ratSqrt, sqrt_le
-/
theorem ratSqrt_sq_le (x : Nat) {prec : Nat} (h : 0 < prec) : (ratSqrt x prec) ^ 2 <= x := by
  unfold ratSqrt
  rw [div_pow]; rw [div_le_iff₀ (by positivity)]
  norm_cast
  exact sqrt_le' (x * prec ^ 2)

/--
theorem `lt_ratSqrt_add_inv_prec_sq` / 定理 `lt_ratSqrt_add_inv_prec_sq`

English:
theorem lt_ratSqrt_add_inv_prec_sq
  given: (x : Nat) {prec : Nat} (h : 0 < prec)
  proof: by
  unfold ratSqrt
  rw [← mul_lt_mul_iff_of_pos_right (a := (prec ^ 2 : Rat)) (by positivity)]
  rw [← mul_pow]; rw [add_mul]
  rw [div_mul_cancel₀]; rw [div_mul_cancel₀]
  · norm_cast
    exact lt_succ_sqrt' (x * prec ^ 2)
  all_goals norm_cast; positivity

中文:
定理 lt_ratSqrt_add_inv_prec_sq
  条件: (x : 自然数) {prec : 自然数} (h : 0 < prec)
  证明: by
  unfold ratSqrt
  rw [← mul_lt_mul_iff_of_pos_right (a := (prec ^ 2 : Rat)) (by positivity)]
  rw [← mul_pow]; rw [add_mul]
  rw [div_mul_cancel₀]; rw [div_mul_cancel₀]
  · norm_cast
    exact lt_succ_sqrt' (x * prec ^ 2)
  all_goals norm_cast; positivity

Depends on / 依赖: add_mul, all_goals, lt_succ_sqrt, mul_lt_mul_iff_of_pos_right, mul_pow, ratSqrt
-/
theorem lt_ratSqrt_add_inv_prec_sq (x : Nat) {prec : Nat} (h : 0 < prec) :
    x < (ratSqrt x prec + 1 / prec) ^ 2 := by
  unfold ratSqrt
  rw [← mul_lt_mul_iff_of_pos_right (a := (prec ^ 2 : Rat)) (by positivity)]
  rw [← mul_pow]; rw [add_mul]
  rw [div_mul_cancel₀]; rw [div_mul_cancel₀]
  · norm_cast
    exact lt_succ_sqrt' (x * prec ^ 2)
  all_goals norm_cast; positivity

end Nat
