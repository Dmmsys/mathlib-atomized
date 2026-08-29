/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Integral elements of ℂ

This file proves that `Complex.I` is integral over ℤ and ℚ.
-/

public section

open Polynomial

namespace Complex

/--
theorem `isIntegral_int_I` / 定理 `isIntegral_int_I`

English:
theorem isIntegral_int_I
  statement: IsIntegral Int I
  proof: by
  refine ⟨X ^ 2 + C 1, monic_X_pow_add_C _ two_ne_zero, ?_⟩
  rw [eval₂_add]; rw [eval₂_X_pow]; rw [eval₂_C]; rw [I_sq]; rw [eq_intCast]; rw [Int.cast_one]; rw [neg_add_cancel]

中文:
定理 isIntegral_int_I
  结论: Is整数egral 整数 I
  证明: by
  refine ⟨X ^ 2 + C 1, monic_X_pow_add_C _ two_ne_zero, ?_⟩
  rw [eval₂_add]; rw [eval₂_X_pow]; rw [eval₂_C]; rw [I_sq]; rw [eq_intCast]; rw [Int.cast_one]; rw [neg_add_cancel]

Depends on / 依赖: I_sq, Int.cast_one, cast_one, eq_intCast, monic_X_pow_add_C, neg_add_cancel, two_ne_zero
-/
theorem isIntegral_int_I : IsIntegral Int I := by
  refine ⟨X ^ 2 + C 1, monic_X_pow_add_C _ two_ne_zero, ?_⟩
  rw [eval₂_add]; rw [eval₂_X_pow]; rw [eval₂_C]; rw [I_sq]; rw [eq_intCast]; rw [Int.cast_one]; rw [neg_add_cancel]

/--
theorem `isIntegral_rat_I` / 定理 `isIntegral_rat_I`

English:
theorem isIntegral_rat_I
  statement: IsIntegral Rat I
  proof: isIntegral_int_I.tower_top

中文:
定理 isIntegral_rat_I
  结论: Is整数egral Rat I
  证明: isIntegral_int_I.tower_top

Depends on / 依赖: isIntegral_int_I, isIntegral_int_I.tower_top, tower_top
-/
theorem isIntegral_rat_I : IsIntegral Rat I :=
  isIntegral_int_I.tower_top

end Complex
