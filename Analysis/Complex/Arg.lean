/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Rays in the complex numbers

This file links the definition `SameRay ℝ x y` with the equality of arguments of complex numbers,
the usual way this is considered.

## Main statements

* `Complex.sameRay_iff` : Two complex numbers are on the same ray iff one of them is zero, or they
  have the same argument.
* `Complex.abs_add_eq/Complex.abs_sub_eq`: If two nonzero complex numbers have the same argument,
  then the triangle inequality is an equality.

-/

public section


variable {x y : Complex}

namespace Complex

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/--
theorem `sameRay_iff` / 定理 `sameRay_iff`

English:
theorem sameRay_iff
  statement: SameRay Real x y ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg
  proof: by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  rcases eq_or_ne y 0 with (rfl | hy)
  · simp
  simp only [hx, hy, sameRay_iff_norm_smul_eq, arg_eq_arg_iff hx hy]
  simp [field, hx, mul_comm, eq_comm]

中文:
定理 sameRay_iff
  结论: SameRay 实数 x y ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg
  证明: by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  rcases eq_or_ne y 0 with (rfl | hy)
  · simp
  simp only [hx, hy, sameRay_iff_norm_smul_eq, arg_eq_arg_iff hx hy]
  simp [field, hx, mul_comm, eq_comm]

Depends on / 依赖: arg_eq_arg_iff, eq_comm, eq_or_ne, mul_comm, sameRay_iff_norm_smul_eq
-/
theorem sameRay_iff : SameRay Real x y ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  rcases eq_or_ne y 0 with (rfl | hy)
  · simp
  simp only [hx, hy, sameRay_iff_norm_smul_eq, arg_eq_arg_iff hx hy]
  simp [field, hx, mul_comm, eq_comm]

/--
theorem `sameRay_iff_arg_div_eq_zero` / 定理 `sameRay_iff_arg_div_eq_zero`

English:
theorem sameRay_iff_arg_div_eq_zero
  statement: SameRay Real x y ↔ arg (x / y) = 0
  proof: by
  rw [← Real.Angle.toReal_zero]; rw [← arg_coe_angle_eq_iff_eq_toReal]; rw [sameRay_iff]
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  simp [hx, hy, arg_div_coe_angle, sub_eq_zero]

中文:
定理 sameRay_iff_arg_div_eq_zero
  结论: SameRay 实数 x y ↔ arg (x / y) = 0
  证明: by
  rw [← Real.Angle.toReal_zero]; rw [← arg_coe_angle_eq_iff_eq_toReal]; rw [sameRay_iff]
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  simp [hx, hy, arg_div_coe_angle, sub_eq_zero]

Depends on / 依赖: Real.Angle.toReal_zero, arg_coe_angle_eq_iff_eq_toReal, arg_div_coe_angle, sameRay_iff, sub_eq_zero, toReal_zero
-/
theorem sameRay_iff_arg_div_eq_zero : SameRay Real x y ↔ arg (x / y) = 0 := by
  rw [← Real.Angle.toReal_zero]; rw [← arg_coe_angle_eq_iff_eq_toReal]; rw [sameRay_iff]
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  simp [hx, hy, arg_div_coe_angle, sub_eq_zero]

/--
theorem `norm_add_eq_iff` / 定理 `norm_add_eq_iff`

English:
theorem norm_add_eq_iff
  statement: ‖x + y‖ = ‖x‖ + ‖y‖ ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg
  proof: sameRay_iff_norm_add.symm.trans sameRay_iff

中文:
定理 norm_add_eq_iff
  结论: ‖x + y‖ = ‖x‖ + ‖y‖ ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg
  证明: sameRay_iff_norm_add.symm.trans sameRay_iff

Depends on / 依赖: sameRay_iff, sameRay_iff_norm_add, sameRay_iff_norm_add.symm.trans
-/
theorem norm_add_eq_iff : ‖x + y‖ = ‖x‖ + ‖y‖ ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg :=
  sameRay_iff_norm_add.symm.trans sameRay_iff

/--
theorem `norm_sub_eq_iff` / 定理 `norm_sub_eq_iff`

English:
theorem norm_sub_eq_iff
  statement: ‖x - y‖ = |‖x‖ - ‖y‖| ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg
  proof: sameRay_iff_norm_sub.symm.trans sameRay_iff

中文:
定理 norm_sub_eq_iff
  结论: ‖x - y‖ = |‖x‖ - ‖y‖| ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg
  证明: sameRay_iff_norm_sub.symm.trans sameRay_iff

Depends on / 依赖: sameRay_iff, sameRay_iff_norm_sub, sameRay_iff_norm_sub.symm.trans
-/
theorem norm_sub_eq_iff : ‖x - y‖ = |‖x‖ - ‖y‖| ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg :=
  sameRay_iff_norm_sub.symm.trans sameRay_iff

/--
theorem `sameRay_of_arg_eq` / 定理 `sameRay_of_arg_eq`

English:
theorem sameRay_of_arg_eq
  given: (h : x.arg = y.arg)
  statement: SameRay Real x y
  proof: sameRay_iff.mpr Or.inr Or.inr h

中文:
定理 sameRay_of_arg_eq
  条件: (h : x.arg = y.arg)
  结论: SameRay 实数 x y
  证明: sameRay_iff.mpr Or.inr Or.inr h

Depends on / 依赖: Or.inr, sameRay_iff, sameRay_iff.mpr
-/
theorem sameRay_of_arg_eq (h : x.arg = y.arg) : SameRay Real x y :=
sameRay_iff.mpr Or.inr Or.inr h

/--
theorem `norm_add_eq` / 定理 `norm_add_eq`

English:
theorem norm_add_eq
  given: (h : x.arg = y.arg)
  statement: ‖x + y‖ = ‖x‖ + ‖y‖
  proof: (sameRay_of_arg_eq h).norm_add

中文:
定理 norm_add_eq
  条件: (h : x.arg = y.arg)
  结论: ‖x + y‖ = ‖x‖ + ‖y‖
  证明: (sameRay_of_arg_eq h).norm_add

Depends on / 依赖: norm_add, sameRay_of_arg_eq
-/
theorem norm_add_eq (h : x.arg = y.arg) : ‖x + y‖ = ‖x‖ + ‖y‖ :=
  (sameRay_of_arg_eq h).norm_add

/--
theorem `norm_sub_eq` / 定理 `norm_sub_eq`

English:
theorem norm_sub_eq
  given: (h : x.arg = y.arg)
  statement: ‖x - y‖ = ‖‖x‖ - ‖y‖‖
  proof: (sameRay_of_arg_eq h).norm_sub

中文:
定理 norm_sub_eq
  条件: (h : x.arg = y.arg)
  结论: ‖x - y‖ = ‖‖x‖ - ‖y‖‖
  证明: (sameRay_of_arg_eq h).norm_sub

Depends on / 依赖: norm_sub, sameRay_of_arg_eq
-/
theorem norm_sub_eq (h : x.arg = y.arg) : ‖x - y‖ = ‖‖x‖ - ‖y‖‖ :=
  (sameRay_of_arg_eq h).norm_sub

end Complex
