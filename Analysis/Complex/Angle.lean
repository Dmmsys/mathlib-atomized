/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Angle between complex numbers

This file relates the Euclidean geometric notion of angle between complex numbers to the argument of
their quotient.

It also shows that the arc and chord distances between two unit complex numbers are equivalent up to
a factor of `π / 2`.

## TODO

Prove the corresponding results for oriented angles.

## Tags

arc-length, arc-distance
-/

public section

open InnerProductGeometry Set
open scoped Real

namespace Complex
variable {a x y : Complex}

/--
lemma `angle_eq_abs_arg` / 引理 `angle_eq_abs_arg`

English:
lemma angle_eq_abs_arg
  given: (hx : x != 0) (hy : y != 0)
  statement: angle x y = |(x / y).arg|
  proof: by
  refine Real.arccos_eq_of_eq_cos (abs_nonneg _) (abs_arg_le_pi _) ?_
  rw [Real.cos_abs]; rw [Complex.cos_arg (div_ne_zero hx hy)]
  simp [div_eq_mul_inv, Complex.normSq_eq_norm_sq]
  field

中文:
引理 angle_eq_abs_arg
  条件: (hx : x != 0) (hy : y != 0)
  结论: angle x y = |(x / y).arg|
  证明: by
  refine Real.arccos_eq_of_eq_cos (abs_nonneg _) (abs_arg_le_pi _) ?_
  rw [Real.cos_abs]; rw [Complex.cos_arg (div_ne_zero hx hy)]
  simp [div_eq_mul_inv, Complex.normSq_eq_norm_sq]
  field

Depends on / 依赖: Complex.cos_arg, Complex.normSq_eq_norm_sq, Real.arccos_eq_of_eq_cos, Real.cos_abs, abs_arg_le_pi, abs_nonneg, arccos_eq_of_eq_cos, cos_abs, cos_arg, div_eq_mul_inv, div_ne_zero, normSq_eq_norm_sq
-/
lemma angle_eq_abs_arg (hx : x != 0) (hy : y != 0) : angle x y = |(x / y).arg| := by
  refine Real.arccos_eq_of_eq_cos (abs_nonneg _) (abs_arg_le_pi _) ?_
  rw [Real.cos_abs]; rw [Complex.cos_arg (div_ne_zero hx hy)]
  simp [div_eq_mul_inv, Complex.normSq_eq_norm_sq]
  field

/--
lemma `angle_one_left` / 引理 `angle_one_left`

English:
lemma angle_one_left
  given: (hy : y != 0)
  statement: angle 1 y = |y.arg|
  proof: by simp [angle_eq_abs_arg, hy]

中文:
引理 angle_one_left
  条件: (hy : y != 0)
  结论: angle 1 y = |y.arg|
  证明: by simp [angle_eq_abs_arg, hy]

Depends on / 依赖: angle_eq_abs_arg
-/
lemma angle_one_left (hy : y != 0) : angle 1 y = |y.arg| := by simp [angle_eq_abs_arg, hy]
/--
lemma `angle_one_right` / 引理 `angle_one_right`

English:
lemma angle_one_right
  given: (hx : x != 0)
  statement: angle x 1 = |x.arg|
  proof: by simp [angle_eq_abs_arg, hx]

中文:
引理 angle_one_right
  条件: (hx : x != 0)
  结论: angle x 1 = |x.arg|
  证明: by simp [angle_eq_abs_arg, hx]

Depends on / 依赖: angle_eq_abs_arg
-/
lemma angle_one_right (hx : x != 0) : angle x 1 = |x.arg| := by simp [angle_eq_abs_arg, hx]

/--
lemma `angle_mul_left` / 引理 `angle_mul_left`

English:
lemma angle_mul_left
  given: (ha : a != 0) (x y : Complex)
  statement: angle (a * x) (a * y) = angle x y
  proof: by
  obtain rfl | hx := eq_or_ne x 0 <;> obtain rfl | hy := eq_or_ne y 0 <;>
    simp [angle_eq_abs_arg, mul_div_mul_left, *]

中文:
引理 angle_mul_left
  条件: (ha : a != 0) (x y : Complex)
  结论: angle (a * x) (a * y) = angle x y
  证明: by
  obtain rfl | hx := eq_or_ne x 0 <;> obtain rfl | hy := eq_or_ne y 0 <;>
    simp [angle_eq_abs_arg, mul_div_mul_left, *]
-/
@[simp] lemma angle_mul_left (ha : a != 0) (x y : Complex) : angle (a * x) (a * y) = angle x y := by
  obtain rfl | hx := eq_or_ne x 0 <;> obtain rfl | hy := eq_or_ne y 0 <;>
    simp [angle_eq_abs_arg, mul_div_mul_left, *]

/--
lemma `angle_mul_right` / 引理 `angle_mul_right`

English:
lemma angle_mul_right
  given: (ha : a != 0) (x y : Complex)
  statement: angle (x * a) (y * a) = angle x y
  proof: by
  simp [mul_comm, angle_mul_left ha]

中文:
引理 angle_mul_right
  条件: (ha : a != 0) (x y : Complex)
  结论: angle (x * a) (y * a) = angle x y
  证明: by
  simp [mul_comm, angle_mul_left ha]
-/
@[simp] lemma angle_mul_right (ha : a != 0) (x y : Complex) : angle (x * a) (y * a) = angle x y := by
  simp [mul_comm, angle_mul_left ha]

/--
lemma `angle_div_left_eq_angle_mul_right` / 引理 `angle_div_left_eq_angle_mul_right`

English:
lemma angle_div_left_eq_angle_mul_right
  given: (a x y : Complex)
  statement: angle (x / a) y = angle x (y * a)
  proof: by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · rw [← angle_mul_right ha, div_mul_cancel₀ _ ha]

中文:
引理 angle_div_left_eq_angle_mul_right
  条件: (a x y : Complex)
  结论: angle (x / a) y = angle x (y * a)
  证明: by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · rw [← angle_mul_right ha, div_mul_cancel₀ _ ha]

Depends on / 依赖: angle_mul_right, eq_or_ne
-/
lemma angle_div_left_eq_angle_mul_right (a x y : Complex) : angle (x / a) y = angle x (y * a) := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · rw [← angle_mul_right ha, div_mul_cancel₀ _ ha]

/--
lemma `angle_div_right_eq_angle_mul_left` / 引理 `angle_div_right_eq_angle_mul_left`

English:
lemma angle_div_right_eq_angle_mul_left
  given: (a x y : Complex)
  statement: angle x (y / a) = angle (x * a) y
  proof: by
  rw [angle_comm]; rw [angle_div_left_eq_angle_mul_right]; rw [angle_comm]

中文:
引理 angle_div_right_eq_angle_mul_left
  条件: (a x y : Complex)
  结论: angle x (y / a) = angle (x * a) y
  证明: by
  rw [angle_comm]; rw [angle_div_left_eq_angle_mul_right]; rw [angle_comm]

Depends on / 依赖: angle_comm, angle_div_left_eq_angle_mul_right
-/
lemma angle_div_right_eq_angle_mul_left (a x y : Complex) : angle x (y / a) = angle (x * a) y := by
  rw [angle_comm]; rw [angle_div_left_eq_angle_mul_right]; rw [angle_comm]

/--
lemma `angle_exp_exp` / 引理 `angle_exp_exp`

English:
lemma angle_exp_exp
  given: (x y : Real)
  proof: by
  simp_rw [angle_eq_abs_arg (exp_ne_zero _) (exp_ne_zero _), ← exp_sub, ← sub_mul, ← ofReal_sub,
    arg_exp_mul_I]

中文:
引理 angle_exp_exp
  条件: (x y : 实数)
  证明: by
  simp_rw [angle_eq_abs_arg (exp_ne_zero _) (exp_ne_zero _), ← exp_sub, ← sub_mul, ← ofReal_sub,
    arg_exp_mul_I]

Depends on / 依赖: angle_eq_abs_arg, arg_exp_mul_I, exp_ne_zero, exp_sub, ofReal_sub, simp_rw, sub_mul
-/
lemma angle_exp_exp (x y : Real) :
    angle (exp (x * I)) (exp (y * I)) = |toIocMod Real.two_pi_pos (-π) (x - y)| := by
  simp_rw [angle_eq_abs_arg (exp_ne_zero _) (exp_ne_zero _), ← exp_sub, ← sub_mul, ← ofReal_sub,
    arg_exp_mul_I]

/--
lemma `angle_exp_one` / 引理 `angle_exp_one`

English:
lemma angle_exp_one
  given: (x : Real)
  statement: angle (exp (x * I)) 1 = |toIocMod Real.two_pi_pos (-π) x|
  proof: by
  simpa using angle_exp_exp x 0

中文:
引理 angle_exp_one
  条件: (x : 实数)
  结论: angle (exp (x * I)) 1 = |toIocMod 实数.two_pi_pos (-π) x|
  证明: by
  simpa using angle_exp_exp x 0

Depends on / 依赖: angle_exp_exp
-/
lemma angle_exp_one (x : Real) : angle (exp (x * I)) 1 = |toIocMod Real.two_pi_pos (-π) x| := by
  simpa using angle_exp_exp x 0

/-!
### Arc-length and chord-length are equivalent

This section shows that the arc and chord distances between two unit complex numbers are equivalent
up to a factor of `π / 2`.
-/

/--
lemma `norm_sub_mem_Icc_angle` / 引理 `norm_sub_mem_Icc_angle`

English:
lemma norm_sub_mem_Icc_angle
  given: (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  proof: by
  wlog h : y = 1
  · have := @this (x / y) 1 (by simp only [norm_div, hx, hy, div_one]) norm_one rfl
    rwa [angle_div_left_eq_angle_mul_right, div_sub_one, norm_div, hy, div_one, one_mul]
      at this
    rintro rfl
    simp at hy
  subst y
  rw [norm_eq_one_iff'] at hx
  obtain ⟨θ, hθ, rfl⟩ :

中文:
引理 norm_sub_mem_Icc_angle
  条件: (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  证明: by
  wlog h : y = 1
  · have := @this (x / y) 1 (by simp only [norm_div, hx, hy, div_one]) norm_one rfl
    rwa [angle_div_left_eq_angle_mul_right, div_sub_one, norm_div, hy, div_one, one_mul]
      at this
    rintro rfl
    simp at hy
  subst y
  rw [norm_eq_one_iff'] at hx
  obtain ⟨θ, hθ, rfl⟩ :

Depends on / 依赖: Real.le_sqrt_of_sq_le, abs_pow, abs_sq, add_sub_right_comm, angle_div_left_eq_angle_mul_right, angle_exp_one, div_one, div_sub_one, exp_mul_I, le_sqrt_of_sq_le, mul_pow, norm_add_mul_I, norm_div, norm_eq_one_iff, norm_one, one_mul, toIocMod_eq_self
-/
lemma norm_sub_mem_Icc_angle (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖ in Icc (2 / π * angle x y) (angle x y) := by
  wlog h : y = 1
  · have := @this (x / y) 1 (by simp only [norm_div, hx, hy, div_one]) norm_one rfl
    rwa [angle_div_left_eq_angle_mul_right, div_sub_one, norm_div, hy, div_one, one_mul]
      at this
    rintro rfl
    simp at hy
  subst y
  rw [norm_eq_one_iff'] at hx
  obtain ⟨θ, hθ, rfl⟩ := hx
  rw [angle_exp_one]; rw [exp_mul_I]; rw [add_sub_right_comm]; rw [(toIocMod_eq_self _).2]
  · norm_cast
    rw [norm_add_mul_I]
    refine ⟨Real.le_sqrt_of_sq_le ?_, ?_⟩
    · rw [mul_pow, ← abs_pow, abs_sq]
      calc
        _ = 2 * (1 - (1 - 2 / π ^ 2 * θ ^ 2)) := by ring
        _ <= 2 * (1 - θ.cos) := by
gcongr; exact Real.cos_le_one_sub_mul_cos_sq abs_le.2 Ioc_subset_Icc_self hθ
        _ = _ := by linear_combination -θ.cos_sq_add_sin_sq
    · rw [Real.sqrt_le_left (by positivity), ← abs_pow, abs_sq]
      calc
        _ = 2 * (1 - θ.cos) := by linear_combination θ.cos_sq_add_sin_sq
        _ <= 2 * (1 - (1 - θ ^ 2 / 2)) := by gcongr; exact Real.one_sub_sq_div_two_le_cos
        _ = _ := by ring
  · convert! hθ
    ring

/--
lemma `norm_sub_le_angle` / 引理 `norm_sub_le_angle`

English:
lemma norm_sub_le_angle
  given: (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  statement: ‖x - y‖ <= angle x y
  proof: (norm_sub_mem_Icc_angle hx hy).2

中文:
引理 norm_sub_le_angle
  条件: (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  结论: ‖x - y‖ <= angle x y
  证明: (norm_sub_mem_Icc_angle hx hy).2

Depends on / 依赖: norm_sub_mem_Icc_angle
-/
lemma norm_sub_le_angle (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ‖x - y‖ <= angle x y :=
  (norm_sub_mem_Icc_angle hx hy).2

/--
lemma `mul_angle_le_norm_sub` / 引理 `mul_angle_le_norm_sub`

English:
lemma mul_angle_le_norm_sub
  given: (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  statement: 2 / π * angle x y <= ‖x - y‖
  proof: (norm_sub_mem_Icc_angle hx hy).1

中文:
引理 mul_angle_le_norm_sub
  条件: (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  结论: 2 / π * angle x y <= ‖x - y‖
  证明: (norm_sub_mem_Icc_angle hx hy).1

Depends on / 依赖: norm_sub_mem_Icc_angle
-/
lemma mul_angle_le_norm_sub (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : 2 / π * angle x y <= ‖x - y‖ :=
  (norm_sub_mem_Icc_angle hx hy).1

/--
lemma `angle_le_mul_norm_sub` / 引理 `angle_le_mul_norm_sub`

English:
lemma angle_le_mul_norm_sub
  given: (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  statement: angle x y <= π / 2 * ‖x - y‖
  proof: by
  rw [← div_le_iff₀' <| by positivity]; rw [div_eq_inv_mul]; rw [inv_div]; exact mul_angle_le_norm_sub hx hy

中文:
引理 angle_le_mul_norm_sub
  条件: (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  结论: angle x y <= π / 2 * ‖x - y‖
  证明: by
  rw [← div_le_iff₀' <| by positivity]; rw [div_eq_inv_mul]; rw [inv_div]; exact mul_angle_le_norm_sub hx hy

Depends on / 依赖: div_eq_inv_mul, inv_div, mul_angle_le_norm_sub
-/
lemma angle_le_mul_norm_sub (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : angle x y <= π / 2 * ‖x - y‖ := by
  rw [← div_le_iff₀' <| by positivity]; rw [div_eq_inv_mul]; rw [inv_div]; exact mul_angle_le_norm_sub hx hy

end Complex
