/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# Right-angled triangles

This file proves basic geometric results about distances and angles in (possibly degenerate)
right-angled triangles in real inner product spaces and Euclidean affine spaces.

## Implementation notes

Results in this file are generally given in a form with only those non-degeneracy conditions
needed for the particular result, rather than requiring affine independence of the points of a
triangle unnecessarily.

## References

* https://en.wikipedia.org/wiki/Pythagorean_theorem

-/

public section


noncomputable section

open scoped EuclideanGeometry

open scoped Real

open scoped RealInnerProductSpace

namespace InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]

/--
theorem `norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two` / 定理 `norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two`

English:
theorem norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two
  given: (x y : V)
  proof: by
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y

中文:
定理 norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two
  条件: (x y : V)
  证明: by
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y

Depends on / 依赖: inner_eq_zero_iff_angle_eq_pi_div_two, norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero
-/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2 := by
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y

/--
theorem `norm_add_sq_eq_norm_sq_add_norm_sq'` / 定理 `norm_add_sq_eq_norm_sq_add_norm_sq'`

English:
theorem norm_add_sq_eq_norm_sq_add_norm_sq'
  given: (x y : V) (h : angle x y = π / 2)
  proof: (norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

中文:
定理 norm_add_sq_eq_norm_sq_add_norm_sq'
  条件: (x y : V) (h : angle x y = π / 2)
  证明: (norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

Depends on / 依赖: norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two
-/
theorem norm_add_sq_eq_norm_sq_add_norm_sq' (x y : V) (h : angle x y = π / 2) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

/--
theorem `norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two` / 定理 `norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two`

English:
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two
  given: (x y : V)
  proof: by
  rw [norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y

中文:
定理 norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two
  条件: (x y : V)
  证明: by
  rw [norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y

Depends on / 依赖: inner_eq_zero_iff_angle_eq_pi_div_two, norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero
-/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2 := by
  rw [norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y

/--
theorem `norm_sub_sq_eq_norm_sq_add_norm_sq'` / 定理 `norm_sub_sq_eq_norm_sq_add_norm_sq'`

English:
theorem norm_sub_sq_eq_norm_sq_add_norm_sq'
  given: (x y : V) (h : angle x y = π / 2)
  proof: (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

中文:
定理 norm_sub_sq_eq_norm_sq_add_norm_sq'
  条件: (x y : V) (h : angle x y = π / 2)
  证明: (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

Depends on / 依赖: norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two
-/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq' (x y : V) (h : angle x y = π / 2) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

/--
theorem `angle_add_eq_arccos_of_inner_eq_zero` / 定理 `angle_add_eq_arccos_of_inner_eq_zero`

English:
theorem angle_add_eq_arccos_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0)
  proof: by
  rw [angle]; rw [inner_add_right]; rw [h]; rw [add_zero]; rw [real_inner_self_eq_norm_mul_norm]
  by_cases hx : ‖x‖ = 0; · simp [hx]
  rw [div_mul_eq_div_div]; rw [mul_self_div_self]

中文:
定理 angle_add_eq_arccos_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0)
  证明: by
  rw [angle]; rw [inner_add_right]; rw [h]; rw [add_zero]; rw [real_inner_self_eq_norm_mul_norm]
  by_cases hx : ‖x‖ = 0; · simp [hx]
  rw [div_mul_eq_div_div]; rw [mul_self_div_self]

Depends on / 依赖: add_zero, div_mul_eq_div_div, inner_add_right, mul_self_div_self, real_inner_self_eq_norm_mul_norm
-/
theorem angle_add_eq_arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    angle x (x + y) = Real.arccos (‖x‖ / ‖x + y‖) := by
  rw [angle]; rw [inner_add_right]; rw [h]; rw [add_zero]; rw [real_inner_self_eq_norm_mul_norm]
  by_cases hx : ‖x‖ = 0; · simp [hx]
  rw [div_mul_eq_div_div]; rw [mul_self_div_self]

/--
theorem `angle_add_eq_arcsin_of_inner_eq_zero` / 定理 `angle_add_eq_arcsin_of_inner_eq_zero`

English:
theorem angle_add_eq_arcsin_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0)
  proof: by
  have hxy : ‖x + y‖ ^ 2 != 0 := by
    rw [pow_two]; rw [norm_add_sq_eq_norm_sq_add_norm_sq_real h]; rw [ne_comm]
    refine ne_of_lt ?_
    rcases h0 with (h0 | h0)
    · exact
        Left.add_pos_of_pos_of_nonneg (mul_self_pos.2 (norm_ne_zero_iff.2 h0)) (mul_self_nonneg _)
    · exact
        Left.add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_self_pos.2 (norm_ne_zero_iff.2 h0))
  rw [angle_add_eq_arccos_of_inner_eq_zero h]; rw [Real.arccos_eq_arcsin (div_nonneg (norm_nonneg _) (norm_nonneg _))]; rw [div_pow]; rw [one_sub_div hxy]
  nth_rw 1 [pow_two]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_real h]; rw [pow_two]; rw [add_sub_cancel_left]; rw [← pow_two]; rw [← div_pow]; rw [Real.sqrt_sq (div_nonneg (norm_nonneg _) (norm_nonneg _))]

中文:
定理 angle_add_eq_arcsin_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0)
  证明: by
  have hxy : ‖x + y‖ ^ 2 != 0 := by
    rw [pow_two]; rw [norm_add_sq_eq_norm_sq_add_norm_sq_real h]; rw [ne_comm]
    refine ne_of_lt ?_
    rcases h0 with (h0 | h0)
    · exact
        Left.add_pos_of_pos_of_nonneg (mul_self_pos.2 (norm_ne_zero_iff.2 h0)) (mul_self_nonneg _)
    · exact
        Left.add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_self_pos.2 (norm_ne_zero_iff.2 h0))
  rw [angle_add_eq_arccos_of_inner_eq_zero h]; rw [Real.arccos_eq_arcsin (div_nonneg (norm_nonneg _) (norm_nonneg _))]; rw [div_pow]; rw [one_sub_div hxy]
  nth_rw 1 [pow_two]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_real h]; rw [pow_two]; rw [add_sub_cancel_left]; rw [← pow_two]; rw [← div_pow]; rw [Real.sqrt_sq (div_nonneg (norm_nonneg _) (norm_nonneg _))]

Depends on / 依赖: Left.add_pos_of_nonneg_of_pos, Left.add_pos_of_pos_of_nonneg, Real.arccos_eq_arcsin, add_pos_of_nonneg_of_pos, add_pos_of_pos_of_nonneg, angle_add_eq_arccos_of_inner_eq_zero, arccos_eq_arcsin, div_nonneg, div_pow, mul_self_nonneg, mul_self_pos, ne_comm, ne_of_lt, norm_add_sq_eq_norm_sq_add_norm_sq_real, norm_ne_zero_iff, norm_nonneg, one_sub_di, pow_two
-/
theorem angle_add_eq_arcsin_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0) :
    angle x (x + y) = Real.arcsin (‖y‖ / ‖x + y‖) := by
  have hxy : ‖x + y‖ ^ 2 != 0 := by
    rw [pow_two]; rw [norm_add_sq_eq_norm_sq_add_norm_sq_real h]; rw [ne_comm]
    refine ne_of_lt ?_
    rcases h0 with (h0 | h0)
    · exact
        Left.add_pos_of_pos_of_nonneg (mul_self_pos.2 (norm_ne_zero_iff.2 h0)) (mul_self_nonneg _)
    · exact
        Left.add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_self_pos.2 (norm_ne_zero_iff.2 h0))
  rw [angle_add_eq_arccos_of_inner_eq_zero h]; rw [Real.arccos_eq_arcsin (div_nonneg (norm_nonneg _) (norm_nonneg _))]; rw [div_pow]; rw [one_sub_div hxy]
  nth_rw 1 [pow_two]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_real h]; rw [pow_two]; rw [add_sub_cancel_left]; rw [← pow_two]; rw [← div_pow]; rw [Real.sqrt_sq (div_nonneg (norm_nonneg _) (norm_nonneg _))]

/--
theorem `angle_add_eq_arctan_of_inner_eq_zero` / 定理 `angle_add_eq_arctan_of_inner_eq_zero`

English:
theorem angle_add_eq_arctan_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0)
  proof: by
  rw [angle_add_eq_arcsin_of_inner_eq_zero h (Or.inl h0)]; rw [Real.arctan_eq_arcsin]; rw [←
    div_mul_eq_div_div]; rw [norm_add_eq_sqrt_iff_real_inner_eq_zero.2 h]
  nth_rw 3 [← Real.sqrt_sq (norm_nonneg x)]
  rw_mod_cast [← Real.sqrt_mul (sq_nonneg _), div_pow, pow_two, pow_two, mul_add, mul_one, mul_div,
    mul_comm (‖x‖ * ‖x‖), ← mul_div, div_self (mul_self_pos.2 (norm_ne_zero_iff.2 h0)).ne', mul_one]

中文:
定理 angle_add_eq_arctan_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0)
  证明: by
  rw [angle_add_eq_arcsin_of_inner_eq_zero h (Or.inl h0)]; rw [Real.arctan_eq_arcsin]; rw [←
    div_mul_eq_div_div]; rw [norm_add_eq_sqrt_iff_real_inner_eq_zero.2 h]
  nth_rw 3 [← Real.sqrt_sq (norm_nonneg x)]
  rw_mod_cast [← Real.sqrt_mul (sq_nonneg _), div_pow, pow_two, pow_two, mul_add, mul_one, mul_div,
    mul_comm (‖x‖ * ‖x‖), ← mul_div, div_self (mul_self_pos.2 (norm_ne_zero_iff.2 h0)).ne', mul_one]

Depends on / 依赖: Or.inl, Real.arctan_eq_arcsin, Real.sqrt_mul, Real.sqrt_sq, angle_add_eq_arcsin_of_inner_eq_zero, arctan_eq_arcsin, div_mul_eq_div_div, div_pow, div_self, mul_add, mul_comm, mul_div, mul_one, mul_self_pos, norm_add_eq_sqrt_iff_real_inner_eq_zero, norm_ne_zero_iff, norm_nonneg, nth_rw, pow_two, rw_mod_cast
-/
theorem angle_add_eq_arctan_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0) :
    angle x (x + y) = Real.arctan (‖y‖ / ‖x‖) := by
  rw [angle_add_eq_arcsin_of_inner_eq_zero h (Or.inl h0)]; rw [Real.arctan_eq_arcsin]; rw [←
    div_mul_eq_div_div]; rw [norm_add_eq_sqrt_iff_real_inner_eq_zero.2 h]
  nth_rw 3 [← Real.sqrt_sq (norm_nonneg x)]
  rw_mod_cast [← Real.sqrt_mul (sq_nonneg _), div_pow, pow_two, pow_two, mul_add, mul_one, mul_div,
    mul_comm (‖x‖ * ‖x‖), ← mul_div, div_self (mul_self_pos.2 (norm_ne_zero_iff.2 h0)).ne', mul_one]

/--
theorem `angle_add_pos_of_inner_eq_zero` / 定理 `angle_add_pos_of_inner_eq_zero`

English:
theorem angle_add_pos_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0)
  proof: by
  rw [angle_add_eq_arccos_of_inner_eq_zero h]; rw [Real.arccos_pos]; rw [norm_add_eq_sqrt_iff_real_inner_eq_zero.2 h]
  by_cases hx : x = 0; · simp [hx]
  rw [div_lt_one (Real.sqrt_pos.2 (Left.add_pos_of_pos_of_nonneg (mul_self_pos.2
    (norm_ne_zero_iff.2 hx)) (mul_self_nonneg _)))]; rw [Real.lt_sqrt (norm_nonneg _)]; rw [pow_two]
  simpa [hx] using h0

中文:
定理 angle_add_pos_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0)
  证明: by
  rw [angle_add_eq_arccos_of_inner_eq_zero h]; rw [Real.arccos_pos]; rw [norm_add_eq_sqrt_iff_real_inner_eq_zero.2 h]
  by_cases hx : x = 0; · simp [hx]
  rw [div_lt_one (Real.sqrt_pos.2 (Left.add_pos_of_pos_of_nonneg (mul_self_pos.2
    (norm_ne_zero_iff.2 hx)) (mul_self_nonneg _)))]; rw [Real.lt_sqrt (norm_nonneg _)]; rw [pow_two]
  simpa [hx] using h0

Depends on / 依赖: Left.add_pos_of_pos_of_nonneg, Real.arccos_pos, Real.lt_sqrt, Real.sqrt_pos, add_pos_of_pos_of_nonneg, angle_add_eq_arccos_of_inner_eq_zero, arccos_pos, div_lt_one, lt_sqrt, mul_self_nonneg, mul_self_pos, norm_add_eq_sqrt_iff_real_inner_eq_zero, norm_ne_zero_iff, norm_nonneg, pow_two, sqrt_pos
-/
theorem angle_add_pos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0) :
    0 < angle x (x + y) := by
  rw [angle_add_eq_arccos_of_inner_eq_zero h]; rw [Real.arccos_pos]; rw [norm_add_eq_sqrt_iff_real_inner_eq_zero.2 h]
  by_cases hx : x = 0; · simp [hx]
  rw [div_lt_one (Real.sqrt_pos.2 (Left.add_pos_of_pos_of_nonneg (mul_self_pos.2
    (norm_ne_zero_iff.2 hx)) (mul_self_nonneg _)))]; rw [Real.lt_sqrt (norm_nonneg _)]; rw [pow_two]
  simpa [hx] using h0

/--
theorem `angle_add_le_pi_div_two_of_inner_eq_zero` / 定理 `angle_add_le_pi_div_two_of_inner_eq_zero`

English:
theorem angle_add_le_pi_div_two_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0)
  proof: by
  rw [angle_add_eq_arccos_of_inner_eq_zero h]; rw [Real.arccos_le_pi_div_two]
  exact div_nonneg (norm_nonneg _) (norm_nonneg _)

中文:
定理 angle_add_le_pi_div_two_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0)
  证明: by
  rw [angle_add_eq_arccos_of_inner_eq_zero h]; rw [Real.arccos_le_pi_div_two]
  exact div_nonneg (norm_nonneg _) (norm_nonneg _)

Depends on / 依赖: Real.arccos_le_pi_div_two, angle_add_eq_arccos_of_inner_eq_zero, arccos_le_pi_div_two, div_nonneg, norm_nonneg
-/
theorem angle_add_le_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    angle x (x + y) <= π / 2 := by
  rw [angle_add_eq_arccos_of_inner_eq_zero h]; rw [Real.arccos_le_pi_div_two]
  exact div_nonneg (norm_nonneg _) (norm_nonneg _)

/--
theorem `angle_add_lt_pi_div_two_of_inner_eq_zero` / 定理 `angle_add_lt_pi_div_two_of_inner_eq_zero`

English:
theorem angle_add_lt_pi_div_two_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0)
  proof: by
  rw [angle_add_eq_arccos_of_inner_eq_zero h]; rw [Real.arccos_lt_pi_div_two]; rw [norm_add_eq_sqrt_iff_real_inner_eq_zero.2 h]
  exact div_pos (norm_pos_iff.2 h0) (Real.sqrt_pos.2 (Left.add_pos_of_pos_of_nonneg
    (mul_self_pos.2 (norm_ne_zero_iff.2 h0)) (mul_self_nonneg _)))

中文:
定理 angle_add_lt_pi_div_two_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0)
  证明: by
  rw [angle_add_eq_arccos_of_inner_eq_zero h]; rw [Real.arccos_lt_pi_div_two]; rw [norm_add_eq_sqrt_iff_real_inner_eq_zero.2 h]
  exact div_pos (norm_pos_iff.2 h0) (Real.sqrt_pos.2 (Left.add_pos_of_pos_of_nonneg
    (mul_self_pos.2 (norm_ne_zero_iff.2 h0)) (mul_self_nonneg _)))

Depends on / 依赖: Left.add_pos_of_pos_of_nonneg, Real.arccos_lt_pi_div_two, Real.sqrt_pos, add_pos_of_pos_of_nonneg, angle_add_eq_arccos_of_inner_eq_zero, arccos_lt_pi_div_two, div_pos, mul_self_nonneg, mul_self_pos, norm_add_eq_sqrt_iff_real_inner_eq_zero, norm_ne_zero_iff, norm_pos_iff, sqrt_pos
-/
theorem angle_add_lt_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0) :
    angle x (x + y) < π / 2 := by
  rw [angle_add_eq_arccos_of_inner_eq_zero h]; rw [Real.arccos_lt_pi_div_two]; rw [norm_add_eq_sqrt_iff_real_inner_eq_zero.2 h]
  exact div_pos (norm_pos_iff.2 h0) (Real.sqrt_pos.2 (Left.add_pos_of_pos_of_nonneg
    (mul_self_pos.2 (norm_ne_zero_iff.2 h0)) (mul_self_nonneg _)))

/--
theorem `cos_angle_add_of_inner_eq_zero` / 定理 `cos_angle_add_of_inner_eq_zero`

English:
theorem cos_angle_add_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0)
  proof: by
  rw [angle_add_eq_arccos_of_inner_eq_zero h]; rw [Real.cos_arccos (le_trans (by simp) (div_nonneg (norm_nonneg _) (norm_nonneg _)))
      (div_le_one_of_le₀ _ (norm_nonneg _))]
  rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)]; rw [norm_add_sq_eq_norm_sq_add_norm_sq_real h]
  exact le_add_of_nonneg_right (mul_self_nonneg _)

中文:
定理 cos_angle_add_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0)
  证明: by
  rw [angle_add_eq_arccos_of_inner_eq_zero h]; rw [Real.cos_arccos (le_trans (by simp) (div_nonneg (norm_nonneg _) (norm_nonneg _)))
      (div_le_one_of_le₀ _ (norm_nonneg _))]
  rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)]; rw [norm_add_sq_eq_norm_sq_add_norm_sq_real h]
  exact le_add_of_nonneg_right (mul_self_nonneg _)

Depends on / 依赖: Real.cos_arccos, angle_add_eq_arccos_of_inner_eq_zero, cos_arccos, div_nonneg, le_add_of_nonneg_right, le_trans, mul_self_le_mul_self_iff, mul_self_nonneg, norm_add_sq_eq_norm_sq_add_norm_sq_real, norm_nonneg
-/
theorem cos_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.cos (angle x (x + y)) = ‖x‖ / ‖x + y‖ := by
  rw [angle_add_eq_arccos_of_inner_eq_zero h]; rw [Real.cos_arccos (le_trans (by simp) (div_nonneg (norm_nonneg _) (norm_nonneg _)))
      (div_le_one_of_le₀ _ (norm_nonneg _))]
  rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)]; rw [norm_add_sq_eq_norm_sq_add_norm_sq_real h]
  exact le_add_of_nonneg_right (mul_self_nonneg _)

/--
theorem `sin_angle_add_of_inner_eq_zero` / 定理 `sin_angle_add_of_inner_eq_zero`

English:
theorem sin_angle_add_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0)
  proof: by
  rw [angle_add_eq_arcsin_of_inner_eq_zero h h0]; rw [Real.sin_arcsin (le_trans (by simp) (div_nonneg (norm_nonneg _) (norm_nonneg _)))
      (div_le_one_of_le₀ _ (norm_nonneg _))]
  rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)]; rw [norm_add_sq_eq_norm_sq_add_norm_sq_real h]
  exact le_add_of_nonneg_left (mul_self_nonneg _)

中文:
定理 sin_angle_add_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0)
  证明: by
  rw [angle_add_eq_arcsin_of_inner_eq_zero h h0]; rw [Real.sin_arcsin (le_trans (by simp) (div_nonneg (norm_nonneg _) (norm_nonneg _)))
      (div_le_one_of_le₀ _ (norm_nonneg _))]
  rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)]; rw [norm_add_sq_eq_norm_sq_add_norm_sq_real h]
  exact le_add_of_nonneg_left (mul_self_nonneg _)

Depends on / 依赖: Real.sin_arcsin, angle_add_eq_arcsin_of_inner_eq_zero, div_nonneg, le_add_of_nonneg_left, le_trans, mul_self_le_mul_self_iff, mul_self_nonneg, norm_add_sq_eq_norm_sq_add_norm_sq_real, norm_nonneg, sin_arcsin
-/
theorem sin_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0) :
    Real.sin (angle x (x + y)) = ‖y‖ / ‖x + y‖ := by
  rw [angle_add_eq_arcsin_of_inner_eq_zero h h0]; rw [Real.sin_arcsin (le_trans (by simp) (div_nonneg (norm_nonneg _) (norm_nonneg _)))
      (div_le_one_of_le₀ _ (norm_nonneg _))]
  rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)]; rw [norm_add_sq_eq_norm_sq_add_norm_sq_real h]
  exact le_add_of_nonneg_left (mul_self_nonneg _)

/--
theorem `tan_angle_add_of_inner_eq_zero` / 定理 `tan_angle_add_of_inner_eq_zero`

English:
theorem tan_angle_add_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0)
  proof: by
  by_cases h0 : x = 0; · simp [h0]
  rw [angle_add_eq_arctan_of_inner_eq_zero h h0]; rw [Real.tan_arctan]

中文:
定理 tan_angle_add_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0)
  证明: by
  by_cases h0 : x = 0; · simp [h0]
  rw [angle_add_eq_arctan_of_inner_eq_zero h h0]; rw [Real.tan_arctan]

Depends on / 依赖: Real.tan_arctan, angle_add_eq_arctan_of_inner_eq_zero, tan_arctan
-/
theorem tan_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.tan (angle x (x + y)) = ‖y‖ / ‖x‖ := by
  by_cases h0 : x = 0; · simp [h0]
  rw [angle_add_eq_arctan_of_inner_eq_zero h h0]; rw [Real.tan_arctan]

/--
theorem `cos_angle_add_mul_norm_of_inner_eq_zero` / 定理 `cos_angle_add_mul_norm_of_inner_eq_zero`

English:
theorem cos_angle_add_mul_norm_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0)
  proof: by
  rw [cos_angle_add_of_inner_eq_zero h]
  by_cases hxy : ‖x + y‖ = 0
  · have h' := norm_add_sq_eq_norm_sq_add_norm_sq_real h
    rw [hxy]; rw [zero_mul]; rw [eq_comm]; rw [add_eq_zero_iff_of_nonneg (mul_self_nonneg ‖x‖) (mul_self_nonneg ‖y‖)]; rw [mul_self_eq_zero] at h'
    simp [h'.1]
  · exact div_mul_cancel₀ _ hxy

中文:
定理 cos_angle_add_mul_norm_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0)
  证明: by
  rw [cos_angle_add_of_inner_eq_zero h]
  by_cases hxy : ‖x + y‖ = 0
  · have h' := norm_add_sq_eq_norm_sq_add_norm_sq_real h
    rw [hxy]; rw [zero_mul]; rw [eq_comm]; rw [add_eq_zero_iff_of_nonneg (mul_self_nonneg ‖x‖) (mul_self_nonneg ‖y‖)]; rw [mul_self_eq_zero] at h'
    simp [h'.1]
  · exact div_mul_cancel₀ _ hxy

Depends on / 依赖: add_eq_zero_iff_of_nonneg, cos_angle_add_of_inner_eq_zero, eq_comm, mul_self_eq_zero, mul_self_nonneg, norm_add_sq_eq_norm_sq_add_norm_sq_real, zero_mul
-/
theorem cos_angle_add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.cos (angle x (x + y)) * ‖x + y‖ = ‖x‖ := by
  rw [cos_angle_add_of_inner_eq_zero h]
  by_cases hxy : ‖x + y‖ = 0
  · have h' := norm_add_sq_eq_norm_sq_add_norm_sq_real h
    rw [hxy]; rw [zero_mul]; rw [eq_comm]; rw [add_eq_zero_iff_of_nonneg (mul_self_nonneg ‖x‖) (mul_self_nonneg ‖y‖)]; rw [mul_self_eq_zero] at h'
    simp [h'.1]
  · exact div_mul_cancel₀ _ hxy

/--
theorem `sin_angle_add_mul_norm_of_inner_eq_zero` / 定理 `sin_angle_add_mul_norm_of_inner_eq_zero`

English:
theorem sin_angle_add_mul_norm_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0)
  proof: by
  by_cases h0 : x = 0 ∧ y = 0; · simp [h0]
  rw [not_and_or] at h0
  rw [sin_angle_add_of_inner_eq_zero h h0]; rw [div_mul_cancel₀]
  rw [← mul_self_ne_zero]; rw [norm_add_sq_eq_norm_sq_add_norm_sq_real h]
  refine (ne_of_lt ?_).symm
  rcases h0 with (h0 | h0)
  · exact Left.add_pos_of_pos_of_nonneg (mul_self_pos.2 (norm_ne_zero_iff.2 h0)) (mul_self_nonneg _)
  · exact Left.add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_self_pos.2 (norm_ne_zero_iff.2 h0))

中文:
定理 sin_angle_add_mul_norm_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0)
  证明: by
  by_cases h0 : x = 0 ∧ y = 0; · simp [h0]
  rw [not_and_or] at h0
  rw [sin_angle_add_of_inner_eq_zero h h0]; rw [div_mul_cancel₀]
  rw [← mul_self_ne_zero]; rw [norm_add_sq_eq_norm_sq_add_norm_sq_real h]
  refine (ne_of_lt ?_).symm
  rcases h0 with (h0 | h0)
  · exact Left.add_pos_of_pos_of_nonneg (mul_self_pos.2 (norm_ne_zero_iff.2 h0)) (mul_self_nonneg _)
  · exact Left.add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_self_pos.2 (norm_ne_zero_iff.2 h0))

Depends on / 依赖: Left.add_pos_of_nonneg_of_pos, Left.add_pos_of_pos_of_nonneg, add_pos_of_nonneg_of_pos, add_pos_of_pos_of_nonneg, mul_self_ne_zero, mul_self_nonneg, mul_self_pos, ne_of_lt, norm_add_sq_eq_norm_sq_add_norm_sq_real, norm_ne_zero_iff, not_and_or, sin_angle_add_of_inner_eq_zero
-/
theorem sin_angle_add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.sin (angle x (x + y)) * ‖x + y‖ = ‖y‖ := by
  by_cases h0 : x = 0 ∧ y = 0; · simp [h0]
  rw [not_and_or] at h0
  rw [sin_angle_add_of_inner_eq_zero h h0]; rw [div_mul_cancel₀]
  rw [← mul_self_ne_zero]; rw [norm_add_sq_eq_norm_sq_add_norm_sq_real h]
  refine (ne_of_lt ?_).symm
  rcases h0 with (h0 | h0)
  · exact Left.add_pos_of_pos_of_nonneg (mul_self_pos.2 (norm_ne_zero_iff.2 h0)) (mul_self_nonneg _)
  · exact Left.add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_self_pos.2 (norm_ne_zero_iff.2 h0))

/--
theorem `tan_angle_add_mul_norm_of_inner_eq_zero` / 定理 `tan_angle_add_mul_norm_of_inner_eq_zero`

English:
theorem tan_angle_add_mul_norm_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0)
  proof: by
  rw [tan_angle_add_of_inner_eq_zero h]
  rcases h0 with (h0 | h0) <;> simp [h0]

中文:
定理 tan_angle_add_mul_norm_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0)
  证明: by
  rw [tan_angle_add_of_inner_eq_zero h]
  rcases h0 with (h0 | h0) <;> simp [h0]

Depends on / 依赖: tan_angle_add_of_inner_eq_zero
-/
theorem tan_angle_add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0) :
    Real.tan (angle x (x + y)) * ‖x‖ = ‖y‖ := by
  rw [tan_angle_add_of_inner_eq_zero h]
  rcases h0 with (h0 | h0) <;> simp [h0]

/--
theorem `norm_div_cos_angle_add_of_inner_eq_zero` / 定理 `norm_div_cos_angle_add_of_inner_eq_zero`

English:
theorem norm_div_cos_angle_add_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0)
  proof: by
  rw [cos_angle_add_of_inner_eq_zero h]
  rcases h0 with (h0 | h0)
  · rw [div_div_eq_mul_div, mul_comm, div_eq_mul_inv, mul_inv_cancel_right₀ (norm_ne_zero_iff.2 h0)]
  · simp [h0]

中文:
定理 norm_div_cos_angle_add_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0)
  证明: by
  rw [cos_angle_add_of_inner_eq_zero h]
  rcases h0 with (h0 | h0)
  · rw [div_div_eq_mul_div, mul_comm, div_eq_mul_inv, mul_inv_cancel_right₀ (norm_ne_zero_iff.2 h0)]
  · simp [h0]

Depends on / 依赖: cos_angle_add_of_inner_eq_zero, div_div_eq_mul_div, div_eq_mul_inv, mul_comm, norm_ne_zero_iff
-/
theorem norm_div_cos_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0) :
    ‖x‖ / Real.cos (angle x (x + y)) = ‖x + y‖ := by
  rw [cos_angle_add_of_inner_eq_zero h]
  rcases h0 with (h0 | h0)
  · rw [div_div_eq_mul_div, mul_comm, div_eq_mul_inv, mul_inv_cancel_right₀ (norm_ne_zero_iff.2 h0)]
  · simp [h0]

/--
theorem `norm_div_sin_angle_add_of_inner_eq_zero` / 定理 `norm_div_sin_angle_add_of_inner_eq_zero`

English:
theorem norm_div_sin_angle_add_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0)
  proof: by
  rcases h0 with (h0 | h0); · simp [h0]
  rw [sin_angle_add_of_inner_eq_zero h (Or.inr h0)]; rw [div_div_eq_mul_div]; rw [mul_comm]; rw [div_eq_mul_inv]; rw [mul_inv_cancel_right₀ (norm_ne_zero_iff.2 h0)]

中文:
定理 norm_div_sin_angle_add_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0)
  证明: by
  rcases h0 with (h0 | h0); · simp [h0]
  rw [sin_angle_add_of_inner_eq_zero h (Or.inr h0)]; rw [div_div_eq_mul_div]; rw [mul_comm]; rw [div_eq_mul_inv]; rw [mul_inv_cancel_right₀ (norm_ne_zero_iff.2 h0)]

Depends on / 依赖: Or.inr, div_div_eq_mul_div, div_eq_mul_inv, mul_comm, norm_ne_zero_iff, sin_angle_add_of_inner_eq_zero
-/
theorem norm_div_sin_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0) :
    ‖y‖ / Real.sin (angle x (x + y)) = ‖x + y‖ := by
  rcases h0 with (h0 | h0); · simp [h0]
  rw [sin_angle_add_of_inner_eq_zero h (Or.inr h0)]; rw [div_div_eq_mul_div]; rw [mul_comm]; rw [div_eq_mul_inv]; rw [mul_inv_cancel_right₀ (norm_ne_zero_iff.2 h0)]

/--
theorem `norm_div_tan_angle_add_of_inner_eq_zero` / 定理 `norm_div_tan_angle_add_of_inner_eq_zero`

English:
theorem norm_div_tan_angle_add_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0)
  proof: by
  rw [tan_angle_add_of_inner_eq_zero h]
  rcases h0 with (h0 | h0)
  · simp [h0]
  · rw [div_div_eq_mul_div, mul_comm, div_eq_mul_inv, mul_inv_cancel_right₀ (norm_ne_zero_iff.2 h0)]

中文:
定理 norm_div_tan_angle_add_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0)
  证明: by
  rw [tan_angle_add_of_inner_eq_zero h]
  rcases h0 with (h0 | h0)
  · simp [h0]
  · rw [div_div_eq_mul_div, mul_comm, div_eq_mul_inv, mul_inv_cancel_right₀ (norm_ne_zero_iff.2 h0)]

Depends on / 依赖: div_div_eq_mul_div, div_eq_mul_inv, mul_comm, norm_ne_zero_iff, tan_angle_add_of_inner_eq_zero
-/
theorem norm_div_tan_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0) :
    ‖y‖ / Real.tan (angle x (x + y)) = ‖x‖ := by
  rw [tan_angle_add_of_inner_eq_zero h]
  rcases h0 with (h0 | h0)
  · simp [h0]
  · rw [div_div_eq_mul_div, mul_comm, div_eq_mul_inv, mul_inv_cancel_right₀ (norm_ne_zero_iff.2 h0)]

/--
theorem `angle_sub_eq_arccos_of_inner_eq_zero` / 定理 `angle_sub_eq_arccos_of_inner_eq_zero`

English:
theorem angle_sub_eq_arccos_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0)
  proof: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [angle_add_eq_arccos_of_inner_eq_zero h]

中文:
定理 angle_sub_eq_arccos_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0)
  证明: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [angle_add_eq_arccos_of_inner_eq_zero h]

Depends on / 依赖: angle_add_eq_arccos_of_inner_eq_zero, inner_neg_right, neg_eq_zero, sub_eq_add_neg
-/
theorem angle_sub_eq_arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    angle x (x - y) = Real.arccos (‖x‖ / ‖x - y‖) := by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [angle_add_eq_arccos_of_inner_eq_zero h]

/--
theorem `angle_sub_eq_arcsin_of_inner_eq_zero` / 定理 `angle_sub_eq_arcsin_of_inner_eq_zero`

English:
theorem angle_sub_eq_arcsin_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0)
  proof: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [or_comm]; rw [← neg_ne_zero]; rw [or_comm] at h0
  rw [sub_eq_add_neg]; rw [angle_add_eq_arcsin_of_inner_eq_zero h h0]; rw [norm_neg]

中文:
定理 angle_sub_eq_arcsin_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0)
  证明: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [or_comm]; rw [← neg_ne_zero]; rw [or_comm] at h0
  rw [sub_eq_add_neg]; rw [angle_add_eq_arcsin_of_inner_eq_zero h h0]; rw [norm_neg]

Depends on / 依赖: angle_add_eq_arcsin_of_inner_eq_zero, inner_neg_right, neg_eq_zero, neg_ne_zero, norm_neg, or_comm, sub_eq_add_neg
-/
theorem angle_sub_eq_arcsin_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0) :
    angle x (x - y) = Real.arcsin (‖y‖ / ‖x - y‖) := by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [or_comm]; rw [← neg_ne_zero]; rw [or_comm] at h0
  rw [sub_eq_add_neg]; rw [angle_add_eq_arcsin_of_inner_eq_zero h h0]; rw [norm_neg]

/--
theorem `angle_sub_eq_arctan_of_inner_eq_zero` / 定理 `angle_sub_eq_arctan_of_inner_eq_zero`

English:
theorem angle_sub_eq_arctan_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0)
  proof: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [angle_add_eq_arctan_of_inner_eq_zero h h0]; rw [norm_neg]

中文:
定理 angle_sub_eq_arctan_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0)
  证明: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [angle_add_eq_arctan_of_inner_eq_zero h h0]; rw [norm_neg]

Depends on / 依赖: angle_add_eq_arctan_of_inner_eq_zero, inner_neg_right, neg_eq_zero, norm_neg, sub_eq_add_neg
-/
theorem angle_sub_eq_arctan_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0) :
    angle x (x - y) = Real.arctan (‖y‖ / ‖x‖) := by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [angle_add_eq_arctan_of_inner_eq_zero h h0]; rw [norm_neg]

/--
theorem `angle_sub_pos_of_inner_eq_zero` / 定理 `angle_sub_pos_of_inner_eq_zero`

English:
theorem angle_sub_pos_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0)
  proof: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [← neg_ne_zero] at h0
  rw [sub_eq_add_neg]
  exact angle_add_pos_of_inner_eq_zero h h0

中文:
定理 angle_sub_pos_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0)
  证明: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [← neg_ne_zero] at h0
  rw [sub_eq_add_neg]
  exact angle_add_pos_of_inner_eq_zero h h0

Depends on / 依赖: angle_add_pos_of_inner_eq_zero, inner_neg_right, neg_eq_zero, neg_ne_zero, sub_eq_add_neg
-/
theorem angle_sub_pos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0) :
    0 < angle x (x - y) := by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [← neg_ne_zero] at h0
  rw [sub_eq_add_neg]
  exact angle_add_pos_of_inner_eq_zero h h0

/--
theorem `angle_sub_le_pi_div_two_of_inner_eq_zero` / 定理 `angle_sub_le_pi_div_two_of_inner_eq_zero`

English:
theorem angle_sub_le_pi_div_two_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0)
  proof: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]
  exact angle_add_le_pi_div_two_of_inner_eq_zero h

中文:
定理 angle_sub_le_pi_div_two_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0)
  证明: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]
  exact angle_add_le_pi_div_two_of_inner_eq_zero h

Depends on / 依赖: angle_add_le_pi_div_two_of_inner_eq_zero, inner_neg_right, neg_eq_zero, sub_eq_add_neg
-/
theorem angle_sub_le_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    angle x (x - y) <= π / 2 := by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]
  exact angle_add_le_pi_div_two_of_inner_eq_zero h

/--
theorem `angle_sub_lt_pi_div_two_of_inner_eq_zero` / 定理 `angle_sub_lt_pi_div_two_of_inner_eq_zero`

English:
theorem angle_sub_lt_pi_div_two_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0)
  proof: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]
  exact angle_add_lt_pi_div_two_of_inner_eq_zero h h0

中文:
定理 angle_sub_lt_pi_div_two_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0)
  证明: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]
  exact angle_add_lt_pi_div_two_of_inner_eq_zero h h0

Depends on / 依赖: angle_add_lt_pi_div_two_of_inner_eq_zero, inner_neg_right, neg_eq_zero, sub_eq_add_neg
-/
theorem angle_sub_lt_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0) :
    angle x (x - y) < π / 2 := by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]
  exact angle_add_lt_pi_div_two_of_inner_eq_zero h h0

/--
theorem `cos_angle_sub_of_inner_eq_zero` / 定理 `cos_angle_sub_of_inner_eq_zero`

English:
theorem cos_angle_sub_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0)
  proof: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [cos_angle_add_of_inner_eq_zero h]

中文:
定理 cos_angle_sub_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0)
  证明: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [cos_angle_add_of_inner_eq_zero h]

Depends on / 依赖: cos_angle_add_of_inner_eq_zero, inner_neg_right, neg_eq_zero, sub_eq_add_neg
-/
theorem cos_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.cos (angle x (x - y)) = ‖x‖ / ‖x - y‖ := by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [cos_angle_add_of_inner_eq_zero h]

/--
theorem `sin_angle_sub_of_inner_eq_zero` / 定理 `sin_angle_sub_of_inner_eq_zero`

English:
theorem sin_angle_sub_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0)
  proof: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [or_comm]; rw [← neg_ne_zero]; rw [or_comm] at h0
  rw [sub_eq_add_neg]; rw [sin_angle_add_of_inner_eq_zero h h0]; rw [norm_neg]

中文:
定理 sin_angle_sub_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0)
  证明: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [or_comm]; rw [← neg_ne_zero]; rw [or_comm] at h0
  rw [sub_eq_add_neg]; rw [sin_angle_add_of_inner_eq_zero h h0]; rw [norm_neg]

Depends on / 依赖: inner_neg_right, neg_eq_zero, neg_ne_zero, norm_neg, or_comm, sin_angle_add_of_inner_eq_zero, sub_eq_add_neg
-/
theorem sin_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0) :
    Real.sin (angle x (x - y)) = ‖y‖ / ‖x - y‖ := by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [or_comm]; rw [← neg_ne_zero]; rw [or_comm] at h0
  rw [sub_eq_add_neg]; rw [sin_angle_add_of_inner_eq_zero h h0]; rw [norm_neg]

/--
theorem `tan_angle_sub_of_inner_eq_zero` / 定理 `tan_angle_sub_of_inner_eq_zero`

English:
theorem tan_angle_sub_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0)
  proof: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [tan_angle_add_of_inner_eq_zero h]; rw [norm_neg]

中文:
定理 tan_angle_sub_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0)
  证明: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [tan_angle_add_of_inner_eq_zero h]; rw [norm_neg]

Depends on / 依赖: inner_neg_right, neg_eq_zero, norm_neg, sub_eq_add_neg, tan_angle_add_of_inner_eq_zero
-/
theorem tan_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.tan (angle x (x - y)) = ‖y‖ / ‖x‖ := by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [tan_angle_add_of_inner_eq_zero h]; rw [norm_neg]

/--
theorem `cos_angle_sub_mul_norm_of_inner_eq_zero` / 定理 `cos_angle_sub_mul_norm_of_inner_eq_zero`

English:
theorem cos_angle_sub_mul_norm_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0)
  proof: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [cos_angle_add_mul_norm_of_inner_eq_zero h]

中文:
定理 cos_angle_sub_mul_norm_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0)
  证明: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [cos_angle_add_mul_norm_of_inner_eq_zero h]

Depends on / 依赖: cos_angle_add_mul_norm_of_inner_eq_zero, inner_neg_right, neg_eq_zero, sub_eq_add_neg
-/
theorem cos_angle_sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.cos (angle x (x - y)) * ‖x - y‖ = ‖x‖ := by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [cos_angle_add_mul_norm_of_inner_eq_zero h]

/--
theorem `sin_angle_sub_mul_norm_of_inner_eq_zero` / 定理 `sin_angle_sub_mul_norm_of_inner_eq_zero`

English:
theorem sin_angle_sub_mul_norm_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0)
  proof: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [sin_angle_add_mul_norm_of_inner_eq_zero h]; rw [norm_neg]

中文:
定理 sin_angle_sub_mul_norm_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0)
  证明: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [sin_angle_add_mul_norm_of_inner_eq_zero h]; rw [norm_neg]

Depends on / 依赖: inner_neg_right, neg_eq_zero, norm_neg, sin_angle_add_mul_norm_of_inner_eq_zero, sub_eq_add_neg
-/
theorem sin_angle_sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.sin (angle x (x - y)) * ‖x - y‖ = ‖y‖ := by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [sub_eq_add_neg]; rw [sin_angle_add_mul_norm_of_inner_eq_zero h]; rw [norm_neg]

/--
theorem `tan_angle_sub_mul_norm_of_inner_eq_zero` / 定理 `tan_angle_sub_mul_norm_of_inner_eq_zero`

English:
theorem tan_angle_sub_mul_norm_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0)
  proof: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [← neg_eq_zero] at h0
  rw [sub_eq_add_neg]; rw [tan_angle_add_mul_norm_of_inner_eq_zero h h0]; rw [norm_neg]

中文:
定理 tan_angle_sub_mul_norm_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0)
  证明: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [← neg_eq_zero] at h0
  rw [sub_eq_add_neg]; rw [tan_angle_add_mul_norm_of_inner_eq_zero h h0]; rw [norm_neg]

Depends on / 依赖: inner_neg_right, neg_eq_zero, norm_neg, sub_eq_add_neg, tan_angle_add_mul_norm_of_inner_eq_zero
-/
theorem tan_angle_sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0) :
    Real.tan (angle x (x - y)) * ‖x‖ = ‖y‖ := by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [← neg_eq_zero] at h0
  rw [sub_eq_add_neg]; rw [tan_angle_add_mul_norm_of_inner_eq_zero h h0]; rw [norm_neg]

/--
theorem `norm_div_cos_angle_sub_of_inner_eq_zero` / 定理 `norm_div_cos_angle_sub_of_inner_eq_zero`

English:
theorem norm_div_cos_angle_sub_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0)
  proof: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [← neg_eq_zero] at h0
  rw [sub_eq_add_neg]; rw [norm_div_cos_angle_add_of_inner_eq_zero h h0]

中文:
定理 norm_div_cos_angle_sub_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0)
  证明: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [← neg_eq_zero] at h0
  rw [sub_eq_add_neg]; rw [norm_div_cos_angle_add_of_inner_eq_zero h h0]

Depends on / 依赖: inner_neg_right, neg_eq_zero, norm_div_cos_angle_add_of_inner_eq_zero, sub_eq_add_neg
-/
theorem norm_div_cos_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0) :
    ‖x‖ / Real.cos (angle x (x - y)) = ‖x - y‖ := by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [← neg_eq_zero] at h0
  rw [sub_eq_add_neg]; rw [norm_div_cos_angle_add_of_inner_eq_zero h h0]

/--
theorem `norm_div_sin_angle_sub_of_inner_eq_zero` / 定理 `norm_div_sin_angle_sub_of_inner_eq_zero`

English:
theorem norm_div_sin_angle_sub_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0)
  proof: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [← neg_ne_zero] at h0
  rw [sub_eq_add_neg]; rw [← norm_neg]; rw [norm_div_sin_angle_add_of_inner_eq_zero h h0]

中文:
定理 norm_div_sin_angle_sub_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0)
  证明: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [← neg_ne_zero] at h0
  rw [sub_eq_add_neg]; rw [← norm_neg]; rw [norm_div_sin_angle_add_of_inner_eq_zero h h0]

Depends on / 依赖: inner_neg_right, neg_eq_zero, neg_ne_zero, norm_div_sin_angle_add_of_inner_eq_zero, norm_neg, sub_eq_add_neg
-/
theorem norm_div_sin_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0) :
    ‖y‖ / Real.sin (angle x (x - y)) = ‖x - y‖ := by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [← neg_ne_zero] at h0
  rw [sub_eq_add_neg]; rw [← norm_neg]; rw [norm_div_sin_angle_add_of_inner_eq_zero h h0]

/--
theorem `norm_div_tan_angle_sub_of_inner_eq_zero` / 定理 `norm_div_tan_angle_sub_of_inner_eq_zero`

English:
theorem norm_div_tan_angle_sub_of_inner_eq_zero
  given: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0)
  proof: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [← neg_ne_zero] at h0
  rw [sub_eq_add_neg]; rw [← norm_neg]; rw [norm_div_tan_angle_add_of_inner_eq_zero h h0]

中文:
定理 norm_div_tan_angle_sub_of_inner_eq_zero
  条件: {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0)
  证明: by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [← neg_ne_zero] at h0
  rw [sub_eq_add_neg]; rw [← norm_neg]; rw [norm_div_tan_angle_add_of_inner_eq_zero h h0]

Depends on / 依赖: inner_neg_right, neg_eq_zero, neg_ne_zero, norm_div_tan_angle_add_of_inner_eq_zero, norm_neg, sub_eq_add_neg
-/
theorem norm_div_tan_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0) :
    ‖y‖ / Real.tan (angle x (x - y)) = ‖x‖ := by
  rw [← neg_eq_zero]; rw [← inner_neg_right] at h
  rw [← neg_ne_zero] at h0
  rw [sub_eq_add_neg]; rw [← norm_neg]; rw [norm_div_tan_angle_add_of_inner_eq_zero h h0]

end InnerProductGeometry

namespace EuclideanGeometry

open InnerProductGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P]

/--
theorem `dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two` / 定理 `dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two`

English:
theorem dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two
  given: (p₁ p₂ p₃ : P)
  proof: by
  rw [dist_comm p₃ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₂ p₃]; rw [angle]; rw [← norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two]; rw [vsub_sub_vsub_cancel_right p₁]; rw [← neg_vsub_eq_vsub_rev p₂ p₃]; rw [norm_neg]

中文:
定理 dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two
  条件: (p₁ p₂ p₃ : P)
  证明: by
  rw [dist_comm p₃ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₂ p₃]; rw [angle]; rw [← norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two]; rw [vsub_sub_vsub_cancel_right p₁]; rw [← neg_vsub_eq_vsub_rev p₂ p₃]; rw [norm_neg]

Depends on / 依赖: dist_comm, dist_eq_norm_vsub, neg_vsub_eq_vsub_rev, norm_neg, norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two, vsub_sub_vsub_cancel_right
-/
theorem dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two (p₁ p₂ p₃ : P) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ ↔
      ∠ p₁ p₂ p₃ = π / 2 := by
  rw [dist_comm p₃ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₂ p₃]; rw [angle]; rw [← norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two]; rw [vsub_sub_vsub_cancel_right p₁]; rw [← neg_vsub_eq_vsub_rev p₂ p₃]; rw [norm_neg]

/--
theorem `angle_eq_arccos_of_angle_eq_pi_div_two` / 定理 `angle_eq_arccos_of_angle_eq_pi_div_two`

English:
theorem angle_eq_arccos_of_angle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  proof: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [angle_add_eq_arccos_of_inner_eq_zero h]

中文:
定理 angle_eq_arccos_of_angle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  证明: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [angle_add_eq_arccos_of_inner_eq_zero h]

Depends on / 依赖: add_comm, angle_add_eq_arccos_of_inner_eq_zero, dist_eq_norm_vsub, inner_eq_zero_iff_angle_eq_pi_div_two, inner_neg_left, neg_eq_zero, neg_vsub_eq_vsub_rev, real_inner_comm, vsub_add_vsub_cancel
-/
theorem angle_eq_arccos_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    ∠ p₂ p₃ p₁ = Real.arccos (dist p₃ p₂ / dist p₁ p₃) := by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [angle_add_eq_arccos_of_inner_eq_zero h]

/--
theorem `angle_eq_arcsin_of_angle_eq_pi_div_two` / 定理 `angle_eq_arcsin_of_angle_eq_pi_div_two`

English:
theorem angle_eq_arcsin_of_angle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  proof: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [← @vsub_ne_zero V]; rw [@ne_comm _ p₃]; rw [← @vsub_ne_zero V _ _ _ p₂]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [angle_add_eq_arcsin_of_inner_eq_zero h h0]

中文:
定理 angle_eq_arcsin_of_angle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  证明: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [← @vsub_ne_zero V]; rw [@ne_comm _ p₃]; rw [← @vsub_ne_zero V _ _ _ p₂]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [angle_add_eq_arcsin_of_inner_eq_zero h h0]

Depends on / 依赖: add_comm, angle_add_eq_arcsin_of_inner_eq_zero, dist_eq_norm_vsub, inner_eq_zero_iff_angle_eq_pi_div_two, inner_neg_left, ne_comm, neg_eq_zero, neg_vsub_eq_vsub_rev, or_comm, real_inner_comm, vsub_add_vsub_cancel, vsub_ne_zero
-/
theorem angle_eq_arcsin_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ != p₂ ∨ p₃ != p₂) : ∠ p₂ p₃ p₁ = Real.arcsin (dist p₁ p₂ / dist p₁ p₃) := by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [← @vsub_ne_zero V]; rw [@ne_comm _ p₃]; rw [← @vsub_ne_zero V _ _ _ p₂]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [angle_add_eq_arcsin_of_inner_eq_zero h h0]

/--
theorem `angle_eq_arctan_of_angle_eq_pi_div_two` / 定理 `angle_eq_arctan_of_angle_eq_pi_div_two`

English:
theorem angle_eq_arctan_of_angle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  proof: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [ne_comm]; rw [← @vsub_ne_zero V] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [angle_add_eq_arctan_of_inner_eq_zero h h0]

中文:
定理 angle_eq_arctan_of_angle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  证明: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [ne_comm]; rw [← @vsub_ne_zero V] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [angle_add_eq_arctan_of_inner_eq_zero h h0]

Depends on / 依赖: add_comm, angle_add_eq_arctan_of_inner_eq_zero, dist_eq_norm_vsub, inner_eq_zero_iff_angle_eq_pi_div_two, inner_neg_left, ne_comm, neg_eq_zero, neg_vsub_eq_vsub_rev, real_inner_comm, vsub_add_vsub_cancel, vsub_ne_zero
-/
theorem angle_eq_arctan_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₃ != p₂) : ∠ p₂ p₃ p₁ = Real.arctan (dist p₁ p₂ / dist p₃ p₂) := by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [ne_comm]; rw [← @vsub_ne_zero V] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [angle_add_eq_arctan_of_inner_eq_zero h h0]

/--
theorem `angle_pos_of_angle_eq_pi_div_two` / 定理 `angle_pos_of_angle_eq_pi_div_two`

English:
theorem angle_pos_of_angle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  proof: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [← @vsub_ne_zero V]; rw [eq_comm]; rw [← @vsub_eq_zero_iff_eq V]; rw [or_comm] at h0
  rw [angle]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]
  exact angle_add_pos_of_inner_eq_zero h h0

中文:
定理 angle_pos_of_angle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  证明: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [← @vsub_ne_zero V]; rw [eq_comm]; rw [← @vsub_eq_zero_iff_eq V]; rw [or_comm] at h0
  rw [angle]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]
  exact angle_add_pos_of_inner_eq_zero h h0

Depends on / 依赖: add_comm, angle_add_pos_of_inner_eq_zero, eq_comm, inner_eq_zero_iff_angle_eq_pi_div_two, inner_neg_left, neg_eq_zero, neg_vsub_eq_vsub_rev, or_comm, real_inner_comm, vsub_add_vsub_cancel, vsub_eq_zero_iff_eq, vsub_ne_zero
-/
theorem angle_pos_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ != p₂ ∨ p₃ = p₂) : 0 < ∠ p₂ p₃ p₁ := by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [← @vsub_ne_zero V]; rw [eq_comm]; rw [← @vsub_eq_zero_iff_eq V]; rw [or_comm] at h0
  rw [angle]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]
  exact angle_add_pos_of_inner_eq_zero h h0

/--
theorem `angle_le_pi_div_two_of_angle_eq_pi_div_two` / 定理 `angle_le_pi_div_two_of_angle_eq_pi_div_two`

English:
theorem angle_le_pi_div_two_of_angle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  proof: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]
  exact angle_add_le_pi_div_two_of_inner_eq_zero h

中文:
定理 angle_le_pi_div_two_of_angle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  证明: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]
  exact angle_add_le_pi_div_two_of_inner_eq_zero h

Depends on / 依赖: add_comm, angle_add_le_pi_div_two_of_inner_eq_zero, inner_eq_zero_iff_angle_eq_pi_div_two, inner_neg_left, neg_eq_zero, neg_vsub_eq_vsub_rev, real_inner_comm, vsub_add_vsub_cancel
-/
theorem angle_le_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    ∠ p₂ p₃ p₁ <= π / 2 := by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]
  exact angle_add_le_pi_div_two_of_inner_eq_zero h

/--
theorem `angle_lt_pi_div_two_of_angle_eq_pi_div_two` / 定理 `angle_lt_pi_div_two_of_angle_eq_pi_div_two`

English:
theorem angle_lt_pi_div_two_of_angle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  proof: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [ne_comm]; rw [← @vsub_ne_zero V] at h0
  rw [angle]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]
  exact angle_add_lt_pi_div_two_of_inner_eq_zero h h0

中文:
定理 angle_lt_pi_div_two_of_angle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  证明: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [ne_comm]; rw [← @vsub_ne_zero V] at h0
  rw [angle]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]
  exact angle_add_lt_pi_div_two_of_inner_eq_zero h h0

Depends on / 依赖: add_comm, angle_add_lt_pi_div_two_of_inner_eq_zero, inner_eq_zero_iff_angle_eq_pi_div_two, inner_neg_left, ne_comm, neg_eq_zero, neg_vsub_eq_vsub_rev, real_inner_comm, vsub_add_vsub_cancel, vsub_ne_zero
-/
theorem angle_lt_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₃ != p₂) : ∠ p₂ p₃ p₁ < π / 2 := by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [ne_comm]; rw [← @vsub_ne_zero V] at h0
  rw [angle]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]
  exact angle_add_lt_pi_div_two_of_inner_eq_zero h h0

/--
theorem `cos_angle_of_angle_eq_pi_div_two` / 定理 `cos_angle_of_angle_eq_pi_div_two`

English:
theorem cos_angle_of_angle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  proof: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [cos_angle_add_of_inner_eq_zero h]

中文:
定理 cos_angle_of_angle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  证明: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [cos_angle_add_of_inner_eq_zero h]

Depends on / 依赖: add_comm, cos_angle_add_of_inner_eq_zero, dist_eq_norm_vsub, inner_eq_zero_iff_angle_eq_pi_div_two, inner_neg_left, neg_eq_zero, neg_vsub_eq_vsub_rev, real_inner_comm, vsub_add_vsub_cancel
-/
theorem cos_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    Real.cos (∠ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₃ := by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [cos_angle_add_of_inner_eq_zero h]

/--
theorem `sin_angle_of_angle_eq_pi_div_two` / 定理 `sin_angle_of_angle_eq_pi_div_two`

English:
theorem sin_angle_of_angle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  proof: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [← @vsub_ne_zero V]; rw [@ne_comm _ p₃]; rw [← @vsub_ne_zero V _ _ _ p₂]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [sin_angle_add_of_inner_eq_zero h h0]

中文:
定理 sin_angle_of_angle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  证明: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [← @vsub_ne_zero V]; rw [@ne_comm _ p₃]; rw [← @vsub_ne_zero V _ _ _ p₂]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [sin_angle_add_of_inner_eq_zero h h0]

Depends on / 依赖: add_comm, dist_eq_norm_vsub, inner_eq_zero_iff_angle_eq_pi_div_two, inner_neg_left, ne_comm, neg_eq_zero, neg_vsub_eq_vsub_rev, or_comm, real_inner_comm, sin_angle_add_of_inner_eq_zero, vsub_add_vsub_cancel, vsub_ne_zero
-/
theorem sin_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ != p₂ ∨ p₃ != p₂) : Real.sin (∠ p₂ p₃ p₁) = dist p₁ p₂ / dist p₁ p₃ := by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [← @vsub_ne_zero V]; rw [@ne_comm _ p₃]; rw [← @vsub_ne_zero V _ _ _ p₂]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [sin_angle_add_of_inner_eq_zero h h0]

/--
theorem `tan_angle_of_angle_eq_pi_div_two` / 定理 `tan_angle_of_angle_eq_pi_div_two`

English:
theorem tan_angle_of_angle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  proof: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [tan_angle_add_of_inner_eq_zero h]

中文:
定理 tan_angle_of_angle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  证明: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [tan_angle_add_of_inner_eq_zero h]

Depends on / 依赖: add_comm, dist_eq_norm_vsub, inner_eq_zero_iff_angle_eq_pi_div_two, inner_neg_left, neg_eq_zero, neg_vsub_eq_vsub_rev, real_inner_comm, tan_angle_add_of_inner_eq_zero, vsub_add_vsub_cancel
-/
theorem tan_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    Real.tan (∠ p₂ p₃ p₁) = dist p₁ p₂ / dist p₃ p₂ := by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [tan_angle_add_of_inner_eq_zero h]

/--
theorem `cos_angle_mul_dist_of_angle_eq_pi_div_two` / 定理 `cos_angle_mul_dist_of_angle_eq_pi_div_two`

English:
theorem cos_angle_mul_dist_of_angle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  proof: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [cos_angle_add_mul_norm_of_inner_eq_zero h]

中文:
定理 cos_angle_mul_dist_of_angle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  证明: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [cos_angle_add_mul_norm_of_inner_eq_zero h]

Depends on / 依赖: add_comm, cos_angle_add_mul_norm_of_inner_eq_zero, dist_eq_norm_vsub, inner_eq_zero_iff_angle_eq_pi_div_two, inner_neg_left, neg_eq_zero, neg_vsub_eq_vsub_rev, real_inner_comm, vsub_add_vsub_cancel
-/
theorem cos_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    Real.cos (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂ := by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [cos_angle_add_mul_norm_of_inner_eq_zero h]

/--
theorem `sin_angle_mul_dist_of_angle_eq_pi_div_two` / 定理 `sin_angle_mul_dist_of_angle_eq_pi_div_two`

English:
theorem sin_angle_mul_dist_of_angle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  proof: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [sin_angle_add_mul_norm_of_inner_eq_zero h]

中文:
定理 sin_angle_mul_dist_of_angle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  证明: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [sin_angle_add_mul_norm_of_inner_eq_zero h]

Depends on / 依赖: add_comm, dist_eq_norm_vsub, inner_eq_zero_iff_angle_eq_pi_div_two, inner_neg_left, neg_eq_zero, neg_vsub_eq_vsub_rev, real_inner_comm, sin_angle_add_mul_norm_of_inner_eq_zero, vsub_add_vsub_cancel
-/
theorem sin_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    Real.sin (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂ := by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [sin_angle_add_mul_norm_of_inner_eq_zero h]

/--
theorem `tan_angle_mul_dist_of_angle_eq_pi_div_two` / 定理 `tan_angle_mul_dist_of_angle_eq_pi_div_two`

English:
theorem tan_angle_mul_dist_of_angle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  proof: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [ne_comm]; rw [← @vsub_ne_zero V]; rw [← @vsub_eq_zero_iff_eq V]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [tan_angle_add_mul_norm_of_inner_eq_zero h h0]

中文:
定理 tan_angle_mul_dist_of_angle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  证明: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [ne_comm]; rw [← @vsub_ne_zero V]; rw [← @vsub_eq_zero_iff_eq V]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [tan_angle_add_mul_norm_of_inner_eq_zero h h0]

Depends on / 依赖: add_comm, dist_eq_norm_vsub, inner_eq_zero_iff_angle_eq_pi_div_two, inner_neg_left, ne_comm, neg_eq_zero, neg_vsub_eq_vsub_rev, or_comm, real_inner_comm, tan_angle_add_mul_norm_of_inner_eq_zero, vsub_add_vsub_cancel, vsub_eq_zero_iff_eq, vsub_ne_zero
-/
theorem tan_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ = p₂ ∨ p₃ != p₂) : Real.tan (∠ p₂ p₃ p₁) * dist p₃ p₂ = dist p₁ p₂ := by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [ne_comm]; rw [← @vsub_ne_zero V]; rw [← @vsub_eq_zero_iff_eq V]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [tan_angle_add_mul_norm_of_inner_eq_zero h h0]

/--
theorem `dist_div_cos_angle_of_angle_eq_pi_div_two` / 定理 `dist_div_cos_angle_of_angle_eq_pi_div_two`

English:
theorem dist_div_cos_angle_of_angle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  proof: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [ne_comm]; rw [← @vsub_ne_zero V]; rw [← @vsub_eq_zero_iff_eq V]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [norm_div_cos_angle_add_of_inner_eq_zero h h0]

中文:
定理 dist_div_cos_angle_of_angle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  证明: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [ne_comm]; rw [← @vsub_ne_zero V]; rw [← @vsub_eq_zero_iff_eq V]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [norm_div_cos_angle_add_of_inner_eq_zero h h0]

Depends on / 依赖: add_comm, dist_eq_norm_vsub, inner_eq_zero_iff_angle_eq_pi_div_two, inner_neg_left, ne_comm, neg_eq_zero, neg_vsub_eq_vsub_rev, norm_div_cos_angle_add_of_inner_eq_zero, or_comm, real_inner_comm, vsub_add_vsub_cancel, vsub_eq_zero_iff_eq, vsub_ne_zero
-/
theorem dist_div_cos_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ = p₂ ∨ p₃ != p₂) : dist p₃ p₂ / Real.cos (∠ p₂ p₃ p₁) = dist p₁ p₃ := by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [ne_comm]; rw [← @vsub_ne_zero V]; rw [← @vsub_eq_zero_iff_eq V]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [norm_div_cos_angle_add_of_inner_eq_zero h h0]

/--
theorem `dist_div_sin_angle_of_angle_eq_pi_div_two` / 定理 `dist_div_sin_angle_of_angle_eq_pi_div_two`

English:
theorem dist_div_sin_angle_of_angle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  proof: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [eq_comm]; rw [← @vsub_ne_zero V]; rw [← @vsub_eq_zero_iff_eq V]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [norm_div_sin_angle_add_of_inner_eq_zero h h0]

中文:
定理 dist_div_sin_angle_of_angle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  证明: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [eq_comm]; rw [← @vsub_ne_zero V]; rw [← @vsub_eq_zero_iff_eq V]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [norm_div_sin_angle_add_of_inner_eq_zero h h0]

Depends on / 依赖: add_comm, dist_eq_norm_vsub, eq_comm, inner_eq_zero_iff_angle_eq_pi_div_two, inner_neg_left, neg_eq_zero, neg_vsub_eq_vsub_rev, norm_div_sin_angle_add_of_inner_eq_zero, or_comm, real_inner_comm, vsub_add_vsub_cancel, vsub_eq_zero_iff_eq, vsub_ne_zero
-/
theorem dist_div_sin_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ != p₂ ∨ p₃ = p₂) : dist p₁ p₂ / Real.sin (∠ p₂ p₃ p₁) = dist p₁ p₃ := by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [eq_comm]; rw [← @vsub_ne_zero V]; rw [← @vsub_eq_zero_iff_eq V]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [norm_div_sin_angle_add_of_inner_eq_zero h h0]

/--
theorem `dist_div_tan_angle_of_angle_eq_pi_div_two` / 定理 `dist_div_tan_angle_of_angle_eq_pi_div_two`

English:
theorem dist_div_tan_angle_of_angle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  proof: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [eq_comm]; rw [← @vsub_ne_zero V]; rw [← @vsub_eq_zero_iff_eq V]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [norm_div_tan_angle_add_of_inner_eq_zero h h0]

中文:
定理 dist_div_tan_angle_of_angle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  证明: by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [eq_comm]; rw [← @vsub_ne_zero V]; rw [← @vsub_eq_zero_iff_eq V]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [norm_div_tan_angle_add_of_inner_eq_zero h h0]

Depends on / 依赖: add_comm, dist_eq_norm_vsub, eq_comm, inner_eq_zero_iff_angle_eq_pi_div_two, inner_neg_left, neg_eq_zero, neg_vsub_eq_vsub_rev, norm_div_tan_angle_add_of_inner_eq_zero, or_comm, real_inner_comm, vsub_add_vsub_cancel, vsub_eq_zero_iff_eq, vsub_ne_zero
-/
theorem dist_div_tan_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ != p₂ ∨ p₃ = p₂) : dist p₁ p₂ / Real.tan (∠ p₂ p₃ p₁) = dist p₃ p₂ := by
  rw [angle]; rw [← inner_eq_zero_iff_angle_eq_pi_div_two]; rw [real_inner_comm]; rw [← neg_eq_zero]; rw [←
    inner_neg_left]; rw [neg_vsub_eq_vsub_rev] at h
  rw [eq_comm]; rw [← @vsub_ne_zero V]; rw [← @vsub_eq_zero_iff_eq V]; rw [or_comm] at h0
  rw [angle]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub' V p₃ p₂]; rw [← vsub_add_vsub_cancel p₁ p₂ p₃]; rw [add_comm]; rw [norm_div_tan_angle_add_of_inner_eq_zero h h0]

end EuclideanGeometry
