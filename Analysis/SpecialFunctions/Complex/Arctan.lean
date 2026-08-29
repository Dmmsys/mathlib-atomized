/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Complex arctangent

This file defines the complex arctangent `Complex.arctan` as
$$\arctan z = -\frac i2 \log \frac{1 + zi}{1 - zi}$$
and shows that it extends `Real.arctan` to the complex plane. Its Taylor series expansion
$$\arctan z = \frac{(-1)^n}{2n + 1} z^{2n + 1},\ |z|<1$$
is proved in `Complex.hasSum_arctan`.
-/

@[expose] public section


namespace Complex

open scoped Real

/--
Definition of `arctan` / `arctan` 的定义

English:
definition arctan
  signature: (z : Complex)
  body: -I / 2 * log ((1 + z * I) / (1 - z * I))

中文:
定义 arctan
  签名: (z : 复形)
  定义体: -I / 2 * log ((1 + z * I) / (1 - z * I))
-/
noncomputable def arctan (z : Complex) : Complex := -I / 2 * log ((1 + z * I) / (1 - z * I))

/--
theorem `tan_arctan` / 定理 `tan_arctan`

English:
theorem tan_arctan
  given: {z : Complex} (h₁ : z != I) (h₂ : z != -I)
  statement: tan (arctan z) = z
  proof: by
  unfold tan sin cos
  rw [div_div_eq_mul_div]; rw [div_mul_cancel₀ _ two_ne_zero]; rw [← div_mul_eq_mul_div]; rw [-- multiply top and bottom by `exp (arctan z * I)`
    ← mul_div_mul_right _ _ (exp_ne_zero (arctan z * I))]; rw [sub_mul]; rw [add_mul]; rw [← exp_add]; rw [neg_mul]; rw [neg_add_cancel]; rw [exp_zero]; rw [← exp_add]; rw [← two_mul]
  have z₁ : 1 + z * I != 0 := by
    contrapose h₁
    rw [add_eq_zero_iff_neg_eq]; rw [← div_eq_iff I_ne_zero]; rw [div_I]; rw [neg_one_mul]; rw [neg_neg] at h₁
    exact h₁.symm
  have z₂ : 1 - z * I != 0 := by
    contrapose h₂
    rw [sub_eq_zero]; rw [← div_eq_iff I_ne_zero]; rw [div_I]; rw [one_mul] at h₂
    exact h₂.symm
  have key : exp (2 * (arctan z * I)) = (1 + z * I) / (1 - z * I) := by
    rw [arctan]; rw [← mul_rotate]; rw [← mul_assoc]; rw [show 2 * (I * (-I / 2)) = 1 by simp [field], one_mul, exp_log]
    · exact div_ne_zero z₁ z₂
  -- multiply top and bottom by `1 - z * I`
  rw [key]; rw [← mul_div_mul_right _ _ z₂]; rw [sub_mul]; rw [add_mul]; rw [div_mul_cancel₀ _ z₂]; rw [one_mul]; rw [show _ / _ * I = -(I * I) * z by ring]; rw [I_mul_I]; rw [neg_neg]; rw [one_mul]

中文:
定理 tan_arctan
  条件: {z : 复形} (h₁ : z != I) (h₂ : z != -I)
  结论: tan (arctan z) = z
  证明: by
  unfold tan sin cos
  rw [div_div_eq_mul_div]; rw [div_mul_cancel₀ _ two_ne_zero]; rw [← div_mul_eq_mul_div]; rw [-- multiply top and bottom by `exp (arctan z * I)`
    ← mul_div_mul_right _ _ (exp_ne_zero (arctan z * I))]; rw [sub_mul]; rw [add_mul]; rw [← exp_add]; rw [neg_mul]; rw [neg_add_cancel]; rw [exp_zero]; rw [← exp_add]; rw [← two_mul]
  have z₁ : 1 + z * I != 0 := by
    contrapose h₁
    rw [add_eq_zero_iff_neg_eq]; rw [← div_eq_iff I_ne_zero]; rw [div_I]; rw [neg_one_mul]; rw [neg_neg] at h₁
    exact h₁.symm
  have z₂ : 1 - z * I != 0 := by
    contrapose h₂
    rw [sub_eq_zero]; rw [← div_eq_iff I_ne_zero]; rw [div_I]; rw [one_mul] at h₂
    exact h₂.symm
  have key : exp (2 * (arctan z * I)) = (1 + z * I) / (1 - z * I) := by
    rw [arctan]; rw [← mul_rotate]; rw [← mul_assoc]; rw [show 2 * (I * (-I / 2)) = 1 by simp [field], one_mul, exp_log]
    · exact div_ne_zero z₁ z₂
  -- multiply top and bottom by `1 - z * I`
  rw [key]; rw [← mul_div_mul_right _ _ z₂]; rw [sub_mul]; rw [add_mul]; rw [div_mul_cancel₀ _ z₂]; rw [one_mul]; rw [show _ / _ * I = -(I * I) * z by ring]; rw [I_mul_I]; rw [neg_neg]; rw [one_mul]

Depends on / 依赖: I_ne_zero, add_eq_zero_iff_neg_eq, add_mul, arctan, bottom, contrapose, div_I, div_div_eq_mul_div, div_eq_iff, div_mul_eq_mul_div, exp_add, exp_ne_zero, exp_zero, mul_div_mul_right, multiply, neg_add_cancel, neg_mul, neg_neg, neg_one_mul, sub_mul
-/
theorem tan_arctan {z : Complex} (h₁ : z != I) (h₂ : z != -I) : tan (arctan z) = z := by
  unfold tan sin cos
  rw [div_div_eq_mul_div]; rw [div_mul_cancel₀ _ two_ne_zero]; rw [← div_mul_eq_mul_div]; rw [-- multiply top and bottom by `exp (arctan z * I)`
    ← mul_div_mul_right _ _ (exp_ne_zero (arctan z * I))]; rw [sub_mul]; rw [add_mul]; rw [← exp_add]; rw [neg_mul]; rw [neg_add_cancel]; rw [exp_zero]; rw [← exp_add]; rw [← two_mul]
  have z₁ : 1 + z * I != 0 := by
    contrapose h₁
    rw [add_eq_zero_iff_neg_eq]; rw [← div_eq_iff I_ne_zero]; rw [div_I]; rw [neg_one_mul]; rw [neg_neg] at h₁
    exact h₁.symm
  have z₂ : 1 - z * I != 0 := by
    contrapose h₂
    rw [sub_eq_zero]; rw [← div_eq_iff I_ne_zero]; rw [div_I]; rw [one_mul] at h₂
    exact h₂.symm
  have key : exp (2 * (arctan z * I)) = (1 + z * I) / (1 - z * I) := by
    rw [arctan]; rw [← mul_rotate]; rw [← mul_assoc]; rw [show 2 * (I * (-I / 2)) = 1 by simp [field], one_mul, exp_log]
    · exact div_ne_zero z₁ z₂
  -- multiply top and bottom by `1 - z * I`
  rw [key]; rw [← mul_div_mul_right _ _ z₂]; rw [sub_mul]; rw [add_mul]; rw [div_mul_cancel₀ _ z₂]; rw [one_mul]; rw [show _ / _ * I = -(I * I) * z by ring]; rw [I_mul_I]; rw [neg_neg]; rw [one_mul]

/--
lemma `cos_ne_zero_of_arctan_bounds` / 引理 `cos_ne_zero_of_arctan_bounds`

English:
lemma cos_ne_zero_of_arctan_bounds
  statement: {z : Complex} (h₀ : z != π / 2) (h₁ : -(π / 2) < z.re)
  proof: by
  refine cos_ne_zero_iff.mpr (fun k => ?_)
  rw [ne_eq]; rw [Complex.ext_iff]; rw [not_and_or] at h₀ ⊢
  norm_cast at h₀ ⊢
  rcases h₀ with nr | ni
  · left; contrapose nr
    rw [nr]; rw [mul_div_assoc]; rw [neg_eq_neg_one_mul]; rw [mul_lt_mul_iff_of_pos_right (by positivity)] at h₁
    rw [nr]; rw [← one_mul (π / 2)]; rw [mul_div_assoc]; rw [mul_le_mul_iff_of_pos_right (by positivity)] at h₂
    norm_cast at h₁ h₂
    change -1 < _ at h₁
    rwa [show 2 * k + 1 = 1 by lia, Int.cast_one, one_mul] at nr
  · exact Or.inr ni

中文:
引理 cos_ne_zero_of_arctan_bounds
  结论: {z : 复形} (h₀ : z != π / 2) (h₁ : -(π / 2) < z.re)
  证明: by
  refine cos_ne_zero_iff.mpr (fun k => ?_)
  rw [ne_eq]; rw [Complex.ext_iff]; rw [not_and_or] at h₀ ⊢
  norm_cast at h₀ ⊢
  rcases h₀ with nr | ni
  · left; contrapose nr
    rw [nr]; rw [mul_div_assoc]; rw [neg_eq_neg_one_mul]; rw [mul_lt_mul_iff_of_pos_right (by positivity)] at h₁
    rw [nr]; rw [← one_mul (π / 2)]; rw [mul_div_assoc]; rw [mul_le_mul_iff_of_pos_right (by positivity)] at h₂
    norm_cast at h₁ h₂
    change -1 < _ at h₁
    rwa [show 2 * k + 1 = 1 by lia, Int.cast_one, one_mul] at nr
  · exact Or.inr ni

Depends on / 依赖: Complex.ext_iff, Int.cast_one, Or.inr, cast_one, contrapose, cos_ne_zero_iff, cos_ne_zero_iff.mpr, ext_iff, mul_div_assoc, mul_le_mul_iff_of_pos_right, mul_lt_mul_iff_of_pos_right, ne_eq, neg_eq_neg_one_mul, not_and_or, one_mul
-/
lemma cos_ne_zero_of_arctan_bounds {z : Complex} (h₀ : z != π / 2) (h₁ : -(π / 2) < z.re)
    (h₂ : z.re <= π / 2) : cos z != 0 := by
  refine cos_ne_zero_iff.mpr (fun k => ?_)
  rw [ne_eq]; rw [Complex.ext_iff]; rw [not_and_or] at h₀ ⊢
  norm_cast at h₀ ⊢
  rcases h₀ with nr | ni
  · left; contrapose nr
    rw [nr]; rw [mul_div_assoc]; rw [neg_eq_neg_one_mul]; rw [mul_lt_mul_iff_of_pos_right (by positivity)] at h₁
    rw [nr]; rw [← one_mul (π / 2)]; rw [mul_div_assoc]; rw [mul_le_mul_iff_of_pos_right (by positivity)] at h₂
    norm_cast at h₁ h₂
    change -1 < _ at h₁
    rwa [show 2 * k + 1 = 1 by lia, Int.cast_one, one_mul] at nr
  · exact Or.inr ni

set_option linter.flexible false in -- TODO: fix non-terminal simp
/--
theorem `arctan_tan` / 定理 `arctan_tan`

English:
theorem arctan_tan
  given: {z : Complex} (h₀ : z != π / 2) (h₁ : -(π / 2) < z.re) (h₂ : z.re <= π / 2)
  proof: by
  have h := cos_ne_zero_of_arctan_bounds h₀ h₁ h₂
  unfold arctan tan
  -- multiply top and bottom by `cos z`
  rw [← mul_div_mul_right (1 + _) _ h]; rw [add_mul]; rw [sub_mul]; rw [one_mul]; rw [← mul_rotate]; rw [mul_div_cancel₀ _ h]
  conv_lhs =>
    enter [2, 1, 2]
    rw [sub_eq_add_neg]; rw [← neg_mul]; rw [← sin_neg]; rw [← cos_neg]
  rw [← exp_mul_I]; rw [← exp_mul_I]; rw [← exp_sub]; rw [show z * I - -z * I = 2 * (I * z) by ring]; rw [log_exp]; rw [show -I / 2 * (2 * (I * z)) = -(I * I) * z by ring]; rw [I_mul_I]; rw [neg_neg]; rw [one_mul]
  all_goals simp
  · rwa [← div_lt_iff₀' two_pos, neg_div]
  · rwa [← le_div_iff₀' two_pos]

@[simp, norm_cast]

中文:
定理 arctan_tan
  条件: {z : 复形} (h₀ : z != π / 2) (h₁ : -(π / 2) < z.re) (h₂ : z.re <= π / 2)
  证明: by
  have h := cos_ne_zero_of_arctan_bounds h₀ h₁ h₂
  unfold arctan tan
  -- multiply top and bottom by `cos z`
  rw [← mul_div_mul_right (1 + _) _ h]; rw [add_mul]; rw [sub_mul]; rw [one_mul]; rw [← mul_rotate]; rw [mul_div_cancel₀ _ h]
  conv_lhs =>
    enter [2, 1, 2]
    rw [sub_eq_add_neg]; rw [← neg_mul]; rw [← sin_neg]; rw [← cos_neg]
  rw [← exp_mul_I]; rw [← exp_mul_I]; rw [← exp_sub]; rw [show z * I - -z * I = 2 * (I * z) by ring]; rw [log_exp]; rw [show -I / 2 * (2 * (I * z)) = -(I * I) * z by ring]; rw [I_mul_I]; rw [neg_neg]; rw [one_mul]
  all_goals simp
  · rwa [← div_lt_iff₀' two_pos, neg_div]
  · rwa [← le_div_iff₀' two_pos]

@[simp, norm_cast]

Depends on / 依赖: arctan, cos_ne_zero_of_arctan_bounds
-/
theorem arctan_tan {z : Complex} (h₀ : z != π / 2) (h₁ : -(π / 2) < z.re) (h₂ : z.re <= π / 2) :
    arctan (tan z) = z := by
  have h := cos_ne_zero_of_arctan_bounds h₀ h₁ h₂
  unfold arctan tan
  -- multiply top and bottom by `cos z`
  rw [← mul_div_mul_right (1 + _) _ h]; rw [add_mul]; rw [sub_mul]; rw [one_mul]; rw [← mul_rotate]; rw [mul_div_cancel₀ _ h]
  conv_lhs =>
    enter [2, 1, 2]
    rw [sub_eq_add_neg]; rw [← neg_mul]; rw [← sin_neg]; rw [← cos_neg]
  rw [← exp_mul_I]; rw [← exp_mul_I]; rw [← exp_sub]; rw [show z * I - -z * I = 2 * (I * z) by ring]; rw [log_exp]; rw [show -I / 2 * (2 * (I * z)) = -(I * I) * z by ring]; rw [I_mul_I]; rw [neg_neg]; rw [one_mul]
  all_goals simp
  · rwa [← div_lt_iff₀' two_pos, neg_div]
  · rwa [← le_div_iff₀' two_pos]

@[simp, norm_cast]
/--
theorem `ofReal_arctan` / 定理 `ofReal_arctan`

English:
theorem ofReal_arctan
  given: (x : Real)
  statement: (Real.arctan x : Complex) = arctan x
  proof: by
  conv_rhs => rw [← Real.tan_arctan x]
  rw [ofReal_tan]; rw [arctan_tan]
  all_goals norm_cast
  · rw [← ne_eq]; exact (Real.arctan_lt_pi_div_two _).ne
  · exact Real.neg_pi_div_two_lt_arctan _
  · exact (Real.arctan_lt_pi_div_two _).le

中文:
定理 of实数_arctan
  条件: (x : 实数)
  结论: (实数.arctan x : 复形) = arctan x
  证明: by
  conv_rhs => rw [← Real.tan_arctan x]
  rw [ofReal_tan]; rw [arctan_tan]
  all_goals norm_cast
  · rw [← ne_eq]; exact (Real.arctan_lt_pi_div_two _).ne
  · exact Real.neg_pi_div_two_lt_arctan _
  · exact (Real.arctan_lt_pi_div_two _).le

Depends on / 依赖: Real.arctan_lt_pi_div_two, Real.neg_pi_div_two_lt_arctan, Real.tan_arctan, all_goals, arctan_lt_pi_div_two, arctan_tan, conv_rhs, ne_eq, neg_pi_div_two_lt_arctan, ofReal_tan, tan_arctan
-/
theorem ofReal_arctan (x : Real) : (Real.arctan x : Complex) = arctan x := by
  conv_rhs => rw [← Real.tan_arctan x]
  rw [ofReal_tan]; rw [arctan_tan]
  all_goals norm_cast
  · rw [← ne_eq]; exact (Real.arctan_lt_pi_div_two _).ne
  · exact Real.neg_pi_div_two_lt_arctan _
  · exact (Real.arctan_lt_pi_div_two _).le

/--
lemma `arg_one_add_mem_Ioo` / 引理 `arg_one_add_mem_Ioo`

English:
lemma arg_one_add_mem_Ioo
  given: {z : Complex} (hz : ‖z‖ < 1)
  statement: (1 + z).arg in Set.Ioo (-(π / 2)) (π / 2)
  proof: by
  rw [Set.mem_Ioo]; rw [← abs_lt]; rw [abs_arg_lt_pi_div_two_iff]; rw [add_re]; rw [one_re]; rw [← neg_lt_iff_pos_add']
  exact Or.inl (abs_lt.mp ((abs_re_le_norm z).trans_lt hz)).1

中文:
引理 arg_one_add_mem_Ioo
  条件: {z : 复形} (hz : ‖z‖ < 1)
  结论: (1 + z).arg in 集合.开区间 (-(π / 2)) (π / 2)
  证明: by
  rw [Set.mem_Ioo]; rw [← abs_lt]; rw [abs_arg_lt_pi_div_two_iff]; rw [add_re]; rw [one_re]; rw [← neg_lt_iff_pos_add']
  exact Or.inl (abs_lt.mp ((abs_re_le_norm z).trans_lt hz)).1

Depends on / 依赖: Or.inl, Set.mem_Ioo, abs_arg_lt_pi_div_two_iff, abs_lt, abs_lt.mp, abs_re_le_norm, add_re, mem_Ioo, neg_lt_iff_pos_add, one_re, trans_lt
-/
lemma arg_one_add_mem_Ioo {z : Complex} (hz : ‖z‖ < 1) : (1 + z).arg in Set.Ioo (-(π / 2)) (π / 2) := by
  rw [Set.mem_Ioo]; rw [← abs_lt]; rw [abs_arg_lt_pi_div_two_iff]; rw [add_re]; rw [one_re]; rw [← neg_lt_iff_pos_add']
  exact Or.inl (abs_lt.mp ((abs_re_le_norm z).trans_lt hz)).1

/--
lemma `hasSum_arctan_aux` / 引理 `hasSum_arctan_aux`

English:
lemma hasSum_arctan_aux
  given: {z : Complex} (hz : ‖z‖ < 1)
  proof: by
  have z₁ := mem_slitPlane_iff_arg.mp (mem_slitPlane_of_norm_lt_one (z := z * I) (by simpa))
  have z₂ := mem_slitPlane_iff_arg.mp (mem_slitPlane_of_norm_lt_one (z := -(z * I)) (by simpa))
  rw [← sub_eq_add_neg] at z₂
  rw [← log_inv _ z₂.1]; rw [← (log_mul_eq_add_log_iff z₁.2 (inv_eq_zero.ne.mpr z₂.2)).mpr]; rw [div_eq_mul_inv]
  -- `log_mul_eq_add_log_iff` requires a bound on `arg (1 + z * I) + arg (1 - z * I)⁻¹`.
  -- `arg_one_add_mem_Ioo` provides sufficiently tight bounds on both terms
  have b₁ := arg_one_add_mem_Ioo (z := z * I) (by simpa)
  have b₂ : arg (1 - z * I)⁻¹ in Set.Ioo (-(π / 2)) (π / 2) := by
    simp_rw [arg_inv, z₂.1, ite_false, Set.neg_mem_Ioo_iff, neg_neg, sub_eq_add_neg]
    exact arg_one_add_mem_Ioo (by simpa)
  have c₁ := add_lt_add b₁.1 b₂.1
  have c₂ := add_lt_add b₁.2 b₂.2
  rw [show -(π / 2) + -(π / 2) = -π by ring] at c₁
  rw [show π / 2 + π / 2 = π by ring] at c₂
  exact ⟨c₁, c₂.le⟩

中文:
引理 hasSum_arctan_aux
  条件: {z : 复形} (hz : ‖z‖ < 1)
  证明: by
  have z₁ := mem_slitPlane_iff_arg.mp (mem_slitPlane_of_norm_lt_one (z := z * I) (by simpa))
  have z₂ := mem_slitPlane_iff_arg.mp (mem_slitPlane_of_norm_lt_one (z := -(z * I)) (by simpa))
  rw [← sub_eq_add_neg] at z₂
  rw [← log_inv _ z₂.1]; rw [← (log_mul_eq_add_log_iff z₁.2 (inv_eq_zero.ne.mpr z₂.2)).mpr]; rw [div_eq_mul_inv]
  -- `log_mul_eq_add_log_iff` requires a bound on `arg (1 + z * I) + arg (1 - z * I)⁻¹`.
  -- `arg_one_add_mem_Ioo` provides sufficiently tight bounds on both terms
  have b₁ := arg_one_add_mem_Ioo (z := z * I) (by simpa)
  have b₂ : arg (1 - z * I)⁻¹ in Set.Ioo (-(π / 2)) (π / 2) := by
    simp_rw [arg_inv, z₂.1, ite_false, Set.neg_mem_Ioo_iff, neg_neg, sub_eq_add_neg]
    exact arg_one_add_mem_Ioo (by simpa)
  have c₁ := add_lt_add b₁.1 b₂.1
  have c₂ := add_lt_add b₁.2 b₂.2
  rw [show -(π / 2) + -(π / 2) = -π by ring] at c₁
  rw [show π / 2 + π / 2 = π by ring] at c₂
  exact ⟨c₁, c₂.le⟩

Depends on / 依赖: div_eq_mul_inv, inv_eq_zero, inv_eq_zero.ne.mpr, log_inv, log_mul_eq_add_log_iff, mem_slitPlane_iff_arg, mem_slitPlane_iff_arg.mp, mem_slitPlane_of_norm_lt_one, sub_eq_add_neg
-/
lemma hasSum_arctan_aux {z : Complex} (hz : ‖z‖ < 1) :
    log (1 + z * I) + -log (1 - z * I) = log ((1 + z * I) / (1 - z * I)) := by
  have z₁ := mem_slitPlane_iff_arg.mp (mem_slitPlane_of_norm_lt_one (z := z * I) (by simpa))
  have z₂ := mem_slitPlane_iff_arg.mp (mem_slitPlane_of_norm_lt_one (z := -(z * I)) (by simpa))
  rw [← sub_eq_add_neg] at z₂
  rw [← log_inv _ z₂.1]; rw [← (log_mul_eq_add_log_iff z₁.2 (inv_eq_zero.ne.mpr z₂.2)).mpr]; rw [div_eq_mul_inv]
  -- `log_mul_eq_add_log_iff` requires a bound on `arg (1 + z * I) + arg (1 - z * I)⁻¹`.
  -- `arg_one_add_mem_Ioo` provides sufficiently tight bounds on both terms
  have b₁ := arg_one_add_mem_Ioo (z := z * I) (by simpa)
  have b₂ : arg (1 - z * I)⁻¹ in Set.Ioo (-(π / 2)) (π / 2) := by
    simp_rw [arg_inv, z₂.1, ite_false, Set.neg_mem_Ioo_iff, neg_neg, sub_eq_add_neg]
    exact arg_one_add_mem_Ioo (by simpa)
  have c₁ := add_lt_add b₁.1 b₂.1
  have c₂ := add_lt_add b₁.2 b₂.2
  rw [show -(π / 2) + -(π / 2) = -π by ring] at c₁
  rw [show π / 2 + π / 2 = π by ring] at c₂
  exact ⟨c₁, c₂.le⟩

set_option backward.defeqAttrib.useBackward true in
/--
theorem `hasSum_arctan` / 定理 `hasSum_arctan`

English:
theorem hasSum_arctan
  given: {z : Complex} (hz : ‖z‖ < 1)
  proof: by
  have := ((hasSum_taylorSeries_log (z := z * I) (by simpa)).add
    (hasSum_taylorSeries_neg_log (z := z * I) (by simpa))).mul_left (-I / 2)
  simp_rw [← add_div, ← add_one_mul, hasSum_arctan_aux hz] at this
  replace := (Nat.divModEquiv 2).symm.hasSum_iff.mpr this
  dsimp [Function.comp_def] at this
  simp_rw [← mul_comm 2 _] at this
  refine this.prod_fiberwise fun k => ?_
  dsimp only
  convert! hasSum_fintype (_ : Fin 2 -> Complex) using 1
  rw [Fin.sum_univ_two]; rw [Fin.val_zero]; rw [Fin.val_one]; rw [Odd.neg_one_pow (n := 2 * k + 0 + 1) (by simp)]; rw [neg_add_cancel]; rw [zero_mul]; rw [zero_div]; rw [mul_zero]; rw [zero_add]; rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]; rw [Even.neg_one_pow (n := 2 * (k + 1)) (by simp)]; rw [← mul_div_assoc (_ / _)]; rw [← mul_assoc]; rw [show -I / 2 * (1 + 1) = -I by ring]
  congr 1
  rw [mul_pow]; rw [pow_succ' I]; rw [pow_mul]; rw [I_sq]; rw [show -I * _ = -(I * I) * (-1) ^ k * z ^ (2 * k + 1) by ring]; rw [I_mul_I]; rw [neg_neg]; rw [one_mul]

中文:
定理 hasSum_arctan
  条件: {z : 复形} (hz : ‖z‖ < 1)
  证明: by
  have := ((hasSum_taylorSeries_log (z := z * I) (by simpa)).add
    (hasSum_taylorSeries_neg_log (z := z * I) (by simpa))).mul_left (-I / 2)
  simp_rw [← add_div, ← add_one_mul, hasSum_arctan_aux hz] at this
  replace := (Nat.divModEquiv 2).symm.hasSum_iff.mpr this
  dsimp [Function.comp_def] at this
  simp_rw [← mul_comm 2 _] at this
  refine this.prod_fiberwise fun k => ?_
  dsimp only
  convert! hasSum_fintype (_ : Fin 2 -> Complex) using 1
  rw [Fin.sum_univ_two]; rw [Fin.val_zero]; rw [Fin.val_one]; rw [Odd.neg_one_pow (n := 2 * k + 0 + 1) (by simp)]; rw [neg_add_cancel]; rw [zero_mul]; rw [zero_div]; rw [mul_zero]; rw [zero_add]; rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]; rw [Even.neg_one_pow (n := 2 * (k + 1)) (by simp)]; rw [← mul_div_assoc (_ / _)]; rw [← mul_assoc]; rw [show -I / 2 * (1 + 1) = -I by ring]
  congr 1
  rw [mul_pow]; rw [pow_succ' I]; rw [pow_mul]; rw [I_sq]; rw [show -I * _ = -(I * I) * (-1) ^ k * z ^ (2 * k + 1) by ring]; rw [I_mul_I]; rw [neg_neg]; rw [one_mul]

Depends on / 依赖: Fin.sum_univ_two, Fin.val_one, Fin.val_zero, Function, Function.comp_def, Nat.divModEquiv, add_div, add_one_mul, comp_def, convert, divModEquiv, hasSum_arctan_aux, hasSum_fintype, hasSum_iff, hasSum_taylorSeries_log, hasSum_taylorSeries_neg_log, mul_comm, mul_left, prod_fiberwise, replace
-/
theorem hasSum_arctan {z : Complex} (hz : ‖z‖ < 1) :
    HasSum (fun n : Nat => (-1) ^ n * z ^ (2 * n + 1) / ↑(2 * n + 1)) (arctan z) := by
  have := ((hasSum_taylorSeries_log (z := z * I) (by simpa)).add
    (hasSum_taylorSeries_neg_log (z := z * I) (by simpa))).mul_left (-I / 2)
  simp_rw [← add_div, ← add_one_mul, hasSum_arctan_aux hz] at this
  replace := (Nat.divModEquiv 2).symm.hasSum_iff.mpr this
  dsimp [Function.comp_def] at this
  simp_rw [← mul_comm 2 _] at this
  refine this.prod_fiberwise fun k => ?_
  dsimp only
  convert! hasSum_fintype (_ : Fin 2 -> Complex) using 1
  rw [Fin.sum_univ_two]; rw [Fin.val_zero]; rw [Fin.val_one]; rw [Odd.neg_one_pow (n := 2 * k + 0 + 1) (by simp)]; rw [neg_add_cancel]; rw [zero_mul]; rw [zero_div]; rw [mul_zero]; rw [zero_add]; rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]; rw [Even.neg_one_pow (n := 2 * (k + 1)) (by simp)]; rw [← mul_div_assoc (_ / _)]; rw [← mul_assoc]; rw [show -I / 2 * (1 + 1) = -I by ring]
  congr 1
  rw [mul_pow]; rw [pow_succ' I]; rw [pow_mul]; rw [I_sq]; rw [show -I * _ = -(I * I) * (-1) ^ k * z ^ (2 * k + 1) by ring]; rw [I_mul_I]; rw [neg_neg]; rw [one_mul]

end Complex

/--
theorem `Real.hasSum_arctan` / 定理 `Real.hasSum_arctan`

English:
theorem Real.hasSum_arctan
  given: {x : Real} (hx : ‖x‖ < 1)
  proof: mod_cast Complex.hasSum_arctan (z := x) (by simpa)

中文:
定理 实数.hasSum_arctan
  条件: {x : 实数} (hx : ‖x‖ < 1)
  证明: mod_cast Complex.hasSum_arctan (z := x) (by simpa)

Depends on / 依赖: Complex.hasSum_arctan, hasSum_arctan, mod_cast
-/
theorem Real.hasSum_arctan {x : Real} (hx : ‖x‖ < 1) :
    HasSum (fun n : Nat => (-1) ^ n * x ^ (2 * n + 1) / ↑(2 * n + 1)) (arctan x) :=
  mod_cast Complex.hasSum_arctan (z := x) (by simpa)
