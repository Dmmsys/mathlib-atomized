/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Joseph Myers
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bounds on specific values of the exponential
-/

public section


namespace Real

open IsAbsoluteValue Finset CauSeq Complex

/--
theorem `exp_one_near_10` / 定理 `exp_one_near_10`

English:
theorem exp_one_near_10
  statement: |exp 1 - 2244083 / 825552| <= 1 / 10 ^ 10
  proof: by
  apply exp_approx_start
  iterate 13 refine exp_1_approx_succ_eq (by norm_num1; rfl) (by norm_cast) ?_
  refine exp_approx_end' _ (by norm_num1; rfl) _ (by norm_cast) (by simp) ?_
  norm_num1

中文:
定理 exp_one_near_10
  结论: |exp 1 - 2244083 / 825552| <= 1 / 10 ^ 10
  证明: by
  apply exp_approx_start
  iterate 13 refine exp_1_approx_succ_eq (by norm_num1; rfl) (by norm_cast) ?_
  refine exp_approx_end' _ (by norm_num1; rfl) _ (by norm_cast) (by simp) ?_
  norm_num1

Depends on / 依赖: exp_1_approx_succ_eq, exp_approx_end, exp_approx_start, iterate, norm_num1
-/
theorem exp_one_near_10 : |exp 1 - 2244083 / 825552| <= 1 / 10 ^ 10 := by
  apply exp_approx_start
  iterate 13 refine exp_1_approx_succ_eq (by norm_num1; rfl) (by norm_cast) ?_
  refine exp_approx_end' _ (by norm_num1; rfl) _ (by norm_cast) (by simp) ?_
  norm_num1

/--
theorem `exp_one_near_20` / 定理 `exp_one_near_20`

English:
theorem exp_one_near_20
  statement: |exp 1 - 363916618873 / 133877442384| <= 1 / 10 ^ 20
  proof: by
  apply exp_approx_start
  iterate 21 refine exp_1_approx_succ_eq (by norm_num1; rfl) (by norm_cast) ?_
  refine exp_approx_end' _ (by norm_num1; rfl) _ (by norm_cast) (by simp) ?_
  norm_num1

中文:
定理 exp_one_near_20
  结论: |exp 1 - 363916618873 / 133877442384| <= 1 / 10 ^ 20
  证明: by
  apply exp_approx_start
  iterate 21 refine exp_1_approx_succ_eq (by norm_num1; rfl) (by norm_cast) ?_
  refine exp_approx_end' _ (by norm_num1; rfl) _ (by norm_cast) (by simp) ?_
  norm_num1

Depends on / 依赖: exp_1_approx_succ_eq, exp_approx_end, exp_approx_start, iterate, norm_num1
-/
theorem exp_one_near_20 : |exp 1 - 363916618873 / 133877442384| <= 1 / 10 ^ 20 := by
  apply exp_approx_start
  iterate 21 refine exp_1_approx_succ_eq (by norm_num1; rfl) (by norm_cast) ?_
  refine exp_approx_end' _ (by norm_num1; rfl) _ (by norm_cast) (by simp) ?_
  norm_num1

/--
theorem `exp_one_gt_d9` / 定理 `exp_one_gt_d9`

English:
theorem exp_one_gt_d9
  statement: 2.7182818283 < exp 1
  proof: lt_of_lt_of_le (by norm_num) (sub_le_comm.1 (abs_sub_le_iff.1 exp_one_near_10).2)

中文:
定理 exp_one_gt_d9
  结论: 2.7182818283 < exp 1
  证明: lt_of_lt_of_le (by norm_num) (sub_le_comm.1 (abs_sub_le_iff.1 exp_one_near_10).2)

Depends on / 依赖: abs_sub_le_iff, exp_one_near_10, lt_of_lt_of_le, sub_le_comm
-/
theorem exp_one_gt_d9 : 2.7182818283 < exp 1 :=
  lt_of_lt_of_le (by norm_num) (sub_le_comm.1 (abs_sub_le_iff.1 exp_one_near_10).2)

/--
theorem `exp_one_lt_d9` / 定理 `exp_one_lt_d9`

English:
theorem exp_one_lt_d9
  statement: exp 1 < 2.7182818286
  proof: lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 exp_one_near_10).1) (by norm_num)

中文:
定理 exp_one_lt_d9
  结论: exp 1 < 2.7182818286
  证明: lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 exp_one_near_10).1) (by norm_num)

Depends on / 依赖: abs_sub_le_iff, exp_one_near_10, lt_of_le_of_lt, sub_le_iff_le_add
-/
theorem exp_one_lt_d9 : exp 1 < 2.7182818286 :=
  lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 exp_one_near_10).1) (by norm_num)

/--
theorem `exp_one_gt_two` / 定理 `exp_one_gt_two`

English:
theorem exp_one_gt_two
  statement: 2 < exp 1
  proof: lt_trans (by norm_num) exp_one_gt_d9

中文:
定理 exp_one_gt_two
  结论: 2 < exp 1
  证明: lt_trans (by norm_num) exp_one_gt_d9

Depends on / 依赖: exp_one_gt_d9, lt_trans
-/
theorem exp_one_gt_two : 2 < exp 1 :=
  lt_trans (by norm_num) exp_one_gt_d9

/--
theorem `exp_one_lt_three` / 定理 `exp_one_lt_three`

English:
theorem exp_one_lt_three
  statement: exp 1 < 3
  proof: lt_trans exp_one_lt_d9 (by norm_num)

中文:
定理 exp_one_lt_three
  结论: exp 1 < 3
  证明: lt_trans exp_one_lt_d9 (by norm_num)

Depends on / 依赖: exp_one_lt_d9, lt_trans
-/
theorem exp_one_lt_three : exp 1 < 3 :=
  lt_trans exp_one_lt_d9 (by norm_num)

/--
theorem `floor_exp_one_eq_two` / 定理 `floor_exp_one_eq_two`

English:
theorem floor_exp_one_eq_two
  statement: ⌊exp 1⌋ = 2
  proof: Int.floor_eq_iff.mpr ⟨exp_one_gt_two.le, by exact_mod_cast exp_one_lt_three⟩

中文:
定理 floor_exp_one_eq_two
  结论: ⌊exp 1⌋ = 2
  证明: Int.floor_eq_iff.mpr ⟨exp_one_gt_two.le, by exact_mod_cast exp_one_lt_three⟩

Depends on / 依赖: Int.floor_eq_iff.mpr, exp_one_gt_two, exp_one_gt_two.le, exp_one_lt_three, floor_eq_iff
-/
theorem floor_exp_one_eq_two : ⌊exp 1⌋ = 2 :=
  Int.floor_eq_iff.mpr ⟨exp_one_gt_two.le, by exact_mod_cast exp_one_lt_three⟩

/--
theorem `ceil_exp_one_eq_three` / 定理 `ceil_exp_one_eq_three`

English:
theorem ceil_exp_one_eq_three
  statement: ⌈exp 1⌉ = 3
  proof: Int.ceil_eq_iff.mpr ⟨by exact_mod_cast exp_one_gt_two, exp_one_lt_three.le⟩

中文:
定理 ceil_exp_one_eq_three
  结论: ⌈exp 1⌉ = 3
  证明: Int.ceil_eq_iff.mpr ⟨by exact_mod_cast exp_one_gt_two, exp_one_lt_three.le⟩

Depends on / 依赖: Int.ceil_eq_iff.mpr, ceil_eq_iff, exp_one_gt_two, exp_one_lt_three, exp_one_lt_three.le
-/
theorem ceil_exp_one_eq_three : ⌈exp 1⌉ = 3 :=
  Int.ceil_eq_iff.mpr ⟨by exact_mod_cast exp_one_gt_two, exp_one_lt_three.le⟩

/--
theorem `round_exp_one_eq_three` / 定理 `round_exp_one_eq_three`

English:
theorem round_exp_one_eq_three
  statement: round (exp 1) = 3
  proof: by
.trans Int.floor_eq_iff.mpr ⟨?_, by grind [exp_one_lt_three]⟩ refine round_eq _
  grw [← exp_one_gt_d9]
  norm_num

中文:
定理 round_exp_one_eq_three
  结论: round (exp 1) = 3
  证明: by
.trans Int.floor_eq_iff.mpr ⟨?_, by grind [exp_one_lt_three]⟩ refine round_eq _
  grw [← exp_one_gt_d9]
  norm_num

Depends on / 依赖: Int.floor_eq_iff.mpr, exp_one_gt_d9, exp_one_lt_three, floor_eq_iff, round_eq
-/
theorem round_exp_one_eq_three : round (exp 1) = 3 := by
.trans Int.floor_eq_iff.mpr ⟨?_, by grind [exp_one_lt_three]⟩ refine round_eq _
  grw [← exp_one_gt_d9]
  norm_num

/--
theorem `exp_neg_one_gt_d9` / 定理 `exp_neg_one_gt_d9`

English:
theorem exp_neg_one_gt_d9
  statement: 0.36787944116 < exp (-1)
  proof: by
  rw [exp_neg]; rw [lt_inv_comm₀ _ (exp_pos _)]
  · refine lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 exp_one_near_10).1) ?_
    norm_num
  · norm_num

中文:
定理 exp_neg_one_gt_d9
  结论: 0.36787944116 < exp (-1)
  证明: by
  rw [exp_neg]; rw [lt_inv_comm₀ _ (exp_pos _)]
  · refine lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 exp_one_near_10).1) ?_
    norm_num
  · norm_num

Depends on / 依赖: abs_sub_le_iff, exp_neg, exp_one_near_10, exp_pos, lt_of_le_of_lt, sub_le_iff_le_add
-/
theorem exp_neg_one_gt_d9 : 0.36787944116 < exp (-1) := by
  rw [exp_neg]; rw [lt_inv_comm₀ _ (exp_pos _)]
  · refine lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 exp_one_near_10).1) ?_
    norm_num
  · norm_num

/--
theorem `exp_neg_one_lt_d9` / 定理 `exp_neg_one_lt_d9`

English:
theorem exp_neg_one_lt_d9
  statement: exp (-1) < 0.3678794412
  proof: by
  rw [exp_neg]; rw [inv_lt_comm₀ (exp_pos _) (by norm_num)]
  exact lt_of_lt_of_le (by norm_num) (sub_le_comm.1 (abs_sub_le_iff.1 exp_one_near_10).2)

中文:
定理 exp_neg_one_lt_d9
  结论: exp (-1) < 0.3678794412
  证明: by
  rw [exp_neg]; rw [inv_lt_comm₀ (exp_pos _) (by norm_num)]
  exact lt_of_lt_of_le (by norm_num) (sub_le_comm.1 (abs_sub_le_iff.1 exp_one_near_10).2)

Depends on / 依赖: abs_sub_le_iff, exp_neg, exp_one_near_10, exp_pos, lt_of_lt_of_le, sub_le_comm
-/
theorem exp_neg_one_lt_d9 : exp (-1) < 0.3678794412 := by
  rw [exp_neg]; rw [inv_lt_comm₀ (exp_pos _) (by norm_num)]
  exact lt_of_lt_of_le (by norm_num) (sub_le_comm.1 (abs_sub_le_iff.1 exp_one_near_10).2)

/--
theorem `exp_neg_one_lt_half` / 定理 `exp_neg_one_lt_half`

English:
theorem exp_neg_one_lt_half
  statement: exp (-1) < 1 / 2
  proof: lt_trans exp_neg_one_lt_d9 (by norm_num)

中文:
定理 exp_neg_one_lt_half
  结论: exp (-1) < 1 / 2
  证明: lt_trans exp_neg_one_lt_d9 (by norm_num)

Depends on / 依赖: exp_neg_one_lt_d9, lt_trans
-/
theorem exp_neg_one_lt_half : exp (-1) < 1 / 2 :=
  lt_trans exp_neg_one_lt_d9 (by norm_num)

/--
theorem `log_two_near_10` / 定理 `log_two_near_10`

English:
theorem log_two_near_10
  statement: |log 2 - 287209 / 414355| <= 1 / 10 ^ 10
  proof: by
  suffices |log 2 - 287209 / 414355| <= 1 / 17179869184 + (1 / 10 ^ 10 - 1 / 2 ^ 34) by
    norm_num1 at *
    assumption
  have t : |(2⁻¹ : Real)| = 2⁻¹ := by rw [abs_of_pos]; norm_num
  have z := Real.abs_log_sub_add_sum_range_le (show |(2⁻¹ : Real)| < 1 by rw [t]; norm_num) 34
  rw [t] at z
  norm_num1 at z
  rw [one_div (2 : Real)]; rw [log_inv]; rw [← sub_eq_add_neg]; rw [_root_.abs_sub_comm] at z
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _)
  norm_num

中文:
定理 log_two_near_10
  结论: |log 2 - 287209 / 414355| <= 1 / 10 ^ 10
  证明: by
  suffices |log 2 - 287209 / 414355| <= 1 / 17179869184 + (1 / 10 ^ 10 - 1 / 2 ^ 34) by
    norm_num1 at *
    assumption
  have t : |(2⁻¹ : Real)| = 2⁻¹ := by rw [abs_of_pos]; norm_num
  have z := Real.abs_log_sub_add_sum_range_le (show |(2⁻¹ : Real)| < 1 by rw [t]; norm_num) 34
  rw [t] at z
  norm_num1 at z
  rw [one_div (2 : Real)]; rw [log_inv]; rw [← sub_eq_add_neg]; rw [_root_.abs_sub_comm] at z
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _)
  norm_num

Depends on / 依赖: Real.abs_log_sub_add_sum_range_le, _root_, _root_.abs_sub_comm, _root_.abs_sub_le, abs_log_sub_add_sum_range_le, abs_of_pos, abs_sub_comm, abs_sub_le, add_le_add, le_trans, log_inv, norm_num1, one_div, sub_eq_add_neg
-/
theorem log_two_near_10 : |log 2 - 287209 / 414355| <= 1 / 10 ^ 10 := by
  suffices |log 2 - 287209 / 414355| <= 1 / 17179869184 + (1 / 10 ^ 10 - 1 / 2 ^ 34) by
    norm_num1 at *
    assumption
  have t : |(2⁻¹ : Real)| = 2⁻¹ := by rw [abs_of_pos]; norm_num
  have z := Real.abs_log_sub_add_sum_range_le (show |(2⁻¹ : Real)| < 1 by rw [t]; norm_num) 34
  rw [t] at z
  norm_num1 at z
  rw [one_div (2 : Real)]; rw [log_inv]; rw [← sub_eq_add_neg]; rw [_root_.abs_sub_comm] at z
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _)
  norm_num

/--
theorem `log_two_gt_d9` / 定理 `log_two_gt_d9`

English:
theorem log_two_gt_d9
  statement: 0.6931471803 < log 2
  proof: lt_of_lt_of_le (by norm_num1) (sub_le_comm.1 (abs_sub_le_iff.1 log_two_near_10).2)

中文:
定理 log_two_gt_d9
  结论: 0.6931471803 < log 2
  证明: lt_of_lt_of_le (by norm_num1) (sub_le_comm.1 (abs_sub_le_iff.1 log_two_near_10).2)

Depends on / 依赖: abs_sub_le_iff, log_two_near_10, lt_of_lt_of_le, norm_num1, sub_le_comm
-/
theorem log_two_gt_d9 : 0.6931471803 < log 2 :=
  lt_of_lt_of_le (by norm_num1) (sub_le_comm.1 (abs_sub_le_iff.1 log_two_near_10).2)

/--
theorem `log_two_lt_d9` / 定理 `log_two_lt_d9`

English:
theorem log_two_lt_d9
  statement: log 2 < 0.6931471808
  proof: lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 log_two_near_10).1) (by norm_num)

中文:
定理 log_two_lt_d9
  结论: log 2 < 0.6931471808
  证明: lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 log_two_near_10).1) (by norm_num)

Depends on / 依赖: abs_sub_le_iff, log_two_near_10, lt_of_le_of_lt, sub_le_iff_le_add
-/
theorem log_two_lt_d9 : log 2 < 0.6931471808 :=
  lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 log_two_near_10).1) (by norm_num)

/--
theorem `log_three_near_10` / 定理 `log_three_near_10`

English:
theorem log_three_near_10
  statement: |log 3 - 109861228867 / 100000000000| <= 1 / 10 ^ 10
  proof: by
  suffices |log 3 - 109861228867 / 100000000000| <=
      (2 / 3) ^ 71 / 3⁻¹ + (1 / 10 ^ 10 - (2 / 3) ^ 71 / 3⁻¹) by
    norm_num1 at *
    assumption
  have t : |2 / 3| = (2 : Real) / 3 := by norm_num
  have z := abs_log_sub_add_sum_range_le (x := 2 / 3) (by norm_num) 70
  rw [t]; rw [show (1 - (2 : Real) / 3) = (1 / 3 : Real) by norm_num]; rw [one_div (3 : Real)]; rw [log_inv]; rw [← sub_eq_add_neg]; rw [_root_.abs_sub_comm] at z
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _)
  norm_num [sum_range_succ]

中文:
定理 log_three_near_10
  结论: |log 3 - 109861228867 / 100000000000| <= 1 / 10 ^ 10
  证明: by
  suffices |log 3 - 109861228867 / 100000000000| <=
      (2 / 3) ^ 71 / 3⁻¹ + (1 / 10 ^ 10 - (2 / 3) ^ 71 / 3⁻¹) by
    norm_num1 at *
    assumption
  have t : |2 / 3| = (2 : Real) / 3 := by norm_num
  have z := abs_log_sub_add_sum_range_le (x := 2 / 3) (by norm_num) 70
  rw [t]; rw [show (1 - (2 : Real) / 3) = (1 / 3 : Real) by norm_num]; rw [one_div (3 : Real)]; rw [log_inv]; rw [← sub_eq_add_neg]; rw [_root_.abs_sub_comm] at z
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _)
  norm_num [sum_range_succ]

Depends on / 依赖: _root_, _root_.abs_sub_comm, _root_.abs_sub_le, abs_log_sub_add_sum_range_le, abs_sub_comm, abs_sub_le, add_le_add, le_trans, log_inv, norm_num1, one_div, sub_eq_add_neg, sum_range_succ
-/
theorem log_three_near_10 : |log 3 - 109861228867 / 100000000000| <= 1 / 10 ^ 10 := by
  suffices |log 3 - 109861228867 / 100000000000| <=
      (2 / 3) ^ 71 / 3⁻¹ + (1 / 10 ^ 10 - (2 / 3) ^ 71 / 3⁻¹) by
    norm_num1 at *
    assumption
  have t : |2 / 3| = (2 : Real) / 3 := by norm_num
  have z := abs_log_sub_add_sum_range_le (x := 2 / 3) (by norm_num) 70
  rw [t]; rw [show (1 - (2 : Real) / 3) = (1 / 3 : Real) by norm_num]; rw [one_div (3 : Real)]; rw [log_inv]; rw [← sub_eq_add_neg]; rw [_root_.abs_sub_comm] at z
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _)
  norm_num [sum_range_succ]

/--
theorem `log_three_gt_d9` / 定理 `log_three_gt_d9`

English:
theorem log_three_gt_d9
  statement: 1.0986122885 < log 3
  proof: lt_of_lt_of_le (by norm_num1) (sub_le_comm.1 (abs_sub_le_iff.1 log_three_near_10).2)

中文:
定理 log_three_gt_d9
  结论: 1.0986122885 < log 3
  证明: lt_of_lt_of_le (by norm_num1) (sub_le_comm.1 (abs_sub_le_iff.1 log_three_near_10).2)

Depends on / 依赖: abs_sub_le_iff, log_three_near_10, lt_of_lt_of_le, norm_num1, sub_le_comm
-/
theorem log_three_gt_d9 : 1.0986122885 < log 3 :=
  lt_of_lt_of_le (by norm_num1) (sub_le_comm.1 (abs_sub_le_iff.1 log_three_near_10).2)

/--
theorem `log_three_lt_d9` / 定理 `log_three_lt_d9`

English:
theorem log_three_lt_d9
  statement: log 3 < 1.0986122888
  proof: lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 log_three_near_10).1) (by norm_num)

中文:
定理 log_three_lt_d9
  结论: log 3 < 1.0986122888
  证明: lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 log_three_near_10).1) (by norm_num)

Depends on / 依赖: abs_sub_le_iff, log_three_near_10, lt_of_le_of_lt, sub_le_iff_le_add
-/
theorem log_three_lt_d9 : log 3 < 1.0986122888 :=
  lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 log_three_near_10).1) (by norm_num)

/--
theorem `log_four_eq` / 定理 `log_four_eq`

English:
theorem log_four_eq
  statement: log 4 = 2 * log 2
  proof: by norm_num [← log_rpow]

中文:
定理 log_four_eq
  结论: log 4 = 2 * log 2
  证明: by norm_num [← log_rpow]

Depends on / 依赖: log_rpow
-/
theorem log_four_eq : log 4 = 2 * log 2 := by norm_num [← log_rpow]

/--
theorem `log_five_near_10` / 定理 `log_five_near_10`

English:
theorem log_five_near_10
  statement: |log 5 - 160943791243 / 100000000000| <= 1 / 10 ^ 10
  proof: by
  suffices |log 5 - 160943791243 / 100000000000| <=
      (4 / 5) ^ 131 / 5⁻¹ + (1 / 10 ^ 10 - (4 / 5) ^ 131 / 5⁻¹) by
    norm_num1 at *
    assumption
  have t : |4 / 5| = (4 : Real) / 5 := by norm_num
  have z := abs_log_sub_add_sum_range_le (x := 4 / 5) (by norm_num) 130
  rw [t]; rw [show (1 - (4 : Real) / 5) = (1 / 5 : Real) by norm_num]; rw [one_div (5 : Real)]; rw [log_inv]; rw [← sub_eq_add_neg]; rw [_root_.abs_sub_comm] at z
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _)
  norm_num [sum_range_succ]

中文:
定理 log_five_near_10
  结论: |log 5 - 160943791243 / 100000000000| <= 1 / 10 ^ 10
  证明: by
  suffices |log 5 - 160943791243 / 100000000000| <=
      (4 / 5) ^ 131 / 5⁻¹ + (1 / 10 ^ 10 - (4 / 5) ^ 131 / 5⁻¹) by
    norm_num1 at *
    assumption
  have t : |4 / 5| = (4 : Real) / 5 := by norm_num
  have z := abs_log_sub_add_sum_range_le (x := 4 / 5) (by norm_num) 130
  rw [t]; rw [show (1 - (4 : Real) / 5) = (1 / 5 : Real) by norm_num]; rw [one_div (5 : Real)]; rw [log_inv]; rw [← sub_eq_add_neg]; rw [_root_.abs_sub_comm] at z
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _)
  norm_num [sum_range_succ]

Depends on / 依赖: _root_, _root_.abs_sub_comm, _root_.abs_sub_le, abs_log_sub_add_sum_range_le, abs_sub_comm, abs_sub_le, add_le_add, le_trans, log_inv, norm_num1, one_div, sub_eq_add_neg, sum_range_su
-/
theorem log_five_near_10 : |log 5 - 160943791243 / 100000000000| <= 1 / 10 ^ 10 := by
  suffices |log 5 - 160943791243 / 100000000000| <=
      (4 / 5) ^ 131 / 5⁻¹ + (1 / 10 ^ 10 - (4 / 5) ^ 131 / 5⁻¹) by
    norm_num1 at *
    assumption
  have t : |4 / 5| = (4 : Real) / 5 := by norm_num
  have z := abs_log_sub_add_sum_range_le (x := 4 / 5) (by norm_num) 130
  rw [t]; rw [show (1 - (4 : Real) / 5) = (1 / 5 : Real) by norm_num]; rw [one_div (5 : Real)]; rw [log_inv]; rw [← sub_eq_add_neg]; rw [_root_.abs_sub_comm] at z
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _)
  norm_num [sum_range_succ]

/--
theorem `log_five_gt_d9` / 定理 `log_five_gt_d9`

English:
theorem log_five_gt_d9
  statement: 1.6094379123 < log 5
  proof: lt_of_lt_of_le (by norm_num1) (sub_le_comm.1 (abs_sub_le_iff.1 log_five_near_10).2)

中文:
定理 log_five_gt_d9
  结论: 1.6094379123 < log 5
  证明: lt_of_lt_of_le (by norm_num1) (sub_le_comm.1 (abs_sub_le_iff.1 log_five_near_10).2)

Depends on / 依赖: abs_sub_le_iff, log_five_near_10, lt_of_lt_of_le, norm_num1, sub_le_comm
-/
theorem log_five_gt_d9 : 1.6094379123 < log 5 :=
  lt_of_lt_of_le (by norm_num1) (sub_le_comm.1 (abs_sub_le_iff.1 log_five_near_10).2)

/--
theorem `log_five_lt_d9` / 定理 `log_five_lt_d9`

English:
theorem log_five_lt_d9
  statement: log 5 < 1.6094379126
  proof: lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 log_five_near_10).1) (by norm_num)

中文:
定理 log_five_lt_d9
  结论: log 5 < 1.6094379126
  证明: lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 log_five_near_10).1) (by norm_num)

Depends on / 依赖: abs_sub_le_iff, log_five_near_10, lt_of_le_of_lt, sub_le_iff_le_add
-/
theorem log_five_lt_d9 : log 5 < 1.6094379126 :=
  lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 log_five_near_10).1) (by norm_num)

/--
theorem `log_ten_eq` / 定理 `log_ten_eq`

English:
theorem log_ten_eq
  statement: log 10 = log 2 + log 5
  proof: by norm_num [← log_mul]

中文:
定理 log_ten_eq
  结论: log 10 = log 2 + log 5
  证明: by norm_num [← log_mul]

Depends on / 依赖: log_mul
-/
theorem log_ten_eq : log 10 = log 2 + log 5 := by norm_num [← log_mul]

end Real
