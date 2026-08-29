/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Positive Part of the Logarithm

This file defines the function `Real.posLog = r ↦ max 0 (log r)` and introduces the notation
`log⁺`. For a finite length-`n` sequence `f i` of reals, it establishes the following standard
estimates.

- `theorem posLog_prod : log⁺ (∏ i, f i) ≤ ∑ i, log⁺ (f i)`

- `theorem posLog_sum : log⁺ (∑ i, f i) ≤ log n + ∑ i, log⁺ (f i)`

See `Mathlib/Analysis/SpecialFunctions/Integrals/PosLogEqCircleAverage.lean` for the presentation of
`log⁺` as a Circle Average.
-/

@[expose] public section

namespace Real

variable {x y : Real}

/-!
## Definition, Notation and Reformulations
-/

/--
Definition of `posLog` / `posLog` 的定义

English:
definition posLog
  signature: : Real -> Real
  body: fun r => max 0 (log r)

中文:
定义 posLog
  签名: : 实数 -> 实数
  定义体: fun r => max 0 (log r)
-/
noncomputable def posLog : Real -> Real := fun r => max 0 (log r)

/-- Notation `log⁺` for the positive part of the logarithm. -/
scoped notation "log⁺" => posLog

/--
theorem `posLog_apply` / 定理 `posLog_apply`

English:
theorem posLog_apply
  statement: log⁺ x = max 0 (log x)
  proof: rfl

中文:
定理 posLog_apply
  结论: log⁺ x = 最大值 0 (log x)
  证明: rfl
-/
theorem posLog_apply : log⁺ x = max 0 (log x) := rfl

/--
theorem `posLog_def` / 定理 `posLog_def`

English:
theorem posLog_def
  statement: log⁺ = max 0 (log ·)
  proof: rfl

中文:
定理 posLog_def
  结论: log⁺ = 最大值 0 (log ·)
  证明: rfl
-/
theorem posLog_def : log⁺ = max 0 (log ·) := rfl

/-!
## Elementary Properties
-/

/--
theorem `posLog_sub_posLog_inv` / 定理 `posLog_sub_posLog_inv`

English:
theorem posLog_sub_posLog_inv
  statement: log⁺ x - log⁺ x⁻¹ = log x
  proof: by
  rw [posLog_apply]; rw [posLog_apply]; rw [log_inv]
  by_cases! h : 0 <= log x
  · simp [h]
  · simp [neg_nonneg.1 (Left.nonneg_neg_iff.2 h.le)]

中文:
定理 posLog_sub_posLog_inv
  结论: log⁺ x - log⁺ x⁻¹ = log x
  证明: by
  rw [posLog_apply]; rw [posLog_apply]; rw [log_inv]
  by_cases! h : 0 <= log x
  · simp [h]
  · simp [neg_nonneg.1 (Left.nonneg_neg_iff.2 h.le)]

Depends on / 依赖: Left.nonneg_neg_iff, h.le, log_inv, neg_nonneg, nonneg_neg_iff, posLog_apply
-/
theorem posLog_sub_posLog_inv : log⁺ x - log⁺ x⁻¹ = log x := by
  rw [posLog_apply]; rw [posLog_apply]; rw [log_inv]
  by_cases! h : 0 <= log x
  · simp [h]
  · simp [neg_nonneg.1 (Left.nonneg_neg_iff.2 h.le)]

/--
theorem `half_mul_log_add_log_abs` / 定理 `half_mul_log_add_log_abs`

English:
theorem half_mul_log_add_log_abs
  statement: 2⁻¹ * (log x + |log x|) = log⁺ x
  proof: by
  by_cases! hr : 0 <= log x
  · simp [posLog, hr, abs_of_nonneg]
    ring
  · simp [posLog, hr.le, abs_of_nonpos]

中文:
定理 half_mul_log_add_log_abs
  结论: 2⁻¹ * (log x + |log x|) = log⁺ x
  证明: by
  by_cases! hr : 0 <= log x
  · simp [posLog, hr, abs_of_nonneg]
    ring
  · simp [posLog, hr.le, abs_of_nonpos]

Depends on / 依赖: abs_of_nonneg, abs_of_nonpos, hr.le, posLog
-/
theorem half_mul_log_add_log_abs : 2⁻¹ * (log x + |log x|) = log⁺ x := by
  by_cases! hr : 0 <= log x
  · simp [posLog, hr, abs_of_nonneg]
    ring
  · simp [posLog, hr.le, abs_of_nonpos]

/--
lemma `posLog_zero` / 引理 `posLog_zero`

English:
lemma posLog_zero
  statement: log⁺ 0 = 0
  proof: by simp [posLog]

中文:
引理 posLog_zero
  结论: log⁺ 0 = 0
  证明: by simp [posLog]
-/
@[simp] lemma posLog_zero : log⁺ 0 = 0 := by simp [posLog]

/--
lemma `posLog_one` / 引理 `posLog_one`

English:
lemma posLog_one
  statement: log⁺ 1 = 0
  proof: by simp [posLog]

中文:
引理 posLog_one
  结论: log⁺ 1 = 0
  证明: by simp [posLog]
-/
@[simp] lemma posLog_one : log⁺ 1 = 0 := by simp [posLog]

/--
theorem `posLog_nonneg` / 定理 `posLog_nonneg`

English:
theorem posLog_nonneg
  statement: 0 <= log⁺ x
  proof: by simp [posLog]

中文:
定理 posLog_nonneg
  结论: 0 <= log⁺ x
  证明: by simp [posLog]

Depends on / 依赖: posLog
-/
theorem posLog_nonneg : 0 <= log⁺ x := by simp [posLog]

/--
theorem `posLog_neg` / 定理 `posLog_neg`

English:
theorem posLog_neg
  given: (x : Real)
  statement: log⁺ (-x) = log⁺ x
  proof: by simp [posLog]

中文:
定理 posLog_neg
  条件: (x : 实数)
  结论: log⁺ (-x) = log⁺ x
  证明: by simp [posLog]
-/
@[simp] theorem posLog_neg (x : Real) : log⁺ (-x) = log⁺ x := by simp [posLog]

/--
theorem `posLog_abs` / 定理 `posLog_abs`

English:
theorem posLog_abs
  given: (x : Real)
  statement: log⁺ |x| = log⁺ x
  proof: by simp [posLog]

中文:
定理 posLog_abs
  条件: (x : 实数)
  结论: log⁺ |x| = log⁺ x
  证明: by simp [posLog]
-/
@[simp] theorem posLog_abs (x : Real) : log⁺ |x| = log⁺ x := by simp [posLog]

/--
theorem `posLog_eq_zero_iff` / 定理 `posLog_eq_zero_iff`

English:
theorem posLog_eq_zero_iff
  given: (x : Real)
  statement: log⁺ x = 0 ↔ |x| <= 1
  proof: by
  rw [← posLog_abs]; rw [← log_nonpos_iff (abs_nonneg x)]
  simp [posLog]

中文:
定理 posLog_eq_zero_iff
  条件: (x : 实数)
  结论: log⁺ x = 0 ↔ |x| <= 1
  证明: by
  rw [← posLog_abs]; rw [← log_nonpos_iff (abs_nonneg x)]
  simp [posLog]

Depends on / 依赖: abs_nonneg, log_nonpos_iff, posLog, posLog_abs
-/
theorem posLog_eq_zero_iff (x : Real) : log⁺ x = 0 ↔ |x| <= 1 := by
  rw [← posLog_abs]; rw [← log_nonpos_iff (abs_nonneg x)]
  simp [posLog]

/--
theorem `posLog_eq_log` / 定理 `posLog_eq_log`

English:
theorem posLog_eq_log
  given: (hx : 1 <= |x|)
  statement: log⁺ x = log x
  proof: by
  simp only [posLog, sup_eq_right]
  rw [← log_abs]
  apply log_nonneg hx

中文:
定理 posLog_eq_log
  条件: (hx : 1 <= |x|)
  结论: log⁺ x = log x
  证明: by
  simp only [posLog, sup_eq_right]
  rw [← log_abs]
  apply log_nonneg hx

Depends on / 依赖: log_abs, log_nonneg, posLog, sup_eq_right
-/
theorem posLog_eq_log (hx : 1 <= |x|) : log⁺ x = log x := by
  simp only [posLog, sup_eq_right]
  rw [← log_abs]
  apply log_nonneg hx

/--
theorem `log_of_nat_eq_posLog` / 定理 `log_of_nat_eq_posLog`

English:
theorem log_of_nat_eq_posLog
  given: {n : Nat}
  statement: log⁺ n = log n
  proof: by
  by_cases hn : n = 0
  · simp [hn, posLog]
  · simp [posLog_eq_log, Nat.one_le_iff_ne_zero.2 hn]

中文:
定理 log_of_nat_eq_posLog
  条件: {n : 自然数}
  结论: log⁺ n = log n
  证明: by
  by_cases hn : n = 0
  · simp [hn, posLog]
  · simp [posLog_eq_log, Nat.one_le_iff_ne_zero.2 hn]

Depends on / 依赖: Nat.one_le_iff_ne_zero, one_le_iff_ne_zero, posLog, posLog_eq_log
-/
theorem log_of_nat_eq_posLog {n : Nat} : log⁺ n = log n := by
  by_cases hn : n = 0
  · simp [hn, posLog]
  · simp [posLog_eq_log, Nat.one_le_iff_ne_zero.2 hn]

/--
theorem `posLog_eq_log_max_one` / 定理 `posLog_eq_log_max_one`

English:
theorem posLog_eq_log_max_one
  given: (hx : 0 <= x)
  statement: log⁺ x = log (max 1 x)
  proof: by
  grind [le_abs, posLog_eq_log, log_one, max_eq_left, log_nonpos, posLog_apply]

中文:
定理 posLog_eq_log_max_one
  条件: (hx : 0 <= x)
  结论: log⁺ x = log (最大值 1 x)
  证明: by
  grind [le_abs, posLog_eq_log, log_one, max_eq_left, log_nonpos, posLog_apply]

Depends on / 依赖: le_abs, log_nonpos, log_one, max_eq_left, posLog_apply, posLog_eq_log
-/
theorem posLog_eq_log_max_one (hx : 0 <= x) : log⁺ x = log (max 1 x) := by
  grind [le_abs, posLog_eq_log, log_one, max_eq_left, log_nonpos, posLog_apply]

/--
theorem `monotoneOn_posLog` / 定理 `monotoneOn_posLog`

English:
theorem monotoneOn_posLog
  statement: MonotoneOn log⁺ (Set.Ici 0)
  proof: by
  intro x hx y hy hxy
  simp only [posLog, le_sup_iff, sup_le_iff, le_refl, true_and]
  by_cases! h : log x <= 0
  · tauto
  · right
    have := log_le_log (lt_trans Real.zero_lt_one ((log_pos_iff hx).1 h)) hxy
    simp only [this, and_true, ge_iff_le]
    linarith

@[gcongr]

中文:
定理 monotoneOn_posLog
  结论: MonotoneOn log⁺ (集合.左闭右无界区间 0)
  证明: by
  intro x hx y hy hxy
  simp only [posLog, le_sup_iff, sup_le_iff, le_refl, true_and]
  by_cases! h : log x <= 0
  · tauto
  · right
    have := log_le_log (lt_trans Real.zero_lt_one ((log_pos_iff hx).1 h)) hxy
    simp only [this, and_true, ge_iff_le]
    linarith

@[gcongr]

Depends on / 依赖: Real.zero_lt_one, and_true, ge_iff_le, le_refl, le_sup_iff, log_le_log, log_pos_iff, lt_trans, posLog, sup_le_iff, true_and, zero_lt_one
-/
theorem monotoneOn_posLog : MonotoneOn log⁺ (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [posLog, le_sup_iff, sup_le_iff, le_refl, true_and]
  by_cases! h : log x <= 0
  · tauto
  · right
    have := log_le_log (lt_trans Real.zero_lt_one ((log_pos_iff hx).1 h)) hxy
    simp only [this, and_true, ge_iff_le]
    linarith

@[gcongr]
/--
lemma `posLog_le_posLog` / 引理 `posLog_le_posLog`

English:
lemma posLog_le_posLog
  given: (hx : 0 <= x) (hxy : x <= y)
  statement: log⁺ x <= log⁺ y
  proof: monotoneOn_posLog hx (hx.trans hxy) hxy

中文:
引理 posLog_le_posLog
  条件: (hx : 0 <= x) (hxy : x <= y)
  结论: log⁺ x <= log⁺ y
  证明: monotoneOn_posLog hx (hx.trans hxy) hxy

Depends on / 依赖: hx.trans, monotoneOn_posLog
-/
lemma posLog_le_posLog (hx : 0 <= x) (hxy : x <= y) : log⁺ x <= log⁺ y :=
  monotoneOn_posLog hx (hx.trans hxy) hxy

/--
lemma `posLog_pow` / 引理 `posLog_pow`

English:
lemma posLog_pow
  given: (n : Nat) (x : Real)
  statement: log⁺ (x ^ n) = n * log⁺ x
  proof: by
  by_cases hn : n = 0
  · simp_all
  by_cases hx : |x| <= 1
  · simp_all [pow_le_one₀, (posLog_eq_zero_iff _).2]
  rw [not_le] at hx
  have : 1 <= |x ^ n| := by simp_all [one_le_pow₀, hx.le]
  simp [posLog_eq_log this, posLog_eq_log hx.le]

中文:
引理 posLog_pow
  条件: (n : 自然数) (x : 实数)
  结论: log⁺ (x ^ n) = n * log⁺ x
  证明: by
  by_cases hn : n = 0
  · simp_all
  by_cases hx : |x| <= 1
  · simp_all [pow_le_one₀, (posLog_eq_zero_iff _).2]
  rw [not_le] at hx
  have : 1 <= |x ^ n| := by simp_all [one_le_pow₀, hx.le]
  simp [posLog_eq_log this, posLog_eq_log hx.le]
-/
@[simp] lemma posLog_pow (n : Nat) (x : Real) : log⁺ (x ^ n) = n * log⁺ x := by
  by_cases hn : n = 0
  · simp_all
  by_cases hx : |x| <= 1
  · simp_all [pow_le_one₀, (posLog_eq_zero_iff _).2]
  rw [not_le] at hx
  have : 1 <= |x ^ n| := by simp_all [one_le_pow₀, hx.le]
  simp [posLog_eq_log this, posLog_eq_log hx.le]

/--
theorem `continuous_posLog` / 定理 `continuous_posLog`

English:
theorem continuous_posLog
  statement: Continuous log⁺
  proof: by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · apply ContinuousAt.congr (f := fun _ => 0) (by fun_prop)
    filter_upwards [Metric.ball_mem_nhds _ zero_lt_one] with y hy
    rw [eq_comm]; rw [posLog_eq_zero_iff y]
    simp_all [le_of_lt]
  rw [posLog_def]
  fun_prop

中文:
定理 continuous_posLog
  结论: 连续 log⁺
  证明: by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · apply ContinuousAt.congr (f := fun _ => 0) (by fun_prop)
    filter_upwards [Metric.ball_mem_nhds _ zero_lt_one] with y hy
    rw [eq_comm]; rw [posLog_eq_zero_iff y]
    simp_all [le_of_lt]
  rw [posLog_def]
  fun_prop
-/
@[fun_prop] theorem continuous_posLog : Continuous log⁺ := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · apply ContinuousAt.congr (f := fun _ => 0) (by fun_prop)
    filter_upwards [Metric.ball_mem_nhds _ zero_lt_one] with y hy
    rw [eq_comm]; rw [posLog_eq_zero_iff y]
    simp_all [le_of_lt]
  rw [posLog_def]
  fun_prop

/-!
## Estimates for Products
-/

/--
theorem `posLog_mul` / 定理 `posLog_mul`

English:
theorem posLog_mul
  statement: log⁺ (x * y) <= log⁺ x + log⁺ y
  proof: by
  by_cases ha : x = 0
  · simp [ha, posLog]
  by_cases hb : y = 0
  · simp [hb, posLog]
  unfold posLog
  nth_rw 1 [← add_zero 0, log_mul ha hb]
  exact max_add_add_le_max_add_max

中文:
定理 posLog_mul
  结论: log⁺ (x * y) <= log⁺ x + log⁺ y
  证明: by
  by_cases ha : x = 0
  · simp [ha, posLog]
  by_cases hb : y = 0
  · simp [hb, posLog]
  unfold posLog
  nth_rw 1 [← add_zero 0, log_mul ha hb]
  exact max_add_add_le_max_add_max

Depends on / 依赖: add_zero, log_mul, max_add_add_le_max_add_max, nth_rw, posLog
-/
theorem posLog_mul : log⁺ (x * y) <= log⁺ x + log⁺ y := by
  by_cases ha : x = 0
  · simp [ha, posLog]
  by_cases hb : y = 0
  · simp [hb, posLog]
  unfold posLog
  nth_rw 1 [← add_zero 0, log_mul ha hb]
  exact max_add_add_le_max_add_max

/--
theorem `posLog_nat_mul` / 定理 `posLog_nat_mul`

English:
theorem posLog_nat_mul
  given: {n : Nat}
  statement: log⁺ (n * x) <= log n + log⁺ x
  proof: by
  rw [← log_of_nat_eq_posLog]
  exact posLog_mul

中文:
定理 posLog_nat_mul
  条件: {n : 自然数}
  结论: log⁺ (n * x) <= log n + log⁺ x
  证明: by
  rw [← log_of_nat_eq_posLog]
  exact posLog_mul

Depends on / 依赖: log_of_nat_eq_posLog, posLog_mul
-/
theorem posLog_nat_mul {n : Nat} : log⁺ (n * x) <= log n + log⁺ x := by
  rw [← log_of_nat_eq_posLog]
  exact posLog_mul

/--
theorem `posLog_prod` / 定理 `posLog_prod`

English:
theorem posLog_prod
  given: {α : Type*} (s : Finset α) (f : α -> Real)
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp [posLog]
  | insert a s ha hs =>
    calc log⁺ (∏ t in insert a s, f t)
    _ = log⁺ (f a * ∏ t in s, f t) := by rw [Finset.prod_insert ha]
    _ <= log⁺ (f a) + log⁺ (∏ t in s, f t) := posLog_mul
    _ <= log⁺ (f a) + ∑ t in s, log⁺ (f t) := add_le_add (by rfl) hs
    _ = ∑ t in insert a s, log⁺ (f t) := by rw [Finset.sum_insert ha]

中文:
定理 posLog_prod
  条件: {α : 类型} (s : 有限集 α) (f : α -> 实数)
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp [posLog]
  | insert a s ha hs =>
    calc log⁺ (∏ t in insert a s, f t)
    _ = log⁺ (f a * ∏ t in s, f t) := by rw [Finset.prod_insert ha]
    _ <= log⁺ (f a) + log⁺ (∏ t in s, f t) := posLog_mul
    _ <= log⁺ (f a) + ∑ t in s, log⁺ (f t) := add_le_add (by rfl) hs
    _ = ∑ t in insert a s, log⁺ (f t) := by rw [Finset.sum_insert ha]

Depends on / 依赖: Finset, Finset.induction, Finset.prod_insert, Finset.sum_insert, add_le_add, classical, insert, posLog, posLog_mul, prod_insert, sum_insert
-/
theorem posLog_prod {α : Type*} (s : Finset α) (f : α -> Real) :
    log⁺ (∏ t in s, f t) <= ∑ t in s, log⁺ (f t) := by
  classical
  induction s using Finset.induction with
  | empty => simp [posLog]
  | insert a s ha hs =>
    calc log⁺ (∏ t in insert a s, f t)
    _ = log⁺ (f a * ∏ t in s, f t) := by rw [Finset.prod_insert ha]
    _ <= log⁺ (f a) + log⁺ (∏ t in s, f t) := posLog_mul
    _ <= log⁺ (f a) + ∑ t in s, log⁺ (f t) := add_le_add (by rfl) hs
    _ = ∑ t in insert a s, log⁺ (f t) := by rw [Finset.sum_insert ha]

/-!
## Estimates for Sums
-/

/--
theorem `posLog_sum` / 定理 `posLog_sum`

English:
theorem posLog_sum
  given: {α : Type*} (s : Finset α) (f : α -> Real)
  proof: by
  -- Trivial case: empty sum
  by_cases! hs : s = ∅
  · simp [hs, posLog]
  -- Nontrivial case: Obtain maximal element…
  obtain ⟨t_max, ht_max⟩ := s.exists_max_image (fun t => |f t|) hs
  -- …then calculate
  calc log⁺ (∑ t in s, f t)
  _ = log⁺ |∑ t in s, f t| := by
    rw [Real.posLog_abs]
  _ <= log⁺ (∑ t in s, |f t|) := by
    apply monotoneOn_posLog (by simp) (by simp [Finset.sum_nonneg])
    simp [Finset.abs_sum_le_sum_abs]
  _ <= log⁺ (∑ t in s, |f t_max|) := by
    apply monotoneOn_posLog (by simp [Finset.sum_nonneg]) (by simp [mul_nonneg])
    apply Finset.sum_le_sum (fun i ih => ht_max.2 i ih)
  _ = log⁺ (s.card * |f t_max|) := by
    simp [Finset.sum_const]
  _ <= log s.card + log⁺ |f t_max| := posLog_nat_mul
  _ <= log s.card + ∑ t in s, log⁺ (f t) := by
    gcongr
    rw [posLog_abs]
    apply Finset.single_le_sum (fun _ _ => posLog_nonneg) ht_max.1

中文:
定理 posLog_sum
  条件: {α : 类型} (s : 有限集 α) (f : α -> 实数)
  证明: by
  -- Trivial case: empty sum
  by_cases! hs : s = ∅
  · simp [hs, posLog]
  -- Nontrivial case: Obtain maximal element…
  obtain ⟨t_max, ht_max⟩ := s.exists_max_image (fun t => |f t|) hs
  -- …then calculate
  calc log⁺ (∑ t in s, f t)
  _ = log⁺ |∑ t in s, f t| := by
    rw [Real.posLog_abs]
  _ <= log⁺ (∑ t in s, |f t|) := by
    apply monotoneOn_posLog (by simp) (by simp [Finset.sum_nonneg])
    simp [Finset.abs_sum_le_sum_abs]
  _ <= log⁺ (∑ t in s, |f t_max|) := by
    apply monotoneOn_posLog (by simp [Finset.sum_nonneg]) (by simp [mul_nonneg])
    apply Finset.sum_le_sum (fun i ih => ht_max.2 i ih)
  _ = log⁺ (s.card * |f t_max|) := by
    simp [Finset.sum_const]
  _ <= log s.card + log⁺ |f t_max| := posLog_nat_mul
  _ <= log s.card + ∑ t in s, log⁺ (f t) := by
    gcongr
    rw [posLog_abs]
    apply Finset.single_le_sum (fun _ _ => posLog_nonneg) ht_max.1
-/
theorem posLog_sum {α : Type*} (s : Finset α) (f : α -> Real) :
    log⁺ (∑ t in s, f t) <= log (s.card) + ∑ t in s, log⁺ (f t) := by
  -- Trivial case: empty sum
  by_cases! hs : s = ∅
  · simp [hs, posLog]
  -- Nontrivial case: Obtain maximal element…
  obtain ⟨t_max, ht_max⟩ := s.exists_max_image (fun t => |f t|) hs
  -- …then calculate
  calc log⁺ (∑ t in s, f t)
  _ = log⁺ |∑ t in s, f t| := by
    rw [Real.posLog_abs]
  _ <= log⁺ (∑ t in s, |f t|) := by
    apply monotoneOn_posLog (by simp) (by simp [Finset.sum_nonneg])
    simp [Finset.abs_sum_le_sum_abs]
  _ <= log⁺ (∑ t in s, |f t_max|) := by
    apply monotoneOn_posLog (by simp [Finset.sum_nonneg]) (by simp [mul_nonneg])
    apply Finset.sum_le_sum (fun i ih => ht_max.2 i ih)
  _ = log⁺ (s.card * |f t_max|) := by
    simp [Finset.sum_const]
  _ <= log s.card + log⁺ |f t_max| := posLog_nat_mul
  _ <= log s.card + ∑ t in s, log⁺ (f t) := by
    gcongr
    rw [posLog_abs]
    apply Finset.single_le_sum (fun _ _ => posLog_nonneg) ht_max.1

/--
lemma `posLog_norm_sum_le` / 引理 `posLog_norm_sum_le`

English:
lemma posLog_norm_sum_le
  statement: {E : Type*} [SeminormedAddCommGroup E] {α : Type*} (s : Finset α)
  proof: by
  grw [norm_sum_le, posLog_sum]

中文:
引理 posLog_norm_sum_le
  结论: {E : 类型} [SeminormedAddComm群 E] {α : 类型} (s : 有限集 α)
  证明: by
  grw [norm_sum_le, posLog_sum]

Depends on / 依赖: norm_sum_le, posLog_sum
-/
lemma posLog_norm_sum_le {E : Type*} [SeminormedAddCommGroup E] {α : Type*} (s : Finset α)
    (f : α -> E) :
    log⁺ ‖∑ t in s, f t‖ <= log s.card + ∑ t in s, log⁺ ‖f t‖ := by
  grw [norm_sum_le, posLog_sum]

/--
theorem `posLog_add` / 定理 `posLog_add`

English:
theorem posLog_add
  statement: log⁺ (x + y) <= log 2 + log⁺ x + log⁺ y
  proof: by
  convert! posLog_sum Finset.univ ![x, y] using 1 <;> simp [add_assoc]

中文:
定理 posLog_add
  结论: log⁺ (x + y) <= log 2 + log⁺ x + log⁺ y
  证明: by
  convert! posLog_sum Finset.univ ![x, y] using 1 <;> simp [add_assoc]

Depends on / 依赖: Finset, Finset.univ, add_assoc, convert, posLog_sum
-/
theorem posLog_add : log⁺ (x + y) <= log 2 + log⁺ x + log⁺ y := by
  convert! posLog_sum Finset.univ ![x, y] using 1 <;> simp [add_assoc]

/--
lemma `posLog_norm_add_le` / 引理 `posLog_norm_add_le`

English:
lemma posLog_norm_add_le
  given: {E : Type*} [SeminormedAddCommGroup E] (a b : E)
  proof: by
  grw [norm_add_le, posLog_add, add_rotate]

中文:
引理 posLog_norm_add_le
  条件: {E : 类型} [SeminormedAddComm群 E] (a b : E)
  证明: by
  grw [norm_add_le, posLog_add, add_rotate]

Depends on / 依赖: add_rotate, norm_add_le, posLog_add
-/
lemma posLog_norm_add_le {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    log⁺ ‖a + b‖ <= log⁺ ‖a‖ + log⁺ ‖b‖ + log 2 := by
  grw [norm_add_le, posLog_add, add_rotate]

end Real
