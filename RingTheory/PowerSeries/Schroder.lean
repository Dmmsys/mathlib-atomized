/-
Copyright (c) 2025 Weijie Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weijie Jiang
-/
module

public import Mathlib.Combinatorics.Enumerative.Schroder
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Schröder Numbers Power Series

This file defines lemmas and theorems about the power series for large and small Schröder numbers.

## Main Definitions
* `PowerSeries.largeSchroderSeries`: The power series for large Schröder numbers.
* `PowerSeries.smallSchroderSeries`: The power series for small Schröder numbers.

## Main Results
* `largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq`:
  The functional equation for the large Schröder numbers power series.

## TODO

* Prove the small Schröder numbers power series.

-/

@[expose] public section

open Finset Nat

namespace PowerSeries

/--
Definition of `largeSchroderSeries` / `largeSchroderSeries` 的定义

English:
definition largeSchroderSeries
  signature: : PowerSeries Nat
  body: PowerSeries.mk largeSchroder

@[simp]

中文:
定义 largeSchroderSeries
  签名: : 幂级数 自然数
  定义体: PowerSeries.mk largeSchroder

@[simp]

Depends on / 依赖: PowerSeries, PowerSeries.mk, largeSchroder
-/
def largeSchroderSeries : PowerSeries Nat :=
  PowerSeries.mk largeSchroder

@[simp]
/--
lemma `coeff_largeSchroderSeries` / 引理 `coeff_largeSchroderSeries`

English:
lemma coeff_largeSchroderSeries
  given: (n : Nat)
  proof: by
  simp [largeSchroderSeries]

@[simp]

中文:
引理 coeff_largeSchroderSeries
  条件: (n : 自然数)
  证明: by
  simp [largeSchroderSeries]

@[simp]

Depends on / 依赖: largeSchroderSeries
-/
lemma coeff_largeSchroderSeries (n : Nat) :
    (coeff n) largeSchroderSeries = largeSchroder n := by
  simp [largeSchroderSeries]

@[simp]
/--
lemma `constantCoeff_largeSchroderSeries` / 引理 `constantCoeff_largeSchroderSeries`

English:
lemma constantCoeff_largeSchroderSeries
  proof: by
  simp only [← coeff_zero_eq_constantCoeff_apply, coeff_largeSchroderSeries, largeSchroder_zero]

@[simp]

中文:
引理 constantCoeff_largeSchroderSeries
  证明: by
  simp only [← coeff_zero_eq_constantCoeff_apply, coeff_largeSchroderSeries, largeSchroder_zero]

@[simp]

Depends on / 依赖: coeff_largeSchroderSeries, coeff_zero_eq_constantCoeff_apply, largeSchroder_zero
-/
lemma constantCoeff_largeSchroderSeries :
    constantCoeff largeSchroderSeries = 1 := by
  simp only [← coeff_zero_eq_constantCoeff_apply, coeff_largeSchroderSeries, largeSchroder_zero]

@[simp]
/--
lemma `coeff_X_mul_largeSchroderSeries` / 引理 `coeff_X_mul_largeSchroderSeries`

English:
lemma coeff_X_mul_largeSchroderSeries
  given: (n : Nat) (hn : 0 < n)
  proof: by
  simp only [coeff_mul, coeff_largeSchroderSeries,
    Nat.sum_antidiagonal_eq_sum_range_succ (coeff · X * largeSchroder ·),
    succ_eq_add_one]
  simp only [coeff_X, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range, lt_add_iff_pos_left,
    ite_eq_left_iff, not_lt, nonpos_iff_eq_zero]
  rintro rfl
  simp_all only [lt_self_iff_false]

中文:
引理 coeff_X_mul_largeSchroderSeries
  条件: (n : 自然数) (hn : 0 < n)
  证明: by
  simp only [coeff_mul, coeff_largeSchroderSeries,
    Nat.sum_antidiagonal_eq_sum_range_succ (coeff · X * largeSchroder ·),
    succ_eq_add_one]
  simp only [coeff_X, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range, lt_add_iff_pos_left,
    ite_eq_left_iff, not_lt, nonpos_iff_eq_zero]
  rintro rfl
  simp_all only [lt_self_iff_false]

Depends on / 依赖: Nat.sum_antidiagonal_eq_sum_range_succ, coeff_X, coeff_largeSchroderSeries, coeff_mul, ite_eq_left_iff, ite_mul, largeSchroder, lt_add_iff_pos_left, lt_self_iff_false, mem_range, nonpos_iff_eq_zero, not_lt, one_mul, succ_eq_add_one, sum_antidiagonal_eq_sum_range_succ, sum_ite_eq, zero_mul
-/
lemma coeff_X_mul_largeSchroderSeries (n : Nat) (hn : 0 < n) :
    coeff n (X * largeSchroderSeries) = largeSchroder (n - 1) := by
  simp only [coeff_mul, coeff_largeSchroderSeries,
    Nat.sum_antidiagonal_eq_sum_range_succ (coeff · X * largeSchroder ·),
    succ_eq_add_one]
  simp only [coeff_X, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range, lt_add_iff_pos_left,
    ite_eq_left_iff, not_lt, nonpos_iff_eq_zero]
  rintro rfl
  simp_all only [lt_self_iff_false]

/--
lemma `coeff_X_mul_largeSchroderSeriesSeries_sq` / 引理 `coeff_X_mul_largeSchroderSeriesSeries_sq`

English:
lemma coeff_X_mul_largeSchroderSeriesSeries_sq
  given: (n : Nat) (hn : 0 < n)
  proof: by
  rw [pow_two]; rw [← mul_assoc]; rw [coeff_mul]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => (coeff x) (X * largeSchroderSeries) * (coeff y) largeSchroderSeries) n]; rw [Nat.succ_eq_add_one]; rw [sum_range_succ]
  simp only [coeff_largeSchroderSeries, coeff_X_mul_largeSchroderSeries n hn, tsub_self,
    largeSchroder_zero, mul_one]
  have : ∑ x in range n, (coeff x) (X * largeSchroderSeries) * largeSchroder (n - x) =
      ∑ x in range n, if 0 < x then largeSchroder (x - 1) * largeSchroder (n - x) else 0 := by
    apply sum_congr rfl
    intro x a
    simp_all only [mem_range]
    split
    next h =>
      simp_all only [mul_eq_mul_right_iff]
      simp [coeff_X_mul_largeSchroderSeries x (by lia)]
    next h =>
      simp_all only [not_lt, nonpos_iff_eq_zero, coeff_zero_eq_constantCoeff, map_mul,
      constantCoeff_X, constantCoeff_largeSchroderSeries, mul_one, tsub_zero, zero_mul]
  rw [this]; rw [sum_range_eq_add_Ico _ (by lia)]
  simp only [lt_self_iff_false, reduceIte, zero_add]
  have : (∑ x in Ico 1 n, if 0 < x then largeSchroder (x - 1) * largeSchroder (n - x) else 0) =
    ∑ x in Ico 1 n, largeSchroder (x - 1) * largeSchroder (n - x) := by
    apply sum_congr rfl
    intros x hx
    have hx' : 0 < x := by grind
    rw [if_pos hx']
  rw [this]; rw [sum_Ico_eq_sum_range]; rw [show n = n - 1 + 1 by lia]; rw [sum_range_succ]
  grind [largeSchroder_zero]

中文:
引理 coeff_X_mul_largeSchroderSeriesSeries_sq
  条件: (n : 自然数) (hn : 0 < n)
  证明: by
  rw [pow_two]; rw [← mul_assoc]; rw [coeff_mul]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => (coeff x) (X * largeSchroderSeries) * (coeff y) largeSchroderSeries) n]; rw [Nat.succ_eq_add_one]; rw [sum_range_succ]
  simp only [coeff_largeSchroderSeries, coeff_X_mul_largeSchroderSeries n hn, tsub_self,
    largeSchroder_zero, mul_one]
  have : ∑ x in range n, (coeff x) (X * largeSchroderSeries) * largeSchroder (n - x) =
      ∑ x in range n, if 0 < x then largeSchroder (x - 1) * largeSchroder (n - x) else 0 := by
    apply sum_congr rfl
    intro x a
    simp_all only [mem_range]
    split
    next h =>
      simp_all only [mul_eq_mul_right_iff]
      simp [coeff_X_mul_largeSchroderSeries x (by lia)]
    next h =>
      simp_all only [not_lt, nonpos_iff_eq_zero, coeff_zero_eq_constantCoeff, map_mul,
      constantCoeff_X, constantCoeff_largeSchroderSeries, mul_one, tsub_zero, zero_mul]
  rw [this]; rw [sum_range_eq_add_Ico _ (by lia)]
  simp only [lt_self_iff_false, reduceIte, zero_add]
  have : (∑ x in Ico 1 n, if 0 < x then largeSchroder (x - 1) * largeSchroder (n - x) else 0) =
    ∑ x in Ico 1 n, largeSchroder (x - 1) * largeSchroder (n - x) := by
    apply sum_congr rfl
    intros x hx
    have hx' : 0 < x := by grind
    rw [if_pos hx']
  rw [this]; rw [sum_Ico_eq_sum_range]; rw [show n = n - 1 + 1 by lia]; rw [sum_range_succ]
  grind [largeSchroder_zero]

Depends on / 依赖: Nat.succ_eq_add_one, Nat.sum_antidiagonal_eq_sum_range_succ, coeff_X_mul_largeSchroderSeries, coeff_largeSchroderSeries, coeff_mul, largeSchroder, largeSchroderSeries, largeSchroder_zero, mul_assoc, mul_one, pow_two, succ_eq_add_one, sum_antidiagonal_eq_sum_range_succ, sum_range_succ, tsub_self
-/
lemma coeff_X_mul_largeSchroderSeriesSeries_sq (n : Nat) (hn : 0 < n) :
    coeff n (X * largeSchroderSeries ^ 2) =
      ∑ i in range n, largeSchroder i * largeSchroder (n - 1 - i) := by
  rw [pow_two]; rw [← mul_assoc]; rw [coeff_mul]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => (coeff x) (X * largeSchroderSeries) * (coeff y) largeSchroderSeries) n]; rw [Nat.succ_eq_add_one]; rw [sum_range_succ]
  simp only [coeff_largeSchroderSeries, coeff_X_mul_largeSchroderSeries n hn, tsub_self,
    largeSchroder_zero, mul_one]
  have : ∑ x in range n, (coeff x) (X * largeSchroderSeries) * largeSchroder (n - x) =
      ∑ x in range n, if 0 < x then largeSchroder (x - 1) * largeSchroder (n - x) else 0 := by
    apply sum_congr rfl
    intro x a
    simp_all only [mem_range]
    split
    next h =>
      simp_all only [mul_eq_mul_right_iff]
      simp [coeff_X_mul_largeSchroderSeries x (by lia)]
    next h =>
      simp_all only [not_lt, nonpos_iff_eq_zero, coeff_zero_eq_constantCoeff, map_mul,
      constantCoeff_X, constantCoeff_largeSchroderSeries, mul_one, tsub_zero, zero_mul]
  rw [this]; rw [sum_range_eq_add_Ico _ (by lia)]
  simp only [lt_self_iff_false, reduceIte, zero_add]
  have : (∑ x in Ico 1 n, if 0 < x then largeSchroder (x - 1) * largeSchroder (n - x) else 0) =
    ∑ x in Ico 1 n, largeSchroder (x - 1) * largeSchroder (n - x) := by
    apply sum_congr rfl
    intros x hx
    have hx' : 0 < x := by grind
    rw [if_pos hx']
  rw [this]; rw [sum_Ico_eq_sum_range]; rw [show n = n - 1 + 1 by lia]; rw [sum_range_succ]
  grind [largeSchroder_zero]

/--
theorem `largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq` / 定理 `largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq`

English:
theorem largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
  proof: by
  ext n
  by_cases hn : n = 0
  · aesop
  · have hn' : 0 < n := by omega
    simp only [coeff_largeSchroderSeries, map_add, coeff_one, hn, ↓reduceIte, zero_add]
    rw [coeff_X_mul_largeSchroderSeriesSeries_sq _ hn']; rw [coeff_X_mul_largeSchroderSeries _ hn']; rw [show n = n - 1 + 1 by omega]; rw [largeSchroder_succ (n - 1)]
    simp only [add_tsub_cancel_right, Nat.add_left_cancel_iff]
    rw [Iic_eq_Icc]; rw [Nat.bot_eq_zero]; rw [← range_succ_eq_Icc_zero]

中文:
定理 largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
  证明: by
  ext n
  by_cases hn : n = 0
  · aesop
  · have hn' : 0 < n := by omega
    simp only [coeff_largeSchroderSeries, map_add, coeff_one, hn, ↓reduceIte, zero_add]
    rw [coeff_X_mul_largeSchroderSeriesSeries_sq _ hn']; rw [coeff_X_mul_largeSchroderSeries _ hn']; rw [show n = n - 1 + 1 by omega]; rw [largeSchroder_succ (n - 1)]
    simp only [add_tsub_cancel_right, Nat.add_left_cancel_iff]
    rw [Iic_eq_Icc]; rw [Nat.bot_eq_zero]; rw [← range_succ_eq_Icc_zero]

Depends on / 依赖: Iic_eq_Icc, Nat.add_left_cancel_iff, Nat.bot_eq_zero, add_left_cancel_iff, add_tsub_cancel_right, bot_eq_zero, coeff_X_mul_largeSchroderSeries, coeff_X_mul_largeSchroderSeriesSeries_sq, coeff_largeSchroderSeries, coeff_one, largeSchroder_succ, map_add, range_succ_eq_Icc_zero, reduceIte, zero_add
-/
theorem largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq :
    largeSchroderSeries = 1 + X * largeSchroderSeries + X * largeSchroderSeries ^ 2 := by
  ext n
  by_cases hn : n = 0
  · aesop
  · have hn' : 0 < n := by omega
    simp only [coeff_largeSchroderSeries, map_add, coeff_one, hn, ↓reduceIte, zero_add]
    rw [coeff_X_mul_largeSchroderSeriesSeries_sq _ hn']; rw [coeff_X_mul_largeSchroderSeries _ hn']; rw [show n = n - 1 + 1 by omega]; rw [largeSchroder_succ (n - 1)]
    simp only [add_tsub_cancel_right, Nat.add_left_cancel_iff]
    rw [Iic_eq_Icc]; rw [Nat.bot_eq_zero]; rw [← range_succ_eq_Icc_zero]

end PowerSeries
