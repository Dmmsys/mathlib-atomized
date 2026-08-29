/-
Copyright (c) 2025 Weijie Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weijie Jiang
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Catalan Power Series

We introduce the Catalan generating function as a formal power series over `ℕ`:
  `catalanSeries = ∑_{n ≥ 0} catalan n * X^n`

## Main Definitions
* `PowerSeries.catalanSeries`: The Catalan generating function as a power series.

## Main Results
* `PowerSeries.catalanSeries_one_add_X_mul_self_sq`: The Catalan generating function satisfies the
  equation `catalanSeries = 1 + X * catalanSeries ^ 2`.

## TODO
* Find and prove the closed formula for the Catalan generating function:
  `C(X) = (1 - √(1 - 4X)) / (2X)`
-/

@[expose] public section

open Finset

namespace PowerSeries

/--
Definition of `catalanSeries` / `catalanSeries` 的定义

English:
definition catalanSeries
  signature: : PowerSeries Nat
  body: PowerSeries.mk catalan

@[simp]

中文:
定义 catalanSeries
  签名: : PowerSeries 自然数
  定义体: PowerSeries.mk catalan

@[simp]

Depends on / 依赖: PowerSeries, PowerSeries.mk, catalan
-/
def catalanSeries : PowerSeries Nat := PowerSeries.mk catalan

@[simp]
/--
lemma `catalanSeries_coeff` / 引理 `catalanSeries_coeff`

English:
lemma catalanSeries_coeff
  given: (n : Nat)
  statement: (coeff n) catalanSeries = catalan n
  proof: by
  simp [catalanSeries]

@[simp]

中文:
引理 catalanSeries_coeff
  条件: (n : 自然数)
  结论: (coeff n) catalanSeries = catalan n
  证明: by
  simp [catalanSeries]

@[simp]

Depends on / 依赖: catalanSeries
-/
lemma catalanSeries_coeff (n : Nat) : (coeff n) catalanSeries = catalan n := by
  simp [catalanSeries]

@[simp]
/--
lemma `catalanSeries_constantCoeff` / 引理 `catalanSeries_constantCoeff`

English:
lemma catalanSeries_constantCoeff
  statement: constantCoeff catalanSeries = 1
  proof: by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [catalanSeries_coeff, catalan_zero]

中文:
引理 catalanSeries_constantCoeff
  结论: constantCoeff catalanSeries = 1
  证明: by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [catalanSeries_coeff, catalan_zero]

Depends on / 依赖: PowerSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply, catalanSeries_coeff, catalan_zero, coeff_zero_eq_constantCoeff_apply
-/
lemma catalanSeries_constantCoeff : constantCoeff catalanSeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [catalanSeries_coeff, catalan_zero]

/--
theorem `catalanSeries_sq_mul_X_add_one` / 定理 `catalanSeries_sq_mul_X_add_one`

English:
theorem catalanSeries_sq_mul_X_add_one
  statement: catalanSeries ^ 2 * X + 1 = catalanSeries
  proof: by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp_rw [add_comm, map_add, coeff_one, if_neg n.succ_ne_zero, zero_add, coeff_succ_mul_X, sq,
      coeff_mul, catalanSeries_coeff, catalan_succ']

中文:
定理 catalanSeries_sq_mul_X_add_one
  结论: catalanSeries ^ 2 * X + 1 = catalanSeries
  证明: by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp_rw [add_comm, map_add, coeff_one, if_neg n.succ_ne_zero, zero_add, coeff_succ_mul_X, sq,
      coeff_mul, catalanSeries_coeff, catalan_succ']

Depends on / 依赖: add_comm, catalanSeries_coeff, catalan_succ, coeff_mul, coeff_one, coeff_succ_mul_X, if_neg, map_add, n.succ_ne_zero, simp_rw, succ_ne_zero, zero_add
-/
theorem catalanSeries_sq_mul_X_add_one : catalanSeries ^ 2 * X + 1 = catalanSeries := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp_rw [add_comm, map_add, coeff_one, if_neg n.succ_ne_zero, zero_add, coeff_succ_mul_X, sq,
      coeff_mul, catalanSeries_coeff, catalan_succ']

end PowerSeries
