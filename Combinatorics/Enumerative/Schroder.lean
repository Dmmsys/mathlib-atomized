/-
Copyright (c) 2025 Weijie Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weijie Jiang
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Even
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

/-!
# Schröder numbers

The Schröder numbers (https://oeis.org/A006318) are a sequence of integers that appear in various
combinatorial contexts.

## Main definitions

* `largeSchroder n`: the `n`th large Schröder number, defined recursively as `L 0 = 1` and
  `L (n + 1) = L n + ∑ i ≤ n, L i * L (n - i)`.
* `smallSchroder n`: the `n`th small Schröder number, defined as `S 0 = 1` and `S n = L n / 2`
  for `n > 0`.

## Main results

* `largeSchroder_even` : The large Schröder numbers are positive and even for `n > 0`.
* `smallSchroder_succ` : A recursive formula for small Schröder numbers:
  `S (n + 1) = 3 * S n + 2 * ∑ i < n - 2, S (i + 2) * S (n - 1 - i)`.

## Tags

Schroeder, Schroder
-/

@[expose] public section

open Finset

namespace Nat
variable {n : Nat}

/--
Definition of `largeSchroder` / `largeSchroder` 的定义

English:
definition largeSchroder
  signature: : Nat -> Nat

中文:
定义 largeSchroder
  签名: : 自然数 -> 自然数
-/
def largeSchroder : Nat -> Nat
  | 0 => 1
  | n + 1 => largeSchroder n + ∑ i : Fin n.succ, largeSchroder i * largeSchroder (n - i)

/--
theorem `largeSchroder_zero` / 定理 `largeSchroder_zero`

English:
theorem largeSchroder_zero
  statement: largeSchroder 0 = 1
  proof: by simp [largeSchroder]

中文:
定理 largeSchroder_zero
  结论: largeSchroder 0 = 1
  证明: by simp [largeSchroder]
-/
@[simp] theorem largeSchroder_zero : largeSchroder 0 = 1 := by simp [largeSchroder]
/--
theorem `largeSchroder_one` / 定理 `largeSchroder_one`

English:
theorem largeSchroder_one
  statement: largeSchroder 1 = 2
  proof: by simp [largeSchroder]

中文:
定理 largeSchroder_one
  结论: largeSchroder 1 = 2
  证明: by simp [largeSchroder]
-/
@[simp] theorem largeSchroder_one : largeSchroder 1 = 2 := by simp [largeSchroder]
/--
theorem `largeSchroder_two` / 定理 `largeSchroder_two`

English:
theorem largeSchroder_two
  statement: largeSchroder 2 = 6
  proof: by simp [largeSchroder]

中文:
定理 largeSchroder_two
  结论: largeSchroder 2 = 6
  证明: by simp [largeSchroder]
-/
@[simp] theorem largeSchroder_two : largeSchroder 2 = 6 := by simp [largeSchroder]

/--
theorem `largeSchroder_succ` / 定理 `largeSchroder_succ`

English:
theorem largeSchroder_succ
  given: (n : Nat)
  proof: by
  simp [largeSchroder, ← Iio_add_one_eq_Iic, Nat.Iio_eq_range, ← Fin.sum_univ_eq_sum_range]

中文:
定理 largeSchroder_succ
  条件: (n : 自然数)
  证明: by
  simp [largeSchroder, ← Iio_add_one_eq_Iic, Nat.Iio_eq_range, ← Fin.sum_univ_eq_sum_range]

Depends on / 依赖: Fin.sum_univ_eq_sum_range, Iio_add_one_eq_Iic, Iio_eq_range, Nat.Iio_eq_range, largeSchroder, sum_univ_eq_sum_range
-/
theorem largeSchroder_succ (n : Nat) :
    largeSchroder (n + 1) = largeSchroder n + ∑ i <= n, largeSchroder i * largeSchroder (n - i) := by
  simp [largeSchroder, ← Iio_add_one_eq_Iic, Nat.Iio_eq_range, ← Fin.sum_univ_eq_sum_range]

/--
theorem `even_largeSchroder` / 定理 `even_largeSchroder`

English:
theorem even_largeSchroder
  statement: forall {n : Nat}, n != 0 -> Even (largeSchroder n)
  proof: k
    · simpa using even_largeSchroder n.succ_ne_zero
    have : k < n + 1 := by simp at hk; lia
    exact .mul_right (even_largeSchroder k.succ_ne_zero) _

中文:
定理 even_largeSchroder
  结论: 对任意 {n : 自然数}, n != 0 -> Even (largeSchroder n)
  证明: k
    · simpa using even_largeSchroder n.succ_ne_zero
    have : k < n + 1 := by simp at hk; lia
    exact .mul_right (even_largeSchroder k.succ_ne_zero) _
-/
theorem even_largeSchroder : forall {n : Nat}, n != 0 -> Even (largeSchroder n)
  | 1, _ => by simp
  | n + 2, _ => by
    rw [largeSchroder_succ]
refine .add (even_largeSchroder n.succ_ne_zero) even_sum _ fun k hk => ?_
    obtain _ | k := k
    · simpa using even_largeSchroder n.succ_ne_zero
    have : k < n + 1 := by simp at hk; lia
    exact .mul_right (even_largeSchroder k.succ_ne_zero) _

/--
Definition of `smallSchroder` / `smallSchroder` 的定义

English:
definition smallSchroder
  signature: : Nat -> Nat

中文:
定义 smallSchroder
  签名: : 自然数 -> 自然数
-/
def smallSchroder : Nat -> Nat
  | 0 => 1
  | 1 => 1
  | n + 1 => largeSchroder n / 2

/--
lemma `smallSchroder_zero` / 引理 `smallSchroder_zero`

English:
lemma smallSchroder_zero
  statement: smallSchroder 0 = 1
  proof: by simp [smallSchroder]

中文:
引理 smallSchroder_zero
  结论: smallSchroder 0 = 1
  证明: by simp [smallSchroder]
-/
@[simp] lemma smallSchroder_zero : smallSchroder 0 = 1 := by simp [smallSchroder]
/--
lemma `smallSchroder_one` / 引理 `smallSchroder_one`

English:
lemma smallSchroder_one
  statement: smallSchroder 1 = 1
  proof: by simp [smallSchroder]

中文:
引理 smallSchroder_one
  结论: smallSchroder 1 = 1
  证明: by simp [smallSchroder]

Depends on / 依赖: Bifunctor, Bifunctor.functor, Functor, functor
-/
@[simp] lemma smallSchroder_one : smallSchroder 1 = 1 := by simp [smallSchroder]

/--
lemma `smallSchroder_succ_eq_largeSchroder_div_two` / 引理 `smallSchroder_succ_eq_largeSchroder_div_two`

English:
lemma smallSchroder_succ_eq_largeSchroder_div_two
  given: (h : n != 0)
  proof: by simp [smallSchroder]

中文:
引理 smallSchroder_succ_eq_largeSchroder_div_two
  条件: (h : n != 0)
  证明: by simp [smallSchroder]

Depends on / 依赖: Bifunctor, Bifunctor.lawfulFunctor, LawfulBifunctor, lawfulFunctor, smallSchroder
-/
lemma smallSchroder_succ_eq_largeSchroder_div_two (h : n != 0) :
    smallSchroder (n + 1) = largeSchroder n / 2 := by simp [smallSchroder]

/--
lemma `two_mul_smallSchroder_succ` / 引理 `two_mul_smallSchroder_succ`

English:
lemma two_mul_smallSchroder_succ
  given: (hn : n != 0)
  statement: 2 * smallSchroder (n + 1) = largeSchroder n
  proof: by
  rw [smallSchroder_succ_eq_largeSchroder_div_two hn]; rw [Nat.mul_div_cancel_left' (even_largeSchroder hn).two_dvd]

中文:
引理 two_mul_smallSchroder_succ
  条件: (hn : n != 0)
  结论: 2 * smallSchroder (n + 1) = largeSchroder n
  证明: by
  rw [smallSchroder_succ_eq_largeSchroder_div_two hn]; rw [Nat.mul_div_cancel_left' (even_largeSchroder hn).two_dvd]

Depends on / 依赖: Nat.mul_div_cancel_left, even_largeSchroder, mul_div_cancel_left, smallSchroder_succ_eq_largeSchroder_div_two, two_dvd
-/
lemma two_mul_smallSchroder_succ (hn : n != 0) : 2 * smallSchroder (n + 1) = largeSchroder n := by
  rw [smallSchroder_succ_eq_largeSchroder_div_two hn]; rw [Nat.mul_div_cancel_left' (even_largeSchroder hn).two_dvd]

/--
theorem `smallSchroder_succ` / 定理 `smallSchroder_succ`

English:
theorem smallSchroder_succ
  given: (hn : 1 < n)
  proof: by
  obtain _ | _ | n := n
  · simp at hn
  · simp at hn
  refine Nat.mul_left_cancel zero_lt_two ?_
  calc
        2 * (n + 3).smallSchroder
    _ = 3 * (n + 1).largeSchroder +
          ∑ i in Ioo 0 (n + 1), i.largeSchroder * (n + 1 - i).largeSchroder := by
      rw [two_mul_smallSchroder_succ]; rw [largeSchroder_succ]; rw [← Icc_bot]; rw [← sum_Ioc_add_eq_sum_Icc]; rw [← sum_Ioo_add_eq_sum_Ioc] <;> simp; lia
    _ = 3 * (n + 1).largeSchroder +
          ∑ i in Ioo 0 (n + 1), (2 * (i + 1).smallSchroder) * (2 * (n + 2 - i).smallSchroder) := by
      congr! 2 with i hi
      simp at hi
      rw [← two_mul_smallSchroder_succ]; rw [← two_mul_smallSchroder_succ] <;>
      · #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
        we need to re-enable model-based theory combination in `lia` for this to go through. -/
        lia +mbtc
    _ = 6 * (n + 2).smallSchroder +
          4 * ∑ i in Ioo 0 (n + 1), (i + 1).smallSchroder * (n + 2 - i).smallSchroder := by
      rw [← two_mul_smallSchroder_succ (by lia)]
      simp [mul_mul_mul_comm _ _ 2, ← Finset.mul_sum]
      lia
    _ = _ := by lia

中文:
定理 smallSchroder_succ
  条件: (hn : 1 < n)
  证明: by
  obtain _ | _ | n := n
  · simp at hn
  · simp at hn
  refine Nat.mul_left_cancel zero_lt_two ?_
  calc
        2 * (n + 3).smallSchroder
    _ = 3 * (n + 1).largeSchroder +
          ∑ i in Ioo 0 (n + 1), i.largeSchroder * (n + 1 - i).largeSchroder := by
      rw [two_mul_smallSchroder_succ]; rw [largeSchroder_succ]; rw [← Icc_bot]; rw [← sum_Ioc_add_eq_sum_Icc]; rw [← sum_Ioo_add_eq_sum_Ioc] <;> simp; lia
    _ = 3 * (n + 1).largeSchroder +
          ∑ i in Ioo 0 (n + 1), (2 * (i + 1).smallSchroder) * (2 * (n + 2 - i).smallSchroder) := by
      congr! 2 with i hi
      simp at hi
      rw [← two_mul_smallSchroder_succ]; rw [← two_mul_smallSchroder_succ] <;>
      · #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
        we need to re-enable model-based theory combination in `lia` for this to go through. -/
        lia +mbtc
    _ = 6 * (n + 2).smallSchroder +
          4 * ∑ i in Ioo 0 (n + 1), (i + 1).smallSchroder * (n + 2 - i).smallSchroder := by
      rw [← two_mul_smallSchroder_succ (by lia)]
      simp [mul_mul_mul_comm _ _ 2, ← Finset.mul_sum]
      lia
    _ = _ := by lia

Depends on / 依赖: Icc_bot, Nat.mul_left_cancel, i.largeSchroder, largeSchroder, largeSchroder_succ, mul_left_cancel, smallSchroder, sum_Ioc_add_eq_sum_Icc, sum_Ioo_add_eq_sum_Ioc, two_mul_smallSchroder_succ, zero_lt_two
-/
theorem smallSchroder_succ (hn : 1 < n) :
    smallSchroder (n + 1) =
      3 * n.smallSchroder +
          2 * ∑ i in Ioo 0 (n - 1), (i + 1).smallSchroder * (n - i).smallSchroder := by
  obtain _ | _ | n := n
  · simp at hn
  · simp at hn
  refine Nat.mul_left_cancel zero_lt_two ?_
  calc
        2 * (n + 3).smallSchroder
    _ = 3 * (n + 1).largeSchroder +
          ∑ i in Ioo 0 (n + 1), i.largeSchroder * (n + 1 - i).largeSchroder := by
      rw [two_mul_smallSchroder_succ]; rw [largeSchroder_succ]; rw [← Icc_bot]; rw [← sum_Ioc_add_eq_sum_Icc]; rw [← sum_Ioo_add_eq_sum_Ioc] <;> simp; lia
    _ = 3 * (n + 1).largeSchroder +
          ∑ i in Ioo 0 (n + 1), (2 * (i + 1).smallSchroder) * (2 * (n + 2 - i).smallSchroder) := by
      congr! 2 with i hi
      simp at hi
      rw [← two_mul_smallSchroder_succ]; rw [← two_mul_smallSchroder_succ] <;>
      · #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
        we need to re-enable model-based theory combination in `lia` for this to go through. -/
        lia +mbtc
    _ = 6 * (n + 2).smallSchroder +
          4 * ∑ i in Ioo 0 (n + 1), (i + 1).smallSchroder * (n + 2 - i).smallSchroder := by
      rw [← two_mul_smallSchroder_succ (by lia)]
      simp [mul_mul_mul_comm _ _ 2, ← Finset.mul_sum]
      lia
    _ = _ := by lia

end Nat
