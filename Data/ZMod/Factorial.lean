/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.ZMod.Basic

/-!
# Facts about factorials in ZMod

We collect facts about factorials in context of modular arithmetic.

## Main statements

* `ZMod.cast_descFactorial`: For natural numbers `n` and `p`, where `n` is less than or equal to `p`
  the descending factorial of `(p - 1)` taken `n` times modulo `p` equals `(-1) ^ n * n!`.

## See also

For the prime case and involving `factorial` rather than `descFactorial`, see Wilson's theorem:
* `Nat.prime_iff_fac_equiv_neg_one`

-/

public section

assert_not_exists TwoSidedIdeal

open Finset Nat

namespace ZMod

/--
theorem `cast_descFactorial` / 定理 `cast_descFactorial`

English:
theorem cast_descFactorial
  given: {n p : Nat} (h : n <= p)
  proof: by
  rw [descFactorial_eq_prod_range]; rw [factorial_eq_prod_range_add_one]
  simp only [cast_prod]
  nth_rw 2 [← card_range n]
  rw [pow_card_mul_prod]
  refine prod_congr rfl ?_
  intro x hx
  rw [← tsub_add_eq_tsub_tsub_swap]; rw [Nat.cast_sub Nat.le_trans (Nat.add_one_le_iff.mpr (List.mem_range.

中文:
定理 cast_descFactorial
  条件: {n p : 自然数} (h : n <= p)
  证明: by
  rw [descFactorial_eq_prod_range]; rw [factorial_eq_prod_range_add_one]
  simp only [cast_prod]
  nth_rw 2 [← card_range n]
  rw [pow_card_mul_prod]
  refine prod_congr rfl ?_
  intro x hx
  rw [← tsub_add_eq_tsub_tsub_swap]; rw [Nat.cast_sub Nat.le_trans (Nat.add_one_le_iff.mpr (List.mem_range.

Depends on / 依赖: CharP.cast_eq_zero, List.mem_range.mp, Nat.add_one_le_iff.mpr, Nat.cast_sub, Nat.le_trans, add_comm, add_one_le_iff, card_range, cast_eq_zero, cast_prod, cast_sub, cast_succ, descFactorial_eq_prod_range, factorial_eq_prod_range_add_one, le_trans, mem_range, mul_add, mul_one, neg_add_rev, neg_mul
-/
theorem cast_descFactorial {n p : Nat} (h : n <= p) :
    (descFactorial (p - 1) n : ZMod p) = (-1) ^ n * n ! := by
  rw [descFactorial_eq_prod_range]; rw [factorial_eq_prod_range_add_one]
  simp only [cast_prod]
  nth_rw 2 [← card_range n]
  rw [pow_card_mul_prod]
  refine prod_congr rfl ?_
  intro x hx
  rw [← tsub_add_eq_tsub_tsub_swap]; rw [Nat.cast_sub Nat.le_trans (Nat.add_one_le_iff.mpr (List.mem_range.mp hx)) h]; rw [CharP.cast_eq_zero]; rw [zero_sub]; rw [cast_succ]; rw [neg_add_rev]; rw [mul_add]; rw [neg_mul]; rw [one_mul]; rw [mul_one]; rw [add_comm]

end ZMod
