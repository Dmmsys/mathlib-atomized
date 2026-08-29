/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Basic

/-!

# Vandermonde's identity

In this file we prove Vandermonde's identity (`Nat.add_choose_eq`):
`(m + n).choose k = ∑ (i, j) ∈ antidiagonal k, m.choose i * n.choose j`

We follow the algebraic proof from
https://en.wikipedia.org/wiki/Vandermonde%27s_identity#Algebraic_proof .

-/

public section


open Polynomial Finset Finset.Nat

namespace Nat

/--
theorem `add_choose_eq` / 定理 `add_choose_eq`

English:
theorem add_choose_eq
  given: (m n k : Nat)
  proof: by
  calc
    (m + n).choose k = ((X + 1) ^ (m + n)).coeff k := by rw [coeff_X_add_one_pow, cast_id]
    _ = ((X + 1) ^ m * (X + 1) ^ n).coeff k := by rw [pow_add]
    _ = ∑ ij in antidiagonal k, m.choose ij.1 * n.choose ij.2 := by
      rw [coeff_mul]; rw [Finset.sum_congr rfl]
      simp only [coeff_X_add_one_pow, cast_id, imp_true_iff]

中文:
定理 add_choose_eq
  条件: (m n k : 自然数)
  证明: by
  calc
    (m + n).choose k = ((X + 1) ^ (m + n)).coeff k := by rw [coeff_X_add_one_pow, cast_id]
    _ = ((X + 1) ^ m * (X + 1) ^ n).coeff k := by rw [pow_add]
    _ = ∑ ij in antidiagonal k, m.choose ij.1 * n.choose ij.2 := by
      rw [coeff_mul]; rw [Finset.sum_congr rfl]
      simp only [coeff_X_add_one_pow, cast_id, imp_true_iff]

Depends on / 依赖: Finset, Finset.sum_congr, antidiagonal, cast_id, coeff_X_add_one_pow, coeff_mul, imp_true_iff, m.choose, n.choose, pow_add, sum_congr
-/
theorem add_choose_eq (m n k : Nat) :
    (m + n).choose k = ∑ ij in antidiagonal k, m.choose ij.1 * n.choose ij.2 := by
  calc
    (m + n).choose k = ((X + 1) ^ (m + n)).coeff k := by rw [coeff_X_add_one_pow, cast_id]
    _ = ((X + 1) ^ m * (X + 1) ^ n).coeff k := by rw [pow_add]
    _ = ∑ ij in antidiagonal k, m.choose ij.1 * n.choose ij.2 := by
      rw [coeff_mul]; rw [Finset.sum_congr rfl]
      simp only [coeff_X_add_one_pow, cast_id, imp_true_iff]

/--
theorem `sum_range_choose_sq` / 定理 `sum_range_choose_sq`

English:
theorem sum_range_choose_sq
  given: (n : Nat)
  proof: by
  rw [two_mul]; rw [add_choose_eq]; rw [sum_antidiagonal_eq_sum_range_succ_mk]
  congr! 1 with _ h
  rw [choose_symm (Finset.mem_range_succ_iff.mp h)]; rw [sq]

中文:
定理 sum_range_choose_sq
  条件: (n : 自然数)
  证明: by
  rw [two_mul]; rw [add_choose_eq]; rw [sum_antidiagonal_eq_sum_range_succ_mk]
  congr! 1 with _ h
  rw [choose_symm (Finset.mem_range_succ_iff.mp h)]; rw [sq]

Depends on / 依赖: Finset, Finset.mem_range_succ_iff.mp, add_choose_eq, choose_symm, mem_range_succ_iff, sum_antidiagonal_eq_sum_range_succ_mk, two_mul
-/
theorem sum_range_choose_sq (n : Nat) :
    ∑ i in Finset.range (n + 1), (n.choose i) ^ 2 = (2 * n).choose n := by
  rw [two_mul]; rw [add_choose_eq]; rw [sum_antidiagonal_eq_sum_range_succ_mk]
  congr! 1 with _ h
  rw [choose_symm (Finset.mem_range_succ_iff.mp h)]; rw [sq]

end Nat
