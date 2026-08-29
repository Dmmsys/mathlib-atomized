/-
Copyright (c) 2025 Junqi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jinzhao Pan
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# shifted Legendre Polynomials

In this file, we define the shifted Legendre polynomials `shiftedLegendre n` for `n : ℕ` as a
polynomial in `ℤ[X]`. We prove some basic properties of the Legendre polynomials.

* `factorial_mul_shiftedLegendre_eq`: The analogue of Rodrigues' formula for the shifted Legendre
  polynomials;
* `shiftedLegendre_eval_symm`: The values of the shifted Legendre polynomial at `x` and `1 - x`
  differ by a factor `(-1)ⁿ`.

## Reference

* <https://en.wikipedia.org/wiki/Legendre_polynomials>

## Tags

shifted Legendre polynomials, derivative
-/

@[expose] public section

open Nat Finset

namespace Polynomial

/--
Definition of `shiftedLegendre` / `shiftedLegendre` 的定义

English:
definition shiftedLegendre
  signature: (n : Nat)
  body: ∑ k in Finset.range (n + 1), C ((-1 : Int) ^ k * n.choose k * (n + k).choose n) * X ^ k

中文:
定义 shiftedLegendre
  签名: (n : 自然数)
  定义体: ∑ k in Finset.range (n + 1), C ((-1 : Int) ^ k * n.choose k * (n + k).choose n) * X ^ k

Depends on / 依赖: Finset, Finset.range, n.choose
-/
noncomputable def shiftedLegendre (n : Nat) : Int[X] :=
  ∑ k in Finset.range (n + 1), C ((-1 : Int) ^ k * n.choose k * (n + k).choose n) * X ^ k

set_option backward.isDefEq.respectTransparency false in
/--
theorem `factorial_mul_shiftedLegendre_eq` / 定理 `factorial_mul_shiftedLegendre_eq`

English:
theorem factorial_mul_shiftedLegendre_eq
  given: (n : Nat)
  statement: (n ! : Int[X]) * (shiftedLegendre n) =
  proof: by
  symm
  calc
  _ = derivative^[n] (((X : Int[X]) - X ^ 2) ^ n) := by
    rw [← mul_pow]; rw [mul_one_sub]; rw [← pow_two]
  _ = derivative^[n] (∑ m in range (n + 1), n.choose m • (-1) ^ m * X ^ (n + m)) := by
    congr
    rw [sub_eq_add_neg]; rw [add_comm]; rw [add_pow]
    congr! 1 with m hm
 

中文:
定理 factorial_mul_shiftedLegendre_eq
  条件: (n : 自然数)
  结论: (n ! : 整数[X]) * (shiftedLegendre n) =
  证明: by
  symm
  calc
  _ = derivative^[n] (((X : Int[X]) - X ^ 2) ^ n) := by
    rw [← mul_pow]; rw [mul_one_sub]; rw [← pow_two]
  _ = derivative^[n] (∑ m in range (n + 1), n.choose m • (-1) ^ m * X ^ (n + m)) := by
    congr
    rw [sub_eq_add_neg]; rw [add_comm]; rw [add_pow]
    congr! 1 with m hm
 

Depends on / 依赖: Finset, Finset.mem_range, add_comm, add_pow, derivative, mem_range, mul_assoc, mul_comm, mul_one_sub, mul_pow, n.choose, neg_pow, nsmul_eq_mul, pow_add, pow_mul_pow_sub, pow_two, sub_eq_add_neg
-/
theorem factorial_mul_shiftedLegendre_eq (n : Nat) : (n ! : Int[X]) * (shiftedLegendre n) =
    derivative^[n] (X ^ n * (1 - (X : Int[X])) ^ n) := by
  symm
  calc
  _ = derivative^[n] (((X : Int[X]) - X ^ 2) ^ n) := by
    rw [← mul_pow]; rw [mul_one_sub]; rw [← pow_two]
  _ = derivative^[n] (∑ m in range (n + 1), n.choose m • (-1) ^ m * X ^ (n + m)) := by
    congr
    rw [sub_eq_add_neg]; rw [add_comm]; rw [add_pow]
    congr! 1 with m hm
    rw [neg_pow]; rw [pow_two]; rw [mul_pow]; rw [← mul_assoc]; rw [mul_comm]; rw [mul_assoc]; rw [pow_mul_pow_sub]; rw [mul_assoc]; rw [← pow_add]; rw [← mul_assoc]; rw [nsmul_eq_mul]; rw [add_comm]
    rw [Finset.mem_range] at hm
    linarith
  _ = ∑ x in range (n + 1), ↑((n + x)! / x !) * C (↑(n.choose x) * (-1) ^ x) * X ^ x := by
    rw [iterate_derivative_sum]
    congr! 1 with x _
    rw [show (n.choose x • (-1) ^ x : Int[X]) = C (n.choose x • (-1) ^ x) by simp,
      iterate_derivative_C_mul, iterate_derivative_X_pow_eq_smul,
      descFactorial_eq_div (by lia), show n + x - n = x by lia]
    simp only [Int.reduceNeg, nsmul_eq_mul, eq_intCast, Int.cast_mul, Int.cast_natCast,
      Int.cast_pow, Int.cast_neg, Int.cast_one, zsmul_eq_mul]
    ring
  _ = ∑ i in range (n + 1), ↑n ! * C ((-1) ^ i * ↑(n.choose i) * ↑((n + i).choose n)) * X ^ i := by
    congr! 2 with x _
    rw [C_mul (b := ((n + x).choose n : Int))]; rw [mul_comm]; rw [mul_comm (n ! : Int[X]), mul_comm _ ((-1) ^ x),
      mul_assoc]
    congr 1
    rw [add_comm]; rw [add_choose]
    simp only [Int.natCast_ediv, cast_mul, eq_intCast]
    norm_cast
    rw [mul_comm]; rw [← Nat.mul_div_assoc]
    · rw [mul_comm, Nat.mul_div_mul_right _ _ (by positivity)]
    · simp only [factorial_mul_factorial_dvd_factorial_add]
  _ = (n ! : Int[X]) * (shiftedLegendre n) := by simp [← mul_assoc, shiftedLegendre, mul_sum]

/--
theorem `coeff_shiftedLegendre` / 定理 `coeff_shiftedLegendre`

English:
theorem coeff_shiftedLegendre
  given: (n k : Nat)
  proof: by
  rw [shiftedLegendre]; rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  simp +contextual [choose_eq_zero_of_lt]

中文:
定理 coeff_shiftedLegendre
  条件: (n k : 自然数)
  证明: by
  rw [shiftedLegendre]; rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  simp +contextual [choose_eq_zero_of_lt]

Depends on / 依赖: choose_eq_zero_of_lt, coeff_C_mul_X_pow, contextual, finsetSum_coeff, shiftedLegendre, simp_rw
-/
theorem coeff_shiftedLegendre (n k : Nat) :
    (shiftedLegendre n).coeff k = (-1) ^ k * n.choose k * (n + k).choose n := by
  rw [shiftedLegendre]; rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  simp +contextual [choose_eq_zero_of_lt]

/--
theorem `degree_shiftedLegendre` / 定理 `degree_shiftedLegendre`

English:
theorem degree_shiftedLegendre
  given: (n : Nat)
  statement: (shiftedLegendre n).degree = n
  proof: by
  refine le_antisymm ?_ (le_degree_of_ne_zero ?_)
  · rw [degree_le_iff_coeff_zero]
    intro k h
    norm_cast at h
    simp [coeff_shiftedLegendre, choose_eq_zero_of_lt h]
  · simp [coeff_shiftedLegendre, (choose_pos (show n <= n + n by simp)).ne']

中文:
定理 degree_shiftedLegendre
  条件: (n : 自然数)
  结论: (shiftedLegendre n).degree = n
  证明: by
  refine le_antisymm ?_ (le_degree_of_ne_zero ?_)
  · rw [degree_le_iff_coeff_zero]
    intro k h
    norm_cast at h
    simp [coeff_shiftedLegendre, choose_eq_zero_of_lt h]
  · simp [coeff_shiftedLegendre, (choose_pos (show n <= n + n by simp)).ne']
-/
@[simp] theorem degree_shiftedLegendre (n : Nat) : (shiftedLegendre n).degree = n := by
  refine le_antisymm ?_ (le_degree_of_ne_zero ?_)
  · rw [degree_le_iff_coeff_zero]
    intro k h
    norm_cast at h
    simp [coeff_shiftedLegendre, choose_eq_zero_of_lt h]
  · simp [coeff_shiftedLegendre, (choose_pos (show n <= n + n by simp)).ne']

/--
theorem `natDegree_shiftedLegendre` / 定理 `natDegree_shiftedLegendre`

English:
theorem natDegree_shiftedLegendre
  given: (n : Nat)
  statement: (shiftedLegendre n).natDegree = n
  proof: natDegree_eq_of_degree_eq_some (degree_shiftedLegendre n)

中文:
定理 natDegree_shiftedLegendre
  条件: (n : 自然数)
  结论: (shiftedLegendre n).natDegree = n
  证明: natDegree_eq_of_degree_eq_some (degree_shiftedLegendre n)
-/
@[simp] theorem natDegree_shiftedLegendre (n : Nat) : (shiftedLegendre n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_shiftedLegendre n)

/--
theorem `neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq` / 定理 `neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq`

English:
theorem neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq
  given: (n : Nat)
  proof: by
  refine nat_mul_inj' ?_ (factorial_ne_zero n)
  rw [← mul_assoc]; rw [mul_comm (n ! : Int[X]), mul_assoc, ← natCast_mul_comp,
    factorial_mul_shiftedLegendre_eq, ← iterate_derivative_comp_one_sub_X]
  simp [mul_comm]

中文:
定理 neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq
  条件: (n : 自然数)
  证明: by
  refine nat_mul_inj' ?_ (factorial_ne_zero n)
  rw [← mul_assoc]; rw [mul_comm (n ! : Int[X]), mul_assoc, ← natCast_mul_comp,
    factorial_mul_shiftedLegendre_eq, ← iterate_derivative_comp_one_sub_X]
  simp [mul_comm]

Depends on / 依赖: factorial_mul_shiftedLegendre_eq, factorial_ne_zero, iterate_derivative_comp_one_sub_X, mul_assoc, mul_comm, natCast_mul_comp, nat_mul_inj
-/
theorem neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq (n : Nat) :
    (-1) ^ n * (shiftedLegendre n).comp (1 - X) = shiftedLegendre n := by
  refine nat_mul_inj' ?_ (factorial_ne_zero n)
  rw [← mul_assoc]; rw [mul_comm (n ! : Int[X]), mul_assoc, ← natCast_mul_comp,
    factorial_mul_shiftedLegendre_eq, ← iterate_derivative_comp_one_sub_X]
  simp [mul_comm]

/--
lemma `shiftedLegendre_eval_symm` / 引理 `shiftedLegendre_eval_symm`

English:
lemma shiftedLegendre_eval_symm
  given: (n : Nat) {R : Type*} [Ring R] (x : R)
  proof: by
  have := congr(aeval x $(neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq n))
  simpa [aeval_comp] using this.symm

中文:
引理 shiftedLegendre_eval_symm
  条件: (n : 自然数) {R : 类型} [Ring R] (x : R)
  证明: by
  have := congr(aeval x $(neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq n))
  simpa [aeval_comp] using this.symm

Depends on / 依赖: aeval_comp, neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq, this.symm
-/
lemma shiftedLegendre_eval_symm (n : Nat) {R : Type*} [Ring R] (x : R) :
    aeval x (shiftedLegendre n) = (-1) ^ n * aeval (1 - x) (shiftedLegendre n) := by
  have := congr(aeval x $(neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq n))
  simpa [aeval_comp] using this.symm

end Polynomial
